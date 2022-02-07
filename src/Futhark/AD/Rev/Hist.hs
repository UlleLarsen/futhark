{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module Futhark.AD.Rev.Hist
  ( diffMinMaxHist,
    diffMulHist,
    diffAddHist, 
  )
where

import Futhark.AD.Rev.Monad
import Futhark.Analysis.PrimExp.Convert
import Futhark.Builder
import Futhark.IR.SOACS
import Futhark.Tools
import Futhark.Transform.Rename
import Control.Monad

getBinOpPlus :: PrimType -> BinOp
getBinOpPlus (IntType x) = Add x OverflowUndef
getBinOpPlus (FloatType f) = FAdd f
getBinOpPlus _ = error "In getBinOpMul, Hist.hs: input not supported"

getBinOpDiv :: PrimType -> BinOp
getBinOpDiv (IntType t) = SDiv t Unsafe
getBinOpDiv (FloatType t) = FDiv t
getBinOpDiv _ = error "In getBinOpDiv, Hist.hs: input not supported"

onePrimValue :: PrimType -> PrimValue
onePrimValue (IntType Int8) = IntValue $ Int8Value 1
onePrimValue (IntType Int16) = IntValue $ Int16Value 1
onePrimValue (IntType Int32) = IntValue $ Int32Value 1
onePrimValue (IntType Int64) = IntValue $ Int64Value 1
onePrimValue (FloatType Float16) = FloatValue $ Float16Value 1.0
onePrimValue (FloatType Float32) = FloatValue $ Float32Value 1.0
onePrimValue (FloatType Float64) = FloatValue $ Float64Value 1.0
onePrimValue Bool = BoolValue True
onePrimValue Unit = UnitValue

withinBounds :: [(SubExp, VName)] -> TPrimExp Bool VName
withinBounds [] = TPrimExp $ ValueExp (BoolValue True)
withinBounds [(q, i)] = (le64 i .<. pe64 q) .&&. (pe64 (intConst Int64 (-1)) .<. le64 i)
withinBounds (qi : qis) = withinBounds [qi] .&&. withinBounds qis

--
-- special case of histogram with min/max as operator.
-- Original, assuming `is: [n]i64` and `dst: [w]btp`
--     let x = reduce_by_index dst minmax ne is vs
-- Forward trace:
--     let (x, x_inds) = zip vs (iota n)
--                       |> reduce_by_index dst argminmax (ne,-1) is
--
-- Reverse trace:
--     dst_bar += map (\x_ind b -> if x_ind == -1 
--                                 then b 
--                                 else 0
--                    ) x_inds x_bar

--     vs_ctrbs = map2 (\i b -> if i == -1
--                              then 0
--                              else vs_bar[i] + b
--                     ) x_inds x_bar
--     vs_bar <- scatter vs_bar x_inds vs_ctrbs
diffMinMaxHist ::
  VjpOps -> VName -> StmAux () -> SubExp -> BinOp -> SubExp -> VName -> VName -> SubExp -> SubExp -> VName -> ADM () -> ADM ()
diffMinMaxHist _ops x aux n minmax ne is vs w rf dst m = do
  let t = binOpType minmax

  acc_v_p <- newParam "acc_v" $ Prim t
  acc_i_p <- newParam "acc_i" $ Prim int64
  v_p <- newParam "v" $ Prim t
  i_p <- newParam "i" $ Prim int64
  hist_lam <-
    mkLambda [acc_v_p, acc_i_p, v_p, i_p] $
      fmap varsRes . letTupExp "idx_res"
        =<< eIf
          (eCmpOp (CmpEq t) (eParam acc_v_p) (eParam v_p))
          ( eBody
              [ eParam acc_v_p,
                eBinOp (SMin Int64) (eParam acc_i_p) (eParam i_p)
              ]
          )
          ( eBody
              [ eIf
                  ( eCmpOp
                      (CmpEq t)
                      (eParam acc_v_p)
                      (eBinOp minmax (eParam acc_v_p) (eParam v_p))
                  )
                  (eBody [eParam acc_v_p, eParam acc_i_p])
                  (eBody [eParam v_p, eParam i_p])
              ]
          )

  minus_ones <- 
    letExp "minus_ones" $ 
      BasicOp $ Replicate (Shape [w]) (intConst Int64 (-1)) 
  iota_n <-
    letExp "red_iota" $
      BasicOp $ Iota n (intConst Int64 0) (intConst Int64 1) Int64
  
  let hist_op = HistOp (Shape [w]) rf [dst, minus_ones] [ne, intConst Int64 (-1)] hist_lam
  f' <- mkIdentityLambda [Prim int64, Prim t, Prim int64]
  x_inds <- newVName (baseString x <> "_inds")
  auxing aux $ 
    letBindNames [x, x_inds] $ Op $ Hist n [is, vs, iota_n] [hist_op] f'

  m

  x_bar <- lookupAdjVal x

  x_ind_dst <- newParam (baseString x ++ "_ind_param") $ Prim int64
  x_bar_dst <- newParam (baseString x ++ "_bar_param") $ Prim t
  dst_lam <-
    mkLambda [x_ind_dst, x_bar_dst] $
      fmap varsRes . letTupExp "res" 
        =<< eIf
          (eCmpOp (CmpEq int64) (eParam x_ind_dst) (eSubExp $ intConst Int64 (-1)))
          (eBody $ return $ eParam x_bar_dst)
          (eBody $ return $ eSubExp $ Constant $ blankPrimValue t)

  dst_bar <-
    letExp (baseString dst ++ "_bar") $
      Op $
        Screma w [x_inds, x_bar] $ mapSOAC dst_lam

  updateAdj dst dst_bar

  vs_bar <- lookupAdjVal vs

  x_ind_vs <- newParam (baseString x ++ "_ind_param") $ Prim int64
  x_bar_vs <- newParam (baseString x ++ "_bar_param") $ Prim t
  vs_lam <-
    mkLambda [x_ind_vs, x_bar_vs] $
      fmap varsRes . letTupExp "res" 
        =<< eIf
          (eCmpOp (CmpEq int64) (eParam x_ind_vs) (eSubExp $ intConst Int64 (-1)))
          (eBody $ return $ eSubExp $ Constant $ blankPrimValue t)
          (eBody $ return $ do
             vs_bar_i <-
               letSubExp (baseString vs_bar ++ "_el") $
                 BasicOp $
                   Index vs_bar $ Slice [DimFix $ Var $ paramName x_ind_vs]
             eBinOp (getBinOpPlus t) (eParam x_bar_vs) (eSubExp vs_bar_i))

  vs_bar_p <-
    letExp (baseString vs ++ "_partial") $
      Op $
        Screma w [x_inds, x_bar] $ mapSOAC vs_lam

  f'' <- mkIdentityLambda [Prim int64, Prim t]
  vs_bar' <- 
    letExp (baseString vs ++ "_bar") $ Op $ 
      Scatter w [x_inds, vs_bar_p] f'' [(Shape [n], 1, vs_bar)]
  insAdj vs vs_bar'

--
-- special case of histogram with multiplication as operator.
-- Original, assuming `is: [n]i64` and `dst: [w]btp`
--     let x = reduce_by_index dst (*) ne is vs
-- Forward trace:
--     let (ps, zs) = map (\v -> if x == 0 then (1,1) else (v,0)) vs
--     let non_zero_prod = reduce_by_index nes (*) ne is ps
--     let zero_count = reduce_by_index 0s (+) 0 is zs
--     let h_part = map2 (\p c -> if c == 0 then p else 0
--                       ) non_zero_prod zero_count
--     let x = map2 (*) dst h_part
--
-- Reverse trace:
--     dst_bar += map2 (*) h_part x_bar

--     let part_bar = map2 (*) dst x_bar
--     vs_bar += map2 (\i v -> let zr_cts = zero_count[i]
--                             let pr_bar = part_bar[i]
--                             let nz_prd = non_zero_prod[i]
--                             in if zr_cts == 0
--                             then pr_bar * (nz_prd / v) 
--                             else if zr_cts == 1 and v == 0
--                             then nz_prd * pr_bar
--                             else 0
--                    ) is vs
diffMulHist ::
  VjpOps -> VName -> StmAux () -> SubExp -> BinOp -> SubExp -> VName -> VName -> SubExp -> SubExp -> VName -> ADM () -> ADM ()
diffMulHist _ops x aux n mul ne is vs w rf dst m = do
  let t = binOpType mul

  v_param <- newParam "v" $ Prim t

  map_lam <-  
    mkLambda [v_param] $
      fmap varsRes . letTupExp "map_res" =<<
        eIf
          (eCmpOp (CmpEq t) (eParam  v_param) (eSubExp $ Constant $ blankPrimValue t))
          (eBody $ fmap eSubExp [Constant $ onePrimValue t, intConst Int64 1])
          (eBody [eParam v_param, eSubExp $ intConst Int64 0])

  ps <- newVName "ps"
  zs <- newVName "zs"

  letBindNames [ps, zs] $ 
    Op $ Screma n [vs] $ mapSOAC map_lam
  
  lam_mul <- binOpLambda mul t 
  nz_prods0 <- letExp "nz_prd" $ BasicOp $ Replicate (Shape [w]) ne
  let hist_nzp = HistOp (Shape [w]) rf [nz_prods0] [ne] lam_mul

  lam_add <- binOpLambda (Add Int64 OverflowUndef) int64
  zr_counts0 <- letExp "zr_cts" $ BasicOp $ Replicate (Shape [w]) (intConst Int64 0)
  let hist_zrn = HistOp (Shape [w]) rf [zr_counts0] [intConst Int64 0] lam_add
  
  f' <- mkIdentityLambda [Prim int64, Prim int64, Prim t, Prim int64]
  nz_prods <- newVName "non_zero_prod"
  zr_counts <- newVName "zero_count"
  auxing aux $
    letBindNames [nz_prods, zr_counts] $ Op $ Hist n [is, is, ps, zs] [hist_nzp, hist_zrn] f'

  p_param <- newParam "prod" $ Prim t
  c_param <- newParam "count" $ Prim int64
  h_part_body <-
    mkLambda [p_param, c_param] $
      fmap varsRes . letTupExp "h_part" =<<
        eIf
          (eCmpOp (CmpEq int64) (eSubExp $ intConst Int64 0) (eParam c_param))
          (eBody $ return $ eParam p_param)
          (eBody $ return $ eSubExp $ Constant $ blankPrimValue t)
  h_part <-
    letExp "h_part" $ Op $ Screma w [nz_prods, zr_counts] $ mapSOAC h_part_body

  lam_mul' <- renameLambda lam_mul
  auxing aux $
    letBindNames [x]
      $ Op $ Screma w [dst, h_part] $ mapSOAC lam_mul'

  m

  x_bar <- lookupAdjVal x

  lam_mul'' <- renameLambda lam_mul
  dst_bar <- 
    letExp (baseString dst ++ "_bar") $ Op $ Screma w [h_part, x_bar] $ mapSOAC lam_mul''
  updateAdj dst dst_bar

  lam_mul''' <- renameLambda lam_mul
  part_bar <- 
    letExp "part_bar" $ Op $ Screma w [dst, x_bar] $ mapSOAC lam_mul'''
  
  j_param <- newParam "j" $ Prim int64 
  a_param <- newParam "a" $ Prim t
  lam_vsbar <- 
    mkLambda [j_param, a_param] $
      fmap varsRes . letTupExp "vs_bar" =<< do
        let j = Slice [DimFix $ Var $ paramName j_param]
        names <- traverse newVName ["zr_cts", "pr_bar", "nz_prd"]
        let [zr_cts, pr_bar, nz_prd] = names
        zipWithM_ (\name -> letBindNames [name] . BasicOp . flip Index j) names [zr_counts, part_bar, nz_prods]

        eIf
          (eCmpOp (CmpEq int64) (eSubExp $ intConst Int64 0) (eSubExp $ Var zr_cts))
          (eBody $ return $ eBinOp mul (eSubExp $ Var pr_bar) $ eBinOp (getBinOpDiv t) (eSubExp $ Var nz_prd) $ eParam a_param) 
          (eBody $ return $ 
            eIf 
              (eBinOp LogAnd (eCmpOp (CmpEq int64) (eSubExp $ intConst Int64 1) (eSubExp $ Var zr_cts)) 
                             (eCmpOp (CmpEq t) (eSubExp $ Constant $ blankPrimValue t) $ eParam a_param))
              (eBody $ return $ eBinOp mul (eSubExp $ Var nz_prd) (eSubExp $ Var pr_bar)) 
              (eBody $ return $ eSubExp $ Constant $ blankPrimValue t) 
          )
  vs_bar <- 
    letExp "vs_bar" $ Op $ Screma n [is, vs] $ mapSOAC lam_vsbar

  updateAdj vs vs_bar

diffAddHist ::
  VjpOps -> VName -> StmAux () -> SubExp -> BinOp -> SubExp -> VName -> VName -> SubExp -> SubExp -> VName -> ADM () -> ADM ()
diffAddHist _ops x aux n add ne is vs w rf dst m = do
  let t = binOpType add

  f <- mkIdentityLambda [Prim int64, Prim t]
  add_lam <- binOpLambda add t
  auxing aux $
    letBindNames [x] $
      Op $
        Hist n [is, vs] [HistOp (Shape [w]) rf [dst] [ne] add_lam] f

  m

  x_bar <- lookupAdjVal x

  updateAdj dst x_bar

  ind_param <- newParam (baseString vs ++ "_ind") $ Prim t
  lam_vsbar <- 
      mkLambda [ind_param] $
        fmap varsRes . letTupExp "vs_bar" =<<
          eIf 
            (toExp $ withinBounds $ return (w, paramName ind_param))
            ( do
                r <- letSubExp "r" $ BasicOp $ Index x_bar $ Slice [DimFix $ Var $ paramName ind_param]
                resultBodyM [r]
            )
            (eBody $ return $ eSubExp $ Constant $ blankPrimValue t)

  vs_bar <- letExp (baseString vs ++ "_bar") $ Op $ Screma n [is] $ mapSOAC lam_vsbar
  updateAdj vs vs_bar