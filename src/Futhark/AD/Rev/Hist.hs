{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module Futhark.AD.Rev.Hist
  ( diffMinMaxHist,
    diffMulHist,
  )
where

import Futhark.AD.Rev.Monad
import Futhark.Analysis.PrimExp.Convert
import Futhark.Builder
import Futhark.IR.SOACS
import Futhark.Tools
import Futhark.Transform.Rename

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

--
-- special case of histogram with min/max as operator.
-- Original, assuming `is: [n]i64` and `dest: [w]btp`
--     let histo = reduce_by_index dest max ne is vs
-- Forward trace:
--     let (histo, histo_inds) = map3 (\i v j -> (i,(v,j))) is vs (iota n)
--                       |> reduce_by_index dest argmax (ne,-1)
--
-- Reverse trace:
--     dest += map (\m_ind el -> if m_ind == -1 then el else 0
--                 ) histo_inds histo_bar

--     vs_ctrbs = map2 (\ i h_v -> if i == -1
--                                 then 0
--                                 else vs_bar[i]+h_v
--                     ) histo_inds histo_bar
--     vs_bar <- scatter vs_bar histo_inds vs_ctrbs
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

  x_adj <- lookupAdjVal x

  x_ind_dst <- newParam "x_ind_param" $ Prim int64
  x_adj_dst <- newParam "x_adj_param" $ Prim t
  dst_lam <-
    mkLambda [x_ind_dst, x_adj_dst] $
      fmap varsRes . letTupExp "res" 
        =<< eIf
          (eCmpOp (CmpEq int64) (eParam x_ind_dst) (eSubExp $ intConst Int64 (-1)))
          (eBody $ return $ eParam x_adj_dst)
          (eBody $ return $ eSubExp $ Constant $ blankPrimValue t)

  dst_bar <-
    letExp (baseString dst ++ "_bar") $
      Op $
        Screma w [x_inds, x_adj] $ mapSOAC dst_lam

  updateAdj dst dst_bar

  vs_adj <- lookupAdjVal vs

  x_ind_vs <- newParam "x_ind_param" $ Prim int64
  x_adj_vs <- newParam "x_adj_param" $ Prim t
  vs_lam <-
    mkLambda [x_ind_vs, x_adj_vs] $
      fmap varsRes . letTupExp "res" 
        =<< eIf
          (eCmpOp (CmpEq int64) (eParam x_ind_vs) (eSubExp $ intConst Int64 (-1)))
          (eBody $ return $ eSubExp $ Constant $ blankPrimValue t)
          (eBody $ return $ do
            vs_bar_i <-
                    letSubExp (baseString vs_adj ++ "_el") $
                      BasicOp $
                        Index vs_adj $ Slice [DimFix $ Var $ paramName x_ind_vs]
            eBinOp (getBinOpPlus t) (eParam x_adj_vs) (eSubExp vs_bar_i))

  vs_bar_p <-
    letExp (baseString vs ++ "_partial") $
      Op $
        Screma w [x_inds, x_adj] $ mapSOAC vs_lam

  f'' <- mkIdentityLambda [Prim int64, Prim t]
  let scatter_soac = Scatter w [x_inds, vs_bar_p] f'' [(Shape [n], 1, vs_adj)]
  vs_bar' <- letExp (baseString vs ++ "_bar") $ Op scatter_soac
  insAdj vs vs_bar'

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
        zr_cts <- newVName "zr_cts"
        pr_bar <- newVName "pr_bar"
        nz_prd <- newVName "nz_prd"
        letBindNames [zr_cts] $ BasicOp $ Index zr_counts j
        letBindNames [pr_bar] $ BasicOp $ Index part_bar j
        letBindNames [nz_prd] $ BasicOp $ Index nz_prods j

        eIf
          (eCmpOp (CmpEq int64) (eSubExp $ intConst Int64 0) (eSubExp $ Var zr_cts))
          (eBody $ return $ eBinOp mul (eSubExp $ Var pr_bar) $ eBinOp (getBinOpDiv t) (eSubExp $ Var nz_prd) $ eParam a_param) 
          (eBody $ return $ eIf 
                              (eBinOp LogAnd (eCmpOp (CmpEq int64) (eSubExp $ intConst Int64 1) (eSubExp $ Var zr_cts)) 
                                             (eCmpOp (CmpEq t) (eSubExp $ Constant $ blankPrimValue t) $ eParam a_param))
                              (eBody $ return $ eBinOp mul (eSubExp $ Var nz_prd) (eSubExp $ Var pr_bar)) 
                              (eBody $ return $ eSubExp $ Constant $ blankPrimValue t) 
          )
  vs_bar <- 
    letExp "vs_bar" $ Op $ Screma n [is, vs] $ mapSOAC lam_vsbar

  updateAdj vs vs_bar