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

getBinOpPlus :: PrimType -> BinOp
getBinOpPlus (IntType x) = Add x OverflowUndef
getBinOpPlus (FloatType f) = FAdd f
getBinOpPlus _ = error "In getBinOpMul, Hist.hs: input Cert not supported"

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
  auxing aux $ letBindNames [x, x_inds] $ Op $ Hist n [is, vs, iota_n] [hist_op] f'

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