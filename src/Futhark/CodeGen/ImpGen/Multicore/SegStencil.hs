{-# LANGUAGE TupleSections #-}
module Futhark.CodeGen.ImpGen.Multicore.SegStencil
  ( compileSegStencil
  )
where

import Control.Monad
import Data.List (transpose)

import qualified Futhark.CodeGen.ImpCode.Multicore as Imp
import Futhark.CodeGen.ImpGen
import Futhark.CodeGen.ImpGen.Multicore.Base
import Futhark.IR.MCMem

import Debug.Trace (trace)

compileSegStencil ::
  Pattern MCMem ->
  SegSpace ->
  StencilOp MCMem ->
  KernelBody MCMem ->
  TV Int32 ->
  MulticoreGen Imp.Code
compileSegStencil pat space sten kbody nsubtasks = collect $ do
  emit $ Imp.DebugPrint "SegStencil" Nothing
  let sten_idxs = stencilIndexes sten
      sten_lam = stencilOp sten
      arrs = stencilArrays sten
      -- [ret_tp]   = lambdaReturnType sten_lam
      kbres = map kernelResultSubExp $ kernelBodyResult kbody
      (const_params, sten_params) = splitAt (length kbres) (lambdaParams sten_lam)
      (is, ns) = unzip $ unSegSpace space
      ns' = map toInt64Exp ns

  iter <- dPrim "iter" $ IntType Int64

  body <- collect $ do
    zipWithM_ dPrimV_ is $ unflattenIndex ns' $ tvExp iter
    sComment "kernel body" $
      compileStms mempty (kernelBodyStms kbody) $ do
        -- create expressions for actual (bounded) indices
        -- let idxs = flip map (zip sten_idxs ns') $ \(idxs', n') ->
        --       flip map idxs' $ \idx -> sMin64 (n' - 1) (sMax64 0 (tvExp iter + fromInteger idx))
        let idxs = stencilIdxs (tvExp iter) (zip sten_idxs ns')
        let idxs_with_vnames = concatMap (\vn -> map (vn,) (transpose idxs)) arrs

        dLParams sten_params
        let names = ["a", "b", "c", "x", "y", "z"]
        forM_ (zip3 sten_params idxs_with_vnames names) $ \(param, (arr, idxs'), name) -> do
          forM_ idxs' $ \idx -> emit $ Imp.DebugPrint ("point " ++ name ++ " param " ++ (show $ paramName param) ++ ": ") $ Just (untyped idx)
          copyDWIMFix (paramName param) [] (Var arr) idxs'

        compileStms mempty (bodyStms $ lambdaBody sten_lam) $
          zipWithM_ (compileThreadResult space) (patternElements pat) $
            map (Returns ResultMaySimplify) $ bodyResult $ lambdaBody sten_lam
          

  free_params <- freeParams body [segFlat space, tvVar iter]
  let (body_allocs, body') = extractAllocations body
  emit $ Imp.Op $ Imp.ParLoop "stencil" (tvVar iter) body_allocs body' mempty free_params $ segFlat space

stencilIdxs ::
  Imp.TExp Int64 ->
  [([Integer], Imp.TExp Int64)] -> 
  [[Imp.TExp Int64]]
stencilIdxs flat_iter [] = error "Impossible! 0-dimensional array???"
stencilIdxs flat_iter [(idxs, n)] =
  let idxs' = flip map idxs $ \idx -> sMin64 (n - 1) (sMax64 0 (flat_iter + fromInteger idx))
  in [idxs']
stencilIdxs flat_iter ((idxs, n):rest) =
  let inner = product $ map snd rest
      iter = TPrimExp $ BinOpExp (SDiv Int64 Safe) (untyped flat_iter) (untyped inner)
      elems = TPrimExp $ BinOpExp (Mul Int64 OverflowWrap) (untyped iter) (untyped inner)
      inner_iter = TPrimExp $ BinOpExp (Sub Int64 OverflowWrap) (untyped flat_iter) (untyped elems)
      idxs' = flip map idxs $ \idx -> sMin64 (n - 1) (sMax64 0 (iter + fromInteger idx))
  in idxs' : stencilIdxs inner_iter rest
