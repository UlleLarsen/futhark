module Futhark.AD.Rev.Scan (diffScan, diffScanVec) where

import Control.Monad
import Futhark.AD.Rev.Monad
import Futhark.Analysis.PrimExp.Convert
import Futhark.Builder
import Futhark.IR.SOACS
import Futhark.Tools
import Futhark.Transform.Rename
import Data.List (transpose)

data FirstOrSecond = WrtFirst | WrtSecond

-- computes `d(x op y)/dx` or d(x op y)/dy
mkScanAdjointLam :: VjpOps -> Lambda SOACS -> FirstOrSecond -> [SubExp] -> ADM (Lambda SOACS)
mkScanAdjointLam ops lam0 which adjs = do
  let len = length $ lambdaReturnType lam0
  lam <- renameLambda lam0
  let p2diff =
        case which of
          WrtFirst -> take len $ lambdaParams lam
          WrtSecond -> drop len $ lambdaParams lam
  vjpLambda ops (fmap AdjVal adjs) (map paramName p2diff) lam

identityM :: Int -> Type -> ADM [[SubExp]]
identityM n t =
  traverse (letSubExps "id") $ [ [if i == j then oneExp t else zeroExp t | i <- [1..n]] | j <- [1..n]]

-- Should generate something like:
-- `\ j -> let i = n - 1 - j
--         if i < n-1 then ( ys_adj[i], df2dx ys[i] xs[i+1]) else (0,1) )`
-- where `ys` is  the result of scan
--       `xs` is  the input  of scan
--       `ys_adj` is the known adjoint of ys
--       `j` draw values from `iota n`
mkScanFusedMapLam :: VjpOps -> SubExp -> Lambda SOACS -> [VName] -> [VName] -> [VName] -> ADM (Lambda SOACS)
mkScanFusedMapLam ops w scn_lam xs ys ys_adj = do
  ys_ts <- traverse lookupType ys
  idmat <- identityM (length ys) $ rowType $ head ys_ts
  lams <- traverse (mkScanAdjointLam ops scn_lam WrtFirst) idmat
  par_i <- newParam "i" $ Prim int64
  let i = paramName par_i
  mkLambda [par_i] $
    fmap varsRes . letTupExp "x"
      =<< eIf
        (toExp $ le64 i .==. 0)
        ( buildBody_ $ do
            zs <- mapM (letSubExp "ct_zero" . zeroExp . rowType) ys_ts
            pure $ subExpsRes $ zs  ++ concat idmat
        )
        ( buildBody_ $ do
            j <- letSubExp "j" =<< toExp (pe64 w - (le64 i + 1))
            j1 <- letSubExp "j1" =<< toExp (pe64 w - le64 i)
            let index idx arr t = BasicOp $ Index arr $ fullSlice t [DimFix idx]
            y_s <- forM (zip ys_adj ys_ts) $ \(y_, t) ->
              letSubExp (baseString y_ ++ "_j") $ index j y_ t
            let args = map pure $ zipWith (index j) ys ys_ts ++ zipWith (index j1) xs ys_ts
            lam_rs <- traverse (`eLambda` args) lams

            pure $ subExpsRes y_s ++ concat (transpose lam_rs)
        )

splitEvery :: Int -> [a] -> [[a]]
splitEvery _ [] = []
splitEvery n list = first : splitEvery n rest
  where
    (first,rest) = splitAt n list

matrixMul :: [PrimExp VName] -> [PrimExp VName] -> Int -> PrimType -> [PrimExp VName]
matrixMul m1 m2 d t =
  let mat1 = splitEvery d m1
      mat2t = transpose $ splitEvery d m2
      zero = primExpFromSubExp t $ Constant $ blankPrimValue t
  in concat [[foldl (~+~) zero $ zipWith (~*~) r q | q <- mat2t ] | r <- mat1]

matrixVecMul :: [PrimExp VName] -> [PrimExp VName] -> Int -> PrimType -> [PrimExp VName]
matrixVecMul m v d t =
  let mat = splitEvery d m
      zero = primExpFromSubExp t $ Constant $ blankPrimValue t
  in [foldl (~+~) zero $ zipWith (~*~) v r | r <- mat]

vectorAdd :: [PrimExp VName] -> [PrimExp VName] -> [PrimExp VName]
vectorAdd = zipWith (~+~)

-- \(a1, b1) (a2, b2) -> (a2 + b2 * a1, b2 * b1)
mkScanLinFunO :: Type -> Int -> ADM (Scan SOACS)
mkScanLinFunO t d = do
  let pt = elemType t
  zeros <- replicateM d $ letSubExp "zeros" $ zeroExp $ rowType t
  idmat <- identityM d $ Prim pt
  a1s <- replicateM d $ newVName "a1"
  b1s <- replicateM (d*d) $ newVName "b1"
  a2s <- replicateM d $ newVName "a2"
  b2s <- replicateM (d*d) $ newVName "b2"
  let pet = primExpFromSubExp pt . Var
  lam <- mkLambda (map (\v -> Param mempty v (rowType t)) (a1s ++ b1s ++ a2s ++ b2s)) . fmap subExpsRes $ do
    let [a1s',b1s',a2s',b2s'] = (fmap . fmap) pet [a1s,b1s,a2s,b2s]
    let x1 = matrixVecMul b2s' a1s' d pt
    let x2 = a2s' `vectorAdd` x1
    let x3 = matrixMul b2s' b1s' d pt
    traverse (letSubExp "r" <=< toExp) $ x2 ++ x3

  return $ Scan lam $ zeros ++ concat idmat

-- build the map following the scan with linear-function-composition:
-- for each (ds,cs) length-n array results of the scan, combine them as:
--    `let rs = map2 (\ d_i c_i -> d_i + c_i * y_adj[n-1]) d c |> reverse`
-- but insert explicit indexing to reverse inside the map.
mkScan2ndMaps :: SubExp -> Int -> (Type, [VName], ([VName], [VName])) -> ADM [VName]
mkScan2ndMaps w d (arr_tp, y_adj, (ds, cs)) = do
  nm1 <- letSubExp "nm1" =<< toExp (pe64 w - 1)
  y_adj_last <-
    traverse (\adj ->
      letExp (baseString adj ++ "_last") $
        BasicOp $ Index adj $ fullSlice arr_tp [DimFix nm1]) y_adj

  par_i <- newParam "i" $ Prim int64
  lam <- mkLambda [par_i] $ do
    let i = paramName par_i
    j <- letSubExp "j" =<< toExp (pe64 w - (le64 i + 1))
    dj <- traverse (\dd ->
      letExp (baseString dd ++ "_dj") $
        BasicOp $ Index dd $ fullSlice arr_tp [DimFix j]) ds
    cj <- traverse (\c ->
      letExp (baseString c ++ "_cj") $
        BasicOp $ Index c $ fullSlice arr_tp [DimFix j]) cs

    let pet = primExpFromSubExp (elemType arr_tp) . Var
    fmap subExpsRes $ do
      let [dj',cj',y_adj'] = (fmap . fmap) pet [dj, cj, y_adj_last]
      let x1 = matrixVecMul cj' y_adj' d $ elemType arr_tp
      let x2 = dj' `vectorAdd` x1
      traverse (letSubExp "r" <=< toExp) x2

  iota <- letExp "iota" $ BasicOp $ Iota w (intConst Int64 0) (intConst Int64 1) Int64
  letTupExp "after_scan" $ Op (Screma w [iota] (ScremaForm [] [] lam))

-- perform the final map, which is fusable with the maps obtained from `mkScan2ndMaps`
-- let xs_contribs =
--    map3 (\ i a r -> if i==0 then r else (df2dy (ys[i-1]) a) \bar{*} r)
--         (iota n) xs rs
mkScanFinalMap :: VjpOps -> SubExp -> Int -> Lambda SOACS -> [VName] -> [VName] -> [VName] -> ADM [VName]
mkScanFinalMap ops w d scan_lam xs ys rs = do
  let eltps = lambdaReturnType scan_lam
  idmat <- identityM (length ys) $ head eltps
  lams <- traverse (mkScanAdjointLam ops scan_lam WrtSecond) idmat
  par_i <- newParam "i" $ Prim int64
  let i = paramName par_i
  par_x <- zipWithM (\x -> newParam (baseString x ++ "_par_x")) xs eltps
  par_r <- zipWithM (\r -> newParam (baseString r ++ "_par_r")) rs eltps

  map_lam <-
    mkLambda (par_i : par_x ++ par_r) $
      fmap varsRes . letTupExp "scan_contribs"
        =<< eIf
          (toExp $ le64 i .==. 0)
          (resultBodyM $ map (Var . paramName) par_r)
          ( buildBody_ $ do
              im1 <- letSubExp "im1" =<< toExp (le64 i - 1)
              ys_im1 <- forM ys $ \y -> do
                y_t <- lookupType y
                letSubExp (baseString y ++ "_last") $ BasicOp $ Index y $ fullSlice y_t [DimFix im1]

              let args = map eSubExp $ ys_im1 ++ map (Var . paramName) par_x
              lam_rs <-
                mapM (letExp "const" . BasicOp . SubExp . resSubExp) . concat . transpose
                  =<< traverse (`eLambda` args) lams
              let pt = elemType $ head eltps
              let pet = primExpFromSubExp pt . Var
              fmap subExpsRes $ do
                let [lam_rs',r'] = (fmap . fmap) pet [lam_rs, fmap paramName par_r]
                let x1 = matrixVecMul lam_rs' r' d pt
                traverse (letSubExp "r" <=< toExp) x1
          )

  iota <- letExp "iota" $ BasicOp $ Iota w (intConst Int64 0) (intConst Int64 1) Int64
  letTupExp "scan_contribs" $ Op (Screma w (iota : xs ++ rs) (ScremaForm [] [] map_lam))

diffScan :: VjpOps -> [VName] -> SubExp -> [VName] -> Scan SOACS -> ADM ()
diffScan ops ys w as scan = do
  let d = length as
  ys_adj <- mapM lookupAdjVal ys
  as_ts <- mapM lookupType as
  map1_lam <- mkScanFusedMapLam ops w (scanLambda scan) as ys ys_adj
  scans_lin_fun_o <- mkScanLinFunO (head as_ts) d
  iota <-
    letExp "iota" $ BasicOp $ Iota w (intConst Int64 0) (intConst Int64 1) Int64
  r_scan <-
    letTupExp "adj_ctrb_scan" $
      Op (Screma w [iota] (ScremaForm [scans_lin_fun_o] [] map1_lam))
  red_nms <- mkScan2ndMaps w d (head as_ts, ys_adj, splitAt d r_scan)
  as_contribs <- mkScanFinalMap ops w d (scanLambda scan) as ys red_nms
  zipWithM_ updateAdj as as_contribs

diffScanVec :: VjpOps -> [VName] -> StmAux () -> SubExp -> Lambda SOACS ->
                 [SubExp] -> [VName] -> ADM () -> ADM ()
diffScanVec ops ys aux w lam ne as m = do
  --ts <- traverse lookupType as

  stmts <- collectStms_ $ do
    rank <- arrayRank <$> lookupType (head as)
    let rear = [1,0] ++ drop 2 [0..rank-1]

    transp_as <- traverse (\a ->
      letExp (baseString a ++ "_transp") $ BasicOp $ Rearrange rear a) as

    ts <- traverse lookupType transp_as
    let n = arraysSize 0 ts

    as_par <- traverse (newParam "as_par" . rowType) ts
    ne_par <- traverse (newParam "ne_par") $ lambdaReturnType lam

    scan_form <- scanSOAC [Scan lam (map (Var . paramName) ne_par)]

    map_lam <- mkLambda (as_par ++ ne_par) $
      fmap varsRes . letTupExp "map_res" $
        Op $ Screma w (map paramName as_par) scan_form

    transp_ys <- letTupExp "trans_ys" $
      Op $ Screma n (transp_as ++ subExpVars ne) $ mapSOAC map_lam

    zipWithM (\y x ->
      auxing aux $ letBindNames [y] $
        BasicOp $ Rearrange rear x) ys transp_ys

  foldr (vjpStm ops) m stmts