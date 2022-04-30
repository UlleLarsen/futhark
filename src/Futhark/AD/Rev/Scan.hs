module Futhark.AD.Rev.Scan (diffScan, diffScanVec, diffScanAdd) where

import Control.Monad
import Futhark.AD.Rev.Monad
import Futhark.Analysis.PrimExp.Convert
import Futhark.Builder
import Futhark.IR.SOACS
import Futhark.Tools
import Futhark.Transform.Rename
import Data.List (transpose)
import Futhark.IR.SOACS.Simplify (simplifyLambda)

data FirstOrSecond = WrtFirst | WrtSecond

splitEvery :: Int -> [a] -> [[a]]
splitEvery _ [] = []
splitEvery n list = first : splitEvery n rest
  where
    (first,rest) = splitAt n list

identityM :: Int -> Type -> ADM [[SubExp]]
identityM n t =
  traverse (letSubExps "id") $ [ [if i == j then oneExp t else zeroExp t | i <- [1..n]] | j <- [1..n]]

matrixMul :: [[PrimExp VName]] -> [[PrimExp VName]] -> PrimType -> [[PrimExp VName]]
matrixMul m1 m2 t =
  let zero = primExpFromSubExp t $ Constant $ blankPrimValue t
  in [[foldl (~+~) zero $ zipWith (~*~) r q | q <- transpose m2 ] | r <- m1]

matrixVecMul :: [[PrimExp VName]] -> [PrimExp VName] -> PrimType -> [PrimExp VName]
matrixVecMul m v t =
  let zero = primExpFromSubExp t $ Constant $ blankPrimValue t
  in [foldl (~+~) zero $ zipWith (~*~) v r | r <- m]

vectorAdd :: [PrimExp VName] -> [PrimExp VName] -> [PrimExp VName]
vectorAdd = zipWith (~+~)

orderArgs :: Special -> [a] -> [[a]]
orderArgs s lst =
  let d = div (length lst) $ specialScans s
  in splitEvery d lst

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

-- Should generate something like:
-- `\ j -> let i = n - 1 - j
--         if i < n-1 then ( ys_adj[i], df2dx ys[i] xs[i+1]) else (0,1) )`
-- where `ys` is  the result of scan
--       `xs` is  the input  of scan
--       `ys_adj` is the known adjoint of ys
--       `j` draw values from `iota n`
mkScanFusedMapLam :: VjpOps -> SubExp -> Lambda SOACS -> [VName] -> [VName] ->
                       [VName] -> Special -> ADM (Lambda SOACS)
mkScanFusedMapLam ops w scn_lam xs ys ys_adj s = do
  let sc = specialCase s
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
            let zso = orderArgs s zs
            let ido = orderArgs s $ case_jac sc idmat
            pure $ subExpsRes $ concat $ zipWith (++) zso $ fmap concat ido
        )
        ( buildBody_ $ do
            j <- letSubExp "j" =<< toExp (pe64 w - (le64 i + 1))
            j1 <- letSubExp "j1" =<< toExp (pe64 w - le64 i)
            let index idx arr t = BasicOp $ Index arr $ fullSlice t [DimFix idx]
            y_s <- forM (zip ys_adj ys_ts) $ \(y_, t) ->
              letSubExp (baseString y_ ++ "_j") $ index j y_ t

            let args = fmap pure $ zipWith (index j) ys ys_ts ++ zipWith (index j1) xs ys_ts
            lam_rs <- traverse (`eLambda` args) lams

            let yso = orderArgs s $ subExpsRes y_s
            let jaco = orderArgs s $ case_jac sc $ transpose lam_rs

            pure $ concat $ zipWith (++) yso $ fmap concat jaco
        )
  where
    case_jac :: SpecialCase -> [[a]] -> [[a]]
    case_jac Generic jac = jac
    case_jac ZeroQuadrant jac =
      let half = div (length jac) 2
          (top,bot) = splitAt half jac
          h11 = take half <$> top
          h22 = drop half <$> bot
      in h11 ++ h22
    case_jac MatrixMul jac =
      let half = div (length jac) 2
      in take half <$> take half jac

-- a1 a2 b -> a2 + b * a1
linFunT0 :: [PrimExp VName] -> [PrimExp VName] -> [[PrimExp VName]] -> Special -> Int -> PrimType -> [PrimExp VName]
linFunT0 a1 a2 b s d pt =
  let t = case specialCase s of
            MatrixMul ->
                let (h1,h2) = splitAt (div d 2) a1
                in matrixVecMul b h1 pt ++ matrixVecMul b h2 pt
            _ -> matrixVecMul b a1 pt
    in a2 `vectorAdd` t

-- \(a1, b1) (a2, b2) -> (a2 + b2 * a1, b2 * b1)
mkScanLinFunO :: Type -> Int -> Special -> ADM (Scan SOACS)
mkScanLinFunO t d s = do
  let pt = elemType t
  neu_elm <- mkNeutral $ specialNeutral s
  let (as,bs) = specialParams s
  (a1s,b1s,a2s,b2s) <- mkParams (as,bs)
  let pet = primExpFromSubExp pt . Var
  let (_,n) = specialNeutral s

  lam <- mkLambda (map (\v -> Param mempty v (rowType t)) (a1s ++ b1s ++ a2s ++ b2s)) . fmap subExpsRes $ do
    let [a1s',b1s',a2s',b2s'] = (fmap . fmap) pet [a1s,b1s,a2s,b2s]
    let (b1sm,b2sm) = (splitEvery n b1s',splitEvery n b2s')

    let t0 = linFunT0 a1s' a2s' b2sm s d pt
    let t1 = concat $ matrixMul b2sm b1sm pt
    traverse (letSubExp "r" <=< toExp) $ t0 ++ t1

  return $ Scan lam neu_elm
  where
    mkNeutral (a,b) = do
      zeros <- replicateM a $ letSubExp "zeros" $ zeroExp $ rowType t
      idmat <- identityM b $ Prim $ elemType t
      pure $ zeros ++ concat idmat

    mkParams (a,b) = do
      a1s <- replicateM a $ newVName "a1"
      b1s <- replicateM b $ newVName "b1"
      a2s <- replicateM a $ newVName "a2"
      b2s <- replicateM b $ newVName "b2"
      pure (a1s,b1s,a2s,b2s)


-- build the map following the scan with linear-function-composition:
-- for each (ds,cs) length-n array results of the scan, combine them as:
--    `let rs = map2 (\ d_i c_i -> d_i + c_i * y_adj[n-1]) d c |> reverse`
-- but insert explicit indexing to reverse inside the map.
mkScan2ndMaps :: SubExp -> Int -> (Type, [[VName]], [([VName], [VName])]) -> Special -> ADM [VName]
mkScan2ndMaps w d (arr_tp, y_adjs, dscs) s = do
  let pt = elemType arr_tp
  let (_,n) = specialNeutral s

  nm1 <- letSubExp "nm1" =<< toExp (pe64 w - 1)

  par_i <- newParam "i" $ Prim int64
  lam <- mkLambda [par_i] $ concat <$> zipWithM (\y_adj (ds,cs) -> do
    let i = paramName par_i
    j <- letSubExp "j" =<< toExp (pe64 w - (le64 i + 1))

    y_adj_last <-
      traverse (\adj ->
        letExp (baseString adj ++ "_last") $
          BasicOp $ Index adj $ fullSlice arr_tp [DimFix nm1]) y_adj

    dj <- traverse (\dd ->
      letExp (baseString dd ++ "_dj") $
        BasicOp $ Index dd $ fullSlice arr_tp [DimFix j]) ds
    cj <- traverse (\c ->
      letExp (baseString c ++ "_cj") $
        BasicOp $ Index c $ fullSlice arr_tp [DimFix j]) cs

    let pet = primExpFromSubExp (elemType arr_tp) . Var
    fmap subExpsRes $ do
      let [dj',cj',y_adj'] = (fmap . fmap) pet [dj, cj, y_adj_last]
      let cjm = splitEvery n cj'
      let t0 = linFunT0 y_adj' dj' cjm s d pt
      traverse (letSubExp "r" <=< toExp) t0
    ) y_adjs dscs

  iota <- letExp "iota" $ BasicOp $ Iota w (intConst Int64 0) (intConst Int64 1) Int64
  letTupExp "after_scan" $ Op $ Screma w [iota] $ mapSOAC lam

-- perform the final map, which is fusable with the maps obtained from `mkScan2ndMaps`
-- let xs_contribs =
--    map3 (\ i a r -> if i==0 then r else (df2dy (ys[i-1]) a) \bar{*} r)
--         (iota n) xs rs
mkScanFinalMap :: VjpOps -> SubExp -> Lambda SOACS -> [VName] -> [VName] -> [VName] -> ADM [VName]
mkScanFinalMap ops w scan_lam xs ys rs = do
  let eltps = lambdaReturnType scan_lam

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
              lam <- mkScanAdjointLam ops scan_lam WrtSecond $ fmap (Var . paramName) par_r

              im1 <- letSubExp "im1" =<< toExp (le64 i - 1)
              ys_im1 <- forM ys $ \y -> do
                y_t <- lookupType y
                letSubExp (baseString y ++ "_last") $ BasicOp $ Index y $ fullSlice y_t [DimFix im1]

              let args = map eSubExp $ ys_im1 ++ map (Var . paramName) par_x
              eLambda lam args
          )

  iota <- letExp "iota" $ BasicOp $ Iota w (intConst Int64 0) (intConst Int64 1) Int64
  letTupExp "scan_contribs" $ Op $ Screma w (iota : xs ++ rs) $ mapSOAC map_lam

data SpecialCase =
   Generic
 | ZeroQuadrant
 | MatrixMul
 deriving Show

data Special = Special
  { specialNeutral :: (Int,Int),
    specialParams :: (Int,Int),
    specialCase :: SpecialCase
  }
  deriving Show

specialScans :: Special -> Int
specialScans (Special _ _ ZeroQuadrant) = 2
specialScans _ = 1

cases :: Int -> Type -> [[Exp SOACS]] -> Special
cases d t mat
  | even d,
    half <- div d 2,
    (top,bot) <- splitAt half $ splitAt half <$> mat,
    (h11,h12) <- unzip top,
    (h21,h22) <- unzip bot,
    all (zeroExp t ==) (concat $ h12 ++ h21) =
      if h11 == h22
      then Special (d,half) (d,div (d*d) 4) MatrixMul
      else Special (half,half) (half,div (d*d) 4) ZeroQuadrant
cases d _ _ = Special (d,d) (d,d*d) Generic

identifyCase :: VjpOps -> Lambda SOACS -> ADM Special
identifyCase ops lam = do
  let t = lambdaReturnType lam
  let d = length t
  idmat <- identityM d $ head t
  lams <- traverse (mkScanAdjointLam ops lam WrtFirst) idmat

  par1 <- traverse (newParam "tmp1") t
  par2 <- traverse (newParam "tmp2") t
  jac_lam <- mkLambda (par1 ++ par2) $ do
    let args = fmap eParam $ par1 ++ par2
    lam_rs <- traverse (`eLambda` args) lams

    pure $ concat (transpose lam_rs)

  simp <- simplifyLambda jac_lam
  let jac = splitEvery d $ fmap (BasicOp . SubExp . resSubExp) $ bodyResult $ lambdaBody simp
  pure $ cases d (head t) jac

diffScan :: VjpOps -> [VName] -> SubExp -> [VName] -> Scan SOACS -> ADM ()
diffScan ops ys w as scan = do
  sc <- identifyCase ops (scanLambda scan)
  let d = length as
  ys_adj <- mapM lookupAdjVal ys
  as_ts <- mapM lookupType as
  map1_lam <- mkScanFusedMapLam ops w (scanLambda scan) as ys ys_adj sc
  scans_lin_fun_o <- mkScanLinFunO (head as_ts) d sc
  scan_lams <- mkScans (specialScans sc) scans_lin_fun_o
  iota <-
    letExp "iota" $ BasicOp $ Iota w (intConst Int64 0) (intConst Int64 1) Int64
  r_scan <-
    letTupExp "adj_ctrb_scan" $
      Op $ Screma w [iota] $ ScremaForm scan_lams [] map1_lam
  red_nms <- mkScan2ndMaps w d (head as_ts, orderArgs sc ys_adj, splitScanRes sc r_scan d) sc

  as_contribs <- mkScanFinalMap ops w (scanLambda scan) as ys red_nms
  zipWithM_ updateAdj as as_contribs
  where
    mkScans :: Int -> Scan SOACS -> ADM [Scan SOACS]
    mkScans d s =
      replicateM d $ do
        lam' <- renameLambda $ scanLambda s
        pure $ Scan lam' $ scanNeutral s

    splitScanRes sc res d =
      splitAt (div d $ specialScans sc) <$> orderArgs sc res

diffScanVec :: VjpOps -> [VName] -> StmAux () -> SubExp -> Lambda SOACS ->
                 [SubExp] -> [VName] -> ADM () -> ADM ()
diffScanVec ops ys aux w lam ne as m = do
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

diffScanAdd :: VjpOps -> VName -> SubExp -> Lambda SOACS -> SubExp -> VName -> ADM ()
diffScanAdd _ops ys n lam' ne as = do
  lam <- renameLambda lam'
  ys_bar <- lookupAdjVal ys

  map_scan <- rev_arr_lam ys_bar

  iota <- letExp "iota" $
    BasicOp $ Iota n (intConst Int64 0) (intConst Int64 1) Int64

  scan_res <- letExp "res_rev" $
    Op $ Screma n [iota] $ ScremaForm [Scan lam [ne]] [] map_scan

  rev_lam <- rev_arr_lam scan_res
  contrb <- letExp "contrb" $
    Op $ Screma n [iota] $ mapSOAC rev_lam

  updateAdj as contrb
  where
    rev_arr_lam :: VName -> ADM (Lambda SOACS)
    rev_arr_lam arr = do
      t <- lookupType arr
      par_i <- newParam "i" $ Prim int64
      mkLambda [par_i] $ do
        nmim1 <- letSubExp "nmim1" =<<
          toExp (pe64 n - le64 (paramName par_i) - 1)
        a <- letExp "ys_bar_rev" $
          BasicOp $ Index arr $ fullSlice t [DimFix nmim1]
        pure [varRes a]