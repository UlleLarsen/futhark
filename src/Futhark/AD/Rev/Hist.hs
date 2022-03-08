{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

module Futhark.AD.Rev.Hist
  ( diffMinMaxHist,
    diffMulHist,
    diffAddHist,
    diffHist,
  )
where

import Control.Monad
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

withinBounds :: [(SubExp, VName)] -> TPrimExp Bool VName
withinBounds [] = TPrimExp $ ValueExp (BoolValue True)
withinBounds [(q, i)] = (le64 i .<. pe64 q) .&&. (pe64 (intConst Int64 (-1)) .<. le64 i)
withinBounds (qi : qis) = withinBounds [qi] .&&. withinBounds qis

elseIf :: PrimType -> [(Builder SOACS Exp, Builder SOACS Exp)] -> [Builder SOACS Body] -> Builder SOACS Exp
elseIf t [(c1,c2)] [bt,bf] =
  eIf
    (eCmpOp (CmpEq t) c1 c2) bt bf
elseIf t ((c1,c2):cs) (bt:bs) =
  eIf
    (eCmpOp (CmpEq t) c1 c2) bt $
      eBody $ return $ elseIf t cs bs
elseIf _ _ _ = error "In elseIf, Hist.hs: input not supported"

-- \ds hs -> map2 lam ds hs
mkF' :: Lambda -> [Type] -> SubExp -> ADM ([VName], Lambda)
mkF' lam tps n = do
  lam' <- renameLambda lam

  ds_params <- traverse (newParam "ds_param") tps
  hs_params <- traverse (newParam "hs_param") tps
  let map_params = ds_params <> hs_params
  lam_map <- mkLambda map_params $
    fmap varsRes . letTupExp "map_f'" $
      Op $ Screma n (map paramName map_params) $ mapSOAC lam'

  pure (map paramName ds_params, lam_map)

-- \ls as rs ds -> map (\li ai ri di -> li `lam` ai `lam` ri `lam` di) ls as rs ds
mkF :: Lambda -> [Type] -> SubExp -> ADM ([VName], Lambda)
mkF lam tps n = do
  lam_l <- renameLambda lam
  lam_r <- renameLambda lam
  lam_d <- renameLambda lam
  let q = length $ lambdaReturnType lam
      (dps, lps) = splitAt q $ lambdaParams lam_l
      (ips, aps) = splitAt q $ lambdaParams lam_r
      (jps, rps) = splitAt q $ lambdaParams lam_d
  lam' <- mkLambda (dps <> lps <> aps <> rps) $ do
    lam_l_res <- bodyBind $ lambdaBody lam_l
    forM_ (zip ips lam_l_res) $ \(ip, SubExpRes cs se) ->
      certifying cs $ letBindNames [paramName ip] $ BasicOp $ SubExp se
    lam_r_res <- bodyBind $ lambdaBody lam_r
    forM_ (zip jps lam_r_res) $ \(ip, SubExpRes cs se) ->
      certifying cs $ letBindNames [paramName ip] $ BasicOp $ SubExp se
    bodyBind $ lambdaBody lam_d

  ls_params <- traverse (newParam "ls_param") tps
  as_params <- traverse (newParam "as_param") tps
  rs_params <- traverse (newParam "rs_param") tps
  ds_params <- traverse (newParam "ds_param") tps
  let map_params = ds_params <> ls_params <> as_params <> rs_params
  lam_map <- mkLambda map_params $
    fmap varsRes . letTupExp "map_f" $
      Op $ Screma n (map paramName map_params) $ mapSOAC lam'

  pure (map paramName as_params, lam_map)

--
-- special case of histogram with min/max as operator.
-- Original, assuming `is: [n]i64` and `dst: [w]btp`
--     let x = reduce_by_index dst minmax ne is vs
-- Forward sweep:
--     need to copy dst: reverse sweep might use it 7
--       (see ex. in reducebyindexminmax6.fut where the first map requires the original dst to be differentiated). 
--     let dst_cpy = copy dst
--     let (x, x_inds) = zip vs (iota n)
--                       |> reduce_by_index (dst_cpy,-1s) argminmax (ne,-1) is
--
-- Reverse sweep:
--     dst_bar += map2 (\i b -> if i == -1 
--                              then b 
--                              else 0
--                     ) x_inds x_bar

--     vs_ctrbs = map2 (\i b -> if i == -1
--                              then 0
--                              else vs_bar[i] + b
--                     ) x_inds x_bar
--     vs_bar <- scatter vs_bar x_inds vs_ctrbs
diffMinMaxHist ::
  VjpOps -> VName -> StmAux () -> SubExp -> BinOp -> SubExp -> VName -> VName -> SubExp -> SubExp -> VName -> ADM () -> ADM ()
diffMinMaxHist _ops x aux n minmax ne is vs w rf dst m = do
  let t = binOpType minmax

  dst_cpy <- letExp (baseString dst ++ "_copy") $ BasicOp $ Copy dst

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

  let hist_op = HistOp (Shape [w]) rf [dst_cpy, minus_ones] [ne, intConst Int64 (-1)] hist_lam
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
      fmap varsRes . letTupExp "dst_bar"
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
-- Forward sweep:
--     dst does not need to be copied: dst is not overwritten
--     let (ps, zs) = map (\v -> if x == 0 then (1,1) else (v,0)) vs
--     let non_zero_prod = reduce_by_index nes (*) ne is ps
--     let zero_count = reduce_by_index 0s (+) 0 is zs
--     let h_part = map2 (\p c -> if c == 0 then p else 0
--                       ) non_zero_prod zero_count
--     let x = map2 (*) dst h_part
--
-- Reverse sweep:
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
    letExp (baseString vs ++ "_bar") $ Op $ Screma n [is, vs] $ mapSOAC lam_vsbar

  updateAdj vs vs_bar

--
-- special case of histogram with add as operator.
-- Original, assuming `is: [n]i64` and `dst: [w]btp`
--     let x = reduce_by_index dst (+) ne is vs
-- Forward sweep:
--     need to copy dst: reverse sweep might use it 7
--       (see ex. in reducebyindexminmax6.fut where the first map requires the original dst to be differentiated). 
--     let dst_cpy = copy dst
--     let x = reduce_by_index dst_cpy (+) ne is vs
--
-- Reverse sweep:
--     dst_bar += x_bar
--
--     vs_bar += map (\i -> x_bar[i]) is
diffAddHist ::
  VjpOps -> VName -> StmAux () -> SubExp -> Lambda -> SubExp -> VName -> VName -> SubExp -> SubExp -> VName -> ADM () -> ADM ()
diffAddHist _ops x aux n add ne is vs w rf dst m = do
  let t = paramDec $ head $ lambdaParams add
   
  dst_cpy <- letExp (baseString dst ++ "_copy") $ BasicOp $ Copy dst

  f <- mkIdentityLambda [Prim int64, t]
  auxing aux $
    letBindNames [x] $
      Op $
        Hist n [is, vs] [HistOp (Shape [w]) rf [dst_cpy] [ne] add] f

  m

  x_bar <- lookupAdjVal x

  updateAdj dst x_bar

  x_type <- lookupType x
  ind_param <- newParam (baseString vs ++ "_ind") $ Prim int64
  lam_vsbar <-
      mkLambda [ind_param] $
        fmap varsRes . letTupExp "vs_bar" =<<
          eIf
            (toExp $ withinBounds $ return (w, paramName ind_param))
            (eBody $ return $ return $ BasicOp $ Index x_bar $ fullSlice x_type [DimFix $ Var $ paramName ind_param])
            (eBody $ return $ eSubExp ne)

  vs_bar <- letExp (baseString vs ++ "_bar") $ Op $ Screma n [is] $ mapSOAC lam_vsbar
  updateAdj vs vs_bar

--
-- a step in the radix sort implementation
-- it assumes the key we are sorting
-- after is [n]i64 and it is the first VName 
-- 
-- local def radix_sort_step [n] 't (xs: [n]t) (get_bit: i32 -> t -> i32)
--                                  (digit_n: i32): [n]t =
--   let num x = get_bit (digit_n+1) x * 2 + get_bit digit_n x
--   let pairwise op (a1,b1,c1,d1) (a2,b2,c2,d2) =
--     (a1 `op` a2, b1 `op` b2, c1 `op` c2, d1 `op` d2)
--   let bins = xs |> map num
--   let flags = bins |> map (\x -> if x == 0 then (1,0,0,0)
--                                  else if x == 1 then (0,1,0,0)
--                                  else if x == 2 then (0,0,1,0)
--                                  else (0,0,0,1))
--   let offsets = scan (pairwise (+)) (0,0,0,0) flags
--   let (na,nb,nc,_nd) = last offsets
--   let f bin (a,b,c,d) = match bin
--                         case 0 -> a-1
--                         case 1 -> na+b-1
--                         case 2 -> na+nb+c-1
--                         case _ -> na+nb+nc+d-1
--   let is = map2 f bins offsets
--   in scatter scratch is xs
radixSortStep :: [VName] -> [Type] -> SubExp -> SubExp -> Builder SOACS Exp
radixSortStep xs tps bit n = do
  let is = head xs

  num_param <- newParam "num" $ Prim int64
  num_lam <- mkLambda [num_param] $
    fmap varsRes . letTupExp "num_res" =<<
      eBinOp (Add Int64 OverflowUndef)
        (eBinOp (And Int64)
          (eBinOp (AShr Int64) (eParam num_param) (eSubExp bit))
          (iConst 1)
        )
        (eBinOp (Mul Int64 OverflowUndef)
          (iConst 2)
          (eBinOp (And Int64)
            (eBinOp (AShr Int64) (eParam num_param) (eBinOp (Add Int64 OverflowUndef) (eSubExp bit) (iConst 1)))
            (iConst 1)
          )
        )

  bins <- letExp "bins" $ Op $ Screma n [is] $ mapSOAC num_lam
  flag_param <- newParam "flag" $ Prim int64
  flag_lam <- mkLambda [flag_param] $
    fmap varsRes . letTupExp "flag_res" =<<
      elseIf int64 (map ((,) (eParam flag_param) . iConst) [0..2])
        (map (eBody . fmap iConst . (\i -> map (\j -> if i == j then 1 else 0) [0..3])) ([0..3] :: [Integer]))

  flags <- letTupExp "flags" $ Op $ Screma n [bins] $ mapSOAC flag_lam

  scan_params <- traverse (flip newParam $ Prim int64) ["a1","b1","c1","d1","a2","b2","c2","d2"]
  scan_lam <- mkLambda scan_params $
    fmap subExpsRes . letSubExps "scan_res" =<< do
        uncurry (zipWithM (eBinOp $ Add Int64 OverflowUndef)) $ splitAt 4 $ map eParam scan_params

  scan <- scanSOAC $ return $ Scan scan_lam $ map (intConst Int64) [0,0,0,0]
  offsets <- letTupExp "offsets" $ Op $ Screma n flags scan

  ind <- letSubExp "ind_last" =<< eBinOp (Sub Int64 OverflowUndef) (eSubExp n) (iConst 1)
  let i = Slice [DimFix ind]
  nabcd <- traverse newVName ["na","nb","nc","nd"]
  zipWithM_ (\abcd -> letBindNames [abcd] . BasicOp . flip Index i) nabcd offsets

  let vars = map Var nabcd
  map_params <- traverse (flip newParam $ Prim int64) ["bin","a","b","c","d"]
  map_lam <- mkLambda map_params $
    fmap varsRes . letTupExp "map_res" =<<
      elseIf int64 (map ((,) (eParam $ head map_params) . iConst) [0..2]) (
        zipWith (\j p ->
          eBody $ return $ do
            t <- letSubExp "t" =<< eBinOp (Sub Int64 OverflowUndef) (eParam p) (iConst 1)
            foldBinOp (Add Int64 OverflowUndef) (Constant $ blankPrimValue int64) (t : take j vars)
          )
          [0..3] (tail map_params))

  nis <- letExp "nis" $ Op $ Screma n (bins : offsets) $ mapSOAC map_lam

  ind_param <- newParam "ind_param" $ Prim int64
  scatter_params <- zipWithM newParam (map (flip (++) "_param" . baseString) xs) $ map rowType tps
  scatter_lam <- mkLambda (ind_param : scatter_params) $
    fmap subExpsRes . letSubExps "scatter_map_res" =<< do
      p1 <- replicateM (length scatter_params) $ eParam ind_param
      p2 <- traverse eParam scatter_params
      return $ p1 ++ p2

  scatter_dst <- traverse (\t -> letExp "scatter_dst" $ BasicOp $ Scratch (elemType t) (arrayDims t)) tps
  return $ Op $ Scatter n (nis : xs) scatter_lam $ zipWith (\t -> (,,) (Shape $ return $ arraySize 0 t) 1) tps scatter_dst
  where
    iConst c = eSubExp $ intConst Int64 c

--
-- the radix sort implementation
-- def radix_sort [n] 't (xs: [n]i64) =
--   let iters = if n == 0 then 0 else 32
--   in loop xs for i < iters do radix_sort_step xs i64.get_bit (i*2)
radixSort :: [VName] -> SubExp -> ADM [VName]
radixSort xs n = do
  iters <- letSubExp "iters" =<<
    eIf
      (eCmpOp (CmpEq int64) (eSubExp n) (eSubExp $ Constant $ blankPrimValue int64))
      (eBody $ return $ eSubExp $ Constant $ blankPrimValue int64)
      (eBody $ return $ eSubExp $ intConst Int64 32)

  types <- traverse lookupType xs
  params <- zipWithM (\x -> newParam (baseString x) . flip toDecl Nonunique) xs types
  i <- newVName "i"
  loopbody <- runBodyBuilder . localScope (scopeOfFParams params) $ eBody $ return $ do
    bit <- letSubExp "bit" =<<
      eBinOp (Mul Int64 OverflowUndef) (eSubExp $ Var i) (eSubExp $ intConst Int64 2)
    radixSortStep (map paramName params) types bit n

  letTupExp "sorted" $
    DoLoop
      (zip params $ map Var xs)
      (ForLoop i Int64 iters [])
      loopbody

radixSort' :: [VName] -> SubExp -> ADM [VName]
radixSort' xs n = do
  iota_n <-
    letExp "red_iota" $
      BasicOp $ Iota n (intConst Int64 0) (intConst Int64 1) Int64

  radres <- radixSort [head xs, iota_n] n
  let [is', iota'] = radres

  types <- traverse lookupType xs
  i_param <- newParam "i" $ Prim int64
  let slice = [DimFix $ Var $ paramName i_param]
  map_lam <- mkLambda [i_param] $
    fmap subExpsRes . letSubExps "sorted" $
      zipWith (\t -> BasicOp . flip Index (fullSlice t slice)) (tail types) (tail xs)

  sorted <- letTupExp "sorted" $ Op $ Screma n (tail radres) $ mapSOAC map_lam
  return $ iota' : is' : sorted

--
-- generic case of histogram.
-- Original, assuming `is: [n]i64` and `dst: [w]btp`
--     let xs = reduce_by_index dst op ne is as
-- Forward sweep:
--     let nes = replicate w ne
--     let h_part = reduce_by_index nes op ne is as
--     let xs = map2 op dst h_part
--
-- Reverse sweep:
--     dst_bar += f' dst h_part
--
--     let flag = map (\i -> if i == 0 then true else sis[i] != sis[i-1]) (iota n)
--     let ls = seg_scan_exe op (false, ne) sas
--     let rs = reverse (seg_scan_exe op (reverse sas))
--     let (f_bar, f_dst) = map (\i -> if i < w && -1 < w then (xs_bar[i], dst[i]) else (0,ne)) sis
--     let as_bar' = f f_dst ls as rs
--     as_bar += scatter (Scratch) siota as_bar'
--
-- Where:
--     siota is 'iota n' sorted wrt is
--     sis is 'is' sorted wrt is
--     sas is 'as' sorted wrt is
--     f' = vjpLambda xs_bar dst (\ds hs -> ds `op` hs)
--     f  = vjpLambda f_bar as (\ls as rs ds -> map (\li ai ri di -> li `op` ai `op` ri `op` di) ls as rs ds)
diffHist :: VjpOps -> [VName] -> StmAux () ->  SubExp -> Lambda -> [SubExp] -> [VName] -> [SubExp] -> SubExp -> [VName] -> ADM () -> ADM ()
diffHist ops xs aux n lam0 ne as w rf dst m = do
  as_type <- traverse lookupType $ tail as
  dst_type <- traverse lookupType dst

  nes <- traverse (letExp "new_dst" . BasicOp . Replicate (Shape $ return $ head w)) ne

  h_map <- mkIdentityLambda $ Prim int64 : map rowType as_type
  h_part <- traverse (newVName . flip (++) "_h_part" . baseString) xs
  auxing aux $
    letBindNames h_part $
      Op $
        Hist n as [HistOp (Shape w) rf nes ne lam0] h_map

  lam0' <- renameLambda lam0
  auxing aux $
    letBindNames xs $
      Op $ Screma (head w) (dst ++ h_part) $ mapSOAC lam0'

  m

  xs_bar <- traverse lookupAdjVal xs

  (dst_params, f') <- mkF' lam0 dst_type $ head w
  f'_adj <- vjpLambda ops (map adjFromVar xs_bar) dst_params f'

  dst_bar' <- eLambda f'_adj $ map (eSubExp . Var) $ dst ++ h_part
  dst_bar <- bindSubExpRes "dst_bar" dst_bar'
  zipWithM_ updateAdj dst dst_bar

  lam <- renameLambda lam0
  lam' <- renameLambda lam0

  sorted <- radixSort' as n
  let siota = head sorted
  let sis = head $ tail sorted
  let sas = drop 2 sorted

  iota_n <-
    letExp "iota" $ BasicOp $ Iota n se0 se1 Int64

  --map (\i -> if i == 0 then true else is[i] != is[i-1]) (iota n)
  par_i <- newParam "i" $ Prim int64
  flag_lam <- mkFlagLam par_i sis
  flag <- letExp "flag" $ Op $ Screma n [iota_n] $ mapSOAC flag_lam

  -- map (\i -> (if flag[i] then (true,ne) else (false,vs[i-1]), if i==0 || flag[n-i] then (true,ne) else (false,vs[n-i]))) (iota n)
  par_i' <- newParam "i" $ Prim int64
  let i = paramName par_i'
  g_lam <- mkLambda [par_i'] $
    fmap subExpsRes . letSubExps "scan_inps" =<< do
      im1 <- letSubExp "i_1" =<< toExp (le64 i - pe64 se1)
      nmi <- letSubExp "n_i" =<< toExp (pe64 n - le64 i)
      let s1 = [DimFix im1]
      let s2 = [DimFix nmi]

      -- flag array for left scan
      f1 <- letSubExp "f1" $ BasicOp $ Index flag $ Slice [DimFix $ Var i]

      r1 <- letTupExp' "r1" =<<
        eIf
          (eSubExp f1)
          (eBody $ fmap eSubExp ne)
          (eBody . fmap eSubExp =<<
            forM sas (\x -> do
              t <- lookupType x
              letSubExp (baseString x ++ "_elem_1") $
                BasicOp $ Index x $ fullSlice t s1
            )
          )

      -- tuple with right scan flag array 
      r2 <- letTupExp' "r2" =<<
        eIf
          (toExp $ le64 i .==. pe64 se0)
          (eBody $ fmap eSubExp (Constant (onePrimValue Bool) : ne))
          (eBody $ return $ do
            eIf
              (return $ BasicOp $ Index flag $ Slice s2)
              (eBody $ fmap eSubExp (Constant (onePrimValue Bool) : ne))
              (eBody . fmap eSubExp . (Constant (blankPrimValue Bool) :) =<<
                -- loop needed in case as is array of tuples
                -- Futhark internal rep is tuple of arrays
                forM sas (\x -> do
                  t <- lookupType x
                  letSubExp (baseString x ++ "_elem_2") $
                    BasicOp $ Index x $ fullSlice t s2
                )
              )
          )

      traverse eSubExp $ f1 : r1 ++ r2

  -- scan (\(f1,v1) (f2,v2) ->
  --   let f = f1 || f2
  --   let v = if f2 then v2 else g v1 v2
  --   in (f,v) ) (false,ne) (zip flags vals)
  scan_lams <- traverse (\l -> do
    f1 <- newParam "f1" $ Prim Bool
    f2 <- newParam "f2" $ Prim Bool
    ps <- lambdaParams <$> renameLambda lam0
    let (p1, p2) = splitAt (length ne) ps

    mkLambda (f1 : p1 ++ f2 : p2) $
      fmap varsRes . letTupExp "scan_res" =<< do
        let f = eBinOp LogOr (eParam f1) (eParam f2)
        eIf
          (eParam f2)
          (eBody $ f : fmap eParam p2)
          (eBody . (f:) . fmap (eSubExp . Var) =<<
            bindSubExpRes "gres" =<< eLambda l (fmap eParam ps))
    ) [lam, lam']

  let ne' = Constant (BoolValue False) : ne

  scansres <-
    letTupExp "adj_ctrb_scan" $
      Op $
        Screma n [iota_n] $ ScremaForm (map (`Scan` ne') scan_lams) [] g_lam

  let (_:ls_arr, _:rs_arr_rev) = splitAt (length ne + 1) scansres

  -- map (\i -> if i < w && -1 < w then (xs_bar[i], dst[i]) else (0,ne)) sis
  par_i'' <- newParam "i" $ Prim int64
  let i'' = paramName par_i''
  map_lam <- mkLambda [par_i''] $
    fmap varsRes . letTupExp "scan_res" =<<
      eIf 
        (toExp $ (le64 i'' .<. pe64 (head w)) .&&. (pe64 (intConst Int64 (-1)) .<. le64 i''))
        (eBody $ do 
          zipWith (\x t -> 
            return $ BasicOp $ Index x $ fullSlice t [DimFix $ Var $ paramName par_i'']) (xs_bar ++ dst) (as_type ++ as_type)
        )
        (eBody $ do
          let xs_bar_ne = map (\t -> return $ BasicOp $ Replicate (Shape $ tail $ arrayDims t) (Constant $ blankPrimValue $ elemType t)) as_type
          let dst_ne = map eSubExp ne
          xs_bar_ne ++ dst_ne
        )

  f_bar_dst <- letTupExp "f_bar_dst" $ Op $ Screma n [sis] $ mapSOAC map_lam
  let (f_bar, f_dst) = splitAt (length ne) f_bar_dst

  (as_params, f) <- mkF lam0 as_type n
  f_adj <- vjpLambda ops (map adjFromVar f_bar) as_params f

  -- map (\i -> rs_arr_rev[n-i-1]) (iota n)
  par_i''' <- newParam "i" $ Prim int64
  rev_lam <- mkLambda [par_i'''] $
    varsRes <$>
      zipWithM (\x t -> do
        nmim1 <- letSubExp "n_i_1" =<< toExp (pe64 n - le64 (paramName par_i''') - pe64 se1)
        letExp (baseString x) $
          BasicOp $ Index x $ fullSlice t [DimFix nmim1]
      ) rs_arr_rev as_type

  rs_arr <- letTupExp "rs_arr" $ Op $ Screma n [iota_n] $ mapSOAC rev_lam

  sas_bar' <- eLambda f_adj $ map (eSubExp . Var) $ f_dst <> ls_arr <> sas <> rs_arr
  sas_bar <- bindSubExpRes "sas_bar" sas_bar'

  par_i'''' <- newParam "i" $ Prim int64
  scatter_params <- zipWithM newParam (map (flip (++) "_param" . baseString) xs) $ map rowType as_type
  scatter_lam <- mkLambda (par_i'''' : scatter_params) $
    fmap subExpsRes . letSubExps "scatter_map_res" =<< do
      p1 <- replicateM (length scatter_params) $ eParam par_i''''
      p2 <- traverse eParam scatter_params
      return $ p1 <> p2

  scatter_dst <- traverse (\t -> letExp "scatter_dst" $ BasicOp $ Scratch (elemType t) (arrayDims t)) as_type
  as_bar <- letTupExp "as_bar" $ 
    Op $ Scatter n (siota : sas_bar) scatter_lam $ 
      zipWith (\t -> (,,) (Shape $ return $ arraySize 0 t) 1) as_type scatter_dst

  zipWithM_ updateAdj (tail as) as_bar
  where
    se0 = intConst Int64 0
    se1 = intConst Int64 1
    bindSubExpRes :: String -> [SubExpRes] -> ADM [VName]
    bindSubExpRes s = 
      traverse (\(SubExpRes cs se) -> do
                  bn <- newVName s
                  certifying cs $ letBindNames [bn] $ BasicOp $ SubExp se
                  return bn)
    mkFlagLam :: LParam -> VName -> ADM Lambda
    mkFlagLam par_i sis =     
      mkLambda [par_i] $
        fmap varsRes . letTupExp "flag" =<<
          eIf
            (eCmpOp (CmpEq int64) (eParam par_i) (eSubExp $ Constant $ blankPrimValue int64))
            (eBody $ return $ eSubExp $ Constant $ onePrimValue Bool)
            (eBody $ return $ do
              i_p <- letExp "i_p" =<< eBinOp (Sub Int64 OverflowUndef) (eParam par_i) (eSubExp $ Constant $ onePrimValue int64)
              let [vs_i, vs_p] = map (BasicOp . Index sis . Slice . return . DimFix . Var) [paramName par_i, i_p]

              t <- letSubExp "tmp" =<< eCmpOp (CmpEq int64) (return vs_i) (return vs_p)
              return $ BasicOp $ UnOp Not t
            )