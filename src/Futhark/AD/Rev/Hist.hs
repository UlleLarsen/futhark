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

elseIf :: PrimType -> [(Builder SOACS Exp, Builder SOACS Exp)] -> [Builder SOACS Body] -> Builder SOACS Exp
elseIf t [(c1,c2)] [bt,bf] =
  eIf
    (eCmpOp (CmpEq t) c1 c2) bt bf
elseIf t ((c1,c2):cs) (bt:bs) =
  eIf
    (eCmpOp (CmpEq t) c1 c2) bt $
      eBody $ return $ elseIf t cs bs
elseIf _ _ _ = error "In elseIf, Hist.hs: input not supported"

--
-- special case of histogram with min/max as operator.
-- Original, assuming `is: [n]i64` and `dst: [w]btp`
--     let x = reduce_by_index dst minmax ne is vs
-- Forward trace:
--     need to copy dst: reverse trace might use it 7
--       (see ex. in reducebyindexminmax6.fut where the first map requires the original dst to be differentiated). 
--     let dst_cpy = copy dst
--     let (x, x_inds) = zip vs (iota n)
--                       |> reduce_by_index dst_cpy argminmax (ne,-1) is
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
--     dst does not need to be copied: dst is not overwritten
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
    letExp (baseString vs ++ "_bar") $ Op $ Screma n [is, vs] $ mapSOAC lam_vsbar

  updateAdj vs vs_bar

--
-- special case of histogram with add as operator.
-- Original, assuming `is: [n]i64` and `dst: [w]btp`
--     let x = reduce_by_index dst (+) ne is vs
-- Forward trace:
--     need to copy dst: reverse trace might use it 7
--       (see ex. in reducebyindexminmax6.fut where the first map requires the original dst to be differentiated). 
--     let dst_cpy = copy dst
--     let x = reduce_by_index dst_cpy (+) ne is vs
--
-- Reverse trace:
--     dst_bar += x_bar
--
--     vs_bar += map (\i -> x_bar[i]) is
diffAddHist ::
  VjpOps -> VName -> StmAux () -> SubExp -> BinOp -> SubExp -> VName -> VName -> SubExp -> SubExp -> VName -> ADM () -> ADM ()
diffAddHist _ops x aux n add ne is vs w rf dst m = do
  let t = binOpType add

  dst_cpy <- letExp (baseString dst ++ "_copy") $ BasicOp $ Copy dst

  f <- mkIdentityLambda [Prim int64, Prim t]
  add_lam <- binOpLambda add t
  auxing aux $
    letBindNames [x] $
      Op $
        Hist n [is, vs] [HistOp (Shape [w]) rf [dst_cpy] [ne] add_lam] f

  m

  x_bar <- lookupAdjVal x

  updateAdj dst x_bar

  ind_param <- newParam (baseString vs ++ "_ind") $ Prim int64 
  lam_vsbar <- 
      mkLambda [ind_param] $
        fmap varsRes . letTupExp "vs_bar" =<<
          eIf
            (toExp $ withinBounds $ return (w, paramName ind_param))
            (eBody $ return $ return $ BasicOp $ Index x_bar $ Slice [DimFix $ Var $ paramName ind_param])
            (eBody $ return $ eSubExp $ Constant $ blankPrimValue t)

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
--   in scatter (copy xs) is xs
radixSortStep :: [VName] -> [Type] -> Shape -> SubExp -> SubExp -> Builder SOACS Exp
radixSortStep xs tps shape bit n = do
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

  xsclone <- traverse (\x -> letExp (baseString x ++ "_copy") $ BasicOp $ Copy x) xs

  ind_param <- newParam "ind_param" $ Prim int64
  scatter_params <- zipWithM newParam (map (flip (++) "_param" . baseString) xs) tps
  scatter_lam <- mkLambda (ind_param : scatter_params) $
    fmap subExpsRes . letSubExps "scatter_map_res" =<< do
      p1 <- replicateM (length scatter_params) $ eParam ind_param
      p2 <- traverse eParam scatter_params
      return $ p1 ++ p2

  return $ Op $ Scatter n (nis : xs) scatter_lam $ map ((,,) shape 1) xsclone
  where
    iConst c = eSubExp $ intConst Int64 c

--
-- the radix sort implementation
-- def radix_sort [n] 't (xs: [n]i64) =
--   let iters = if n == 0 then 0 else 32
--   in loop xs for i < iters do radix_sort_step xs i64.get_bit (i*2)
radixSort :: [VName] -> Shape -> SubExp -> ADM [VName]
radixSort xs shape n = do
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
    radixSortStep (map paramName params) (map rowType types) shape bit n

  letTupExp "sorted" $
    DoLoop
      (zip params $ map Var xs)
      (ForLoop i Int64 iters [])
      loopbody

diffHist :: VjpOps -> [VName] -> SubExp -> [VName] -> HistOp SOACS -> ADM ()
--diffAd _ops x aux n add ne is vs w rf dst m 
diffHist _ops xs n as op = do
  sorted <- radixSort as (histShape op) n
  zipWithM_ insAdj (tail as) (tail sorted)

  --error $ "todo\n" ++ show as ++ "\n" ++ show pat_adj ++ "\n" ++ show (histDest op)