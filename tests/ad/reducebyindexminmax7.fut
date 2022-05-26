-- ==
-- entry: compare
-- random input { [500]i64 [100][100]f32 [500][100]f32 } output { true }

-- ==
-- entry: compare2
-- random input { [500]i64 [100][30][20]f32 [500][30][20]f32 } output { true }
def primal [n][m][k] (is: [n]i64) (dst: [m][k]f32) (vs: [n][k]f32) =
  reduce_by_index (copy dst) (map2 f32.max) (replicate k f32.lowest) is vs

entry rev [n][m][k] (is: [n]i64) (dst: [m][k]f32) (vs: [n][k]f32) =
  tabulate m (\i -> vjp (primal is dst) vs (replicate m (replicate k 0) with [i] = replicate k 1))

def fwd [n][m][k] (is: [n]i64) (dst: [m][k]f32) (vs: [n][k]f32) =
  tabulate n (\i -> jvp (primal is dst) vs (replicate n (replicate k 0) with [i] = replicate k 1))
  |> transpose

entry compare [n][m][k] (is': [n]i64) (dst: [m][k]f32) (vs: [n][k]f32) =
  let is = map (\i -> (i64.abs i) %% m) is'
  let r = rev is dst vs
  let f = fwd is dst vs
  in map2 (map2 (==)) r f |> map (reduce (&&) true) |> reduce (&&) true

def primal2 [n][m][k][l] (is: [n]i64) (dst: [m][k][l]f32) (vs: [n][k][l]f32) =
  reduce_by_index (copy dst) (map2 (map2 f32.max)) (replicate k (replicate l f32.lowest)) is vs

entry rev2 [n][m][k][l] (is: [n]i64) (dst: [m][k][l]f32) (vs: [n][k][l]f32) =
  tabulate m (\i -> vjp (primal2 is dst) vs (replicate m (replicate k (replicate l 0)) with [i] = replicate k (replicate l 1)))

def fwd2 [n][m][k][l] (is: [n]i64) (dst: [m][k][l]f32) (vs: [n][k][l]f32) =
  tabulate n (\i -> jvp (primal2 is dst) vs (replicate n (replicate k (replicate l 0)) with [i] = replicate k (replicate l 1)))
  |> transpose

entry compare2 [n][m][k][l] (is': [n]i64) (dst: [m][k][l]f32) (vs: [n][k][l]f32) =
  let is = map (\i -> (i64.abs i) %% m) is'
  let r = rev2 is dst vs
  let f = fwd2 is dst vs
  in map2 (map2 (map2 (==))) r f |> map (map (reduce (&&) true)) |> map (reduce (&&) true) |> reduce (&&) true