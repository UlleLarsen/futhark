-- Scan with nested map
-- vectorised special case, generic case
-- ==
-- entry: fwd_J rev_J
-- compiled input { [[[1f32,2f32], [2f32,3f32]], [[4f32,5f32], [3f32,4f32]], 
--                   [[3f32,4f32], [4f32,5f32]], [[4f32,5f32], [2f32,3f32]]] }
-- output {
--[[[[[[1f32, 0f32], [0f32, 0f32]], [[4f32, 0f32], [0f32, 0f32]], 
--    [[12f32, 0f32], [0f32, 0f32]], [[48f32, 0f32], [0f32, 0f32]]], 
--   [[[0f32, 1f32], [0f32, 0f32]], [[0f32, 5f32], [0f32, 0f32]], 
--    [[0f32, 20f32], [0f32, 0f32]], [[0f32, 100f32], [0f32, 0f32]]]], 
--  [[[[0f32, 0f32], [1f32, 0f32]], [[0f32, 0f32], [3f32, 0f32]], 
--    [[0f32, 0f32], [12f32, 0f32]], [[0f32, 0f32], [24f32, 0f32]]], 
--   [[[0f32, 0f32], [0f32, 1f32]], [[0f32, 0f32], [0f32, 4f32]], 
--    [[0f32, 0f32], [0f32, 20f32]], [[0f32, 0f32], [0f32, 60f32]]]]], 
-- [[[[[0f32, 0f32], [0f32, 0f32]], [[1f32, 0f32], [0f32, 0f32]], 
--    [[3f32, 0f32], [0f32, 0f32]], [[12f32, 0f32], [0f32, 0f32]]], 
--   [[[0f32, 0f32], [0f32, 0f32]], [[0f32, 2f32], [0f32, 0f32]], 
--    [[0f32, 8f32], [0f32, 0f32]], [[0f32, 40f32], [0f32, 0f32]]]], 
--  [[[[0f32, 0f32], [0f32, 0f32]], [[0f32, 0f32], [2f32, 0f32]], 
--    [[0f32, 0f32], [8f32, 0f32]], [[0f32, 0f32], [16f32, 0f32]]], 
--   [[[0f32, 0f32], [0f32, 0f32]], [[0f32, 0f32], [0f32, 3f32]], 
--    [[0f32, 0f32], [0f32, 15f32]], [[0f32, 0f32], [0f32, 45f32]]]]], 
-- [[[[[0f32, 0f32], [0f32, 0f32]], [[0f32, 0f32], [0f32, 0f32]], 
--    [[4f32, 0f32], [0f32, 0f32]], [[16f32, 0f32], [0f32, 0f32]]], 
--   [[[0f32, 0f32], [0f32, 0f32]], [[0f32, 0f32], [0f32, 0f32]], 
--    [[0f32, 10f32], [0f32, 0f32]], [[0f32, 50f32], [0f32, 0f32]]]], 
--  [[[[0f32, 0f32], [0f32, 0f32]], [[0f32, 0f32], [0f32, 0f32]], 
--    [[0f32, 0f32], [6f32, 0f32]], [[0f32, 0f32], [12f32, 0f32]]], 
--   [[[0f32, 0f32], [0f32, 0f32]], [[0f32, 0f32], [0f32, 0f32]], 
--    [[0f32, 0f32], [0f32, 12f32]], [[0f32, 0f32], [0f32, 36f32]]]]], 
-- [[[[[0f32, 0f32], [0f32, 0f32]], [[0f32, 0f32], [0f32, 0f32]], 
--    [[0f32, 0f32], [0f32, 0f32]], [[12f32, 0f32], [0f32, 0f32]]], 
--   [[[0f32, 0f32], [0f32, 0f32]], [[0f32, 0f32], [0f32, 0f32]], 
--    [[0f32, 0f32], [0f32, 0f32]], [[0f32, 40f32], [0f32, 0f32]]]], 
--  [[[[0f32, 0f32], [0f32, 0f32]], [[0f32, 0f32], [0f32, 0f32]], 
--    [[0f32, 0f32], [0f32, 0f32]], [[0f32, 0f32], [24f32, 0f32]]], 
--   [[[0f32, 0f32], [0f32, 0f32]], [[0f32, 0f32], [0f32, 0f32]], 
--    [[0f32, 0f32], [0f32, 0f32]], [[0f32, 0f32], [0f32, 60f32]]]]]]
-- }

def primal [n][m][k] (xs: [n][m][k]f32) =
  scan (map2 (map2 (*))) (replicate m (replicate k 1)) xs

entry fwd_J [n][m][k] (input: [n][m][k]f32) =
  tabulate_3d n m k (\i j q -> jvp primal input 
  (replicate n (replicate m (replicate k 0)) 
    with [i] = (replicate m (replicate k 0) 
      with [j] = (replicate k 0 with [q] = 1))))  

entry rev_J [n][m][k] (input: [n][m][k]f32) =
  let res = tabulate_3d n m k (\i j q -> vjp primal input
   (replicate n (replicate m (replicate k 0))
      with [i] = (replicate m (replicate k 0) 
        with [j] = (replicate k 0 with [q] = 1)))) 
  let a = res |> map (map transpose) |> map (map (map transpose)) |> map (map (map (map transpose)))
  let a2 = a |> map transpose |> map (map transpose) |> map (map (map transpose))
  in a2 |> transpose |> map transpose |> (map (map transpose))
     