-- ==
--  compiled input {
--    [0i64,1i64,2i64,3i64,2i64,1i64,0i64,1i64,2i64]
--    [0f32,1f32,2f32,3f32,4f32]
--    [-1i64,-1i64,-1i64,-1i64,-1i64]
--    [-5f32,0f32,2f32,5f32,4f32,1f32,-2f32,-8f32,4f32]
--    [0i64,1i64,2i64,3i64,4i64,5i64,6i64,7i64,8i64] }
--  output {
--    [1f32,1f32,0f32,0f32,1f32]
--    [1i64,1i64,0i64,0i64,1i64]
--    [0f32,0f32,0f32,1f32,1f32,0f32,0f32,0f32,0f32]
--    [0i64,0i64,0i64,1i64,1i64,0i64,0i64,0i64,0i64] }

def argmax (x: f32,i: i64) (y: f32,j: i64) =
  if x == y
  then (x,i64.min i j)
  else if x > y
  then (x,i)
  else (y,j)

def f [n][m] (is: [n]i64) (dst: [m](f32,i64), vs: [n](f32,i64)) =
  reduce_by_index (copy dst) argmax (f32.lowest,i64.highest) is vs

def main [n][m] (is: [n]i64) (dst0: [m]f32) (dst1: [m]i64) (vs0: [n]f32) (vs1: [n]i64) =
  let (r1,r2) = vjp (f is) (zip dst0 dst1, zip vs0 vs1) (zip (replicate m 1) (replicate m 1))
  let (v1,i1) = unzip r1
  let (v2,i2) = unzip r2
  in (v1,i1,v2,i2)