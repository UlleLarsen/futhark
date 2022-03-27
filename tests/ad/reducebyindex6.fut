-- ==
--  entry: rev
--  compiled input {
--    [2i64,-2i64,2i64,6i64,2i64,-2i64,2i64,6i64]
--    [1f32, 2f32,3f32,4f32,5f32, 6f32,7f32,8f32] }
--  output {
--    [840f32,0f32,280f32,0f32,168f32,0f32,120f32,0f32] }

def f [n] (is: [n]i64) (as: [n]f32) =
  reduce_by_index (replicate 3 0.5) (\x y -> x*y*2) 0.5 is as

entry rev [n] (is: [n]i64) (as: [n]f32) =
  vjp (f is) as (replicate 3 0 with [2] = 1)