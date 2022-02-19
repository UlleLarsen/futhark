-- ==
-- entry: rev
-- compiled input { [0i64, 1i64, 2i64, 3i64, 4i64] [0.0f32, 1.0f32, 2.0f32, 3.0f32, 4.0f32] } output { [1f32,0f32,0f32,0f32,0f32] }
-- compiled input { [0i64, 0i64, 0i64, 0i64, 0i64] [0.0f32, 1.0f32, 2.0f32, 3.0f32, 4.0f32] } output { [24f32,0f32,0f32,0f32,0f32] }
-- compiled input { [0i64, 0i64, 0i64, 0i64, 0i64] [0.0f32, 1.0f32, 0.0f32, 3.0f32, 4.0f32] } output { [0f32,0f32,0f32,0f32,0f32] }
-- compiled input { [0i64, 0i64, 0i64, 0i64, 0i64] [1.0f32, 5.0f32, 2.0f32, 3.0f32, 4.0f32] } output { [120f32,24f32,60f32,40f32,30f32] }

def red_mul [n] (is: [n]i64) (vs: [n]f32) =
  reduce_by_index (replicate 5 1) (*) 1 is vs

entry rev [n] (is: [n]i64) (vs: [n]f32) =
  vjp (red_mul is) vs (replicate 5 0 with [0] = 1)