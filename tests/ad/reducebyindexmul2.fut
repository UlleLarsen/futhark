-- ==
-- entry: rev
-- compiled input { [0f32,1f32,2f32,3f32,4f32] [0i64,0i64,0i64,0i64,0i64] [1f32,2f32,3f32,4f32,5f32] } output { [0f32,0f32,0f32,0f32,0f32] }
-- compiled input { [4f32,1f32,2f32,3f32,4f32] [1i64,0i64,2i64,0i64,3i64] [1f32,2f32,3f32,4f32,5f32] } output { [0f32,16f32,0f32,8f32,0f32] }

def red_mul [n][m] (dst: [m]f32) (is: [n]i64) (vs: [n]f32) =
  reduce_by_index (copy dst) (*) 1 is vs

entry rev [n][m] (dst: [m]f32) (is: [n]i64) (vs: [n]f32) =
  vjp (red_mul dst is) vs (replicate m 0 with [0] = 1)