-- 2D tiling with extra dimensions on top.
-- ==
-- compiled random input { [2][40][40]i32 [2][40][40]i32 } auto output
-- structure gpu { SegMap/SegMap 4
-- SegMap/DoLoop/SegMap 2
-- SegMap/SegMap 3
-- SegMap/DoLoop/DoLoop/SegMap/DoLoop 3 }

def main [a][b][c] (xss: [a][b][c]i32) (yss: [a][b][c]i32) =
  map2 (\xs ys -> map (\xs' -> map (\ys' -> i32.sum (map2 (*) xs' ys')) ys) xs) xss yss
