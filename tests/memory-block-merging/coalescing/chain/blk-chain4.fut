-- Test coalescing with 'Index' index functions where the first slice dimension
-- index is fixed ('i' in the code below).  This needs to be handled separately
-- from 'DimSlice'.
-- ==
-- input { [0, 3, 5] }
-- output { [[ 0,  0,  0],
--           [ 6,  6,  6],
--           [10, 10, 10],
--           [10, 10, 10],
--           [13, 13, 13],
--           [15, 15, 15]]
--        }
-- structure cpu { Alloc 1 }
-- structure gpu { Alloc 2 }

-- The GPU pipeline has additional allocations for the two 'replicate'
-- expressions, though the reuse transformation merges them.

-- I think we need two-dimensional overlap checking for this to work.

let main [n] (a: [n]i32): [][n]i32 =
  let x    = map (\i -> replicate n (i + 10)) a |> opaque
  let a2   = map (\i -> replicate n (2 * i)) a
  let y    = concat a2 x
  in  y
