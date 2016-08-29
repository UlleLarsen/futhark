-- This test has been distilled from CalibVolDiff and exposed a bug in
-- the memory expander.
--
-- ==
-- input {
--   [[1.0f32, 1.5f32, 2.5f32], [3.0f32, 6.5f32, 0.5f32]]
--   [[0.10f32, 0.15f32, 0.25f32], [0.30f32, 0.65f32, 0.05f32]]
--   [[0.1f32, 1.75f32], [1.0f32, 17.5f32]]
--   [[0.01f32, 1.705f32], [0.1f32, 17.05f32]]
--   [[0.02f32, 0.05f32], [0.04f32, 0.07f32]]
--   0.1f32
--   30
-- }
-- output { [[[-1.350561f32, 0.615297f32], [-0.225855f32, 0.103073f32]],
--           [[-1.776825f32, 0.812598f32], [-0.230401f32, 0.105177f32]],
--           [[-2.596339f32, 1.191926f32], [-0.235133f32, 0.107367f32]],
--           [[-4.819269f32, 2.220859f32], [-0.240064f32, 0.109650f32]],
--           [[-33.523365f32, 15.507273f32], [-0.245206f32, 0.112030f32]],
--           [[6.763457f32, -3.140509f32], [-0.250574f32, 0.114514f32]],
--           [[3.071727f32, -1.431704f32], [-0.256181f32, 0.117110f32]],
--           [[1.987047f32, -0.929638f32], [-0.262046f32, 0.119824f32]],
--           [[1.468468f32, -0.689606f32], [-0.268185f32, 0.122666f32]],
--           [[1.164528f32, -0.548925f32], [-0.274619f32, 0.125644f32]],
--           [[0.964817f32, -0.456489f32], [-0.281369f32, 0.128768f32]],
--           [[0.823568f32, -0.391114f32], [-0.288459f32, 0.132050f32]],
--           [[0.718389f32, -0.342435f32], [-0.295916f32, 0.135502f32]],
--           [[0.637028f32, -0.304780f32], [-0.303769f32, 0.139136f32]],
--           [[0.572216f32, -0.274786f32], [-0.312050f32, 0.142969f32]],
--           [[0.519370f32, -0.250331f32], [-0.320795f32, 0.147017f32]],
--           [[0.475458f32, -0.230010f32], [-0.330045f32, 0.151299f32]],
--           [[0.438389f32, -0.212858f32], [-0.339844f32, 0.155834f32]],
--           [[0.406681f32, -0.198186f32], [-0.350242f32, 0.160647f32]],
--           [[0.379247f32, -0.185493f32], [-0.361297f32, 0.165764f32]],
--           [[0.355280f32, -0.174405f32], [-0.373073f32, 0.171215f32]],
--           [[0.334161f32, -0.164635f32], [-0.385643f32, 0.177033f32]],
--           [[0.315410f32, -0.155961f32], [-0.399088f32, 0.183257f32]],
--           [[0.298649f32, -0.148209f32], [-0.413506f32, 0.189930f32]],
--           [[0.283580f32, -0.141239f32], [-0.429004f32, 0.197103f32]],
--           [[0.269957f32, -0.134939f32], [-0.445709f32, 0.204836f32]],
--           [[0.257582f32, -0.129217f32], [-0.463768f32, 0.213195f32]],
--           [[0.246292f32, -0.123996f32], [-0.483353f32, 0.222260f32]],
--           [[0.235948f32, -0.119214f32], [-0.504664f32, 0.232124f32]],
--           [[0.226438f32, -0.114818f32], [-0.527942f32, 0.242899f32]]]
-- }

default(f32)

fun tridagSeq(a:  [n]f32,b: *[]f32,c: []f32,y: *[]f32 ): *[]f32 =
    loop ((y, b)) =
      for i < n-1 do
        let i    = i + 1
        let beta = a[i] / b[i-1]
        let b[i] = b[i] - beta*c[i-1]
        let y[i] = y[i] - beta*y[i-1]
        in  (y, b)

    let y[n-1] = y[n-1]/b[n-1] in
    loop (y) = for j < n - 1 do
                 let i    = n - 2 - j
                 let y[i] = (y[i] - c[i]*y[i+1]) / b[i]
                 in  y
    in  y

fun implicitMethod(myD:  [m][3]f32,  myDD: [m][3]f32,
                   myMu: [n][m]f32, myVar: [n][m]f32,
                   u: [n][m]f32)
                  (dtInv: f32): *[n][m]f32 =
  map (fn (tup:  ([]f32,[]f32,*[]f32) ): *[]f32   =>
         let (mu_row,var_row,u_row) = tup
         let abc = map (fn (tup: (f32,f32,[]f32,[]f32)): (f32,f32,f32)  =>
                          let (mu, var, d, dd) = tup in
                          ( 0.0   - 0.5*(mu*d[0] + 0.5*var*dd[0])
                          , dtInv - 0.5*(mu*d[1] + 0.5*var*dd[1])
                          , 0.0   - 0.5*(mu*d[2] + 0.5*var*dd[2])
                          )
                      ) (zip (mu_row) (var_row) myD myDD
                      )
         let (a,b,c) = unzip(abc) in
         tridagSeq( a, b, c, u_row )
     ) (zip myMu myVar (copy(u))
     )

fun main(myD:  [m][3]f32,  myDD: [m][3]f32,
        myMu: [n][m]f32, myVar: [n][m]f32,
        u: *[n][m]f32,    dtInv: f32,
        num_samples: int): *[num_samples][n][m]f32 =
  map (implicitMethod(myD,myDD,myMu,myVar,u)) (
      map (*dtInv) (map  (/f32(num_samples)) (map f32 (map (+1) (iota(num_samples))))))
