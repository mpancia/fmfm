import Firmware.Smooth

/-- The crossfade position after `k` samples of a block of `size`: the glue starts at 0 and adds the
per-sample step once a sample. -/
def Smooth.crossfadeAfter (size : UInt32) : Nat → Int32
  | 0 => 0
  | k + 1 => Smooth.advance (Smooth.crossfadeAfter size k) (Smooth.perSample size)

/-- The phase step after `k` samples of a block of `size` that moves it from `previous` toward `target`: the
glue adds the same delta once a sample. -/
def Smooth.stepAfter (previous target size : UInt32) : Nat → UInt32
  | 0 => previous
  | k + 1 => Smooth.glide (Smooth.stepAfter previous target size k) (Smooth.stepDelta previous target size)
