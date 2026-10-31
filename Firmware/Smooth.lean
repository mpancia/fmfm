set_option compiler.extract_closed false

/-!
# Smoothing a parameter and a phase step across a block

Port of Braids' `parameter_interpolation.h` and `BEGIN_INTERPOLATE_PHASE_INCREMENT` (Emilie Gillet, MIT).
Each engine gets a new timbre and pitch once a block; these move the values a little every sample instead of
jumping. The loops stay in `voices/*_glue.c`; every number they compute comes from here. Scalar only: it runs
in the audio path. `>>>` on an `Int32` is an arithmetic shift, as `>>` is on the chip's `int32_t`.
-/

/-- The crossfade step for a block of `size` samples: after `size` steps the crossfade reaches
`32767 - 32767 % size`, just short of full. `size` is never 0. -/
@[inline] def Smooth.perSample (size : UInt32) : Int32 := 32767 / size.toInt32

/-- The crossfade position after one more sample. -/
@[inline] def Smooth.advance (xfade perSample : Int32) : Int32 := xfade + perSample

/-- The parameter at crossfade position `xfade` (0 to 32767, in parts of 32768) from `start` to `target`. -/
@[inline] def Smooth.parameter (start target xfade : Int32) : Int32 :=
  start + (((target - start) * xfade) >>> 15)

/-- How much the phase step moves each sample to get from `previous` to `target` in `size` samples. Braids
negates a falling move with `~`, which is one less than the exact negative, so a falling step ends between 1
and `size` below its target. Kept so the output is Braids', sample for sample. -/
@[inline] def Smooth.stepDelta (previous target size : UInt32) : UInt32 :=
  if previous < target then (target - previous) / size else ~~~((previous - target) / size)

/-- The phase step after one more sample. -/
@[inline] def Smooth.glide (inc delta : UInt32) : UInt32 := inc + delta
