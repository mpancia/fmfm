import Firmware.Smooth

set_option compiler.extract_closed false

/-! C entry points for `Firmware/Smooth.lean`. `voices/analog_glue.c`, `digital_glue.c` and `macro_glue.c`
include the generated code next to their engine's own and call these in their sample loops. -/

/-- The crossfade step for a block of `size` samples. -/
@[export fm1_smooth_per_sample] def smoothPerSample (size : UInt32) : Int32 := Smooth.perSample size
/-- The crossfade position after one more sample. -/
@[export fm1_smooth_advance] def smoothAdvance (xfade perSample : Int32) : Int32 :=
  Smooth.advance xfade perSample
/-- The parameter at crossfade position `xfade` between `start` and `target`. -/
@[export fm1_smooth_parameter] def smoothParameter (start target xfade : Int32) : Int32 :=
  Smooth.parameter start target xfade
/-- The per-sample move of the phase step from `previous` to `target` over `size` samples. -/
@[export fm1_smooth_step_delta] def smoothStepDelta (previous target size : UInt32) : UInt32 :=
  Smooth.stepDelta previous target size
/-- The phase step after one more sample. -/
@[export fm1_smooth_glide] def smoothGlide (inc delta : UInt32) : UInt32 := Smooth.glide inc delta
