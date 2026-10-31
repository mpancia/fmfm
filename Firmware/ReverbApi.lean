import Firmware.Reverb

set_option compiler.extract_closed false

/-! C entry points for `Firmware/Reverb.lean`: one function per operation, so each takes and returns plain
numbers.
`fx/reverb_glue.c` includes the generated code and runs the network with them. -/

/-- Where a delay line starts in the shared memory. -/
@[export fm1_rv_start] def rvStart (scale line : UInt32) : UInt32 := Reverb.start scale line
/-- A delay line's length. -/
@[export fm1_rv_length] def rvLength (scale line : UInt32) : UInt32 := Reverb.length scale line
/-- Position in the ring of a sample of a line. -/
@[export fm1_rv_pos] def rvPos (write base offset : UInt32) : UInt32 := Reverb.pos write base offset
/-- The write position one sample later. -/
@[export fm1_rv_next_write] def rvNextWrite (write : UInt32) : UInt32 := Reverb.nextWrite write
/-- A signal for the delay memory. -/
@[export fm1_rv_compress] def rvCompress (signal : Int32) : Int16 := Reverb.compress signal
/-- A stored sample back to Q15. -/
@[export fm1_rv_decompress] def rvDecompress (stored : Int16) : Int32 := Reverb.decompress stored
/-- A signal times a Q15 gain. -/
@[export fm1_rv_mul] def rvMul (signal gain : Int32) : Int32 := Reverb.mul signal gain
/-- One low-pass step. -/
@[export fm1_rv_lowpass] def rvLowpass (state signal coefficient : Int32) : Int32 :=
  Reverb.lowpass state signal coefficient
/-- A point between two stored neighbours. -/
@[export fm1_rv_interpolate] def rvInterpolate (a b fraction : Int32) : Int32 :=
  Reverb.interpolate a b fraction
/-- The slow wobble of a phase, 0 to 32767. -/
@[export fm1_rv_lfo] def rvLfo (phase : UInt32) : Int32 := Reverb.lfo phase
/-- A delay time that moves with an LFO, in samples as Q16. -/
@[export fm1_rv_mod_offset] def rvModOffset (base depth scale lfo : UInt32) : UInt32 :=
  Reverb.modOffset base depth scale lfo
/-- Loop gain for a decay-time setting of 0 to 100. -/
@[export fm1_rv_time_gain] def rvTimeGain (time : UInt32) : Int32 := Reverb.timeGain time
/-- Low-pass amount for a brightness setting of 0 to 100. -/
@[export fm1_rv_bright_gain] def rvBrightGain (bright : UInt32) : Int32 := Reverb.brightGain bright
