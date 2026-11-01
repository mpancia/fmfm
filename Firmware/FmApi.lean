import Firmware.Fm

set_option compiler.extract_closed false

/-! C entry points for `Firmware/Fm.lean`: `voices/fm_glue.c` includes the generated code and calls them in its
sample loop. Settings stay 32-bit numbers throughout: no `Nat` on the sample path. -/

/-- A modulator's push added to the pushes so far. -/
@[export fm1_fm_push] def fmPush (sofar : UInt32) (modulator : Int32) (depth : UInt32) : UInt32 :=
  Fm.push sofar modulator depth

/-- One operator's output for a sample: its phase pushed by its modulators' pushes, then its envelope. -/
@[export fm1_fm_operator] def fmOperator (phase push envelope : UInt32) : Int32 :=
  Fm.operator phase push envelope

/-- A carrier's share of the sample. -/
@[export fm1_fm_carry] def fmCarry (out : Int32) (level : UInt32) : Int32 := Fm.carry out level

/-- The envelope one sample on. -/
@[export fm1_fm_envelope_step] def fmEnvelopeStep (envelope rate : UInt32) : UInt32 :=
  Fm.envelopeStep envelope rate

/-- An operator's phase increment from the voice's and its ratio. -/
@[export fm1_fm_increment] def fmIncrement (voiceInc ratio : UInt32) : UInt32 := Fm.increment voiceInc ratio

/-- The carriers' sum as a 16-bit sample. -/
@[export fm1_fm_saturate] def fmSaturate (x : Int32) : Int16 := Fm.saturate x

/-- 1 if `source` modulates `op` in algorithm `alg`. -/
@[export fm1_fm_modulates] def fmModulates (alg op source : UInt32) : UInt32 :=
  if Fm.modulates alg op source then 1 else 0

/-- 1 if `op` carries in algorithm `alg`. -/
@[export fm1_fm_carries] def fmCarries (alg op : UInt32) : UInt32 :=
  if Fm.carries alg op then 1 else 0

/-- The shape's algorithm. -/
@[export fm1_fm_algorithm] def fmAlgorithm (shape : UInt32) : UInt32 := Fm.algorithm shape

/-- Operator `op`'s ratio, Q8. -/
@[export fm1_fm_ratio] def fmRatio (shape op : UInt32) : UInt32 := Fm.ratio shape op

/-- Operator `op`'s modulation depth at the timbre (Q15). -/
@[export fm1_fm_depth] def fmDepth (shape op timbre : UInt32) : UInt32 :=
  Fm.scaledDepth (Fm.depth shape op) (timbre % 32768)

/-- Operator `op`'s carrier level, Q15. -/
@[export fm1_fm_level] def fmLevel (shape op : UInt32) : UInt32 := Fm.level shape op

/-- Operator `op`'s envelope rate. -/
@[export fm1_fm_rate] def fmRate (shape op : UInt32) : UInt32 := Fm.rate shape op

/-- Operator 4's feedback depth at the colour (Q15). -/
@[export fm1_fm_feedback] def fmFeedback (shape colour : UInt32) : UInt32 :=
  Fm.scaledFeedback shape (colour % 32768)
