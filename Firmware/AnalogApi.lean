import Firmware.Analog

set_option compiler.extract_closed false

/-! C entry points for `Firmware/Analog.lean`: one function per result field, so each returns a plain number.
`voices/analog_glue.c` includes the generated code and calls them in its sample loops. -/

/-- Saw: the phase after the sample. -/
@[export fm1_saw_phase] def sawPhase (phase inc : UInt32) (next : Int32) (sync : UInt8) : UInt32 :=
  (Analog.saw phase inc next sync).phase
/-- Saw: the edge correction carried to the next sample. -/
@[export fm1_saw_next] def sawNext (phase inc : UInt32) (next : Int32) (sync : UInt8) : Int32 :=
  (Analog.saw phase inc next sync).next
/-- Saw: the sample. -/
@[export fm1_saw_out] def sawOut (phase inc : UInt32) (next : Int32) (sync : UInt8) : Int16 :=
  (Analog.saw phase inc next sync).out
/-- Saw: the sync pulse for a following oscillator. -/
@[export fm1_saw_sync] def sawSync (phase inc : UInt32) (next : Int32) (sync : UInt8) : UInt8 :=
  (Analog.saw phase inc next sync).syncOut

/-- Square: the phase after the sample. -/
@[export fm1_square_phase] def squarePhase (phase inc pw : UInt32) (next : Int32) (high : UInt8) (sync : UInt8) : UInt32 :=
  (Analog.square phase inc pw next (high != 0) sync).phase
/-- Square: the edge correction carried to the next sample. -/
@[export fm1_square_next] def squareNext (phase inc pw : UInt32) (next : Int32) (high : UInt8) (sync : UInt8) : Int32 :=
  (Analog.square phase inc pw next (high != 0) sync).next
/-- Square: 1 if the output is in its high half after the sample. -/
@[export fm1_square_high] def squareHigh (phase inc pw : UInt32) (next : Int32) (high : UInt8) (sync : UInt8) : UInt8 :=
  if (Analog.square phase inc pw next (high != 0) sync).high then 1 else 0
/-- Square: the sample. -/
@[export fm1_square_out] def squareOut (phase inc pw : UInt32) (next : Int32) (high : UInt8) (sync : UInt8) : Int16 :=
  (Analog.square phase inc pw next (high != 0) sync).out
/-- Square: the sync pulse for a following oscillator. -/
@[export fm1_square_sync] def squareSync (phase inc pw : UInt32) (next : Int32) (high : UInt8) (sync : UInt8) : UInt8 :=
  (Analog.square phase inc pw next (high != 0) sync).syncOut

/-- Triangle: the phase after the sample. -/
@[export fm1_triangle_phase] def trianglePhase (phase inc : UInt32) (sync : UInt8) : UInt32 :=
  (Analog.triangle phase inc sync).phase
/-- Triangle: the sample. -/
@[export fm1_triangle_out] def triangleOut (phase inc : UInt32) (sync : UInt8) : Int16 :=
  (Analog.triangle phase inc sync).out

/-- Sine: the phase after the sample. -/
@[export fm1_sine_phase] def sinePhase (phase inc : UInt32) (sync : UInt8) : UInt32 :=
  (Analog.sine phase inc sync).phase
/-- Sine: the sample. -/
@[export fm1_sine_out] def sineOut (phase inc : UInt32) (sync : UInt8) : Int16 :=
  (Analog.sine phase inc sync).out

/-- the phase after the sample. -/
@[export fm1_variable_saw_phase] def variableSawPhase (phase : UInt32) (inc : UInt32) (pw : UInt32) (next : Int32) (high : UInt8) (sync : UInt8) : UInt32 :=
  (Analog.variableSaw phase inc pw next (high != 0) sync).phase

/-- the edge correction carried to the next sample. -/
@[export fm1_variable_saw_next] def variableSawNext (phase : UInt32) (inc : UInt32) (pw : UInt32) (next : Int32) (high : UInt8) (sync : UInt8) : Int32 :=
  (Analog.variableSaw phase inc pw next (high != 0) sync).next

/-- 1 if the output is in its high part after the sample. -/
@[export fm1_variable_saw_high] def variableSawHigh (phase : UInt32) (inc : UInt32) (pw : UInt32) (next : Int32) (high : UInt8) (sync : UInt8) : UInt8 :=
  (if (Analog.variableSaw phase inc pw next (high != 0) sync).high then 1 else 0)

/-- the sample. -/
@[export fm1_variable_saw_out] def variableSawOut (phase : UInt32) (inc : UInt32) (pw : UInt32) (next : Int32) (high : UInt8) (sync : UInt8) : Int16 :=
  (Analog.variableSaw phase inc pw next (high != 0) sync).out

/-- the sync pulse for a following oscillator. -/
@[export fm1_variable_saw_sync] def variableSawSync (phase : UInt32) (inc : UInt32) (pw : UInt32) (next : Int32) (high : UInt8) (sync : UInt8) : UInt8 :=
  (Analog.variableSaw phase inc pw next (high != 0) sync).syncOut

/-- the phase after the sample. -/
@[export fm1_csaw_phase] def csawPhase (phase : UInt32) (inc : UInt32) (pw : UInt32) (next : Int32) (depth : Int32) (aux : Int32) (high : UInt8) (sync : UInt8) : UInt32 :=
  (Analog.csaw phase inc pw next depth aux (high != 0) sync).phase

/-- the edge correction carried to the next sample. -/
@[export fm1_csaw_next] def csawNext (phase : UInt32) (inc : UInt32) (pw : UInt32) (next : Int32) (depth : Int32) (aux : Int32) (high : UInt8) (sync : UInt8) : Int32 :=
  (Analog.csaw phase inc pw next depth aux (high != 0) sync).next

/-- 1 if the output is in its high part after the sample. -/
@[export fm1_csaw_high] def csawHigh (phase : UInt32) (inc : UInt32) (pw : UInt32) (next : Int32) (depth : Int32) (aux : Int32) (high : UInt8) (sync : UInt8) : UInt8 :=
  (if (Analog.csaw phase inc pw next depth aux (high != 0) sync).high then 1 else 0)

/-- the sample. -/
@[export fm1_csaw_out] def csawOut (phase : UInt32) (inc : UInt32) (pw : UInt32) (next : Int32) (depth : Int32) (aux : Int32) (high : UInt8) (sync : UInt8) : Int16 :=
  (Analog.csaw phase inc pw next depth aux (high != 0) sync).out

/-- the sync pulse for a following oscillator. -/
@[export fm1_csaw_sync] def csawSync (phase : UInt32) (inc : UInt32) (pw : UInt32) (next : Int32) (depth : Int32) (aux : Int32) (high : UInt8) (sync : UInt8) : UInt8 :=
  (Analog.csaw phase inc pw next depth aux (high != 0) sync).syncOut

/-- the jump depth after the sample. -/
@[export fm1_csaw_depth] def csawDepth (phase : UInt32) (inc : UInt32) (pw : UInt32) (next : Int32) (depth : Int32) (aux : Int32) (high : UInt8) (sync : UInt8) : Int32 :=
  (Analog.csaw phase inc pw next depth aux (high != 0) sync).depth

/-- the phase after the sample. -/
@[export fm1_triangle_fold_phase] def triangleFoldPhase (phase : UInt32) (inc : UInt32) (parameter : Int32) (sync : UInt8) : UInt32 :=
  (Analog.triangleFold phase inc parameter sync).phase

/-- the sample. -/
@[export fm1_triangle_fold_out] def triangleFoldOut (phase : UInt32) (inc : UInt32) (parameter : Int32) (sync : UInt8) : Int16 :=
  (Analog.triangleFold phase inc parameter sync).out

/-- the phase after the sample. -/
@[export fm1_sine_fold_phase] def sineFoldPhase (phase : UInt32) (inc : UInt32) (parameter : Int32) (sync : UInt8) : UInt32 :=
  (Analog.sineFold phase inc parameter sync).phase

/-- the sample. -/
@[export fm1_sine_fold_out] def sineFoldOut (phase : UInt32) (inc : UInt32) (parameter : Int32) (sync : UInt8) : Int16 :=
  (Analog.sineFold phase inc parameter sync).out

/-- the phase after the sample. -/
@[export fm1_buzz_phase] def buzzPhase (phase : UInt32) (inc : UInt32) (zone : UInt32) (zone2 : UInt32) (crossfade : UInt32) (sync : UInt8) : UInt32 :=
  (Analog.buzz phase inc zone zone2 crossfade sync).phase

/-- the sample. -/
@[export fm1_buzz_out] def buzzOut (phase : UInt32) (inc : UInt32) (zone : UInt32) (zone2 : UInt32) (crossfade : UInt32) (sync : UInt8) : Int16 :=
  (Analog.buzz phase inc zone zone2 crossfade sync).out
