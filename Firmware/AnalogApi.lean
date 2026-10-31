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
