import Firmware.Delay

set_option compiler.extract_closed false

/-! C entry points for `Firmware/Delay.lean`: one function per operation, so each takes and returns plain
numbers. `fx/delay_glue.c` includes the generated code and runs the line with them. -/

/-- Position in the line of a sample behind the write position. -/
@[export fm1_dl_pos] def dlPos (write offset : UInt32) : UInt32 := Delay.pos write offset
/-- The write position one sample later. -/
@[export fm1_dl_next_write] def dlNextWrite (write : UInt32) : UInt32 := Delay.nextWrite write
/-- Samples for a TIME setting at a tempo and sample rate. -/
@[export fm1_dl_samples] def dlSamples (time bpm rate : UInt32) : UInt32 := Delay.samples time bpm rate
/-- Feedback gain for a setting of 0 to 100. -/
@[export fm1_dl_feedback_gain] def dlFeedbackGain (feedback : UInt32) : Int32 := Delay.feedbackGain feedback
/-- Low-pass amount for a tone setting of 0 to 100. -/
@[export fm1_dl_tone_gain] def dlToneGain (tone : UInt32) : Int32 := Delay.toneGain tone
/-- A signal for the line, held to 16 bits. -/
@[export fm1_dl_store] def dlStore (signal : Int32) : Int16 := Delay.store signal
/-- A stored sample back to Q15. -/
@[export fm1_dl_fetch] def dlFetch (stored : Int16) : Int32 := Delay.fetch stored
/-- One low-pass step (the reverb's). -/
@[export fm1_dl_lowpass] def dlLowpass (state signal coefficient : Int32) : Int32 :=
  Reverb.lowpass state signal coefficient
/-- What goes into the line. -/
@[export fm1_dl_input] def dlInput (send filtered feedback : Int32) : Int32 := Delay.input send filtered feedback
