import Firmware.Pitch

set_option compiler.extract_closed false

/-! C entry point for `Firmware/Pitch.lean`. `voices/pitch_glue.c` includes the generated code and both Braids
oscillators call it once per block. -/

/-- The phase step per sample for a pitch in 1/128 semitones. -/
@[export fm1_pitch_phase_increment] def pitchPhaseIncrement (pitch : Int16) : UInt32 :=
  Pitch.phaseIncrement pitch
