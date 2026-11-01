import Firmware.AnalogSetup

set_option compiler.extract_closed false

/-! C entry points for `Firmware/AnalogSetup.lean`: one per scalar. `voices/analog_setup_glue.c` includes the
generated code and `voices/braids/analog_oscillator.cc` calls each once per block. -/

/-- The pitch held between 0 and note 128. -/
@[export fm1_analog_setup_clamped_pitch] def analogSetupClampedPitch (pitch : Int16) : Int16 :=
  AnalogSetup.clampedPitch pitch

/-- The square's pulse width as a phase. -/
@[export fm1_analog_setup_square_pulse_width] def analogSetupSquarePulseWidth (parameter : Int16) : UInt32 :=
  AnalogSetup.squarePulseWidth parameter

/-- The variable saw's pulse width as a phase. -/
@[export fm1_analog_setup_variable_saw_pulse_width]
def analogSetupVariableSawPulseWidth (parameter : Int16) : UInt32 :=
  AnalogSetup.variableSawPulseWidth parameter

/-- The buzz's comb zone. -/
@[export fm1_analog_setup_buzz_zone] def analogSetupBuzzZone (pitch parameter : Int16) : UInt32 :=
  AnalogSetup.buzzZone pitch parameter

/-- The comb zone the buzz crossfades towards. -/
@[export fm1_analog_setup_buzz_zone2] def analogSetupBuzzZone2 (pitch parameter : Int16) : UInt32 :=
  AnalogSetup.buzzZone2 pitch parameter

/-- The buzz's crossfade between its two zones. -/
@[export fm1_analog_setup_buzz_crossfade] def analogSetupBuzzCrossfade (pitch parameter : Int16) : UInt32 :=
  AnalogSetup.buzzCrossfade pitch parameter
