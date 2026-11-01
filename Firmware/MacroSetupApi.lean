import Firmware.MacroSetup

set_option compiler.extract_closed false

/-! C entry points for `Firmware/MacroSetup.lean`: one per scalar. `voices/macro_setup_glue.c` includes the
generated code and `voices/braids/macro_oscillator.cc` calls each once per block. -/

/-- CSAW: the sample shift. -/
@[export fm1_macro_setup_csaw_shift] def macroSetupCsawShift (parameter1 : Int16) : Int32 :=
  MacroSetup.csawShift parameter1

/-- Morph: the zone, 0 to 2. -/
@[export fm1_macro_setup_morph_zone] def macroSetupMorphZone (parameter0 : Int16) : UInt32 :=
  MacroSetup.morphZone parameter0

/-- Morph: the crossfade balance. -/
@[export fm1_macro_setup_morph_balance] def macroSetupMorphBalance (parameter0 : Int16) : UInt32 :=
  MacroSetup.morphBalance parameter0

/-- Morph: the first oscillator's parameter. -/
@[export fm1_macro_setup_morph_parameter] def macroSetupMorphParameter (parameter0 : Int16) : Int32 :=
  MacroSetup.morphParameter parameter0

/-- Morph: the low-pass coefficient. -/
@[export fm1_macro_setup_morph_cutoff] def macroSetupMorphCutoff (pitch parameter1 : Int16) : Int32 :=
  MacroSetup.morphCutoff pitch parameter1

/-- Morph: the fuzz amount. -/
@[export fm1_macro_setup_morph_fuzz] def macroSetupMorphFuzz (pitch parameter1 : Int16) : Int32 :=
  MacroSetup.morphFuzz pitch parameter1

/-- Triple: one detuned oscillator's pitch. -/
@[export fm1_macro_setup_triple_pitch] def macroSetupTriplePitch (pitch parameter : Int16) : Int16 :=
  MacroSetup.triplePitch pitch parameter

/-- Sub: the sub oscillator's pitch. -/
@[export fm1_macro_setup_sub_pitch] def macroSetupSubPitch (pitch parameter1 : Int16) : Int16 :=
  MacroSetup.subPitch pitch parameter1

/-- Dual sync: the synced oscillator's pitch. -/
@[export fm1_macro_setup_dual_sync_pitch] def macroSetupDualSyncPitch (pitch parameter0 : Int16) : Int16 :=
  MacroSetup.dualSyncPitch pitch parameter0

/-- Sine triangle: the sine fold's parameter. -/
@[export fm1_macro_setup_sine_parameter] def macroSetupSineParameter (pitch parameter0 : Int16) : Int32 :=
  MacroSetup.sineTriangleSineParameter pitch parameter0

/-- Sine triangle: the triangle fold's parameter. -/
@[export fm1_macro_setup_tri_parameter] def macroSetupTriParameter (pitch parameter0 : Int16) : Int32 :=
  MacroSetup.sineTriangleTriParameter pitch parameter0

/-- Buzz: the second buzz's pitch. -/
@[export fm1_macro_setup_buzz_pitch] def macroSetupBuzzPitch (pitch parameter1 : Int16) : Int16 :=
  MacroSetup.buzzPitch pitch parameter1
