import Firmware.PercussionSetup

set_option compiler.extract_closed false

/-! C entry points for `Firmware/PercussionSetup.lean`: one per number the block setup stores.
`voices/percussion_setup_glue.c` includes the generated code. -/

/-- Bell partial `i`'s amplitude when struck. -/
@[export fm1_percussion_setup_bell_amplitude] def bellAmplitude (i : UInt32) : Int32 :=
  PercussionSetup.bellAmplitude i

/-- Bell partial `i`'s phase step for the block. -/
@[export fm1_percussion_setup_bell_increment] def bellIncrement (pitch param1 : Int32) (i : UInt32) :
    UInt32 :=
  PercussionSetup.bellIncrement pitch param1 i

/-- Bell partial `i`'s amplitude after the block's decay. -/
@[export fm1_percussion_setup_bell_decayed] def bellDecayed (amplitude param0 : Int32) (i : UInt32) : Int32 :=
  PercussionSetup.bellDecayed amplitude param0 i

/-- Drum partial `i`'s amplitude when struck. -/
@[export fm1_percussion_setup_drum_amplitude] def drumAmplitude (i : UInt32) : Int32 :=
  PercussionSetup.drumAmplitude i

/-- Drum partial `i`'s phase step for the block. -/
@[export fm1_percussion_setup_drum_increment] def drumIncrement (pitch : Int32) (i : UInt32) : UInt32 :=
  PercussionSetup.drumIncrement pitch i

/-- Drum partial `i`'s target amplitude after the block's decay. -/
@[export fm1_percussion_setup_drum_decayed] def drumDecayed (amplitude param0 : Int32) (i : UInt32) : Int32 :=
  PercussionSetup.drumDecayed amplitude param0 i

/-- The drum's noise filter coefficient. -/
@[export fm1_percussion_setup_drum_filter] def drumFilter (pitch param1 : Int32) : Int32 :=
  PercussionSetup.drumFilter pitch param1

/-- The drum's gain on all partials. -/
@[export fm1_percussion_setup_drum_harmonics_gain] def drumHarmonicsGain (param1 : Int32) : Int32 :=
  PercussionSetup.drumHarmonicsGain param1

/-- The drum's gain on the noise-modulated partials. -/
@[export fm1_percussion_setup_drum_noise_gain] def drumNoiseGain (param1 : Int32) : Int32 :=
  PercussionSetup.drumNoiseGain param1

/-- The kick's resonance. -/
@[export fm1_percussion_setup_kick_resonance] def kickResonance (param0 : Int32) : Int32 :=
  PercussionSetup.kickResonance param0

/-- The kick's low-pass coefficient. -/
@[export fm1_percussion_setup_kick_lp_coefficient] def kickLpCoefficient (param1 : Int32) : Int32 :=
  PercussionSetup.kickLpCoefficient param1

/-- A snare filter's resonance on a strike, from its base. -/
@[export fm1_percussion_setup_snare_resonance] def snareResonance (base pitch param1 : Int32) : Int32 :=
  PercussionSetup.snareResonance base pitch param1

/-- The snare's noise exciter decay on a strike. -/
@[export fm1_percussion_setup_snare_pulse_decay] def snarePulseDecay (pitch param1 : Int32) : Int32 :=
  PercussionSetup.snarePulseDecay pitch param1

/-- The snare's noise exciter level on a strike. -/
@[export fm1_percussion_setup_snare_snappy] def snareSnappy (param1 : Int32) : Int32 :=
  PercussionSetup.snareSnappy param1

/-- A snare filter's frequency, `semitones` above the pitch. -/
@[export fm1_percussion_setup_snare_frequency] def snareFrequency (pitch semitones : Int32) : Int32 :=
  PercussionSetup.snareFrequency pitch semitones

/-- The snare's gain on its drum part. -/
@[export fm1_percussion_setup_snare_gain1] def snareGain1 (param0 : Int32) : Int32 :=
  PercussionSetup.snareGain1 param0

/-- The snare's gain on its noise part. -/
@[export fm1_percussion_setup_snare_gain2] def snareGain2 (param0 : Int32) : Int32 :=
  PercussionSetup.snareGain2 param0

/-- The cymbal's phase step `i`. -/
@[export fm1_percussion_setup_cymbal_increment] def cymbalIncrement (pitch : Int32) (i : UInt32) : UInt32 :=
  PercussionSetup.cymbalIncrement pitch i

/-- The cymbal's filter frequency. -/
@[export fm1_percussion_setup_cymbal_frequency] def cymbalFrequency (param0 : Int32) : Int32 :=
  PercussionSetup.cymbalFrequency param0
