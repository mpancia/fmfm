import Firmware.PhysicalSetup

set_option compiler.extract_closed false

/-! C entry points for `Firmware/PhysicalSetup.lean`: one per number the block setup stores.
`voices/physical_setup_glue.c` includes the generated code. -/

/-- Comb filter: the smoothed delay pitch. -/
@[export fm1_physical_setup_comb_pitch] def combFilteredPitch (previous pitch param0 : Int32) : Int16 :=
  PhysicalSetup.combFilteredPitch previous pitch param0

/-- Comb filter: the whole samples of the delay. -/
@[export fm1_physical_setup_comb_delay_integral] def combDelayIntegral (delay : UInt32) : UInt32 :=
  PhysicalSetup.combDelayIntegral delay

/-- Comb filter: the fraction of a sample of the delay. -/
@[export fm1_physical_setup_comb_delay_fractional] def combDelayFractional (delay : UInt32) : Int32 :=
  PhysicalSetup.combDelayFractional delay

/-- Plucked string: a new string's oversampling. -/
@[export fm1_physical_setup_pluck_shift] def pluckShift (increment : UInt32) : UInt32 :=
  PhysicalSetup.pluckShift increment

/-- Plucked string: a string's size. -/
@[export fm1_physical_setup_pluck_size] def pluckSize (shift : UInt32) : UInt32 :=
  PhysicalSetup.pluckSize shift

/-- Plucked string: a string's mask. -/
@[export fm1_physical_setup_pluck_mask] def pluckMask (shift : UInt32) : UInt32 :=
  PhysicalSetup.pluckMask shift

/-- Plucked string: how much of a new string is filled. -/
@[export fm1_physical_setup_pluck_initialization] def pluckInitialization (shift : UInt32) (param1 : Int32) :
    UInt32 :=
  PhysicalSetup.pluckInitialization shift param1

/-- Plucked string: the chance each entry is averaged per sample. -/
@[export fm1_physical_setup_pluck_update_probability] def pluckUpdateProbability (param0 : Int32) : UInt32 :=
  PhysicalSetup.pluckUpdateProbability param0

/-- Plucked string: the loss per averaging. -/
@[export fm1_physical_setup_pluck_loss] def pluckLoss (increment : UInt32) (param0 : Int32) : Int32 :=
  PhysicalSetup.pluckLoss increment param0

/-- Bowed string: the bow pressure. -/
@[export fm1_physical_setup_bowed_bow] def bowedBow (param0 : Int32) : Int32 := PhysicalSetup.bowedBow param0

/-- Bowed string: the bridge side's delay. -/
@[export fm1_physical_setup_bowed_bridge_delay] def bowedBridgeDelay (delay : UInt32) (param1 : Int32) :
    UInt32 :=
  PhysicalSetup.bowedBridgeDelay delay param1

/-- Bowed string: the neck side's delay. -/
@[export fm1_physical_setup_bowed_neck_delay] def bowedNeckDelay (delay : UInt32) (param1 : Int32) : UInt32 :=
  PhysicalSetup.bowedNeckDelay delay param1

/-- Bowed string: the envelope pointer kept after a block. -/
@[export fm1_physical_setup_bowed_excitation_clamp] def bowedExcitationClamp (ptr : UInt32) : UInt32 :=
  PhysicalSetup.bowedExcitationClamp ptr

/-- Blown pipe: the bore's delay. -/
@[export fm1_physical_setup_blown_delay] def blownDelay (delay : UInt32) : UInt32 :=
  PhysicalSetup.blownDelay delay

/-- Blown pipe: the breath pressure. -/
@[export fm1_physical_setup_blown_parameter] def blownParameter (param0 : Int32) : Int32 :=
  PhysicalSetup.blownParameter param0

/-- Blown pipe: the body filter coefficient. -/
@[export fm1_physical_setup_blown_filter_coefficient] def blownFilterCoefficient (pitch param1 : Int32) :
    Int32 :=
  PhysicalSetup.blownFilterCoefficient pitch param1

/-- Flute: the bore's delay. -/
@[export fm1_physical_setup_fluted_bore_delay] def flutedBoreDelay (delay : UInt32) (param1 : Int32) :
    UInt32 :=
  PhysicalSetup.flutedBoreDelay delay param1

/-- Flute: the jet's delay. -/
@[export fm1_physical_setup_fluted_jet_delay] def flutedJetDelay (delay : UInt32) (param1 : Int32) : UInt32 :=
  PhysicalSetup.flutedJetDelay delay param1

/-- Flute: the breath noise intensity. -/
@[export fm1_physical_setup_fluted_breath] def flutedBreath (param0 : Int32) : Int32 :=
  PhysicalSetup.flutedBreath param0

/-- Flute: the body filter coefficient. -/
@[export fm1_physical_setup_fluted_filter_coefficient] def flutedFilterCoefficient (pitch : Int32) : Int32 :=
  PhysicalSetup.flutedFilterCoefficient pitch

/-- Flute: the envelope pointer kept after a block. -/
@[export fm1_physical_setup_fluted_excitation_clamp] def flutedExcitationClamp (ptr : UInt32) : UInt32 :=
  PhysicalSetup.flutedExcitationClamp ptr
