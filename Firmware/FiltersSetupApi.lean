import Firmware.FiltersSetup

set_option compiler.extract_closed false

/-! C entry points for `Firmware/FiltersSetup.lean`: one function per setup quantity, called once per block by
`voices/filters_setup_glue.c`. -/

/-- The phase step of saw `saw` (0 to 6) of the swarm. -/
@[export fm1_filters_setup_swarm_increment] def filtersSetupSwarmIncrement (pitch : Int32)
    (parameter : Int32) (saw : Int32) : UInt32 :=
  FiltersSetup.swarmIncrement pitch parameter saw

/-- The swarm's high-pass coefficient. -/
@[export fm1_filters_setup_swarm_cutoff] def filtersSetupSwarmCutoff (pitch : Int32) (parameter : Int32) :
    Int32 :=
  FiltersSetup.swarmCutoff pitch parameter

/-- The digital filter's target resonance phase step. -/
@[export fm1_filters_setup_filter_increment] def filtersSetupFilterIncrement (pitch : Int32)
    (parameter : Int32) : UInt32 :=
  FiltersSetup.filterIncrement pitch parameter

/-- The per-sample change of the resonance phase step over a block. -/
@[export fm1_filters_setup_filter_increment_step] def filtersSetupFilterIncrementStep (current : UInt32)
    (target : UInt32) (size : UInt32) : UInt32 :=
  FiltersSetup.filterIncrementStep current target size

/-- The phase step of a vosim formant. -/
@[export fm1_filters_setup_vosim_increment] def filtersSetupVosimIncrement (parameter : Int32) : UInt32 :=
  FiltersSetup.vosimIncrement parameter

/-- The scale that makes the harmonics' gains sum to full scale. -/
@[export fm1_filters_setup_harmonics_attenuation] def filtersSetupHarmonicsAttenuation (parameter0 : Int32)
    (parameter1 : Int32) : Int32 :=
  FiltersSetup.harmonicsAttenuation parameter0 parameter1

/-- The target amplitude of harmonic partial `index` (0 to 11). -/
@[export fm1_filters_setup_harmonics_target] def filtersSetupHarmonicsTarget (parameter0 : Int32)
    (parameter1 : Int32) (inc : UInt32) (attenuation : Int32) (index : Int32) : Int32 :=
  FiltersSetup.harmonicsTarget parameter0 parameter1 inc attenuation index
