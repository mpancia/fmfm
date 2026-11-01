import Firmware.NoiseSetup

set_option compiler.extract_closed false

/-! C entry points for `Firmware/NoiseSetup.lean`: one function per value a block's setup hands to the
loop. -/

/-- A parameter with hysteresis of `window`. -/
@[export fm1_noise_setup_held] def noiseSetupHeld (parameter : Int16) (previous : Int16) (window : Int32) :
    Int16 :=
  NoiseSetup.held parameter previous window

/-- `filtered_noise`: the cutoff. -/
@[export fm1_noise_setup_cutoff] def noiseSetupCutoff (pitch : Int16) : Int32 := NoiseSetup.cutoff pitch

/-- `filtered_noise`: the damping. -/
@[export fm1_noise_setup_damp] def noiseSetupDamp (param0 : Int16) : Int32 := NoiseSetup.damp param0

/-- `filtered_noise`: the low-pass gain. -/
@[export fm1_noise_setup_lp_gain] def noiseSetupLpGain (param1 : Int16) : Int32 := NoiseSetup.lpGain param1

/-- `filtered_noise`: the band-pass gain. -/
@[export fm1_noise_setup_bp_gain] def noiseSetupBpGain (param1 : Int16) : Int32 := NoiseSetup.bpGain param1

/-- `filtered_noise`: the high-pass gain. -/
@[export fm1_noise_setup_hp_gain] def noiseSetupHpGain (param1 : Int16) : Int32 := NoiseSetup.hpGain param1

/-- `filtered_noise`: the gain correction. -/
@[export fm1_noise_setup_gain_correction] def noiseSetupGainCorrection (pitch : Int16) (param0 : Int16) :
    Int32 :=
  NoiseSetup.gainCorrection pitch param0

/-- `twin_peaks`: the first resonator's coefficient. -/
@[export fm1_noise_setup_peak_c1] def noiseSetupPeakC1 (pitch : Int16) (param0 : Int16) : Int32 :=
  NoiseSetup.peakCoefficient pitch.toInt32 param0

/-- `twin_peaks`: the first resonator's scale. -/
@[export fm1_noise_setup_peak_s1] def noiseSetupPeakS1 (pitch : Int16) : Int32 :=
  NoiseSetup.peakScale pitch.toInt32

/-- `twin_peaks`: the second resonator's coefficient. -/
@[export fm1_noise_setup_peak_c2] def noiseSetupPeakC2 (pitch : Int16) (param0 : Int16) (param1 : Int16) :
    Int32 :=
  NoiseSetup.peakCoefficient (NoiseSetup.secondPeakPitch pitch param1) param0

/-- `twin_peaks`: the second resonator's scale. -/
@[export fm1_noise_setup_peak_s2] def noiseSetupPeakS2 (pitch : Int16) (param1 : Int16) : Int32 :=
  NoiseSetup.peakScale (NoiseSetup.secondPeakPitch pitch param1)

/-- `twin_peaks`: the sharpness squared. -/
@[export fm1_noise_setup_peak_q_squared] def noiseSetupPeakQSquared (param0 : Int16) : Int32 :=
  NoiseSetup.peakQSquared param0

/-- `twin_peaks`: the makeup gain. -/
@[export fm1_noise_setup_peak_makeup] def noiseSetupPeakMakeup (param0 : Int16) : Int32 :=
  NoiseSetup.peakMakeup param0

/-- `clocked_noise`: the phase step moved up. -/
@[export fm1_noise_setup_clock_increment] def noiseSetupClockIncrement (inc : UInt32) : UInt32 :=
  NoiseSetup.clockIncrement inc

/-- `clocked_noise`: the generator's period step. -/
@[export fm1_noise_setup_cycle_increment] def noiseSetupCycleIncrement (prev0 : Int16) : UInt32 :=
  NoiseSetup.cycleIncrement prev0

/-- `clocked_noise`: the quantization step. -/
@[export fm1_noise_setup_quantizer_divider] def noiseSetupQuantizerDivider (prev1 : Int16) : UInt32 :=
  NoiseSetup.quantizerDivider prev1

/-- `granular_cloud`: whether a grain is restarted this block. -/
@[export fm1_noise_setup_grain_done] def noiseSetupGrainDone (envelope : UInt32) (envInc : UInt32) : Bool :=
  NoiseSetup.grainDone envelope envInc

/-- `granular_cloud`: whether a restarted grain starts again. -/
@[export fm1_noise_setup_grain_starts] def noiseSetupGrainStarts (word : UInt32) : Bool :=
  NoiseSetup.grainStarts word

/-- `granular_cloud`: a grain's envelope rate for the block. -/
@[export fm1_noise_setup_grain_rate_start] def noiseSetupGrainRateStart (envelope : UInt32) (envInc : UInt32)
    (word : UInt32) (param0 : Int16) : UInt32 :=
  NoiseSetup.grainRateStart envelope envInc word param0

/-- `granular_cloud`: a grain's envelope phase for the block. -/
@[export fm1_noise_setup_grain_envelope_start] def noiseSetupGrainEnvelopeStart (envelope : UInt32)
    (envInc : UInt32) (word : UInt32) : UInt32 :=
  NoiseSetup.grainEnvelopeStart envelope envInc word

/-- `granular_cloud`: a new grain's phase step. -/
@[export fm1_noise_setup_grain_increment] def noiseSetupGrainIncrement (inc : UInt32) (sample : Int16)
    (param1 : Int16) : UInt32 :=
  NoiseSetup.grainIncrement inc sample param1

/-- `particle_noise`: the hit density. -/
@[export fm1_noise_setup_particle_density] def noiseSetupParticleDensity (param0 : Int16) : UInt32 :=
  NoiseSetup.particleDensity param0
