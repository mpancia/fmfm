import Firmware.Percussion

set_option compiler.extract_closed false

/-! C entry points for `Firmware/Percussion.lean`: one function per result field. -/

/-- `svf`: the filter coefficient for a frequency. -/
@[export fm1_svf_cutoff] def svfCutoff (frequency : Int32) : Int32 := Percussion.svfCutoff frequency

/-- `svf`: the damping for a resonance. -/
@[export fm1_svf_damp] def svfDamp (resonance : Int32) : Int32 := Percussion.svfDamp resonance

/-- `svf`: the low-pass state after the step. -/
@[export fm1_svf_lp] def svfLp (input : Int32) (f : Int32) (damp : Int32) (punch : Int32) (lp : Int32) (bp : Int32) (mode : UInt8) : Int32 :=
  (Percussion.svf input f damp punch lp bp mode).lp

/-- `svf`: the band-pass state after the step. -/
@[export fm1_svf_bp] def svfBp (input : Int32) (f : Int32) (damp : Int32) (punch : Int32) (lp : Int32) (bp : Int32) (mode : UInt8) : Int32 :=
  (Percussion.svf input f damp punch lp bp mode).bp

/-- `svf`: the filter's output. -/
@[export fm1_svf_out] def svfOut (input : Int32) (f : Int32) (damp : Int32) (punch : Int32) (lp : Int32) (bp : Int32) (mode : UInt8) : Int32 :=
  (Percussion.svf input f damp punch lp bp mode).out

/-- `excite`: the pulse after the step. -/
@[export fm1_excite_state] def exciteState (state : Int32) (decay : Int32) (counter : Int32) (level : Int32) : Int32 :=
  (Percussion.excite state decay counter level).state

/-- `excite`: the delay counter after the step. -/
@[export fm1_excite_counter] def exciteCounter (state : Int32) (decay : Int32) (counter : Int32) (level : Int32) : Int32 :=
  (Percussion.excite state decay counter level).counter

/-- `excite`: the signed pulse. -/
@[export fm1_excite_out] def exciteOut (state : Int32) (decay : Int32) (counter : Int32) (level : Int32) : Int32 :=
  (Percussion.excite state decay counter level).out

/-- `kick`: the low-pass state after the sample. -/
@[export fm1_kick_lp] def kickLp (excitation : Int32) (resonator : Int32) (lp : Int32) (coefficient : Int32) : Int32 :=
  (Percussion.kickOut excitation resonator lp coefficient).lp

/-- `kick`: the sample. -/
@[export fm1_kick_out] def kickOut (excitation : Int32) (resonator : Int32) (lp : Int32) (coefficient : Int32) : Int16 :=
  (Percussion.kickOut excitation resonator lp coefficient).out

/-- `snare`: the sample. -/
@[export fm1_snare_mix] def snareMix (filtered1 excitation1 filtered2 excitation2 noise g1 g2 : Int32) : Int16 :=
  Percussion.snareMix filtered1 excitation1 filtered2 excitation2 noise g1 g2

/-- `cymbal`: the metallic noise from six phases. -/
@[export fm1_cymbal_hat_noise] def cymbalHatNoise (p0 p1 p2 p3 p4 p5 : UInt32) : Int32 :=
  Percussion.hatNoise p0 p1 p2 p3 p4 p5

/-- `cymbal`: the white noise from the generator's state. -/
@[export fm1_cymbal_white] def cymbalWhite (rng : UInt32) : Int32 := Percussion.hatWhite rng

/-- `cymbal`: the next generator state. -/
@[export fm1_cymbal_lcg] def cymbalLcg (rng : UInt32) : UInt32 := Digital.lcg rng

/-- `cymbal`: the sample. -/
@[export fm1_cymbal_out] def cymbalOut (metal white xfade : Int32) : Int16 := Percussion.cymbalOut metal white xfade

/-- `bell_partial`: the partial's phase after the step. -/
@[export fm1_bell_partial_phase] def bellPartialPhase (phase : UInt32) (inc : UInt32) (amplitude : Int32) : UInt32 :=
  (Percussion.bellPartial phase inc amplitude).phase

/-- `bell_partial`: the partial's share of the sample. -/
@[export fm1_bell_partial_contribution] def bellPartialContribution (phase : UInt32) (inc : UInt32) (amplitude : Int32) : Int32 :=
  (Percussion.bellPartial phase inc amplitude).contribution

/-- `decay`: a partial's amplitude after one block. -/
@[export fm1_partial_decay] def partialDecay (amplitude decayLong decayShort parameter : Int32) : Int32 :=
  Percussion.decay amplitude decayLong decayShort parameter

/-- `drum_noise`: the low-pass state `lp0` after the sample. -/
@[export fm1_drum_noise_lp0] def drumNoiseLp0 (noise : Int32) (lp0 : Int32) (lp1 : Int32) (lp2 : Int32) (f : Int32) : Int32 :=
  (Percussion.drumNoise noise lp0 lp1 lp2 f).lp0

/-- `drum_noise`: the low-pass state `lp1` after the sample. -/
@[export fm1_drum_noise_lp1] def drumNoiseLp1 (noise : Int32) (lp0 : Int32) (lp1 : Int32) (lp2 : Int32) (f : Int32) : Int32 :=
  (Percussion.drumNoise noise lp0 lp1 lp2 f).lp1

/-- `drum_noise`: the low-pass state `lp2` after the sample. -/
@[export fm1_drum_noise_lp2] def drumNoiseLp2 (noise : Int32) (lp0 : Int32) (lp1 : Int32) (lp2 : Int32) (f : Int32) : Int32 :=
  (Percussion.drumNoise noise lp0 lp1 lp2 f).lp2

/-- `drum_partial`: the partial's phase after the step. -/
@[export fm1_drum_partial_phase] def drumPartialPhase (phase : UInt32) (inc : UInt32) (amplitude : Int32) (target : Int32) (fade : Int32) : UInt32 :=
  (Percussion.drumPartial phase inc amplitude target fade).phase

/-- `drum_partial`: the partial's share of the sample. -/
@[export fm1_drum_partial_contribution] def drumPartialContribution (phase : UInt32) (inc : UInt32) (amplitude : Int32) (target : Int32) (fade : Int32) : Int32 :=
  (Percussion.drumPartial phase inc amplitude target fade).contribution

/-- `drum`: the sample. -/
@[export fm1_drum_mix] def drumMix (partial0 partial1 partial3 harmonics lp2 noiseGain harmonicsGain : Int32) : Int16 :=
  Percussion.drumMix partial0 partial1 partial3 harmonics lp2 noiseGain harmonicsGain

/-- `bell`, `drum`: the clipped sum of the partials. -/
@[export fm1_partials_out] def partialsOut (sum : Int32) : Int16 := (Filters.harmonicsOut sum).toInt16

/-- `bell`, `drum`: the average of the clipped sum with the previous sample. -/
@[export fm1_partials_mid] def partialsMid (sum previous : Int32) : Int16 := (Filters.harmonicsMid sum previous).toInt16
