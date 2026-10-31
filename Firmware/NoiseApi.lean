import Firmware.Noise

set_option compiler.extract_closed false

/-! C entry points for `Firmware/Noise.lean`: one function per result field. -/

/-- `filtered_noise`: the low-pass state after the sample. -/
@[export fm1_filtered_noise_lp] def filteredNoiseLp (input : Int32) (f : Int32) (damp : Int32)
    (bp : Int32) (lp : Int32) (lpGain : Int32) (bpGain : Int32) (hpGain : Int32) (gain : Int32) : Int32 :=
  (Noise.filtered input f damp bp lp lpGain bpGain hpGain gain).lp

/-- `filtered_noise`: the band-pass state after the sample. -/
@[export fm1_filtered_noise_bp] def filteredNoiseBp (input : Int32) (f : Int32) (damp : Int32)
    (bp : Int32) (lp : Int32) (lpGain : Int32) (bpGain : Int32) (hpGain : Int32) (gain : Int32) : Int32 :=
  (Noise.filtered input f damp bp lp lpGain bpGain hpGain gain).bp

/-- `filtered_noise`: the sample. -/
@[export fm1_filtered_noise_out] def filteredNoiseOut (input : Int32) (f : Int32) (damp : Int32)
    (bp : Int32) (lp : Int32) (lpGain : Int32) (bpGain : Int32) (hpGain : Int32) (gain : Int32) : Int16 :=
  (Noise.filtered input f damp bp lp lpGain bpGain hpGain gain).out

/-- `twin_peaks`: the first resonator's last output. -/
@[export fm1_twin_peaks_y11] def twinPeaksY11 (input : Int32) (s1 : Int32) (c1 : Int32) (s2 : Int32)
    (c2 : Int32) (q2 : Int32) (makeup : Int32) (y11 : Int32) (y12 : Int32) (y21 : Int32) (y22 : Int32) : Int32 :=
  (Noise.twinPeaks input s1 c1 s2 c2 q2 makeup y11 y12 y21 y22).y11

/-- `twin_peaks`: the first resonator's output before that. -/
@[export fm1_twin_peaks_y12] def twinPeaksY12 (input : Int32) (s1 : Int32) (c1 : Int32) (s2 : Int32)
    (c2 : Int32) (q2 : Int32) (makeup : Int32) (y11 : Int32) (y12 : Int32) (y21 : Int32) (y22 : Int32) : Int32 :=
  (Noise.twinPeaks input s1 c1 s2 c2 q2 makeup y11 y12 y21 y22).y12

/-- `twin_peaks`: the second resonator's last output. -/
@[export fm1_twin_peaks_y21] def twinPeaksY21 (input : Int32) (s1 : Int32) (c1 : Int32) (s2 : Int32)
    (c2 : Int32) (q2 : Int32) (makeup : Int32) (y11 : Int32) (y12 : Int32) (y21 : Int32) (y22 : Int32) : Int32 :=
  (Noise.twinPeaks input s1 c1 s2 c2 q2 makeup y11 y12 y21 y22).y21

/-- `twin_peaks`: the second resonator's output before that. -/
@[export fm1_twin_peaks_y22] def twinPeaksY22 (input : Int32) (s1 : Int32) (c1 : Int32) (s2 : Int32)
    (c2 : Int32) (q2 : Int32) (makeup : Int32) (y11 : Int32) (y12 : Int32) (y21 : Int32) (y22 : Int32) : Int32 :=
  (Noise.twinPeaks input s1 c1 s2 c2 q2 makeup y11 y12 y21 y22).y22

/-- `twin_peaks`: the sample. -/
@[export fm1_twin_peaks_out] def twinPeaksOut (input : Int32) (s1 : Int32) (c1 : Int32) (s2 : Int32)
    (c2 : Int32) (q2 : Int32) (makeup : Int32) (y11 : Int32) (y12 : Int32) (y21 : Int32) (y22 : Int32) : Int16 :=
  (Noise.twinPeaks input s1 c1 s2 c2 q2 makeup y11 y12 y21 y22).out

/-- `clocked_noise`: the phase after the sample. -/
@[export fm1_clocked_noise_phase] def clockedNoisePhase (phase : UInt32) (inc : UInt32) (rng : UInt32)
    (cycle : UInt32) (cycleInc : UInt32) (seed : UInt32) (held : Int16) (divider : UInt32) (sync : UInt8) : UInt32 :=
  (Noise.clocked phase inc rng cycle cycleInc seed held divider sync).phase

/-- `clocked_noise`: the generator state after the sample. -/
@[export fm1_clocked_noise_rng] def clockedNoiseRng (phase : UInt32) (inc : UInt32) (rng : UInt32)
    (cycle : UInt32) (cycleInc : UInt32) (seed : UInt32) (held : Int16) (divider : UInt32) (sync : UInt8) : UInt32 :=
  (Noise.clocked phase inc rng cycle cycleInc seed held divider sync).rng

/-- `clocked_noise`: the period phase after the sample. -/
@[export fm1_clocked_noise_cycle] def clockedNoiseCycle (phase : UInt32) (inc : UInt32) (rng : UInt32)
    (cycle : UInt32) (cycleInc : UInt32) (seed : UInt32) (held : Int16) (divider : UInt32) (sync : UInt8) : UInt32 :=
  (Noise.clocked phase inc rng cycle cycleInc seed held divider sync).cycle

/-- `clocked_noise`: the held value after the sample. -/
@[export fm1_clocked_noise_held] def clockedNoiseHeld (phase : UInt32) (inc : UInt32) (rng : UInt32)
    (cycle : UInt32) (cycleInc : UInt32) (seed : UInt32) (held : Int16) (divider : UInt32) (sync : UInt8) : Int16 :=
  (Noise.clocked phase inc rng cycle cycleInc seed held divider sync).held

/-- `clocked_noise`: the sample. -/
@[export fm1_clocked_noise_out] def clockedNoiseOut (phase : UInt32) (inc : UInt32) (rng : UInt32)
    (cycle : UInt32) (cycleInc : UInt32) (seed : UInt32) (held : Int16) (divider : UInt32) (sync : UInt8) : Int16 :=
  (Noise.clocked phase inc rng cycle cycleInc seed held divider sync).out

/-- `grain`: the grain's phase after the step. -/
@[export fm1_grain_phase] def grainPhase (phase : UInt32) (inc : UInt32) (envelope : UInt32)
    (envInc : UInt32) : UInt32 :=
  (Noise.grain phase inc envelope envInc).phase

/-- `grain`: the grain's envelope phase after the step. -/
@[export fm1_grain_envelope] def grainEnvelope (phase : UInt32) (inc : UInt32) (envelope : UInt32)
    (envInc : UInt32) : UInt32 :=
  (Noise.grain phase inc envelope envInc).envelope

/-- `grain`: the grain's share of the sample. -/
@[export fm1_grain_contribution] def grainContribution (phase : UInt32) (inc : UInt32) (envelope : UInt32)
    (envInc : UInt32) : Int32 :=
  (Noise.grain phase inc envelope envInc).contribution

/-- `cloud`: the grains' sum, limited to 16 bits. -/
@[export fm1_cloud_out] def cloudOut (sum : Int32) : Int16 := Noise.cloudOut sum

/-- `particle_hit`: the resonator value `c1`. -/
@[export fm1_particle_hit_c1] def particleHitC1 (noise : UInt32) (pitch : Int32) (spread : Int32) : Int32 :=
  (Noise.particleHit noise pitch spread).c1

/-- `particle_hit`: the resonator value `s1`. -/
@[export fm1_particle_hit_s1] def particleHitS1 (noise : UInt32) (pitch : Int32) (spread : Int32) : Int32 :=
  (Noise.particleHit noise pitch spread).s1

/-- `particle_hit`: the resonator value `c2`. -/
@[export fm1_particle_hit_c2] def particleHitC2 (noise : UInt32) (pitch : Int32) (spread : Int32) : Int32 :=
  (Noise.particleHit noise pitch spread).c2

/-- `particle_hit`: the resonator value `s2`. -/
@[export fm1_particle_hit_s2] def particleHitS2 (noise : UInt32) (pitch : Int32) (spread : Int32) : Int32 :=
  (Noise.particleHit noise pitch spread).s2

/-- `particle_hit`: the resonator value `c3`. -/
@[export fm1_particle_hit_c3] def particleHitC3 (noise : UInt32) (pitch : Int32) (spread : Int32) : Int32 :=
  (Noise.particleHit noise pitch spread).c3

/-- `particle_hit`: the resonator value `s3`. -/
@[export fm1_particle_hit_s3] def particleHitS3 (noise : UInt32) (pitch : Int32) (spread : Int32) : Int32 :=
  (Noise.particleHit noise pitch spread).s3

/-- `particle`: the burst's amplitude after the sample. -/
@[export fm1_particle_amplitude] def particleAmplitude (noise : UInt32) (amplitude : UInt16) (s1 : Int32)
    (c1 : Int32) (s2 : Int32) (c2 : Int32) (s3 : Int32) (c3 : Int32) (y11 : Int32) (y12 : Int32)
    (y21 : Int32) (y22 : Int32) (y31 : Int32) (y32 : Int32) : UInt16 :=
  (Noise.particle noise amplitude s1 c1 s2 c2 s3 c3 y11 y12 y21 y22 y31 y32).amplitude

/-- `particle`: the resonator state `y11` after the sample. -/
@[export fm1_particle_y11] def particleY11 (noise : UInt32) (amplitude : UInt16) (s1 : Int32) (c1 : Int32)
    (s2 : Int32) (c2 : Int32) (s3 : Int32) (c3 : Int32) (y11 : Int32) (y12 : Int32) (y21 : Int32)
    (y22 : Int32) (y31 : Int32) (y32 : Int32) : Int32 :=
  (Noise.particle noise amplitude s1 c1 s2 c2 s3 c3 y11 y12 y21 y22 y31 y32).y11

/-- `particle`: the resonator state `y12` after the sample. -/
@[export fm1_particle_y12] def particleY12 (noise : UInt32) (amplitude : UInt16) (s1 : Int32) (c1 : Int32)
    (s2 : Int32) (c2 : Int32) (s3 : Int32) (c3 : Int32) (y11 : Int32) (y12 : Int32) (y21 : Int32)
    (y22 : Int32) (y31 : Int32) (y32 : Int32) : Int32 :=
  (Noise.particle noise amplitude s1 c1 s2 c2 s3 c3 y11 y12 y21 y22 y31 y32).y12

/-- `particle`: the resonator state `y21` after the sample. -/
@[export fm1_particle_y21] def particleY21 (noise : UInt32) (amplitude : UInt16) (s1 : Int32) (c1 : Int32)
    (s2 : Int32) (c2 : Int32) (s3 : Int32) (c3 : Int32) (y11 : Int32) (y12 : Int32) (y21 : Int32)
    (y22 : Int32) (y31 : Int32) (y32 : Int32) : Int32 :=
  (Noise.particle noise amplitude s1 c1 s2 c2 s3 c3 y11 y12 y21 y22 y31 y32).y21

/-- `particle`: the resonator state `y22` after the sample. -/
@[export fm1_particle_y22] def particleY22 (noise : UInt32) (amplitude : UInt16) (s1 : Int32) (c1 : Int32)
    (s2 : Int32) (c2 : Int32) (s3 : Int32) (c3 : Int32) (y11 : Int32) (y12 : Int32) (y21 : Int32)
    (y22 : Int32) (y31 : Int32) (y32 : Int32) : Int32 :=
  (Noise.particle noise amplitude s1 c1 s2 c2 s3 c3 y11 y12 y21 y22 y31 y32).y22

/-- `particle`: the resonator state `y31` after the sample. -/
@[export fm1_particle_y31] def particleY31 (noise : UInt32) (amplitude : UInt16) (s1 : Int32) (c1 : Int32)
    (s2 : Int32) (c2 : Int32) (s3 : Int32) (c3 : Int32) (y11 : Int32) (y12 : Int32) (y21 : Int32)
    (y22 : Int32) (y31 : Int32) (y32 : Int32) : Int32 :=
  (Noise.particle noise amplitude s1 c1 s2 c2 s3 c3 y11 y12 y21 y22 y31 y32).y31

/-- `particle`: the resonator state `y32` after the sample. -/
@[export fm1_particle_y32] def particleY32 (noise : UInt32) (amplitude : UInt16) (s1 : Int32) (c1 : Int32)
    (s2 : Int32) (c2 : Int32) (s3 : Int32) (c3 : Int32) (y11 : Int32) (y12 : Int32) (y21 : Int32)
    (y22 : Int32) (y31 : Int32) (y32 : Int32) : Int32 :=
  (Noise.particle noise amplitude s1 c1 s2 c2 s3 c3 y11 y12 y21 y22 y31 y32).y32

/-- `particle`: the sample. -/
@[export fm1_particle_out] def particleOut (noise : UInt32) (amplitude : UInt16) (s1 : Int32) (c1 : Int32)
    (s2 : Int32) (c2 : Int32) (s3 : Int32) (c3 : Int32) (y11 : Int32) (y12 : Int32) (y21 : Int32)
    (y22 : Int32) (y31 : Int32) (y32 : Int32) : Int16 :=
  (Noise.particle noise amplitude s1 c1 s2 c2 s3 c3 y11 y12 y21 y22 y31 y32).out

