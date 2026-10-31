import Firmware.Filters

set_option compiler.extract_closed false

/-! C entry points for `Firmware/Filters.lean`: one function per result field. -/

/-- `swarm_shape`: the shaped sum of seven saw phases, a signed 16-bit value. -/
@[export fm1_swarm_shape] def swarmShape (p0 p1 p2 p3 p4 p5 p6 : UInt32) : Int16 :=
  (Filters.swarmShape p0 p1 p2 p3 p4 p5 p6).toInt16

/-- `swarm_filter`: the low-pass state after the step. -/
@[export fm1_swarm_filter_lp] def swarmFilterLp (sample : Int32) (f : Int32) (damp : Int32) (bp : Int32)
    (lp : Int32) : Int32 :=
  (Filters.swarmFilter sample f damp bp lp).lp

/-- `swarm_filter`: the band-pass state after the step. -/
@[export fm1_swarm_filter_bp] def swarmFilterBp (sample : Int32) (f : Int32) (damp : Int32) (bp : Int32)
    (lp : Int32) : Int32 :=
  (Filters.swarmFilter sample f damp bp lp).bp

/-- `swarm_filter`: the high-passed sample. -/
@[export fm1_swarm_filter_out] def swarmFilterOut (sample : Int32) (f : Int32) (damp : Int32) (bp : Int32)
    (lp : Int32) : Int16 :=
  (Filters.swarmFilter sample f damp bp lp).out

/-- `digital_filter`: the phase after the sample. -/
@[export fm1_digital_filter_phase] def digitalFilterPhase (phase : UInt32) (inc : UInt32)
    (modPhase : UInt32) (modInc : UInt32) (squarePhase : UInt32) (integrator : Int32) (polarity : UInt8)
    (filterType : UInt8) (parameter : Int32) (sync : UInt8) : UInt32 :=
  (Filters.digitalFilter phase inc modPhase modInc squarePhase integrator polarity filterType parameter sync).phase

/-- `digital_filter`: the resonance phase after the sample. -/
@[export fm1_digital_filter_mod] def digitalFilterMod (phase : UInt32) (inc : UInt32) (modPhase : UInt32)
    (modInc : UInt32) (squarePhase : UInt32) (integrator : Int32) (polarity : UInt8) (filterType : UInt8)
    (parameter : Int32) (sync : UInt8) : UInt32 :=
  (Filters.digitalFilter phase inc modPhase modInc squarePhase integrator polarity filterType parameter sync).modPhase

/-- `digital_filter`: the square's resonance phase after the sample. -/
@[export fm1_digital_filter_square] def digitalFilterSquare (phase : UInt32) (inc : UInt32)
    (modPhase : UInt32) (modInc : UInt32) (squarePhase : UInt32) (integrator : Int32) (polarity : UInt8)
    (filterType : UInt8) (parameter : Int32) (sync : UInt8) : UInt32 :=
  (Filters.digitalFilter phase inc modPhase modInc squarePhase integrator polarity filterType parameter sync).squarePhase

/-- `digital_filter`: the square integrator after the sample. -/
@[export fm1_digital_filter_integrator] def digitalFilterIntegrator (phase : UInt32) (inc : UInt32)
    (modPhase : UInt32) (modInc : UInt32) (squarePhase : UInt32) (integrator : Int32) (polarity : UInt8)
    (filterType : UInt8) (parameter : Int32) (sync : UInt8) : Int32 :=
  (Filters.digitalFilter phase inc modPhase modInc squarePhase integrator polarity filterType parameter sync).integrator

/-- `digital_filter`: the square's polarity after the sample. -/
@[export fm1_digital_filter_polarity] def digitalFilterPolarity (phase : UInt32) (inc : UInt32)
    (modPhase : UInt32) (modInc : UInt32) (squarePhase : UInt32) (integrator : Int32) (polarity : UInt8)
    (filterType : UInt8) (parameter : Int32) (sync : UInt8) : UInt8 :=
  (Filters.digitalFilter phase inc modPhase modInc squarePhase integrator polarity filterType parameter sync).polarity

/-- `digital_filter`: the sample. -/
@[export fm1_digital_filter_out] def digitalFilterOut (phase : UInt32) (inc : UInt32) (modPhase : UInt32)
    (modInc : UInt32) (squarePhase : UInt32) (integrator : Int32) (polarity : UInt8) (filterType : UInt8)
    (parameter : Int32) (sync : UInt8) : Int16 :=
  (Filters.digitalFilter phase inc modPhase modInc squarePhase integrator polarity filterType parameter sync).out

/-- `vosim`: the phase after the sample. -/
@[export fm1_vosim_phase] def vosimPhase (phase : UInt32) (inc : UInt32) (formant0 : UInt32)
    (formant1 : UInt32) (inc0 : UInt32) (inc1 : UInt32) (sync : UInt8) : UInt32 :=
  (Filters.vosim phase inc formant0 formant1 inc0 inc1 sync).phase

/-- `vosim`: the first formant phase after the sample. -/
@[export fm1_vosim_f0] def vosimF0 (phase : UInt32) (inc : UInt32) (formant0 : UInt32) (formant1 : UInt32)
    (inc0 : UInt32) (inc1 : UInt32) (sync : UInt8) : UInt32 :=
  (Filters.vosim phase inc formant0 formant1 inc0 inc1 sync).formant0

/-- `vosim`: the second formant phase after the sample. -/
@[export fm1_vosim_f1] def vosimF1 (phase : UInt32) (inc : UInt32) (formant0 : UInt32) (formant1 : UInt32)
    (inc0 : UInt32) (inc1 : UInt32) (sync : UInt8) : UInt32 :=
  (Filters.vosim phase inc formant0 formant1 inc0 inc1 sync).formant1

/-- `vosim`: the sample. -/
@[export fm1_vosim_out] def vosimOut (phase : UInt32) (inc : UInt32) (formant0 : UInt32)
    (formant1 : UInt32) (inc0 : UInt32) (inc1 : UInt32) (sync : UInt8) : Int16 :=
  (Filters.vosim phase inc formant0 formant1 inc0 inc1 sync).out

/-- `harmonic`: one harmonic's contribution to the sum. -/
@[export fm1_harmonic_sine] def harmonicSine (phase multiple : UInt32) (amplitude : Int32) : Int32 :=
  Filters.harmonicSine phase multiple amplitude

/-- `harmonic`: a harmonic's amplitude, a step closer to its target. -/
@[export fm1_harmonic_glide] def harmonicGlide (amplitude target : Int32) : Int32 := Filters.harmonicGlide amplitude target

/-- `harmonics`: the clipped sum. -/
@[export fm1_harmonics_out] def harmonicsOut (sum : Int32) : Int16 := (Filters.harmonicsOut sum).toInt16

/-- `harmonics`: the average of the clipped sum with the previous sample. -/
@[export fm1_harmonics_mid] def harmonicsMid (sum previous : Int32) : Int16 := (Filters.harmonicsMid sum previous).toInt16
