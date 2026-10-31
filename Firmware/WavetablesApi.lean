import Firmware.Wavetables

set_option compiler.extract_closed false

/-! C entry points for `Firmware/Wavetables.lean`: one function per result field. -/

/-- `wavetable`: the phase after the sample. -/
@[export fm1_wavetable_phase] def wavetablePhase (phase : UInt32) (inc : UInt32) (waveA : UInt32)
    (waveB : UInt32) (balance : UInt32) (sync : UInt8) : UInt32 :=
  (Wavetables.wavetable phase inc waveA waveB balance sync).phase

/-- `wavetable`: the sample. -/
@[export fm1_wavetable_out] def wavetableOut (phase : UInt32) (inc : UInt32) (waveA : UInt32)
    (waveB : UInt32) (balance : UInt32) (sync : UInt8) : Int16 :=
  (Wavetables.wavetable phase inc waveA waveB balance sync).out

/-- `wave_map`: the phase after the sample. -/
@[export fm1_wave_map_phase] def waveMapPhase (phase : UInt32) (inc : UInt32) (w00 : UInt32)
    (w01 : UInt32) (w10 : UInt32) (w11 : UInt32) (xfadeX : UInt32) (xfadeY : UInt32) (sync : UInt8) : UInt32 :=
  (Wavetables.waveMap phase inc w00 w01 w10 w11 xfadeX xfadeY sync).phase

/-- `wave_map`: the sample. -/
@[export fm1_wave_map_out] def waveMapOut (phase : UInt32) (inc : UInt32) (w00 : UInt32) (w01 : UInt32)
    (w10 : UInt32) (w11 : UInt32) (xfadeX : UInt32) (xfadeY : UInt32) (sync : UInt8) : Int16 :=
  (Wavetables.waveMap phase inc w00 w01 w10 w11 xfadeX xfadeY sync).out

/-- `wave_line`: the phase after the sample. -/
@[export fm1_wave_line_phase] def waveLinePhase (phase : UInt32) (inc : UInt32) (waveA : UInt32)
    (waveB : UInt32) (xfadeA : UInt32) (stepA : UInt32) (maskA : UInt32) (waveC : UInt32) (waveD : UInt32)
    (xfadeB : UInt32) (stepB : UInt32) (maskB : UInt32) (balance : UInt32) (sync : UInt8) : UInt32 :=
  (Wavetables.waveLine phase inc waveA waveB xfadeA stepA maskA waveC waveD xfadeB stepB maskB balance sync).phase

/-- `wave_line`: the sample. -/
@[export fm1_wave_line_out] def waveLineOut (phase : UInt32) (inc : UInt32) (waveA : UInt32)
    (waveB : UInt32) (xfadeA : UInt32) (stepA : UInt32) (maskA : UInt32) (waveC : UInt32) (waveD : UInt32)
    (xfadeB : UInt32) (stepB : UInt32) (maskB : UInt32) (balance : UInt32) (sync : UInt8) : Int16 :=
  (Wavetables.waveLine phase inc waveA waveB xfadeA stepA maskA waveC waveD xfadeB stepB maskB balance sync).out

/-- `paraphonic`: the root phase after the step. -/
@[export fm1_paraphonic_p0] def paraphonicP0 (p0 : UInt32) (p1 : UInt32) (p2 : UInt32) (p3 : UInt32)
    (inc0 : UInt32) (inc1 : UInt32) (inc2 : UInt32) (inc3 : UInt32) (waveA : UInt32) (waveB : UInt32)
    (balance : UInt32) : UInt32 :=
  (Wavetables.paraphonic p0 p1 p2 p3 inc0 inc1 inc2 inc3 waveA waveB balance).phase0

/-- `paraphonic`: the first chord note's phase after the step. -/
@[export fm1_paraphonic_p1] def paraphonicP1 (p0 : UInt32) (p1 : UInt32) (p2 : UInt32) (p3 : UInt32)
    (inc0 : UInt32) (inc1 : UInt32) (inc2 : UInt32) (inc3 : UInt32) (waveA : UInt32) (waveB : UInt32)
    (balance : UInt32) : UInt32 :=
  (Wavetables.paraphonic p0 p1 p2 p3 inc0 inc1 inc2 inc3 waveA waveB balance).phase1

/-- `paraphonic`: the second chord note's phase after the step. -/
@[export fm1_paraphonic_p2] def paraphonicP2 (p0 : UInt32) (p1 : UInt32) (p2 : UInt32) (p3 : UInt32)
    (inc0 : UInt32) (inc1 : UInt32) (inc2 : UInt32) (inc3 : UInt32) (waveA : UInt32) (waveB : UInt32)
    (balance : UInt32) : UInt32 :=
  (Wavetables.paraphonic p0 p1 p2 p3 inc0 inc1 inc2 inc3 waveA waveB balance).phase2

/-- `paraphonic`: the third chord note's phase after the step. -/
@[export fm1_paraphonic_p3] def paraphonicP3 (p0 : UInt32) (p1 : UInt32) (p2 : UInt32) (p3 : UInt32)
    (inc0 : UInt32) (inc1 : UInt32) (inc2 : UInt32) (inc3 : UInt32) (waveA : UInt32) (waveB : UInt32)
    (balance : UInt32) : UInt32 :=
  (Wavetables.paraphonic p0 p1 p2 p3 inc0 inc1 inc2 inc3 waveA waveB balance).phase3

/-- `paraphonic`: the sample. -/
@[export fm1_paraphonic_out] def paraphonicOut (p0 : UInt32) (p1 : UInt32) (p2 : UInt32) (p3 : UInt32)
    (inc0 : UInt32) (inc1 : UInt32) (inc2 : UInt32) (inc3 : UInt32) (waveA : UInt32) (waveB : UInt32)
    (balance : UInt32) : Int16 :=
  (Wavetables.paraphonic p0 p1 p2 p3 inc0 inc1 inc2 inc3 waveA waveB balance).out

