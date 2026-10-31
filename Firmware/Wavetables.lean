import Firmware.Digital

set_option compiler.extract_closed false

/-!
# Wavetable engines, one sample at a time

Port of the wavetable, wave map, wave line and paraphonic wave engines of Braids (`digital_oscillator.cc`,
Emilie Gillet, MIT). A wave is named by its number in Braids' table of 129-byte waves; choosing the waves
(per block) and the loops stay in C. Lean shifts bind tighter than `*` and `+`, so shifted products are
parenthesized.
-/

/-- One byte of one of Braids' waves (`wt_waves`, 129 bytes each), looked up by C. Trusted data. -/
@[extern "fm1_braids_wt_wave"] opaque Wavetables.waveByte (wave index : UInt32) : UInt8

/-- Wave `wave` at a 32-bit phase, the two nearest bytes blended and centred on zero (Braids' `Interpolate824`
for bytes, which returns a 16-bit value). -/
@[inline] def Wavetables.read (wave phase : UInt32) : Int32 :=
  let a := (Wavetables.waveByte wave (Analog.tableIndex phase)).toUInt32.toInt32
  let b := (Wavetables.waveByte wave (Analog.tableIndex phase + 1)).toUInt32.toInt32
  (((a <<< 8) + (((b - a) * (phase &&& 0xFFFFFF).toInt32) >>> 16)) - 32768).toInt16.toInt32

/-- Two waves at the same phase, blended by `balance` (16 bits; Braids' `Crossfade`). -/
@[inline] def Wavetables.crossfade (waveA waveB phase balance : UInt32) : Int32 :=
  let a := Wavetables.read waveA phase
  let b := Wavetables.read waveB phase
  (a + (((b - a) * (balance &&& 0xFFFF).toInt32) >>> 16)).toInt16.toInt32

/-- The result of one wavetable or wave map sample: the phase and the sample. -/
structure WaveStep where
  phase : UInt32
  out : Int16

/-- A wave morphing between two neighbours in a wavetable, read twice per sample at half the phase step (`inc` is
half the oscillator's). `balance` is the position between the waves. A sync pulse restarts the cycle. -/
@[inline] def Wavetables.wavetable (phase inc waveA waveB balance : UInt32) (sync : UInt8) : WaveStep :=
  let p1 := if sync != 0 then 0 else phase + inc
  let p2 := p1 + inc
  let s1 := (Wavetables.crossfade waveA waveB (p1 >>> 1) balance) >>> 1
  let s2 := (Wavetables.crossfade waveA waveB (p2 >>> 1) balance) >>> 1
  { phase := p2, out := (s1 + s2).toInt16 }

/-- A wave picked from a 16 by 16 map: the four corner waves of one square, blended by `xfadeX` (between the
rows) and `xfadeY` (between the columns). -/
@[inline] def Wavetables.waveMap (phase inc w00 w01 w10 w11 xfadeX xfadeY : UInt32) (sync : UInt8) : WaveStep :=
  let p1 := if sync != 0 then 0 else phase + inc
  let p2 := p1 + inc
  let one (p : UInt32) : Int32 :=
    (Digital.mix (Wavetables.crossfade w00 w01 (p >>> 1) xfadeY) (Wavetables.crossfade w10 w11 (p >>> 1) xfadeY)
      (xfadeX &&& 0xFFFF)) >>> 1
  { phase := p2, out := (one p1 + one p2).toInt16 }

/-- A half step of the wave line: two readings (a, b), each a crossfade of two waves with its own phase mask,
mixed by `balance`. The mask blocks the phase to fewer steps, which makes the "rough" reading. -/
@[inline] def Wavetables.linePair (phase waveA waveB xfadeA maskA waveC waveD xfadeB maskB balance : UInt32) : Int32 :=
  Digital.mix (Wavetables.crossfade waveA waveB ((phase >>> 1) &&& maskA) xfadeA)
    (Wavetables.crossfade waveC waveD ((phase >>> 1) &&& maskB) xfadeB) (balance &&& 0xFFFF)

/-- One wave line sample: two half steps. The first reading's crossfade moves by `stepA` between the halves,
the second's by `stepB`. -/
@[inline] def Wavetables.waveLine (phase inc waveA waveB xfadeA stepA maskA waveC waveD xfadeB stepB maskB balance : UInt32)
    (sync : UInt8) : WaveStep :=
  let p1 := if sync != 0 then 0 else phase
  let m1 := Wavetables.linePair p1 waveA waveB xfadeA maskA waveC waveD xfadeB maskB balance
  let p2 := p1 + inc
  let m2 := Wavetables.linePair p2 waveA waveB ((xfadeA + stepA) &&& 0xFFFF) maskA waveC waveD
    ((xfadeB + stepB) &&& 0xFFFF) maskB balance
  { phase := p2 + inc, out := ((m1 + m2) >>> 1).toInt16 }

/-- The result of one paraphonic step: the four phases and the sample. -/
structure ParaStep where
  phase0 : UInt32
  phase1 : UInt32
  phase2 : UInt32
  phase3 : UInt32
  out : Int16

/-- Four copies of one wave morph (the root and three chord notes) added and divided by four. -/
@[inline] def Wavetables.paraphonic (p0 p1 p2 p3 inc0 inc1 inc2 inc3 waveA waveB balance : UInt32) : ParaStep :=
  let a0 := p0 + inc0
  let a1 := p1 + inc1
  let a2 := p2 + inc2
  let a3 := p3 + inc3
  let sum := Wavetables.crossfade waveA waveB (a0 >>> 1) balance + Wavetables.crossfade waveA waveB (a1 >>> 1) balance +
    Wavetables.crossfade waveA waveB (a2 >>> 1) balance + Wavetables.crossfade waveA waveB (a3 >>> 1) balance
  { phase0 := a0, phase1 := a1, phase2 := a2, phase3 := a3, out := (sum >>> 2).toInt16 }
