import Firmware.Filters

set_option compiler.extract_closed false

/-!
# Percussion, one sample at a time

Port of the struck bell, struck drum, kick, snare and cymbal engines of Braids (`digital_oscillator.cc`,
`excitation.h`, `svf.h`; Emilie Gillet, MIT), in the style of `Firmware/Digital.lean`. The sample arithmetic,
the exciter and the filter are here; the partial tables and the per-block setup are in
`Firmware/PercussionSetup.lean`. Lean shifts bind tighter than `*` and `+`, so shifted products are
parenthesized.
-/

/-- One entry of Braids' filter cutoff table (257 entries), looked up by C. Trusted data. -/
@[extern "fm1_braids_lut_svf_cutoff"] opaque Percussion.cutoffTable (index : UInt32) : UInt16

/-- One entry of Braids' filter damping table (257 entries), looked up by C. Trusted data. -/
@[extern "fm1_braids_lut_svf_damp"] opaque Percussion.dampTable (index : UInt32) : UInt16

/-- The filter coefficient for a frequency (`Svf::Process` when the frequency changed). -/
@[inline] def Percussion.svfCutoff (frequency : Int32) : Int32 :=
  (Digital.lutAt Percussion.cutoffTable (frequency.toUInt32 <<< 17)).toInt32

/-- The damping for a resonance. -/
@[inline] def Percussion.svfDamp (resonance : Int32) : Int32 :=
  (Digital.lutAt Percussion.dampTable (resonance.toUInt32 <<< 17)).toInt32

/-- The result of one filter step. -/
structure PercSvfStep where
  lp : Int32
  bp : Int32
  out : Int32

/-- Braids' `Svf`: a state-variable filter with cutoff `f`, damping `damp` and an optional `punch` that opens it
with the signal. `mode` 0 gives the low-pass, 1 the band-pass, 2 the high-pass. -/
@[inline] def Percussion.svf (input f damp punch lp bp : Int32) (mode : UInt8) : PercSvfStep :=
  let signal := if lp > 4096 then lp else 2048
  let f' := if punch != 0 then f + (((signal >>> 4) * punch) >>> 9) else f
  let damp' := if punch != 0 then damp + ((signal - 2048) >>> 3) else damp
  let notch := input - ((bp * damp') >>> 15)
  let lp' := Digital.clip (lp + ((f' * bp) >>> 15))
  let hp := notch - lp'
  let bp' := Digital.clip (bp + ((f' * hp) >>> 15))
  { lp := lp', bp := bp', out := if mode == 1 then bp' else if mode == 2 then hp else lp' }

/-- The result of one exciter step. -/
structure ExciteStep where
  state : Int32
  counter : Int32
  out : Int32

/-- Braids' `Excitation`: a decaying pulse (`decay` per sample, 12-bit) that fires with `level` when `counter`
runs out. -/
@[inline] def Percussion.excite (state decay counter level : Int32) : ExciteStep :=
  let decayed := ((state.toUInt32 * decay.toUInt32) >>> 12).toInt32   -- unsigned, as in the C++
  let counter' := if counter > 0 then counter - 1 else counter
  let fired := counter > 0 && counter' == 0
  let state' := if fired then decayed + (if level < 0 then 0 - level else level) else decayed
  { state := state', counter := counter', out := if level < 0 then 0 - state' else state' }

/-- The result of the kick's output stage. -/
structure KickStep where
  lp : Int32
  out : Int16

/-- The kick: the exciter and the resonator added, then low-passed by `coefficient`. -/
@[inline] def Percussion.kickOut (excitation resonator lp coefficient : Int32) : KickStep :=
  let lp' := Digital.clip (lp + ((((excitation >>> 4) + resonator) - lp) * coefficient) >>> 15)
  { lp := lp', out := lp'.toInt16 }

/-- The snare: two filtered exciters (with a bit of each unfiltered) at gains `g1` and `g2`, plus filtered noise. -/
@[inline] def Percussion.snareMix (filtered1 excitation1 filtered2 excitation2 noise g1 g2 : Int32) : Int16 :=
  (Digital.clip ((((filtered1 + (excitation1 >>> 4)) * g1) >>> 15) + (((filtered2 + (excitation2 >>> 4)) * g2) >>> 15)
    + noise)).toInt16

/-- The cymbal's metallic noise: six square waves (given as phases) added. -/
@[inline] def Percussion.hatNoise (p0 p1 p2 p3 p4 p5 : UInt32) : Int32 :=
  (((p0 >>> 31) + (p1 >>> 31) + (p2 >>> 31) + (p3 >>> 31) + (p4 >>> 31) + (p5 >>> 31)).toInt32 - 3) * 5461

/-- The cymbal's white noise from its generator's state, halved. -/
@[inline] def Percussion.hatWhite (rng : UInt32) : Int32 := ((rng >>> 16).toInt32 - 32768) >>> 1

/-- The cymbal: the filtered metallic and white noises, blended by `xfade`. -/
@[inline] def Percussion.cymbalOut (metal white xfade : Int32) : Int16 :=
  (Digital.clip metal + (((Digital.clip white - Digital.clip metal) * xfade) >>> 15)).toInt16

/-- The result of one partial's step. -/
structure PartialStep where
  phase : UInt32
  contribution : Int32

/-- One partial of the bell: a sine at `amplitude`. -/
@[inline] def Percussion.bellPartial (phase inc : UInt32) (amplitude : Int32) : PartialStep :=
  let p := phase + inc
  { phase := p, contribution := (Analog.sineAt p * amplitude) >>> 17 }

/-- A partial's amplitude after one block of decay: between a long and a short decay by `parameter`. -/
@[inline] def Percussion.decay (amplitude decayLong decayShort parameter : Int32) : Int32 :=
  let balance0 := ((32767 - parameter) >>> 8).toInt16.toInt32
  let balance := ((balance0 * balance0) >>> 7).toInt16.toInt32
  let d := decayLong - (((decayLong - decayShort) * balance) >>> 7)
  (amplitude * d) >>> 16

/-- The result of the drum's noise filter: three cascaded low-passes. -/
structure DrumNoiseStep where
  lp0 : Int32
  lp1 : Int32
  lp2 : Int32

/-- The drum's noise, limited to half scale and low-passed three times by `f`. -/
@[inline] def Percussion.drumNoise (noise lp0 lp1 lp2 f : Int32) : DrumNoiseStep :=
  let n := if noise > 16384 then 16384 else if noise < -16384 then -16384 else noise
  let a := lp0 + (((n - lp0) * f) >>> 15)
  let b := lp1 + (((a - lp1) * f) >>> 15)
  let c := lp2 + (((b - lp2) * f) >>> 15)
  { lp0 := a, lp1 := b, lp2 := c }

/-- One partial of the drum: a sine whose amplitude fades from `amplitude` to `target` over the block. -/
@[inline] def Percussion.drumPartial (phase inc : UInt32) (amplitude target fade : Int32) : PartialStep :=
  let p := phase + inc
  let a := amplitude + (((target - amplitude) * fade) >>> 15)
  { phase := p, contribution := (Analog.sineAt p * a) >>> 16 }

/-- The drum's mix: the first partial, two partials ring-modulated by the noise at `noiseGain`, and all the
partials at `harmonicsGain`. -/
@[inline] def Percussion.drumMix (partial0 partial1 partial3 harmonics lp2 noiseGain harmonicsGain : Int32) : Int16 :=
  let mode1 := (partial1 * lp2) >>> 8
  let mode2 := (partial3 * lp2) >>> 9
  (Digital.clip (partial0 + ((mode1 * (12288 - noiseGain)) >>> 14) + ((mode2 * noiseGain) >>> 14) +
    ((harmonics * harmonicsGain) >>> 14))).toInt16
