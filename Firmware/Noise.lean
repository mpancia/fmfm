import Firmware.Digital

set_option compiler.extract_closed false

/-!
# Noise engines, one sample at a time

Port of the filtered noise, twin peaks, clocked noise, granular cloud and particle noise engines of Braids
(`digital_oscillator.cc`, Emilie Gillet, MIT), in the style of `Firmware/Digital.lean`. Random numbers come
from C (Braids' generator, so the sequence stays the same). Lean shifts bind tighter than `*` and `+`, so
shifted products are parenthesized.
-/

/-- One entry of Braids' resonator coefficient table (257 entries), looked up by C. Trusted data. -/
@[extern "fm1_braids_lut_resonator_coefficient"] opaque Noise.resonatorCoefficient (index : UInt32) : UInt16

/-- One entry of Braids' resonator scale table (257 entries), looked up by C. Trusted data. -/
@[extern "fm1_braids_lut_resonator_scale"] opaque Noise.resonatorScale (index : UInt32) : UInt16

/-- One entry of Braids' grain envelope (257 entries), looked up by C. Trusted data. -/
@[extern "fm1_braids_lut_granular_envelope"] opaque Noise.grainEnvelope (index : UInt32) : UInt16

/-- The result of one filtered-noise sample. -/
structure NoiseSvfStep where
  lp : Int32
  bp : Int32
  out : Int16

/-- White noise (`input`, already halved) through a state-variable filter, its low, band and high-pass outputs
mixed by three gains, corrected by `gain` and soft-clipped. -/
@[inline] def Noise.filtered (input f damp bp lp lpGain bpGain hpGain gain : Int32) : NoiseSvfStep :=
  let notch := input - ((bp * damp) >>> 15)
  let lp' := Digital.clip (lp + ((f * bp) >>> 15))
  let hp := notch - lp'
  let bp' := bp + ((f * hp) >>> 15)
  let mixed := Digital.clip (((lpGain * lp') >>> 14) + ((bpGain * bp') >>> 14) + ((hpGain * hp) >>> 14))
  let corrected := (mixed * gain) >>> 15
  { lp := lp', bp := bp', out := (Analog.shape Digital.overdriveTable ((corrected + 32768).toUInt32)).toInt16 }

/-- One two-pole resonator: the input scaled by `s` (sign kept), plus feedback by `c` and `q2`, clipped. -/
@[inline] def Noise.resonate (input s c q2 y1 y2 : Int32) : Int32 :=
  let scaled := if input > 0 then (input * s) >>> 16 else (0 : Int32) - (((0 - input) * s) >>> 16)
  Digital.clip (scaled + ((y1 * c) >>> 15) - ((y2 * q2) >>> 15))

/-- The result of one twin-peaks sample: both resonators' last two outputs and the sample. -/
structure TwinStep where
  y11 : Int32
  y12 : Int32
  y21 : Int32
  y22 : Int32
  out : Int16

/-- Twin peaks: noise (`input`, already halved) through two resonators, summed, boosted by `makeup` and
soft-clipped. -/
@[inline] def Noise.twinPeaks (input s1 c1 s2 c2 q2 makeup y11 y12 y21 y22 : Int32) : TwinStep :=
  let y10 := Noise.resonate input s1 c1 q2 y11 y12
  let y20 := Noise.resonate input s2 c2 q2 y21 y22
  let sum := y10 + y20
  let boosted := Digital.clip (sum + ((sum * makeup) >>> 13))
  { y11 := y10, y12 := y11, y21 := y20, y22 := y21,
    out := (Analog.shape Digital.overdriveTable ((boosted + 32768).toUInt32)).toInt16 }

/-- The result of one clocked-noise sample. -/
structure ClockedStep where
  phase : UInt32
  rng : UInt32
  cycle : UInt32
  held : Int16
  out : Int16

/-- Clocked noise: on each tick of the phase a new random value is held, quantized to steps of `divider`; the
generator restarts from `seed` when its own period (`cycleInc`) wraps. -/
@[inline] def Noise.clocked (phase inc rng cycle cycleInc seed : UInt32) (held : Int16) (divider : UInt32)
    (sync : UInt8) : ClockedStep :=
  let p0 := if sync != 0 then 0 else phase + inc
  let tick := p0 < inc
  let rng1 := Digital.lcg rng
  let cycle1 := cycle + cycleInc
  let restart := cycle1 < cycleInc
  let rng2 := if restart then seed else rng1
  let cycle2 := if restart then cycleInc else cycle1
  let raw := rng2 &&& 0xFFFF
  let quantized := ((raw - raw % divider) + (divider >>> 1)).toUInt16.toInt16
  let held' := if tick then quantized else held
  { phase := if tick then inc else p0, rng := if tick then rng2 else rng, cycle := if tick then cycle2 else cycle,
    held := held', out := held' }

/-- The result of one grain's step: its phases and its share of the sample. -/
structure GrainStep where
  phase : UInt32
  envelope : UInt32
  contribution : Int32

/-- One grain: a sine under its envelope. -/
@[inline] def Noise.grain (phase inc envelope envInc : UInt32) : GrainStep :=
  let p := phase + inc
  let e := envelope + envInc
  { phase := p, envelope := e,
    contribution := (Analog.sineAt p * (Noise.grainEnvelope (e >>> 16)).toUInt32.toInt32) >>> 17 }

/-- The cloud's sample: the grains' sum, limited to 16 bits. -/
@[inline] def Noise.cloudOut (sum : Int32) : Int16 :=
  (if sum < -32768 then -32768 else if sum > 32767 then 32767 else sum).toInt16

/-- A resonator's coefficient and scale for a pitch, limited to the table's range. -/
@[inline] def Noise.resonatorAt (pitch : Int32) : UInt32 × UInt32 :=
  let p := (if pitch < 0 then 0 else if pitch > 16383 then 16383 else pitch).toUInt32 <<< 17
  (Digital.lutAt Noise.resonatorCoefficient p, Digital.lutAt Noise.resonatorScale p)

/-- The result of a particle hit: the three resonators' coefficients and scales. -/
structure ParticleHit where
  c1 : Int32
  s1 : Int32
  c2 : Int32
  s2 : Int32
  c3 : Int32
  s3 : Int32

/-- A particle hit retunes the three resonators around `pitch`, scattered by `noise` and `spread`. -/
@[inline] def Noise.particleHit (noise : UInt32) (pitch spread : Int32) : ParticleHit :=
  let a := ((noise &&& 0x0FFF).toInt32 - 0x800).toInt16.toInt32
  let b := (((noise >>> 15) &&& 0x1FFF).toInt32 - 0x1000).toInt16.toInt32
  let p1 := (pitch + (((3 * a) * spread) >>> 17) + 0x600).toInt16.toInt32
  let p2 := (pitch + ((a * spread) >>> 15) + 0x980).toInt16.toInt32
  let p3 := (pitch + ((b * spread) >>> 16) + 0x790).toInt16.toInt32
  let r1 := Noise.resonatorAt p1
  let r2 := Noise.resonatorAt p2
  let r3 := Noise.resonatorAt p3
  { c1 := (r1.1.toInt32 * 32636) >>> 15, s1 := r1.2.toInt32, c2 := (r2.1.toInt32 * 32636) >>> 15, s2 := r2.2.toInt32,
    c3 := (r3.1.toInt32 * 32636) >>> 15, s3 := r3.2.toInt32 }

/-- The result of one particle-noise sample. -/
structure ParticleStep where
  amplitude : UInt16
  y11 : Int32
  y12 : Int32
  y21 : Int32
  y22 : Int32
  y31 : Int32
  y32 : Int32
  out : Int16

/-- Particle noise: a decaying burst of noise (`amplitude`, reset to full by each hit) through three
resonators. -/
@[inline] def Noise.particle (noise : UInt32) (amplitude : UInt16) (s1 c1 s2 c2 s3 c3 y11 y12 y21 y22 y31 y32 : Int32) :
    ParticleStep :=
  let input := (noise.toUInt16.toInt16.toInt32 * amplitude.toUInt32.toInt32) >>> 16
  let amplitude' := ((amplitude.toUInt32 * 64763) >>> 16).toUInt16
  let y10 := Noise.resonate input s1 c1 32506 y11 y12
  let y20 := Noise.resonate input s2 c2 32506 y21 y22
  let y30 := Noise.resonate input s3 c3 32506 y31 y32
  { amplitude := amplitude', y11 := y10, y12 := y11, y21 := y20, y22 := y21, y31 := y30, y32 := y31,
    out := (Digital.clip (y10 + y20 + y30)).toInt16 }
