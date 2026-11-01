import Firmware.Noise
import Firmware.Percussion
import Firmware.Pitch
import Firmware.BraidsData

set_option compiler.extract_closed false

/-!
# Noise engines, the setup of one block

Port of what `DigitalOscillator::RenderFilteredNoise`, `RenderTwinPeaksNoise`, `RenderClockedNoise`,
`RenderGranularCloud` and `RenderParticleNoise` compute before their loops (Braids, Emilie Gillet, MIT): the
filter coefficients, gains, periods and grain starts of a block from the pitch and the two parameters. The
loops are in `Firmware/Noise.lean`; random numbers come from C. Lean shifts bind tighter than `*` and `+`,
so shifted products are parenthesized.
-/

namespace NoiseSetup

/-- One entry of Braids' filter scale table (257 entries), looked up by C. Trusted data. -/
@[extern "fm1_braids_lut_svf_scale"] opaque scaleTable (index : UInt32) : UInt16

/-- One entry of Braids' grain envelope rate table (257 entries). The body is the data, generated from
`resources.cc` (`BraidsData.granularEnvelopeRate`); on the chip the C reads its own copy. Trusted: that the
one-line C accessor reads the same table. -/
@[extern "fm1_braids_lut_granular_envelope_rate"] def rateTable (index : UInt32) : UInt16 :=
  (BraidsData.granularEnvelopeRate index.toNat).toUInt16

/-- A parameter with hysteresis: it moves to `parameter` only once that is more than `window` away from the
value held so far. -/
@[inline] def held (parameter previous : Int16) (window : Int32) : Int16 :=
  if parameter.toInt32 > previous.toInt32 + window || parameter.toInt32 < previous.toInt32 - window then
    parameter
  else previous

/-- Filtered noise: the filter's cutoff for the pitch. -/
@[inline] def cutoff (pitch : Int16) : Int32 := Percussion.svfCutoff pitch.toInt32

/-- Filtered noise: the filter's damping for the first parameter. -/
@[inline] def damp (param0 : Int16) : Int32 := Percussion.svfDamp param0.toInt32

/-- Filtered noise: the band-pass gain, rising then falling with the second parameter. -/
@[inline] def bpGain (param1 : Int16) : Int32 :=
  if param1.toInt32 < 16384 then param1.toInt32 else 32767 - param1.toInt32

/-- Filtered noise: the low-pass gain, fading out over the first half of the second parameter. -/
@[inline] def lpGain (param1 : Int16) : Int32 := if param1.toInt32 < 16384 then 16384 - param1.toInt32 else 0

/-- Filtered noise: the high-pass gain, fading in over the second half of the second parameter. -/
@[inline] def hpGain (param1 : Int16) : Int32 := if param1.toInt32 < 16384 then 0 else param1.toInt32 - 16384

/-- Filtered noise: the gain that keeps the filter's output level when the cutoff passes the scale table. -/
@[inline] def gainCorrection (pitch param0 : Int16) : Int32 :=
  let f := cutoff pitch
  let scale := (Digital.lutAt scaleTable (param0.toInt32.toUInt32 <<< 17)).toInt32
  if f > scale then scale * 32767 / f else 32767

/-- Twin peaks: the resonators' sharpness, from 65240 up with the first parameter. -/
@[inline] def peakQ (param0 : Int16) : UInt32 := (65240 : UInt32) + (param0.toInt32 >>> 7).toUInt32

/-- Twin peaks: the sharpness squared, as the resonators use it. -/
@[inline] def peakQSquared (param0 : Int16) : Int32 := ((peakQ param0 * peakQ param0) >>> 17).toInt32

/-- Twin peaks: the second peak's pitch, the first moved by up to half the second parameter's range. -/
@[inline] def secondPeakPitch (pitch param1 : Int16) : Int32 :=
  (pitch.toInt32 + ((param1.toInt32 - 16384) >>> 1)).toInt16.toInt32

/-- Twin peaks: a resonator's coefficient for a pitch, scaled by the sharpness. -/
@[inline] def peakCoefficient (pitch : Int32) (param0 : Int16) : Int32 :=
  (((Noise.resonatorAt pitch).1 * peakQ param0) >>> 16).toInt32

/-- Twin peaks: a resonator's scale for a pitch. -/
@[inline] def peakScale (pitch : Int32) : Int32 := (Noise.resonatorAt pitch).2.toInt32

/-- Twin peaks: the makeup gain, out of 8192, falling with the first parameter. -/
@[inline] def peakMakeup (param0 : Int16) : Int32 := (8191 : Int32) - (param0.toInt32 >>> 2)

/-- Clocked noise: the phase step moved up to three octaves up, as far as it stays below half a cycle. -/
@[inline] def clockIncrement (inc : UInt32) : UInt32 :=
  let a := if inc < (1 : UInt32) <<< 31 then inc <<< 1 else inc
  let b := if a < (1 : UInt32) <<< 31 then a <<< 1 else a
  if b < (1 : UInt32) <<< 31 then b <<< 1 else b

/-- Clocked noise: the step of the generator's period, from the held first parameter. -/
@[inline] def cycleIncrement (prev0 : Int16) : UInt32 :=
  Pitch.phaseIncrement (prev0.toInt32 - 16384).toInt16 <<< 1

/-- Clocked noise: how many quantization steps the held second parameter asks for, at least 2. -/
@[inline] def numSteps (prev1 : Int16) : UInt32 :=
  let steps := ((1 : Int32) + (prev1.toInt32 >>> 10)).toUInt32
  if steps == 1 then 2 else steps

/-- Clocked noise: the width of one quantization step. -/
@[inline] def quantizerDivider (prev1 : Int16) : UInt32 := 65536 / numSteps prev1

/-- Granular cloud: whether a grain is restarted this block, its envelope past its end or never started. -/
@[inline] def grainDone (envelope envInc : UInt32) : Bool := envelope > (1 : UInt32) <<< 24 || envInc == 0

/-- Granular cloud: whether a restarted grain starts again, one chance in four by a random word. -/
@[inline] def grainStarts (word : UInt32) : Bool := (word &&& 0xFFFF) < 0x4000

/-- Granular cloud: a new grain's envelope rate, from the first parameter. -/
@[inline] def grainRate (param0 : Int16) : UInt32 :=
  (rateTable (param0.toInt32 >>> 7).toUInt32).toUInt32 <<< 3

/-- Granular cloud: a grain's envelope rate for the block: unchanged while it plays, 0 once done, and a new
rate when it starts again. -/
@[inline] def grainRateStart (envelope envInc word : UInt32) (param0 : Int16) : UInt32 :=
  if grainDone envelope envInc then (if grainStarts word then grainRate param0 else 0) else envInc

/-- Granular cloud: a grain's envelope phase for the block: 0 when it starts again, else unchanged. -/
@[inline] def grainEnvelopeStart (envelope envInc word : UInt32) : UInt32 :=
  if grainDone envelope envInc && grainStarts word then 0 else envelope

/-- Granular cloud: a new grain's phase step, the oscillator's detuned by a random amount scaled by the second
parameter. A downward detune is halved. -/
@[inline] def grainIncrement (inc : UInt32) (sample param1 : Int16) : UInt32 :=
  let pitchMod := (sample.toInt32 * param1.toInt32) >>> 16
  let phi := (inc >>> 8).toInt32
  inc + (phi * (if pitchMod < 0 then pitchMod >>> 8 else pitchMod >>> 7)).toUInt32

/-- Particle noise: how likely a hit is each sample, out of 2^23. -/
@[inline] def particleDensity (param0 : Int16) : UInt32 := ((1024 : Int32) + param0.toInt32).toUInt32

end NoiseSetup
