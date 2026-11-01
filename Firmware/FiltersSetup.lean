import Firmware.Pitch
import Firmware.Percussion

set_option compiler.extract_closed false

/-!
# Saw swarm, digital filters, vosim and harmonics: the setup of a block

The lines at the top of each `Render*` of Braids' `digital_oscillator.cc` (Emilie Gillet, MIT) that turn the
pitch and the two parameters into phase steps, a cutoff and the harmonic amplitudes. Scalar only, one function
per quantity; `voices/filters_setup_glue.c` calls each once per block. Lean shifts bind tighter than `*` and
`+`, so shifted products are parenthesized.
-/

namespace FiltersSetup

/-- The swarm's spread between neighbouring saws, in 1/65536 pitch units: the square of the parameter raised
by 1024, over 512. -/
@[inline] def swarmDetune (parameter : Int32) : Int32 :=
  let raised := parameter + 1024
  (raised * raised) >>> 9

/-- The phase step of saw `saw` (0 to 6) of the swarm: the pitch moved by `saw - 3` times the detune, with the
steps of the two nearest pitches blended by the fraction. The moved pitch is cut to 16 bits as Braids does. -/
@[inline] def swarmIncrement (pitch parameter saw : Int32) : UInt32 :=
  let offset := swarmDetune parameter * (saw - 3)
  let whole := offset >>> 16
  let a := (Pitch.phaseIncrement (pitch + whole).toInt16).toInt32
  let b := (Pitch.phaseIncrement (pitch + whole + 1).toInt16).toInt32
  (a + (((b - a) * (offset &&& 0xFFFF)) >>> 16)).toUInt32

/-- The swarm's high-pass cutoff as a pitch: the oscillator's pitch moved by the second parameter around its
first third, twice as steeply below it, held to 0 to 32767. -/
@[inline] def swarmHpCutoff (pitch parameter : Int32) : Int32 :=
  let slope : Int32 := if parameter < 10922 then 24 else 12
  let moved := pitch + (((parameter - 10922) * slope) >>> 5)
  if moved < 0 then 0 else if moved > 32767 then 32767 else moved

/-- The swarm's high-pass coefficient: the cutoff table at the cutoff pitch. -/
@[inline] def swarmCutoff (pitch parameter : Int32) : Int32 :=
  Percussion.svfCutoff (swarmHpCutoff pitch parameter)

/-- The pitch of the digital filter's resonance: the oscillator's pitch moved by half the first parameter
around 2048, cut to 16 bits as Braids does, then held to at most 16383. -/
@[inline] def filterPitch (pitch parameter : Int32) : Int32 :=
  let shifted := (pitch + ((parameter - 2048) >>> 1)).toInt16.toInt32
  if shifted > 16383 then 16383 else shifted

/-- The phase step the resonance glides toward over the block. -/
@[inline] def filterIncrement (pitch parameter : Int32) : UInt32 :=
  Pitch.phaseIncrement (filterPitch pitch parameter).toInt16

/-- How much the resonance's phase step moves per sample to go from `current` to `target` over a block of
`size` samples: the difference over the size, as a wrapped unsigned step when falling. -/
@[inline] def filterIncrementStep (current target size : UInt32) : UInt32 :=
  if current < target then (target - current) / size else ~~~((current - target) / size)

/-- The phase step of a vosim formant: the step of the pitch that is half its parameter. -/
@[inline] def vosimIncrement (parameter : Int32) : UInt32 := Pitch.phaseIncrement (parameter >>> 1).toInt16

/-- Where the harmonics' first peak sits, in 1/256 partials: the first parameter spread over the twelve. -/
@[inline] def harmonicsPeak (parameter : Int32) : Int32 := (12 * parameter) >>> 7

/-- Where the second peak sits: half as far out as the first, six partials up. -/
@[inline] def harmonicsSecondPeak (parameter : Int32) : Int32 := (harmonicsPeak parameter >>> 1) + 12 * 128

/-- The height of the second peak: the square of the second parameter, 0 to 32767. -/
@[inline] def harmonicsSecondPeakAmount (parameter : Int32) : Int32 := (parameter * parameter) >>> 15

/-- The width of both peaks, 4 to 3973: the fourth power of a tent over the second parameter. -/
@[inline] def harmonicsWidth (parameter : Int32) : Int32 :=
  let sqrtsqrt := if parameter < 16384 then parameter >>> 6 else (511 : Int32) - (parameter >>> 6)
  let sqrt := (sqrtsqrt * sqrtsqrt) >>> 10
  sqrt * sqrt + 4

/-- A bell of height `height` and width `width` around `peak`, at partial position `x` (in 1/256 partials). -/
@[inline] def harmonicsBell (x peak width height : Int32) : Int32 :=
  let d := x - peak
  height * 128 / (128 + d * d / width)

/-- The unscaled gain of partial `index` (0 to 11): the two bells added. -/
@[inline] def harmonicsGain (parameter0 parameter1 index : Int32) : Int32 :=
  let x := index <<< 8
  let width := harmonicsWidth parameter1
  harmonicsBell x (harmonicsPeak parameter0) width 32768 +
    harmonicsBell x (harmonicsSecondPeak parameter0) width (harmonicsSecondPeakAmount parameter1)

/-- The factor that scales the twelve gains so that they sum to full scale, in 1/65536. -/
@[inline] def harmonicsAttenuation (parameter0 parameter1 : Int32) : Int32 :=
  let total := harmonicsGain parameter0 parameter1 0 + harmonicsGain parameter0 parameter1 1 +
    harmonicsGain parameter0 parameter1 2 + harmonicsGain parameter0 parameter1 3 +
    harmonicsGain parameter0 parameter1 4 + harmonicsGain parameter0 parameter1 5 +
    harmonicsGain parameter0 parameter1 6 + harmonicsGain parameter0 parameter1 7 +
    harmonicsGain parameter0 parameter1 8 + harmonicsGain parameter0 parameter1 9 +
    harmonicsGain parameter0 parameter1 10 + harmonicsGain parameter0 parameter1 11
  2147483647 / total

/-- The amplitude partial `index` glides toward: its gain scaled by `attenuation`, or 0 when the partial
would pass a quarter of the sample rate at phase step `inc` (Braids' aliasing guard). -/
@[inline] def harmonicsTarget (parameter0 parameter1 : Int32) (inc : UInt32) (attenuation index : Int32) :
    Int32 :=
  if (inc >>> 16) * (index.toUInt32 + 1) > 0x4000 then 0
  else (harmonicsGain parameter0 parameter1 index * attenuation) >>> 16

end FiltersSetup
