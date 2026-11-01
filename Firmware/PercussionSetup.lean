import Firmware.Percussion
import Firmware.Pitch

set_option compiler.extract_closed false

/-!
# Percussion, the setup of one block

The numbers `RenderStruckBell`, `RenderStruckDrum`, `RenderKick`, `RenderSnare` and `RenderCymbal` in
`voices/braids/digital_oscillator.cc` work out from the pitch and the two parameters before their sample loop
(`Firmware/Percussion.lean`) runs: the partial tables, each partial's pitch and phase step, the decay a block
applies, the drum's noise filter and gains, the kick's resonance and low-pass, the snare's decay, levels and
gains, the hat's seven steps. Scalar only, one value per function: the C++ asks for each number it stores.
Lean shifts bind tighter than `*` and `+`, so shifted products are parenthesized.
-/

namespace PercussionSetup

/-- Bell partial `i` (0 to 10): its offset from the pitch, in 1/128 semitones (Braids' `kBellPartials`). -/
@[inline] def bellPartial (i : UInt32) : Int32 :=
  match i with
  | 0 => -1284 | 1 => -1283 | 2 => -184 | 3 => -183 | 4 => 385 | 5 => 1175 | 6 => 1536 | 7 => 2233
  | 8 => 2434 | 9 => 2934 | _ => 3110

/-- Bell partial `i`: its amplitude when struck (Braids' `kBellPartialAmplitudes`). -/
@[inline] def bellAmplitude (i : UInt32) : Int32 :=
  match i with
  | 0 => 8192 | 1 => 5488 | 2 => 8192 | 3 => 14745 | 4 => 21872 | 5 => 13680 | 6 => 11960 | 7 => 10895
  | 8 => 10895 | 9 => 6144 | _ => 10895

/-- Bell partial `i`: its slowest decay per block, out of 65536 (Braids' `kBellPartialDecayLong`). -/
@[inline] def bellDecayLong (i : UInt32) : Int32 :=
  match i with
  | 0 => 65533 | 1 => 65533 | 2 => 65533 | 3 => 65532 | 4 => 65531 | 5 => 65531 | 6 => 65530 | 7 => 65529
  | 8 => 65527 | 9 => 65523 | _ => 65519

/-- Bell partial `i`: its fastest decay per block (Braids' `kBellPartialDecayShort`). -/
@[inline] def bellDecayShort (i : UInt32) : Int32 :=
  match i with
  | 0 => 65308 | 1 => 65283 | 2 => 65186 | 3 => 65123 | 4 => 64839 | 5 => 64889 | 6 => 64632 | 7 => 64409
  | 8 => 64038 | 9 => 63302 | _ => 62575

/-- Drum partial `i` (0 to 5): its offset from the pitch (Braids' `kDrumPartials`). -/
@[inline] def drumPartial (i : UInt32) : Int32 :=
  match i with
  | 0 => 0 | 1 => 0 | 2 => 1041 | 3 => 1747 | 4 => 1846 | _ => 3072

/-- Drum partial `i`: its amplitude when struck (Braids' `kDrumPartialAmplitude`). -/
@[inline] def drumAmplitude (i : UInt32) : Int32 :=
  match i with
  | 0 => 16986 | 1 => 2654 | 2 => 3981 | 3 => 5308 | 4 => 3981 | _ => 2985

/-- Drum partial `i`: its slowest decay per block (Braids' `kDrumPartialDecayLong`). -/
@[inline] def drumDecayLong (i : UInt32) : Int32 :=
  match i with
  | 0 => 65533 | 1 => 65531 | 2 => 65531 | 3 => 65531 | 4 => 65531 | _ => 65516

/-- Drum partial `i`: its fastest decay per block (Braids' `kDrumPartialDecayShort`). -/
@[inline] def drumDecayShort (i : UInt32) : Int32 :=
  match i with
  | 0 => 65083 | 1 => 64715 | 2 => 64715 | 3 => 64715 | 4 => 64715 | _ => 62312

/-- Bell partial `i`'s pitch: the pitch plus its offset, detuned by `param1` up for odd partials and down for
even ones. Both sums are cut to 16 bits, as the C++ holds them in an `int16_t`. -/
@[inline] def bellPartialPitch (pitch param1 : Int32) (i : UInt32) : Int16 :=
  let base := (pitch + bellPartial i).toInt16.toInt32
  let detune := param1 >>> 7
  (if i &&& 1 == 1 then base + detune else base - detune).toInt16

/-- Bell partial `i`'s phase step: twice the step of its pitch, as the bell runs at half rate. -/
@[inline] def bellIncrement (pitch param1 : Int32) (i : UInt32) : UInt32 :=
  Pitch.phaseIncrement (bellPartialPitch pitch param1 i) <<< 1

/-- Bell partial `i`'s amplitude after one block: decayed between its long and short decay by `param0`, except
that a parameter at 32000 or above keeps the bell ringing without loss. -/
@[inline] def bellDecayed (amplitude param0 : Int32) (i : UInt32) : Int32 :=
  if param0 < 32000 then Percussion.decay amplitude (bellDecayLong i) (bellDecayShort i) param0 else amplitude

/-- Drum partial `i`'s phase step: twice the step of its pitch plus offset (cut to 16 bits). -/
@[inline] def drumIncrement (pitch : Int32) (i : UInt32) : UInt32 :=
  Pitch.phaseIncrement (pitch + drumPartial i).toInt16 <<< 1

/-- Drum partial `i`'s target amplitude for the block: decayed by `param0`, held at 32000 and above. -/
@[inline] def drumDecayed (amplitude param0 : Int32) (i : UInt32) : Int32 :=
  if param0 < 32000 then Percussion.decay amplitude (drumDecayLong i) (drumDecayShort i) param0 else amplitude

/-- The drum's noise filter cutoff: an octave below the pitch, opened by `param1`, held to 0 to 32767. -/
@[inline] def drumCutoff (pitch param1 : Int32) : Int32 :=
  let cutoff := (pitch - (1536 : Int32)) + (param1 >>> 2)
  if cutoff < 0 then 0 else if cutoff > 32767 then 32767 else cutoff

/-- The drum's noise filter coefficient: the cutoff table at the cutoff (`Interpolate824` of the cutoff
shifted by 16). -/
@[inline] def drumFilter (pitch param1 : Int32) : Int32 :=
  (Digital.lutAt Percussion.cutoffTable ((drumCutoff pitch param1).toUInt32 <<< 16)).toInt32

/-- The drum's gain on all its partials: rising with `param1` to 16384. -/
@[inline] def drumHarmonicsGain (param1 : Int32) : Int32 := if param1 < 12888 then param1 + 4096 else 16384

/-- The drum's gain on the noise-modulated partials: nothing below half, then rising to 12888. -/
@[inline] def drumNoiseGain (param1 : Int32) : Int32 :=
  let raw := if param1 < 16384 then 0 else param1 - 16384
  (raw * 12888) >>> 14

/-- The kick's resonance for the decay `param0`: the complement of the decay cubed, taken from 32640. The C++
does this unsigned and hands the result to a 16-bit setter. -/
@[inline] def kickResonance (param0 : Int32) : Int32 :=
  let scaled := (65535 : UInt32) - (param0.toUInt32 <<< 1)
  let squared := (scaled * scaled) >>> 16
  let cubed := (squared * scaled) >>> 18
  (32768 - 128 - cubed).toUInt16.toInt16.toInt32

/-- The kick's low-pass coefficient for `param1`: 128 plus three halves of the parameter's fourth power. -/
@[inline] def kickLpCoefficient (param1 : Int32) : Int32 :=
  let squared := (param1.toUInt32 * param1.toUInt32) >>> 15
  let fourth := (squared * squared) >>> 15
  ((128 : UInt32) + (fourth >>> 1) * 3).toInt32

/-- The snare's decay on a strike: longer for low pitches and for `param1` above half, held to 65535. -/
@[inline] def snareDecay (pitch param1 : Int32) : Int32 :=
  let decay := 49152 - pitch + (if param1 < 16384 then 0 else param1 - 16384)
  if decay > 65535 then 65535 else decay

/-- The snare's resonance on a strike: `base` (29000 or 26500) plus a 32nd of the decay, as a 16-bit value. -/
@[inline] def snareResonance (base pitch param1 : Int32) : Int32 :=
  (base + (snareDecay pitch param1 >>> 5)).toInt16.toInt32

/-- The snare's noise exciter decay on a strike: 4092 plus the top bits of the decay. -/
@[inline] def snarePulseDecay (pitch param1 : Int32) : Int32 :=
  (4092 : Int32) + (snareDecay pitch param1 >>> 14)

/-- The snare's noise exciter level on a strike: 512 plus twice `param1`, which is held to 14336. -/
@[inline] def snareSnappy (param1 : Int32) : Int32 :=
  let snappy := if param1 ≥ 14336 then 14336 else param1
  (512 : Int32) + (snappy <<< 1)

/-- A snare filter's frequency: the pitch `semitones` up, as the 16-bit value the setter takes. -/
@[inline] def snareFrequency (pitch semitones : Int32) : Int32 := (pitch + (semitones <<< 7)).toInt16.toInt32

/-- The snare's gain on its drum part: 22000 less half of `param0`. -/
@[inline] def snareGain1 (param0 : Int32) : Int32 := (22000 : Int32) - (param0 >>> 1)

/-- The snare's gain on its noise part: 22000 plus half of `param0`. -/
@[inline] def snareGain2 (param0 : Int32) : Int32 := (22000 : Int32) + (param0 >>> 1)

/-- The cymbal's root note: note 40 plus half the pitch, as the 16-bit pitch the step takes. -/
@[inline] def cymbalNote (pitch : Int32) : Int16 := ((5120 : Int32) + (pitch >>> 1)).toInt16

/-- The cymbal's phase step `i` (0 to 6): the root's step, five inharmonic ratios of it, and 24 times it. -/
@[inline] def cymbalIncrement (pitch : Int32) (i : UInt32) : UInt32 :=
  let root := Pitch.phaseIncrement (cymbalNote pitch)
  let base := root >>> 10
  match i with
  | 0 => root | 1 => (base * 24273) >>> 4 | 2 => (base * 12561) >>> 4 | 3 => (base * 18417) >>> 4
  | 4 => (base * 22452) >>> 4 | 5 => (base * 31858) >>> 4 | _ => root * 24

/-- The cymbal's filter frequency: half of `param0`, as a 16-bit value. -/
@[inline] def cymbalFrequency (param0 : Int32) : Int32 := (param0 >>> 1).toInt16.toInt32

end PercussionSetup
