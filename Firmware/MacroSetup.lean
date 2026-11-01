import Firmware.Percussion

set_option compiler.extract_closed false

/-!
The per-block setup of Braids' macro oscillator (`MacroOscillator::Render*` in
`voices/braids/macro_oscillator.cc`): the pitch and the two parameters of a block become the parameters,
detuned pitches, balance, filter cutoff and fuzz the analog oscillators and the mixing loops run with. A pitch
is a MIDI note in 1/128 semitones; a parameter is 0 to 32767. A detuned pitch is cut to 16 bits, as the C++
does when it passes an `int` to `set_pitch(int16_t)`. Scalar only.
-/

namespace MacroSetup

/-- One entry of Braids' 65-entry table of detune intervals for the triple oscillators, in 1/128 semitones
(`intervals` in `voices/braids/macro_oscillator.cc`), looked up by C. Trusted data. -/
@[extern "fm1_braids_macro_interval"] opaque intervalTable (index : UInt32) : Int16

/-- CSAW: how far the second parameter shifts the sample, 0 to 2047. -/
@[inline] def csawShift (parameter1 : Int16) : Int32 :=
  ((0 - (parameter1.toInt32 - 32767)) >>> 4).toInt16.toInt32

/-- Morph's three zones of the first parameter: 0 fades triangle to saw, 1 saw to square, 2 widens the
square's pulse against a sine. -/
@[inline] def morphZone (parameter0 : Int16) : UInt32 :=
  if parameter0 ≤ 10922 then 0 else if parameter0 ≤ 21845 then 1 else 2

/-- Morph's 16-bit crossfade from its first oscillator to its second. -/
@[inline] def morphBalance (parameter0 : Int16) : UInt32 :=
  let p := parameter0.toInt32
  (if p ≤ 10922 then p * 6 else if p ≤ 21845 then 65535 - (p - 10923) * 6 else 0).toUInt32 &&& 0xFFFF

/-- The parameter morph's first oscillator runs with: the square's pulse width in the last zone, else 0. -/
@[inline] def morphParameter (parameter0 : Int16) : Int32 :=
  if parameter0 ≤ 21845 then 0 else ((parameter0.toInt32 - 21846) * 3).toInt16.toInt32

/-- Morph's low-pass cutoff as a pitch, 0 to 32767: the pitch, an octave up, lowered by half the second
parameter. -/
@[inline] def morphLpCutoff (pitch parameter1 : Int16) : Int32 :=
  let cutoff := pitch.toInt32 - (parameter1.toInt32 >>> 1) + 16384
  if cutoff < 0 then 0 else if cutoff > 32767 then 32767 else cutoff

/-- Morph's low-pass coefficient, from the filter cutoff table. -/
@[inline] def morphCutoff (pitch parameter1 : Int16) : Int32 :=
  Percussion.svfCutoff (morphLpCutoff pitch parameter1)

/-- How much of morph's overdriven signal is mixed in: twice the second parameter, fading out above note
80. -/
@[inline] def morphFuzz (pitch parameter1 : Int16) : Int32 :=
  let fuzz := parameter1.toInt32 <<< 1
  let faded := fuzz - ((pitch.toInt32 - 10240) <<< 4)
  if pitch > 10240 then (if faded < 0 then 0 else faded) else fuzz

/-- Which interval a triple's parameter falls on, 0 to 63. -/
@[inline] def tripleIndex (parameter : Int16) : UInt32 := (parameter.toInt32 >>> 9).toUInt32

/-- The interval a triple's parameter crossfades towards, 0 to 64: the one nearest the parameter's high byte
rounded up. -/
@[inline] def tripleIndex2 (parameter : Int16) : UInt32 := (((parameter.toInt32 >>> 8) + 1) >>> 1).toUInt32

/-- A triple oscillator's detune in 1/128 semitones: the two intervals around the parameter, blended by its
low byte. -/
@[inline] def tripleDetune (parameter : Int16) : Int32 :=
  let a := (intervalTable (tripleIndex parameter)).toInt32
  let b := (intervalTable (tripleIndex2 parameter)).toInt32
  let xfade := ((parameter.toInt32 <<< 8).toUInt32 &&& 0xFFFF).toInt32
  (a + (((b - a) * xfade) >>> 16)).toInt16.toInt32

/-- A triple oscillator's pitch: the block's pitch detuned by its parameter. -/
@[inline] def triplePitch (pitch parameter : Int16) : Int16 :=
  (pitch.toInt32 + tripleDetune parameter).toInt16

/-- The sub oscillator's pitch: two octaves down in the lower half of the second parameter, else one. -/
@[inline] def subPitch (pitch parameter1 : Int16) : Int16 :=
  (pitch.toInt32 - (if parameter1 < 16384 then 3072 else 1536)).toInt16

/-- The synced oscillator's pitch: the block's pitch raised by a quarter of the first parameter. -/
@[inline] def dualSyncPitch (pitch parameter0 : Int16) : Int16 :=
  (pitch.toInt32 + (parameter0.toInt32 >>> 2)).toInt16

/-- A fold amount held between 0 and 32767. -/
@[inline] def attenuation (x : Int32) : Int32 := if x < 0 then 0 else if x > 32767 then 32767 else x

/-- The sine fold's parameter: the first parameter, fading out above note 92. -/
@[inline] def sineTriangleSineParameter (pitch parameter0 : Int16) : Int32 :=
  ((parameter0.toInt32 * attenuation (32767 - 6 * (pitch.toInt32 - 11776))) >>> 15).toInt16.toInt32

/-- The triangle fold's parameter: the first parameter, fading out above note 80. -/
@[inline] def sineTriangleTriParameter (pitch parameter0 : Int16) : Int32 :=
  ((parameter0.toInt32 * attenuation (32767 - 7 * (pitch.toInt32 - 10240))) >>> 15).toInt16.toInt32

/-- The second buzz's pitch: the block's pitch raised by the second parameter's high byte. -/
@[inline] def buzzPitch (pitch parameter1 : Int16) : Int16 :=
  (pitch.toInt32 + (parameter1.toInt32 >>> 8)).toInt16

end MacroSetup
