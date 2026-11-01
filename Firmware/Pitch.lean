import Firmware.BraidsData

set_option compiler.extract_closed false

/-!
Braids' pitch to phase step (`ComputePhaseIncrement` in `voices/braids/analog_oscillator.cc` and
`digital_oscillator.cc`). A pitch is a MIDI note in 1/128 semitones. The table holds the top octave, one phase
step per 16 pitch units, and every lower octave is that step shifted right once per octave. Scalar only: the
chip's audio interrupt cannot allocate.
-/

namespace Pitch

/-- One entry of Braids' table of phase steps for the top octave (97 entries, in
`voices/braids/resources.cc`). The body is the data, generated from the C source
(`BraidsData.oscillatorIncrement`); on the chip the C reads its own copy. Trusted: that the one-line C
accessor reads the same table. -/
@[extern "fm1_braids_oscillator_increment"] def incrementTable (index : UInt32) : UInt32 :=
  (BraidsData.oscillatorIncrement index.toNat).toUInt32

/-- The table's top, in pitch units: note 128. Pitches at or above it are held one unit below. -/
@[inline] def tableStart : Int32 := 128 * 128

/-- One octave, in pitch units. -/
@[inline] def octave : UInt32 := 12 * 128

/-- How far below the table's top a pitch is, in pitch units, from 1 to 49152. The clamp keeps every pitch
below the top, so this is never 0. -/
@[inline] def below (pitch : Int16) : UInt32 :=
  let clamped := if pitch.toInt32 ≥ tableStart then tableStart - 1 else pitch.toInt32
  (tableStart - clamped).toUInt32

/-- How many octaves down from the table a pitch is, from 1 to 32: the number of right shifts of its step. -/
@[inline] def octaveShifts (pitch : Int16) : UInt32 := (below pitch + (octave - 1)) / octave

/-- A pitch folded into the table's octave, from 0 to 1535. -/
@[inline] def folded (pitch : Int16) : UInt32 := octaveShifts pitch * octave - below pitch

/-- Which table entry a pitch falls on. The entry after it is blended in. -/
@[inline] def tableIndex (pitch : Int16) : UInt32 := folded pitch >>> 4

/-- The table's step at the folded pitch, with the two nearest entries blended by the low four pitch bits. -/
@[inline] def topOctaveStep (pitch : Int16) : UInt32 :=
  let a := incrementTable (tableIndex pitch)
  let b := incrementTable (tableIndex pitch + 1)
  a + (((b - a).toInt32 * (folded pitch &&& 0xF).toInt32) >>> 4).toUInt32

/-- The phase step per sample for a pitch, as a 32-bit fraction of a cycle. A pitch 32 octaves below the table
(-31233 and lower) has no step: the original shifts by 32 there, which the chip's shifter reads as 0. -/
@[inline] def phaseIncrement (pitch : Int16) : UInt32 :=
  let shifts := octaveShifts pitch
  if shifts ≥ 32 then 0 else topOctaveStep pitch >>> shifts

end Pitch
