import Firmware.Physical

set_option compiler.extract_closed false

/-!
# Physical models, the setup of one block

The numbers `RenderComb`, `RenderPlucked`, `RenderBowed`, `RenderBlown` and `RenderFluted` in
`voices/braids/digital_oscillator.cc` work out before their sample loop (`Firmware/Physical.lean`) runs: the
comb's smoothed pitch and delay, a new string's oversampling, size, mask and fill count, the loss and update
chance, each pipe's delay times with the octave transpositions that fit them into their lines, the bow and
breath settings, the body filter, and the envelope pointer clamps after the block. The pitch's delay time
(`delay_`, from `DigitalOscillator::ComputeDelay`) is an input. Scalar only, one value per function.

Braids halves a delay in a `while` loop until it fits its line. Here each loop is a fixed chain of steps that
count a halving while the test holds: a step after the test first fails adds nothing, because the halved
values only fall, and no delay (even one wrapped below zero) needs more halvings than the chain has.
-/

namespace PhysicalSetup

/-- Comb filter: the pitch, moved by `param0` up to half an octave either way. -/
@[inline] def combPitch (pitch param0 : Int32) : Int32 := pitch + ((param0 - 16384) >>> 1)

/-- Comb filter: the delay pitch smoothed from the block before, a sixteenth of the way to the new pitch, as
the 16-bit value the C++ keeps. -/
@[inline] def combFilteredPitch (previous pitch param0 : Int32) : Int16 :=
  ((15 * previous + combPitch pitch param0) >>> 4).toInt16

/-- Comb filter: the delay time of the smoothed pitch (as 16.16 samples) held to the 8192 line. -/
@[inline] def combDelay (delay : UInt32) : UInt32 := if delay > 8192 * 65536 then 8192 * 65536 else delay

/-- Comb filter: the whole samples of the delay. -/
@[inline] def combDelayIntegral (delay : UInt32) : UInt32 := combDelay delay >>> 16

/-- Comb filter: the fraction of a sample of the delay, out of 65536. -/
@[inline] def combDelayFractional (delay : UInt32) : Int32 := (combDelay delay &&& 0xffff).toInt32

/-- Plucked string: one halving of the oversampling search. `n` halvings so far; one more if the step still
passes 2^23 (as a signed value, so a step at or above 2^31 is never halved). -/
@[inline] def pluckShiftStep (increment n : UInt32) : UInt32 :=
  if (increment >>> n).toInt32 > 8388608 then n + 1 else n

/-- Plucked string: the oversampling of a new string, the halvings of the doubled phase step `increment` that
bring it to 2^23 or below. Nine steps cover any step below 2^31. -/
@[inline] def pluckShift (increment : UInt32) : UInt32 :=
  let three := pluckShiftStep increment (pluckShiftStep increment (pluckShiftStep increment 0))
  let six := pluckShiftStep increment (pluckShiftStep increment (pluckShiftStep increment three))
  pluckShiftStep increment (pluckShiftStep increment (pluckShiftStep increment six))

/-- Plucked string: the entries a string of oversampling `shift` uses in its 1025-entry line. -/
@[inline] def pluckSize (shift : UInt32) : UInt32 := 1024 >>> shift

/-- Plucked string: the mask that keeps a position inside a string of `pluckSize shift` entries. -/
@[inline] def pluckMask (shift : UInt32) : UInt32 := pluckSize shift - 1

/-- Plucked string: how many entries of a new string are filled with noise, between an eighth and the whole
string by `param1`. -/
@[inline] def pluckInitialization (shift : UInt32) (param1 : Int32) : UInt32 :=
  let width := (3 * param1) >>> 1
  (pluckSize shift * ((8192 : Int32) + width).toUInt32) >>> 16

/-- Plucked string: the chance each entry is averaged per sample, out of 65536 (65535 up to half of
`param0`, then falling). -/
@[inline] def pluckUpdateProbability (param0 : Int32) : UInt32 :=
  if param0 < 16384 then 65535 else ((131072 : Int32) - (param0 >>> 3) * 31).toUInt32

/-- Plucked string: the loss per averaging, out of 4096: less for high notes, at least 256, scaled down by
`param0` to nothing at half. The first difference is cut to 16 bits, as the C++ holds it in an `int16_t`. -/
@[inline] def pluckLoss (increment : UInt32) (param0 : Int32) : Int32 :=
  let raw := ((4096 : UInt32) - (increment >>> 14)).toUInt16.toInt16.toInt32
  let floored := if raw < 256 then 256 else raw
  if param0 < 16384 then ((floored * (16384 - param0)) >>> 14).toInt16.toInt32 else 0

/-- Bowed string: the bow pressure, 172 down to 45 with `param0`. -/
@[inline] def bowedBow (param0 : Int32) : Int32 := ((172 : Int32) - (param0 >>> 8)).toInt16.toInt32

/-- Bowed string: the string's delay in 16.16 samples: half the pitch's, less two samples for the one-pole. -/
@[inline] def bowedDelay (delay : UInt32) : UInt32 := (delay >>> 1) - 2 * 65536

/-- Bowed string: the bridge side's share of the delay, 6 to 69 parts in 256 by `param1`. -/
@[inline] def bowedBridge (delay : UInt32) (param1 : Int32) : UInt32 :=
  (bowedDelay delay >>> 8) * ((6 : Int32) + (param1 >>> 9)).toInt16.toInt32.toUInt32

/-- Bowed string: one step of the octave transposition: one more halving while the neck side passes 4095
samples or the bridge side 1023. -/
@[inline] def bowedFitStep (delay bridge n : UInt32) : UInt32 :=
  if (delay >>> n) - (bridge >>> n) > 4095 * 65536 || (bridge >>> n) > 1023 * 65536 then n + 1 else n

/-- Bowed string: four transposition steps. -/
@[inline] def bowedFit4 (delay bridge n : UInt32) : UInt32 :=
  bowedFitStep delay bridge
    (bowedFitStep delay bridge (bowedFitStep delay bridge (bowedFitStep delay bridge n)))

/-- Bowed string: sixteen transposition steps. -/
@[inline] def bowedFit16 (delay bridge n : UInt32) : UInt32 :=
  bowedFit4 delay bridge (bowedFit4 delay bridge (bowedFit4 delay bridge (bowedFit4 delay bridge n)))

/-- Bowed string: the octaves the string is transposed up to fit its lines. -/
@[inline] def bowedOctaves (delay : UInt32) (param1 : Int32) : UInt32 :=
  let d := bowedDelay delay
  let b := bowedBridge delay param1
  bowedFit16 d b (bowedFit16 d b 0)

/-- Bowed string: the bridge side's delay in 16.16 samples, transposed to fit. -/
@[inline] def bowedBridgeDelay (delay : UInt32) (param1 : Int32) : UInt32 :=
  bowedBridge delay param1 >>> bowedOctaves delay param1

/-- Bowed string: the neck side's delay in 16.16 samples, the rest of the string, transposed to fit. -/
@[inline] def bowedNeckDelay (delay : UInt32) (param1 : Int32) : UInt32 :=
  let n := bowedOctaves delay param1
  (bowedDelay delay >>> n) - (bowedBridge delay param1 >>> n)

/-- Bowed string: the envelope pointer after a block, as the 16 bits the state keeps, held back to 1440 (entry
720 of the 752-entry bowing envelope) so the next block's reads stay inside the envelope. -/
@[inline] def bowedExcitationClamp (ptr : UInt32) : UInt32 :=
  let kept := ptr.toUInt16.toUInt32
  if kept >>> 1 ≥ 720 then 1440 else kept

/-- Blown pipe: one step of the octave transposition: one more halving while the bore passes 2047 samples. -/
@[inline] def blownFitStep (delay n : UInt32) : UInt32 := if (delay >>> n) > 2047 * 65536 then n + 1 else n

/-- Blown pipe: four transposition steps. -/
@[inline] def blownFit4 (delay n : UInt32) : UInt32 :=
  blownFitStep delay (blownFitStep delay (blownFitStep delay (blownFitStep delay n)))

/-- Blown pipe: sixteen transposition steps. -/
@[inline] def blownFit16 (delay n : UInt32) : UInt32 :=
  blownFit4 delay (blownFit4 delay (blownFit4 delay (blownFit4 delay n)))

/-- Blown pipe: the bore's delay in 16.16 samples: half the pitch's less one sample, transposed to fit. -/
@[inline] def blownDelay (delay : UInt32) : UInt32 :=
  let d := (delay >>> 1) - 65536
  d >>> blownFit16 d (blownFit16 d 0)

/-- Blown pipe: the breath pressure, 28000 down to 11617 with `param0`. -/
@[inline] def blownParameter (param0 : Int32) : Int32 := ((28000 : Int32) - (param0 >>> 1)) &&& 0xffff

/-- Blown pipe: the note that picks the body filter, the pitch two octaves down (raised by `param1`) in
semitones, held to the 128-entry filter table. -/
@[inline] def blownNormalizedPitch (pitch param1 : Int32) : Int32 :=
  let note := ((pitch - (8192 : Int32) + (param1 >>> 1)) >>> 7).toInt16.toInt32
  if note < 0 then 0 else if note > 127 then 127 else note

/-- One entry of Braids' flute body filter table (128 entries), looked up by C. Trusted data. -/
@[extern "fm1_braids_lut_flute_body_filter"] opaque fluteBodyTable (index : UInt32) : UInt16

/-- Blown pipe: the body filter coefficient of the note. -/
@[inline] def blownFilterCoefficient (pitch param1 : Int32) : Int32 :=
  (fluteBodyTable (blownNormalizedPitch pitch param1).toUInt32).toUInt32.toInt32

/-- Flute: the bore's delay before the jet is taken out: twice the pitch's, less two samples. -/
@[inline] def flutedBore (delay : UInt32) : UInt32 := (delay <<< 1) - 2 * 65536

/-- Flute: the jet's delay, 48 to 79 parts in 256 of the bore's by `param1`. -/
@[inline] def flutedJet (delay : UInt32) (param1 : Int32) : UInt32 :=
  (flutedBore delay >>> 8) * ((48 : Int32) + (param1 >>> 10)).toUInt32

/-- Flute: one step of the octave transposition: one more halving while the bore passes 4095 samples or the
jet 1023. -/
@[inline] def flutedFitStep (bore jet n : UInt32) : UInt32 :=
  if (bore >>> n) > 4095 * 65536 || (jet >>> n) > 1023 * 65536 then n + 1 else n

/-- Flute: four transposition steps. -/
@[inline] def flutedFit4 (bore jet n : UInt32) : UInt32 :=
  flutedFitStep bore jet (flutedFitStep bore jet (flutedFitStep bore jet (flutedFitStep bore jet n)))

/-- Flute: sixteen transposition steps. -/
@[inline] def flutedFit16 (bore jet n : UInt32) : UInt32 :=
  flutedFit4 bore jet (flutedFit4 bore jet (flutedFit4 bore jet (flutedFit4 bore jet n)))

/-- Flute: the octaves the pipe is transposed up to fit its lines. -/
@[inline] def flutedOctaves (delay : UInt32) (param1 : Int32) : UInt32 :=
  let j := flutedJet delay param1
  let b := flutedBore delay - j
  flutedFit16 b j (flutedFit16 b j 0)

/-- Flute: the bore's delay in 16.16 samples, the jet taken out, transposed to fit. -/
@[inline] def flutedBoreDelay (delay : UInt32) (param1 : Int32) : UInt32 :=
  (flutedBore delay - flutedJet delay param1) >>> flutedOctaves delay param1

/-- Flute: the jet's delay in 16.16 samples, transposed to fit. -/
@[inline] def flutedJetDelay (delay : UInt32) (param1 : Int32) : UInt32 :=
  flutedJet delay param1 >>> flutedOctaves delay param1

/-- Flute: the breath noise intensity, 2100 down to 53 with `param0`. -/
@[inline] def flutedBreath (param0 : Int32) : Int32 := ((2100 : Int32) - (param0 >>> 4)) &&& 0xffff

/-- Flute: the note that picks the body filter, the pitch in semitones held to the 128-entry table. Braids
reads past the table above note 127; the pitch is held there instead. -/
@[inline] def flutedNote (pitch : Int32) : Int32 :=
  let note := pitch >>> 7
  if note < 0 then 0 else if note > 127 then 127 else note

/-- Flute: the body filter coefficient of the pitch. -/
@[inline] def flutedFilterCoefficient (pitch : Int32) : Int32 :=
  (fluteBodyTable (flutedNote pitch).toUInt32).toUInt32.toInt32

/-- Flute: the envelope pointer after a block, as the 16 bits the state keeps, held back to 360 (of the
392-entry blowing envelope) so the next block's reads stay inside the envelope. -/
@[inline] def flutedExcitationClamp (ptr : UInt32) : UInt32 :=
  let kept := ptr.toUInt16.toUInt32
  if kept ≥ 360 then 360 else kept

end PhysicalSetup
