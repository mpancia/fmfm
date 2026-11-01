import Firmware.Percussion

set_option compiler.extract_closed false

/-!
# Vowels and the question mark: the setup of a block

The lines at the top of `RenderVowel`, `RenderVowelFof` and `RenderQuestionMark` of Braids'
`digital_oscillator.cc` (Emilie Gillet, MIT) that turn the two parameters into formant steps, amplitudes,
cutoffs and the question mark's timing. The phoneme and formant data stay in C, read through the accessors
below; `voices/vowels_setup_glue.c` calls each function once per block. Lean shifts bind tighter than `*` and
`+`, so shifted products are parenthesized.
-/

namespace VowelsSetup

/-- Formant `formant` (0 to 2) of vowel `vowel` (0 to 8) of Braids' `vowels_data`, as a byte of frequency,
looked up by C. Trusted data. -/
@[extern "fm1_braids_vowel_frequency"] opaque vowelFrequencyAt (vowel formant : UInt32) : UInt8

/-- The amplitude (0 to 15) of formant `formant` of vowel `vowel` of `vowels_data`, looked up by C. -/
@[extern "fm1_braids_vowel_amplitude"] opaque vowelAmplitudeAt (vowel formant : UInt32) : UInt8

/-- Formant `formant` of consonant `consonant` (0 to 7) of Braids' `consonant_data`, as a byte of frequency,
looked up by C. Trusted data. -/
@[extern "fm1_braids_consonant_frequency"] opaque consonantFrequencyAt (consonant formant : UInt32) : UInt8

/-- The amplitude (0 to 15) of formant `formant` of consonant `consonant` of `consonant_data`, looked up by
C. -/
@[extern "fm1_braids_consonant_amplitude"] opaque consonantAmplitudeAt (consonant formant : UInt32) : UInt8

/-- The pitch of formant `formant` (0 to 4) at row `x` and column `y` (0 to 4 each) of the FOF vowel's grid of
voices by vowels (Braids' `formant_f_data`), looked up by C. Trusted data. -/
@[extern "fm1_braids_fof_frequency"] opaque fofFrequencyAt (x y formant : UInt32) : Int16

/-- The amplitude of formant `formant` at row `x` and column `y` of the FOF vowel's grid (`formant_a_data`),
looked up by C. Trusted data. -/
@[extern "fm1_braids_fof_amplitude"] opaque fofAmplitudeAt (x y formant : UInt32) : Int16

/-- Which vowel the first parameter selects, 0 to 7; the one after it is blended in. -/
@[inline] def vowelIndex (parameter : Int32) : UInt32 := (parameter >>> 12).toUInt32

/-- How far from the selected vowel toward the next, 0 to 4095. -/
@[inline] def vowelBalance (parameter : Int32) : UInt32 := (parameter &&& 0xFFF).toUInt32

/-- The multiplier the second parameter applies to every formant's step, 200 to 711. -/
@[inline] def formantShift (parameter : Int32) : UInt32 := ((200 : Int32) + (parameter >>> 6)).toUInt32

/-- The phase step of formant `formant` of a vowel: the frequencies of the two nearest vowels blended by the
balance (the 12 fraction bits are kept), times the shift. -/
@[inline] def vowelIncrement (parameter0 parameter1 : Int32) (formant : UInt32) : UInt32 :=
  let vowel := vowelIndex parameter0
  let balance := vowelBalance parameter0
  ((vowelFrequencyAt vowel formant).toUInt32 * (0x1000 - balance) +
      (vowelFrequencyAt (vowel + 1) formant).toUInt32 * balance) * formantShift parameter1

/-- The amplitude of formant `formant` of a vowel: the two nearest vowels' amplitudes blended by the
balance. -/
@[inline] def vowelAmplitude (parameter0 : Int32) (formant : UInt32) : UInt32 :=
  let vowel := vowelIndex parameter0
  let balance := vowelBalance parameter0
  ((vowelAmplitudeAt vowel formant).toUInt32 * (0x1000 - balance) +
      (vowelAmplitudeAt (vowel + 1) formant).toUInt32 * balance) >>> 12

/-- Which consonant a strike picks, 0 to 7, from the random sample Braids draws. -/
@[inline] def consonantIndex (random : Int32) : UInt32 := ((random + 1) &&& 7).toUInt32

/-- The phase step of formant `formant` of the consonant picked by `random`: its frequency, with 12 fraction
bits, times the shift. -/
@[inline] def consonantIncrement (random parameter1 : Int32) (formant : UInt32) : UInt32 :=
  (consonantFrequencyAt (consonantIndex random) formant).toUInt32 * 0x1000 * formantShift parameter1

/-- The amplitude of formant `formant` of the consonant picked by `random`. -/
@[inline] def consonantAmplitude (random : Int32) (formant : UInt32) : UInt32 :=
  (consonantAmplitudeAt (consonantIndex random) formant).toUInt32

/-- The noise of the consonant picked by `random`: 4095 for the last two consonants, else 0. -/
@[inline] def consonantNoise (random : Int32) : Int32 := if consonantIndex random ≥ 6 then 4095 else 0

/-- Which row (or column) of the FOF vowel's grid a parameter selects, 0 to 3: its top two bits. The row
after it is blended in. -/
@[inline] def fofRow (parameter : Int32) : UInt32 := (parameter >>> 13).toUInt32

/-- Braids' `InterpolateFormantParameter`: a formant's value from a 4-by-4 grid at the point the two
parameters select, each parameter's top two bits picking a row and the rest blending toward the next. Every
blend is cut to 16 bits as the original's `int16_t` does. -/
@[inline] def fofBlend (table : UInt32 → UInt32 → UInt32 → Int16) (x y : Int32) (formant : UInt32) : Int32 :=
  let xi := fofRow x
  let xm := (x <<< 3) &&& 0xFFFF
  let yi := fofRow y
  let ym := (y <<< 3) &&& 0xFFFF
  let a := (table xi yi formant).toInt32
  let b := (table (xi + 1) yi formant).toInt32
  let c := (table xi (yi + 1) formant).toInt32
  let d := (table (xi + 1) (yi + 1) formant).toInt32
  let ab := (a + (((b - a) * xm) >>> 16)).toInt16.toInt32
  let cd := (c + (((d - c) * xm) >>> 16)).toInt16.toInt32
  (ab + (((cd - ab) * ym) >>> 16)).toInt16.toInt32

/-- The cutoff coefficient of formant filter `formant` (0 to 4) of the FOF vowel: the formant's pitch, an
octave up, through the cutoff table, cut to 16 bits as Braids stores it. -/
@[inline] def fofCutoff (parameter0 parameter1 : Int32) (formant : UInt32) : Int32 :=
  (Percussion.svfCutoff (fofBlend fofFrequencyAt parameter1 parameter0 formant + 1536)).toInt16.toInt32

/-- The amplitude of formant filter `formant` of the FOF vowel, a signed 16-bit value. -/
@[inline] def fofAmplitude (parameter0 parameter1 : Int32) (formant : UInt32) : Int32 :=
  fofBlend fofAmplitudeAt parameter1 parameter0 formant

/-- The length of the question mark's dit, in samples: 3600 plus a quarter of what is left of the first
parameter. -/
@[inline] def questionDit (parameter : Int32) : UInt32 :=
  ((3600 : Int32) + ((32767 - parameter) >>> 2)).toUInt32

/-- The question mark's noise threshold: 1024 plus an eighth of the second parameter. -/
@[inline] def questionThreshold (parameter : Int32) : Int32 := (1024 : Int32) + (parameter >>> 3)

end VowelsSetup
