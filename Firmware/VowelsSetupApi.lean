import Firmware.VowelsSetup

set_option compiler.extract_closed false

/-! C entry points for `Firmware/VowelsSetup.lean`: one function per setup quantity, called once per block by
`voices/vowels_setup_glue.c`. -/

/-- The phase step of formant `formant` (0 to 2) of a vowel. -/
@[export fm1_vowels_setup_vowel_increment] def vowelsSetupVowelIncrement (parameter0 : Int32)
    (parameter1 : Int32) (formant : UInt32) : UInt32 :=
  VowelsSetup.vowelIncrement parameter0 parameter1 formant

/-- The amplitude of formant `formant` of a vowel. -/
@[export fm1_vowels_setup_vowel_amplitude] def vowelsSetupVowelAmplitude (parameter0 : Int32)
    (formant : UInt32) : UInt32 :=
  VowelsSetup.vowelAmplitude parameter0 formant

/-- The phase step of formant `formant` of the consonant picked by `random`. -/
@[export fm1_vowels_setup_consonant_increment] def vowelsSetupConsonantIncrement (random : Int32)
    (parameter1 : Int32) (formant : UInt32) : UInt32 :=
  VowelsSetup.consonantIncrement random parameter1 formant

/-- The amplitude of formant `formant` of the consonant picked by `random`. -/
@[export fm1_vowels_setup_consonant_amplitude] def vowelsSetupConsonantAmplitude (random : Int32)
    (formant : UInt32) : UInt32 :=
  VowelsSetup.consonantAmplitude random formant

/-- The noise of the consonant picked by `random`. -/
@[export fm1_vowels_setup_consonant_noise] def vowelsSetupConsonantNoise (random : Int32) : Int32 :=
  VowelsSetup.consonantNoise random

/-- The cutoff coefficient of formant filter `formant` (0 to 4) of the FOF vowel. -/
@[export fm1_vowels_setup_fof_cutoff] def vowelsSetupFofCutoff (parameter0 : Int32) (parameter1 : Int32)
    (formant : UInt32) : Int32 :=
  VowelsSetup.fofCutoff parameter0 parameter1 formant

/-- The amplitude of formant filter `formant` of the FOF vowel. -/
@[export fm1_vowels_setup_fof_amplitude] def vowelsSetupFofAmplitude (parameter0 : Int32)
    (parameter1 : Int32) (formant : UInt32) : Int32 :=
  VowelsSetup.fofAmplitude parameter0 parameter1 formant

/-- The length of the question mark's dit, in samples. -/
@[export fm1_vowels_setup_question_dit] def vowelsSetupQuestionDit (parameter : Int32) : UInt32 :=
  VowelsSetup.questionDit parameter

/-- The question mark's noise threshold. -/
@[export fm1_vowels_setup_question_threshold] def vowelsSetupQuestionThreshold (parameter : Int32) : Int32 :=
  VowelsSetup.questionThreshold parameter
