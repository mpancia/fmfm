import Firmware.Vowels

set_option compiler.extract_closed false

/-! C entry points for `Firmware/Vowels.lean`: one function per result field. -/

/-- `vowel`: the phase after the sample. -/
@[export fm1_vowel_phase] def vowelPhase (phase : UInt32) (inc : UInt32) (f0 : UInt32) (f1 : UInt32)
    (f2 : UInt32) (inc0 : UInt32) (inc1 : UInt32) (inc2 : UInt32) (amp0 : UInt32) (amp1 : UInt32)
    (amp2 : UInt32) (noise : Int32) (random : Int32) : UInt32 :=
  (Vowels.vowel phase inc f0 f1 f2 inc0 inc1 inc2 amp0 amp1 amp2 noise random).phase

/-- `vowel`: the first formant phase after the sample. -/
@[export fm1_vowel_f0] def vowelF0 (phase : UInt32) (inc : UInt32) (f0 : UInt32) (f1 : UInt32)
    (f2 : UInt32) (inc0 : UInt32) (inc1 : UInt32) (inc2 : UInt32) (amp0 : UInt32) (amp1 : UInt32)
    (amp2 : UInt32) (noise : Int32) (random : Int32) : UInt32 :=
  (Vowels.vowel phase inc f0 f1 f2 inc0 inc1 inc2 amp0 amp1 amp2 noise random).formant0

/-- `vowel`: the second formant phase after the sample. -/
@[export fm1_vowel_f1] def vowelF1 (phase : UInt32) (inc : UInt32) (f0 : UInt32) (f1 : UInt32)
    (f2 : UInt32) (inc0 : UInt32) (inc1 : UInt32) (inc2 : UInt32) (amp0 : UInt32) (amp1 : UInt32)
    (amp2 : UInt32) (noise : Int32) (random : Int32) : UInt32 :=
  (Vowels.vowel phase inc f0 f1 f2 inc0 inc1 inc2 amp0 amp1 amp2 noise random).formant1

/-- `vowel`: the third formant phase after the sample. -/
@[export fm1_vowel_f2] def vowelF2 (phase : UInt32) (inc : UInt32) (f0 : UInt32) (f1 : UInt32)
    (f2 : UInt32) (inc0 : UInt32) (inc1 : UInt32) (inc2 : UInt32) (amp0 : UInt32) (amp1 : UInt32)
    (amp2 : UInt32) (noise : Int32) (random : Int32) : UInt32 :=
  (Vowels.vowel phase inc f0 f1 f2 inc0 inc1 inc2 amp0 amp1 amp2 noise random).formant2

/-- `vowel`: the sample. -/
@[export fm1_vowel_out] def vowelOut (phase : UInt32) (inc : UInt32) (f0 : UInt32) (f1 : UInt32)
    (f2 : UInt32) (inc0 : UInt32) (inc1 : UInt32) (inc2 : UInt32) (amp0 : UInt32) (amp1 : UInt32)
    (amp2 : UInt32) (noise : Int32) (random : Int32) : Int16 :=
  (Vowels.vowel phase inc f0 f1 f2 inc0 inc1 inc2 amp0 amp1 amp2 noise random).out

/-- `fof_saw`: the phase after the step. -/
@[export fm1_fof_saw_phase] def fofSawPhase (phase : UInt32) (inc : UInt32) (next : Int32) : UInt32 :=
  (Vowels.fofSaw phase inc next).phase

/-- `fof_saw`: this step's saw sample. -/
@[export fm1_fof_saw_here] def fofSawHere (phase : UInt32) (inc : UInt32) (next : Int32) : Int32 :=
  (Vowels.fofSaw phase inc next).here

/-- `fof_saw`: the share carried to the next step. -/
@[export fm1_fof_saw_next] def fofSawNext (phase : UInt32) (inc : UInt32) (next : Int32) : Int32 :=
  (Vowels.fofSaw phase inc next).next

/-- `fof_filter`: the low-pass state after the step. -/
@[export fm1_fof_filter_lp] def fofFilterLp (lp : Int32) (bp : Int32) (f : Int32) (amp : Int32)
    (input : Int32) : Int32 :=
  (Vowels.fofFilter lp bp f amp input).lp

/-- `fof_filter`: the band-pass state after the step. -/
@[export fm1_fof_filter_bp] def fofFilterBp (lp : Int32) (bp : Int32) (f : Int32) (amp : Int32)
    (input : Int32) : Int32 :=
  (Vowels.fofFilter lp bp f amp input).bp

/-- `fof_filter`: the filter's share of the output. -/
@[export fm1_fof_filter_contribution] def fofFilterContribution (lp : Int32) (bp : Int32) (f : Int32)
    (amp : Int32) (input : Int32) : Int32 :=
  (Vowels.fofFilter lp bp f amp input).contribution

/-- `fof_out`: the average of the clipped sum with the last sample. -/
@[export fm1_fof_out_mid] def fofOutMid (sum : Int32) (previous : Int32) : Int16 :=
  (Vowels.fofOut sum previous).mid

/-- `fof_out`: the clipped sum. -/
@[export fm1_fof_out_out] def fofOutOut (sum : Int32) (previous : Int32) : Int16 :=
  (Vowels.fofOut sum previous).out

/-- `question`: the phase after the sample. -/
@[export fm1_question_phase] def questionPhase (phase : UInt32) (inc : UInt32) (cycle : UInt32)
    (cycleIndex : UInt32) (on : UInt8) (seed : Int32) (length : Int16) (dit : UInt32) (threshold : Int32)
    (parameter : Int32) (r1 : Int32) (r2 : Int32) : UInt32 :=
  (Vowels.question phase inc cycle cycleIndex (on != 0) seed length dit threshold parameter r1 r2).phase

/-- `question`: the dit counter after the sample. -/
@[export fm1_question_cycle] def questionCycle (phase : UInt32) (inc : UInt32) (cycle : UInt32)
    (cycleIndex : UInt32) (on : UInt8) (seed : Int32) (length : Int16) (dit : UInt32) (threshold : Int32)
    (parameter : Int32) (r1 : Int32) (r2 : Int32) : UInt32 :=
  (Vowels.question phase inc cycle cycleIndex (on != 0) seed length dit threshold parameter r1 r2).cycle

/-- `question`: the position in the code after the sample. -/
@[export fm1_question_index] def questionIndex (phase : UInt32) (inc : UInt32) (cycle : UInt32)
    (cycleIndex : UInt32) (on : UInt8) (seed : Int32) (length : Int16) (dit : UInt32) (threshold : Int32)
    (parameter : Int32) (r1 : Int32) (r2 : Int32) : UInt32 :=
  (Vowels.question phase inc cycle cycleIndex (on != 0) seed length dit threshold parameter r1 r2).cycleIndex

/-- `question`: 1 if the tone is on after the sample. -/
@[export fm1_question_on] def questionOn (phase : UInt32) (inc : UInt32) (cycle : UInt32)
    (cycleIndex : UInt32) (on : UInt8) (seed : Int32) (length : Int16) (dit : UInt32) (threshold : Int32)
    (parameter : Int32) (r1 : Int32) (r2 : Int32) : UInt8 :=
  (if (Vowels.question phase inc cycle cycleIndex (on != 0) seed length dit threshold parameter r1 r2).on then 1 else 0)

/-- `question`: the noise seed after the sample. -/
@[export fm1_question_seed] def questionSeed (phase : UInt32) (inc : UInt32) (cycle : UInt32)
    (cycleIndex : UInt32) (on : UInt8) (seed : Int32) (length : Int16) (dit : UInt32) (threshold : Int32)
    (parameter : Int32) (r1 : Int32) (r2 : Int32) : Int32 :=
  (Vowels.question phase inc cycle cycleIndex (on != 0) seed length dit threshold parameter r1 r2).seed

/-- `question`: the remaining dits after the sample. -/
@[export fm1_question_length] def questionLength (phase : UInt32) (inc : UInt32) (cycle : UInt32)
    (cycleIndex : UInt32) (on : UInt8) (seed : Int32) (length : Int16) (dit : UInt32) (threshold : Int32)
    (parameter : Int32) (r1 : Int32) (r2 : Int32) : Int16 :=
  (Vowels.question phase inc cycle cycleIndex (on != 0) seed length dit threshold parameter r1 r2).length

/-- `question`: the sample. -/
@[export fm1_question_out] def questionOut (phase : UInt32) (inc : UInt32) (cycle : UInt32)
    (cycleIndex : UInt32) (on : UInt8) (seed : Int32) (length : Int16) (dit : UInt32) (threshold : Int32)
    (parameter : Int32) (r1 : Int32) (r2 : Int32) : Int16 :=
  (Vowels.question phase inc cycle cycleIndex (on != 0) seed length dit threshold parameter r1 r2).out

