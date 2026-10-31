import Firmware.Digital

set_option compiler.extract_closed false

/-! C entry points for `Firmware/Digital.lean`: one function per result field. `voices/digital_glue.c` includes the
generated code and calls them in its sample loops. -/

/-- fm: the carrier phase after the sample. -/
@[export fm1_fm_phase] def fmPhase (phase : UInt32) (modPhase : UInt32) (inc : UInt32) (modInc : UInt32)
    (index : Int32) (sync : UInt8) : UInt32 :=
  (Digital.fm phase modPhase inc modInc index sync).phase

/-- fm: the modulator phase after the sample. -/
@[export fm1_fm_mod] def fmMod (phase : UInt32) (modPhase : UInt32) (inc : UInt32) (modInc : UInt32)
    (index : Int32) (sync : UInt8) : UInt32 :=
  (Digital.fm phase modPhase inc modInc index sync).modPhase

/-- fm: the sample. -/
@[export fm1_fm_out] def fmOut (phase : UInt32) (modPhase : UInt32) (inc : UInt32) (modInc : UInt32)
    (index : Int32) (sync : UInt8) : Int16 :=
  (Digital.fm phase modPhase inc modInc index sync).out

/-- feedback_fm: the carrier phase after the sample. -/
@[export fm1_feedback_fm_phase] def feedbackfmPhase (phase : UInt32) (modPhase : UInt32) (inc : UInt32)
    (modInc : UInt32) (previous : Int16) (index : Int32) (attenuation : Int32) (sync : UInt8) : UInt32 :=
  (Digital.feedbackFm phase modPhase inc modInc previous index attenuation sync).phase

/-- feedback_fm: the modulator phase after the sample. -/
@[export fm1_feedback_fm_mod] def feedbackfmMod (phase : UInt32) (modPhase : UInt32) (inc : UInt32)
    (modInc : UInt32) (previous : Int16) (index : Int32) (attenuation : Int32) (sync : UInt8) : UInt32 :=
  (Digital.feedbackFm phase modPhase inc modInc previous index attenuation sync).modPhase

/-- feedback_fm: the sample fed back next time. -/
@[export fm1_feedback_fm_previous] def feedbackfmPrevious (phase : UInt32) (modPhase : UInt32)
    (inc : UInt32) (modInc : UInt32) (previous : Int16) (index : Int32) (attenuation : Int32)
    (sync : UInt8) : Int16 :=
  (Digital.feedbackFm phase modPhase inc modInc previous index attenuation sync).previous

/-- feedback_fm: the sample. -/
@[export fm1_feedback_fm_out] def feedbackfmOut (phase : UInt32) (modPhase : UInt32) (inc : UInt32)
    (modInc : UInt32) (previous : Int16) (index : Int32) (attenuation : Int32) (sync : UInt8) : Int16 :=
  (Digital.feedbackFm phase modPhase inc modInc previous index attenuation sync).out

/-- chaotic_fm: the carrier phase after the sample. -/
@[export fm1_chaotic_fm_phase] def chaoticfmPhase (phase : UInt32) (modPhase : UInt32) (inc : UInt32)
    (modInc : UInt32) (index : Int32) (sync : UInt8) : UInt32 :=
  (Digital.chaoticFm phase modPhase inc modInc index sync).phase

/-- chaotic_fm: the modulator phase after the sample. -/
@[export fm1_chaotic_fm_mod] def chaoticfmMod (phase : UInt32) (modPhase : UInt32) (inc : UInt32)
    (modInc : UInt32) (index : Int32) (sync : UInt8) : UInt32 :=
  (Digital.chaoticFm phase modPhase inc modInc index sync).modPhase

/-- chaotic_fm: the sample fed back next time. -/
@[export fm1_chaotic_fm_previous] def chaoticfmPrevious (phase : UInt32) (modPhase : UInt32)
    (inc : UInt32) (modInc : UInt32) (index : Int32) (sync : UInt8) : Int16 :=
  (Digital.chaoticFm phase modPhase inc modInc index sync).previous

/-- chaotic_fm: the sample. -/
@[export fm1_chaotic_fm_out] def chaoticfmOut (phase : UInt32) (modPhase : UInt32) (inc : UInt32)
    (modInc : UInt32) (index : Int32) (sync : UInt8) : Int16 :=
  (Digital.chaoticFm phase modPhase inc modInc index sync).out

/-- ring_mod: the carrier phase after the sample. -/
@[export fm1_ring_mod_phase] def ringmodPhase (phase : UInt32) (mod1 : UInt32) (mod2 : UInt32)
    (inc : UInt32) (inc1 : UInt32) (inc2 : UInt32) (sync : UInt8) : UInt32 :=
  (Digital.ringMod phase mod1 mod2 inc inc1 inc2 sync).phase

/-- ring_mod: the first modulator phase after the sample. -/
@[export fm1_ring_mod_mod1] def ringmodMod1 (phase : UInt32) (mod1 : UInt32) (mod2 : UInt32)
    (inc : UInt32) (inc1 : UInt32) (inc2 : UInt32) (sync : UInt8) : UInt32 :=
  (Digital.ringMod phase mod1 mod2 inc inc1 inc2 sync).mod1

/-- ring_mod: the second modulator phase after the sample. -/
@[export fm1_ring_mod_mod2] def ringmodMod2 (phase : UInt32) (mod1 : UInt32) (mod2 : UInt32)
    (inc : UInt32) (inc1 : UInt32) (inc2 : UInt32) (sync : UInt8) : UInt32 :=
  (Digital.ringMod phase mod1 mod2 inc inc1 inc2 sync).mod2

/-- ring_mod: the sample. -/
@[export fm1_ring_mod_out] def ringmodOut (phase : UInt32) (mod1 : UInt32) (mod2 : UInt32) (inc : UInt32)
    (inc1 : UInt32) (inc2 : UInt32) (sync : UInt8) : Int16 :=
  (Digital.ringMod phase mod1 mod2 inc inc1 inc2 sync).out

/-- toy: the phase after the sample. -/
@[export fm1_toy_phase] def toyPhase (phase : UInt32) (inc : UInt32) (held : UInt8) (counter : UInt16)
    (count : UInt16) (x : UInt8) (sync : UInt8) : UInt32 :=
  (Digital.toy phase inc held counter count x sync).phase

/-- toy: the held value after the sample. -/
@[export fm1_toy_held] def toyHeld (phase : UInt32) (inc : UInt32) (held : UInt8) (counter : UInt16)
    (count : UInt16) (x : UInt8) (sync : UInt8) : UInt8 :=
  (Digital.toy phase inc held counter count x sync).held

/-- toy: the hold counter after the sample. -/
@[export fm1_toy_counter] def toyCounter (phase : UInt32) (inc : UInt32) (held : UInt8) (counter : UInt16)
    (count : UInt16) (x : UInt8) (sync : UInt8) : UInt16 :=
  (Digital.toy phase inc held counter count x sync).counter

/-- toy: the sample. -/
@[export fm1_toy_out] def toyOut (phase : UInt32) (inc : UInt32) (held : UInt8) (counter : UInt16)
    (count : UInt16) (x : UInt8) (sync : UInt8) : Int16 :=
  (Digital.toy phase inc held counter count x sync).out

/-- modulation: the carrier phase after the sample. -/
@[export fm1_modulation_phase] def modulationPhase (phase : UInt32) (inc : UInt32) (symbolPhase : UInt32)
    (symbolInc : UInt32) (count : UInt16) (filter : Int32) (data : UInt8) (parameter : Int32) : UInt32 :=
  (Digital.modulation phase inc symbolPhase symbolInc count filter data parameter).phase

/-- modulation: the symbol clock phase after the sample. -/
@[export fm1_modulation_symbol] def modulationSymbol (phase : UInt32) (inc : UInt32)
    (symbolPhase : UInt32) (symbolInc : UInt32) (count : UInt16) (filter : Int32) (data : UInt8)
    (parameter : Int32) : UInt32 :=
  (Digital.modulation phase inc symbolPhase symbolInc count filter data parameter).symbolPhase

/-- modulation: the symbol count after the sample. -/
@[export fm1_modulation_count] def modulationCount (phase : UInt32) (inc : UInt32) (symbolPhase : UInt32)
    (symbolInc : UInt32) (count : UInt16) (filter : Int32) (data : UInt8) (parameter : Int32) : UInt16 :=
  (Digital.modulation phase inc symbolPhase symbolInc count filter data parameter).count

/-- modulation: the smoothed parameter after the sample. -/
@[export fm1_modulation_filter] def modulationFilter (phase : UInt32) (inc : UInt32)
    (symbolPhase : UInt32) (symbolInc : UInt32) (count : UInt16) (filter : Int32) (data : UInt8)
    (parameter : Int32) : Int32 :=
  (Digital.modulation phase inc symbolPhase symbolInc count filter data parameter).filter

/-- modulation: the data byte after the sample. -/
@[export fm1_modulation_data] def modulationData (phase : UInt32) (inc : UInt32) (symbolPhase : UInt32)
    (symbolInc : UInt32) (count : UInt16) (filter : Int32) (data : UInt8) (parameter : Int32) : UInt8 :=
  (Digital.modulation phase inc symbolPhase symbolInc count filter data parameter).data

/-- modulation: the sample. -/
@[export fm1_modulation_out] def modulationOut (phase : UInt32) (inc : UInt32) (symbolPhase : UInt32)
    (symbolInc : UInt32) (count : UInt16) (filter : Int32) (data : UInt8) (parameter : Int32) : Int16 :=
  (Digital.modulation phase inc symbolPhase symbolInc count filter data parameter).out
