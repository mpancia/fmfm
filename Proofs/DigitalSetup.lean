import Firmware.DigitalSetup
import Proofs.Pitch

/-!
The per-block setup of the digital oscillator reads two tables of C data without a bounds check and hands
phase steps to the sample code. These theorems say the reads stay inside their tables and the steps stay
below half a cycle per sample.
-/

/-- An `Int32` shifted right 8 places is its value divided by 256, rounded down. -/
private theorem digital_setup_shift_eight (s : Int32) : (s >>> 8).toInt = s.toInt / 256 := by
  have : (s >>> 8).toInt = s.toInt >>> 8 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (8 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- A signed value that is not negative keeps its value as an unsigned one. -/
private theorem digital_setup_nonneg_toUInt32 (p : Int32) (lo : 0 ≤ p.toInt) :
    (p.toUInt32.toNat : Int) = p.toInt := by
  have e : p.toInt = p.toBitVec.toInt := rfl
  have n : p.toUInt32.toNat = p.toBitVec.toNat := rfl
  rw [BitVec.toInt_eq_toNat_cond] at e
  rw [n]
  have := BitVec.isLt p.toBitVec
  split at e <;> omega

/-- The quantizer index of a parameter that is not negative is at most 127. -/
private theorem digital_setup_quantizer_index_le (param : Int16) (nonneg : 0 ≤ param) :
    (DigitalSetup.fmQuantizerIndex param).toNat ≤ 127 := by
  unfold DigitalSetup.fmQuantizerIndex
  have lo : 0 ≤ param.toInt := by
    rw [Int16.le_iff_toInt_le] at nonneg
    simpa using nonneg
  have hi := Int16.toInt_le param
  have top : Int16.maxValue.toInt = 32767 := by decide
  have shifted := digital_setup_shift_eight param.toInt32
  rw [Int16.toInt_toInt32] at shifted
  have kept := digital_setup_nonneg_toUInt32 (param.toInt32 >>> 8) (by rw [shifted]; omega)
  rw [UInt32.toNat_and]
  have := Nat.and_le_left (n := (param.toInt32 >>> 8).toUInt32.toNat) (m := (0xFFFF : UInt32).toNat)
  omega

/-- Adding one to an index that is not at the top of the 32-bit range adds one to its value. -/
private theorem digital_setup_succ_toNat (x : UInt32) (small : x.toNat < 4294967295) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [UInt32.toNat_add]
  simp
  omega

/-- A parameter that is not negative reads two neighbouring entries of the 129-entry FM ratio quantizer,
both inside it. Braids' parameters are 0 to 32767, so `nonneg` holds for every block; a negative one would
read 65535 entries past the table, which is why the limit is stated.
Why it matters: the quantizer is C data read without a check, once per block for the three FM engines. -/
theorem digital_setup_fm_quantizer_in_table (param : Int16) (nonneg : 0 ≤ param) :
    (DigitalSetup.fmQuantizerIndex param).toNat < 129 ∧
      (DigitalSetup.fmQuantizerIndex param + 1).toNat < 129 := by
  have := digital_setup_quantizer_index_le param nonneg
  rw [digital_setup_succ_toNat _ (by omega)]
  omega

/-- Every phase step the setup hands to the FM, ring modulator, toy and digital modulation sample code is
below half a cycle per sample. The detuned pitches are cut to 16 bits before the lookup, so no offset can
escape the clamp.
Why it matters: the sample code's steps come from here, and a step at or above half a cycle would alias;
the modulators' detunes can reach pitches far outside the carrier's range, and this says the clamp still
holds them. -/
theorem digital_setup_increments_half_cycle (pitch param : Int16) (increment : UInt32) :
    (DigitalSetup.fmModulatorIncrement pitch param).toNat < 2 ^ 31 ∧
      (DigitalSetup.ringIncrement pitch param).toNat < 2 ^ 31 ∧
      (DigitalSetup.modulationSymbolIncrement pitch param).toNat < 2 ^ 31 ∧
      (DigitalSetup.toyIncrement increment).toNat < 2 ^ 31 := by
  have modulator := pitch_increment_bounded (DigitalSetup.fmModulatorPitch pitch param)
  have ring := pitch_increment_bounded (DigitalSetup.ringPitch pitch param)
  have symbol := pitch_increment_bounded (DigitalSetup.modulationSymbolPitch pitch param)
  have quarter := increment.toNat_lt
  unfold DigitalSetup.fmModulatorIncrement DigitalSetup.ringIncrement DigitalSetup.modulationSymbolIncrement
    DigitalSetup.toyIncrement
  rw [UInt32.toNat_shiftRight, UInt32.toNat_shiftRight]
  simp only [UInt32.reduceToNat, Nat.shiftRight_eq_div_pow, Nat.reduceMod]
  omega

/-- The clamped pitch, as a signed 32-bit value, is between -32768 and 16384. -/
private theorem digital_setup_clamped_range (pitch : Int16) :
    -32768 ≤ (if pitch.toInt32 ≥ 16384 then 16384 else pitch.toInt32).toInt ∧
      (if pitch.toInt32 ≥ 16384 then 16384 else pitch.toInt32).toInt ≤ 16384 := by
  have lo := Int16.le_toInt pitch
  have hi := Int16.toInt_le pitch
  have top : Int16.maxValue.toInt = 32767 := by decide
  split
  · decide
  · rename_i above
    simp only [ge_iff_le, Int32.not_le, Int32.lt_iff_toInt_lt, Int16.toInt_toInt32] at above
    rw [Int16.toInt_toInt32]
    simp at above
    omega

/-- A signed value between 0 and 49152 keeps its value as an unsigned one. -/
private theorem digital_setup_small_toUInt32 (p : Int32) (lo : 0 ≤ p.toInt) (hi : p.toInt ≤ 49152) :
    p.toUInt32.toNat ≤ 49152 := by
  have := digital_setup_nonneg_toUInt32 p lo
  omega

/-- A pitch is at most 49152 units below the delay table's top. -/
private theorem digital_setup_below_range (pitch : Int16) :
    (DigitalSetup.delayBelow pitch).toNat ≤ 49152 := by
  unfold DigitalSetup.delayBelow
  have ⟨lo, hi⟩ := digital_setup_clamped_range pitch
  have top : (16384 : Int32).toInt = 16384 := by decide
  apply digital_setup_small_toUInt32
  · rw [Int32.toInt_sub, top, Int.bmod_eq_of_le] <;> omega
  · rw [Int32.toInt_sub, top, Int.bmod_eq_of_le] <;> omega

/-- The folded pitch is below 1536. -/
private theorem digital_setup_folded_lt (pitch : Int16) : (DigitalSetup.delayFolded pitch).toNat < 1536 := by
  have hi := digital_setup_below_range pitch
  have shifts : (DigitalSetup.delayShifts pitch).toNat =
      ((DigitalSetup.delayBelow pitch).toNat + 1535) / 1536 := by
    unfold DigitalSetup.delayShifts
    rw [UInt32.toNat_div, UInt32.toNat_add]
    simp
    omega
  unfold DigitalSetup.delayFolded
  rw [UInt32.toNat_sub, UInt32.toNat_mul, shifts]
  simp
  omega

/-- Every pitch reads two neighbouring entries of the 97-entry delay table, both inside it.
Why it matters: the table is C data read without a check; the clamp to note 128 and the fold into one octave
are what keep the read inside it for any 16-bit pitch, including the lowest a filtered comb pitch reaches. -/
theorem digital_setup_delay_in_table (pitch : Int16) :
    (DigitalSetup.delayIndex pitch).toNat < 97 ∧ (DigitalSetup.delayIndex pitch + 1).toNat < 97 := by
  have folded := digital_setup_folded_lt pitch
  have index : (DigitalSetup.delayIndex pitch).toNat < 96 := by
    unfold DigitalSetup.delayIndex
    rw [UInt32.toNat_shiftRight]
    have : (UInt32.toNat 4 % 32) = 4 := by decide
    rw [this, Nat.shiftRight_eq_div_pow]
    omega
  rw [digital_setup_succ_toNat _ (by omega)]
  omega
