import Firmware.VowelsSetup

/-!
The per-block setup of the vowels reads phoneme and formant data by indexes it computes from the parameters,
and hands the vowel engine amplitudes that index the formant tables. These theorems say every such index stays
inside its data, and the amplitudes stay within the nibble `tables_formant_reads_inside_256` needs.
-/

/-- An `Int32` shifted right 12 places is its value divided by 4096, rounded down. -/
private theorem vowels_setup_shift_twelve (s : Int32) : (s >>> 12).toInt = s.toInt / 4096 := by
  have : (s >>> 12).toInt = s.toInt >>> 12 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (12 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- An `Int32` shifted right 13 places is its value divided by 8192, rounded down. -/
private theorem vowels_setup_shift_thirteen (s : Int32) : (s >>> 13).toInt = s.toInt / 8192 := by
  have : (s >>> 13).toInt = s.toInt >>> 13 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (13 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- A signed value between 0 and 32767 keeps its value as an unsigned one. -/
private theorem vowels_setup_small_toUInt32 (p : Int32) (lo : 0 ≤ p.toInt) (hi : p.toInt ≤ 32767) :
    p.toUInt32.toNat = p.toInt.toNat := by
  have e : p.toInt = p.toBitVec.toInt := rfl
  have n : p.toUInt32.toNat = p.toBitVec.toNat := rfl
  rw [BitVec.toInt_eq_toNat_cond] at e
  rw [n]
  have := BitVec.isLt p.toBitVec
  split at e <;> omega

/-- Adding one to an index that is not at the top of the 32-bit range adds one to its value. -/
private theorem vowels_setup_succ_toNat (x : UInt32) (small : x.toNat < 4294967295) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [UInt32.toNat_add]
  simp
  omega

/-- A parameter of 0 to 32767 selects a vowel from 0 to 7, and the vowel after it is at most 8, so both reads
are inside the nine entries of `vowels_data`.
Why it matters: the vowel blends two neighbouring rows of its data without a bounds check; the top three bits
of the parameter can never name the last row, so the row after is always there to blend with. -/
theorem vowels_setup_vowel_index_in_table (parameter : Int32)
    (shaped : 0 ≤ parameter.toInt ∧ parameter.toInt ≤ 32767) :
    (VowelsSetup.vowelIndex parameter).toNat ≤ 7 ∧ (VowelsSetup.vowelIndex parameter + 1).toNat ≤ 8 := by
  unfold VowelsSetup.vowelIndex
  have s := vowels_setup_shift_twelve parameter
  have e := vowels_setup_small_toUInt32 (parameter >>> 12) (by omega) (by omega)
  rw [vowels_setup_succ_toNat _ (by omega), e]
  omega

/-- A strike's random sample selects a consonant from 0 to 7, inside the eight entries of `consonant_data`.
Why it matters: the consonant is read without a bounds check from whatever the random generator gives; the
mask to three bits is what keeps it inside. -/
theorem vowels_setup_consonant_index_in_table (random : Int32) :
    (VowelsSetup.consonantIndex random).toNat ≤ 7 := by
  unfold VowelsSetup.consonantIndex
  show ((random + 1).toBitVec &&& (7 : Int32).toBitVec).toNat ≤ 7
  rw [BitVec.toNat_and]
  have := Nat.and_le_right (n := (random + 1).toBitVec.toNat) (m := (7 : Int32).toBitVec.toNat)
  have seven : (7 : Int32).toBitVec.toNat = 7 := by decide
  omega

/-- A parameter of 0 to 32767 selects a row of the FOF vowel's 5-by-5 grid from 0 to 3, and the row after it
is at most 4, so the four corners the blend reads are inside the grid.
Why it matters: `fofBlend` reads the corner past the selected row and column; the top two bits of a parameter
can never select the last row, so that corner exists. -/
theorem vowels_setup_fof_reads_in_table (parameter : Int32)
    (shaped : 0 ≤ parameter.toInt ∧ parameter.toInt ≤ 32767) :
    (VowelsSetup.fofRow parameter).toNat ≤ 3 ∧ (VowelsSetup.fofRow parameter + 1).toNat ≤ 4 := by
  unfold VowelsSetup.fofRow
  have s := vowels_setup_shift_thirteen parameter
  have e := vowels_setup_small_toUInt32 (parameter >>> 13) (by omega) (by omega)
  rw [vowels_setup_succ_toNat _ (by omega), e]
  omega

/-- The low twelve bits of a value are below 4096. -/
private theorem vowels_setup_balance_le (parameter : Int32) :
    (VowelsSetup.vowelBalance parameter).toNat ≤ 4095 := by
  unfold VowelsSetup.vowelBalance
  show ((parameter.toBitVec &&& (0xFFF : Int32).toBitVec)).toNat ≤ 4095
  rw [BitVec.toNat_and]
  have := Nat.and_le_right (n := parameter.toBitVec.toNat) (m := (0xFFF : Int32).toBitVec.toNat)
  have mask : (0xFFF : Int32).toBitVec.toNat = 4095 := by decide
  omega

/-- Two nibbles weighted by a balance of at most 4095 and its complement to 4096 sum to at most 61440. -/
private theorem vowels_setup_weighted_le (a b balance : Nat) (ha : a ≤ 15) (hb : b ≤ 15)
    (hbal : balance ≤ 4095) : a * (4096 - balance) + b * balance ≤ 61440 := by
  have := Nat.mul_le_mul_right (4096 - balance) ha
  have := Nat.mul_le_mul_right balance hb
  omega

/-- The amplitude the vowel hands each formant is at most 15, given that every amplitude in `vowels_data` is
at most 15 (a fact about the data, so a hypothesis here).
Why it matters: the formant tables are indexed by the phase's top nibble or-ed with the amplitude, and
`tables_formant_reads_inside_256` needs the amplitude to be a nibble; this closes that hypothesis for every
parameter and formant. -/
theorem vowels_setup_formant_amplitude_in_range (parameter : Int32) (formant : UInt32)
    (nibble : ∀ vowel formant, (VowelsSetup.vowelAmplitudeAt vowel formant).toNat ≤ 15) :
    (VowelsSetup.vowelAmplitude parameter formant).toNat ≤ 15 := by
  unfold VowelsSetup.vowelAmplitude
  dsimp only
  have bal := vowels_setup_balance_le parameter
  have ha := nibble (VowelsSetup.vowelIndex parameter) formant
  have hb := nibble (VowelsSetup.vowelIndex parameter + 1) formant
  generalize VowelsSetup.vowelBalance parameter = balance at *
  generalize VowelsSetup.vowelAmplitudeAt (VowelsSetup.vowelIndex parameter) formant = a at *
  generalize VowelsSetup.vowelAmplitudeAt (VowelsSetup.vowelIndex parameter + 1) formant = b at *
  have sub : ((0x1000 : UInt32) - balance).toNat = 4096 - balance.toNat := by
    rw [UInt32.toNat_sub_of_le]
    · rfl
    · rw [UInt32.le_iff_toNat_le]; show balance.toNat ≤ 4096; omega
  have weighted := vowels_setup_weighted_le a.toNat b.toNat balance.toNat ha hb bal
  rw [UInt32.toNat_shiftRight, UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_mul, UInt8.toNat_toUInt32,
    UInt8.toNat_toUInt32, sub, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  have twelve : (UInt32.toNat 12 % 32) = 12 := by decide
  rw [twelve, Nat.shiftRight_eq_div_pow]
  omega

/-- An `Int32` cut to 16 bits and widened again is between -32768 and 32767. -/
private theorem vowels_setup_cut16_range (x : Int32) :
    -32768 ≤ x.toInt16.toInt32.toInt ∧ x.toInt16.toInt32.toInt ≤ 32767 := by
  rw [Int16.toInt_toInt32, Int32.toInt_toInt16]
  have lo := Int.le_bmod (x := x.toInt) (m := 2 ^ 16) (by decide)
  have hi := Int.bmod_lt (x := x.toInt) (m := 2 ^ 16) (by decide)
  omega

/-- The amplitude the FOF vowel hands its formant filters is a signed 16-bit value, for any parameters.
Why it matters: `vowels_fof_contribution_never_wraps` takes a 16-bit amplitude; the blend's final cut to 16
bits (the original's `int16_t` return) is what makes that so, so the hypothesis is met for every block. -/
theorem vowels_setup_fof_amplitude_16bit (parameter0 parameter1 : Int32) (formant : UInt32) :
    -32768 ≤ (VowelsSetup.fofAmplitude parameter0 parameter1 formant).toInt ∧
      (VowelsSetup.fofAmplitude parameter0 parameter1 formant).toInt ≤ 32767 := by
  unfold VowelsSetup.fofAmplitude VowelsSetup.fofBlend
  exact vowels_setup_cut16_range _
