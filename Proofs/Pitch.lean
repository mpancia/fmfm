import Firmware.Pitch
import Proofs.BraidsData

/-!
The pitch to phase step reads a 97-entry table of C data without a bounds check and shifts the result down by
octaves. These theorems say the reads stay inside the table and the step stays below half a cycle per sample.
-/

/-- The clamped pitch, as a signed 32-bit value, is between -32768 and 16383. -/
private theorem pitch_clamped_range (pitch : Int16) :
    -32768 ≤ (if pitch.toInt32 ≥ Pitch.tableStart then Pitch.tableStart - 1 else pitch.toInt32).toInt ∧
      (if pitch.toInt32 ≥ Pitch.tableStart then Pitch.tableStart - 1 else pitch.toInt32).toInt ≤ 16383 := by
  have lo := Int16.le_toInt pitch
  have hi := Int16.toInt_le pitch
  have top : Int16.maxValue.toInt = 32767 := by decide
  unfold Pitch.tableStart
  split
  · decide
  · rename_i above
    simp only [ge_iff_le, Int32.not_le, Int32.lt_iff_toInt_lt, Int16.toInt_toInt32] at above
    rw [Int16.toInt_toInt32]
    simp at above
    omega

/-- A signed value between 1 and 49152 keeps its value as an unsigned one. -/
private theorem pitch_small_toUInt32 (p : Int32) (lo : 1 ≤ p.toInt) (hi : p.toInt ≤ 49152) :
    1 ≤ p.toUInt32.toNat ∧ p.toUInt32.toNat ≤ 49152 := by
  have e : p.toInt = p.toBitVec.toInt := rfl
  have n : p.toUInt32.toNat = p.toBitVec.toNat := rfl
  rw [BitVec.toInt_eq_toNat_cond] at e
  rw [n]
  have := BitVec.isLt p.toBitVec
  split at e <;> omega

/-- A pitch is between 1 and 49152 units below the table's top. -/
private theorem pitch_below_range (pitch : Int16) :
    1 ≤ (Pitch.below pitch).toNat ∧ (Pitch.below pitch).toNat ≤ 49152 := by
  unfold Pitch.below
  have ⟨lo, hi⟩ := pitch_clamped_range pitch
  have start : Pitch.tableStart.toInt = 16384 := by decide
  apply pitch_small_toUInt32
  · rw [Int32.toInt_sub, start, Int.bmod_eq_of_le] <;> omega
  · rw [Int32.toInt_sub, start, Int.bmod_eq_of_le] <;> omega

/-- The octave count is between 1 and 32, and the folded pitch is below 1536. -/
private theorem pitch_shifts_and_folded (pitch : Int16) :
    1 ≤ (Pitch.octaveShifts pitch).toNat ∧ (Pitch.octaveShifts pitch).toNat ≤ 32 ∧
      (Pitch.folded pitch).toNat < 1536 := by
  have ⟨lo, hi⟩ := pitch_below_range pitch
  have shifts : (Pitch.octaveShifts pitch).toNat = ((Pitch.below pitch).toNat + 1535) / 1536 := by
    unfold Pitch.octaveShifts Pitch.octave
    rw [UInt32.toNat_div, UInt32.toNat_add]
    simp
    omega
  refine ⟨by omega, by omega, ?_⟩
  unfold Pitch.folded Pitch.octave
  rw [UInt32.toNat_sub, UInt32.toNat_mul, shifts]
  simp
  omega

/-- Adding one to an index that is not at the top of the 32-bit range adds one to its value. -/
private theorem pitch_succ_toNat (x : UInt32) (small : x.toNat < 4294967295) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [UInt32.toNat_add]
  simp
  omega

/-- The table index is below 96. -/
private theorem pitch_index_lt (pitch : Int16) : (Pitch.tableIndex pitch).toNat < 96 := by
  have := (pitch_shifts_and_folded pitch).2.2
  unfold Pitch.tableIndex
  rw [UInt32.toNat_shiftRight]
  have : (UInt32.toNat 4 % 32) = 4 := by decide
  rw [this, Nat.shiftRight_eq_div_pow]
  omega

/-- Every pitch reads two neighbouring entries of the 97-entry phase step table, both inside it.
Why it matters: the table is C data read without a check; the clamp to note 128 and the fold into one
octave keep the read inside for any 16-bit pitch, including the negative ones a detuned FM operator asks
for. -/
theorem pitch_table_reads_inside (pitch : Int16) :
    (Pitch.tableIndex pitch).toNat < 97 ∧ (Pitch.tableIndex pitch + 1).toNat < 97 := by
  have := pitch_index_lt pitch
  rw [pitch_succ_toNat _ (by omega)]
  omega

/-- A `UInt32` below 2^31 keeps its value as an `Int32`. -/
private theorem pitch_small_toInt32 (x : UInt32) (below : x.toNat < 2 ^ 31) :
    x.toInt32.toInt = (x.toNat : Int) := by
  show x.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt]
  · simp
  · simp at below ⊢; omega

/-- An `Int32` shifted right 4 places is its value divided by 16, rounded down. -/
private theorem pitch_shift_four (s : Int32) : (s >>> 4).toInt = s.toInt / 16 := by
  have : (s >>> 4).toInt = s.toInt >>> 4 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (4 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- A signed value between 0 and 2^31 keeps its value as an unsigned one. -/
private theorem pitch_nonneg_toUInt32 (p : Int32) (lo : 0 ≤ p.toInt) :
    (p.toUInt32.toNat : Int) = p.toInt := by
  have e : p.toInt = p.toBitVec.toInt := rfl
  have n : p.toUInt32.toNat = p.toBitVec.toNat := rfl
  rw [BitVec.toInt_eq_toNat_cond] at e
  rw [n]
  have := BitVec.isLt p.toBitVec
  split at e <;> omega

/-- Blending two neighbouring table entries that rise by less than 2^27 gives a value between them. -/
private theorem pitch_blend_le (a b frac : UInt32) (rising : a ≤ b) (close : b.toNat - a.toNat < 2 ^ 27)
    (small : frac.toNat < 16) :
    (a + (((b - a).toInt32 * frac.toInt32) >>> 4).toUInt32).toNat ≤ b.toNat := by
  rw [UInt32.le_iff_toNat_le] at rising
  have aLt := a.toNat_lt
  have bLt := b.toNat_lt
  have d : (b - a).toNat = b.toNat - a.toNat := by rw [UInt32.toNat_sub]; omega
  have product : ((b - a).toInt32 * frac.toInt32).toInt = ((b.toNat - a.toNat) * frac.toNat : Nat) := by
    rw [Int32.toInt_mul, pitch_small_toInt32 _ (by omega), pitch_small_toInt32 _ (by omega), d,
      Int.bmod_eq_of_le]
    · simp
    · have := Nat.mul_le_mul (Nat.le_of_lt_succ close) (Nat.le_of_lt_succ small); omega
    · have := Nat.mul_le_mul (Nat.le_of_lt_succ close) (Nat.le_of_lt_succ small); omega
  have quotient := pitch_shift_four ((b - a).toInt32 * frac.toInt32)
  rw [product] at quotient
  have step : ((((b - a).toInt32 * frac.toInt32) >>> 4).toUInt32.toNat : Int) =
      (((b.toNat - a.toNat) * frac.toNat : Nat) : Int) / 16 := by
    rw [pitch_nonneg_toUInt32 _ (by rw [quotient]; omega), quotient]
  have stepLe : ((((b - a).toInt32 * frac.toInt32) >>> 4).toUInt32.toNat : Int) ≤ b.toNat - a.toNat := by
    rw [step]
    have := Nat.mul_le_mul_left (b.toNat - a.toNat) (Nat.le_of_lt_succ small)
    have := Int.ediv_le_self 16 (Int.natCast_nonneg ((b.toNat - a.toNat) * frac.toNat))
    omega
  rw [UInt32.toNat_add]
  omega

/-- The low four bits of a value are below 16. -/
private theorem pitch_low_bits (x : UInt32) : (x &&& 0xF).toNat < 16 := by
  rw [UInt32.toNat_and]
  exact Nat.and_lt_two_pow _ (by decide : (0xF : UInt32).toNat < 2 ^ 4)

/-- A value no larger than the table's top entry, shifted down at least one octave, is below half a cycle. -/
private theorem pitch_halved (step shifts : Nat) (one : 1 ≤ shifts) (small : step ≤ 2588618730) :
    step / 2 ^ shifts < 2 ^ 31 := by
  have two : 2 ≤ 2 ^ shifts := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by decide) one
  have := Nat.div_le_div_left two (by decide : 0 < 2) (a := step)
  omega

/-- The step is below half a cycle per sample. The table's entries rise from one to the next by less than
2^27 and the top one is 2588618730 (`Proofs/BraidsData.lean`, checked against `resources.cc`).
Why it matters: the table's top entry is above half a cycle, so the bound comes from the clamp, which puts
every pitch at least one octave below the table; a step below half a cycle keeps the oscillators under
Nyquist. -/
theorem pitch_increment_bounded (pitch : Int16) : (Pitch.phaseIncrement pitch).toNat < 2 ^ 31 := by
  have ⟨one, _, _⟩ := pitch_shifts_and_folded pitch
  have inside := pitch_index_lt pitch
  unfold Pitch.phaseIncrement
  dsimp only
  split
  · decide
  · rename_i under
    have thirtyTwo : (32 : UInt32).toNat = 32 := by decide
    rw [UInt32.not_le, UInt32.lt_iff_toNat_lt, thirtyTwo] at under
    have blended := pitch_blend_le _ _ _ (braids_data_increments_rising _ inside)
      (braids_data_increments_close _ inside) (pitch_low_bits (Pitch.folded pitch))
    have := braids_data_increments_top (Pitch.tableIndex pitch + 1)
    unfold Pitch.topOctaveStep
    dsimp only
    rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
    exact pitch_halved _ _ one (by omega)
