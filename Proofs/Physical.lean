import Firmware.Physical

/-- An `Int32` shifted right one place is its value halved, rounded down. -/
private theorem physical_shift_one (s : Int32) : (s >>> 1).toInt = s.toInt / 2 := by
  have : (s >>> 1).toInt = s.toInt >>> 1 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (1 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- An `Int32` shifted right 15 places is its value divided by 32768, rounded down. -/
private theorem physical_shift_fifteen (s : Int32) : (s >>> 15).toInt = s.toInt / 32768 := by
  have : (s >>> 15).toInt = s.toInt >>> 15 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (15 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- Scaling by a factor between 0 and 1 (in 15 bits) never grows a value or flips its sign. -/
private theorem physical_scale_down (half k : Int) (lo : 0 ≤ k) (hi : k ≤ 32768) :
    (half * k / 32768 ≤ half ∧ 0 ≤ half * k / 32768) ∨ (half ≤ half * k / 32768 ∧ half * k / 32768 ≤ 0) := by
  by_cases h : 0 ≤ half
  · left
    have a : half * k ≤ half * 32768 := Int.mul_le_mul_of_nonneg_left hi h
    have b : 0 ≤ half * k := Int.mul_nonneg h lo
    constructor
    · have := Int.ediv_le_ediv (by decide : (0 : Int) < 32768) a
      rw [Int.mul_ediv_cancel _ (by decide)] at this
      exact this
    · exact Int.ediv_nonneg b (by decide)
  · right
    have neg : half ≤ 0 := by omega
    have a : half * 32768 ≤ half * k := Int.mul_le_mul_of_nonpos_left neg hi
    have b : half * k ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg neg lo
    constructor
    · have := Int.ediv_le_ediv (by decide : (0 : Int) < 32768) a
      rw [Int.mul_ediv_cancel _ (by decide)] at this
      exact this
    · exact Int.ediv_nonpos_of_nonpos_of_neg b (by decide)

/-- One step of the plucked string's loop never makes the signal louder: the result is within the louder of
the two neighbours it averages, for 16-bit neighbours and a loss between 0 and 32768.
Why it matters: the Karplus-Strong loop feeds its output back into itself; a step that could gain would make
the string grow instead of ring down. -/
theorem physical_pluck_average_no_gain (a b loss : Int32)
    (ha : -32767 ≤ a.toInt ∧ a.toInt ≤ 32767) (hb : -32767 ≤ b.toInt ∧ b.toInt ≤ 32767)
    (hl : 0 ≤ loss.toInt ∧ loss.toInt ≤ 32768) :
    -(max a.toInt.natAbs b.toInt.natAbs : Int) ≤ (Physical.pluckAverage a b loss).toInt ∧
      (Physical.pluckAverage a b loss).toInt ≤ max a.toInt.natAbs b.toInt.natAbs := by
  unfold Physical.pluckAverage
  dsimp only
  have sum : (a + b).toInt = a.toInt + b.toInt := by
    rw [Int32.toInt_add]; simp [Int.bmod_def]; split <;> omega
  generalize hhalf : (if a + b < 0 then -((-(a + b)) >>> 1) else (a + b) >>> 1) = half
  have halfRange : -(max a.toInt.natAbs b.toInt.natAbs : Int) ≤ half.toInt ∧
      half.toInt ≤ max a.toInt.natAbs b.toInt.natAbs := by
    subst hhalf
    split
    · rename_i neg
      rw [Int32.lt_iff_toInt_lt, sum] at neg
      have n : (-(a + b)).toInt = -(a.toInt + b.toInt) := by
        rw [Int32.toInt_neg, sum]; simp [Int.bmod_def]; split <;> omega
      rw [Int32.toInt_neg, physical_shift_one, n]
      simp [Int.bmod_def]
      split <;> omega
    · rw [physical_shift_one, sum]
      omega
  have k : (32768 - loss).toInt = 32768 - loss.toInt := by
    rw [Int32.toInt_sub]; simp [Int.bmod_def]; split <;> omega
  have hr : -32768 ≤ half.toInt ∧ half.toInt ≤ 32767 := by omega
  have productSmall : -1073741824 ≤ half.toInt * (32768 - loss.toInt) ∧
      half.toInt * (32768 - loss.toInt) ≤ 1073741824 := by
    have k0 : 0 ≤ 32768 - loss.toInt := by omega
    have k1 : 32768 - loss.toInt ≤ 32768 := by omega
    constructor
    · have := Int.mul_le_mul_of_nonneg_right (hr.1) k0
      have := Int.mul_le_mul_of_nonpos_left (by decide : (-32768 : Int) ≤ 0) k1
      omega
    · have := Int.mul_le_mul_of_nonneg_right (hr.2) k0
      have := Int.mul_le_mul_of_nonneg_left k1 (by decide : (0 : Int) ≤ 32767)
      omega
  have product : (half * (32768 - loss)).toInt = half.toInt * (32768 - loss.toInt) := by
    rw [Int32.toInt_mul, k]
    simp [Int.bmod_def]
    split <;> omega
  have scaled := physical_scale_down half.toInt (32768 - loss.toInt) (by omega) (by omega)
  split
  · rw [Int32.toInt_toInt16, physical_shift_fifteen, product]
    simp [Int.bmod_def]
    split <;> omega
  · rw [Int32.toInt_toInt16]
    simp [Int.bmod_def]
    split <;> omega
