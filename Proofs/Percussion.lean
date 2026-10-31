import Firmware.Percussion

/-- A signed value between 0 and 2^19 keeps its value as an unsigned one. -/
private theorem percussion_small_toUInt32 (p : Int32) (lo : 0 ≤ p.toInt) (hi : p.toInt ≤ 524288) :
    p.toUInt32.toNat = p.toInt := by
  have e : p.toInt = p.toBitVec.toInt := rfl
  have n : p.toUInt32.toNat = p.toBitVec.toNat := rfl
  rw [BitVec.toInt_eq_toNat_cond] at e
  rw [n]
  have := BitVec.isLt p.toBitVec
  split at e <;> omega

/-- A `UInt32` below 2^31 keeps its value when read as an `Int32`. -/
private theorem percussion_uint32_toInt32_toInt (x : UInt32) (below : x.toNat < 2 ^ 31) :
    x.toInt32.toInt = (x.toNat : Int) := by
  show x.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt]
  · simp
  · simp at below ⊢; omega

/-- Between hits, an exciter's pulse only decays: it stays at or below where it was, and never below zero.
The pulse is at most 2^19 (the loudest strike is 15 times 32768) and the decay at most 4096 (one, in 12 bits).
Why it matters: a drum hit dies away; the exciter cannot grow on its own or swing negative. -/
theorem percussion_excite_decays (state decay counter level : Int32)
    (nonneg : 0 ≤ state.toInt) (small : state.toInt ≤ 524288) (gentle : 0 ≤ decay.toInt ∧ decay.toInt ≤ 4096)
    (quiet : counter.toInt ≠ 1) :
    0 ≤ (Percussion.excite state decay counter level).state.toInt ∧
      (Percussion.excite state decay counter level).state.toInt ≤ state.toInt := by
  unfold Percussion.excite
  dsimp only
  have notFired : (counter > 0 && (if counter > 0 then counter - 1 else counter) == 0) = false := by
    by_cases h : counter > 0
    · simp only [h, decide_true, Bool.true_and, ite_true]
      rw [beq_eq_false_iff_ne]
      intro bad
      apply quiet
      have := congrArg Int32.toInt bad
      rw [Int32.toInt_sub] at this
      simp [Int.bmod_def] at this
      have r := Int32.toInt_lt counter
      have l := Int32.le_iff_toInt_le.mp (Int32.minValue_le counter)
      rw [Int32.toInt_minValue] at l
      split at this <;> omega
    · simp [h]
  rw [notFired]
  simp only [Bool.false_eq_true, ite_false]
  have sv := percussion_small_toUInt32 state nonneg small
  have dv := percussion_small_toUInt32 decay gentle.1 (by omega)
  have product : (state.toUInt32 * decay.toUInt32).toNat = state.toUInt32.toNat * decay.toUInt32.toNat := by
    rw [UInt32.toNat_mul, Nat.mod_eq_of_lt]
    have a : state.toUInt32.toNat ≤ 524288 := by omega
    have b : decay.toUInt32.toNat ≤ 4096 := by omega
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul a b) (by decide)
  have shifted : ((state.toUInt32 * decay.toUInt32) >>> 12).toNat =
      state.toUInt32.toNat * decay.toUInt32.toNat / 4096 := by
    rw [UInt32.toNat_shiftRight, product]
    have : (UInt32.toNat 12 % 32) = 12 := by decide
    rw [this, Nat.shiftRight_eq_div_pow]
  have le : state.toUInt32.toNat * decay.toUInt32.toNat / 4096 ≤ state.toUInt32.toNat := by
    have b : decay.toUInt32.toNat ≤ 4096 := by omega
    have := Nat.mul_le_mul_left state.toUInt32.toNat b
    omega
  rw [percussion_uint32_toInt32_toInt _ (by omega), shifted]
  omega
