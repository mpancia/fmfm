import Firmware.Random

/-- A random pick is always below its limit, so it is a valid index into a list of `limit` choices.
Why it matters: a pick one too big would read past the end of a note list or a step table. -/
theorem random_below_lt (state limit : UInt32) (positive : 0 < limit.toNat) (small : limit.toNat ≤ 65535) :
    (Random.below state limit).toNat < limit.toNat := by
  have high : (state >>> 16).toNat < 65536 := by
    have := state.toNat_lt
    simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    omega
  unfold Random.below
  generalize state >>> 16 = h at high ⊢
  have product : h.toNat * limit.toNat < 4294967296 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right high positive) (by omega)
  have under : h.toNat * limit.toNat < 65536 * limit.toNat := Nat.mul_lt_mul_of_pos_right high positive
  rw [UInt32.toNat_shiftRight, UInt32.toNat_mul, Nat.mod_eq_of_lt product]
  simp only [Nat.shiftRight_eq_div_pow]
  have : UInt32.toNat 16 % 32 = 16 := by decide
  rw [this]
  omega
