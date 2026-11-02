import Firmware.Random

/-- `Random.below` returns a value below `limit` (for `0 < limit ≤ 65535`).
Why it matters: a pick is always a valid index into a list of `limit` choices. -/
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

/-- No state maps to itself under `Random.next`: `next x = x` would need `(a - 1) * x ≡ -c` mod 2^32, but
`a - 1` is a multiple of 4 and `c` is odd.
Why it matters: the generator can never get stuck on one value, whatever the seed. -/
theorem random_never_stands_still (state : UInt32) : Random.next state ≠ state := by
  intro same
  unfold Random.next at same
  have h := congrArg UInt32.toNat same
  rw [UInt32.toNat_add, UInt32.toNat_mul] at h
  simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
  have lt := UInt32.toNat_lt state
  omega
