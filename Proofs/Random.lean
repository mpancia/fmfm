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

/-- The generator never stands still: no state maps to itself, so a random lane can never freeze on one value.
`next x = x` would need `(a - 1) * x ≡ -c` modulo 2^32; `a - 1` is a multiple of 4 and `c` is odd, so the two
sides have different parity. (Hull and Dobell's conditions for the full period include these two facts.)
Why it matters: whatever the seed, the next draw is a different state, so random, walk and the play chance
keep moving; a stuck generator would play one note forever. -/
theorem random_never_stands_still (state : UInt32) : Random.next state ≠ state := by
  intro same
  unfold Random.next at same
  have h := congrArg UInt32.toNat same
  rw [UInt32.toNat_add, UInt32.toNat_mul] at h
  simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
  have lt := UInt32.toNat_lt state
  omega
