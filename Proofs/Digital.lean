import Firmware.Digital

/-- Weighted by `t` out of `N` (`0 ≤ t ≤ N`), two values between `lo` and `hi` combine to something between
`lo * N` and `hi * N`. -/
private theorem digital_convex (a b lo hi t N : Int) (ht : 0 ≤ t ∧ t ≤ N) (ha : lo ≤ a ∧ a ≤ hi)
    (hb : lo ≤ b ∧ b ≤ hi) :
    lo * N ≤ a * (N - t) + b * t ∧ a * (N - t) + b * t ≤ hi * N := by
  have w : 0 ≤ N - t := by omega
  have a1 := Int.mul_le_mul_of_nonneg_right ha.2 w
  have a2 := Int.mul_le_mul_of_nonneg_right ha.1 w
  have b1 := Int.mul_le_mul_of_nonneg_right hb.2 ht.1
  have b2 := Int.mul_le_mul_of_nonneg_right hb.1 ht.1
  have e1 : hi * (N - t) = hi * N - hi * t := Int.mul_sub hi N t
  have e2 : lo * (N - t) = lo * N - lo * t := Int.mul_sub lo N t
  omega

/-- An `Int32` shifted right 16 places is its value divided by 65536, rounded down. -/
private theorem digital_shift_sixteen (s : Int32) : (s >>> 16).toInt = s.toInt / 65536 := by
  have : (s >>> 16).toInt = s.toInt >>> 16 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (16 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- A `UInt32` below 2^31 keeps its value as an `Int32`. -/
private theorem digital_small_toInt32 (x : UInt32) (below : x.toNat < 2 ^ 31) :
    x.toInt32.toInt = (x.toNat : Int) := by
  show x.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt]
  · simp
  · simp at below ⊢; omega

/-- A crossfade of two 16-bit values never leaves the range between them (give or take one rounding step
toward zero), for any balance up to 65535.
Why it matters: every macro shape mixes its oscillators with this, as do the wavetable engines; a crossfade
can never be louder than its louder input, so it cannot wrap. -/
theorem digital_mix_between_inputs (a b : Int32) (balance : UInt32) (hbal : balance.toNat ≤ 65535)
    (ha : -32768 ≤ a.toInt ∧ a.toInt ≤ 32767) (hb : -32768 ≤ b.toInt ∧ b.toInt ≤ 32767) :
    min a.toInt b.toInt - 1 ≤ (Digital.mix a b balance).toInt ∧
      (Digital.mix a b balance).toInt ≤ max a.toInt b.toInt := by
  unfold Digital.mix
  have t : balance.toInt32.toInt = (balance.toNat : Int) := digital_small_toInt32 balance (by omega)
  have u : (65535 - balance).toInt32.toInt = 65535 - (balance.toNat : Int) := by
    rw [digital_small_toInt32 _ (by rw [UInt32.toNat_sub]; simp; omega), UInt32.toNat_sub]
    simp
    omega
  have c := digital_convex a.toInt b.toInt (min a.toInt b.toInt) (max a.toInt b.toInt) balance.toNat 65535
    (by omega) (by omega) (by omega)
  have pa : (a * (65535 - balance).toInt32).toInt = a.toInt * (65535 - (balance.toNat : Int)) := by
    rw [Int32.toInt_mul, u]
    have := Int.mul_le_mul_of_nonneg_right ha.2 (by omega : (0 : Int) ≤ 65535 - balance.toNat)
    have := Int.mul_le_mul_of_nonneg_right ha.1 (by omega : (0 : Int) ≤ 65535 - balance.toNat)
    have e1 : (32767 : Int) * (65535 - balance.toNat) = 32767 * 65535 - 32767 * balance.toNat :=
      Int.mul_sub _ _ _
    have e2 : (-32768 : Int) * (65535 - balance.toNat) = -32768 * 65535 - -32768 * balance.toNat :=
      Int.mul_sub _ _ _
    simp [Int.bmod_def]
    split <;> omega
  have pb : (b * balance.toInt32).toInt = b.toInt * (balance.toNat : Int) := by
    rw [Int32.toInt_mul, t]
    have := Int.mul_le_mul_of_nonneg_right hb.2 (by omega : (0 : Int) ≤ balance.toNat)
    have := Int.mul_le_mul_of_nonneg_right hb.1 (by omega : (0 : Int) ≤ balance.toNat)
    simp [Int.bmod_def]
    split <;> omega
  have sum : (a * (65535 - balance).toInt32 + b * balance.toInt32).toInt =
      a.toInt * (65535 - (balance.toNat : Int)) + b.toInt * (balance.toNat : Int) := by
    rw [Int32.toInt_add, pa, pb]
    simp [Int.bmod_def]
    split <;> omega
  rw [Int16.toInt_toInt32, Int32.toInt_toInt16, digital_shift_sixteen, sum]
  generalize a.toInt * (65535 - (balance.toNat : Int)) + b.toInt * (balance.toNat : Int) = s at *
  simp [Int.bmod_def]
  split <;> omega
