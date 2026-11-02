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

/-- A 16-bit value times a weight up to 65535 fits a signed 32-bit number. -/
private theorem digital_scaled_fits (x w : Int) (hx : -32768 ≤ x ∧ x ≤ 32767) (hw : 0 ≤ w ∧ w ≤ 65535) :
    Int.bmod (x * w) (2 ^ 32) = x * w := by
  have hi := Int.mul_le_mul_of_nonneg_right hx.2 hw.1
  have lo := Int.mul_le_mul_of_nonneg_right hx.1 hw.1
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A weighted sum between `lo * 65535` and `hi * 65535` for 16-bit `lo` and `hi` fits 32 bits; shifted down
16 places it fits 16 bits and lands between `lo - 1` and `hi`. -/
private theorem digital_weighted_between (s lo hi : Int) (hc : lo * 65535 ≤ s ∧ s ≤ hi * 65535)
    (hlo : -32768 ≤ lo) (hhi : hi ≤ 32767) :
    Int.bmod s (2 ^ 32) = s ∧ Int.bmod (s / 65536) (2 ^ 16) = s / 65536 ∧
      lo - 1 ≤ s / 65536 ∧ s / 65536 ≤ hi := by
  refine ⟨Int.bmod_eq_of_le (by omega) (by omega), Int.bmod_eq_of_le (by omega) (by omega), by omega, by omega⟩

/-- A crossfade of two 16-bit values stays between them (give or take one rounding step toward zero), for
any balance up to 65535.
Why it matters: the macro shapes and the wavetable engines mix with this; it cannot exceed its louder input,
so it cannot wrap. -/
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
  have pa := digital_scaled_fits a.toInt (65535 - (balance.toNat : Int)) ha (by omega)
  have pb := digital_scaled_fits b.toInt (balance.toNat : Int) hb (by omega)
  obtain ⟨sum, fits, lo, hi⟩ := digital_weighted_between _ _ _ c (by omega) (by omega)
  rw [Int16.toInt_toInt32, Int32.toInt_toInt16, digital_shift_sixteen, Int32.toInt_add, Int32.toInt_mul,
    Int32.toInt_mul, t, u, pa, pb, sum, fits]
  exact ⟨lo, hi⟩

/-- An `Int32` value in 16-bit range survives the cut to 16 bits. -/
private theorem digital_keep16 (x : Int32) (lo : -32768 ≤ x.toInt) (hi : x.toInt ≤ 32767) :
    x.toInt16.toInt = x.toInt := by
  rw [Int32.toInt_toInt16]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A value cut to 16 bits and widened again lies between -32768 and 32767. -/
private theorem digital_cut16_range (x : Int32) :
    -32768 ≤ x.toInt16.toInt32.toInt ∧ x.toInt16.toInt32.toInt ≤ 32767 := by
  rw [Int16.toInt_toInt32, Int32.toInt_toInt16]
  have lo := Int.le_bmod (x := x.toInt) (m := 2 ^ 16) (by decide)
  have hi := Int.bmod_lt (x := x.toInt) (m := 2 ^ 16) (by decide)
  omega

/-- A blended sine is a 16-bit value. -/
private theorem digital_sine_range (phase : UInt32) :
    -32768 ≤ (Analog.sineAt phase).toInt ∧ (Analog.sineAt phase).toInt ≤ 32767 := by
  unfold Analog.sineAt
  exact digital_cut16_range _

/-- A wave shaper's output is a 16-bit value. -/
private theorem digital_shape_range (table : UInt32 → Int16) (index : UInt32) :
    -32768 ≤ (Analog.shape table index).toInt ∧ (Analog.shape table index).toInt ≤ 32767 := by
  unfold Analog.shape Analog.blend88
  exact digital_cut16_range _

/-- Braids' `CLIP` gives a value between -32767 and 32767, and the 16-bit sample written is exactly that
value.
Why it matters: the engines that end in a clip (saw swarm, harmonics, FOF vowel, question mark) are limited
by the clip only, never a wrap. -/
theorem digital_clip_never_wraps (x : Int32) :
    (Digital.clip x).toInt16.toInt = (Digital.clip x).toInt ∧
      -32767 ≤ (Digital.clip x).toInt ∧ (Digital.clip x).toInt ≤ 32767 := by
  have range : -32767 ≤ (Digital.clip x).toInt ∧ (Digital.clip x).toInt ≤ 32767 := by
    unfold Digital.clip
    split
    · decide
    · split
      · decide
      · rename_i low high
        simp only [gt_iff_lt] at high
        rw [Int32.lt_iff_toInt_lt] at low high
        simp at low high
        omega
  exact ⟨digital_keep16 _ (by omega) range.2, range⟩

/-- Each of the three FM engines (FM, feedback FM, chaotic FM) writes exactly the blended sine at its
modulated phase; the cut to 16 bits changes nothing.
Why it matters: an FM sample is always a sine table value (`analog_sine_between_entries`), so no modulation
depth, feedback or sync can overflow it. -/
theorem digital_fm_never_wraps (phase modPhase inc modInc : UInt32) (previous : Int16)
    (index attenuation : Int32) (sync : UInt8) :
    (Digital.fm phase modPhase inc modInc index sync).out.toInt =
      (Analog.sineAt ((if sync != 0 then 0 else phase + inc) +
        ((Analog.sineAt ((if sync != 0 then 0 else modPhase) + modInc) * index) <<< 2).toUInt32)).toInt ∧
    (Digital.feedbackFm phase modPhase inc modInc previous index attenuation sync).out.toInt =
      (Analog.sineAt ((if sync != 0 then 0 else phase + inc) +
        ((Analog.sineAt ((if sync != 0 then 0 else modPhase) + modInc + (previous.toInt32 <<< 14).toUInt32) *
          ((index * attenuation) >>> 15)) <<< 1).toUInt32)).toInt ∧
    (Digital.chaoticFm phase modPhase inc modInc index sync).out.toInt =
      (Analog.sineAt ((if sync != 0 then 0 else phase + inc) +
        ((Analog.sineAt (if sync != 0 then 0 else modPhase) * index) <<< 1).toUInt32)).toInt := by
  unfold Digital.fm Digital.feedbackFm Digital.chaoticFm
  dsimp only
  exact ⟨digital_keep16 _ (digital_sine_range _).1 (digital_sine_range _).2,
    digital_keep16 _ (digital_sine_range _).1 (digital_sine_range _).2,
    digital_keep16 _ (digital_sine_range _).1 (digital_sine_range _).2⟩

/-- The product of two values of at most `m` and `n` in size is at most `m * n` in size. -/
private theorem digital_product_small (a b : Int) (m n : Nat) (ha : a.natAbs ≤ m) (hb : b.natAbs ≤ n) :
    -((m * n : Nat) : Int) ≤ a * b ∧ a * b ≤ ((m * n : Nat) : Int) := by
  have := Int.natAbs_mul a b
  have := Nat.mul_le_mul ha hb
  omega

/-- The product of two 16-bit signals is exact in 32 bits. -/
private theorem digital_product16 (a b : Int32) (ha : -32768 ≤ a.toInt ∧ a.toInt ≤ 32767)
    (hb : -32768 ≤ b.toInt ∧ b.toInt ≤ 32767) :
    (a * b).toInt = a.toInt * b.toInt ∧
      -1073741824 ≤ a.toInt * b.toInt ∧ a.toInt * b.toInt ≤ 1073741824 := by
  have small := digital_product_small a.toInt b.toInt 32768 32768 (by omega) (by omega)
  rw [Int32.toInt_mul]
  exact ⟨Int.bmod_eq_of_le (by omega) (by omega), by omega, by omega⟩

/-- The ring modulator's product of two 16-bit signals is their exact product divided by 65536, between
-16384 and 16384; the multiplication never wraps and the cut to 16 bits changes nothing.
Why it matters: the ring modulator multiplies three full-scale sines in a row, and the soft clipper after
them gets a value of at most half scale. -/
theorem digital_ring_product_never_wraps (a b : Int32)
    (ha : -32768 ≤ a.toInt ∧ a.toInt ≤ 32767) (hb : -32768 ≤ b.toInt ∧ b.toInt ≤ 32767) :
    (Digital.ringProduct a b).toInt = a.toInt * b.toInt / 65536 ∧
      -16384 ≤ (Digital.ringProduct a b).toInt ∧ (Digital.ringProduct a b).toInt ≤ 16384 := by
  unfold Digital.ringProduct
  obtain ⟨product, lo, hi⟩ := digital_product16 a b ha hb
  rw [Int16.toInt_toInt32, Int32.toInt_toInt16, digital_shift_sixteen, product,
    Int.bmod_eq_of_le (by omega) (by omega)]
  omega

/-- The ring modulator writes exactly its soft-clipped triple product; the cut to 16 bits changes nothing.
Why it matters: the sample is always a value of the overdrive shaper, so it cannot overflow. -/
theorem digital_ring_mod_never_wraps (phase mod1 mod2 inc inc1 inc2 : UInt32) (sync : UInt8) :
    (Digital.ringMod phase mod1 mod2 inc inc1 inc2 sync).out.toInt =
      (Analog.shape Digital.overdriveTable
        ((Digital.ringProduct (Digital.ringProduct (Analog.sineAt (if sync != 0 then 0 else phase + inc))
          (Analog.sineAt ((if sync != 0 then 0 else mod1) + inc1)))
          (Analog.sineAt ((if sync != 0 then 0 else mod2) + inc2)) + 32768) &&& 0xFFFF).toUInt32).toInt := by
  unfold Digital.ringMod
  dsimp only
  exact digital_keep16 _ (digital_shape_range _ _).1 (digital_shape_range _ _).2

/-- The toy's four weights add up to 56416, so the weighted average of four bytes shifted down 8 places is at
most 56195. -/
private theorem digital_toy_average (h1 h2 h3 h4 : UInt8) :
    (10530 * h1.toNat + 14751 * h2.toNat + 16384 * h3.toNat + 14751 * h4.toNat) / 256 ≤ 56195 := by
  have := h1.toNat_lt; have := h2.toNat_lt; have := h3.toNat_lt; have := h4.toNat_lt
  omega

/-- Taking 28208 from an average of at most 56195 in unsigned 32-bit arithmetic, then reading the low 16 bits
as signed, gives the signed difference. -/
private theorem digital_toy_centre (q : Nat) (small : q ≤ 56195) :
    (((2 ^ 32 - 28208 + q) % 2 ^ 32 % 2 ^ 16 : Nat) : Int).bmod (2 ^ 16) = (q : Int) - 28208 := by
  by_cases above : 28208 ≤ q
  · have low : (2 ^ 32 - 28208 + q) % 2 ^ 32 % 2 ^ 16 = q - 28208 := by omega
    rw [low, Int.natCast_sub above]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  · have low : (2 ^ 32 - 28208 + q) % 2 ^ 32 % 2 ^ 16 = q + 37328 := by omega
    rw [low, ← Int.sub_bmod_right, Int.bmod_eq_of_le (by omega) (by omega)]
    omega

/-- The toy's smoothing filter writes exactly the weighted average of its four held values, centred on zero
(between -28208 and 27987); the unsigned subtraction wraps for a low average and the read as a 16-bit value
undoes that wrap exactly.
Why it matters: the wrap Braids relies on is proved harmless; the sample is never off by 65536. -/
theorem digital_toy_never_wraps (h1 h2 h3 h4 : UInt8) :
    (Digital.toyFilter h1 h2 h3 h4).toInt =
      ((10530 * h1.toNat + 14751 * h2.toNat + 16384 * h3.toNat + 14751 * h4.toNat) / 256 : Nat) - 28208 := by
  unfold Digital.toyFilter
  dsimp only
  have b1 := h1.toNat_lt; have b2 := h2.toNat_lt; have b3 := h3.toNat_lt; have b4 := h4.toNat_lt
  have sum : (10530 * h1.toUInt32 + 14751 * h2.toUInt32 + 16384 * h3.toUInt32 + 14751 * h4.toUInt32).toNat =
      10530 * h1.toNat + 14751 * h2.toNat + 16384 * h3.toNat + 14751 * h4.toNat := by
    simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt8.toNat_toUInt32, UInt32.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod]
    omega
  have small := digital_toy_average h1 h2 h3 h4
  generalize 10530 * h1.toUInt32 + 14751 * h2.toUInt32 + 16384 * h3.toUInt32 + 14751 * h4.toUInt32 = s at sum
  have shifted : (s >>> 8).toNat =
      (10530 * h1.toNat + 14751 * h2.toNat + 16384 * h3.toNat + 14751 * h4.toNat) / 256 := by
    rw [UInt32.toNat_shiftRight, sum]
    have : (UInt32.toNat 8 % 32) = 8 := by decide
    rw [this, Nat.shiftRight_eq_div_pow]
  generalize (10530 * h1.toNat + 14751 * h2.toNat + 16384 * h3.toNat + 14751 * h4.toNat) / 256 = q at *
  generalize s >>> 8 = x at shifted
  show (x - 28208).toUInt16.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_bmod]
  have low16 : (x - 28208).toUInt16.toBitVec.toNat = (x - 28208).toNat % 2 ^ 16 := UInt32.toNat_toUInt16 _
  rw [low16, UInt32.toNat_sub, shifted]
  have centre : UInt32.toNat 28208 = 28208 := by decide
  rw [centre]
  exact digital_toy_centre q small
