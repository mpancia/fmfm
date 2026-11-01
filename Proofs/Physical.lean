import Firmware.Physical

/-- A 32-bit addition whose true sum fits is exact. -/
private theorem physical_add_exact (a b : Int32) (fits : (a.toInt + b.toInt).natAbs < 2 ^ 31) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [Int32.toInt_add]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A 32-bit subtraction whose true difference fits is exact. -/
private theorem physical_sub_exact (a b : Int32) (fits : (a.toInt - b.toInt).natAbs < 2 ^ 31) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [Int32.toInt_sub]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A 32-bit product whose true value fits is exact. -/
private theorem physical_mul_exact (a b : Int32) (fits : (a.toInt * b.toInt).natAbs < 2 ^ 31) :
    (a * b).toInt = a.toInt * b.toInt := by
  rw [Int32.toInt_mul]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- The size of a product is at most the product of the sizes. -/
private theorem physical_abs_mul_le (a b : Int) (A B : Nat) (ha : a.natAbs ≤ A) (hb : b.natAbs ≤ B) :
    (a * b).natAbs ≤ A * B := by
  rw [Int.natAbs_mul]; exact Nat.mul_le_mul ha hb

/-- An `Int32` shifted right one place is its value halved, rounded down. -/
private theorem physical_shift_one (s : Int32) : (s >>> 1).toInt = s.toInt / 2 := by
  show (s >>> 1).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by two places. -/
private theorem physical_shift_two (s : Int32) : (s >>> 2).toInt = s.toInt / 4 := by
  show (s >>> 2).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by five places. -/
private theorem physical_shift_five (s : Int32) : (s >>> 5).toInt = s.toInt / 32 := by
  show (s >>> 5).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by eight places. -/
private theorem physical_shift_eight (s : Int32) : (s >>> 8).toInt = s.toInt / 256 := by
  show (s >>> 8).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by nine places. -/
private theorem physical_shift_nine (s : Int32) : (s >>> 9).toInt = s.toInt / 512 := by
  show (s >>> 9).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by twelve places. -/
private theorem physical_shift_twelve (s : Int32) : (s >>> 12).toInt = s.toInt / 4096 := by
  show (s >>> 12).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by fifteen places. -/
private theorem physical_shift_fifteen (s : Int32) : (s >>> 15).toInt = s.toInt / 32768 := by
  show (s >>> 15).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by sixteen places. -/
private theorem physical_shift_sixteen (s : Int32) : (s >>> 16).toInt = s.toInt / 65536 := by
  show (s >>> 16).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- A shift left by one is a doubling. -/
private theorem physical_shift_left_one (s : Int32) : s <<< 1 = s * 2 := by
  apply Int32.toBitVec_inj.mp
  rw [Int32.toBitVec_shiftLeft, Int32.toBitVec_mul, BitVec.shiftLeft_eq', BitVec.shiftLeft_eq_mul_twoPow]
  rfl

/-- A shift left by eight is a multiplication by 256. -/
private theorem physical_shift_left_eight (s : Int32) : s <<< 8 = s * 256 := by
  apply Int32.toBitVec_inj.mp
  rw [Int32.toBitVec_shiftLeft, Int32.toBitVec_mul, BitVec.shiftLeft_eq', BitVec.shiftLeft_eq_mul_twoPow]
  rfl

/-- A shift left by nine is a multiplication by 512. -/
private theorem physical_shift_left_nine (s : Int32) : s <<< 9 = s * 512 := by
  apply Int32.toBitVec_inj.mp
  rw [Int32.toBitVec_shiftLeft, Int32.toBitVec_mul, BitVec.shiftLeft_eq', BitVec.shiftLeft_eq_mul_twoPow]
  rfl

/-- Braids' clip as a plain number: the value held between -32767 and 32767. -/
private theorem physical_clip_value (x : Int32) :
    (Digital.clip x).toInt = max (-32767) (min 32767 x.toInt) := by
  unfold Digital.clip
  split
  · rename_i lt; rw [Int32.lt_iff_toInt_lt] at lt; simp at lt ⊢; omega
  · split
    · rename_i _ gt; simp only [gt_iff_lt] at gt; rw [Int32.lt_iff_toInt_lt] at gt; simp at gt ⊢; omega
    · rename_i nlt ngt; simp only [gt_iff_lt] at ngt; rw [Int32.lt_iff_toInt_lt] at nlt ngt
      simp at nlt ngt; omega

/-- A value within 16 bits survives the cut to 16 bits. -/
private theorem physical_keep16 (x : Int32) (lo : -32768 ≤ x.toInt) (hi : x.toInt ≤ 32767) :
    x.toInt16.toInt = x.toInt := by
  rw [Int32.toInt_toInt16]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A `UInt32` below 2^31 keeps its value as an `Int32`. -/
private theorem physical_small_toInt32 (x : UInt32) (below : x.toNat < 2 ^ 31) :
    x.toInt32.toInt = (x.toNat : Int) := by
  show x.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt]
  · simp
  · simp at below ⊢; omega

/-- A signed value that is not negative keeps its value as an unsigned one. -/
private theorem physical_toUInt32_of_nonneg (p : Int32) (nonneg : 0 ≤ p.toInt) :
    p.toUInt32.toNat = p.toInt := by
  have e : p.toInt = p.toBitVec.toInt := rfl
  have n : p.toUInt32.toNat = p.toBitVec.toNat := rfl
  rw [BitVec.toInt_eq_toNat_cond] at e
  rw [n]
  have := BitVec.isLt p.toBitVec
  split at e <;> omega

/-- The low 16 bits of a value are at most 65535. -/
private theorem physical_and_ffff (x : UInt32) : (x &&& 0xFFFF).toNat ≤ 65535 := by
  rw [UInt32.toNat_and]
  have := Nat.and_le_right (n := x.toNat) (m := (0xFFFF : UInt32).toNat)
  simpa using this

/-- Weighting `a` by `N - t` and `b` by `t` (`0 ≤ t ≤ N`) lands between `lo * N` and `hi * N` when both are
between `lo` and `hi`. -/
private theorem physical_blend_bounds (a b t N lo hi : Int) (ht : 0 ≤ t ∧ t ≤ N)
    (ha : lo ≤ a ∧ a ≤ hi) (hb : lo ≤ b ∧ b ≤ hi) :
    lo * N ≤ a * (N - t) + b * t ∧ a * (N - t) + b * t ≤ hi * N := by
  have u1 := Int.mul_le_mul_of_nonneg_right ha.2 (by omega : 0 ≤ N - t)
  have l1 := Int.mul_le_mul_of_nonneg_right ha.1 (by omega : 0 ≤ N - t)
  have u2 := Int.mul_le_mul_of_nonneg_right hb.2 ht.1
  have l2 := Int.mul_le_mul_of_nonneg_right hb.1 ht.1
  simp only [Int.mul_sub] at u1 l1 ⊢
  omega

/-- Moving from `a` toward `b` by `t` parts in `N` (`0 ≤ t ≤ N`) lands between the two. -/
private theorem physical_between (a b t N : Int) (pos : 0 < N) (ht : 0 ≤ t ∧ t ≤ N) :
    min a b ≤ a + (b - a) * t / N ∧ a + (b - a) * t / N ≤ max a b := by
  by_cases h : 0 ≤ b - a
  · have u : (b - a) * t ≤ (b - a) * N := Int.mul_le_mul_of_nonneg_left ht.2 h
    have l : 0 ≤ (b - a) * t := Int.mul_nonneg h ht.1
    have u' := Int.ediv_le_ediv pos u
    rw [Int.mul_ediv_cancel _ (by omega)] at u'
    have l' := Int.ediv_nonneg l (by omega : (0 : Int) ≤ N)
    omega
  · have neg : b - a ≤ 0 := by omega
    have l : (b - a) * N ≤ (b - a) * t := Int.mul_le_mul_of_nonpos_left neg ht.2
    have u : (b - a) * t ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg neg ht.1
    have l' := Int.ediv_le_ediv pos l
    rw [Int.mul_ediv_cancel _ (by omega)] at l'
    have u' := Int.ediv_nonpos_of_nonpos_of_neg u pos
    omega

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

/-- Braids' `Mix` of two 16-bit delay-line samples by a 16-bit fraction is exact: the weighted sum sits at the
very edge of 32 bits (32768 times 65535) and never crosses it.
Why it matters: every delay-line read of the bowed string, blown pipe and flute goes through this blend; an
overflow here would put a wrong sample back into the string or bore on every pass. -/
theorem physical_mix_never_wraps (a b : Int32) (fraction : UInt32)
    (aFits : -32768 ≤ a.toInt ∧ a.toInt ≤ 32767) (bFits : -32768 ≤ b.toInt ∧ b.toInt ≤ 32767)
    (fractionFits : fraction.toNat ≤ 65535) :
    (Physical.mix a b fraction).toInt =
      (a.toInt * (65535 - fraction.toNat) + b.toInt * fraction.toNat) / 65536 := by
  unfold Physical.mix
  have f := physical_small_toInt32 fraction (by omega)
  have k : ((65535 : Int32) - fraction.toInt32).toInt = 65535 - fraction.toNat := by
    rw [physical_sub_exact _ _ (by rw [f]; simp; omega), f]; rfl
  have bounds := physical_blend_bounds a.toInt b.toInt fraction.toNat 65535 (-32768) 32767
    (by omega) aFits bFits
  have p1 : (a * ((65535 : Int32) - fraction.toInt32)).toInt = a.toInt * (65535 - fraction.toNat) := by
    rw [physical_mul_exact, k]
    rw [k]
    have := physical_abs_mul_le a.toInt (65535 - fraction.toNat) 32768 65535 (by omega) (by omega)
    omega
  have p2 : (b * fraction.toInt32).toInt = b.toInt * fraction.toNat := by
    rw [physical_mul_exact, f]
    rw [f]
    have := physical_abs_mul_le b.toInt fraction.toNat 32768 65535 (by omega) (by omega)
    omega
  rw [physical_shift_sixteen, physical_add_exact, p1, p2]
  rw [p1, p2]
  have := physical_abs_mul_le a.toInt (65535 - fraction.toNat) 32768 65535 (by omega) (by omega)
  have := physical_abs_mul_le b.toInt fraction.toNat 32768 65535 (by omega) (by omega)
  omega

/-- A blend of two 8-bit values lands within 8 bits. -/
private theorem physical_mix_fits_byte (a b : Int32) (fraction : UInt32)
    (aFits : -128 ≤ a.toInt ∧ a.toInt ≤ 127) (bFits : -128 ≤ b.toInt ∧ b.toInt ≤ 127)
    (fractionFits : fraction.toNat ≤ 65535) :
    -128 ≤ (Physical.mix a b fraction).toInt ∧ (Physical.mix a b fraction).toInt ≤ 127 := by
  rw [physical_mix_never_wraps a b fraction (by omega) (by omega) fractionFits]
  have := physical_blend_bounds a.toInt b.toInt fraction.toNat 65535 (-128) 127 (by omega) aFits bFits
  omega

/-- The comb filter's sample and the sample it feeds back are exact: the delayed sample is the exact blend of
its two neighbours, and each output is that arithmetic held between -32767 and 32767, with nothing wrapping in
between. Holds for 16-bit input and delay-line samples, a fraction from 0 to 65535 and a 16-bit resonance.
Why it matters: the comb's delay line feeds itself; a wrapped sample would ring round the loop as a click. -/
theorem physical_comb_never_wraps (input a b fraction resonance : Int32)
    (inputFits : -32768 ≤ input.toInt ∧ input.toInt ≤ 32767)
    (aFits : -32768 ≤ a.toInt ∧ a.toInt ≤ 32767) (bFits : -32768 ≤ b.toInt ∧ b.toInt ≤ 32767)
    (fractionFits : 0 ≤ fraction.toInt ∧ fraction.toInt ≤ 65535)
    (resonanceFits : -32768 ≤ resonance.toInt ∧ resonance.toInt ≤ 32767) :
    (Physical.comb input a b fraction resonance).out.toInt =
      max (-32767) (min 32767
        ((input.toInt + 2 * (a.toInt + (b.toInt - a.toInt) * (fraction.toInt / 2) / 32768)) / 2)) ∧
    (Physical.comb input a b fraction resonance).feedback.toInt =
      max (-32767) (min 32767
        ((a.toInt + (b.toInt - a.toInt) * (fraction.toInt / 2) / 32768) * resonance.toInt / 32768
          + input.toInt / 2)) := by
  unfold Physical.comb
  dsimp only
  have d : (b - a).toInt = b.toInt - a.toInt := physical_sub_exact _ _ (by omega)
  have half : (fraction >>> 1).toInt = fraction.toInt / 2 := physical_shift_one fraction
  have p : ((b - a) * (fraction >>> 1)).toInt = (b.toInt - a.toInt) * (fraction.toInt / 2) := by
    rw [physical_mul_exact, d, half]
    rw [d, half]
    have := physical_abs_mul_le (b.toInt - a.toInt) (fraction.toInt / 2) 65535 32767 (by omega) (by omega)
    omega
  have between := physical_between a.toInt b.toInt (fraction.toInt / 2) 32768 (by decide) (by omega)
  have delayed : (a + (((b - a) * (fraction >>> 1)) >>> 15)).toInt =
      a.toInt + (b.toInt - a.toInt) * (fraction.toInt / 2) / 32768 := by
    rw [physical_add_exact, physical_shift_fifteen, p]
    rw [physical_shift_fifteen, p]
    omega
  generalize hv : a + (((b - a) * (fraction >>> 1)) >>> 15) = v at delayed
  generalize hd : a.toInt + (b.toInt - a.toInt) * (fraction.toInt / 2) / 32768 = D at delayed between ⊢
  have vFits : -32768 ≤ v.toInt ∧ v.toInt ≤ 32767 := by omega
  constructor
  · have two : (2 : Int32).toInt = 2 := by decide
    have dbl : (v <<< 1).toInt = v.toInt * 2 := by
      rw [physical_shift_left_one, physical_mul_exact _ _ (by rw [two]; omega), two]
    have sum : (input + (v <<< 1)).toInt = input.toInt + v.toInt * 2 := by
      rw [physical_add_exact _ _ (by rw [dbl]; omega), dbl]
    rw [physical_keep16 _ (by rw [physical_clip_value]; omega) (by rw [physical_clip_value]; omega),
      physical_clip_value, physical_shift_one, sum]
    omega
  · have small := physical_abs_mul_le v.toInt resonance.toInt 32768 32768 (by omega) (by omega)
    have prod : (v * resonance).toInt = v.toInt * resonance.toInt := physical_mul_exact _ _ (by omega)
    have sum : (((v * resonance) >>> 15) + (input >>> 1)).toInt =
        v.toInt * resonance.toInt / 32768 + input.toInt / 2 := by
      rw [physical_add_exact, physical_shift_fifteen, physical_shift_one, prod]
      rw [physical_shift_fifteen, physical_shift_one, prod]
      omega
    rw [physical_keep16 _ (by rw [physical_clip_value]; omega) (by rw [physical_clip_value]; omega),
      physical_clip_value, sum, delayed]

/-- The comb filter reads its resonance curve inside the curve's 257 entries, whatever the setting.
Why it matters: the curve is a plain C array read without a bounds check; the cut to 16 bits before the
offset is what keeps every setting inside. -/
theorem physical_comb_resonance_index_in_table (parameter : Int32) :
    (Physical.combResonanceIndex parameter).toNat ≤ 65535 := by
  unfold Physical.combResonanceIndex
  have hi := Int16.toInt_lt ((parameter <<< 1) - 32768).toInt16
  have lo := Int16.le_toInt ((parameter <<< 1) - 32768).toInt16
  have c : (32768 : Int32).toInt = 32768 := by decide
  have sum : (((parameter <<< 1) - 32768).toInt16.toInt32 + 32768).toInt =
      ((parameter <<< 1) - 32768).toInt16.toInt + 32768 := by
    rw [physical_add_exact _ _ (by rw [Int16.toInt_toInt32, c]; omega), Int16.toInt_toInt32, c]
  have e := physical_toUInt32_of_nonneg _ (by rw [sum]; omega)
  rw [sum] at e
  omega

/-- Filling a new string never wraps: each place gets exactly a quarter of the old sample plus three quarters
of the noise, which fits 16 bits for 16-bit inputs.
Why it matters: a pluck starts from this fill; a wrapped value would start the note with a click. -/
theorem physical_pluck_fill_never_wraps (old noise : Int32)
    (oldFits : -32768 ≤ old.toInt ∧ old.toInt ≤ 32767)
    (noiseFits : -32768 ≤ noise.toInt ∧ noise.toInt ≤ 32767) :
    (Physical.pluckFill old noise).toInt = (old.toInt + 3 * noise.toInt) / 4 := by
  unfold Physical.pluckFill
  have three : (3 : Int32).toInt = 3 := by decide
  have p : ((3 : Int32) * noise).toInt = 3 * noise.toInt := by
    rw [physical_mul_exact _ _ (by rw [three]; omega), three]
  have sum : (old + 3 * noise).toInt = old.toInt + 3 * noise.toInt := by
    rw [physical_add_exact _ _ (by rw [p]; omega), p]
  rw [physical_keep16 _ (by rw [physical_shift_two, sum]; omega) (by rw [physical_shift_two, sum]; omega),
    physical_shift_two, sum]

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

/-- Reading the plucked string between two entries gives exactly the blend of the two, for 16-bit entries at
any phase. The product inside can pass 32 bits (as in Braids' `Interpolate1022`), but the excess is a multiple
of 2^16 and the cut to 16 bits removes it exactly.
Why it matters: this read is the plucked string's sample; the overflow in the original is shown harmless
rather than assumed. -/
theorem physical_pluck_read_never_wraps (a b : Int32) (phase : UInt32)
    (aFits : -32768 ≤ a.toInt ∧ a.toInt ≤ 32767) (bFits : -32768 ≤ b.toInt ∧ b.toInt ≤ 32767) :
    (Physical.pluckRead a b phase).toInt =
      a.toInt + (b.toInt - a.toInt) * ((phase >>> 6) &&& 0xFFFF).toNat / 65536 := by
  unfold Physical.pluckRead
  have f := physical_and_ffff (phase >>> 6)
  have t : ((phase >>> 6) &&& 0xFFFF).toInt32.toInt = (((phase >>> 6) &&& 0xFFFF).toNat : Int) :=
    physical_small_toInt32 _ (by omega)
  have d : (b - a).toInt = b.toInt - a.toInt := physical_sub_exact _ _ (by omega)
  have bt := physical_between a.toInt b.toInt (((phase >>> 6) &&& 0xFFFF).toNat : Int) 65536 (by decide)
    (by omega)
  rw [Int16.toInt_toInt32, Int32.toInt_toInt16, Int32.toInt_add, physical_shift_sixteen, Int32.toInt_mul, d,
    t]
  have pb := physical_abs_mul_le (b.toInt - a.toInt) (((phase >>> 6) &&& 0xFFFF).toNat : Int) 65535 65535
    (by omega) (by omega)
  generalize (b.toInt - a.toInt) * (((phase >>> 6) &&& 0xFFFF).toNat : Int) = P at *
  simp only [Int.bmod_def]
  split <;> split <;> split <;> omega

/-- The two samples of an engine that runs at half rate are exact: the sample is the voices' sum held between
-32767 and 32767, and the in-between sample is the mean of that and the previous 16-bit sample, rounded down.
Why it matters: the plucked string and the bowed string hand every other sample through here; the mean of two
16-bit values must not wrap on the way to the buffer. -/
theorem physical_half_rate_never_wraps (sum previous : Int32)
    (previousFits : -32768 ≤ previous.toInt ∧ previous.toInt ≤ 32767) :
    (Digital.clip sum).toInt16.toInt = max (-32767) (min 32767 sum.toInt) ∧
    (Physical.halfSum (Digital.clip sum) previous).toInt =
      (max (-32767) (min 32767 sum.toInt) + previous.toInt) / 2 := by
  have c := physical_clip_value sum
  constructor
  · rw [physical_keep16 _ (by omega) (by omega), c]
  · unfold Physical.halfSum
    have s : (Digital.clip sum + previous).toInt = max (-32767) (min 32767 sum.toInt) + previous.toInt := by
      rw [physical_add_exact _ _ (by omega), c]
    rw [physical_keep16 _ (by rw [physical_shift_one, s]; omega) (by rw [physical_shift_one, s]; omega),
      physical_shift_one, s]

/-- The bowed string's sample is exact: the body filter's arithmetic on the bridge sample (the blend of two
8-bit line samples, scaled up by 256) and its two previous outputs, held between -32767 and 32767. The two
previous outputs are within 2^18, which `physical_bowed_body_stays_bounded` keeps true from one sample to the
next.
Why it matters: the body filter runs on every sample of a bowed note; a wrap in it would be a click. -/
theorem physical_bowed_never_wraps (bridgeA bridgeB nutA nutB : Int32) (bridgeFraction neckFraction : UInt32)
    (lp : Int32) (excitation : UInt32) (bow : Int32) (y0 y1 : Int32)
    (bridgeAFits : -128 ≤ bridgeA.toInt ∧ bridgeA.toInt ≤ 127)
    (bridgeBFits : -128 ≤ bridgeB.toInt ∧ bridgeB.toInt ≤ 127)
    (bridgeFractionFits : bridgeFraction.toNat ≤ 65535)
    (y0Fits : y0.toInt.natAbs ≤ 2 ^ 18) (y1Fits : y1.toInt.natAbs ≤ 2 ^ 18) :
    (Physical.bowed bridgeA bridgeB nutA nutB bridgeFraction neckFraction lp excitation bow y0 y1).out.toInt =
      max (-32767) (min 32767
        ((Physical.mix bridgeA bridgeB bridgeFraction).toInt * 256 * 6553 / 32768
          + y0.toInt * 6948 / 4096 + y1.toInt * (-2959) / 4096 - y1.toInt)) := by
  have shape :
      (Physical.bowed bridgeA bridgeB nutA nutB bridgeFraction neckFraction lp excitation bow y0 y1).out =
      (Digital.clip ((((Physical.mix bridgeA bridgeB bridgeFraction <<< 8) * 6553) >>> 15)
        + ((y0 * 6948) >>> 12) + ((y1 * (-2959 : Int32)) >>> 12) - y1)).toInt16 := rfl
  rw [shape]
  have mixFits := physical_mix_fits_byte bridgeA bridgeB bridgeFraction bridgeAFits bridgeBFits
    bridgeFractionFits
  generalize Physical.mix bridgeA bridgeB bridgeFraction = m at mixFits ⊢
  have c256 : (256 : Int32).toInt = 256 := by decide
  have c6553 : (6553 : Int32).toInt = 6553 := by decide
  have c6948 : (6948 : Int32).toInt = 6948 := by decide
  have c2959 : (-2959 : Int32).toInt = -2959 := by decide
  have bridge : (m <<< 8).toInt = m.toInt * 256 := by
    rw [physical_shift_left_eight, physical_mul_exact _ _ (by rw [c256]; omega), c256]
  have t0 : (((m <<< 8) * 6553) >>> 15).toInt = m.toInt * 256 * 6553 / 32768 := by
    rw [physical_shift_fifteen, physical_mul_exact _ _ (by rw [bridge, c6553]; omega), bridge, c6553]
  have t1 : ((y0 * 6948) >>> 12).toInt = y0.toInt * 6948 / 4096 := by
    rw [physical_shift_twelve, physical_mul_exact _ _ (by rw [c6948]; omega), c6948]
  have t2 : ((y1 * (-2959 : Int32)) >>> 12).toInt = y1.toInt * (-2959) / 4096 := by
    rw [physical_shift_twelve, physical_mul_exact _ _ (by rw [c2959]; omega), c2959]
  generalize ((m <<< 8) * 6553) >>> 15 = T0 at t0
  generalize (y0 * 6948) >>> 12 = T1 at t1
  generalize (y1 * (-2959 : Int32)) >>> 12 = T2 at t2
  have temp : (T0 + T1 + T2).toInt = T0.toInt + T1.toInt + T2.toInt := by
    rw [physical_add_exact, physical_add_exact _ _ (by omega)]
    rw [physical_add_exact _ _ (by omega)]
    omega
  have diff : (T0 + T1 + T2 - y1).toInt = T0.toInt + T1.toInt + T2.toInt - y1.toInt := by
    rw [physical_sub_exact _ _ (by rw [temp]; omega), temp]
  rw [physical_keep16 _ (by rw [physical_clip_value]; omega) (by rw [physical_clip_value]; omega),
    physical_clip_value, diff, t0, t1, t2]

/-- The bowed string's bridge low-pass never runs away: when its state is within 16 bits, so is the next
state, for 8-bit line samples and any fraction up to 65535.
Why it matters: this state feeds the string back to itself on every sample; a state that could grow would make
the string swell instead of settle, and would wrap the bow's arithmetic. -/
theorem physical_bowed_lowpass_stays_bounded (bridgeA bridgeB nutA nutB : Int32)
    (bridgeFraction neckFraction : UInt32) (lp : Int32) (excitation : UInt32) (bow : Int32) (y0 y1 : Int32)
    (bridgeAFits : -128 ≤ bridgeA.toInt ∧ bridgeA.toInt ≤ 127)
    (bridgeBFits : -128 ≤ bridgeB.toInt ∧ bridgeB.toInt ≤ 127)
    (bridgeFractionFits : bridgeFraction.toNat ≤ 65535) (lpFits : lp.toInt.natAbs ≤ 32768) :
    (Physical.bowed bridgeA bridgeB nutA nutB bridgeFraction neckFraction lp excitation bow
      y0 y1).lp.toInt.natAbs ≤ 32768 := by
  have shape :
      (Physical.bowed bridgeA bridgeB nutA nutB bridgeFraction neckFraction lp excitation bow y0 y1).lp =
      (((Physical.mix bridgeA bridgeB bridgeFraction <<< 8) * 14008) + (lp * 18022)) >>> 15 := rfl
  rw [shape]
  have mixFits := physical_mix_fits_byte bridgeA bridgeB bridgeFraction bridgeAFits bridgeBFits
    bridgeFractionFits
  generalize Physical.mix bridgeA bridgeB bridgeFraction = m at mixFits ⊢
  have c256 : (256 : Int32).toInt = 256 := by decide
  have c14008 : (14008 : Int32).toInt = 14008 := by decide
  have c18022 : (18022 : Int32).toInt = 18022 := by decide
  have bridge : (m <<< 8).toInt = m.toInt * 256 := by
    rw [physical_shift_left_eight, physical_mul_exact _ _ (by rw [c256]; omega), c256]
  have t0 : ((m <<< 8) * 14008).toInt = m.toInt * 256 * 14008 := by
    rw [physical_mul_exact _ _ (by rw [bridge, c14008]; omega), bridge, c14008]
  have t1 : (lp * 18022).toInt = lp.toInt * 18022 := by
    rw [physical_mul_exact _ _ (by rw [c18022]; omega), c18022]
  rw [physical_shift_fifteen, physical_add_exact _ _ (by rw [t0, t1]; omega), t0, t1]
  omega

/-- The bowed string reads its friction curve inside the curve's 257 entries, for a bow pressure up to 1024
and a bow-to-string speed difference up to 2^20 (Braids' pressure is at most 172 and the difference at most
2^17).
Why it matters: the friction read is a plain C array access with no bounds check; the cap at 131071 before
the top 8 bits are taken is what keeps it inside. -/
theorem physical_friction_index_in_table (delta bow : Int32)
    (deltaFits : delta.toInt.natAbs ≤ 2 ^ 20) (bowFits : bow.toInt.natAbs ≤ 1024) :
    (Physical.frictionIndex delta bow).toNat ≤ 255 := by
  unfold Physical.frictionIndex
  dsimp only
  have small := physical_abs_mul_le delta.toInt bow.toInt (2 ^ 20) 1024 deltaFits bowFits
  have raw : ((delta * bow) >>> 5).toInt = delta.toInt * bow.toInt / 32 := by
    rw [physical_shift_five, physical_mul_exact _ _ (by omega)]
  generalize (delta * bow) >>> 5 = r at raw
  have magnitude : (if r < 0 then -r else r).toInt = if r.toInt < 0 then -r.toInt else r.toInt := by
    split
    · rename_i neg
      rw [Int32.lt_iff_toInt_lt] at neg
      simp at neg
      rw [Int32.toInt_neg, Int.bmod_eq_of_le (by omega) (by omega)]
      split <;> omega
    · rename_i nonneg
      rw [Int32.lt_iff_toInt_lt] at nonneg
      simp at nonneg
      split <;> omega
  generalize (if r < 0 then -r else r) = mag at magnitude
  have magFits : 0 ≤ mag.toInt ∧ mag.toInt ≤ 2 ^ 25 := by rw [magnitude]; split <;> omega
  have capped : (if mag ≥ 131072 then (131071 : Int32) else mag).toInt =
      if 131072 ≤ mag.toInt then 131071 else mag.toInt := by
    split
    · rename_i ge
      simp only [ge_iff_le] at ge
      rw [Int32.le_iff_toInt_le] at ge
      simp at ge ⊢
      omega
    · rename_i lt
      simp only [ge_iff_le] at lt
      rw [Int32.le_iff_toInt_le] at lt
      simp at lt
      split <;> omega
  generalize (if mag ≥ 131072 then (131071 : Int32) else mag) = cap at capped
  have capFits : 0 ≤ cap.toInt ∧ cap.toInt ≤ 131071 := by rw [capped]; split <;> omega
  have e := physical_toUInt32_of_nonneg (cap >>> 9) (by rw [physical_shift_nine]; omega)
  rw [physical_shift_nine] at e
  omega

/-- The blown pipe's output filter lands between the bore's new sample and the filter's own last output, so it
fits 16 bits with nothing to cut, for a coefficient from 0 to 4096 and a 16-bit last output.
Why it matters: this filter is the blown pipe's sample; it can only smooth what the bore gives it, never add a
wrapped value of its own. -/
theorem physical_blown_filter_stays_between (noise a b : Int32) (fraction : UInt32)
    (lp parameter filter coefficient : Int32)
    (coefficientFits : 0 ≤ coefficient.toInt ∧ coefficient.toInt ≤ 4096)
    (filterFits : -32768 ≤ filter.toInt ∧ filter.toInt ≤ 32767) :
    min (Physical.blown noise a b fraction lp parameter filter coefficient).bore.toInt filter.toInt ≤
        (Physical.blown noise a b fraction lp parameter filter coefficient).filter.toInt ∧
      (Physical.blown noise a b fraction lp parameter filter coefficient).filter.toInt ≤
        max (Physical.blown noise a b fraction lp parameter filter coefficient).bore.toInt filter.toInt := by
  unfold Physical.blown
  dsimp only
  generalize h : Digital.clip ((((_ : Int32) * (_ : Int32)) >>> (15 : Int32)) + (_ : Int32)) = out
  have outFits : -32767 ≤ out.toInt ∧ out.toInt ≤ 32767 := by rw [← h, physical_clip_value]; omega
  clear h
  have c4096 : (4096 : Int32).toInt = 4096 := by decide
  have k : ((4096 : Int32) - coefficient).toInt = 4096 - coefficient.toInt := by
    rw [physical_sub_exact _ _ (by rw [c4096]; omega), c4096]
  have bounds := physical_blend_bounds out.toInt filter.toInt (4096 - coefficient.toInt) 4096
    (min out.toInt filter.toInt) (max out.toInt filter.toInt) (by omega) (by omega) (by omega)
  have p1 : (coefficient * out).toInt = out.toInt * (4096 - (4096 - coefficient.toInt)) := by
    have e : 4096 - (4096 - coefficient.toInt) = coefficient.toInt := by omega
    have := physical_abs_mul_le coefficient.toInt out.toInt 4096 32767 (by omega) (by omega)
    rw [e, physical_mul_exact _ _ (by omega), Int.mul_comm]
  have p2 : (((4096 : Int32) - coefficient) * filter).toInt = filter.toInt * (4096 - coefficient.toInt) := by
    have := physical_abs_mul_le (4096 - coefficient.toInt) filter.toInt 4096 32768 (by omega) (by omega)
    rw [physical_mul_exact _ _ (by rw [k]; omega), k, Int.mul_comm]
  have sum : (coefficient * out + ((4096 : Int32) - coefficient) * filter).toInt =
      out.toInt * (4096 - (4096 - coefficient.toInt)) + filter.toInt * (4096 - coefficient.toInt) := by
    rw [physical_add_exact _ _ (by rw [p1, p2]; omega), p1, p2]
  rw [physical_keep16 out (by omega) (by omega), physical_keep16 _ (by rw [physical_shift_twelve, sum]; omega)
    (by rw [physical_shift_twelve, sum]; omega), physical_shift_twelve, sum]
  omega

/-- The flute's sample is exact: the bore's blended 8-bit sample scaled up by 256, held between -32767 and
32767, for 8-bit line samples and any fraction up to 65535.
Why it matters: the flute's sample is read straight off the bore; nothing on that path can wrap. -/
theorem physical_fluted_never_wraps (boreA boreB jetA jetB : Int32) (boreFraction jetFraction : UInt32)
    (excitation : UInt32) (noise intensity coefficient lp dcX dcY : Int32)
    (boreAFits : -128 ≤ boreA.toInt ∧ boreA.toInt ≤ 127) (boreBFits : -128 ≤ boreB.toInt ∧ boreB.toInt ≤ 127)
    (boreFractionFits : boreFraction.toNat ≤ 65535) :
    (Physical.fluted boreA boreB jetA jetB boreFraction jetFraction excitation noise intensity coefficient
        lp dcX dcY).out.toInt =
      max (-32767) (min 32767 ((Physical.mix boreA boreB boreFraction).toInt * 256)) := by
  have shape : (Physical.fluted boreA boreB jetA jetB boreFraction jetFraction excitation noise intensity
      coefficient lp dcX dcY).out =
      (Digital.clip ((Physical.mix boreA boreB boreFraction <<< 9) >>> 1)).toInt16 := rfl
  rw [shape]
  have mixFits := physical_mix_fits_byte boreA boreB boreFraction boreAFits boreBFits boreFractionFits
  generalize Physical.mix boreA boreB boreFraction = m at mixFits ⊢
  have c512 : (512 : Int32).toInt = 512 := by decide
  have bore : ((m <<< 9) >>> 1).toInt = m.toInt * 256 := by
    rw [physical_shift_one, physical_shift_left_nine, physical_mul_exact _ _ (by rw [c512]; omega), c512]
    omega
  rw [physical_keep16 _ (by rw [physical_clip_value]; omega) (by rw [physical_clip_value]; omega),
    physical_clip_value, bore]

/-- The flute reads its jet curve inside the curve's 257 entries, whatever the jet's value.
Why it matters: the jet read is a plain C array access with no bounds check; the limit to 0 to 65535 before
the top 8 bits are taken is what keeps it inside. -/
theorem physical_jet_index_in_table (jetValue : Int32) : (Physical.jetIndex jetValue).toNat ≤ 255 := by
  unfold Physical.jetIndex
  dsimp only
  have limFits :
      0 ≤ (if jetValue < 0 then (0 : Int32) else if jetValue > 65535 then 65535 else jetValue).toInt ∧
      (if jetValue < 0 then (0 : Int32) else if jetValue > 65535 then 65535 else jetValue).toInt ≤ 65535 := by
    split
    · simp
    · rename_i nonneg
      rw [Int32.lt_iff_toInt_lt] at nonneg; simp at nonneg
      split
      · simp
      · rename_i small
        simp only [gt_iff_lt] at small; rw [Int32.lt_iff_toInt_lt] at small; simp at small
        omega
  generalize (if jetValue < 0 then (0 : Int32) else if jetValue > 65535 then 65535 else jetValue) = lim
    at limFits
  have e := physical_toUInt32_of_nonneg (lim >>> 8) (by rw [physical_shift_eight]; omega)
  rw [physical_shift_eight] at e
  omega

/-- The body filter's state the bowed string carries to the next sample is within 2^18, whatever the inputs.
Why it matters: with `physical_bowed_never_wraps` this closes the loop: the two states a sample needs are the
two a previous sample left, so the body filter never wraps however long the note is bowed. -/
theorem physical_bowed_body_stays_bounded (bridgeA bridgeB nutA nutB : Int32)
    (bridgeFraction neckFraction : UInt32) (lp : Int32) (excitation : UInt32) (bow : Int32) (y0 y1 : Int32) :
    let step := Physical.bowed bridgeA bridgeB nutA nutB bridgeFraction neckFraction lp excitation bow y0 y1
    step.biquad.toInt.natAbs ≤ 2 ^ 18 := by
  intro step
  have shape :
      (Physical.bowed bridgeA bridgeB nutA nutB bridgeFraction neckFraction lp excitation bow y0 y1).biquad =
      Physical.bodyState ((((Physical.mix bridgeA bridgeB bridgeFraction <<< 8) * 6553) >>> 15)
        + ((y0 * 6948) >>> 12) + ((y1 * (-2959 : Int32)) >>> 12)) := rfl
  rw [shape]
  generalize (((Physical.mix bridgeA bridgeB bridgeFraction <<< 8) * 6553) >>> 15)
        + ((y0 * 6948) >>> 12) + ((y1 * (-2959 : Int32)) >>> 12) = temp
  have hi : (262144 : Int32).toInt = 262144 := by decide
  have lo : (-262144 : Int32).toInt = -262144 := by decide
  unfold Physical.bodyState
  split
  · rw [hi]; decide
  · split
    · rw [lo]; decide
    · rename_i notHigh notLow
      rw [Int32.not_lt, Int32.le_iff_toInt_le, hi] at notHigh
      rw [Int32.not_lt, Int32.le_iff_toInt_le, lo] at notLow
      omega
