import Firmware.Vowels
import Proofs.Digital

/-- An `Int32` shifted right one place is its value halved, rounded down. -/
private theorem vowels_shift_one (s : Int32) : (s >>> 1).toInt = s.toInt / 2 := by
  have : (s >>> 1).toInt = s.toInt >>> 1 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (1 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- An `Int32` shifted right 14 places is its value divided by 16384, rounded down. -/
private theorem vowels_shift_fourteen (s : Int32) : (s >>> 14).toInt = s.toInt / 16384 := by
  have : (s >>> 14).toInt = s.toInt >>> 14 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (14 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- An `Int32` shifted right 15 places is its value divided by 32768, rounded down. -/
private theorem vowels_shift_fifteen (s : Int32) : (s >>> 15).toInt = s.toInt / 32768 := by
  have : (s >>> 15).toInt = s.toInt >>> 15 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (15 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- An `Int32` shifted right 17 places is its value divided by 131072, rounded down. -/
private theorem vowels_shift_seventeen (s : Int32) : (s >>> 17).toInt = s.toInt / 131072 := by
  have : (s >>> 17).toInt = s.toInt >>> 17 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (17 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- An `Int32` value in 16-bit range survives the cut to 16 bits. -/
private theorem vowels_keep16 (x : Int32) (lo : -32768 ≤ x.toInt) (hi : x.toInt ≤ 32767) :
    x.toInt16.toInt = x.toInt := by
  rw [Int32.toInt_toInt16]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- The product of two values of at most `m` and `n` in size is at most `m * n` in size. -/
private theorem vowels_product_small (a b : Int) (m n : Nat) (ha : a.natAbs ≤ m) (hb : b.natAbs ≤ n) :
    -((m * n : Nat) : Int) ≤ a * b ∧ a * b ≤ ((m * n : Nat) : Int) := by
  have := Int.natAbs_mul a b
  have := Nat.mul_le_mul ha hb
  omega

/-- A clipped band-pass state times a 16-bit amplitude is exact in 32 bits, and shifted down 17 places it is
between -8192 and 8191. -/
private theorem vowels_contribution (band amp : Int32) (band16 : -32767 ≤ band.toInt ∧ band.toInt ≤ 32767)
    (amp16 : -32768 ≤ amp.toInt ∧ amp.toInt ≤ 32767) :
    (band * amp).toInt = band.toInt * amp.toInt ∧
      -8192 ≤ band.toInt * amp.toInt / 131072 ∧ band.toInt * amp.toInt / 131072 ≤ 8191 := by
  have small := vowels_product_small band.toInt amp.toInt 32767 32768 (by omega) (by omega)
  rw [Int32.toInt_mul]
  exact ⟨Int.bmod_eq_of_le (by omega) (by omega), by omega, by omega⟩

/-- Each formant filter of the FOF vowel contributes exactly its band-pass state scaled by the amplitude (a
16-bit value) and divided by 131072: between -8192 and 8191, with nothing wrapping.
Why it matters: the five contributions are added in C as a 32-bit sum, which therefore never passes 40960, so
the clip after it is the only thing that limits the FOF vowel. -/
theorem vowels_fof_contribution_never_wraps (lp bp f amp input : Int32)
    (amp16 : -32768 ≤ amp.toInt ∧ amp.toInt ≤ 32767) :
    (Vowels.fofFilter lp bp f amp input).contribution.toInt =
        (Vowels.fofFilter lp bp f amp input).bp.toInt * amp.toInt / 131072 ∧
      -8192 ≤ (Vowels.fofFilter lp bp f amp input).contribution.toInt ∧
        (Vowels.fofFilter lp bp f amp input).contribution.toInt ≤ 8191 := by
  unfold Vowels.fofFilter
  dsimp only
  obtain ⟨_, clipped⟩ := digital_clip_never_wraps
    (bp + ((f * ((input - (bp >>> 6)) - Digital.clip (lp + ((f * bp) >>> 15)))) >>> 15))
  generalize
    Digital.clip (bp + ((f * ((input - (bp >>> 6)) - Digital.clip (lp + ((f * bp) >>> 15)))) >>> 15)) =
    band at clipped ⊢
  obtain ⟨product, lo, hi⟩ := vowels_contribution band amp clipped amp16
  rw [vowels_shift_seventeen, product]
  exact ⟨rfl, lo, hi⟩

/-- The FOF vowel writes exactly its clipped filter sum, and the in-between sample exactly the average of that
with the last sample.
Why it matters: the FOF vowel is limited by its clip and only its clip; the half-rate smoothing cannot wrap,
so the engine cannot click from an overflow. -/
theorem vowels_fof_out_never_wraps (sum previous : Int32)
    (previous16 : -32768 ≤ previous.toInt ∧ previous.toInt ≤ 32767) :
    (Vowels.fofOut sum previous).out.toInt = (Digital.clip sum).toInt ∧
      (Vowels.fofOut sum previous).mid.toInt = ((Digital.clip sum).toInt + previous.toInt) / 2 := by
  unfold Vowels.fofOut
  dsimp only
  obtain ⟨written, lo, hi⟩ := digital_clip_never_wraps sum
  refine ⟨written, ?_⟩
  generalize Digital.clip sum = c at *
  have added : (c + previous).toInt = c.toInt + previous.toInt := by
    rw [Int32.toInt_add]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have halved : ((c + previous) >>> 1).toInt = (c.toInt + previous.toInt) / 2 := by
    rw [vowels_shift_one, added]
  rw [vowels_keep16 _ (by omega) (by omega), halved]

/-- The square of a clipped sample is exact in 32 bits, and shifted down 14 places it is between 0 and
65535. -/
private theorem vowels_square (sample : Int32) (clipped : -32767 ≤ sample.toInt ∧ sample.toInt ≤ 32767) :
    (sample * sample).toInt = sample.toInt * sample.toInt ∧
      0 ≤ sample.toInt * sample.toInt / 16384 ∧ sample.toInt * sample.toInt / 16384 ≤ 65535 := by
  have small := vowels_product_small sample.toInt sample.toInt 32767 32767 (by omega) (by omega)
  have nonneg : 0 ≤ sample.toInt * sample.toInt := by
    have := Int.natAbs_mul_self (a := sample.toInt)
    omega
  rw [Int32.toInt_mul]
  exact ⟨Int.bmod_eq_of_le (by omega) (by omega), by omega, by omega⟩

/-- A value of 0 to 65535 times a drive of 0 to 32767 is exact in 32 bits, and shifted down 15 places it is
between 0 and 65535. -/
private theorem vowels_driven (square parameter : Int) (hs : 0 ≤ square ∧ square ≤ 65535)
    (drive : 0 ≤ parameter ∧ parameter ≤ 32767) :
    (square * parameter).bmod (2 ^ 32) = square * parameter ∧
      0 ≤ square * parameter / 32768 ∧ square * parameter / 32768 ≤ 65535 := by
  have := Int.mul_le_mul hs.2 drive.2 drive.1 (by decide)
  have := Int.mul_nonneg hs.1 drive.1
  exact ⟨Int.bmod_eq_of_le (by omega) (by omega), by omega, by omega⟩

/-- The question mark's distortion term is exactly the square-law formula, between 0 and 65535, for a clipped
sample and a drive of 0 to 32767: neither product wraps.
Why it matters: at full drive the distortion cannot overflow and flip the sample's sign; the clip after it is
the only thing that limits the question mark. -/
theorem vowels_question_drive_never_wraps (sample parameter : Int32)
    (clipped : -32767 ≤ sample.toInt ∧ sample.toInt ≤ 32767)
    (drive : 0 ≤ parameter.toInt ∧ parameter.toInt ≤ 32767) :
    (Vowels.questionDrive sample parameter).toInt =
        sample.toInt * sample.toInt / 16384 * parameter.toInt / 32768 ∧
      0 ≤ (Vowels.questionDrive sample parameter).toInt ∧
        (Vowels.questionDrive sample parameter).toInt ≤ 65535 := by
  unfold Vowels.questionDrive
  obtain ⟨squared, lo, hi⟩ := vowels_square sample clipped
  obtain ⟨scaled, dlo, dhi⟩ :=
    vowels_driven (sample.toInt * sample.toInt / 16384) parameter.toInt ⟨lo, hi⟩ drive
  rw [vowels_shift_fifteen, Int32.toInt_mul, vowels_shift_fourteen, squared, scaled]
  exact ⟨rfl, dlo, dhi⟩
