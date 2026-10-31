import Firmware.Analog
import Proofs.Blend

/-- Clamping to 65535 leaves a value of at most 65535. -/
private theorem analog_clamp_le (t : UInt32) : (if t > 65535 then (65535 : UInt32) else t).toNat ≤ 65535 := by
  by_cases h : t > 65535
  · simp [h]
  · simp only [h, ite_false]
    have : ¬ (65535 < t.toNat) := by
      intro bad
      exact h (by simpa [UInt32.lt_iff_toNat_lt] using bad)
    omega

/-- The square of a number of at most 65535, shifted down 18 places, is below 16384 and does not wrap. -/
private theorem analog_square_shift (c : UInt32) (bound : c.toNat ≤ 65535) :
    ((c * c) >>> 18).toNat < 16384 := by
  have noWrap : c.toNat * c.toNat < 4294967296 := Nat.lt_of_le_of_lt (Nat.mul_le_mul bound bound) (by omega)
  rw [UInt32.toNat_shiftRight, UInt32.toNat_mul, Nat.mod_eq_of_lt noWrap]
  simp only [Nat.shiftRight_eq_div_pow]
  have : (UInt32.toNat 18 % 32) = 18 := by decide
  rw [this]
  omega

/-- A `UInt32` below 2^31 keeps its value when read as an `Int32`. -/
private theorem analog_uint32_toInt32_toInt (x : UInt32) (below : x.toNat < 2 ^ 31) :
    x.toInt32.toInt = (x.toNat : Int) := by
  show x.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt]
  · simp
  · simp at below ⊢; omega

/-- The correction a step edge adds to its own sample is between 0 and 16383.
Why it matters: the band-limiting correction can never be large enough to throw a sample out of range. -/
theorem analog_this_blep_range (t : UInt32) :
    0 ≤ (Analog.thisBlep t).toInt ∧ (Analog.thisBlep t).toInt ≤ 16383 := by
  have small := analog_square_shift _ (analog_clamp_le t)
  unfold Analog.thisBlep
  rw [analog_uint32_toInt32_toInt _ (by omega)]
  omega

/-- The correction a step edge leaves for the next sample is between -16383 and 0.
Why it matters: like the correction for its own sample, it can never throw a sample out of range. -/
theorem analog_next_blep_range (t : UInt32) :
    -16383 ≤ (Analog.nextBlep t).toInt ∧ (Analog.nextBlep t).toInt ≤ 0 := by
  have small := analog_square_shift _ (by
    have := analog_clamp_le t
    simp only [UInt32.toNat_sub, UInt32.toNat_ofNat] at *
    omega : (65535 - (if t > 65535 then (65535 : UInt32) else t)).toNat ≤ 65535)
  unfold Analog.nextBlep
  dsimp only
  generalize ((65535 - (if t > 65535 then (65535 : UInt32) else t)) *
    (65535 - (if t > 65535 then (65535 : UInt32) else t))) >>> 18 = x at *
  have value := analog_uint32_toInt32_toInt x (by omega)
  rw [Int32.toInt_sub, value]
  simp [Int.bmod_def]
  omega

/-- A 16-bit pattern read as signed lies between -32768 and 32767. -/
private theorem analog_signed_half (folded : UInt32) (small : folded.toNat < 65536) :
    -32768 ≤ (if folded ≥ 0x8000 then folded.toInt32 - 65536 else folded.toInt32).toInt ∧
      (if folded ≥ 0x8000 then folded.toInt32 - 65536 else folded.toInt32).toInt ≤ 32767 := by
  have value := analog_uint32_toInt32_toInt folded (by omega)
  by_cases high : folded ≥ 0x8000
  · have big : 0x8000 ≤ folded.toNat := by simpa [UInt32.le_iff_toNat_le] using high
    simp only [high, ite_true]
    rw [Int32.toInt_sub, value]
    simp [Int.bmod_def]
    omega
  · have low : folded.toNat < 0x8000 := by
      have : ¬ (0x8000 ≤ folded.toNat) := fun h => high (by simpa [UInt32.le_iff_toNat_le] using h)
      omega
    simp only [high, ite_false]
    omega

/-- Shifting an `Int32` right by one halves it, rounding down. -/
private theorem analog_int32_shift_one (s : Int32) : (s >>> 1).toInt = s.toInt / 2 := by
  have : (s >>> 1).toInt = s.toInt >>> 1 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (1 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  simp

/-- A triangle wave lies between -32768 and 32767. -/
private theorem analog_triangle_wave_range (phase : UInt32) :
    -32768 ≤ (Analog.triangleWave phase).toInt ∧ (Analog.triangleWave phase).toInt ≤ 32767 := by
  unfold Analog.triangleWave
  dsimp only
  generalize (((phase >>> 16) <<< 1) ^^^ (if (phase >>> 16) &&& 0x8000 != 0 then (0xFFFF : UInt32) else 0)) = raw
  have folded : (((raw &&& 0xFFFF) ^^^ 0x8000 : UInt32)).toNat < 65536 := by
    rw [UInt32.toNat_xor, UInt32.toNat_and]
    exact Nat.xor_lt_two_pow (n := 16) (Nat.and_lt_two_pow _ (by decide)) (by decide)
  exact analog_signed_half _ folded

/-- Each half of a triangle step lies between -16384 and 16383.
Why it matters: the two halves can be added without ever leaving the range of a 16-bit sample. -/
theorem analog_triangle_half_range (phase : UInt32) :
    -16384 ≤ (Analog.triangleHalf phase).toInt ∧ (Analog.triangleHalf phase).toInt ≤ 16383 := by
  unfold Analog.triangleHalf
  rw [analog_int32_shift_one]
  have := analog_triangle_wave_range phase
  omega

/-- The triangle's sample is exactly the sum of its two halves: nothing wraps around.
Why it matters: the triangle can never click from an overflow, at any pitch or phase. -/
theorem analog_triangle_never_wraps (phase inc : UInt32) (sync : UInt8) :
    (Analog.triangle phase inc sync).out.toInt =
      (Analog.triangleHalf ((if sync != 0 then 0 else phase) + (inc >>> 1))).toInt +
      (Analog.triangleHalf ((if sync != 0 then 0 else phase) + (inc >>> 1) + (inc >>> 1))).toInt := by
  have first := analog_triangle_half_range ((if sync != 0 then 0 else phase) + (inc >>> 1))
  have second := analog_triangle_half_range ((if sync != 0 then 0 else phase) + (inc >>> 1) + (inc >>> 1))
  unfold Analog.triangle
  dsimp only
  generalize Analog.triangleHalf ((if sync != 0 then 0 else phase) + (inc >>> 1)) = a at first ⊢
  generalize Analog.triangleHalf ((if sync != 0 then 0 else phase) + (inc >>> 1) + (inc >>> 1)) = b at second ⊢
  rw [Int32.toInt_toInt16, Int32.toInt_add]
  simp [Int.bmod_def]
  omega

/-- The sine at any phase lies between the two table entries it blends, as long as neighbouring entries are
at most 32767 apart (the sine table's neighbours differ by at most about 800).
Why it matters: the sine, and everything FM-modulated through it, can never put out more than the table
holds; the cut to 16 bits in `Analog.sineAt` never changes a value. -/
theorem analog_sine_between_entries (phase : UInt32)
    (near : -32767 ≤ (Analog.sineTable (Analog.tableIndex phase + 1)).toInt -
        (Analog.sineTable (Analog.tableIndex phase)).toInt ∧
      (Analog.sineTable (Analog.tableIndex phase + 1)).toInt -
        (Analog.sineTable (Analog.tableIndex phase)).toInt ≤ 32767) :
    min (Analog.sineTable (Analog.tableIndex phase)).toInt
        (Analog.sineTable (Analog.tableIndex phase + 1)).toInt ≤ (Analog.sineAt phase).toInt ∧
      (Analog.sineAt phase).toInt ≤
        max (Analog.sineTable (Analog.tableIndex phase)).toInt
          (Analog.sineTable (Analog.tableIndex phase + 1)).toInt := by
  unfold Analog.sineAt
  dsimp only
  generalize (Analog.sineTable (Analog.tableIndex phase)) = x at *
  generalize (Analog.sineTable (Analog.tableIndex phase + 1)) = y at *
  have hx := Int16.toInt_lt x
  have hx' := Int16.le_iff_toInt_le.mp (Int16.minValue_le x)
  have hy := Int16.toInt_lt y
  have hy' := Int16.le_iff_toInt_le.mp (Int16.minValue_le y)
  rw [Int16.toInt_minValue] at hx' hy'
  have := blend_sixteen_between x.toInt32 y.toInt32 (phase >>> 8) (by simp; omega) (by simp; omega)
    (by simp; omega)
  simpa using this
