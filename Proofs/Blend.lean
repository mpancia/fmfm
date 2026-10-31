import Firmware.Analog

/-!
The two blends every table read and crossfade is built from: `Interpolate88` (8-bit fraction) and
`Interpolate824` (16-bit fraction). Both land between the two values they blend.
-/

/-- An `Int32` shifted right 8 places is its value divided by 256, rounded down. -/
private theorem blend_shift_eight (s : Int32) : (s >>> 8).toInt = s.toInt / 256 := by
  have : (s >>> 8).toInt = s.toInt >>> 8 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (8 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- An `Int32` shifted right 16 places is its value divided by 65536, rounded down. -/
private theorem blend_shift_sixteen (s : Int32) : (s >>> 16).toInt = s.toInt / 65536 := by
  have : (s >>> 16).toInt = s.toInt >>> 16 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (16 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- A `UInt32` below 2^31 keeps its value as an `Int32`. -/
private theorem blend_small_toInt32 (x : UInt32) (below : x.toNat < 2 ^ 31) :
    x.toInt32.toInt = (x.toNat : Int) := by
  show x.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt]
  · simp
  · simp at below ⊢; omega

/-- The low byte of a value is at most 255. -/
private theorem blend_and_ff (index : UInt32) : (index &&& 0xFF).toNat ≤ 255 := by
  rw [UInt32.toNat_and]
  have := Nat.and_le_right (n := index.toNat) (m := (0xFF : UInt32).toNat)
  simpa using this

/-- The low 16 bits of a value are at most 65535. -/
private theorem blend_and_ffff (x : UInt32) : (x &&& 0xFFFF).toNat ≤ 65535 := by
  rw [UInt32.toNat_and]
  have := Nat.and_le_right (n := x.toNat) (m := (0xFFFF : UInt32).toNat)
  simpa using this

/-- An `Int32` value in 16-bit range survives the cut to 16 bits. -/
private theorem blend_keep16 (x : Int32) (lo : -32768 ≤ x.toInt) (hi : x.toInt ≤ 32767) :
    x.toInt16.toInt32.toInt = x.toInt := by
  rw [Int16.toInt_toInt32, Int32.toInt_toInt16]
  simp [Int.bmod_def]
  split <;> omega

/-- Moving from `a` toward `b` by `t` parts in `N` (`0 ≤ t ≤ N`) lands between the two. -/
private theorem blend_between (a b t N : Int) (pos : 0 < N) (ht : 0 ≤ t ∧ t ≤ N) :
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

/-- Blending two 16-bit entries by an 8-bit fraction (`Interpolate88`, `Analog.blend88`) lands between the
two.
Why it matters: a wave shaper can never put out more than its table holds, whatever the index; its output is
16-bit without relying on the cut. -/
theorem blend_eight_between (a b : Int32) (index : UInt32)
    (ha : -32768 ≤ a.toInt ∧ a.toInt ≤ 32767) (hb : -32768 ≤ b.toInt ∧ b.toInt ≤ 32767) :
    min a.toInt b.toInt ≤ (Analog.blend88 a b index).toInt ∧
      (Analog.blend88 a b index).toInt ≤ max a.toInt b.toInt := by
  unfold Analog.blend88
  have f := blend_and_ff index
  have t : (index &&& 0xFF).toInt32.toInt = ((index &&& 0xFF).toNat : Int) := blend_small_toInt32 _ (by omega)
  have d : (b - a).toInt = b.toInt - a.toInt := by
    rw [Int32.toInt_sub]; simp [Int.bmod_def]; split <;> omega
  have p : ((b - a) * (index &&& 0xFF).toInt32).toInt =
      (b.toInt - a.toInt) * ((index &&& 0xFF).toNat : Int) := by
    rw [Int32.toInt_mul, d, t]
    have nonneg : (0 : Int) ≤ (index &&& 0xFF).toNat := by omega
    have := Int.mul_le_mul_of_nonneg_right (by omega : b.toInt - a.toInt ≤ 65535) nonneg
    have := Int.mul_le_mul_of_nonneg_right (by omega : -65535 ≤ b.toInt - a.toInt) nonneg
    generalize (b.toInt - a.toInt) * ((index &&& 0xFF).toNat : Int) = q at *
    simp only [Int.bmod_def]
    split <;> omega
  have bt := blend_between a.toInt b.toInt ((index &&& 0xFF).toNat : Int) 256 (by decide) (by omega)
  have inner : (a + (((b - a) * (index &&& 0xFF).toInt32) >>> 8)).toInt =
      a.toInt + (b.toInt - a.toInt) * ((index &&& 0xFF).toNat : Int) / 256 := by
    rw [Int32.toInt_add, blend_shift_eight, p]
    generalize (b.toInt - a.toInt) * ((index &&& 0xFF).toNat : Int) / 256 = q at *
    simp [Int.bmod_def]
    split <;> omega
  rw [blend_keep16 _ (by omega) (by omega), inner]
  exact bt
/-- Blending two 16-bit values by a 16-bit fraction (`Interpolate824`) lands between them, for any two values.
The product inside can wrap in 32 bits (Braids' own C++ does so for steep comb and wave tables), but the wrap is
a multiple of 2^16 and the cut to 16 bits cancels it exactly, so the result is the intended value.
Why it matters: this is the blend inside every table read and every wave crossfade; the result can never
exceed what it blends, and the overflow in the original is proved harmless rather than assumed. -/
theorem blend_sixteen_between (a b : Int32) (frac : UInt32)
    (ha : -32768 ≤ a.toInt ∧ a.toInt ≤ 32767) (hb : -32768 ≤ b.toInt ∧ b.toInt ≤ 32767) :
    min a.toInt b.toInt ≤ (a + (((b - a) * (frac &&& 0xFFFF).toInt32) >>> 16)).toInt16.toInt32.toInt ∧
      (a + (((b - a) * (frac &&& 0xFFFF).toInt32) >>> 16)).toInt16.toInt32.toInt ≤ max a.toInt b.toInt := by
  have f := blend_and_ffff frac
  have t : (frac &&& 0xFFFF).toInt32.toInt = ((frac &&& 0xFFFF).toNat : Int) :=
    blend_small_toInt32 _ (by omega)
  have d : (b - a).toInt = b.toInt - a.toInt := by
    rw [Int32.toInt_sub]; simp [Int.bmod_def]; split <;> omega
  have bt := blend_between a.toInt b.toInt ((frac &&& 0xFFFF).toNat : Int) 65536 (by decide) (by omega)
  rw [Int16.toInt_toInt32, Int32.toInt_toInt16, Int32.toInt_add, blend_shift_sixteen, Int32.toInt_mul, d, t]
  generalize (b.toInt - a.toInt) * ((frac &&& 0xFFFF).toNat : Int) = P at *
  simp only [Int.bmod_def]
  split <;> split <;> split <;> omega
