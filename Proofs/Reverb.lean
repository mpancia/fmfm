import Firmware.Reverb

/-- `min t 100` is at most 100. -/
private theorem reverb_clamped_setting (t : UInt32) : (min t 100).toNat ≤ 100 := by
  rw [UInt32.min_def]; split <;> simp_all [UInt32.le_iff_toNat_le]

/-- The loop gain as a plain number. -/
private theorem reverb_time_gain_value (t : UInt32) :
    (11469 + 20644 * min t 100 / 100 : UInt32).toNat = 11469 + 20644 * (min t 100).toNat / 100 := by
  have := reverb_clamped_setting t
  have h1 : 20644 * (min t 100).toNat < 4294967296 := by omega
  simp only [UInt32.toNat_add, UInt32.toNat_div, UInt32.toNat_mul, UInt32.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 20644 % 4294967296 * (min t 100).toNat < 4294967296)]
  simp only [Nat.reducePow, Nat.reduceMod]
  omega

/-- The low-pass amount as a plain number. -/
private theorem reverb_bright_gain_value (t : UInt32) :
    (19661 + 12124 * min t 100 / 100 : UInt32).toNat = 19661 + 12124 * (min t 100).toNat / 100 := by
  have := reverb_clamped_setting t
  have h1 : 12124 * (min t 100).toNat < 4294967296 := by omega
  simp only [UInt32.toNat_add, UInt32.toNat_div, UInt32.toNat_mul, UInt32.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 12124 % 4294967296 * (min t 100).toNat < 4294967296)]
  simp only [Nat.reducePow, Nat.reduceMod]
  omega

/-- A number below 2^31 keeps its value when read as a signed 32-bit number. -/
private theorem reverb_small_stays (x : UInt32) (h : x.toNat < 2 ^ 31) : x.toInt32.toInt = x.toNat := by
  have same : x.toNat = x.toBitVec.toNat := rfl
  have small : 2 * x.toBitVec.toNat < 2 ^ 32 := by omega
  rw [Int32.toInt, UInt32.toBitVec_toInt32, BitVec.toInt_eq_toNat_cond]
  simp only [small, ↓reduceIte, same]

/-- A sample position is always inside the shared delay memory, whatever the write position, line start
and offset.
Why it matters: a read or write can never land outside the memory, so no setting of a knob can crash the
reverb. -/
theorem reverb_position_in_ring (write base offset : UInt32) :
    (Reverb.pos write base offset).toNat < 32768 := by
  unfold Reverb.pos
  rw [UInt32.toNat_and]
  have : (32767 : UInt32).toNat = 32767 := rfl
  rw [this]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by omega)

/-- At every scale up to 400 (353 is the shipped one), each delay line ends inside the memory, and each
line starts
one sample after the previous one ends.
Why it matters: the ten lines never overlap, so one line cannot overwrite another, and none runs off the
end. -/
theorem reverb_lines_fit_and_do_not_overlap (scale : UInt32) (small : scale.toNat ≤ 400) (line : UInt32)
    (exists_ : line.toNat < 10) :
    (Reverb.start scale line).toNat + (Reverb.length scale line).toNat < 32768 ∧
      (line.toNat < 9 → (Reverb.start scale (line + 1)).toNat =
        (Reverb.start scale line).toNat + (Reverb.length scale line).toNat + 1) := by
  have table : ∀ (s : Fin 401) (l : Fin 10),
      let at_ := s.val.toUInt32; let line := l.val.toUInt32
      (Reverb.start at_ line).toNat + (Reverb.length at_ line).toNat < 32768 ∧
      (l.val < 9 → (Reverb.start at_ (line + 1)).toNat =
        (Reverb.start at_ line).toNat + (Reverb.length at_ line).toNat + 1) := by
    decide +kernel
  have := table ⟨scale.toNat, by omega⟩ ⟨line.toNat, exists_⟩
  simpa using this

/-- For every decay-time setting, the loop gain is positive and below 1.0 (at most 0.98), and for every
brightness
setting the low-pass amount is too (at most 0.97).
Why it matters: the tail always dies away; no knob position makes the reverb feed back on itself and grow.
This is
about the gain settings, not a proof that the whole network is stable. -/
theorem reverb_gains_below_one (setting : UInt32) :
    0 < (Reverb.timeGain setting).toInt ∧ (Reverb.timeGain setting).toInt < 32768 ∧
      0 < (Reverb.brightGain setting).toInt ∧ (Reverb.brightGain setting).toInt < 32768 := by
  have m := reverb_clamped_setting setting
  have t := reverb_time_gain_value setting
  have b := reverb_bright_gain_value setting
  unfold Reverb.timeGain Reverb.brightGain
  rw [reverb_small_stays _ (by omega), reverb_small_stays _ (by omega), t, b]
  omega

/-- The signal stored in the delay memory is the signal divided by 8, rounded towards zero, and it
saturates at the
ends of the 16-bit range instead of wrapping around: from 262144 up it stores 32767, from -262152 down it
stores
-32768, and in between it is within 7 of the signal (times 8).
Why it matters: a loud signal in the loops clips like an overdriven analogue stage; it never wraps to the
opposite
sign, which is the harsh noise a digital reverb is known for. -/
theorem reverb_compress_saturates (signal : Int32) :
    (262144 ≤ signal.toInt → (Reverb.compress signal).toInt = 32767) ∧
    (signal.toInt ≤ -262152 → (Reverb.compress signal).toInt = -32768) ∧
    (-262152 < signal.toInt → signal.toInt < 262144 →
      (Reverb.compress signal).toInt * 8 ≤ signal.toInt + 7 ∧
        signal.toInt ≤ (Reverb.compress signal).toInt * 8 + 7) := by
  have tdiv : ∀ a : Int, a.tdiv 8 = if 0 ≤ a then a / 8 else -((-a) / 8) := by
    intro a
    rw [Int.tdiv_eq_ediv]
    split <;> split <;> simp [Int.sign] <;> omega
  have stored : (signal / 8).toInt = signal.toInt.tdiv 8 := by
    rw [Int32.toInt_div_of_ne_right]; · rfl
    decide
  have hd := stored
  have hlt := Int32.toInt_lt signal
  have hge := Int32.le_toInt signal
  unfold Reverb.compress
  dsimp only
  have c1 : (32767 : Int32).toInt = 32767 := by decide
  have c2 : (-32768 : Int32).toInt = -32768 := by decide
  have above : (signal / 8 > 32767) ↔ (32767 < (signal / 8).toInt) := by
    show (32767 < signal / 8) ↔ _
    rw [Int32.lt_iff_toInt_lt, c1]
  have below : (signal / 8 < -32768) ↔ ((signal / 8).toInt < -32768) := by
    rw [Int32.lt_iff_toInt_lt, c2]
  rw [tdiv] at hd
  by_cases h1 : signal / 8 > 32767
  · have := above.mp h1
    simp only [h1, ite_true]
    exact ⟨fun _ => by decide, fun h => by split at hd <;> omega, fun a b => by split at hd <;> omega⟩
  · by_cases h2 : signal / 8 < -32768
    · have := below.mp h2
      simp only [h1, h2, ite_true, ite_false]
      exact ⟨fun h => by split at hd <;> omega, fun _ => by decide, fun a b => by split at hd <;> omega⟩
    · have a := mt above.mpr h1
      have b := mt below.mpr h2
      simp only [h1, h2, ite_false]
      have within := Int32.toInt_toInt16 (signal / 8)
      rw [Int.bmod] at within
      refine ⟨fun h => by omega, fun h => by omega, fun l u => ?_⟩
      rw [within]
      have a' : (signal / 8).toInt ≤ 32767 := by omega
      have b' : -32768 ≤ (signal / 8).toInt := by omega
      split at hd <;> split <;> omega
