import Spec.Fm

/-! Symmetry of the sine by polynomial (`Fm.sineAt`): half a cycle on, it is the negative; mirrored about a
quarter, it is the same; so any 256 samples spaced evenly round the cycle sum to zero. -/

/-- The sine as a function of the phase's value: quadrant `p / 2^30`, place `p / 2^15 % 2^15`, mirrored in
the odd quadrants, negated in the upper two. -/
private def sineNat (p : Nat) : Int32 :=
  let y := (Fm.quarter (if p / 1073741824 % 2 = 1 then 32767 - p / 32768 % 32768
    else p / 32768 % 32768).toUInt32).toInt32
  if p / 1073741824 ≥ 2 then -y else y

/-- The quadrant is the phase's value divided by 2^30. -/
private theorem fm_quadrant (phase : UInt32) : (phase >>> 30).toNat = phase.toNat / 1073741824 := by
  rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl

/-- The place in the quarter is the phase's value divided by 2^15, modulo 2^15. -/
private theorem fm_place (phase : UInt32) :
    ((phase >>> 15) &&& 0x7FFF).toNat = phase.toNat / 32768 % 32768 := by
  rw [UInt32.toNat_and, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
    show (0x7FFF : UInt32).toNat = 2 ^ 15 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; rfl

/-- The odd-quadrant test, on the phase's value. -/
private theorem fm_odd_iff (phase : UInt32) :
    ((phase >>> 30) &&& 1 = 1) ↔ phase.toNat / 1073741824 % 2 = 1 := by
  rw [← UInt32.toNat_inj, UInt32.toNat_and, fm_quadrant,
    show (1 : UInt32).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The upper-half test, on the phase's value. -/
private theorem fm_upper_iff (phase : UInt32) : (phase >>> 30 ≥ 2) ↔ phase.toNat / 1073741824 ≥ 2 := by
  show (2 : UInt32) ≤ phase >>> 30 ↔ _
  rw [UInt32.le_iff_toNat_le, fm_quadrant]; rfl

/-- A place taken back to 32 bits is the same number. -/
private theorem fm_place_toUInt32 (phase : UInt32) :
    (phase >>> 15) &&& 0x7FFF = (phase.toNat / 32768 % 32768).toUInt32 := by
  rw [← UInt32.toNat_inj, fm_place, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (show phase.toNat / 32768 % 32768 < 2 ^ 32 by omega)]

/-- The mirror of a place, in 32 bits as in numbers. -/
private theorem fm_mirror_toUInt32 (x : Nat) (inside : x < 32768) :
    (32767 : UInt32) - x.toUInt32 = (32767 - x).toUInt32 := by
  rw [← UInt32.toNat_inj, UInt32.toNat_sub_of_le, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rfl
  · rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; show x ≤ 32767; omega

/-- The sine depends on the phase only through its value, as `sineNat` says. -/
private theorem fm_sine_of_nat (phase : UInt32) : Fm.sineAt phase = sineNat phase.toNat := by
  simp only [Fm.sineAt, Fm.folded, sineNat, fm_place_toUInt32, fm_odd_iff, fm_upper_iff]
  rw [fm_mirror_toUInt32 _ (Nat.mod_lt _ (by decide))]
  by_cases h : phase.toNat / 1073741824 % 2 = 1 <;> simp [h]

/-- Half a cycle on from a value below 2^32, the sine is the negative. -/
private theorem fm_half_wave_nat (p : Nat) (inside : p < 4294967296) :
    sineNat ((p + 2147483648) % 4294967296) = -sineNat p := by
  unfold sineNat
  have odd : (p + 2147483648) % 4294967296 / 1073741824 % 2 = p / 1073741824 % 2 := by omega
  have place : (p + 2147483648) % 4294967296 / 32768 % 32768 = p / 32768 % 32768 := by omega
  have upper : ((p + 2147483648) % 4294967296 / 1073741824 ≥ 2) ↔ ¬ (p / 1073741824 ≥ 2) := by omega
  rw [odd, place]
  by_cases h : p / 1073741824 ≥ 2 <;> simp [upper, h]

/-- Mirrored about the quarter point (value `2^31 - 1 - p`), the sine is the same. -/
private theorem fm_quarter_wave_nat (p : Nat) (inside : p < 4294967296) :
    sineNat ((4294967296 - p + 2147483647) % 4294967296) = sineNat p := by
  unfold sineNat
  have fold : (if (4294967296 - p + 2147483647) % 4294967296 / 1073741824 % 2 = 1 then
        32767 - (4294967296 - p + 2147483647) % 4294967296 / 32768 % 32768
      else (4294967296 - p + 2147483647) % 4294967296 / 32768 % 32768) =
      (if p / 1073741824 % 2 = 1 then 32767 - p / 32768 % 32768 else p / 32768 % 32768) := by
    split <;> split <;> omega
  have upper : ((4294967296 - p + 2147483647) % 4294967296 / 1073741824 ≥ 2) ↔
      (p / 1073741824 ≥ 2) := by omega
  rw [fold]
  simp only [upper]

/-- The sine half a cycle on is the negative of the sine: `sineAt (phase + 2^31) = -sineAt phase` for every
phase (the quadrant moves by two, the place in the quarter is unchanged, the sign flips).
Why it matters: a half-wave-symmetric waveform has no DC and no even harmonics, so the polynomial's error
sits at odd harmonics only. -/
theorem fm_sine_half_wave (phase : UInt32) : Fm.sineAt (phase + 0x80000000) = -Fm.sineAt phase := by
  rw [fm_sine_of_nat, fm_sine_of_nat, UInt32.toNat_add,
    show (0x80000000 : UInt32).toNat = 2147483648 from rfl]
  exact fm_half_wave_nat phase.toNat phase.toNat_lt

/-- The sine is mirrored about the quarter points: `sineAt (0x7FFFFFFF - phase) = sineAt phase` for every
phase. Position `p` (the phase's top 17 bits) pairs with position `65535 - p` (modulo 2^17), so place `x` in
an even quadrant pairs with place `32767 - x` in the odd quadrant above it, which `Fm.folded` reads at the
same `x`. (`0x80000000 - phase` would land one position off: the mirror of position 0 is 65535, not 65536.)
Why it matters: the engine evaluates the polynomial on 0 to 32767 only and reads the other three quarters
by mirror and sign; this symmetry is what makes that exact. -/
theorem fm_sine_quarter_wave (phase : UInt32) : Fm.sineAt (0x7FFFFFFF - phase) = Fm.sineAt phase := by
  rw [fm_sine_of_nat, fm_sine_of_nat, UInt32.toNat_sub,
    show (0x7FFFFFFF : UInt32).toNat = 2147483647 from rfl]
  exact fm_quarter_wave_nat phase.toNat phase.toNat_lt

/-- The quarter polynomial never passes 32767: it is held there. -/
private theorem fm_quarter_le (x : UInt32) : (Fm.quarter x).toNat ≤ 32767 := by
  unfold Fm.quarter
  rw [UInt32.min_def]
  split
  · rename_i h; exact UInt32.le_iff_toNat_le.mp h
  · decide

/-- A 32-bit unsigned number below 2^31 keeps its value as a signed one. -/
private theorem fm_small_toInt32 (u : UInt32) (small : u.toNat < 2 ^ 31) : u.toInt32.toInt = u.toNat := by
  show u.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt]
  · rfl
  · simp; omega

/-- The sine is within 32767 either way. -/
private theorem fm_sine_small (phase : UInt32) : (Fm.sineAt phase).toInt.natAbs ≤ 32767 := by
  simp only [Fm.sineAt]
  have q := fm_quarter_le (Fm.folded phase)
  have v := fm_small_toInt32 (Fm.quarter (Fm.folded phase)) (by omega)
  generalize Fm.quarter (Fm.folded phase) = y at *
  split
  · rw [Int32.toInt_neg, Int.bmod_eq_of_le (by omega) (by omega)]; omega
  · omega

/-- Two samples half a cycle apart cancel exactly: `sineAt p + sineAt (p + 2^31) = 0` as integers for every
phase (the negation cannot wrap, the sine being within 32767).
Why it matters: this is the pairing behind `fm_sine_has_no_dc`. -/
theorem fm_sine_pairs_cancel (phase : UInt32) :
    (Fm.sineAt phase).toInt + (Fm.sineAt (phase + 0x80000000)).toInt = 0 := by
  rw [fm_sine_half_wave, Int32.toInt_neg]
  have := fm_sine_small phase
  rw [Int.bmod_eq_of_le (by omega) (by omega)]
  omega

/-- The sample `k` of a run from `start`, spaced a 256th of a cycle apart. -/
private def sampleAt (start : UInt32) (k : Nat) : Int :=
  (Fm.sineAt (start + k.toUInt32 * 0x01000000)).toInt

/-- The sum of the first `n` samples of the run. -/
private def runSum (start : UInt32) (n : Nat) : Int :=
  (List.range n).foldl (fun acc k => acc + sampleAt start k) 0

/-- One more sample on the run. -/
private theorem fm_run_succ (start : UInt32) (n : Nat) :
    runSum start (n + 1) = runSum start n + sampleAt start n := by
  unfold runSum
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]

/-- Sample `k + 128` is read half a cycle on from sample `k`. -/
private theorem fm_sample_half (start : UInt32) (k : Nat) :
    start + (k + 128).toUInt32 * 0x01000000 = (start + k.toUInt32 * 0x01000000) + 0x80000000 := by
  rw [← UInt32.toNat_inj]
  simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat']
  rw [show (0x01000000 : UInt32).toNat = 16777216 from rfl,
    show (0x80000000 : UInt32).toNat = 2147483648 from rfl]
  omega

/-- The second half of the run cancels the first, sample by sample. -/
private theorem fm_run_pairs (start : UInt32) (m : Nat) :
    runSum start (128 + m) + runSum start m = runSum start 128 := by
  induction m with
  | zero =>
    show runSum start (128 + 0) + runSum start 0 = runSum start 128
    have z : runSum start 0 = 0 := rfl
    rw [Nat.add_zero]; omega
  | succ m ih =>
    rw [show 128 + (m + 1) = (128 + m) + 1 by omega, fm_run_succ, fm_run_succ]
    have pair : sampleAt start m + sampleAt start (128 + m) = 0 := by
      unfold sampleAt
      rw [show 128 + m = m + 128 by omega, fm_sample_half]
      exact fm_sine_pairs_cancel _
    omega

/-- Any 256 samples of the sine spaced a 256th of a cycle apart sum to zero, from any starting phase: sample
`k` and sample `k + 128` are half a cycle apart and cancel (`fm_sine_half_wave`).
Why it matters: a carrier at any pitch and phase adds no DC to the mix over a cycle, and the polynomial's
error has no even harmonics. -/
theorem fm_sine_has_no_dc (start : UInt32) :
    (List.range 256).foldl (fun acc k => acc + (Fm.sineAt (start + k.toUInt32 * 0x01000000)).toInt) 0
      = 0 := by
  have := fm_run_pairs start 128
  simp only [show 128 + 128 = 256 from rfl] at this
  show runSum start 256 = 0
  omega
