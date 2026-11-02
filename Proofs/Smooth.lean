import Spec.Smooth

/-!
What the block smoothing promises: a smoothed parameter stays between the old and the new value and ends next
to the new one, and a smoothed phase step never overshoots its target and ends at most `size` below it.
-/

/-- An `Int32` shifted right 15 places is its value divided by 32768, rounded down. -/
private theorem smooth_shift_fifteen (s : Int32) : (s >>> 15).toInt = s.toInt / 32768 := by
  have : (s >>> 15).toInt = s.toInt >>> 15 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (15 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- The smoothed parameter, as the exact integer it stands for: nothing inside wraps. -/
private theorem smooth_parameter_exact (start target xfade : Int32)
    (startInRange : 0 ≤ start.toInt ∧ start.toInt ≤ 32767)
    (targetInRange : 0 ≤ target.toInt ∧ target.toInt ≤ 32767)
    (xfadeInRange : 0 ≤ xfade.toInt ∧ xfade.toInt ≤ 32767) :
    (Smooth.parameter start target xfade).toInt =
      start.toInt + (target.toInt - start.toInt) * xfade.toInt / 32768 := by
  unfold Smooth.parameter
  have change : (target - start).toInt = target.toInt - start.toInt := by
    rw [Int32.toInt_sub]; simp [Int.bmod_def]; split <;> omega
  have upper := Int.mul_le_mul_of_nonneg_right (by omega : target.toInt - start.toInt ≤ 32767) xfadeInRange.1
  have lower := Int.mul_le_mul_of_nonneg_right (by omega : -32767 ≤ target.toInt - start.toInt) xfadeInRange.1
  have product : ((target - start) * xfade).toInt = (target.toInt - start.toInt) * xfade.toInt := by
    rw [Int32.toInt_mul, change]
    generalize (target.toInt - start.toInt) * xfade.toInt = q at *
    simp only [Int.bmod_def]
    split <;> omega
  rw [Int32.toInt_add, smooth_shift_fifteen, product]
  generalize (target.toInt - start.toInt) * xfade.toInt = p at *
  simp [Int.bmod_def]
  split <;> omega

/-- Moving from `a` toward `b` by `t` parts in 32768 (`0 ≤ t ≤ 32767`) lands between the two. -/
private theorem smooth_between (a b t : Int) (ht : 0 ≤ t ∧ t ≤ 32767) :
    min a b ≤ a + (b - a) * t / 32768 ∧ a + (b - a) * t / 32768 ≤ max a b := by
  by_cases h : 0 ≤ b - a
  · have u : (b - a) * t ≤ (b - a) * 32768 := Int.mul_le_mul_of_nonneg_left (by omega) h
    have l : 0 ≤ (b - a) * t := Int.mul_nonneg h ht.1
    generalize (b - a) * t = q at *
    omega
  · have neg : b - a ≤ 0 := by omega
    have l : (b - a) * 32768 ≤ (b - a) * t := Int.mul_le_mul_of_nonpos_left neg (by omega)
    have u : (b - a) * t ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg neg ht.1
    generalize (b - a) * t = q at *
    omega

/-- A smoothed parameter lies between `start` and `target`, for parameters 0 to 32767 (Braids' range) and any
crossfade position 0 to 32767, and nothing in the arithmetic wraps.
Why it matters: a moving knob glides the timbre between the two settings without overshoot or a wrapped
jump. -/
theorem smooth_parameter_between (start target xfade : Int32)
    (startInRange : 0 ≤ start.toInt ∧ start.toInt ≤ 32767)
    (targetInRange : 0 ≤ target.toInt ∧ target.toInt ≤ 32767)
    (xfadeInRange : 0 ≤ xfade.toInt ∧ xfade.toInt ≤ 32767) :
    min start.toInt target.toInt ≤ (Smooth.parameter start target xfade).toInt ∧
      (Smooth.parameter start target xfade).toInt ≤ max start.toInt target.toInt := by
  rw [smooth_parameter_exact start target xfade startInRange targetInRange xfadeInRange]
  exact smooth_between start.toInt target.toInt xfade.toInt xfadeInRange

/-- A `UInt32` of at most 32767 keeps its value as an `Int32`. -/
private theorem smooth_small_toInt32 (x : UInt32) (small : x.toNat ≤ 32767) :
    x.toInt32.toInt = (x.toNat : Int) := by
  show x.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt]
  · simp
  · simp at small ⊢; omega

/-- The per-sample crossfade step is `32767 / size`, as an integer. -/
private theorem smooth_per_sample_toInt (size : UInt32) (small : size.toNat ≤ 32767) :
    (Smooth.perSample size).toInt = ((32767 / size.toNat : Nat) : Int) := by
  unfold Smooth.perSample
  rw [Int32.toInt_div, smooth_small_toInt32 size small]
  have : (32767 : Int32).toInt = ((32767 : Nat) : Int) := rfl
  rw [this, ← Int.ofNat_tdiv]
  have := Nat.div_le_self 32767 size.toNat
  generalize (32767 / size.toNat : Nat) = q at *
  simp only [Int.bmod_def]
  split <;> omega

/-- After `k ≤ size` samples the crossfade is exactly `k` steps along, with no wrap. -/
private theorem smooth_crossfade_exact (size : UInt32) (small : size.toNat ≤ 32767) (k : Nat)
    (within : k ≤ size.toNat) :
    (Smooth.crossfadeAfter size k).toInt = ((k * (32767 / size.toNat) : Nat) : Int) := by
  induction k with
  | zero => simp [Smooth.crossfadeAfter]
  | succ k ih =>
    have step := smooth_per_sample_toInt size small
    have sofar := ih (by omega)
    have fits : size.toNat * (32767 / size.toNat) ≤ 32767 := Nat.mul_div_le 32767 size.toNat
    have below : (k + 1) * (32767 / size.toNat) ≤ size.toNat * (32767 / size.toNat) :=
      Nat.mul_le_mul_right _ within
    have split_k : (k + 1) * (32767 / size.toNat) = k * (32767 / size.toNat) + 32767 / size.toNat :=
      Nat.succ_mul k _
    simp only [Smooth.crossfadeAfter, Smooth.advance]
    rw [Int32.toInt_add, sofar, step]
    simp only [Int.bmod_def]
    split <;> omega

/-- When the block ends, the smoothed parameter is within `size` of its target: the last crossfade position
is `32767 - 32767 % size` rather than 32768, so it stops just short. Blocks on the FM-1 are 16 samples, so
the parameter ends within 16 of its target on a scale of 32768.
Why it matters: the step from the end of one block to the start of the next is at most `size`, so block
boundaries are inaudible. -/
theorem smooth_parameter_reaches_target (start target : Int32) (size : UInt32)
    (startInRange : 0 ≤ start.toInt ∧ start.toInt ≤ 32767)
    (targetInRange : 0 ≤ target.toInt ∧ target.toInt ≤ 32767)
    (notEmpty : 0 < size.toNat) (small : size.toNat ≤ 32767) :
    target.toInt - size.toNat ≤
        (Smooth.parameter start target (Smooth.crossfadeAfter size size.toNat)).toInt ∧
      (Smooth.parameter start target (Smooth.crossfadeAfter size size.toNat)).toInt ≤
        target.toInt + size.toNat := by
  have position := smooth_crossfade_exact size small size.toNat (Nat.le_refl _)
  have fits := Nat.div_add_mod 32767 size.toNat
  have rest := Nat.mod_lt 32767 notEmpty
  rw [smooth_parameter_exact start target _ startInRange targetInRange (by omega), position]
  have changeInRange : -32767 ≤ target.toInt - start.toInt ∧ target.toInt - start.toInt ≤ 32767 := by omega
  generalize changeDef : target.toInt - start.toInt = change at *
  generalize (32767 % size.toNat : Nat) = r at *
  generalize (size.toNat * (32767 / size.toNat) : Nat) = x at *
  have xval : (x : Int) = 32768 - ((r : Int) + 1) := by omega
  have short : change * (x : Int) = -(change * ((r : Int) + 1)) + change * 32768 := by
    rw [xval, Int.mul_sub]; omega
  rw [short, Int.add_mul_ediv_right _ _ (by decide)]
  have hi : change * ((r : Int) + 1) ≤ 32767 * ((r : Int) + 1) :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  have lo : -32767 * ((r : Int) + 1) ≤ change * ((r : Int) + 1) :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  generalize change * ((r : Int) + 1) = d at *
  omega

/-- Rising: after `k ≤ size` samples the phase step is `previous` plus `k` whole steps, with no wrap. -/
private theorem smooth_step_rising (previous target size : UInt32) (rising : previous < target) (k : Nat)
    (within : k ≤ size.toNat) :
    (Smooth.stepAfter previous target size k).toNat =
      previous.toNat + k * ((target.toNat - previous.toNat) / size.toNat) := by
  induction k with
  | zero => simp [Smooth.stepAfter]
  | succ k ih =>
    have sofar := ih (by omega)
    have fits : size.toNat * ((target.toNat - previous.toNat) / size.toNat) ≤ target.toNat - previous.toNat :=
      Nat.mul_div_le _ _
    have below : (k + 1) * ((target.toNat - previous.toNat) / size.toNat) ≤
        size.toNat * ((target.toNat - previous.toNat) / size.toNat) := Nat.mul_le_mul_right _ within
    have split_k : (k + 1) * ((target.toNat - previous.toNat) / size.toNat) =
        k * ((target.toNat - previous.toNat) / size.toNat) + (target.toNat - previous.toNat) / size.toNat :=
      Nat.succ_mul k _
    have order : previous.toNat < target.toNat := UInt32.lt_iff_toNat_lt.mp rising
    have bound := target.toNat_lt
    simp only [Smooth.stepAfter, Smooth.glide, Smooth.stepDelta, rising, ite_true]
    rw [UInt32.toNat_add, sofar, UInt32.toNat_div, UInt32.toNat_sub_of_le _ _ (UInt32.le_of_lt rising)]
    omega

/-- Falling (or level): each sample takes one whole step plus one, so after `k ≤ size` samples the phase step
is `previous` less `k` of those, with no wrap while the target is at least `size`. -/
private theorem smooth_step_falling (previous target size : UInt32) (falling : target ≤ previous)
    (room : size.toNat ≤ target.toNat) (k : Nat) (within : k ≤ size.toNat) :
    (Smooth.stepAfter previous target size k).toNat +
      k * ((previous.toNat - target.toNat) / size.toNat + 1) = previous.toNat := by
  induction k with
  | zero => simp [Smooth.stepAfter]
  | succ k ih =>
    have sofar := ih (by omega)
    have fits : size.toNat * ((previous.toNat - target.toNat) / size.toNat) ≤ previous.toNat - target.toNat :=
      Nat.mul_div_le _ _
    have below : (k + 1) * ((previous.toNat - target.toNat) / size.toNat + 1) ≤
        size.toNat * ((previous.toNat - target.toNat) / size.toNat + 1) := Nat.mul_le_mul_right _ within
    have split_k : (k + 1) * ((previous.toNat - target.toNat) / size.toNat + 1) =
        k * ((previous.toNat - target.toNat) / size.toNat + 1) +
          ((previous.toNat - target.toNat) / size.toNat + 1) := Nat.succ_mul k _
    have split_size : size.toNat * ((previous.toNat - target.toNat) / size.toNat + 1) =
        size.toNat * ((previous.toNat - target.toNat) / size.toNat) + size.toNat := Nat.mul_succ _ _
    have order : target.toNat ≤ previous.toNat := UInt32.le_iff_toNat_le.mp falling
    have notRising : ¬ previous < target := UInt32.not_lt.mpr falling
    have bound := previous.toNat_lt
    simp only [Smooth.stepAfter, Smooth.glide, Smooth.stepDelta, notRising, ite_false]
    rw [UInt32.toNat_add, UInt32.toNat_not, UInt32.toNat_div, UInt32.toNat_sub_of_le _ _ falling]
    simp only [UInt32.size] at *
    omega

/-- While a block smooths the phase step from `previous` to `target`, the step never rises above the larger
of the two nor falls more than `size` below the smaller. Rising, it stays between the two; falling or level,
Braids' `~` moves each sample one more than the exact share, so the step can pass the target by up to `size`.
The target must be at least `size` for the falling case to stay in range.
Why it matters: a pitch glide cannot pass the note by more than 16 units of 2^32 per sample, under a
millionth of a semitone. -/
theorem smooth_step_glide_bound (previous target size : UInt32) (room : size.toNat ≤ target.toNat) (k : Nat)
    (within : k ≤ size.toNat) :
    min previous.toNat target.toNat - size.toNat ≤ (Smooth.stepAfter previous target size k).toNat ∧
      (Smooth.stepAfter previous target size k).toNat ≤ max previous.toNat target.toNat := by
  by_cases rising : previous < target
  · rw [smooth_step_rising previous target size rising k within]
    have fits : size.toNat * ((target.toNat - previous.toNat) / size.toNat) ≤ target.toNat - previous.toNat :=
      Nat.mul_div_le _ _
    have below : k * ((target.toNat - previous.toNat) / size.toNat) ≤
        size.toNat * ((target.toNat - previous.toNat) / size.toNat) := Nat.mul_le_mul_right _ within
    have order : previous.toNat < target.toNat := UInt32.lt_iff_toNat_lt.mp rising
    omega
  · have falling : target ≤ previous := UInt32.not_lt.mp rising
    have exact := smooth_step_falling previous target size falling room k within
    have fits : size.toNat * ((previous.toNat - target.toNat) / size.toNat) ≤ previous.toNat - target.toNat :=
      Nat.mul_div_le _ _
    have below : k * ((previous.toNat - target.toNat) / size.toNat + 1) ≤
        size.toNat * ((previous.toNat - target.toNat) / size.toNat + 1) := Nat.mul_le_mul_right _ within
    have split_size : size.toNat * ((previous.toNat - target.toNat) / size.toNat + 1) =
        size.toNat * ((previous.toNat - target.toNat) / size.toNat) + size.toNat := Nat.mul_succ _ _
    have order : target.toNat ≤ previous.toNat := UInt32.le_iff_toNat_le.mp falling
    omega

/-- When the block ends, the smoothed phase step is at or below its target and within `size` of it: rising,
it lands `(target - previous) % size` short; falling or level, between 1 and `size` below. The target must
be at least `size` for the falling case to stay in range.
Why it matters: after every block the pitch is within 16 units of 2^32 per sample of the note asked for and
never sharp. -/
theorem smooth_step_lands_near_target (previous target size : UInt32) (notEmpty : 0 < size.toNat)
    (room : size.toNat ≤ target.toNat) :
    target.toNat - size.toNat ≤ (Smooth.stepAfter previous target size size.toNat).toNat ∧
      (Smooth.stepAfter previous target size size.toNat).toNat ≤ target.toNat := by
  by_cases rising : previous < target
  · rw [smooth_step_rising previous target size rising size.toNat (Nat.le_refl _)]
    have fits := Nat.div_add_mod (target.toNat - previous.toNat) size.toNat
    have rest := Nat.mod_lt (target.toNat - previous.toNat) notEmpty
    have order : previous.toNat < target.toNat := UInt32.lt_iff_toNat_lt.mp rising
    omega
  · have falling : target ≤ previous := UInt32.not_lt.mp rising
    have exact := smooth_step_falling previous target size falling room size.toNat (Nat.le_refl _)
    have fits := Nat.div_add_mod (previous.toNat - target.toNat) size.toNat
    have rest := Nat.mod_lt (previous.toNat - target.toNat) notEmpty
    have split_size : size.toNat * ((previous.toNat - target.toNat) / size.toNat + 1) =
        size.toNat * ((previous.toNat - target.toNat) / size.toNat) + size.toNat := Nat.mul_succ _ _
    have order : target.toNat ≤ previous.toNat := UInt32.le_iff_toNat_le.mp falling
    omega
