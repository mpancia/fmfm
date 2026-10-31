import Spec.Divider

/-- Starting from count `count`, `ticks` clock ticks give `(count + ticks) / div` pulses. -/
private theorem divider_pulses_from (div : Nat) (positive : 0 < div) :
    ∀ ticks count, count < div → (Divider.run div count ticks).2 = (count + ticks) / div := by
  intro ticks
  induction ticks with
  | zero => intro count below; simp [Divider.run, Nat.div_eq_of_lt below]
  | succ ticks ih =>
    intro count below
    unfold Divider.run Divider.tick
    by_cases wrap : count + 1 ≥ div
    · have : count + 1 = div := by omega
      simp only [wrap, ite_true]
      rw [ih 0 positive]
      have : (count + (ticks + 1)) / div = (0 + ticks) / div + 1 := by
        rw [show count + (ticks + 1) = ticks + div by omega, Nat.add_div_right _ positive, Nat.zero_add]
      simp [this]
    · simp only [wrap, ite_false]
      rw [ih (count + 1) (by omega)]
      simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      congr 1; omega

/-- A divide-by-`div` counter that starts at 0 and gets `ticks` ticks gives exactly `ticks / div` pulses.
Why it matters: a divide-by-4 clock never drops or doubles a beat, however long it runs. -/
theorem divider_pulse_count (div ticks : Nat) (positive : 0 < div) :
    (Divider.run div 0 ticks).2 = ticks / div := by
  rw [divider_pulses_from div positive ticks 0 positive]; simp

/-- The count never reaches `div`: it always stays between 0 and `div - 1`.
Why it matters: the counter is a small number for good, so it can never grow into a big number the chip's
Lean runtime cannot handle. -/
theorem divider_count_bounded (div ticks count : Nat) (below : count < div) :
    (Divider.run div count ticks).1 < div := by
  induction ticks generalizing count with
  | zero => simpa [Divider.run] using below
  | succ ticks ih =>
    unfold Divider.run Divider.tick
    by_cases wrap : count + 1 ≥ div
    · simp only [wrap, ite_true]; exact ih 0 (by omega)
    · simp only [wrap, ite_false]; exact ih (count + 1) (by omega)
