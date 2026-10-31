import Spec.Euclid

/-- The running total `step * hits / steps` goes up by 0 or 1 each step when `hits ≤ steps`. -/
private theorem euclid_total_steps_by_at_most_one (hits steps step : Nat) (positive : 0 < steps)
    (fits : hits ≤ steps) :
    step * hits / steps ≤ (step + 1) * hits / steps ∧
      (step + 1) * hits / steps ≤ step * hits / steps + 1 := by
  constructor
  · exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_succ _))
  · calc (step + 1) * hits / steps = (step * hits + hits) / steps := by rw [Nat.succ_mul]
      _ ≤ (step * hits + steps) / steps := Nat.div_le_div_right (by omega)
      _ = step * hits / steps + 1 := by rw [Nat.add_div_right _ positive]

/-- After `upTo` steps the hit count equals the running total `upTo * hits / steps`. -/
private theorem euclid_count_is_total (hits steps : Nat) (positive : 0 < steps) (fits : hits ≤ steps) :
    ∀ upTo, Euclid.countHits hits steps upTo = upTo * hits / steps := by
  intro upTo
  induction upTo with
  | zero => simp [Euclid.countHits]
  | succ upTo ih =>
    have ⟨low, high⟩ := euclid_total_steps_by_at_most_one hits steps upTo positive fits
    unfold Euclid.countHits Euclid.hit
    rw [ih]
    by_cases same : (upTo + 1) * hits / steps = upTo * hits / steps
    · simp [same]
    · simp only [bne_iff_ne, ne_eq, same, not_false_eq_true, ite_true]
      omega

/-- A bar of `steps` steps with `hits` hits (`hits ≤ steps`) plays exactly `hits` notes.
Why it matters: the pattern has the density you asked for, with no missing or extra notes. -/
theorem euclid_hit_count (hits steps : Nat) (positive : 0 < steps) (fits : hits ≤ steps) :
    Euclid.countHits hits steps steps = hits := by
  rw [euclid_count_is_total hits steps positive fits, Nat.mul_comm, Nat.mul_div_cancel _ positive]
