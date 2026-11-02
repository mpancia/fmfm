import Spec.Presets

/-- All 128 factory patches satisfy `Patch.Fits`, checked value by value.
Why it matters: the firmware trusts its own patch table without the checks a loaded slot gets, and a
generated patch that strays out of range fails the build. -/
theorem presets_all_fit : ∀ p ∈ Presets.all, p.Fits := by
  have checked : Presets.all.all (fun p => decide p.Fits) = true := by decide +kernel
  intro p member
  have := List.all_eq_true.mp checked p member
  exact of_decide_eq_true this
