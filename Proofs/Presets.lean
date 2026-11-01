import Spec.Presets

/-- Every factory patch is one the knobs could have produced: all 128 satisfy `Patch.Fits`, every global and
every lane setting in range, checked value by value.
Why it matters: the firmware trusts its own patch table without the checks a loaded slot gets
(`patch_decode_only_fits`); this closes that gap, so no shipped patch can hand a lane a sound index, scale,
step count or note range it would read past a table with. It is also a check on the generator: a patch
written by hand or by a mood table that strays out of range fails the build. -/
theorem presets_all_fit : ∀ p ∈ Presets.all, p.Fits := by
  have checked : Presets.all.all (fun p => decide p.Fits) = true := by decide +kernel
  intro p member
  have := List.all_eq_true.mp checked p member
  exact of_decide_eq_true this
