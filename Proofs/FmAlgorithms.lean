import Spec.Fm

/-!
The algorithms and shapes use the whole voice: in every algorithm every operator is either heard or
modulates another, the eight algorithms are eight different routings, and in every shape every operator is
either heard or pushes something with a nonzero depth.
-/

/-- `Fm.modulates` only looks at `alg % 8`, so it is the same at `alg` and at `alg % 8`. -/
private theorem modulates_mod (alg op source : UInt32) :
    Fm.modulates alg op source = Fm.modulates (alg % 8) op source := by
  have h : alg % 8 % 8 = alg % 8 := by
    rw [← UInt32.toNat_inj]
    simp
  unfold Fm.modulates
  rw [h]

/-- `Fm.carries` only looks at `alg % 8`, so it is the same at `alg` and at `alg % 8`. -/
private theorem carries_mod (alg op : UInt32) : Fm.carries alg op = Fm.carries (alg % 8) op := by
  have h : alg % 8 % 8 = alg % 8 := by
    rw [← UInt32.toNat_inj]
    simp
  unfold Fm.carries
  rw [h]

/-- The eight residues of `alg % 8`, as `UInt32` equations. -/
private theorem alg_mod_cases (alg : UInt32) :
    alg % 8 = 0 ∨ alg % 8 = 1 ∨ alg % 8 = 2 ∨ alg % 8 = 3 ∨ alg % 8 = 4 ∨ alg % 8 = 5 ∨
      alg % 8 = 6 ∨ alg % 8 = 7 := by
  have h8 := Nat.mod_lt alg.toNat (by decide : 0 < 8)
  simp only [← UInt32.toNat_inj]; simp; omega

/-- The idle-operator statement, checked over the eight algorithms by the kernel. -/
private theorem no_idle_fin : ∀ a : Fin 8, ∀ op : Fin 4,
    Fm.carries a.val.toUInt32 (op.val + 1).toUInt32 = true ∨
      ∃ target : Fin 4,
        Fm.modulates a.val.toUInt32 (target.val + 1).toUInt32 (op.val + 1).toUInt32 = true := by
  decide +kernel

/-- In every algorithm every operator either carries or modulates some operator; none of the four is wired
to nothing.
Why it matters: an operator that neither sounds nor modulates would be a quarter of the voice computed
every sample for nothing. -/
theorem fm_no_operator_idle (alg : UInt32) (op : Fin 4) :
    Fm.carries alg (op.val + 1).toUInt32 = true ∨
      ∃ target : Fin 4, Fm.modulates alg (target.val + 1).toUInt32 (op.val + 1).toUInt32 = true := by
  have hc := carries_mod alg
  have hm := modulates_mod alg
  rcases alg_mod_cases alg with h | h | h | h | h | h | h | h <;> rw [h] at hc hm <;> rw [hc] <;>
    simp only [hm]
  · exact no_idle_fin ⟨0, by decide⟩ op
  · exact no_idle_fin ⟨1, by decide⟩ op
  · exact no_idle_fin ⟨2, by decide⟩ op
  · exact no_idle_fin ⟨3, by decide⟩ op
  · exact no_idle_fin ⟨4, by decide⟩ op
  · exact no_idle_fin ⟨5, by decide⟩ op
  · exact no_idle_fin ⟨6, by decide⟩ op
  · exact no_idle_fin ⟨7, by decide⟩ op

/-- The eight algorithms are pairwise different: any two differ in some modulation link or in which
operators carry.
Why it matters: no two positions of the algorithm knob wire the operators the same way. -/
theorem fm_algorithms_distinct : ∀ a b : Fin 8, a ≠ b → ∃ op src : Fin 4,
    Fm.modulates a.val.toUInt32 (op.val + 1).toUInt32 (src.val + 1).toUInt32 ≠
        Fm.modulates b.val.toUInt32 (op.val + 1).toUInt32 (src.val + 1).toUInt32 ∨
      Fm.carries a.val.toUInt32 (op.val + 1).toUInt32 ≠ Fm.carries b.val.toUInt32 (op.val + 1).toUInt32 := by
  decide +kernel

/-- In every shape every operator is either a carrier of the shape's algorithm or has nonzero depth and
modulates some operator in it; no shape has a silent modulator.
Why it matters: a modulator with depth zero would run its sine and envelope every sample for nothing. -/
theorem fm_every_shape_uses_four_operators (shape : Fin 8) : ∀ op : Fin 4,
    Fm.carries (Fm.algorithm shape.val.toUInt32) (op.val + 1).toUInt32 = true ∨
      (0 < (Fm.depth shape.val.toUInt32 (op.val + 1).toUInt32).toNat ∧
        ∃ target : Fin 4,
          Fm.modulates (Fm.algorithm shape.val.toUInt32) (target.val + 1).toUInt32
            (op.val + 1).toUInt32 = true) := by
  revert shape
  decide +kernel
