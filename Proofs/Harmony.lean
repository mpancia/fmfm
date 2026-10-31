import Firmware.Harmony

/-- Checked for every scale, key, chord root and follow mode: the mask is never empty and fits in 12 bits. -/
private theorem harmony_every_mask_ok :
    ∀ scale, scale < 14 → ∀ key, key < 12 → ∀ root, root < 12 → ∀ follow, follow < 3 →
      Harmony.laneMask scale key root follow ≠ 0 ∧ Harmony.laneMask scale key root follow < 4096 := by
  decide +kernel

/-- Checked likewise: with triad follow, every note of the chord is a note of the turned scale. -/
private theorem harmony_every_triad_inside :
    ∀ scale, scale < 14 → ∀ key, key < 12 → ∀ root, root < 12 →
      Harmony.laneMask scale key root 2 &&& Harmony.laneMask scale key root 1 =
        Harmony.laneMask scale key root 2 := by
  decide +kernel

/-- The mask handed to a lane always has at least one note and fits in 12 bits, for every scale, key, chord
and follow mode the firmware offers.
Why it matters: `lane_note_in_scale` needs a non-empty 12-bit scale; this is what makes that promise hold for
the chord-following lanes too, so a chord change can never leave a lane with nothing to play. -/
theorem harmony_mask_never_empty (scale key root follow : UInt32) :
    (harmonyMask scale key root follow).toNat ≠ 0 ∧ (harmonyMask scale key root follow).toNat < 4096 := by
  unfold harmonyMask
  have ⟨ne, small⟩ := harmony_every_mask_ok (scale.toNat % 14) (Nat.mod_lt _ (by decide)) (key.toNat % 12)
    (Nat.mod_lt _ (by decide)) (root.toNat % 12) (Nat.mod_lt _ (by decide)) (follow.toNat % 3)
    (Nat.mod_lt _ (by decide))
  generalize Harmony.laneMask (scale.toNat % 14) (key.toNat % 12) (root.toNat % 12) (follow.toNat % 3) = m
    at *
  simp [Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show m < 2 ^ 32 by omega), ne, small]

/-- A chord's notes are always notes of the scale it was taken from.
Why it matters: TRIAD follow narrows a lane to the chord; it can never add a note that is outside the key. -/
theorem harmony_triad_within_scale (scale key root : UInt32) :
    (harmonyMask scale key root 2).toNat &&& (harmonyMask scale key root 1).toNat =
      (harmonyMask scale key root 2).toNat := by
  unfold harmonyMask
  have ⟨_, s2⟩ := harmony_every_mask_ok (scale.toNat % 14) (Nat.mod_lt _ (by decide)) (key.toNat % 12)
    (Nat.mod_lt _ (by decide)) (root.toNat % 12) (Nat.mod_lt _ (by decide)) 2 (by decide)
  have ⟨_, s1⟩ := harmony_every_mask_ok (scale.toNat % 14) (Nat.mod_lt _ (by decide)) (key.toNat % 12)
    (Nat.mod_lt _ (by decide)) (root.toNat % 12) (Nat.mod_lt _ (by decide)) 1 (by decide)
  have inside := harmony_every_triad_inside (scale.toNat % 14) (Nat.mod_lt _ (by decide)) (key.toNat % 12)
    (Nat.mod_lt _ (by decide)) (root.toNat % 12) (Nat.mod_lt _ (by decide))
  simp only [show (2 : UInt32).toNat % 3 = 2 from rfl, show (1 : UInt32).toNat % 3 = 1 from rfl]
  generalize Harmony.laneMask (scale.toNat % 14) (key.toNat % 12) (root.toNat % 12) 2 = a at *
  generalize Harmony.laneMask (scale.toNat % 14) (key.toNat % 12) (root.toNat % 12) 1 = b at *
  simp [Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show b < 2 ^ 32 by omega), inside]
