import Firmware.Rhythm
import Proofs.Euclid

/-- Setting bits below `width` (at most 32) keeps a row below `2 ^ width`. -/
private theorem rhythm_fold_fits (width : Nat) (small : width ≤ 32) (f : Nat → Bool) : ∀ (l : List Nat) (acc : UInt32),
    (∀ i ∈ l, i < width) → acc.toNat < 2 ^ width →
    (l.foldl (fun acc i => if f i then acc ||| (1 <<< i.toUInt32) else acc) acc).toNat < 2 ^ width := by
  intro l
  induction l with
  | nil => intro acc _ h; simpa using h
  | cons i rest ih =>
    intro acc below h
    simp only [List.foldl_cons]
    apply ih
    · intro j mem; exact below j (List.mem_cons_of_mem _ mem)
    · split
      · rw [UInt32.toNat_or]
        apply Nat.or_lt_two_pow h
        have lt : i < 32 := by have := below i (List.mem_cons_self); omega
        rw [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]
        have one : UInt32.toNat 1 = 1 := by decide
        have small : i.toUInt32.toNat % 32 = i := by simp; omega
        rw [one, Nat.one_mul, small, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) lt)]
        exact Nat.pow_lt_pow_right (by decide) (below i (List.mem_cons_self))
      · exact h

/-- One generation of the automaton stays inside the bar: the new row has no bit at or beyond `steps` (a bar
has at most 32 steps).
Why it matters: the row is a `steps`-bit pattern however long the automaton runs; a hit can never appear on a
step that does not exist, and the row stays the size the circle draws. -/
theorem rhythm_automaton_row_fits (rule steps : Nat) (row : UInt32) (small : steps ≤ 32) :
    (Automaton.step rule steps row).toNat < 2 ^ steps := by
  unfold Automaton.step
  apply rhythm_fold_fits steps small
  · intro i mem; exact List.mem_range.mp mem
  · exact Nat.two_pow_pos steps

/-- An accent only falls on a hit.
Why it matters: accents shape the rhythm's hits; they can never add a note where the pattern has a rest. -/
theorem rhythm_accent_only_on_hit (r : Rhythm) (hits steps step : Nat)
    (accented : Rhythm.accent r hits steps step = true) : Rhythm.hit r hits steps step = true := by
  unfold Rhythm.accent at accented
  simp only [Bool.and_eq_true] at accented
  exact accented.1.2
