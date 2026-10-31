import Firmware.Rhythm
import Proofs.Euclid

/-- Setting bits below `width` keeps a row below `2 ^ width`. -/
private theorem rhythm_fold_fits (width : Nat) (f : Nat → Bool) : ∀ (l : List Nat) (acc : Nat),
    (∀ i ∈ l, i < width) → acc < 2 ^ width →
    l.foldl (fun acc i => if f i then acc ||| (1 <<< i) else acc) acc < 2 ^ width := by
  intro l
  induction l with
  | nil => intro acc _ h; simpa using h
  | cons i rest ih =>
    intro acc below h
    simp only [List.foldl_cons]
    apply ih
    · intro j mem; exact below j (List.mem_cons_of_mem _ mem)
    · split
      · apply Nat.or_lt_two_pow h
        rw [Nat.shiftLeft_eq, Nat.one_mul]
        exact Nat.pow_lt_pow_right (by decide) (below i (List.mem_cons_self))
      · exact h

/-- One generation of the automaton stays inside the bar: the new row has no bit at or beyond `steps`.
Why it matters: the row is a `steps`-bit pattern however long the automaton runs; a hit can never appear on a
step that does not exist, and the row stays the size the circle draws. -/
theorem rhythm_automaton_row_fits (rule steps row : Nat) : Automaton.step rule steps row < 2 ^ steps := by
  unfold Automaton.step
  apply rhythm_fold_fits steps
  · intro i mem; exact List.mem_range.mp mem
  · exact Nat.two_pow_pos steps

/-- The last step of a bar is always a hit when there is at least one hit. -/
private theorem rhythm_euclid_last_hits (hits steps : Nat) (positive : 0 < hits) (fits : hits ≤ steps) :
    Euclid.hit hits steps (steps - 1) = true := by
  unfold Euclid.hit
  have stepsPos : 0 < steps := by omega
  have e : (steps - 1 + 1) * hits / steps = hits := by
    rw [Nat.sub_add_cancel stepsPos, Nat.mul_comm, Nat.mul_div_cancel _ stepsPos]
  have lt : (steps - 1) * hits / steps < hits := by
    rw [Nat.div_lt_iff_lt_mul stepsPos, Nat.mul_comm hits steps]
    exact Nat.mul_lt_mul_of_pos_right (by omega) positive
  simp only [bne_iff_ne, ne_eq, e]
  omega

/-- Ratcheting never takes away the hit itself: on a hit step, the first tick plays whenever at least one
sub-hit is kept.
Why it matters: the RATCHET and SUB-HITS knobs add notes inside a hit; they can never silence the hit the
Euclidean pattern put there. -/
theorem rhythm_ratchet_keeps_the_hit (r : Rhythm) (div : Nat) (kind : r.kind = 3) (kept : 0 < r.subHits)
    (fits : r.subHits ≤ r.ratchet) : Rhythm.tickPlays r div 0 = true := by
  unfold Rhythm.tickPlays Rhythm.subIndex
  simp only [kind, ite_true]
  have pos : 0 < r.ratchet := by omega
  have first : ∀ n, (List.range (n + 1)).find? (fun k => k * div / (n + 1) = 0) = some 0 := by
    intro n
    rw [List.range_succ_eq_map]
    simp
  have eq : r.ratchet = (r.ratchet - 1) + 1 := by omega
  rw [eq, first, ← eq]
  simp only [Nat.zero_add]
  rw [Nat.mod_eq_of_lt (by omega : r.ratchet - 1 < r.ratchet)]
  exact rhythm_euclid_last_hits r.subHits r.ratchet kept fits

/-- An accent only falls on a hit.
Why it matters: accents shape the rhythm's hits; they can never add a note where the pattern has a rest. -/
theorem rhythm_accent_only_on_hit (r : Rhythm) (hits steps step : Nat)
    (accented : Rhythm.accent r hits steps step = true) : Rhythm.hit r hits steps step = true := by
  unfold Rhythm.accent at accented
  simp only [Bool.and_eq_true] at accented
  exact accented.1.2
