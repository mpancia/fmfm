import Spec.Rhythm
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

/-- Turning a bar by `s` steps keeps the count of any property of its steps. -/
private theorem rhythm_turn_keeps_count (f : Nat → Bool) (n s : Nat) (small : s < n) :
    Rhythm.count (fun i => f ((i + n - s) % n)) n = Rhythm.count f n := by
  unfold Rhythm.count
  -- the bar as the steps before the turn point and after it
  have split : List.range n = List.range' 0 s ++ List.range' s (n - s) := by
    rw [List.range_eq_range']
    have := @List.range'_append_1 0 s (n - s)
    rw [Nat.zero_add, show s + (n - s) = n by omega] at this
    exact this.symm
  have splitBack : List.range n = List.range' 0 (n - s) ++ List.range' (n - s) s := by
    rw [List.range_eq_range']
    have := @List.range'_append_1 0 (n - s) s
    rw [Nat.zero_add, show n - s + s = n by omega] at this
    exact this.symm
  rw [show ((List.range n).filter f).length = ((List.range' 0 (n - s)).filter f).length +
      ((List.range' (n - s) s).filter f).length by rw [splitBack, List.filter_append, List.length_append]]
  rw [split, List.filter_append, List.length_append]
  -- the steps below the turn point land from n - s up; the rest land from 0 up
  have first : ((List.range' 0 s).filter (fun i => f ((i + n - s) % n))).length =
      ((List.range' (n - s) s).filter f).length := by
    rw [show List.range' (n - s) s = (List.range' 0 s).map ((n - s) + ·) by rw [List.map_add_range']; rfl,
      List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro i mem
    rw [List.mem_range'] at mem
    simp only [Function.comp]
    congr 2
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have second : ((List.range' s (n - s)).filter (fun i => f ((i + n - s) % n))).length =
      ((List.range' 0 (n - s)).filter f).length := by
    rw [show List.range' s (n - s) = (List.range' 0 (n - s)).map (s + ·) by rw [List.map_add_range']; rfl,
      List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro i mem
    rw [List.mem_range'] at mem
    simp only [Function.comp]
    congr 2
    rw [show s + i + n - s = i + n by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  rw [first, second]
  omega

/-- Turning the bar (ROTATE) keeps the number of hits: a turned bar has exactly `hits` hits, like the plain
one (`euclid_hit_count`).
Why it matters: ROTATE moves the pattern round the circle without adding or losing a note. -/
theorem rhythm_rotate_keeps_hits (r : Rhythm) (hits steps : Nat) (kind : r.kind = 1) (positive : 0 < steps) :
    Rhythm.count (Rhythm.hit r hits steps) steps = Rhythm.count (Euclid.hit hits steps) steps := by
  have e : Rhythm.hit r hits steps = fun i => Euclid.hit hits steps ((i + steps - r.rotate % steps) % steps) := by
    funext i; unfold Rhythm.hit Rhythm.source; simp [kind]
  rw [e]
  exact rhythm_turn_keeps_count (Euclid.hit hits steps) steps (r.rotate % steps) (Nat.mod_lt _ positive)

/-- Bit `i` of a row built by setting bit `j` for every `j` in `l` with `f j`. -/
private theorem rhythm_fold_testBit (f : Nat → Bool) (i : Nat) (small : i < 32) : ∀ (l : List Nat) (acc : UInt32),
    (∀ j ∈ l, j < 32) →
    (l.foldl (fun acc j => if f j then acc ||| (1 <<< j.toUInt32) else acc) acc).toNat.testBit i =
      (acc.toNat.testBit i || (l.contains i && f i)) := by
  intro l
  induction l with
  | nil => intro acc _; simp
  | cons j rest ih =>
    intro acc below
    simp only [List.foldl_cons]
    rw [ih _ (fun k mem => below k (List.mem_cons_of_mem _ mem))]
    have jLt : j < 32 := below j (List.mem_cons_self)
    have one : (1 <<< j.toUInt32).toNat = 2 ^ j := by
      rw [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]
      have e : (1 : UInt32).toNat = 1 := by decide
      have m : j.toUInt32.toNat % 32 = j := by simp; omega
      rw [e, Nat.one_mul, m, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) jLt)]
    by_cases fj : f j
    · simp only [fj, ite_true, UInt32.toNat_or, Nat.testBit_or, one, Nat.testBit_two_pow]
      by_cases e : i = j
      · subst e; simp [fj]
      · simp [e, Ne.symm e, List.contains_cons]
    · simp only [fj, ite_false]
      by_cases e : i = j
      · subst e; simp [fj]
      · simp [e, List.contains_cons]

/-- Bit `i` of a built row, from the bar's steps. -/
private theorem rhythm_built_testBit (f : Nat → Bool) (steps i : Nat) (small : steps ≤ 32) (inside : i < 32) :
    ((List.range steps).foldl (fun acc j => if f j then acc ||| (1 <<< j.toUInt32) else acc) 0).toNat.testBit i =
      (decide (i < steps) && f i) := by
  rw [rhythm_fold_testBit f i inside (List.range steps) 0 (fun j mem => by have := List.mem_range.mp mem; omega)]
  simp [List.contains_iff_mem, List.mem_range]

/-- `Rhythm.bit` reads a bit of the row's value. -/
private theorem rhythm_bit_eq (row : UInt32) (i : Nat) (inside : i < 32) : Rhythm.bit row i = row.toNat.testBit i := by
  unfold Rhythm.bit
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have m : i.toUInt32.toNat % 32 = i := by simp; omega
  have v : ((row >>> i.toUInt32) &&& 1).toNat = row.toNat / 2 ^ i % 2 := by
    rw [UInt32.toNat_and, UInt32.toNat_shiftRight, m, Nat.shiftRight_eq_div_pow]
    simp [Nat.and_one_is_mod]
  have mod : row.toNat / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases one : row.toNat / 2 ^ i % 2 = 1
  · have : (row >>> i.toUInt32) &&& 1 = 1 := by rw [← UInt32.toNat_inj, v, one]; rfl
    simp [this, one]
  · have : (row >>> i.toUInt32) &&& 1 = 0 := by rw [← UInt32.toNat_inj, v]; simp; omega
    simp [this, one]

/-- Rule 0 kills the row: after one generation nothing plays.
Why it matters: the automaton has a rule that is silence, and the reseed on a dead row is what brings the
bar back. -/
theorem rhythm_rule_zero_dies (steps : Nat) (row : UInt32) (small : steps ≤ 32) : Automaton.step 0 steps row = 0 := by
  rw [← UInt32.toNat_inj]
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < 32
  · unfold Automaton.step
    rw [rhythm_built_testBit _ steps i small inside]
    simp
  · have := UInt32.toNat_lt (Automaton.step 0 steps row)
    have big : 2 ^ 32 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega : _ < 2 ^ i)]
    simp [Nat.testBit_lt_two_pow (by simp [Nat.two_pow_pos] : (0 : UInt32).toNat < 2 ^ i)]

/-- Bits of a row at or past 32 are clear. -/
private theorem rhythm_high_bit (row : UInt32) (i : Nat) (outside : 32 ≤ i) : row.toNat.testBit i = false := by
  have := UInt32.toNat_lt row
  have big : 2 ^ 32 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) outside
  exact Nat.testBit_lt_two_pow (by omega)

/-- Rule 255 fills the bar: after one generation every step plays.
Why it matters: the other end of the rule knob is a wall of hits, so the circle shows the whole range from
silence (rule 0) to everything (rule 255). -/
theorem rhythm_rule_full_fills (steps : Nat) (row : UInt32) (small : steps ≤ 32) :
    (Automaton.step 255 steps row).toNat = 2 ^ steps - 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_two_pow_sub_one]
  by_cases inside : i < 32
  · unfold Automaton.step
    rw [rhythm_built_testBit _ steps i small inside]
    by_cases lt : i < steps
    · simp only [lt, decide_true, Bool.true_and]
      by_cases a : Rhythm.bit row ((i + steps - 1) % steps) <;> by_cases b : Rhythm.bit row i <;>
        by_cases c : Rhythm.bit row ((i + 1) % steps) <;> simp [a, b, c] <;> decide
    · simp [lt]
  · rw [rhythm_high_bit _ i (by omega)]
    simp; omega

/-- The low `steps` bits of a row, bit by bit. -/
private theorem rhythm_cut_testBit (steps : Nat) (row : UInt32) (i : Nat) (small : steps ≤ 32) :
    (Rhythm.cut steps row).toNat.testBit i = (decide (i < steps) && row.toNat.testBit i) := by
  unfold Rhythm.cut
  split
  · rename_i lt
    rw [UInt32.toNat_and, Nat.testBit_and, UInt32.toNat_sub, UInt32.toNat_shiftLeft]
    have e : (1 : UInt32).toNat = 1 := by decide
    have m : steps.toUInt32.toNat % 32 = steps := by simp; omega
    rw [e, Nat.shiftLeft_eq, Nat.one_mul, m, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) lt)]
    have pos : 0 < 2 ^ steps := Nat.two_pow_pos steps
    have lt32 : 2 ^ steps < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) lt
    rw [show (2 ^ 32 - 1 + 2 ^ steps) % 2 ^ 32 = 2 ^ steps - 1 by omega, Nat.testBit_two_pow_sub_one, Bool.and_comm]
  · rename_i ge
    have : steps = 32 := by omega
    subst this
    by_cases inside : i < 32
    · simp [inside]
    · rw [rhythm_high_bit _ i (by omega)]; simp

/-- Rule 204 freezes the bar: a row that fits the bar comes back unchanged every generation.
Why it matters: there is a rule on which the automaton is exactly the Euclidean bar it was seeded with, so
turning RULE from 204 is the way to make it move. -/
theorem rhythm_rule_204_freezes (steps : Nat) (row : UInt32) (small : steps ≤ 32) :
    Automaton.step 204 steps row = Rhythm.cut steps row := by
  rw [← UInt32.toNat_inj]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [rhythm_cut_testBit steps row i small]
  by_cases inside : i < 32
  · unfold Automaton.step
    rw [rhythm_built_testBit _ steps i small inside]
    by_cases lt : i < steps
    · simp only [lt, decide_true, Bool.true_and]
      rw [← rhythm_bit_eq row i inside]
      -- rule 204 = 11001100: the new cell is the old cell, whatever its neighbours
      by_cases a : Rhythm.bit row ((i + steps - 1) % steps) <;> by_cases b : Rhythm.bit row i <;>
        by_cases c : Rhythm.bit row ((i + 1) % steps) <;> simp [a, b, c] <;> decide
    · simp [lt]
  · rw [rhythm_high_bit _ i (by omega)]; simp; omega
