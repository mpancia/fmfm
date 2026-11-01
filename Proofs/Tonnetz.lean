import Spec.Tonnetz

/-- Each of P, L and R undoes itself: C major to E minor and back.
Why it matters: a walk can always be retraced; and it is the first of the dihedral relations below. -/
theorem tonnetz_moves_are_involutions (g : Fin 3) (t : Tonnetz.Triad) :
    Tonnetz.move g (Tonnetz.move g t) = t := by
  revert g t; decide +kernel

/-- Checked for every element and move: a move after an element is again one of the 24 elements. -/
private theorem tonnetz_every_move_closed :
    ∀ i : Fin 24, ∀ g : Fin 3, ∃ j : Fin 24, ∀ t : Tonnetz.Triad,
      Tonnetz.act j t = Tonnetz.act i (Tonnetz.move g t) := by
  decide +kernel

/-- Checked: the 24 elements act differently (each pair disagrees on some triad). -/
private theorem tonnetz_every_element_distinct :
    ∀ i j : Fin 24, i ≠ j → ∃ t : Tonnetz.Triad, Tonnetz.act i t ≠ Tonnetz.act j t := by
  decide +kernel

/-- The group the three moves generate has exactly 24 elements: every word of moves acts as one of the 24
listed elements, and no two of those act alike.
Why it matters: however long a word of P, L and R, there are only 24 things it can do to a triad; the
knob's walks live in a small, fully known group (the dihedral group of order 24, `tonnetz_group_is_dihedral`),
the neo-Riemannian PLR group of music theory. -/
theorem tonnetz_group_has_order_24 :
    (∀ w : List (Fin 3), ∃ i : Fin 24, ∀ t, Tonnetz.apply w t = Tonnetz.act i t) ∧
      ∀ i j : Fin 24, i ≠ j → ∃ t, Tonnetz.act i t ≠ Tonnetz.act j t := by
  refine ⟨?_, tonnetz_every_element_distinct⟩
  intro w
  induction w with
  | nil => exact ⟨0, fun t => rfl⟩
  | cons g w ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, hj⟩ := tonnetz_every_move_closed i g
    exact ⟨j, fun t => by rw [Tonnetz.apply, hi, hj]⟩

/-- The group acts simply transitively on the triads: from any triad there is exactly one element reaching
any other.
Why it matters: every one of the 24 triads is reachable from every other by some word of moves, and the word's
effect is determined by where it sends a single triad: a walk that returns C major to C major returns every
triad to itself. -/
theorem tonnetz_simply_transitive :
    (∀ a b : Tonnetz.Triad, ∃ i : Fin 24, Tonnetz.act i a = b) ∧
      ∀ a : Tonnetz.Triad, ∀ i j : Fin 24, Tonnetz.act i a = Tonnetz.act j a → i = j := by
  constructor <;> decide +kernel

/-- The PLR group commutes with every transposition and every inversion (the duality of the two groups,
Lewin's): moving by P, L or R and then transposing is transposing and then moving, likewise inverting.
Why it matters: a walk sounds the same in every key: the walk from D major is the walk from C major moved up
a tone, note for note; and the walk from a minor triad is the inversion of the walk from a major one. -/
theorem tonnetz_commutes_with_transposition_and_inversion (i : Fin 24) (n : Fin 12) (t : Tonnetz.Triad) :
    Tonnetz.act i (Tonnetz.transpose n t) = Tonnetz.transpose n (Tonnetz.act i t) ∧
      Tonnetz.act i (Tonnetz.invert n t) = Tonnetz.invert n (Tonnetz.act i t) := by
  revert i n t; decide +kernel

/-- The dihedral relations: L R has order exactly 12, L has order 2, and L conjugates L R to its inverse R L.
Why it matters: with `tonnetz_group_has_order_24` this names the group: the dihedral group of order 24, the
symmetries of a 12-gon, with L R the rotation and L a reflection. -/
theorem tonnetz_group_is_dihedral :
    (∀ t, Tonnetz.apply ((List.replicate 12 [1, 2]).flatten) t = t) ∧
      (∀ k : Fin 12, 0 < k.val → ∃ t, Tonnetz.apply ((List.replicate k.val [1, 2]).flatten) t ≠ t) ∧
      (∀ t, Tonnetz.apply [1, 1, 2, 1] t = Tonnetz.apply [2, 1] t) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- The L R walk visits all 24 triads, each once, and comes back after 24 moves, from any start; the P L walk
is a cycle of six (a hexatonic cycle) and the P R walk one of eight (an octatonic cycle).
Why it matters: the walks on the knob are these: L R is a Hamiltonian cycle on the Tonnetz, every major and
minor triad once in 24 chords, a note changing at a time (`harmony_walk_keeps_two_notes`); P L and P R are
the two short cycles, six and eight chords, that the same two-note rule allows. -/
theorem tonnetz_walks_are_cycles (start : Fin 24) :
    ((List.range 24).map (Tonnetz.walk 0 start)).Nodup ∧ Tonnetz.walk 0 start 24 = start ∧
      ((List.range 6).map (Tonnetz.walk 1 start)).Nodup ∧ Tonnetz.walk 1 start 6 = start ∧
      ((List.range 8).map (Tonnetz.walk 2 start)).Nodup ∧ Tonnetz.walk 2 start 8 = start := by
  revert start; decide +kernel
