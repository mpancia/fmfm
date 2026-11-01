import Firmware.Tonnetz

/-- The 24 triads as a finite type: `Tonnetz.make` below 24. -/
abbrev Tonnetz.Triad := Fin 24

/-- Move `g` (0 P, 1 L, 2 R) on the finite type. -/
def Tonnetz.move (g : Fin 3) (t : Tonnetz.Triad) : Tonnetz.Triad :=
  ⟨Tonnetz.step g t % 24, Nat.mod_lt _ (by decide)⟩

/-- A word of moves, applied left to right. -/
def Tonnetz.apply : List (Fin 3) → Tonnetz.Triad → Tonnetz.Triad
  | [], t => t
  | g :: w, t => Tonnetz.apply w (Tonnetz.move g t)

/-- The 24 elements of the group the moves generate, as words: `(L R)^k` for `k` below 12, then `(L R)^k L`. -/
def Tonnetz.element (i : Fin 24) : List (Fin 3) :=
  (List.replicate (i.val % 12) [1, 2]).flatten ++ (if 12 ≤ i.val then [1] else [])

/-- Group element `i` acting on a triad. -/
def Tonnetz.act (i : Fin 24) (t : Tonnetz.Triad) : Tonnetz.Triad := Tonnetz.apply (Tonnetz.element i) t

/-- Transposition by `n` semitones: the same quality, the root moved up. -/
def Tonnetz.transpose (n : Nat) (t : Tonnetz.Triad) : Tonnetz.Triad :=
  ⟨Tonnetz.make (t.val % 12 + n) (Tonnetz.minor t), by unfold Tonnetz.make; split <;> omega⟩

/-- Inversion about `n`: pitch `x` goes to `n - x`, so a major triad on `r` becomes the minor triad on
`n - r - 7` and back. -/
def Tonnetz.invert (n : Nat) (t : Tonnetz.Triad) : Tonnetz.Triad :=
  ⟨Tonnetz.make (n + 24 - t.val % 12 - 7) (!Tonnetz.minor t), by unfold Tonnetz.make; split <;> omega⟩
