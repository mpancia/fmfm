set_option compiler.extract_closed false

/-!
The Tonnetz: the 24 major and minor triads and the three neo-Riemannian moves between them. Each move keeps
two of the triad's three notes and shifts the third by a semitone or a tone: P (parallel) C major ↔ C minor,
L (leading tone) C major ↔ E minor, R (relative) C major ↔ A minor. A progression on GLO > HARMONY can be a
walk by a repeated word of these moves instead of a table of degrees; `Proofs/Tonnetz.lean` is the group
theory (the moves generate a group of 24 elements acting simply transitively on the triads, which commutes
with every transposition and inversion) and `Proofs/Harmony.lean` what it means for the lanes.
-/

/-- A triad as a number below 24: the root (0 to 11, semitones above C or above the key), plus 12 for minor. -/
def Tonnetz.make (root : Nat) (minor : Bool) : Nat := root % 12 + if minor then 12 else 0

/-- The triad's root, 0 to 11. -/
def Tonnetz.root (t : Nat) : Nat := t % 12

/-- Is the triad minor? -/
def Tonnetz.minor (t : Nat) : Bool := t % 24 ≥ 12

/-- Parallel: the same root, the other quality. -/
def Tonnetz.P (t : Nat) : Nat := Tonnetz.make (Tonnetz.root t) (!Tonnetz.minor t)

/-- Leading-tone exchange: a major triad's root falls a semitone (C major to E minor), a minor triad's fifth
rises one (E minor back to C major). -/
def Tonnetz.L (t : Nat) : Nat :=
  if Tonnetz.minor t then Tonnetz.make (Tonnetz.root t + 8) false else Tonnetz.make (Tonnetz.root t + 4) true

/-- Relative: a major triad's fifth rises a tone (C major to A minor), a minor triad's root falls one. -/
def Tonnetz.R (t : Nat) : Nat :=
  if Tonnetz.minor t then Tonnetz.make (Tonnetz.root t + 3) false else Tonnetz.make (Tonnetz.root t + 9) true

/-- Move `letter`: 0 is P, 1 is L, anything else R. -/
def Tonnetz.step (letter t : Nat) : Nat :=
  match letter with
  | 0 => Tonnetz.P t
  | 1 => Tonnetz.L t
  | _ => Tonnetz.R t

/-- The words on the knob, two letters each, read in turn: word 0 is L R (the walk through all 24 triads),
1 is P L (the six triads of a hexatonic cycle), anything else P R (the eight of an octatonic cycle). -/
def Tonnetz.letter (word i : Nat) : Nat :=
  match word, i % 2 with
  | 0, 0 => 1 | 0, _ => 2
  | 1, 0 => 0 | 1, _ => 1
  | _, 0 => 0 | _, _ => 2

/-- The triad after `count` moves of `word` from `start`. -/
def Tonnetz.walk (word start : Nat) : Nat → Nat
  | 0 => start % 24
  | count + 1 => Tonnetz.step (Tonnetz.letter word count) (Tonnetz.walk word start count)

/-- The triad's three notes as a 12-bit mask of pitch classes above its own root's reference. -/
def Tonnetz.mask (t : Nat) : Nat :=
  let root := Tonnetz.root t
  (1 <<< root) ||| (1 <<< ((root + if Tonnetz.minor t then 3 else 4) % 12)) ||| (1 <<< ((root + 7) % 12))
