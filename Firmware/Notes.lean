import Firmware.Random

set_option compiler.extract_closed false

/-- How a lane picks the pitch of its next note inside its range. -/
structure NoteRule where
  /-- 0 random, 1 walk, 2 up, 3 down, 4 bounce, 5 loop. Anything else behaves like random. -/
  algo : Nat
  /-- Walk: the biggest step. Loop: the length of the loop. -/
  amount : Nat
  /-- Loop: chance in percent that a slot is replaced by a new random note each time it plays. -/
  mutate : Nat

/-- What the note algorithms remember: where the walk or arpeggio is, which way it is going, and the loop. -/
structure NoteState where
  pos : Nat
  rising : Bool
  slot : Nat
  reg : List Nat

/-- Number of slots in the loop memory. -/
def Notes.regLen : Nat := 16

/-- `count` random positions below `span`, drawn from the generator starting at `seed`. -/
def Notes.fill (span : Nat) : Nat → UInt32 → List Nat
  | 0, _ => []
  | count + 1, seed => (Random.below seed span.toUInt32).toNat :: Notes.fill span count (Random.next seed)

/-- A fresh memory for a range of `span` positions: at the bottom, going up, with a random loop. -/
def Notes.start (span : Nat) (seed : UInt32) : NoteState :=
  { pos := 0, rising := true, slot := 0, reg := Notes.fill span Notes.regLen seed }

/-- The pitch chosen (as a position in the range) and the memory afterwards. -/
structure NoteChoice where
  offset : Nat
  state : NoteState

/-- Pick the next pitch. The caller supplies random numbers: `any` below `span`, `step` up to twice the
amount, and `chance` below 100. Each algorithm moves differently:
walk takes a random step of up to `amount` positions (stopping at the ends); up and down cycle through the
range; bounce goes up and down; loop replays a memory of `amount` notes, sometimes replacing one. -/
def Notes.choose (rule : NoteRule) (span : Nat) (s : NoteState) (any step chance : Nat) : NoteChoice :=
  match rule.algo with
  | 1 =>
    let pos := if step < rule.amount then s.pos - (rule.amount - step)
      else min (span - 1) (s.pos + (step - rule.amount))
    { offset := pos, state := { s with pos } }
  | 2 =>
    let pos := (s.pos + 1) % span
    { offset := pos, state := { s with pos } }
  | 3 =>
    let pos := (s.pos + span - 1) % span
    { offset := pos, state := { s with pos } }
  | 4 =>
    if s.rising then
      if s.pos + 1 < span then { offset := s.pos + 1, state := { s with pos := s.pos + 1 } }
      else { offset := s.pos - 1, state := { s with pos := s.pos - 1, rising := false } }
    else if 0 < s.pos then { offset := s.pos - 1, state := { s with pos := s.pos - 1 } }
    else
      let pos := min 1 (span - 1)
      { offset := pos, state := { s with pos, rising := true } }
  | 5 =>
    let kept := s.reg.getD s.slot 0
    let value := if chance < rule.mutate then any else kept
    { offset := value, state := { s with slot := (s.slot + 1) % rule.amount, reg := s.reg.set s.slot value } }
  | _ => { offset := any, state := { s with pos := any } }
