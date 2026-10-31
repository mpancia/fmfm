import Firmware.Random
import Firmware.Quantizer

set_option compiler.extract_closed false

/-- How a lane picks the pitch of its next note inside its range. -/
structure NoteRule where
  /-- 0 random, 1 walk, 2 up, 3 down, 4 bounce, 5 loop, 6 turing, 7 step, 8 markov, 9 grammar, 10 chord.
  Anything else behaves like random. -/
  algo : Nat
  /-- Walk: the biggest step. Loop, step and turing: the length. Markov: the style. Grammar: the grammar.
  Chord: how many chord tones the cycle climbs. -/
  amount : Nat
  /-- Loop and step: chance in percent that a slot is replaced by a new random note each time it plays. Turing:
  chance that the recycled bit flips. Markov: chance of a doubled move. Grammar: the depth (25 percent a level).
  Chord: chance of an octave jump. -/
  mutate : Nat

/-- What the note algorithms remember: where the walk or arpeggio is, which way it is going, the loop and the
slot it is on, the slot the keys write next, the turing register, the markov chain (49 counts: the last move
by the next) and the last move, and the grammar's position in its phrase. -/
structure NoteState where
  pos : Nat
  rising : Bool
  slot : Nat
  reg : List Nat
  cursor : Nat
  shift : Nat
  chain : List Nat
  last : Nat
  phrase : Nat

/-- Number of slots in the loop memory. -/
def Notes.regLen : Nat := 16

/-- Number of move classes in the markov chain: a move of -3 to +3 positions. -/
def Notes.moves : Nat := 7

/-- `count` random positions below `span`, drawn from the generator starting at `seed`. -/
def Notes.fill (span : Nat) : Nat → UInt32 → List Nat
  | 0, _ => []
  | count + 1, seed => (Random.below seed span.toUInt32).toNat :: Notes.fill span count (Random.next seed)

/-- A fresh memory for a range of `span` positions: at the bottom, going up, with a random loop, a random
turing register and an unlearnt chain. -/
def Notes.start (span : Nat) (seed : UInt32) : NoteState :=
  { pos := 0, rising := true, slot := 0, reg := Notes.fill span Notes.regLen seed, cursor := 0,
    shift := (seed >>> 8).toNat % 65536, chain := List.replicate (Notes.moves * Notes.moves) 0, last := 3,
    phrase := 0 }

/-- The pitch chosen (as a position in the range) and the memory afterwards. -/
structure NoteChoice where
  offset : Nat
  state : NoteState

/-- Move `pos` by `move - 3` positions, stopping at the ends of the range. -/
def Notes.moveBy (span pos move : Nat) : Nat :=
  if move < 3 then pos - (3 - move) else min (span - 1) (pos + (move - 3))

/-- The markov styles: the weight of each move (-3 to +3) given the last one, four styles of 49 weights.
Style 0 steps, 1 leaps, 2 repeats, 3 climbs then falls. -/
def Notes.style (style : Nat) : List Nat :=
  match style % 4 with
  | 0 => [1, 2, 6, 2, 6, 2, 1, 1, 3, 6, 2, 5, 2, 1, 1, 2, 6, 3, 6, 2, 1, 1, 2, 5, 2, 5, 2, 1, 1, 2, 6, 3, 6, 2, 1,
          1, 2, 5, 2, 6, 3, 1, 1, 2, 6, 2, 6, 2, 1]
  | 1 => [4, 1, 1, 1, 1, 1, 6, 5, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 3,
          2, 3, 1, 1, 1, 1, 5, 6, 1, 1, 1, 1, 1, 4]
  | 2 => [1, 1, 2, 8, 2, 1, 1, 1, 1, 2, 8, 2, 1, 1, 1, 1, 3, 8, 3, 1, 1, 1, 1, 2, 12, 2, 1, 1, 1, 1, 3, 8, 3, 1, 1,
          1, 1, 2, 8, 2, 1, 1, 1, 1, 2, 8, 2, 1, 1]
  | _ => [1, 1, 1, 1, 2, 4, 6, 1, 1, 1, 1, 2, 4, 6, 1, 1, 1, 1, 3, 5, 4, 1, 1, 1, 2, 3, 3, 1, 4, 5, 3, 1, 1, 1, 1,
          6, 4, 2, 1, 1, 1, 1, 6, 4, 2, 1, 1, 1, 1]

/-- The move whose weight range holds `pick`, in a row of `Notes.moves` weights starting at `base`: the first
move whose running total passes `pick`; the last move when the row is empty. Never above the last move. -/
def Notes.pickMove (weights : List Nat) (base pick : Nat) : Nat :=
  let go := (List.range Notes.moves).foldl (fun (acc : Nat × Option Nat) m =>
    match acc with
    | (total, some found) => (total, some found)
    | (total, none) =>
      let w := weights.getD (base + m) 0
      if pick < total + w then (total + w, some m) else (total + w, none)) (0, none)
  min (Notes.moves - 1) (go.2.getD (Notes.moves - 1))

/-- The weights the markov chain plays from: what it learnt from the keys, or the chosen style while it has
learnt nothing. -/
def Notes.chainWeights (style : Nat) (chain : List Nat) : List Nat :=
  if chain.all (· = 0) then Notes.style style else chain

/-- The sum of a row of weights. -/
def Notes.rowTotal (weights : List Nat) (base : Nat) : Nat :=
  (List.range Notes.moves).foldl (fun acc m => acc + weights.getD (base + m) 0) 0

/-- The grammars (L-systems): an axiom and a rule for each of four symbols, as lists of symbols. Symbol `s`
moves the melody by `Notes.grammarMove s`. -/
def Notes.grammar (g : Nat) : List Nat × (Nat → List Nat) :=
  match g % 4 with
  | 0 => ([0], fun s => if s = 0 then [0, 1] else [0])                    -- fibonacci: A -> AB, B -> A
  | 1 => ([0, 2], fun s => if s = 0 then [0, 1, 0] else if s = 1 then [2] else [1, 2])
  | 2 => ([3], fun s => if s = 3 then [3, 0, 1] else if s = 0 then [1] else [3])
  | _ => ([0, 1], fun s => if s = 0 then [1, 2] else if s = 1 then [2, 3] else if s = 2 then [3, 0] else [0])

/-- The move a grammar symbol makes: up a step, up a third, down a step, down a third (as move classes). -/
def Notes.grammarMove (s : Nat) : Nat :=
  match s % 4 with
  | 0 => 4
  | 1 => 5
  | 2 => 2
  | _ => 1

/-- Every symbol of `syms` rewritten by `rule`, `depth` times over. -/
def Notes.expand (rule : Nat → List Nat) : Nat → List Nat → List Nat
  | 0, syms => syms
  | d + 1, syms => Notes.expand rule d (syms.flatMap rule)

/-- The phrase a grammar writes at `depth`: the axiom with every symbol rewritten `depth` times. -/
def Notes.phraseOf (g depth : Nat) : List Nat :=
  Notes.expand (Notes.grammar g).2 depth (Notes.grammar g).1

/-- The `n`-th note of the scale `mask` at or above `low` (the 0th is the first such note), looking up to 60
semitones; `low + 60` if there are not enough. -/
def Notes.scaleTone (mask low n : Nat) : Nat :=
  let found := ((List.range 60).filter (fun k => Quantizer.inScale mask (low + k))).getD n 60
  low + found

/-- Loop and step: replay the memory, sometimes replacing the slot with a new random note. -/
def Notes.replay (rule : NoteRule) (span : Nat) (s : NoteState) (any chance : Nat) : NoteChoice :=
  let kept := s.reg.getD s.slot 0
  let value := if chance < rule.mutate then any else kept
  { offset := value, state := { s with slot := (s.slot + 1) % rule.amount, reg := s.reg.set s.slot value } }

/-- Pick the next pitch. The caller supplies random numbers: `any` below `span`, `step` up to twice the
amount, and `chance` below 100; `mask` and `low` are the lane's scale and bottom note. Each algorithm moves
differently: walk takes a random step of up to `amount` positions (stopping at the ends); up and down cycle
through the range; bounce goes up and down; loop (and step, whose memory the keys write) replays a memory of
`amount` notes, sometimes replacing one; turing shifts a register of `amount` bits, sometimes flipping the
recycled bit, and plays its low byte; markov chooses a move from the last by learnt or styled weights; grammar
walks its phrase; chord climbs `amount` notes of the scale from the bottom. -/
def Notes.choose (rule : NoteRule) (span mask low : Nat) (s : NoteState) (any step chance : Nat) : NoteChoice :=
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
  | 5 => Notes.replay rule span s any chance
  | 6 =>
    let len := rule.amount
    let bit := (s.shift >>> (len - 1)) % 2
    let bit := if chance < rule.mutate then 1 - bit else bit
    let shift := ((s.shift <<< 1) % 65536) ||| bit
    let offset := (shift % 256) * span / 256
    { offset, state := { s with shift, pos := offset } }
  | 7 => Notes.replay rule span s any chance
  | 8 =>
    let weights := Notes.chainWeights rule.amount s.chain
    let base := (s.last % Notes.moves) * Notes.moves
    let total := Notes.rowTotal weights base
    let move := Notes.pickMove weights base (if total = 0 then 0 else any * total / span)
    let far := if chance < rule.mutate then (if move < 3 then move - (3 - move) else min 6 (move + (move - 3))) else move
    let pos := Notes.moveBy span s.pos far
    { offset := pos, state := { s with pos, last := move } }
  | 9 =>
    let phrase := Notes.phraseOf rule.amount (rule.mutate / 25)
    let sym := phrase.getD s.phrase 0
    let pos := Notes.moveBy span s.pos (Notes.grammarMove sym)
    { offset := pos, state := { s with pos, phrase := (s.phrase + 1) % max 1 phrase.length } }
  | 10 =>
    let n := (s.slot + 1) % rule.amount
    let jump := if chance < rule.mutate then 12 else 0
    let offset := min (span - 1) (Notes.scaleTone mask low n + jump - low)
    { offset, state := { s with slot := n, pos := offset } }
  | _ => { offset := any, state := { s with pos := any } }

/-- What a key the player presses teaches the lane: the step sequencer writes the note (as a position in the
range, cut to it) into the slot under the cursor and moves the cursor on; the markov chain counts the move from
the last note played. Other algorithms learn nothing. -/
def Notes.learn (rule : NoteRule) (span : Nat) (s : NoteState) (offset : Nat) : NoteState :=
  let offset := min (span - 1) offset
  match rule.algo with
  | 7 => { s with reg := s.reg.set s.cursor offset, cursor := (s.cursor + 1) % rule.amount, pos := offset }
  | 8 =>
    let move := if offset + 3 ≤ s.pos then 0 else if s.pos + 3 ≤ offset then 6 else offset + 3 - s.pos
    let cell := (s.last % Notes.moves) * Notes.moves + move
    { s with chain := s.chain.set cell (s.chain.getD cell 0 + 1), last := move, pos := offset }
  | _ => s
