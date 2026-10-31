import Firmware.Random
import Firmware.Divider
import Firmware.Euclid
import Firmware.Quantizer
import Firmware.Notes
import Firmware.Rhythm

set_option compiler.extract_closed false

/-- One generative lane: a clock divider drives a rhythm (Euclidean at heart, see `Rhythm`); each hit may play
a note, whose pitch a note algorithm picks in a range and the scale then adjusts, for a short gate. At most
one note sounds per lane. -/
structure Lane where
  /-- Euclid: notes per bar, steps per bar. -/
  hits : Nat
  steps : Nat
  /-- Clock ticks per step. -/
  div : Nat
  /-- Scale: bit 0 is C, bit 11 is B. -/
  mask : Nat
  /-- Notes come from `low` up to `low + span - 1`, before snapping to the scale. -/
  low : Nat
  span : Nat
  /-- Ticks a note sounds for. -/
  gate : Nat
  /-- Percent chance that a hit plays. -/
  prob : Nat
  rule : NoteRule
  rhythm : Rhythm
  rng : UInt32
  /-- Running state: ticks since the last step, the current step, the note memory, the note sounding and its
  ticks left. -/
  count : Nat
  step : Nat
  notes : NoteState
  playing : Option Nat
  gateLeft : Nat
  /-- What the latest tick did: a note to stop and a note to start, and whether the start is accented. -/
  off : Option Nat
  on : Option Nat
  loud : Bool

/-- Gate length for a step of `div` ticks: half a step, at least one tick. -/
def Lane.gateFor (div : Nat) : Nat := max 1 (div / 2)

/-- Keep `value` between `lo` and `hi`. -/
def Lane.clamp (lo hi value : Nat) : Nat := max lo (min hi value)

/-- A scale mask forced into 12 bits and never empty (an empty one becomes the chromatic scale). -/
def Lane.cleanMask (mask : Nat) : Nat := if mask % 4096 = 0 then 4095 else mask % 4096

/-- A lane in a safe state: every setting is forced into its allowed range. `span` is cut so notes stay
below 120. It starts on the random algorithm, always playing. -/
def Lane.make (hits steps div mask low span : Nat) (seed : UInt32) : Lane :=
  let steps := Lane.clamp 1 32 steps
  let div := Lane.clamp 1 96 div
  let low := Lane.clamp 12 96 low
  let span := Lane.clamp 1 (120 - low) span
  { hits := min hits steps, steps, div, mask := Lane.cleanMask mask, low, span, gate := Lane.gateFor div,
    prob := 100, rule := { algo := 0, amount := 4, mutate := 10 }, rhythm := Rhythm.make 0 0 0 90 1 1 (min hits steps) steps 0,
    rng := seed, count := 0, step := 0, notes := Notes.start span seed, playing := none, gateLeft := 0, off := none,
    on := none, loud := false }

/-- Change the rhythm, speed and scale of a running lane. Its position, memory and sounding note carry on. -/
def Lane.reconfigure (l : Lane) (hits steps div mask : Nat) : Lane :=
  let steps := Lane.clamp 1 32 steps
  let div := Lane.clamp 1 96 div
  { l with
      hits := min hits steps
      steps, div
      mask := Lane.cleanMask mask
      gate := Lane.gateFor div
      rhythm := Rhythm.make l.rhythm.kind l.rhythm.rotate l.rhythm.accents l.rhythm.rule l.rhythm.ratchet l.rhythm.subHits
        (min hits steps) steps l.rhythm.row
      count := l.count % div
      step := l.step % steps
      gateLeft := min l.gateLeft (Lane.gateFor div) }

/-- Change the rhythm source (see `Rhythm`): the kind, rotation, accents, automaton rule, ratchet and sub-hits.
The automaton's row is reseeded from the pattern when the kind changes to it or `reseed` is set. -/
def Lane.setRhythm (l : Lane) (kind rotate accents rule ratchet subHits : Nat) (reseed : Bool) : Lane :=
  let row := if reseed || (min 3 kind ≠ l.rhythm.kind) then 0 else l.rhythm.row
  { l with rhythm := Rhythm.make kind rotate accents rule ratchet subHits l.hits l.steps row }

/-- What the player's key teaches the lane: the note, as a position in the range (notes below the range teach
the bottom). -/
def Lane.learn (l : Lane) (note : Nat) : Lane :=
  { l with notes := Notes.learn l.rule l.span l.notes (note - l.low) }

/-- Change how the lane chooses notes: the algorithm (0 to 10), the chance a hit plays, the amount (walk size,
loop length, ...) and the mutation chance. The note memory carries on. -/
def Lane.setNotes (l : Lane) (algo prob amount mutate : Nat) : Lane :=
  let amount := Lane.clamp 1 Notes.regLen amount
  { l with
      prob := min prob 100
      rule := { algo := min algo 10, amount, mutate := min mutate 100 }
      notes := { l.notes with slot := l.notes.slot % amount, cursor := l.notes.cursor % amount } }

/-- A random number below `limit` (from 1 to 65535), drawn from generator state `r`. -/
def Lane.draw (r : UInt32) (limit : Nat) : Nat := (Random.below r limit.toUInt32).toNat

/-- Is this tick the start of a new step? -/
def Lane.atStep (l : Lane) : Bool := (Divider.tick l.div l.count).2

/-- Does the rhythm mark the current step as a hit? -/
def Lane.stepHit (l : Lane) : Bool := Rhythm.hit l.rhythm l.hits l.steps l.step

/-- Is this tick one that plays on a hit step: its first tick, or one of the ratchet's sub-hits? -/
def Lane.isHit (l : Lane) : Bool := l.stepHit && Rhythm.tickPlays l.rhythm l.div l.count

/-- The gate of a note this tick starts: a sub-hit's gate is cut to the time before the next one. -/
def Lane.gateNow (l : Lane) : Nat :=
  if l.rhythm.kind = 3 then max 1 (min l.gate (l.div / l.rhythm.ratchet)) else l.gate

/-- Does this tick start a note? It must be a hit, and then the play chance decides. -/
def Lane.plays (l : Lane) : Bool :=
  l.isHit && decide (Lane.draw (Random.next (Random.next (Random.next l.rng))) 100 < l.prob)

/-- The pitch the note algorithm picks for this tick, and the memory afterwards. -/
def Lane.noteChoice (l : Lane) : NoteChoice :=
  Notes.choose l.rule l.span l.mask l.low l.notes (Lane.draw l.rng l.span)
    (Lane.draw (Random.next l.rng) (2 * l.rule.amount + 1)) (Lane.draw (Random.next (Random.next l.rng)) 100)

/-- Is this tick the last of the bar? -/
def Lane.atBarEnd (l : Lane) : Bool := l.atStep && l.step + 1 = l.steps

/-- The lane one tick later, apart from notes: the clock and step have moved, the rhythm has moved on at the
end of a bar, and the random generator has moved on if this tick was a hit, played or not, so a skipped hit
does not repeat. -/
def Lane.moved (l : Lane) : Lane :=
  { l with
      count := (Divider.tick l.div l.count).1
      step := if l.atStep then (l.step + 1) % l.steps else l.step
      rhythm := if l.atBarEnd then Rhythm.endBar l.rhythm l.steps else l.rhythm
      rng := if l.isHit then Random.next (Random.next (Random.next (Random.next l.rng))) else l.rng }

/-- Advance one clock tick. A hit that plays starts a new note (stopping the old one first); otherwise the
sounding note's gate runs down and stops it at zero. -/
def Lane.tick (l : Lane) : Lane :=
  if l.plays then
    let choice := l.noteChoice
    let note := Quantizer.snap l.mask (l.low + choice.offset)
    { l.moved with
        notes := choice.state, playing := some note, gateLeft := l.gateNow, off := l.playing, on := some note,
        loud := Rhythm.accent l.rhythm l.hits l.steps l.step }
  else if l.gateLeft ≤ 1 then
    { l.moved with playing := none, gateLeft := 0, off := l.playing, on := none, loud := false }
  else
    { l.moved with gateLeft := l.gateLeft - 1, off := none, on := none, loud := false }

/-- Stop the sounding note now (the clock was stopped). The next tick reports it as stopped. -/
def Lane.silence (l : Lane) : Lane :=
  { l with playing := none, gateLeft := 0, off := l.playing, on := none, loud := false }
