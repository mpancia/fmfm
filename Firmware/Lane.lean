import Firmware.Random
import Firmware.Divider
import Firmware.Euclid
import Firmware.Quantizer

set_option compiler.extract_closed false

/-- One generative lane: a clock divider drives a Euclidean rhythm; each hit picks a random note in a
range, snaps it to the scale, and plays it for a short gate. At most one note sounds per lane. -/
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
  rng : UInt32
  /-- Running state: ticks since the last step, the current step, the note sounding and its ticks left. -/
  count : Nat
  step : Nat
  playing : Option Nat
  gateLeft : Nat
  /-- What the latest tick did: a note to stop and a note to start. -/
  off : Option Nat
  on : Option Nat

/-- Gate length for a step of `div` ticks: half a step, at least one tick. -/
def Lane.gateFor (div : Nat) : Nat := max 1 (div / 2)

/-- Keep `value` between `lo` and `hi`. -/
def Lane.clamp (lo hi value : Nat) : Nat := max lo (min hi value)

/-- A lane in a safe state: every setting is forced into its allowed range. `span` is cut so notes stay
below 120. -/
def Lane.make (hits steps div mask low span : Nat) (seed : UInt32) : Lane :=
  let steps := Lane.clamp 1 32 steps
  let div := Lane.clamp 1 96 div
  let low := Lane.clamp 12 96 low
  { hits := min hits steps, steps, div, mask := if mask % 4096 = 0 then 4095 else mask % 4096,
    low, span := Lane.clamp 1 (120 - low) span, gate := Lane.gateFor div, rng := seed,
    count := 0, step := 0, playing := none, gateLeft := 0, off := none, on := none }

/-- Change the rhythm, speed and scale of a running lane. Its position and sounding note carry on. -/
def Lane.reconfigure (l : Lane) (hits steps div mask : Nat) : Lane :=
  let fresh := Lane.make hits steps div mask l.low l.span l.rng
  { fresh with
      count := l.count % fresh.div
      step := l.step % fresh.steps
      playing := l.playing
      gateLeft := min l.gateLeft fresh.gate }

/-- Advance one clock tick. A step boundary that is a hit plays a new note (stopping the old one first);
otherwise the sounding note's gate runs down and stops it at zero. -/
def Lane.tick (l : Lane) : Lane :=
  let (count, boundary) := Divider.tick l.div l.count
  let trigger := boundary && Euclid.hit l.hits l.steps l.step
  let expired := l.gateLeft ≤ 1
  let step := if boundary then (l.step + 1) % l.steps else l.step
  if trigger then
    let note := Quantizer.snap l.mask (l.low + (Random.below l.rng l.span.toUInt32).toNat)
    { l with
        count, step
        rng := Random.next l.rng
        playing := some note
        gateLeft := l.gate
        off := l.playing
        on := some note }
  else if expired then
    { l with count, step, playing := none, gateLeft := 0, off := l.playing, on := none }
  else
    { l with count, step, gateLeft := l.gateLeft - 1, off := none, on := none }

/-- Stop the sounding note now (the clock was stopped). The next tick reports it as stopped. -/
def Lane.silence (l : Lane) : Lane :=
  { l with playing := none, gateLeft := 0, off := l.playing, on := none }
