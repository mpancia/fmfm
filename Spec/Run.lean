import Firmware.Lane
import Spec.Lane

/-- What the firmware can do to a lane between notes: a clock tick, or a change of settings from the knobs. -/
inductive Lane.Op
  | tick
  | reconfigure (hits steps div mask : Nat)
  | setNotes (algo prob amount mutate : Nat)

/-- Apply one operation. -/
def Lane.apply (l : Lane) : Lane.Op → Lane
  | .tick => l.tick
  | .reconfigure h s d m => l.reconfigure h s d m
  | .setNotes a p n m => l.setNotes a p n m

/-- The lane after a list of operations, oldest first. -/
def Lane.run (l : Lane) : List Lane.Op → Lane
  | [] => l
  | op :: rest => (l.apply op).run rest

/-- What the lane told the firmware to do on each tick of a run: a note to stop and a note to start. Only
ticks speak; setting changes say nothing. -/
def Lane.trace (l : Lane) : List Lane.Op → List (Option Nat × Option Nat)
  | [] => []
  | .tick :: rest => (l.tick.off, l.tick.on) :: l.tick.trace rest
  | op :: rest => (l.apply op).trace rest

/-- How many notes a trace starts. -/
def Lane.noteOns (t : List (Option Nat × Option Nat)) : Nat := (t.filter (·.2.isSome)).length

/-- How many notes a trace stops. -/
def Lane.noteOffs (t : List (Option Nat × Option Nat)) : Nat := (t.filter (·.1.isSome)).length

/-- The number of notes a lane counts as sounding: one or none. -/
def Lane.soundingCount (l : Lane) : Nat := if l.playing.isSome then 1 else 0

/-- After `ticks` ticks from a fresh lane, where the clock stands: this is what step the lane is on. -/
def Lane.stepAfter (div steps ticks : Nat) : Nat := (ticks / div) % steps
