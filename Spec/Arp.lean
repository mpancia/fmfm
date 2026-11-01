import Firmware.Arp

/-- An arpeggiator is consistent: settings in range, held notes playable, counters inside their ranges, and
the sounding note and its timer in step. -/
structure Arp.Valid (a : Arp) : Prop where
  modeFits : a.mode ≤ 5
  octavesPositive : 1 ≤ a.octaves
  octavesFit : a.octaves ≤ 3
  divPositive : 1 ≤ a.div
  gatePositive : 1 ≤ a.gate
  gateFits : a.gate ≤ a.div
  heldPlayable : ∀ n ∈ a.held, n ≤ 127
  heldFew : a.held.length ≤ 64
  countBelowDiv : a.count < a.div
  soundingHasTimer : a.playing.isSome = true ↔ 0 < a.gateLeft
  timerWithinGate : a.gateLeft ≤ a.gate

/-- What the firmware does to the arpeggiator between notes. -/
inductive Arp.Op
  | tick
  | press (note : Nat)
  | release (note : Nat)
  | clear
  | set (mode octaves div gate : Nat)

/-- Apply one operation. -/
def Arp.apply (a : Arp) : Arp.Op → Arp
  | .tick => a.tick
  | .press n => a.press n
  | .release n => a.release n
  | .clear => a.clear
  | .set m o d g => a.set m o d g

/-- The arpeggiator after a list of operations, oldest first. -/
def Arp.run (a : Arp) : List Arp.Op → Arp
  | [] => a
  | op :: rest => (a.apply op).run rest

/-- What each tick of a run told the firmware: a note to stop and a note to start. -/
def Arp.trace (a : Arp) : List Arp.Op → List (Option Nat × Option Nat)
  | [] => []
  | .tick :: rest => (a.tick.off, a.tick.on) :: a.tick.trace rest
  | op :: rest => (a.apply op).trace rest

/-- How many notes a trace starts. -/
def Arp.noteOns (t : List (Option Nat × Option Nat)) : Nat := (t.filter (·.2.isSome)).length
/-- How many notes a trace stops. -/
def Arp.noteOffs (t : List (Option Nat × Option Nat)) : Nat := (t.filter (·.1.isSome)).length
/-- The notes counted as sounding: one or none. -/
def Arp.soundingCount (a : Arp) : Nat := if a.playing.isSome then 1 else 0

/-! Worked examples: C, E and G held (pressed in the order E, C, G), one note a tick. -/

/-- The example: E, C, G pressed in that order, a step of one tick. -/
def Arp.example : Arp := (((Arp.make 1 7).press 64).press 60).press 67

#guard Arp.example.pattern == [60, 64, 67]                                        -- up: sorted
#guard { Arp.example with mode := 5 }.pattern == [64, 60, 67]                     -- as played
#guard { Arp.example with octaves := 2 }.pattern == [60, 64, 67, 72, 76, 79]      -- two octaves
#guard (List.range 4).map (fun k => ((List.range k).foldl (fun (a : Arp) _ => a.tick) Arp.example).tick.on) ==
  [some 60, some 64, some 67, some 60]                                            -- up, round and round
#guard (List.range 4).map (fun k => ((List.range k).foldl (fun (a : Arp) _ => a.tick) { Arp.example with mode := 2 }).tick.on) ==
  [some 60, some 67, some 64, some 60]                                            -- down from where it stood
#guard (Arp.example.release 64).pattern == [60, 67]
#guard Arp.example.tick.tick.on == some 64 && Arp.example.tick.tick.off == some 60   -- the new note stops the old
#guard { Arp.example with mode := 0 }.tick.on == none                             -- off: silent
