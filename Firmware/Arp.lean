import Firmware.Random
import Firmware.Divider

set_option compiler.extract_closed false

/-- The arpeggiator: the keys you hold, played one at a time in step with the clock. `held` are the held notes
in the order they were pressed; the pattern is those notes sorted (or as pressed), repeated over `octaves`
octaves. Modes: 0 off, 1 up, 2 down, 3 up and down, 4 random, 5 as played. At most one note sounds. -/
structure Arp where
  held : List Nat
  mode : Nat
  octaves : Nat
  /-- Clock ticks a step, and ticks a note sounds for. -/
  div : Nat
  gate : Nat
  rng : UInt32
  /-- Running state: ticks since the last step, the position in the pattern, which way up and down goes, the
  note sounding and its ticks left, and what the latest tick did. -/
  count : Nat
  pos : Nat
  rising : Bool
  playing : Option Nat
  gateLeft : Nat
  off : Option Nat
  on : Option Nat

/-- Keep `value` between `lo` and `hi`. -/
def Arp.clamp (lo hi value : Nat) : Nat := max lo (min hi value)

/-- Insert `n` into a sorted list. -/
def Arp.insertSorted (n : Nat) : List Nat → List Nat
  | [] => [n]
  | x :: xs => if n ≤ x then n :: x :: xs else x :: Arp.insertSorted n xs

/-- The held notes sorted upwards. -/
def Arp.sorted (held : List Nat) : List Nat := held.foldr Arp.insertSorted []

/-- The notes the pattern runs through: the held notes sorted (as pressed in mode 5), once an octave. -/
def Arp.pattern (a : Arp) : List Nat :=
  let base := if a.mode = 5 then a.held else Arp.sorted a.held
  (List.range (max 1 a.octaves)).flatMap (fun o => base.map (· + 12 * o))

/-- A fresh, silent arpeggiator: nothing held, up, one octave, a step of `div` ticks. -/
def Arp.make (div : Nat) (seed : UInt32) : Arp :=
  let div := Arp.clamp 1 96 div
  { held := [], mode := 1, octaves := 1, div, gate := max 1 (div / 2), rng := seed, count := 0, pos := 0,
    rising := true, playing := none, gateLeft := 0, off := none, on := none }

/-- Change the settings: mode 0 to 5, 1 to 3 octaves, a step of `div` ticks, a gate of `gate` ticks (cut to the
step). The arpeggio carries on from where it is. -/
def Arp.set (a : Arp) (mode octaves div gate : Nat) : Arp :=
  let div := Arp.clamp 1 96 div
  { a with mode := min 5 mode, octaves := Arp.clamp 1 3 octaves, div, gate := Arp.clamp 1 div gate,
           count := a.count % div, gateLeft := min a.gateLeft (Arp.clamp 1 div gate) }

/-- A key pressed: the note joins the held notes (once). Notes above 127 are ignored, and so is a 65th note. -/
def Arp.press (a : Arp) (note : Nat) : Arp :=
  if note ≤ 127 && !a.held.contains note && a.held.length < 64 then { a with held := a.held ++ [note] } else a

/-- A key released: the note leaves the held notes. -/
def Arp.release (a : Arp) (note : Nat) : Arp := { a with held := a.held.filter (· ≠ note) }

/-- All keys released at once (the latch let go). -/
def Arp.clear (a : Arp) : Arp := { a with held := [] }

/-- The position the next note is taken from, and the position and direction after it, for a pattern of
`len` notes. Up and down climb and fall; up-and-down turns at the ends; random picks anywhere. -/
def Arp.step (a : Arp) (len : Nat) : Nat × Nat × Bool :=
  let pos := a.pos % len
  match a.mode with
  | 2 => (pos, (pos + len - 1) % len, false)
  | 3 =>
    if a.rising then
      if pos + 1 < len then (pos, pos + 1, true) else (pos, pos - 1, false)
    else if 0 < pos then (pos, pos - 1, false) else (pos, min 1 (len - 1), true)
  | 4 => let r := (Random.below a.rng len.toUInt32).toNat; (r, r, true)
  | _ => (pos, (pos + 1) % len, true)

/-- Is this tick the start of a step? -/
def Arp.atStep (a : Arp) : Bool := (Divider.tick a.div a.count).2

/-- One clock tick. On a step with notes held and the arpeggiator on, the next note of the pattern starts
(stopping the one before); otherwise the sounding note's gate runs down and stops it at zero. -/
def Arp.tick (a : Arp) : Arp :=
  let count := (Divider.tick a.div a.count).1
  let pattern := a.pattern
  if a.atStep && a.mode ≠ 0 && !pattern.isEmpty then
    let (here, pos, rising) := a.step pattern.length
    let note := pattern.getD here 0
    { a with count, pos, rising, rng := Random.next a.rng, playing := some note, gateLeft := a.gate,
             off := a.playing, on := some note }
  else if a.gateLeft ≤ 1 then
    { a with count, playing := none, gateLeft := 0, off := a.playing, on := none }
  else
    { a with count, gateLeft := a.gateLeft - 1, off := none, on := none }

/-- Stop the sounding note now. The next report shows it as stopped. -/
def Arp.silence (a : Arp) : Arp := { a with playing := none, gateLeft := 0, off := a.playing, on := none }
