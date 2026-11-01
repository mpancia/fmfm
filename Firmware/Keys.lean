import Firmware.Harmony

set_option compiler.extract_closed false

/-!
The keys quantized (ARP > KEYS, QUANT): the white keys become the degrees of a scale. Mode 1 (SCALE) uses the
chosen lane's scale in the song's key, mode 2 (CHORD) the lane's chord-follow mask, so with a progression
running the white keys are the chord tones of the moment. C D E F G A B play degrees 1 to 7 (a five-note scale
wraps: A and B are its first two degrees an octave up); a black key plays as the white key below it; the
octave
of the key is kept, the key's root added. Mode 0 (OFF) plays the keys as they are.
-/

/-- The white key a pitch class is, 0 (C) to 6 (B); a black key counts as the white key below it. -/
@[inline] def Keys.white (pitchClass : UInt32) : UInt32 :=
  match pitchClass % 12 with
  | 0 | 1 => 0 | 2 | 3 => 1 | 4 => 2 | 5 | 6 => 3 | 7 | 8 => 4 | 9 | 10 => 5 | _ => 6

/-- The offsets above the root at which `mask` has a note, in order: the scale's degrees in semitones. -/
def Keys.offsets (mask root : Nat) : List Nat :=
  (List.range 12).filter (fun d => mask.testBit ((root + d) % 12))

/-- Degree `k` (0 up) of `mask` above `root`, in semitones: the `k`th offset, an octave more for every time
`k` goes round the scale. An empty mask gives `k` semitones. -/
def Keys.degree (mask root k : Nat) : Nat :=
  let offsets := Keys.offsets mask root
  if offsets.length = 0 then k else offsets.getD (k % offsets.length) 0 + 12 * (k / offsets.length)

/-- A played note quantized: in mode 0 itself; else the white key it is, taken as a degree of `mask` above
`key`, in the note's own octave, held to the MIDI range. -/
def Keys.quantize (mode mask key note : UInt32) : UInt32 :=
  if mode = 0 then min note 127
  else
    let octave := (min note 127 / 12).toNat   -- the note held to MIDI first: every number below stays small
    let degree := Keys.degree (mask % 4096).toNat (key % 12).toNat (Keys.white note).toNat
    (min (octave * 12 + (key % 12).toNat + degree) 127).toUInt32

/-- C entry: a played note quantized (see `Keys.quantize`). -/
@[export fm1_keys_quantize]
def keysQuantize (mode mask key note : UInt32) : UInt32 := Keys.quantize (mode % 3) mask key note
