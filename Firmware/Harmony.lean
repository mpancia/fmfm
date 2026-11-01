set_option compiler.extract_closed false

/-- Scale number `scale` as a 12-bit mask: bit 0 is the root, bit 11 the major seventh. The order matches the
names on the screen: major, minor, pentatonic major, pentatonic minor, dorian, harmonic minor, whole tone,
chromatic, phrygian, lydian, blues, ukrainian dorian, double harmonic, harmonic major. Any other number is
chromatic. A function rather than a list: a list would be a global that only the module initialiser fills, and
the firmware runs no initialisers. -/
def Harmony.scale : Nat → Nat
  | 0 => 0xAB5 | 1 => 0x5AD | 2 => 0x295 | 3 => 0x4A9 | 4 => 0x6AD | 5 => 0x9AD | 6 => 0x555
  | 8 => 0x5AB | 9 => 0xAD5 | 10 => 0x4E9 | 11 => 0x6CD | 12 => 0x9B3 | 13 => 0x9B5
  | _ => 0xFFF

/-- A scale mask turned up by `root` semitones (0 to 11). -/
def Harmony.rotate (mask root : Nat) : Nat :=
  ((mask <<< root) ||| (mask >>> (12 - root))) &&& 0xFFF

/-- The notes of `mask` from `root` upwards, as pitch classes. -/
def Harmony.tones (mask root : Nat) : List Nat :=
  (List.range 12).filter (fun d => mask.testBit ((root + d) % 12)) |>.map (fun d => (root + d) % 12)

/-- The chord on `root`: the first, third and fifth note of the scale from there (fewer if the scale is short).
An empty scale gives the scale back. -/
def Harmony.triad (mask root : Nat) : Nat :=
  let tones := Harmony.tones mask root
  if tones.isEmpty then mask
  else (List.range 3).foldl (fun acc d => acc ||| (1 <<< tones.getD ((d * 2) % tones.length) 0)) 0

/-- The mask a lane plays in: scale number `scale`, in `key`, moved to the chord `chordRoot` semitones above it
when `follow` is 1 (scale) or 2 (triad). -/
def Harmony.laneMask (scale key chordRoot follow : Nat) : Nat :=
  let mask := Harmony.scale scale
  let root := (key + (if follow = 0 then 0 else chordRoot)) % 12
  let turned := Harmony.rotate mask root
  if follow = 2 then Harmony.triad turned root else turned

/-- The chord progressions on GLO > HARMONY, as scale degrees (0 is the key's root, 4 the fifth note of the
scale), four chords each, chord `s`: 0 is no progression, then 1-4-5-1, 1-5-6-4, 6-4-1-5, 2-5-1-1, 1-6-3-7,
1-3-4-5 and 1-6-2-5. Degrees, not semitones, so the same progression fits every scale: 1-4-5-1 is I IV V in a
major key and i iv v in a minor one. -/
def Harmony.degree (p s : Nat) : Nat :=
  match p, s % 4 with
  | 1, 1 => 3 | 1, 2 => 4
  | 2, 1 => 4 | 2, 2 => 5 | 2, 3 => 3
  | 3, 0 => 5 | 3, 1 => 3 | 3, 3 => 4
  | 4, 0 => 1 | 4, 1 => 4
  | 5, 1 => 5 | 5, 2 => 2 | 5, 3 => 6
  | 6, 1 => 2 | 6, 2 => 3 | 6, 3 => 4
  | 7, 1 => 5 | 7, 2 => 1 | 7, 3 => 4
  | _, _ => 0

/-- The root of chord `s` of progression `p` in scale number `scale`, as semitones above the key: the scale's
note at that degree, counting round for scales with fewer than seven notes. -/
def Harmony.chordRoot (scale p s : Nat) : Nat :=
  let tones := Harmony.tones (Harmony.scale scale) 0
  tones.getD (Harmony.degree p s % tones.length) 0

/-- C entry: the chord root for the lanes and the screen (see `Harmony.chordRoot`). -/
@[export fm1_harmony_chord_root]
def harmonyChordRoot (scale progression step : UInt32) : UInt32 :=
  (Harmony.chordRoot (scale.toNat % 14) (progression.toNat % 8) (step.toNat % 4)).toUInt32

/-- C entry: the mask for a lane (see `Harmony.laneMask`). -/
@[export fm1_harmony_mask]
def harmonyMask (scale key chordRoot follow : UInt32) : UInt32 :=
  (Harmony.laneMask (scale.toNat % 14) (key.toNat % 12) (chordRoot.toNat % 12) (follow.toNat % 3)).toUInt32
