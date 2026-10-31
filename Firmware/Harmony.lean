set_option compiler.extract_closed false

/-- The scales, as 12-bit masks: bit 0 is the root, bit 11 the major seventh. The order matches the names on
the screen: major, minor, pentatonic major, pentatonic minor, dorian, harmonic minor, whole tone, chromatic,
phrygian, lydian, blues, ukrainian dorian, double harmonic, harmonic major. -/
def Harmony.scales : List Nat :=
  [0xAB5, 0x5AD, 0x295, 0x4A9, 0x6AD, 0x9AD, 0x555, 0xFFF, 0x5AB, 0xAD5, 0x4E9, 0x6CD, 0x9B3, 0x9B5]

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
  let mask := Harmony.scales.getD scale 0xFFF
  let root := (key + (if follow = 0 then 0 else chordRoot)) % 12
  let turned := Harmony.rotate mask root
  if follow = 2 then Harmony.triad turned root else turned

/-- C entry: the mask for a lane (see `Harmony.laneMask`). -/
@[export fm1_harmony_mask]
def harmonyMask (scale key chordRoot follow : UInt32) : UInt32 :=
  (Harmony.laneMask (scale.toNat % 14) (key.toNat % 12) (chordRoot.toNat % 12) (follow.toNat % 3)).toUInt32
