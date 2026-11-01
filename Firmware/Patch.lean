set_option compiler.extract_closed false

/-- One lane of a saved patch: what the knobs set for that lane. Every field is stored as one byte except
`seed`, which takes two. -/
structure PatchLane where
  /-- Rhythm: notes per bar, steps per bar, clock division index. -/
  hits : Nat
  steps : Nat
  speed : Nat
  /-- Scale index, sound index, lowest note, range in semitones. -/
  scale : Nat
  sound : Nat
  low : Nat
  span : Nat
  /-- Note algorithm, play chance, walk size or loop length, loop mutation chance, chord follow. -/
  algo : Nat
  chance : Nat
  amount : Nat
  mutate : Nat
  chord : Nat
  /-- Mix level and reverb send, both in percent. -/
  level : Nat
  send : Nat
  seed : Nat
  /-- The rhythm source (the FEEL page): kind, rotation, accents, automaton rule, ratchet, sub-hits. -/
  feel : Nat
  rotate : Nat
  accents : Nat
  rule : Nat
  ratchet : Nat
  subHits : Nat
  /-- Where the lane sits in the stereo picture: 0 hard left, 50 the middle, 100 hard right. -/
  pan : Nat

/-- A whole patch: the global settings and four lanes. Every field is stored as one byte. -/
structure Patch where
  bpm : Nat
  key : Nat
  progression : Nat
  /-- Bars a chord lasts: 1, 2 or 4. -/
  rate : Nat
  /-- 0 for off, otherwise a scale index plus one. -/
  scaleLock : Nat
  /-- The send reverb: decay, brightness, return, in percent. -/
  reverbTime : Nat
  reverbBright : Nat
  reverbAmount : Nat
  /-- The send delay: note value (0 to 7), feedback, tone, return, the last three in percent. -/
  delayTime : Nat
  delayFeedback : Nat
  delayTone : Nat
  delayAmount : Nat
  lane0 : PatchLane
  lane1 : PatchLane
  lane2 : PatchLane
  lane3 : PatchLane

/-- The lane settings the knobs can produce: 1 to 32 steps with no more hits than steps, 8 speeds, 14 scales,
255 sounds (`NSOUNDS` in `voices/presets.h`; `tools/gen_presets.py --check` keeps this number with it), lowest note 12 to 96, range 1 to 36, 11 algorithms, percentages at most 100, amount 1 to 16, chord
follow 0 to 3, a 16-bit seed, and a rhythm source in range: 4 kinds, a rotation below the steps, no more
accents than hits, a rule byte, a ratchet of 1 to 4 with 1 to `ratchet` sub-hits, and a pan of 0 to 100. -/
def PatchLane.Fits (l : PatchLane) : Prop :=
  l.hits ≤ l.steps ∧ 1 ≤ l.steps ∧ l.steps ≤ 32 ∧ l.speed < 8 ∧ l.scale < 14 ∧ l.sound < 255 ∧
  12 ≤ l.low ∧ l.low ≤ 96 ∧ 1 ≤ l.span ∧ l.span ≤ 36 ∧ l.algo < 11 ∧ l.chance ≤ 100 ∧
  1 ≤ l.amount ∧ l.amount ≤ 16 ∧ l.mutate ≤ 100 ∧ l.chord ≤ 3 ∧ l.level ≤ 100 ∧ l.send ≤ 100 ∧
  l.seed < 65536 ∧ l.feel < 4 ∧ l.rotate < l.steps ∧ l.accents ≤ l.hits ∧ l.rule < 256 ∧
  1 ≤ l.ratchet ∧ l.ratchet ≤ 4 ∧ 1 ≤ l.subHits ∧ l.subHits ≤ l.ratchet ∧ l.pan ≤ 100

instance (l : PatchLane) : Decidable l.Fits := by unfold PatchLane.Fits; infer_instance

/-- The patch settings the knobs can produce: 40 to 240 bpm, 12 keys, 11 progressions, a chord rate of 1, 2 or
4 bars, a scale lock of 0 to 14, reverb settings at most 100, a delay note value below 8 with its other
settings at most 100, and four lanes that fit. -/
def Patch.Fits (p : Patch) : Prop :=
  40 ≤ p.bpm ∧ p.bpm ≤ 240 ∧ p.key < 12 ∧ p.progression < 11 ∧ (p.rate = 1 ∨ p.rate = 2 ∨ p.rate = 4) ∧
  p.scaleLock ≤ 14 ∧ p.reverbTime ≤ 100 ∧ p.reverbBright ≤ 100 ∧ p.reverbAmount ≤ 100 ∧
  p.delayTime < 8 ∧ p.delayFeedback ≤ 100 ∧ p.delayTone ≤ 100 ∧ p.delayAmount ≤ 100 ∧
  p.lane0.Fits ∧ p.lane1.Fits ∧ p.lane2.Fits ∧ p.lane3.Fits

instance (p : Patch) : Decidable p.Fits := by unfold Patch.Fits; infer_instance

/-- The 23 bytes of a lane, in field order; the seed is big-endian. -/
def PatchLane.bytes (l : PatchLane) : List UInt8 :=
  [UInt8.ofNat l.hits, UInt8.ofNat l.steps, UInt8.ofNat l.speed, UInt8.ofNat l.scale, UInt8.ofNat l.sound,
   UInt8.ofNat l.low, UInt8.ofNat l.span, UInt8.ofNat l.algo, UInt8.ofNat l.chance, UInt8.ofNat l.amount,
   UInt8.ofNat l.mutate, UInt8.ofNat l.chord, UInt8.ofNat l.level, UInt8.ofNat l.send,
   UInt8.ofNat (l.seed / 256), UInt8.ofNat (l.seed % 256), UInt8.ofNat l.feel, UInt8.ofNat l.rotate,
   UInt8.ofNat l.accents, UInt8.ofNat l.rule, UInt8.ofNat l.ratchet, UInt8.ofNat l.subHits, UInt8.ofNat l.pan]

/-- A lane read from the front of `bytes`, with the bytes after it; `none` if fewer than 23 are left. -/
def PatchLane.ofBytes : List UInt8 → Option (PatchLane × List UInt8)
  | hits :: steps :: speed :: scale :: sound :: low :: span :: algo :: chance :: amount :: mutate :: chord ::
      level :: send :: seedHigh :: seedLow :: feel :: rotate :: accents :: rule :: ratchet :: subHits :: pan ::
      rest =>
    some ({ hits := hits.toNat, steps := steps.toNat, speed := speed.toNat, scale := scale.toNat,
            sound := sound.toNat, low := low.toNat, span := span.toNat, algo := algo.toNat,
            chance := chance.toNat, amount := amount.toNat, mutate := mutate.toNat, chord := chord.toNat,
            level := level.toNat, send := send.toNat, seed := seedHigh.toNat * 256 + seedLow.toNat,
            feel := feel.toNat, rotate := rotate.toNat, accents := accents.toNat, rule := rule.toNat,
            ratchet := ratchet.toNat, subHits := subHits.toNat, pan := pan.toNat }, rest)
  | _ => none

/-- The 106 bytes of a patch as they sit in a flash slot: the marker byte 0xA7, the layout version 4, the
twelve global settings, then the four lanes. (Version 1 slots, 74 bytes without the rhythm source, version 2,
98 bytes without the delay, and version 3, 102 bytes without the pans, no longer load.) -/
def Patch.bytes (p : Patch) : List UInt8 :=
  [0xA7, 4, UInt8.ofNat p.bpm, UInt8.ofNat p.key, UInt8.ofNat p.progression, UInt8.ofNat p.rate,
   UInt8.ofNat p.scaleLock, UInt8.ofNat p.reverbTime, UInt8.ofNat p.reverbBright, UInt8.ofNat p.reverbAmount,
   UInt8.ofNat p.delayTime, UInt8.ofNat p.delayFeedback, UInt8.ofNat p.delayTone, UInt8.ofNat p.delayAmount]
  ++ p.lane0.bytes ++ p.lane1.bytes ++ p.lane2.bytes ++ p.lane3.bytes

/-- A patch read from exactly the bytes `Patch.bytes` writes; `none` for any other marker, version or
length. -/
def Patch.ofBytes : List UInt8 → Option Patch
  | marker :: version :: bpm :: key :: prog :: rate :: scaleLock :: time :: bright :: amount :: dTime ::
      dFeedback :: dTone :: dAmount :: lanes => do
    guard (marker = 0xA7 ∧ version = 4)
    let (lane0, lanes) ← PatchLane.ofBytes lanes
    let (lane1, lanes) ← PatchLane.ofBytes lanes
    let (lane2, lanes) ← PatchLane.ofBytes lanes
    let (lane3, lanes) ← PatchLane.ofBytes lanes
    guard lanes.isEmpty
    pure { bpm := bpm.toNat, key := key.toNat, progression := prog.toNat, rate := rate.toNat,
           scaleLock := scaleLock.toNat, reverbTime := time.toNat, reverbBright := bright.toNat,
           reverbAmount := amount.toNat, delayTime := dTime.toNat, delayFeedback := dFeedback.toNat,
           delayTone := dTone.toNat, delayAmount := dAmount.toNat, lane0, lane1, lane2, lane3 }
  | _ => none

/-- The bytes to write to a flash slot. (Built from an array, not `List.toByteArray`, whose compiled form
reads `ByteArray.empty`, a global that only module initialisation would fill.) -/
def Patch.encode (p : Patch) : ByteArray := ⟨p.bytes.toArray⟩

/-- The patch in a flash slot, or `none` when the bytes are not a patch or hold a setting outside the knob
ranges (`Patch.Fits`). -/
def Patch.decode (bytes : ByteArray) : Option Patch :=
  match Patch.ofBytes bytes.data.toList with
  | some p => if p.Fits then some p else none
  | none => none
