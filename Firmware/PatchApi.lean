import Firmware.Patch

set_option compiler.extract_closed false

/-- C entry: one lane's settings, in the order of `PatchLane`. -/
@[export fm1_patch_lane_make]
def patchLaneMake (hits steps speed scale sound low span algo chance amount mutate chord level send seed :
    UInt32) : PatchLane :=
  { hits := hits.toNat, steps := steps.toNat, speed := speed.toNat, scale := scale.toNat,
    sound := sound.toNat, low := low.toNat, span := span.toNat, algo := algo.toNat, chance := chance.toNat,
    amount := amount.toNat, mutate := mutate.toNat, chord := chord.toNat, level := level.toNat,
    send := send.toNat, seed := seed.toNat }

/-- C entry: a patch from the global settings and its four lanes. -/
@[export fm1_patch_make]
def patchMake (bpm key progression rate scaleLock reverbTime reverbBright reverbAmount : UInt32)
    (lane0 lane1 lane2 lane3 : PatchLane) : Patch :=
  { bpm := bpm.toNat, key := key.toNat, progression := progression.toNat, rate := rate.toNat,
    scaleLock := scaleLock.toNat, reverbTime := reverbTime.toNat, reverbBright := reverbBright.toNat,
    reverbAmount := reverbAmount.toNat, lane0, lane1, lane2, lane3 }

/-- C entry: the bytes to store. -/
@[export fm1_patch_encode]
def patchEncode (p : Patch) : ByteArray := p.encode

/-- C entry: the patch stored in `bytes`, or `none` (a scalar to C). -/
@[export fm1_patch_decode]
def patchDecode (bytes : ByteArray) : Option Patch := Patch.decode bytes

/-- C entry: global setting `index`, in the order of `Patch`: bpm, key, progression, rate, scale lock, reverb
decay, brightness, return. -/
@[export fm1_patch_field]
def patchField (p : Patch) (index : UInt32) : UInt32 :=
  match index with
  | 0 => p.bpm.toUInt32
  | 1 => p.key.toUInt32
  | 2 => p.progression.toUInt32
  | 3 => p.rate.toUInt32
  | 4 => p.scaleLock.toUInt32
  | 5 => p.reverbTime.toUInt32
  | 6 => p.reverbBright.toUInt32
  | _ => p.reverbAmount.toUInt32

/-- C entry: lane `index` (0 to 3) of the patch. -/
@[export fm1_patch_lane]
def patchLane (p : Patch) (index : UInt32) : PatchLane :=
  match index with
  | 0 => p.lane0
  | 1 => p.lane1
  | 2 => p.lane2
  | _ => p.lane3

/-- C entry: lane setting `index`, in the order of `PatchLane`: hits, steps, speed, scale, sound, low, span,
algo, chance, amount, mutate, chord, level, send, seed. -/
@[export fm1_patch_lane_field]
def patchLaneField (l : PatchLane) (index : UInt32) : UInt32 :=
  match index with
  | 0 => l.hits.toUInt32
  | 1 => l.steps.toUInt32
  | 2 => l.speed.toUInt32
  | 3 => l.scale.toUInt32
  | 4 => l.sound.toUInt32
  | 5 => l.low.toUInt32
  | 6 => l.span.toUInt32
  | 7 => l.algo.toUInt32
  | 8 => l.chance.toUInt32
  | 9 => l.amount.toUInt32
  | 10 => l.mutate.toUInt32
  | 11 => l.chord.toUInt32
  | 12 => l.level.toUInt32
  | 13 => l.send.toUInt32
  | _ => l.seed.toUInt32
