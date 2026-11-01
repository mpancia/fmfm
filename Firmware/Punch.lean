set_option compiler.extract_closed false

/-!
Punch-in effects (REC): while the PUNCH page is up, the keys are momentary effects on the whole performance,
as the OP-XY's punch-in FX: a key held is an effect on, a key let go is the effect gone. Everything here is a
pure function of the keys held and the settings underneath, so there is no effect state to undo: when no
key is
held every function hands back exactly what it was given (`punch_nothing_held_changes_nothing`). The lower
octave (keys 0 to 11, F3 to E4): HALF and DOUBLE time, STUTTER and ROLL (notes re-struck every period), OCTAVE
down and up and SHIFT (a transposition), GATE (the mix chopped), CRUSH (the mix held every `n`th sample),
WASH (the reverb full up), THROW (the delay full up), BREAK (every lane muted). Keys 12 to 15 mute lanes 1 to
4. `fw/firmware/src/dinghy.c` reads these each tick and each sample.
-/

/-- Is key `k` held? Bit `k` of the keys word. -/
@[inline] def Punch.held (keys k : UInt32) : Bool := (keys >>> k) &&& 1 = 1

/-- The clock's speed in percent: HALF (key 0) halves it, DOUBLE (key 1) doubles it. -/
@[inline] def Punch.tempoPercent (keys : UInt32) : UInt32 :=
  if Punch.held keys 0 then 50 else if Punch.held keys 1 then 200 else 100

/-- The STUTTER period in ticks from the knob's choice: 0 is an eighth (12 ticks), 1 a sixteenth (6), 2 a
thirty-second (3). -/
@[inline] def Punch.stutterChoice (choice : UInt32) : UInt32 := if choice = 0 then 12 else if choice = 1
    then 6 else 3

/-- The re-strike period in ticks, 0 for none: ROLL (key 3) is every three ticks, STUTTER (key 2) the
knob's. -/
@[inline] def Punch.stutterPeriod (keys choice : UInt32) : UInt32 :=
  if Punch.held keys 3 then 3 else if Punch.held keys 2 then Punch.stutterChoice choice else 0

/-- Does this tick re-strike every sounding note? -/
@[inline] def Punch.restrike (keys choice tick : UInt32) : Bool :=
  let period := Punch.stutterPeriod keys choice
  period ≠ 0 && tick % period = 0

/-- The transposition in semitones: OCTAVE down (key 4), OCTAVE up (key 5), SHIFT (key 6) by the knob's
semitones (at most 12); they add. -/
@[inline] def Punch.transpose (keys shift : UInt32) : Int32 :=
  (if Punch.held keys 4 then -12 else 0) + (if Punch.held keys 5 then 12 else 0) +
    (if Punch.held keys 6 then (min shift 12).toInt32 else 0)

/-- A note to play, transposed and held to the MIDI range. -/
@[inline] def Punch.note (keys shift note : UInt32) : UInt32 :=
  let moved := (min note 127).toInt32 + Punch.transpose keys shift
  if moved < 0 then 0 else if moved > 127 then 127 else moved.toUInt32

/-- The GATE's period in ticks (key 7), 0 for none: the knob chooses an eighth (12) or a sixteenth (6). -/
@[inline] def Punch.gatePeriod (keys choice : UInt32) : UInt32 :=
  if Punch.held keys 7 then (if choice = 0 then 12 else 6) else 0

/-- Is the gate open on this tick? Open for the first half of every period; always when there is no gate. -/
@[inline] def Punch.gateOpen (keys choice tick : UInt32) : Bool :=
  let period := Punch.gatePeriod keys choice
  period = 0 || tick % period < period / 2

/-- The gain the gate is heading for, Q15: one when open, nothing when shut. -/
@[inline] def Punch.gateTarget (isOpen : Bool) : UInt32 := if isOpen then 32768 else 0

/-- The gate's gain one sample on: 512 (a 64th of full scale) toward its target, so a chop takes 64 samples,
a millisecond and a half, and never clicks. -/
@[inline] def Punch.gateStep (gain target : UInt32) : UInt32 :=
  if gain < target then min target (gain + 512) else if target < gain then gain - min (gain - target) 512
else gain

/-- A mix sample through the gate: the sample (within the mix's limit of 2^19) times the gain (Q15). -/
@[inline] def Punch.gateSample (sample : Int32) (gain : UInt32) : Int32 :=
  ((sample >>> 4) * gain.toInt32) >>> 11

/-- CRUSH (key 8): the mix held for `factor` samples at a time, from the knob (2 to 8); 1 (every sample its
own)
when the key is up. -/
@[inline] def Punch.crushFactor (keys factor : UInt32) : UInt32 :=
  if Punch.held keys 8 then max 2 (min 8 factor) else 1

/-- A mix sample through the crush: a fresh sample on every `factor`th sample, the held one between. -/
@[inline] def Punch.crushSample (factor index : UInt32) (heldSample sample : Int32) : Int32 :=
  if index % factor = 0 then sample else heldSample

/-- The reverb amount: full with WASH (key 9) held, else the setting. -/
@[inline] def Punch.reverbAmount (keys base : UInt32) : UInt32 := if Punch.held keys 9 then 100 else base

/-- The delay amount: full with THROW (key 10) held, else the setting. -/
@[inline] def Punch.delayAmount (keys base : UInt32) : UInt32 := if Punch.held keys 10 then 100 else base

/-- Is lane `lane` (0 to 3) muted by a key: BREAK (key 11) mutes every lane, keys 12 to 15 one each. -/
@[inline] def Punch.laneMuted (keys lane : UInt32) : Bool :=
  Punch.held keys 11 || Punch.held keys (12 + lane % 4)
