import Firmware.Lane

set_option compiler.extract_closed false

/-- C entry: a lane with the given settings (forced into range). Seeds the random source with `seed`. -/
@[export fm1_lane_make]
def laneMake (hits steps div mask low span seed : UInt32) : Lane :=
  Lane.make hits.toNat steps.toNat div.toNat mask.toNat low.toNat span.toNat seed

/-- C entry: advance one clock tick. -/
@[export fm1_lane_tick]
def laneTick (lane : Lane) : Lane := lane.tick

/-- C entry: change the rhythm, speed and scale of a running lane. -/
@[export fm1_lane_reconfigure]
def laneReconfigure (lane : Lane) (hits steps div mask : UInt32) : Lane :=
  lane.reconfigure hits.toNat steps.toNat div.toNat mask.toNat

/-- C entry: change the rhythm source: kind (0 Euclid, 1 rotate and accent, 2 automaton, 3 ratchet), rotation,
accents, automaton rule, ratchet and sub-hits; `reseed` 1 restarts the automaton from the pattern. -/
@[export fm1_lane_set_rhythm]
def laneSetRhythm (lane : Lane) (kind rotate accents rule ratchet subHits reseed : UInt32) : Lane :=
  lane.setRhythm kind.toNat rotate.toNat accents.toNat rule.toNat ratchet.toNat subHits.toNat (reseed != 0)

/-- C entry: a key the player pressed, for the algorithms that learn (step, markov). -/
@[export fm1_lane_learn]
def laneLearn (lane : Lane) (note : UInt32) : Lane := lane.learn note.toNat

/-- C entry: change how the lane picks notes (algorithm 0 to 10, play chance, amount, mutation chance). -/
@[export fm1_lane_set_notes]
def laneSetNotes (lane : Lane) (algo prob amount mutate : UInt32) : Lane :=
  lane.setNotes algo.toNat prob.toNat amount.toNat mutate.toNat

/-- C entry: stop the sounding note (the clock stopped); `fm1_lane_off` then reports it. -/
@[export fm1_lane_silence]
def laneSilence (lane : Lane) : Lane := lane.silence

/-- A note number for C, or 255 for none. -/
def Lane.noteOrNone (note : Option Nat) : UInt32 := (note.getD 255).toUInt32

/-- C entry: the note the last tick started, or 255. -/
@[export fm1_lane_on]
def laneOn (lane : Lane) : UInt32 := Lane.noteOrNone lane.on

/-- C entry: the note the last tick stopped, or 255. -/
@[export fm1_lane_off]
def laneOff (lane : Lane) : UInt32 := Lane.noteOrNone lane.off

/-- C entry: is the note the last tick started accented (1) or not (0)? -/
@[export fm1_lane_loud]
def laneLoud (lane : Lane) : UInt32 := if lane.loud then 1 else 0

/-- C entry: the step the lane is on. -/
@[export fm1_lane_step]
def laneStep (lane : Lane) : UInt32 := lane.step.toUInt32

/-- C entry: does step `index` of the bar play a note (1) or rest (0)? -/
@[export fm1_lane_hit_at]
def laneHitAt (lane : Lane) (index : UInt32) : UInt32 :=
  if Rhythm.hit lane.rhythm lane.hits lane.steps index.toNat then 1 else 0

/-- C entry: is step `index` of the bar an accented hit (1) or not (0)? -/
@[export fm1_lane_accent_at]
def laneAccentAt (lane : Lane) (index : UInt32) : UInt32 :=
  if Rhythm.accent lane.rhythm lane.hits lane.steps index.toNat then 1 else 0
