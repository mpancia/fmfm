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

/-- C entry: change how the lane picks notes (algorithm 0 to 5, play chance, walk size or loop length, loop
mutation chance). -/
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

/-- C entry: the step the lane is on. -/
@[export fm1_lane_step]
def laneStep (lane : Lane) : UInt32 := lane.step.toUInt32

/-- C entry: does step `index` of the bar play a note (1) or rest (0)? -/
@[export fm1_lane_hit_at]
def laneHitAt (lane : Lane) (index : UInt32) : UInt32 :=
  if Euclid.hit lane.hits lane.steps index.toNat then 1 else 0
