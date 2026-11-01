import Firmware.Drum

set_option compiler.extract_closed false

/-! C entry points for `Firmware/Drum.lean`: `voices/drum_glue.c` includes the generated code and calls them
in its sample loop. Settings stay 32-bit numbers throughout: no `Nat` on the sample path. -/

/-- The noise state one step on. -/
@[export fm1_drum_lfsr] def drumLfsr (s : UInt32) : UInt32 := Drum.lfsr s

/-- The noise sample from the state, Q15. -/
@[export fm1_drum_noise] def drumNoise (s : UInt32) : Int32 := Drum.noise s

/-- The sine at a phase, Q15. -/
@[export fm1_drum_sine] def drumSine (phase : UInt32) : Int32 := Fm.sineAt phase

/-- An envelope one sample on. -/
@[export fm1_drum_envelope] def drumEnvelope (env rate : UInt32) : UInt32 := Drum.envelope env rate

/-- A swept increment one sample on. -/
@[export fm1_drum_sweep] def drumSweep (inc target rate : UInt32) : UInt32 := Drum.sweep inc target rate

/-- Where a sweep starts for a tuning and a colour. -/
@[export fm1_drum_sweep_start] def drumSweepStart (target colour : UInt32) : UInt32 :=
  Drum.sweepStart target colour

/-- A one-pole low-pass one sample on, with its coefficient (Q14) from the tables. -/
@[export fm1_drum_one_pole] def drumOnePole (y x : Int32) (a : UInt32) : Int32 :=
  Drum.onePole y x (min a 16384).toInt32

/-- The high-pass: what the low-pass left. -/
@[export fm1_drum_high_pass] def drumHighPass (lp x : Int32) : Int32 := Drum.highPass lp x

/-- A square at a phase. -/
@[export fm1_drum_square] def drumSquare (phase : UInt32) : Int32 := Drum.square phase

/-- The six squares summed. -/
@[export fm1_drum_metal] def drumMetal (p1 p2 p3 p4 p5 p6 : UInt32) : Int32 :=
  Drum.metal p1 p2 p3 p4 p5 p6

/-- An envelope through a level into a gain (Q13). -/
@[export fm1_drum_gain] def drumGain (env level : UInt32) : UInt32 := Drum.gain env level

/-- A signal through a gain (Q13). -/
@[export fm1_drum_scale] def drumScale (x : Int32) (gain : UInt32) : Int32 := Drum.scale x gain

/-- The mix as a 16-bit sample. -/
@[export fm1_drum_saturate] def drumSaturate (x : Int32) : Int16 := Drum.saturate x

/-- The clap's age one sample on. -/
@[export fm1_drum_age_step] def drumAgeStep (age : UInt32) : UInt32 := Drum.ageStep age

/-- 1 when the clap's burst restarts at this age. -/
@[export fm1_drum_clap_retrigger] def drumClapRetrigger (age : UInt32) : UInt32 :=
  if Drum.clapRetrigger age then 1 else 0

/-- The body envelope's rate for a shape at a timbre. -/
@[export fm1_drum_rate] def drumRate (shape timbre : UInt32) : UInt32 := Drum.decay (Drum.rate shape) timbre

/-- The second envelope's rate for a shape at a timbre. -/
@[export fm1_drum_second_rate] def drumSecondRate (shape timbre : UInt32) : UInt32 :=
  Drum.decay (Drum.secondRate shape) timbre

/-- The sweep's rate for a shape. -/
@[export fm1_drum_sweep_rate] def drumSweepRate (shape : UInt32) : UInt32 := Drum.sweepRate shape

/-- An oscillator's increment for a shape at the voice's increment. -/
@[export fm1_drum_tuning] def drumTuning (shape osc voiceInc : UInt32) : UInt32 :=
  Drum.tuning shape osc voiceInc

/-- The body's level (Q13) for a shape at a colour. -/
@[export fm1_drum_level] def drumLevel (shape colour : UInt32) : UInt32 := Drum.level shape colour

/-- The second part's level (Q13) for a shape at a colour. -/
@[export fm1_drum_second_level] def drumSecondLevel (shape colour : UInt32) : UInt32 :=
  Drum.secondLevel shape colour

/-- The band's high-pass coefficient (Q14) for a shape at a colour. -/
@[export fm1_drum_high_coefficient] def drumHighCoefficient (shape colour : UInt32) : UInt32 :=
  Drum.highCoefficient shape colour

/-- The low-pass coefficient (Q14) for a shape. -/
@[export fm1_drum_low_coefficient] def drumLowCoefficient (shape : UInt32) : UInt32 :=
  Drum.lowCoefficient shape

/-- The cymbal's upper band's coefficients (Q14): stage 0 the high-pass, 1 the low-pass. -/
@[export fm1_drum_upper_coefficient] def drumUpperCoefficient (stage : UInt32) : UInt32 :=
  Drum.upperCoefficient stage
