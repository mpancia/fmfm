import Firmware.Drum

/-! Definitions for the statements about the drum voice (`Proofs/Drum.lean`): runs of the noise generator and
the envelope, and each drum family's sample as the glue composes it, stage for stage. -/

/-- The noise state after `n` steps. -/
def Drum.lfsrAfter (s : UInt32) : Nat → UInt32
  | 0 => s
  | n + 1 => Drum.lfsr (Drum.lfsrAfter s n)

/-- Whether the next `n` states on from `s` all differ from `seed`. -/
def Drum.orbitAvoids (seed s : UInt32) : Nat → Bool
  | 0 => true
  | n + 1 => Drum.lfsr s != seed && Drum.orbitAvoids seed (Drum.lfsr s) n

/-- The envelope after `n` samples at `rate`. -/
def Drum.envelopeAfter (env rate : UInt32) : Nat → UInt32
  | 0 => env
  | n + 1 => Drum.envelope (Drum.envelopeAfter env rate n) rate

/-- A band-pass on a signal then a gain, as the glue runs it for the hi-hats, the cowbell and each of the
cymbal's bands: the high-pass (what the first low-pass leaves of the input), the second low-pass, the gain. -/
def Drum.bandOut (input lp1 lp2 aH aL : Int32) (gain : UInt32) : Int32 :=
  Drum.scale (Drum.onePole lp2 (Drum.highPass (Drum.onePole lp1 input aH) input) aL) gain

/-- The kick's and toms' mix, as the glue runs it: the sine through its gain plus the noise through a low-pass
and its gain. -/
def Drum.tunedOut (phase noise : UInt32) (lp aL : Int32) (gA gB : UInt32) : Int32 :=
  Drum.scale (Fm.sineAt phase) gA + Drum.scale (Drum.onePole lp (Drum.noise noise) aL) gB

/-- The snare's mix: two sines through a gain plus the noise through a high-pass and its gain. -/
def Drum.snareOut (p1 p2 noise : UInt32) (lp aH : Int32) (gA gB : UInt32) : Int32 :=
  Drum.scale (Fm.sineAt p1 + Fm.sineAt p2) gA +
    Drum.scale (Drum.highPass (Drum.onePole lp (Drum.noise noise) aH) (Drum.noise noise)) gB

/-- The clap's mix: the noise through the band, through the tail's gain and the burst's. -/
def Drum.clapOut (noise : UInt32) (lp1 lp2 aH aL : Int32) (gA gB : UInt32) : Int32 :=
  Drum.bandOut (Drum.noise noise) lp1 lp2 aH aL gA + Drum.bandOut (Drum.noise noise) lp1 lp2 aH aL gB

/-- The cymbal's mix: the metal through two bands, each with its gain. -/
def Drum.cymbalOut (p1 p2 p3 p4 p5 p6 : UInt32) (lp1 lp2 lp3 lp4 aH aL uH uL : Int32)
    (gA gB : UInt32) : Int32 :=
  Drum.bandOut (Drum.metal p1 p2 p3 p4 p5 p6) lp1 lp2 aH aL gA +
    Drum.bandOut (Drum.metal p1 p2 p3 p4 p5 p6) lp3 lp4 uH uL gB
