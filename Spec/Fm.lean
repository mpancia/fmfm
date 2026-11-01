import Firmware.Fm

/-! Definitions for the statements about the FM voice (`Proofs/Fm*.lean`): what a run of samples does to a
phase and an envelope, and the position a phase reads the sine at. -/

/-- The phase after `n` samples from `phase`, stepping by `inc` (modulo 2^32, as the voice does). -/
def Fm.phaseAfter (phase inc : UInt32) : Nat → UInt32
  | 0 => phase
  | n + 1 => Fm.phaseAfter phase inc n + inc

/-- The envelope after `k` blocks at `rate`. -/
def Fm.envelopeAfter (envelope rate : UInt32) : Nat → UInt32
  | 0 => envelope
  | k + 1 => Fm.envelopeStep (Fm.envelopeAfter envelope rate k) rate

/-- The position a phase reads the sine at: its top 17 bits, the quadrant and the place in it. `Fm.sineAt`
depends on the phase only through this. -/
def Fm.position (phase : UInt32) : UInt32 := phase >>> 15
