import Firmware.Analog

/-- The saw's phase after `n` samples with no sync pulse, at a steady step. The other oscillators move their
phase the same way. -/
def Analog.freeRun (phase inc : UInt32) : Nat → UInt32
  | 0 => phase
  | n + 1 => (Analog.saw (Analog.freeRun phase inc n) inc 0 0).phase
