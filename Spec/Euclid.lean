import Firmware.Euclid

/-- How many of the first `upTo` steps of the pattern play a note. -/
def Euclid.countHits (hits steps : Nat) : Nat → Nat
  | 0 => 0
  | upTo + 1 => Euclid.countHits hits steps upTo + if Euclid.hit hits steps upTo then 1 else 0
