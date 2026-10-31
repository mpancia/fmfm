set_option compiler.extract_closed false

/-- Is `note` in the scale `mask`? Bit 0 of `mask` is C, bit 1 is C sharp, up to bit 11 for B. -/
def Quantizer.inScale (mask note : Nat) : Bool := mask.testBit (note % 12)

/-- The in-scale note exactly `dist` semitones from `note`: below first, then above. -/
def Quantizer.at (mask note dist : Nat) : Option Nat :=
  if dist ≤ note && inScale mask (note - dist) then some (note - dist)
  else if inScale mask (note + dist) then some (note + dist)
  else none

/-- Try distances `dist`, `dist + 1`, ... while `tries` last; give back `note` if none fits. -/
def Quantizer.search (mask note : Nat) : Nat → Nat → Nat
  | 0, _ => note
  | tries + 1, dist =>
    match Quantizer.at mask note dist with
    | some found => found
    | none => Quantizer.search mask note tries (dist + 1)

/-- The nearest note in the scale, looking up to 6 semitones either way (below wins a tie).
An empty scale leaves the note as it is. -/
def Quantizer.snap (mask note : Nat) : Nat := Quantizer.search mask note 7 0
