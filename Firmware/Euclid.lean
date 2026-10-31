set_option compiler.extract_closed false

/-- Does step `step` of a bar of `steps` steps with `hits` hits play a note? A step plays when the running
total `(step + 1) * hits / steps` goes up, which spreads the hits as evenly as whole steps allow.
The pattern repeats every `steps` steps. -/
def Euclid.hit (hits steps step : Nat) : Bool :=
  (step + 1) * hits / steps != step * hits / steps
