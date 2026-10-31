set_option compiler.extract_closed false

/-- One clock tick of a divide-by-`div` counter. `count` is the ticks since the last output pulse.
Returns the new count and whether to pulse now. -/
def Divider.tick (div count : Nat) : Nat × Bool :=
  if count + 1 ≥ div then (0, true) else (count + 1, false)
