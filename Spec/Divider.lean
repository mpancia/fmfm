import Firmware.Divider

/-- Run a divide-by-`div` counter for `ticks` clock ticks from `count`.
Returns the final count and how many output pulses it gave. -/
def Divider.run (div count : Nat) : Nat → Nat × Nat
  | 0 => (count, 0)
  | ticks + 1 =>
    let (next, pulse) := Divider.tick div count
    let (last, pulses) := Divider.run div next ticks
    (last, pulses + if pulse then 1 else 0)
