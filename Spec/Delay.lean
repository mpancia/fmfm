import Firmware.Delay

/-- An echo going round the delay with nothing new on the send and no filtering: what the line stores, read
back. `n` hops from a sample `echo`; hop 0 is the sample itself. The low-pass only ever brings a value
between the state and the echo (`reverb_lowpass_stays_between`), so this is the loudest case. -/
def Delay.hops (echo feedback : Int32) : Nat → Int32
  | 0 => echo
  | n + 1 => Delay.fetch (Delay.store (Delay.input 0 (Delay.hops echo feedback n) feedback))
