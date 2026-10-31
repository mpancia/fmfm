set_option compiler.extract_closed false

/-- Random numbers from a 32-bit linear congruential generator. Every 32-bit value is a valid state,
so there is no bad seed, and the same seed always gives the same music. -/
def Random.next (state : UInt32) : UInt32 := state * 1664525 + 1013904223

/-- A number from 0 to `limit - 1`, taken from the high bits of `state` (the low bits repeat too quickly).
`limit` must be between 1 and 65535. -/
def Random.below (state limit : UInt32) : UInt32 := ((state >>> 16) * limit) >>> 16
