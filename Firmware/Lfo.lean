set_option compiler.extract_closed false

/-- A slow modulator: a 32-bit phase that wraps once a cycle. -/
def Lfo.advance (phase step : UInt32) : UInt32 := phase + step

/-- The modulator's value at `phase`, as a triangle from 0 up to 65535 and back. -/
def Lfo.triangle (phase : UInt32) : UInt32 :=
  let half := phase >>> 15
  if half < 65536 then half else 131071 - half

/-- Apply a modulator to a value: `base` moved by up to `depth` either way (both 0 to 100 percent) at the
triangle's position, and kept between 0 and 100. -/
def Lfo.modulate (base depth tri : UInt32) : UInt32 :=
  let swing := (depth * tri) / 32768                      -- 0 .. 2 * depth
  let raised := base + swing
  if raised < depth then 0 else min 100 (raised - depth)

/-- C entry: the phase after one step. -/
@[export fm1_lfo_advance]
def lfoAdvance (phase step : UInt32) : UInt32 := Lfo.advance phase step

/-- C entry: the modulated percentage. -/
@[export fm1_lfo_modulate]
def lfoModulate (base depth phase : UInt32) : UInt32 :=
  Lfo.modulate (min base 100) (min depth 100) (Lfo.triangle phase)
