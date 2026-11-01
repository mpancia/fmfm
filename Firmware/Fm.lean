set_option compiler.extract_closed false

/-!
A four-operator FM voice, ours from the first line (the Braids shapes are ports). Each operator is a sine
read from a 32-bit phase; an operator's phase is pushed by the outputs of the operators that modulate it (the
algorithm says which), scaled by a depth; the carriers are summed. Every operator has an exponential envelope
started at the strike, so a modulator can fade and leave the carrier clean (the electric piano, the bell), and
operator 4 can feed itself back (the brass, the clang). Phase arithmetic is modulo 2^32, so modulation can
never read outside the table, only round the circle: that is the whole reason FM is cheap to get right.

Fixed point: phases and increments in 32 bits (one cycle is 2^32), samples and levels in Q15 (32767 is one),
envelopes in Q24 (16777216 is one), ratios in Q8 (256 is one), depths in phase units per unit of modulator.
`voices/fm_glue.c` keeps the state and runs the loop; the arithmetic of a sample is here.
-/

/-- A quarter sine by polynomial: for `x` from 0 to 32767 (Q15, a quarter cycle),
`sin (π x / 2) ≈ x (a - x² (b - c x²))` with `a, b, c` the usual degree-5 fit (1.5708, 0.6460, 0.0797; within
0.0002 of the sine, a hair over one at the top, held to 32767). Six multiplies,
    no table: nothing to read past,
and the kernel can evaluate it, so `fm_sine_bounded` is a check over every input rather than trust in a
table. -/
@[inline] def Fm.quarter (x : UInt32) : UInt32 :=
  let x2 := (x * x) >>> 15
  let inner := (21167 : UInt32) - ((x2 * 2611) >>> 15)
  let outer := (51472 : UInt32) - ((x2 * inner) >>> 15)
  min ((x * outer) >>> 15) 32767

/-- The position in the quarter for a phase: the top two bits pick the quadrant,
    the next fifteen the position,
mirrored in the second and fourth quadrants. -/
@[inline] def Fm.folded (phase : UInt32) : UInt32 :=
  let x := (phase >>> 15) &&& 0x7FFF
  if (phase >>> 30) &&& 1 = 1 then 32767 - x else x

/-- The sine at a 32-bit phase, Q15: the quarter value at the folded position, negated in the second half. -/
@[inline] def Fm.sineAt (phase : UInt32) : Int32 :=
  let y := (Fm.quarter (Fm.folded phase)).toInt32
  if phase >>> 30 ≥ 2 then -y else y

/-- A modulator's push on the phase of the operator it modulates: its output (Q15) times its depth, added to
the pushes of the other modulators. Modular: a push past the end of the cycle comes round to the start, as a
sine does, so the sum can never point outside the cycle whatever the depths. -/
@[inline] def Fm.push (sofar : UInt32) (modulator : Int32) (depth : UInt32) : UInt32 :=
  sofar + modulator.toUInt32 * depth

/-- An operator's output, Q15: the sine at its phase pushed by `push`, through its envelope (Q24). -/
@[inline] def Fm.operator (phase push envelope : UInt32) : Int32 :=
  (Fm.sineAt (phase + push) * (envelope >>> 8).toInt32) >>> 16

/-- A carrier's share of the sample: its output at its level (Q15). -/
@[inline] def Fm.carry (out : Int32) (level : UInt32) : Int32 := (out * level.toInt32) >>> 15

/-- An envelope one block (16 samples) on: a share `rate / 2^20` of what is left goes, so the time constant is
`2^20 / rate` blocks (rate 24 is about 16 seconds at 44.1 kHz, 384 one second). Rate 0 holds. -/
@[inline] def Fm.envelopeStep (envelope rate : UInt32) : UInt32 :=
  envelope - (((envelope >>> 8) * rate) >>> 12)

/-- An operator's phase increment: the voice's increment (from the pitch) times the operator's ratio (Q8),
held below half a cycle a sample, the highest frequency a sample rate can carry. -/
@[inline] def Fm.increment (voiceInc ratio : UInt32) : UInt32 :=
  let product := (voiceInc.toUInt64 * ratio.toUInt64) >>> 8
  if product ≥ 0x80000000 then 0x80000000 else product.toUInt32

/-- The carriers' sum into a sample, Q15: each carrier at most one, four at most four, held to one. -/
@[inline] def Fm.saturate (x : Int32) : Int16 :=
  if x > 32767 then 32767 else if x < -32767 then -32767 else x.toInt16

/-! The algorithms: which operators modulate which (an operator is only ever modulated by higher-numbered
ones, so a sample is computed from operator 4 down and every modulator is fresh), and which are carriers.
0: 4 → 3 → 2 → 1. 1: 4 → 3 → 1, 2 → 1. 2: 2 → 1 and 4 → 3, two stacks. 3: 4 → 1, 2, 3. 4: 2, 3, 4 → 1.
5: 4 → 3; 1, 2, 3 carry. 6: 3 → 2 → 1; 4 carries. 7: all four carry. Operator 4 may feed itself back in any
of them (`Fm.feedbackDepth`). -/

/-- Does operator `source` modulate operator `op` in algorithm `alg`? (Operators 1 to 4.) The settings are
32-bit numbers throughout: no `Nat` on the chip's sample path. -/
@[inline] def Fm.modulates (alg op source : UInt32) : Bool :=
  match alg % 8, op, source with
  | 0, 1, 2 | 0, 2, 3 | 0, 3, 4 => true
  | 1, 1, 2 | 1, 1, 3 | 1, 3, 4 => true
  | 2, 1, 2 | 2, 3, 4 => true
  | 3, 1, 4 | 3, 2, 4 | 3, 3, 4 => true
  | 4, 1, 2 | 4, 1, 3 | 4, 1, 4 => true
  | 5, 3, 4 => true
  | 6, 1, 2 | 6, 2, 3 => true
  | _, _, _ => false

/-- Is operator `op` a carrier (heard) in algorithm `alg`? -/
@[inline] def Fm.carries (alg op : UInt32) : Bool :=
  match alg % 8, op with
  | 0, 1 | 1, 1 | 4, 1 => true
  | 2, 1 | 2, 3 => true
  | 3, 1 | 3, 2 | 3, 3 => true
  | 5, 1 | 5, 2 | 5, 3 => true
  | 6, 1 | 6, 4 => true
  | 7, 1 | 7, 2 | 7, 3 | 7, 4 => true
  | _, _ => false

/-! The shapes: eight FM voices after the Braids ones (shape 48 on). For each operator a ratio (Q8), a
modulation depth (phase units per unit of modulator, so 20861 is one radian), a carrier level (Q15) and an
envelope rate (per `Fm.envelopeStep`, a block at a time: 0 holds, 384 is a time constant of a second,
    3840 a tenth). -/

/-- The shape's algorithm. -/
@[inline] def Fm.algorithm (shape : UInt32) : UInt32 :=
  match shape % 8 with
  | 0 => 2 | 1 => 4 | 2 => 0 | 3 => 0 | 4 => 3 | 5 => 6 | 6 => 7 | _ => 1

/-- Operator `op`'s frequency ratio, Q8. -/
@[inline] def Fm.ratio (shape op : UInt32) : UInt32 :=
  match shape % 8, op with
  | 0, 1 => 256 | 0, 2 => 256 | 0, 3 => 256 | 0, 4 => 3584           -- piano: 1, 1; 1, 14 (the tine)
  | 1, 1 => 256 | 1, 2 => 896 | 1, 3 => 1843 | 1, 4 => 358           -- bell: 1; 3.5, 7.2, 1.4
  | 2, 1 => 256 | 2, 2 => 256 | 2, 3 => 512 | 2, 4 => 256            -- bass: 1, 1, 2, 1
  | 3, 1 => 256 | 3, 2 => 256 | 3, 3 => 256 | 3, 4 => 256            -- brass: all 1
  | 4, 1 => 256 | 4, 2 => 512 | 4, 3 => 1024 | 4, 4 => 256           -- glass: carriers 1, 2, 4; modulator 1
  | 5, 1 => 256 | 5, 2 => 1024 | 5, 3 => 2560 | 5, 4 => 1024         -- mallet: 1; 4, 10; a 4 carrier
  | 6, 1 => 256 | 6, 2 => 512 | 6, 3 => 768 | 6, 4 => 1024           -- organ: 1, 2, 3, 4
  | _, 1 => 256 | _, 2 => 362 | _, 3 => 724 | _, 4 => 1448           -- clang: 1, √2, 2√2, 4√2
  | _, _ => 256

/-- Operator `op`'s modulation depth at the nominal timbre. -/
@[inline] def Fm.depth (shape op : UInt32) : UInt32 :=
  match shape % 8, op with
  | 0, 2 => 70000 | 0, 4 => 25000
  | 1, 2 => 50000 | 1, 3 => 36000 | 1, 4 => 40000
  | 2, 2 => 80000 | 2, 3 => 40000 | 2, 4 => 24000
  | 3, 2 => 50000 | 3, 3 => 36000 | 3, 4 => 24000
  | 4, 4 => 30000
  | 5, 2 => 60000 | 5, 3 => 36000
  | 7, 2 => 90000 | 7, 3 => 70000 | 7, 4 => 60000
  | _, _ => 0

/-- Operator `op`'s level as a carrier, Q15. -/
@[inline] def Fm.level (shape op : UInt32) : UInt32 :=
  match shape % 8, op with
  | 0, 1 => 22000 | 0, 3 => 10000
  | 1, 1 => 30000
  | 2, 1 => 30000
  | 3, 1 => 30000
  | 4, 1 => 16000 | 4, 2 => 10000 | 4, 3 => 6000
  | 5, 1 => 24000 | 5, 4 => 8000
  | 6, 1 => 16000 | 6, 2 => 8000 | 6, 3 => 5000 | 6, 4 => 3000
  | 7, 1 => 30000
  | _, _ => 0

/-- Operator `op`'s envelope rate, Q16 a sample. -/
@[inline] def Fm.rate (shape op : UInt32) : UInt32 :=
  match shape % 8, op with
  | 0, 2 => 960 | 0, 3 => 480 | 0, 4 => 6400
  | 1, 2 => 400 | 1, 3 => 960 | 1, 4 => 640
  | 2, 2 => 1920 | 2, 3 => 3200 | 2, 4 => 4800
  | 3, 2 => 128 | 3, 3 => 192 | 3, 4 => 256
  | 4, 4 => 320
  | 5, 2 => 4000 | 5, 3 => 8000 | 5, 4 => 11200
  | 7, 2 => 800 | 7, 3 => 1120 | 7, 4 => 1440
  | _, _ => 0

/-- Operator 4's feedback depth at full colour. -/
@[inline] def Fm.feedbackDepth (shape : UInt32) : UInt32 :=
  match shape % 8 with
  | 3 => 30000 | 7 => 60000 | 2 => 16000 | _ => 8000

/-- A modulation depth scaled by the timbre (Q15; 16384 is the shape's own depth, 32767 twice it). -/
@[inline] def Fm.scaledDepth (depth timbre : UInt32) : UInt32 := (depth * timbre) >>> 14

/-- The feedback depth scaled by the colour (Q15; 0 is none). -/
@[inline] def Fm.scaledFeedback (shape colour : UInt32) : UInt32 :=
  (Fm.feedbackDepth shape * colour) >>> 15
