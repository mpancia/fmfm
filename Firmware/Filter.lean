set_option compiler.extract_closed false

/-!
A resonant filter for every voice: a state-variable filter in the trapezoidal (Zavalishin / Cytomic) form,
run by `dinghy.c`'s `render_voice` on each voice's 16-bit sample stream after the engine (a Braids shape or
the FM voice) has made it. Two integrator states `ic1`, `ic2`; a sample gives the band-pass node `v1` and the
low-pass node `v2`, the output is one of low, band or high, and the states move to `2 v - ic`.

Fixed point, all in 32 bits: samples 16-bit; the states and the nodes held to ±65536 (twice full scale) after
every update, so they are bounded by construction and a 15-bit coefficient times a state fits in 31 bits
(32767 × 65536 < 2^31); `g` (the cutoff, `tan (π f / fs)`), `a1` and `a2` in Q15 (32768 is one, all at most
32767); `k` (the damping, `2 - 2 r`) in Q13 (16384 is 2.0). Products on the sample path: `a1 · ic1`,
`a2 · ((x - ic2) / 2)`, `g · v1` (each at most 32767 × 65536) and `k · v1` (at most 16384 × 65536); the sums
stay under 2^19. `Proofs/Filter.lean` checks all of that.

With the cutoff fully open (100) and no resonance the filter is bypassed outright (`Filter.active` is false
and `Filter.step` hands the sample back), so every sound with the default settings is bit for bit what it was.
-/

/-- `y` held to `±bound`: a saturation, never a wrap. -/
@[inline] def Filter.hold (y bound : Int32) : Int32 :=
  if y > bound then bound else if y < -bound then -bound else y

/-- Is the filter doing anything? Not with the cutoff fully open (100 or more) and no resonance: that is the
default, and `Filter.step` passes the sample through untouched. One test a block in the C. -/
@[inline] def Filter.active (cutoff resonance : UInt32) : Bool := !(cutoff ≥ 100 && resonance == 0)

/-- The cutoff coefficient `g = tan (π f / fs)` in Q15 for a cutoff setting 0 to 100: a log sweep from 30 Hz
(setting 0) to 11 kHz (setting 100), `round (32768 · tan (π · 30 · (11000 / 30)^(c / 100) / 44100))`. 11 kHz
is a quarter of the sample rate, where `tan` reaches one and Q15 ends: above that the filter is as open as
it gets, which is what setting 100 with no resonance is (`Filter.active`). Settings past 100 read as 100. -/
@[inline] def Filter.g (cutoff : UInt32) : UInt32 :=
  match cutoff with
  | 0 => 70 | 1 => 74 | 2 => 79 | 3 => 84 | 4 => 89 | 5 => 94 | 6 => 100 | 7 => 106 | 8 => 112 | 9 => 119
  | 10 => 126 | 11 => 134 | 12 => 142 | 13 => 151 | 14 => 160 | 15 => 170 | 16 => 180 | 17 => 191 | 18 => 203
  | 19 => 215 | 20 => 228 | 21 => 242 | 22 => 257 | 23 => 272 | 24 => 289 | 25 => 306 | 26 => 325 | 27 => 345
  | 28 => 366 | 29 => 388 | 30 => 412 | 31 => 437 | 32 => 463 | 33 => 492 | 34 => 521 | 35 => 553 | 36 => 587
  | 37 => 622 | 38 => 660 | 39 => 701 | 40 => 743 | 41 => 788 | 42 => 836 | 43 => 887 | 44 => 941 | 45 => 998
  | 46 => 1059 | 47 => 1124 | 48 => 1192 | 49 => 1265 | 50 => 1342 | 51 => 1423 | 52 => 1510 | 53 => 1602
  | 54 => 1700 | 55 => 1803 | 56 => 1913 | 57 => 2030 | 58 => 2154 | 59 => 2285 | 60 => 2425 | 61 => 2573
  | 62 => 2730 | 63 => 2897 | 64 => 3074 | 65 => 3262 | 66 => 3462 | 67 => 3674 | 68 => 3900 | 69 => 4139
  | 70 => 4394 | 71 => 4665 | 72 => 4953 | 73 => 5259 | 74 => 5585 | 75 => 5931 | 76 => 6301 | 77 => 6694
  | 78 => 7114 | 79 => 7561 | 80 => 8039 | 81 => 8549 | 82 => 9095 | 83 => 9678 | 84 => 10304 | 85 => 10975
  | 86 => 11696 | 87 => 12473 | 88 => 13310 | 89 => 14214 | 90 => 15194 | 91 => 16259 | 92 => 17420
  | 93 => 18689 | 94 => 20084 | 95 => 21623 | 96 => 23333 | 97 => 25243 | 98 => 27395 | 99 => 29841
  | _ => 32651

/-- The damping `k = 2 - 2 r` in Q13 (16384 is 2.0) for a resonance setting 0 to 100: 16384 at none (no
peak, the Butterworth response), down by 155 a step to 884 (0.108, a peak of about 19 dB in the ideal
filter; the ±65536 hold on the states caps it lower). Settings past 100 read as 100. -/
@[inline] def Filter.k (resonance : UInt32) : UInt32 := 16384 - 155 * min resonance 100

/-- `a1 = 1 / (1 + g (g + k))` in Q15 from `g` (Q15) and `k` (Q13; `4 k` is `k` in Q15): the denominator in
Q15 is `32768 + g (g + 4 k) / 32768`, at least 32768, and the quotient `2^30 / denominator` is held to 32767.
Once a block; `g (g + 4 k)` is at most 32767 × 98303, within 32 bits. -/
@[inline] def Filter.a1 (g k : UInt32) : UInt32 :=
  min ((1073741824 : UInt32) / ((32768 : UInt32) + ((g * (g + 4 * k)) >>> 15))) 32767

/-- `a2 = g · a1` in Q15. Once a block. -/
@[inline] def Filter.a2 (g k : UInt32) : UInt32 := (g * Filter.a1 g k) >>> 15

/-- The band-pass node before the hold: `a1 · ic1 + a2 · (x - ic2)` in Q15, the second product taken on half
the difference so it fits (`x - ic2` is up to 2^17, `a2` 15 bits). -/
@[inline] def Filter.band (ic1 ic2 x : Int32) (a1 a2 : UInt32) : Int32 :=
  ((a1.toInt32 * ic1) >>> 15) + ((a2.toInt32 * ((x - ic2) >>> 1)) >>> 14)

/-- The band-pass node `v1`, held to ±65536 so `g · v1` and `k · v1` fit. -/
@[inline] def Filter.v1 (ic1 ic2 x : Int32) (a1 a2 : UInt32) : Int32 :=
  Filter.hold (Filter.band ic1 ic2 x a1 a2) 65536

/-- The low-pass node `v2 = ic2 + g · v1`. -/
@[inline] def Filter.v2 (ic2 v1 : Int32) (g : UInt32) : Int32 := ic2 + ((g.toInt32 * v1) >>> 15)

/-- A state after the sample: `2 v - ic`, held to ±65536. -/
@[inline] def Filter.next (ic v : Int32) : Int32 := Filter.hold (2 * v - ic) 65536

/-- The output before the clip: low-pass `v2` (mode 0), band-pass `v1` (mode 1), high-pass
`x - k · v1 - v2` (any other mode; `k` is Q13). -/
@[inline] def Filter.raw (mode : UInt32) (x v1 v2 : Int32) (k : UInt32) : Int32 :=
  match mode with
  | 0 => v2
  | 1 => v1
  | _ => x - ((k.toInt32 * v1) >>> 13) - v2

/-- The output as a 16-bit sample: the node held to ±32767 (a resonant peak goes flat, not inside out). -/
@[inline] def Filter.out (mode : UInt32) (x v1 v2 : Int32) (k : UInt32) : Int32 :=
  Filter.hold (Filter.raw mode x v1 v2 k) 32767

/-- What one sample of the filter yields: the output sample and the two states after it. -/
structure Filter.Step where
  /-- The output sample. -/
  out : Int32
  /-- The first integrator state after the sample. -/
  ic1 : Int32
  /-- The second integrator state after the sample. -/
  ic2 : Int32

/-- One sample of the filter, whole, from the settings: what `render_voice` does with the pieces in
`Firmware/FilterApi.lean` (the coefficients once a block, the nodes, the output and the two state updates a
sample), or, with the filter not active, the sample itself and the states as they were. -/
@[inline] def Filter.step (cutoff resonance mode : UInt32) (ic1 ic2 x : Int32) : Filter.Step :=
  if Filter.active cutoff resonance then
    let g := Filter.g cutoff
    let k := Filter.k resonance
    let a1 := Filter.a1 g k
    let a2 := Filter.a2 g k
    let v1 := Filter.v1 ic1 ic2 x a1 a2
    let v2 := Filter.v2 ic2 v1 g
    ⟨Filter.out mode x v1 v2 k, Filter.next ic1 v1, Filter.next ic2 v2⟩
  else ⟨x, ic1, ic2⟩
