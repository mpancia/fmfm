import Firmware.Filter

set_option compiler.extract_closed false

/-! C entry points for `Firmware/Filter.lean`: `fw/firmware/src/dinghy.c`'s `render_voice` calls them on each
voice's stream after the engine. Once a block: `fm1_filter_active (cutoff, resonance)`; if 0 the stream is
left alone (that is `Filter.step`'s bypass branch); else `g = fm1_filter_g (cutoff)`,
`k = fm1_filter_k (resonance)`, `a1 = fm1_filter_a1 (g, k)`, `a2 = fm1_filter_a2 (g, k)`. Then a sample, in
this order: `v1 = fm1_filter_v1 (ic1, ic2, x, a1, a2)`, `v2 = fm1_filter_v2 (ic2, v1, g)`,
`out = fm1_filter_out (mode, x, v1, v2, k)`, `ic1 = fm1_filter_next (ic1, v1)`,
`ic2 = fm1_filter_next (ic2, v2)`. The states start at 0 on a strike. Settings stay 32-bit numbers
throughout: no `Nat` on the sample path. -/

/-- 1 if the filter changes anything: 0 with the cutoff fully open (100) and no resonance. Once a block. -/
@[export fm1_filter_active] def filterActive (cutoff resonance : UInt32) : UInt32 :=
  if Filter.active cutoff resonance then 1 else 0

/-- The cutoff coefficient `g`, Q15, for a cutoff setting 0 to 100. Once a block. -/
@[export fm1_filter_g] def filterG (cutoff : UInt32) : UInt32 := Filter.g cutoff

/-- The damping `k`, Q13 (16384 is 2.0), for a resonance setting 0 to 100. Once a block. -/
@[export fm1_filter_k] def filterK (resonance : UInt32) : UInt32 := Filter.k resonance

/-- `a1 = 1 / (1 + g (g + k))`, Q15, from `g` and `k`. Once a block. -/
@[export fm1_filter_a1] def filterA1 (g k : UInt32) : UInt32 := Filter.a1 g k

/-- `a2 = g · a1`, Q15, from `g` and `k`. Once a block. -/
@[export fm1_filter_a2] def filterA2 (g k : UInt32) : UInt32 := Filter.a2 g k

/-- The band-pass node `v1` for the sample `x` from the states and `a1`, `a2`; first each sample. -/
@[export fm1_filter_v1] def filterV1 (ic1 ic2 x : Int32) (a1 a2 : UInt32) : Int32 :=
  Filter.v1 ic1 ic2 x a1 a2

/-- The low-pass node `v2` from the second state, `v1` and `g`; second each sample. -/
@[export fm1_filter_v2] def filterV2 (ic2 v1 : Int32) (g : UInt32) : Int32 := Filter.v2 ic2 v1 g

/-- The output sample (held to ±32767) for the mode (0 low, 1 band, else high) from `x`, the nodes and `k`;
third each sample. -/
@[export fm1_filter_out] def filterOut (mode : UInt32) (x v1 v2 : Int32) (k : UInt32) : Int32 :=
  Filter.out mode x v1 v2 k

/-- A state after the sample: `2 v - ic` held to ±65536; called for `(ic1, v1)` then `(ic2, v2)`, last each
sample. -/
@[export fm1_filter_next] def filterNext (ic v : Int32) : Int32 := Filter.next ic v
