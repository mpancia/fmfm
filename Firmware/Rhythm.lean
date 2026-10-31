import Firmware.Euclid

set_option compiler.extract_closed false

/-- How a lane decides which steps of its bar play. Every source keeps `hits` and `steps` as its base pattern
(spread by `Euclid.hit`); the kinds add a twist:
0 plain Euclid; 1 the pattern turned by `rotate` steps, with `accents` of the hits played louder;
2 a cellular automaton (`rule`, 0 to 255) that rewrites the row of hits at the end of every bar, starting from
the Euclidean pattern; 3 each hit split into `ratchet` sub-hits (1 to 4), of which `subHits` play. -/
structure Rhythm where
  kind : Nat
  rotate : Nat
  accents : Nat
  rule : Nat
  ratchet : Nat
  subHits : Nat
  /-- The automaton's row of hits: bit `step` is set when the step plays. -/
  row : Nat

/-- Bit `i` of `row`. -/
def Rhythm.bit (row i : Nat) : Bool := row.testBit i

/-- One generation of an elementary cellular automaton over a ring of `steps` cells: each cell becomes bit
`left * 4 + self * 2 + right` of `rule`, where its neighbours wrap around the bar. -/
def Automaton.step (rule steps row : Nat) : Nat :=
  (List.range steps).foldl (fun acc i =>
    let l := if Rhythm.bit row ((i + steps - 1) % steps) then 4 else 0
    let c := if Rhythm.bit row i then 2 else 0
    let r := if Rhythm.bit row ((i + 1) % steps) then 1 else 0
    if Rhythm.bit rule (l + c + r) then acc ||| (1 <<< i) else acc) 0

/-- The Euclidean pattern as a row of bits. -/
def Rhythm.seedRow (hits steps : Nat) : Nat :=
  (List.range steps).foldl (fun acc i => if Euclid.hit hits steps i then acc ||| (1 <<< i) else acc) 0

/-- The index of the step `step` looks at in the Euclidean pattern: turned back by `rotate` for kind 1. -/
def Rhythm.source (r : Rhythm) (steps step : Nat) : Nat :=
  if r.kind = 1 then (step + steps - r.rotate % steps) % steps else step

/-- Does step `step` of the bar play? -/
def Rhythm.hit (r : Rhythm) (hits steps step : Nat) : Bool :=
  if r.kind = 2 then Rhythm.bit r.row step else Euclid.hit hits steps (Rhythm.source r steps step)

/-- Is step `step` an accented hit? Only kind 1 accents: the `accents` hits spread among the `hits` by a second
Euclidean pattern over the hit numbers (hit `i * hits / steps` is the one at step `i`). -/
def Rhythm.accent (r : Rhythm) (hits steps step : Nat) : Bool :=
  r.kind = 1 && Rhythm.hit r hits steps step &&
    Euclid.hit r.accents hits (Rhythm.source r steps step * hits / steps)

/-- Which sub-hit of a step tick `count` (0 to `div - 1`) starts, for `ratchet` sub-hits a step: sub-hit `k`
starts at tick `k * div / ratchet`. `none` when the tick starts no sub-hit. -/
def Rhythm.subIndex (div ratchet count : Nat) : Option Nat :=
  (List.range ratchet).find? (fun k => k * div / ratchet = count)

/-- Does tick `count` of a hit step play, for kind 3: it must start a sub-hit, and that sub-hit must be one of
the `subHits` the Euclidean pattern over the sub-hits keeps (turned so that the first sub-hit, the step itself,
always plays). Other kinds play on tick 0 only. -/
def Rhythm.tickPlays (r : Rhythm) (div count : Nat) : Bool :=
  if r.kind = 3 then
    match Rhythm.subIndex div r.ratchet count with
    | some k => Euclid.hit r.subHits r.ratchet ((k + r.ratchet - 1) % r.ratchet)
    | none => false
  else count = 0

/-- The rhythm at the end of a bar: the automaton's row moves one generation on; nothing else changes. -/
def Rhythm.endBar (r : Rhythm) (steps : Nat) : Rhythm :=
  if r.kind = 2 then { r with row := Automaton.step r.rule steps r.row } else r

/-- Settings forced into range: kind 0 to 3, rotation below `steps`, accents at most the hits, a rule byte,
ratchet 1 to 4 with sub-hits at most the ratchet. The row is cut to the bar and seeded from the pattern when
it would be empty. -/
def Rhythm.make (kind rotate accents rule ratchet subHits hits steps row : Nat) : Rhythm :=
  let ratchet := max 1 (min 4 ratchet)
  let cut := row % (2 ^ steps)
  { kind := min 3 kind, rotate := rotate % steps, accents := min accents hits, rule := rule % 256, ratchet,
    subHits := min subHits ratchet, row := if cut = 0 then Rhythm.seedRow hits steps % (2 ^ steps) else cut }
