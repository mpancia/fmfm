import Firmware.Euclid

/-- How many of the first `upTo` steps of the pattern play a note. -/
def Euclid.countHits (hits steps : Nat) : Nat → Nat
  | 0 => 0
  | upTo + 1 => Euclid.countHits hits steps upTo + if Euclid.hit hits steps upTo then 1 else 0

/-- How many of the steps from `start` up to (not including) `stop` play. The pattern is read past the bar, where
it repeats. -/
def Euclid.countBetween (hits steps start stop : Nat) : Nat :=
  ((List.range (stop - start)).filter (fun k => Euclid.hit hits steps (start + k))).length

/-- Berstel's definition of the lower Christoffel word of slope `hits / steps`: letter `k` is a hit when the
multiples of `hits` wrap round modulo `steps` between `k` and `k + 1`. -/
def Euclid.christoffel (hits steps k : Nat) : Bool :=
  ((k + 1) * hits) % steps < (k * hits) % steps

/-- Bjorklund's algorithm as Toussaint describes it: `hits` ones and `steps - hits` zeros as one-letter
sequences, then the remainder sequences are paired off onto the main ones until at most one remainder is left;
the sequences are then read in order. `fuel` is only for termination (every round shortens the lists). -/
def Euclid.bjorklundRounds : Nat → List (List Bool) → List (List Bool) → List Bool
  | 0, main, rem => (main ++ rem).flatten
  | fuel + 1, main, rem =>
    if rem.length ≤ 1 ∨ main.length = 0 then (main ++ rem).flatten
    else
      let m := min main.length rem.length
      let paired := List.zipWith (· ++ ·) (main.take m) (rem.take m)
      let leftover := if m < main.length then main.drop m else rem.drop m
      Euclid.bjorklundRounds fuel paired leftover

/-- Bjorklund's rhythm of `hits` hits in `steps` steps. -/
def Euclid.bjorklund (hits steps : Nat) : List Bool :=
  Euclid.bjorklundRounds steps (List.replicate hits [true]) (List.replicate (steps - hits) [false])

/-- The firmware's pattern as a word of `steps` letters, read from step `rotation`. -/
def Euclid.word (hits steps rotation : Nat) : List Bool :=
  (List.range steps).map (fun k => Euclid.hit hits steps ((k + rotation) % steps))

/-- A set of pitch classes as the firmware's 12-bit mask: bit `k` for every `k` the pattern plays. -/
def Euclid.mask (hits rotation : Nat) : Nat :=
  (List.range 12).foldl
    (fun acc k => if Euclid.hit hits 12 ((k + rotation) % 12) then acc ||| (1 <<< k) else acc) 0
