import Firmware.Harmony

/-! Worked examples: the chord roots the progressions give in a few scales. -/

-- 1-4-5-1 in C major: C F G C; in A minor (scale 1): the minor's own fourth and fifth, A D E A
#guard (List.range 4).map (Harmony.chordRoot 0 1) == [0, 5, 7, 0]
#guard (List.range 4).map (Harmony.chordRoot 1 1) == [0, 5, 7, 0]
-- 1-5-6-4 in major: I V vi IV; 1-6-3-7 in minor: i VI III VII (semitones 0 8 3 10)
#guard (List.range 4).map (Harmony.chordRoot 0 2) == [0, 7, 9, 5]
#guard (List.range 4).map (Harmony.chordRoot 1 5) == [0, 8, 3, 10]
-- 1-6-2-5 in major: I vi ii V
#guard (List.range 4).map (Harmony.chordRoot 0 7) == [0, 9, 2, 7]
-- in a pentatonic (five notes) the degrees count round: 1-6-2-5 in C pentatonic major is C C D A
#guard (List.range 4).map (Harmony.chordRoot 2 7) == [0, 0, 2, 9]
-- a chord root is always a note of the scale
#guard (List.range 14).all fun sc => (List.range 8).all fun p => (List.range 4).all fun s =>
  (Harmony.scale sc).testBit (Harmony.chordRoot sc p s)

/-- How many pitch classes a 12-bit mask holds. -/
def Harmony.size (mask : Nat) : Nat := ((List.range 12).filter (fun k => mask.testBit k)).length

/-- The interval vector of a pitch-class set: for each interval class 1 to 6, the number of pairs of its notes
that interval apart (a tritone pair counted once). -/
def Harmony.intervalVector (mask : Nat) : List Nat :=
  (List.range 6).map fun d =>
    ((List.range (if d = 5 then 6 else 12)).filter
      (fun k => mask.testBit k && mask.testBit ((k + d + 1) % 12))).length

/-- The general setting, any cycle `Z_n` and any set `S` of its points: the size of `S`. -/
def Harmony.count (n : Nat) (S : Nat → Bool) : Nat := ((List.range n).filter S).length

/-- The number of points `k` of `S` whose `d`-th neighbour `k + d` is in `S` too (an ordered count: a pair at
distance `d` and `n - d` is seen twice). -/
def Harmony.pairs (n d : Nat) (S : Nat → Bool) : Nat :=
  ((List.range n).filter (fun k => S k && S ((k + d) % n))).length
