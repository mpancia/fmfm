import Proofs.Lane
import Proofs.Run
import Proofs.Rhythm
import Proofs.Swing
import Proofs.Divider
import Proofs.Euclid
import Proofs.Notes
import Proofs.Quantizer
import Proofs.Random
import Proofs.Harmony
import Proofs.Tonnetz
import Proofs.Arp
import Proofs.Machine
import Proofs.Lfo
import Proofs.Punch
import Proofs.PunchMix
import Proofs.Keys
import Proofs.KeysChord
import Proofs.Clock
import Proofs.Patch
import Proofs.Presets

/-!
Every public theorem of the sequencer side (lanes, rhythm, notes, harmony, keys, punch, clock, patches)
instantiated on one concrete input with every hypothesis discharged. The running example is a lane of five
hits in sixteen steps, a step every clock tick, C major (mask `0xAB5`), notes from C3 (48) over an octave,
seed 1.
-/

/-- The running example lane: 5 of 16, one tick a step, C major from C3 over an octave. -/
def ExSeq.lane : Lane := Lane.make 5 16 1 0xAB5 48 12 1

/-- A dense lane, every step a hit, so its very first tick starts a note (C3, 48). -/
def ExSeq.dense : Lane := Lane.make 16 16 1 0xAB5 48 12 1

#guard ExSeq.dense.tick.on == some 48                                -- the dense lane plays C3 on tick one
#guard ExSeq.dense.tick.playing == some 48 && ExSeq.dense.tick.gateLeft == 1   -- gate: one tick left

/-! Lane -/

-- A lane built from the knobs is consistent.
example : Lane.Valid ExSeq.lane := lane_make_valid 5 16 1 0xAB5 48 12 1
-- Changing it to 3 of 8 at a half-note step in C minor keeps it consistent.
example : Lane.Valid (ExSeq.lane.reconfigure 3 8 12 0x5AD) :=
  lane_reconfigure_valid _ (lane_make_valid 5 16 1 0xAB5 48 12 1) 3 8 12 0x5AD
-- Switching to the walk algorithm (1), 80 percent, walk size 3, 10 percent mutation keeps it consistent.
example : Lane.Valid (ExSeq.lane.setNotes 1 80 3 10) :=
  lane_set_notes_valid _ (lane_make_valid 5 16 1 0xAB5 48 12 1) 1 80 3 10
-- One clock tick keeps the lane consistent.
example : Lane.Valid ExSeq.lane.tick := lane_tick_valid _ (lane_make_valid 5 16 1 0xAB5 48 12 1)
-- The dense lane has C3 sounding with one tick left after tick one: tick two stops C3.
example : (Lane.tick ExSeq.dense.tick).off = some 48 :=
  lane_gate_end_stops_note ExSeq.dense.tick 48 (by decide) (by decide)
-- Tick one of the dense lane starts C3, so it stops whatever was sounding before (nothing).
example : (Lane.tick ExSeq.dense).off = ExSeq.dense.playing := lane_new_note_stops_old _ 48 (by decide)
-- That start only happened because step 0 is a hit of the dense rhythm.
example : Rhythm.hit ExSeq.dense.rhythm ExSeq.dense.hits ExSeq.dense.steps ExSeq.dense.hitStep = true :=
  lane_note_only_on_hit _ 48 (by decide)
-- The note that starts is a MIDI note in C major.
example : 48 ≤ 127 ∧ Quantizer.inScale ExSeq.dense.mask 48 = true :=
  lane_note_in_scale _ (lane_make_valid 16 16 1 0xAB5 48 12 1) 48 (by decide)
-- Silencing keeps the lane consistent.
example : Lane.Valid ExSeq.dense.tick.silence :=
  lane_silence_valid _ (lane_tick_valid _ (lane_make_valid 16 16 1 0xAB5 48 12 1))
-- Silencing the dense lane after tick one stops C3 and leaves nothing sounding.
example : ExSeq.dense.tick.silence.off = ExSeq.dense.tick.playing ∧ ExSeq.dense.tick.silence.playing = none :=
  lane_silence_stops_note _
-- Feeding the example lane its own settings back changes nothing.
example :
    ExSeq.lane.reconfigure ExSeq.lane.hits ExSeq.lane.steps ExSeq.lane.div ExSeq.lane.mask = ExSeq.lane ∧
    ExSeq.lane.setNotes ExSeq.lane.rule.algo ExSeq.lane.prob ExSeq.lane.rule.amount ExSeq.lane.rule.mutate =
      ExSeq.lane :=
  lane_reconfigure_self _ (lane_make_valid 5 16 1 0xAB5 48 12 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
-- A rotated Euclid (kind 1) turned by 3, two accents, rule 90, ratchet 2 of 2, reseeded, keeps it consistent.
example : Lane.Valid (ExSeq.lane.setRhythm 1 3 2 90 2 2 true) :=
  lane_set_rhythm_valid _ (lane_make_valid 5 16 1 0xAB5 48 12 1) 1 3 2 90 2 2 true
-- Learning E3 (52) into the loop keeps the lane consistent.
example : Lane.Valid (ExSeq.lane.learn 52) := lane_learn_valid _ (lane_make_valid 5 16 1 0xAB5 48 12 1) 52
-- The first lane of the first preset, loaded at a step of six ticks in C major, keeps its FEEL settings.
example :=
  lane_from_patch_keeps_feel
    { hits := 4, steps := 16, speed := 3, scale := 4, sound := 23, low := 36, span := 12, algo := 6,
      chance := 100, amount := 8, mutate := 0, chord := 2, level := 100, send := 10, seed := 201, feel := 1,
      rotate := 0, accents := 2, rule := 90, ratchet := 1, subHits := 1, pan := 50 }
    (by decide) 6 0xAB5 1

/-! Run -/

-- Over tick, a knob change, two ticks and a learned note, every note-on of a fresh lane has its note-off.
example :=
  run_every_note_on_has_a_note_off ExSeq.dense rfl [.tick, .reconfigure 5 16 2 0xAB5, .tick, .tick, .learn 52]
-- After 37 ticks a lane at a step of four ticks sits on step 37 / 4 with 37 mod 4 ticks counted.
example := run_clock_never_drifts 5 16 4 0xAB5 48 12 1 37
-- A bar of a rotated Euclid (kind 1, turned 3) with two accents plays exactly its rhythm's hits.
example := run_bar_plays_the_rhythm 5 16 2 0xAB5 48 12 1 1 3 2 90 1 1 (by decide)
-- A bar of 5 in 16 at two ticks a step plays exactly five notes.
example := run_bar_plays_every_hit 5 16 2 0xAB5 48 12 1
-- Turned by 3 with two accents, rule 90, ratchet 2 of 2: still every hit is played, five a bar.
example := run_bar_plays_every_hit_turned 5 16 2 0xAB5 48 12 1 3 2 90 2 2
-- 3 of 8 at twelve ticks a step with a ratchet of 4 playing 2 sub-hits: hits times sub-plays note-ons.
example := run_bar_plays_every_ratchet 3 8 12 0xAB5 48 12 1 0 0 90 4 2 (by decide)

/-! Rhythm -/

-- Rule 90 over sixteen steps keeps the row inside sixteen bits.
example : (Automaton.step 90 16 0xB00B).toNat < 2 ^ 16 := rhythm_automaton_row_fits 90 16 0xB00B (by decide)
-- Step 2 of a rotated 5 of 16 (turned by 3) with two accents is accented, so it is a hit.
example : Rhythm.hit (Rhythm.make 1 3 2 90 1 1 5 16 0) 5 16 2 = true :=
  rhythm_accent_only_on_hit _ 5 16 2 (by decide)
-- Rotating 5 of 16 by three (kind 1) keeps five hits a bar.
example : Rhythm.count (Rhythm.hit (Rhythm.make 1 3 0 90 1 1 5 16 0) 5 16) 16 =
    Rhythm.count (Euclid.hit 5 16) 16 :=
  rhythm_rotate_keeps_hits (Rhythm.make 1 3 0 90 1 1 5 16 0) 5 16 rfl (by decide)
-- Rule 0 kills any sixteen-step row.
example : Automaton.step 0 16 0xB00B = 0 := rhythm_rule_zero_dies 16 0xB00B (by decide)
-- Rule 255 fills all sixteen steps.
example : (Automaton.step 255 16 0xB00B).toNat = 2 ^ 16 - 1 := rhythm_rule_full_fills 16 0xB00B (by decide)
-- Rule 204 holds a sixteen-step row still.
example : Automaton.step 204 16 0xB00B = Rhythm.cut 16 0xB00B := rhythm_rule_204_freezes 16 0xB00B (by decide)

/-! Swing -/

-- At 60 percent swing, tick 5 of the quarter note lasts between a third and five thirds of a straight tick.
example := swing_tick_in_range 5 60
-- At 60 percent swing a tick and the tick half a quarter note later add up to two straight ticks.
example := swing_keeps_time 5 60 (by decide)
-- At 60 percent swing a quarter note of 24 ticks lasts exactly 240 ms.
example := swing_quarter_note_exact 60

/-! Divider -/

-- A divide-by-6 from a zero count fires 100 / 6 = 16 pulses over 100 ticks.
example : (Divider.run 6 0 100).2 = 100 / 6 := divider_pulse_count 6 100 (by decide)
-- A divide-by-6 counter at 2 stays below 6 over 100 ticks.
example : (Divider.run 6 2 100).1 < 6 := divider_count_bounded 6 100 2 (by decide)

/-! Euclid -/

-- Five of sixteen has five hits a bar.
example : Euclid.countHits 5 16 16 = 5 := euclid_hit_count 5 16 (by decide) (by decide)
-- Five of sixteen hits on step 15.
example : Euclid.hit 5 16 (16 - 1) = true := euclid_last_step_hits 5 16 (by decide) (by decide)
-- Any eight-step window of five in sixteen holds two or three hits.
example := euclid_window_balanced 5 16 3 8 (by decide) (by decide)
-- Two eight-step windows of five in sixteen differ by at most one hit.
example := euclid_windows_within_one 5 16 3 11 8 (by decide) (by decide)
-- Five of sixteen at step 7 agrees with the lower Christoffel word.
example : Euclid.hit 5 16 7 = Euclid.christoffel 5 16 7 := euclid_is_christoffel 5 16 7 (by decide)
-- Bjorklund's 5 of 16 is a rotation of the firmware's.
example := euclid_bjorklund_is_rotation 16 (by decide) (by decide) 5 (by decide)
-- The major scale is seven of twelve Euclidean, the pentatonic five of twelve.
example : Euclid.mask 7 6 = Harmony.scale 0 ∧ Euclid.mask 5 7 = Harmony.scale 2 :=
  euclid_major_scale_is_seven_of_twelve

/-! Notes -/

/-- The note memory of an octave range from seed 1, parked at position `pos`. -/
def ExSeq.notesAt (pos : Nat) : NoteState := { Notes.start 12 1 with pos }

-- The note memory for an octave range, loop of four, seed 1 is consistent.
example : NoteState.Valid 12 4 (Notes.start 12 1) :=
  notes_start_valid 12 4 1 (by decide) (by decide) (by decide)
-- A walk choice (algo 1, loop of 4) in an octave of C major from C3 stays inside the range and consistent.
example :=
  notes_choose_stays_in_range ⟨1, 4, 10⟩ 12 0xAB5 48 (Notes.start 12 1) 7 5 50 (by decide) (by decide)
    (by decide) (notes_start_valid 12 4 1 (by decide) (by decide) (by decide)) (by decide)
-- Eight UP picks from position 3 of an octave visit 4, 5, ..., 11, 0.
example := notes_up_visits_every_position 12 3 (by decide) (by decide) (ExSeq.notesAt 3) rfl 8
-- Eight DOWN picks from position 3 of an octave visit 2, 1, 0, 11, ...
example := notes_down_visits_every_position 12 3 (by decide) (by decide) (ExSeq.notesAt 3) rfl 8
-- BOUNCE from position 3 moves to 2 or 4.
example := notes_bounce_moves_one 12 0xAB5 48 (ExSeq.notesAt 3) (by decide) (by decide) 7 5 50
-- A WALK of size 3 from position 5 lands within three positions.
example := notes_walk_bounded 3 12 0xAB5 48 (ExSeq.notesAt 5) 4 7 50 (by decide) (by decide)
-- LOOP of length 4 at slot 1 replays slot 1 and moves to slot 2.
example := notes_loop_repeats 4 12 0xAB5 48 { Notes.start 12 1 with slot := 1 } (by decide) (by decide) 7 5 50
-- MARKOV from position 5 moves at most three positions.
example := notes_markov_moves_at_most_three 4 10 12 0xAB5 48 (ExSeq.notesAt 5) 7 5 50 (by decide)
-- GRAMMAR from position 5 moves at most two positions.
example := notes_grammar_moves_at_most_two 4 10 12 0xAB5 48 (ExSeq.notesAt 5) 7 5 50 (by decide)
-- Learning offset 4 into a fresh loop-of-four memory keeps it consistent.
example : NoteState.Valid 12 4 (Notes.learn ⟨5, 4, 0⟩ 12 (Notes.start 12 1) 4) :=
  notes_learn_keeps_valid ⟨5, 4, 0⟩ 12 (Notes.start 12 1) 4 (by decide)
    (notes_start_valid 12 4 1 (by decide) (by decide) (by decide))
-- A locked Turing machine of eight bits repeats its eight bits after eight picks.
example := notes_turing_locked_repeats 8 12 (Notes.start 12 1) (by decide) (by decide)
-- Grammar 3 rewritten two deep is never an empty phrase.
example : Notes.phraseOf 3 2 ≠ [] := notes_grammar_phrase_never_empty 3 2
-- The 10th C-major scale tone above C3 is in C major.
example : Quantizer.inScale 0xAB5 (Notes.scaleTone 0xAB5 48 10) = true :=
  notes_scale_tone_in_scale 0xAB5 48 10 (by decide)

/-! Quantizer -/

-- E3 (52) is in C major, so snapping leaves it alone.
example : Quantizer.snap 0xAB5 52 = 52 := quantizer_snap_keeps_scale_notes 0xAB5 52 (by decide)
-- Snapping C#3 (49) to C major lands in C major.
example : Quantizer.inScale 0xAB5 (Quantizer.snap 0xAB5 49) = true :=
  quantizer_snap_in_scale 0xAB5 49 (by decide) (by decide) (by decide)
-- Snapping C#3 moves it by at most a tritone.
example := quantizer_snap_is_near 0xAB5 49 (by decide) (by decide) (by decide)
-- Snapping C#3 and F#3 (54) to C major keeps their order.
example : Quantizer.snap 0xAB5 49 ≤ Quantizer.snap 0xAB5 54 :=
  quantizer_snap_monotone 0xAB5 49 54 (by decide) (by decide) (by decide) (by decide)

/-! Random -/

-- A draw below 12 from state 0xDEADBEEF is below 12.
example : (Random.below 0xDEADBEEF 12).toNat < (12 : UInt32).toNat :=
  random_below_lt 0xDEADBEEF 12 (by decide) (by decide)
-- The generator never returns the state 0xDEADBEEF to itself.
example : Random.next 0xDEADBEEF ≠ 0xDEADBEEF := random_never_stands_still 0xDEADBEEF

/-! Harmony -/

-- Scale 0 (major) in D (key 2), progression 1, step 3, chord follow 1: a non-empty twelve-bit mask.
example := harmony_mask_never_empty 0 2 1 3 1
-- A table progression (1) with chord follow (1) stays inside D major.
example := harmony_follow_in_key 0 2 1 3 1 (by decide) (by decide)
-- The step-3 chord of progression 1 in D major contains its root.
example := harmony_progression_chord_has_root 0 2 1 3 1 (by decide)
-- The step-3 chord root of progression 1 is a major-scale degree below 12.
example := harmony_chord_root_in_key 0 1 3 (by decide)
-- A Tonnetz walk progression (8) at step 5 with chord follow 2 in D is a three-note triad.
example := harmony_walk_chord_is_triad 0 2 8 5 2 (by decide) (by decide)
-- Consecutive triads of walk word 1 from triad 4 share two notes.
example : Harmony.size (Tonnetz.mask (Tonnetz.walk 1 4 3) &&& Tonnetz.mask (Tonnetz.walk 1 4 (3 + 1))) = 2 :=
  harmony_walk_keeps_two_notes 1 4 3
-- Complement follow (3) in D major lies outside the key, or fills it when the key is chromatic.
example := harmony_complement_outside_key 0 2 1 3 3 (by decide)
-- The interval-content identity for interval 5 over 12 pitches and the C-major set.
example := harmony_complement_interval_content 12 5 (by decide) (fun k => Quantizer.inScale 0xAB5 k)
-- The whole-tone hexachord 0x555 shares its interval vector with its complement.
example : Harmony.intervalVector 0x555 = Harmony.intervalVector (0xFFF ^^^ 0x555) :=
  harmony_hexachord_theorem 0x555 (by decide) (by decide)

/-! Tonnetz -/

-- The relative move (R, 2) applied twice to C major (triad 0) gives C major back.
example : Tonnetz.move 2 (Tonnetz.move 2 0) = 0 := tonnetz_moves_are_involutions 2 0
-- The PLR group has order 24.
example := tonnetz_group_has_order_24
-- The PLR group acts simply transitively on the 24 triads.
example := tonnetz_simply_transitive
-- Group element 7 commutes with transposition by 5 and inversion about 5 on triad 3.
example := tonnetz_commutes_with_transposition_and_inversion 7 5 3
-- The PLR group is dihedral of order 24.
example := tonnetz_group_is_dihedral
-- The three walks from C major (triad 0) are cycles of 24, 6 and 8.
example := tonnetz_walks_are_cycles 0

/-! Arp -/

-- The note the example arpeggiator (C, E, G held) starts on its first tick is a held note, C (60).
example : ∃ h ∈ Arp.example.held, ∃ o, o < max 1 Arp.example.octaves ∧ 60 = h + 12 * o :=
  arp_note_is_held Arp.example
    (arp_keys_valid _ (arp_keys_valid _ (arp_keys_valid _ (arp_make_valid 1 7) 64).1 60).1 67).1
    60 (by decide)
-- A fresh arpeggiator at six ticks a step is consistent.
example : Arp.Valid (Arp.make 6 7) := arp_make_valid 6 7
-- Setting mode DOWN (2), two octaves, three ticks a step, gate 2 keeps it consistent.
example : Arp.Valid ((Arp.make 6 7).set 2 2 3 2) := arp_set_valid _ (arp_make_valid 6 7) 2 2 3 2
-- Pressing, releasing and clearing E4 (64) each keep it consistent.
example := arp_keys_valid (Arp.make 6 7) (arp_make_valid 6 7) 64
-- One tick keeps the example arpeggiator (made valid, then three valid presses) consistent.
example : Arp.Valid Arp.example.tick :=
  arp_tick_valid _
    (arp_keys_valid _ (arp_keys_valid _ (arp_keys_valid _ (arp_make_valid 1 7) 64).1 60).1 67).1
-- Over presses, ticks, a release and a clear, every note-on of a fresh arpeggiator has its note-off.
example := arp_every_note_on_has_a_note_off (Arp.make 1 7) rfl
  [.press 60, .tick, .press 64, .tick, .release 60, .tick, .set 2 2 1 1, .tick, .clear, .tick]
-- UP at one tick a step from the start plays the example's pattern C, E, G in order.
example : Arp.example.played Arp.example.pattern.length = Arp.example.pattern :=
  arp_up_plays_pattern Arp.example rfl rfl rfl (by decide)

/-! Machine -/

-- Four fresh lanes and the example arpeggiator: every note-on over a run has its note-off, and stop silences.
example :=
  machine_every_note_on_has_a_note_off { lanes := fun _ => ExSeq.dense, arp := Arp.example }
    ⟨fun _ => rfl, rfl⟩ (fun i => [.tick, .reconfigure 3 8 i.val 0xAB5, .tick]) [.tick, .press 72, .tick]

/-! Lfo -/

-- An LFO over base 50 at full depth, any phase, stays within 0 to 100.
example : (lfoModulate 50 100 0x40000000).toNat ≤ 100 := lfo_modulate_in_range 50 100 0x40000000
-- The triangle at phase 0x12345678 equals the triangle at its complement.
example : Lfo.triangle (~~~0x12345678) = Lfo.triangle 0x12345678 := lfo_triangle_symmetric 0x12345678
-- At the zero crossing, or at zero depth, the LFO leaves base 50 alone.
example := lfo_modulate_centred 50 100 0x12345678 (by decide) (by decide)

/-! Punch -/

-- No key held: tempo 100, no restrike, note 60 untouched, gate open, reverb and delay as set, lane 2 unmuted.
example := punch_nothing_held_changes_nothing 1 7 60 2 3 5 11 (by decide)
-- OCT+ and SHIFT held (keys 5 and 6) with shift 7 on B8 (119) stays a MIDI note.
example : Punch.note 96 7 119 ≤ 127 := punch_note_in_range 96 7 119
-- HALF held (key 0) gives a tempo of 50, 100 or 200 percent.
example := punch_tempo_in_range 1
-- GATE held (key 7) with an eighth-note period (choice 0) from tick 100 is open six of twelve ticks.
example := punch_gate_half_open 128 0 100 (by decide) (by decide)
-- A gate gain of 1000 heading for full (32768) glides monotonically and stays in range.
example := punch_gate_glides 1000 32768 (by decide) (by decide)
-- CRUSH by 8 at sample index 3 plays either the live sample or the held one.
example := punch_crush_repeats 8 3 (-1234) 5678
-- STUTTER held (key 2) with a sixteenth period (choice 1) re-strikes on a divisor of the quarter note.
example : 24 % Punch.stutterPeriod 4 1 = 0 := punch_restrikes_on_the_beat 4 1 (by decide)

/-! PunchMix -/

-- A half-gain gate on a loud sample never amplifies it and keeps it within 20 bits.
example := punch_gate_never_amplifies 400000 16384 (by decide) (by decide)
-- CRUSH by 8 at index 3 of two in-limit samples stays in limit.
example := punch_crush_keeps_limit 8 3 (-400000) 400000 (by decide) (by decide)
-- CRUSH then a half gate on an in-limit mix never wraps.
example := punch_master_never_wraps 8 3 16384 (-400000) 400000 (by decide) (by decide) (by decide)

/-! Keys -/

-- Mode 0 leaves C#4 (61) alone.
example : Keys.quantize 0 0xAB5 0 61 = 61 := keys_off_is_itself 0xAB5 0 61 (by decide)
-- Mode 1 in C major keeps a note of 200 inside MIDI.
example : Keys.quantize 1 0xAB5 0 200 ≤ 127 := keys_in_range 1 0xAB5 0 200
-- Mode 1 in C major puts C#4 on a C-major pitch class.
example : (0xAB5 % 4096 : UInt32).toNat.testBit ((Keys.quantize 1 0xAB5 0 61).toNat % 12) = true :=
  keys_in_scale 1 0xAB5 0 61 (by decide) (by decide) (by decide)
-- Mode 1 in C major keeps C#4 (61) at or below F#4 (66).
example : Keys.quantize 1 0xAB5 0 61 ≤ Keys.quantize 1 0xAB5 0 66 :=
  keys_keep_order 1 0xAB5 0 61 66 (by decide) (by decide) (by decide)

/-! KeysChord -/

-- Triad 0 (C major) in key D: three chord tones an octave apart.
example := keys_triad_three_an_octave 0 2 (by decide) (by decide)
-- Triad 0 in key D: the white keys' degrees land on chord tones.
example := keys_triad_is_the_chord 0 2 (by decide) (by decide)
-- Triad 0 in key D: the three white keys make exactly the chord mask.
example := keys_triad_white_keys_are_the_chord 0 2 (by decide) (by decide)

/-! Clock -/

-- A 1 ms gap at 120 bpm, full tempo, from an accumulator of 5000 advances without wrapping.
example := clock_advance_never_wraps 5000 1000 120 100 (by decide) (by decide) (by decide) (by decide)
-- 25000 units at a tick length of 10000 is two ticks with 5000 left over.
example := clock_division_is_the_loop 25000 10000 (by decide)
-- Half time over a 20 ms gap at 120 bpm gives half the ticks, within rounding.
example := clock_half_time_is_half 5000 20000 120 (by decide) (by decide) (by decide)
-- Double time over a 20 ms gap at 120 bpm gives twice the ticks, within rounding.
example := clock_double_time_is_double 5000 20000 120 (by decide) (by decide) (by decide)

/-! Patch -/

/-- The first factory preset, named so the examples below can reach it. -/
def ExSeq.patch : Patch := Presets.all.head (by decide)

-- The first preset survives a save and a load.
example : Patch.decode (Patch.encode ExSeq.patch) = some ExSeq.patch :=
  patch_decode_encode_round_trip ExSeq.patch (presets_all_fit _ (List.head_mem _))
-- Whatever a load of its bytes gives back fits.
example : ExSeq.patch.Fits :=
  patch_decode_only_fits (Patch.encode ExSeq.patch) ExSeq.patch
    (patch_decode_encode_round_trip ExSeq.patch (presets_all_fit _ (List.head_mem _)))
-- 106 bytes starting with 0x00 are not a patch.
example : Patch.decode (ByteArray.mk (Array.replicate 106 0)) = none :=
  patch_decode_rejects_wrong_marker _ (by decide) (by decide)
-- Two bytes, even with the right marker, are not a patch.
example : Patch.decode (ByteArray.mk #[0xA7, 0]) = none := patch_decode_rejects_wrong_size _ (by decide)
-- The first preset saves to 106 bytes.
example : (Patch.encode ExSeq.patch).size = 106 := patch_encode_size ExSeq.patch

/-! Presets -/

-- Every factory preset fits; in particular the first one.
example : ExSeq.patch.Fits := presets_all_fit _ (List.head_mem _)

/-! Rejections: the spec says no to bad behaviour -/

-- Euclid: five of sixteen is not four hits a bar.
#guard Euclid.countHits 5 16 16 ≠ 4
-- Euclid: five of sixteen does not hit on step 0 (it lands on the last step instead).
#guard !Euclid.hit 5 16 0
-- Quantizer: C#4 is not in C major, so snapping moves it (to C, 60) rather than keeping it.
#guard !Quantizer.inScale 0xAB5 61 && Quantizer.snap 0xAB5 61 ≠ 61 && Quantizer.snap 0xAB5 61 == 60
-- Patch: a wrong marker byte in front of 105 good bytes is refused.
#guard (Patch.decode (ByteArray.mk (#[0x00] ++ (Patch.encode ExSeq.patch).data.extract 1 106))).isNone
-- Patch: a saved preset cut to 105 bytes is refused.
#guard (Patch.decode (ByteArray.mk ((Patch.encode ExSeq.patch).data.extract 0 105))).isNone
-- Run: a ratchet of 4 at a step of two ticks cannot fit, so a bar does not play hits times sub-hits notes.
#guard let l := ((Lane.make 7 16 2 0xAB5 48 12 1).setNotes 0 100 1 0).setRhythm 0 0 0 90 4 4 true
  Lane.noteOns (l.trace (List.replicate (l.steps * l.div) .tick)) ≠
    l.hits * Rhythm.count (Rhythm.subPlays l.rhythm) l.rhythm.ratchet
-- Keys: a note of 200 is held to 127, never passed through.
#guard Keys.quantize 1 0xAB5 0 200 == 127 && Keys.quantize 0 0xAB5 0 200 ≠ 200
-- Keys: C#4 (61) quantized in C major (mode 1) is not C#.
#guard Keys.quantize 1 0xAB5 0 61 ≠ 61
-- Punch: OCT+ held (key 5) on a top note never pushes it past 127.
#guard Punch.note 32 7 127 == 127
-- Harmony: COMPL (follow 3) in C major shares no note with the key.
#guard harmonyMask 0 0 0 0 3 &&& harmonyMask 0 0 0 0 0 == 0 && harmonyMask 0 0 0 0 3 ≠ 0
