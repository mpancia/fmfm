# FORMALFRED

Firmware for the M-VAVE FM-1 that makes music on its own. Four lanes of generative rhythm and melody, Braids
voices, an FM voice, an 808, a filter, reverb and delay. The sequencer, the voices' arithmetic, the effects and
the patch format are Lean 4, and 313 theorems about that code are checked on every build. Alfred, a little
pixel-art butler, bows at boot and waits in the corner when you stop. Made for the Vibecheck hackathon.

Hear it now, no hardware: https://mpancia.github.io/fmfm/sim/ (Chrome or Edge for MIDI in). The site also has
the installer and the pitch deck.

Or build it:

```
make install && make run
```

Open http://localhost:8000/, click Power on, and it plays. The simulator is the real firmware
(`fw/firmware/src/dinghy.c`) compiled to WebAssembly: same screen, keys, knobs, audio, MIDI in. It can record what
you hear, save the screen as a PNG, and give you a link to the patch you're on (`?patch=N`). Space is PLAY,
PageUp and PageDown change patch, hover a button for what it does. `docs/SIMULATOR.md`.

To put it on an FM-1: the installer on the site, and `docs/FM1.md` for the hardware and the backup to take
first. What is proved is [below](#what-is-proved).

## Using it

The panel works like Mutable Dreams. Each group button opens its pages; press it again for the next page. The
four knobs set the four values on screen.

| Group | Pages (knobs 1 to 4) |
|---|---|
| HOME | the four lanes: hits, steps, speed, chance |
| SEQ | RHYTHM: hits, steps, speed, chance, the bar drawn as a circle. FEEL: rhythm source (Euclid, rotate with accents, cellular automaton, ratchet) and its knobs. NOTES: note source (random, walk, up, down, bounce, loop, turing, step, markov, grammar, chord) and its knobs. RANGE: scale, low note, chord follow. `docs/SEQUENCERS.md` |
| EDIT | SOUND: shape (48 Braids, 8 FM, 10 drums), timbre, colour, level. FILTER: cutoff, resonance, envelope, low/band/high. ENVELOPE: attack, release, envelope to timbre. MIX: lane levels. PAN |
| LFO | target (OFF, CHANCE, LEVEL, TIMBRE, COLOUR), rate in bars, depth, for the chosen lane (`lfo_modulate_in_range`) |
| FX | REVERB: send, decay, bright, return. DELAY: time, feedback, tone, return. `docs/FX.md` |
| GLO | HARMONY: key, scale lock, chord progression, bars per chord. SYSTEM: tempo, keys octave, LOOK (seven colour schemes), SWING. MIDI: channels, INT or EXT clock. BANKS: patch, save slot, DEMO, AUTO (plays the demo songs in turn, changing a lane every 8 bars) |

| Control | Does |
|---|---|
| SELECT | pick a lane (in a browser: the group) |
| PRESETS | the browser: sounds on EDIT (255, by engine or by type), patches elsewhere (142 factory, 8 user). ALGO changes the grouping while it is open |
| ALGORITHM | tempo |
| PLAY | start or stop; stopping silences everything |
| SEL | mute the chosen lane |
| REC | PUNCH: while the page is up the keys are momentary effects on the mix, like the OP-XY's punch-in FX. HALF and DOUBLE time, STUTTER, ROLL, OCT- and OCT+, SHIFT, GATE, CRUSH, WASH (reverb up), THROW (delay up), BREAK (all muted), then mute lane 1 to 4, then re-roll lane 1 to 4. The knobs set the rates. Let go and the effect is gone: with no key held every effect is the identity (`punch_nothing_held_changes_nothing`); the gate gain fades over 1.5 ms (`punch_gate_glides`) |
| SAVE | save the patch to the slot chosen on GLO > BANKS |
| ARP | held keys play one at a time in step with the clock, on the chosen lane's sound (MODE, RATE, OCTAVES, GATE). ARP again while holding keys latches them. ARP with nothing held opens QUANT: OFF, SCALE (white keys are the scale degrees) or CHORD (white keys are the current chord). `keys_in_scale`, `keys_keep_order` |
| keys, OCT- OCT+ | play the chosen lane's sound |

## How it works

A lane divides the clock into a rhythm, and on every hit picks a note and snaps it to the scale. Rhythms come
from Euclidean patterns (rotated and accented if you like), a cellular automaton, or ratchets. Notes come from
the eleven sources above; MARKOV learns from what you play, GRAMMAR rewrites a phrase, TURING is a shift
register with a flip chance.

Chord progressions (GLO > HARMONY) are written as degrees: 1-4-5-1 is I IV V in a major key and i iv v in a
minor one. A lane follows them with 7TH or TRIAD on SEQ > RANGE. The chords are stacked from the key's scale, so
a lane that follows one of the eight table progressions stays in key (`harmony_follow_in_key`; the three walks
below leave it on purpose). COMPL does the opposite: only the notes outside the key. Those have the scale's
intervals, each shifted by the same count (two fewer for a seven-note scale, two more for a pentatonic):
Babbitt's hexachord theorem in general form (`harmony_complement_interval_content`), and why BLACK KEYS still
sounds like C major.

The last three progressions walk the Tonnetz (`Firmware/Tonnetz.lean`): each move is P, L or R, which keeps two
notes of the triad and changes one. WALK LR visits all 24 major and minor triads and comes back; WALK PL is a
hexatonic cycle of six, WALK PR an octatonic cycle of eight. `Proofs/Tonnetz.lean` does the group theory: P, L
and R generate the dihedral group of order 24, which is why every walk comes home and sounds the same in every
key.

The voices are all 48 Braids shapes from Mutable's source (`voices/`), each engine's sample arithmetic moved
into Lean and checked against the C++ sample for sample (`make test-lean`). Then a four-operator FM voice
(`Firmware/Fm.lean`: piano, bell, bass, brass, glass, mallet, organ, clang) whose sine is a polynomial, not a
table, so its bound, symmetry and continuity are checked at every phase (`fm_sine_bounded`, `fm_sine_half_wave`,
`fm_sine_continuous`). Then ten 808 drums (`Firmware/Drum.lean`) made from a swept sine, a 16-bit noise
generator, one-pole filters and the 808's six-square metal bank. TIMBRE is decay, COLOUR is tone. Every sound
goes through a state-variable filter (`Firmware/Filter.lean`), which at its default is an exact bypass. `make
audit` checks the level of every factory sound.

## What is proved

<!-- proofs:begin -->
313 theorems, checked by Lean's kernel and by `make comparator`. Generated from the docstrings
in `Proofs/` by `make proofs`; `docs/PROOFS.md` has the full statements.

<details><summary><b>The sequencer</b>: 104 theorems</summary>

The four lanes. No note is left sounding when you stop, the lanes stay in phase, at play chance 100 a bar plays exactly
the hits set and never a rest below it, and every note is in the scale and the range.

| Theorem | Says | Protects against |
|---|---|---|
| `lane_make_valid` | `make` gives a valid lane for any settings. | out-of-range values from the screen or a saved file cannot produce an invalid lane. |
| `lane_reconfigure_valid` | `reconfigure` keeps a valid lane valid for any settings. | turning a knob mid-song cannot push a position or timer out of range. |
| `lane_set_notes_valid` | `setNotes` keeps a valid lane valid for any settings. | switching note algorithm mid-song cannot leave the loop position outside the loop. |
| `lane_tick_valid` | A tick keeps a valid lane valid. | counters, note memory and the sounding note stay consistent for any number of ticks. |
| `lane_gate_end_stops_note` | When a sounding note's gate runs out, the tick reports it as stopped. | no stuck notes. |
| `lane_new_note_stops_old` | A tick that starts a note also stops the one sounding before it. | a lane never has two notes on at once. |
| `lane_note_only_on_hit` | A note starts only on a step the rhythm marks as a hit (for a ratchet sub-hit, the step that just pulsed). | a rest never plays, regardless of note algorithm or play chance. |
| `lane_note_in_scale` | A note a tick starts is at most 127 and is in the lane's scale. | the lane never plays a note the voices reject or one outside the chosen key. |
| `lane_silence_valid` | `silence` keeps a valid lane valid. | stopping the clock cannot leave a timer without a note or a note without a timer. |
| `lane_silence_stops_note` | `silence` reports the sounding note as stopped and leaves nothing sounding. | stop never leaves a note hanging. |
| `lane_reconfigure_self` | Applying a lane's own settings back to it changes nothing, for a valid lane whose settings are within knob range and whose gate is `gateFor div`. | saving and reloading a patch, or redrawing a knob at its current value, does not change the lane. |
| `lane_set_rhythm_valid` | `setRhythm` keeps a valid lane valid for any settings. | switching rhythm source mid-song cannot break the lane. |
| `lane_learn_valid` | `learn` (a key press) keeps a valid lane valid. | playing along or programming the step sequencer cannot break the lane. |
| `lane_from_patch_keeps_feel` | A patch lane that fits (`PatchLane.Fits`) gives a lane with exactly the patch's rhythm settings: no clamp in `Lane.make` or `Rhythm.make` changes a fitting value. | the FEEL settings a patch saves are the ones it plays back. |
| `run_every_note_on_has_a_note_off` | After any sequence of ticks and setting changes from a fresh lane, note-ons equal note-offs plus the one note still sounding; `silence` then stops that note and leaves nothing sounding. | no stuck notes over a whole performance, not just one tick. |
| `run_clock_never_drifts` | After `n` ticks from a fresh lane the step position is `(n / div) % steps`, regardless of the notes played. | lanes at different speeds stay in phase; notes cannot make a lane drift. |
| `run_bar_plays_the_rhythm` | A lane with the Euclidean, rotated or automaton rhythm (any kind but ratchet) at play chance 100 plays, over the `steps * div` ticks of a bar from a fresh lane, exactly the hits its rhythm marks in that bar (for the automaton, the hits of its row at the start of the bar). | for every non-ratchet FEEL setting the bar plays exactly the row of hits the screen shows. |
| `run_bar_plays_every_hit` | A plain lane (Euclidean source, play chance 100) has exactly `hits` note-ons over the `steps * div` ticks of a bar from a fresh lane, for any settings (`make` clamps them to knob range). | the safety theorems say a lane never plays on a rest; this one says it plays on every hit. |
| `run_bar_plays_every_hit_turned` | A rotated lane (Euclidean source turned by ROTATE, play chance 100) also plays exactly `hits` notes in a bar. | ROTATE never loses or doubles a hit. |
| `run_bar_plays_every_ratchet` | A ratchet lane (kind 3, play chance 100) with `ratchet ≤ div` plays, over the `steps * div` ticks of a bar from a fresh lane, exactly `hits` times the number of sub-hits that play; every hit step rolls the same sub-hits, each on its own tick. | ratchets play exactly the rolls the knobs ask for, so every rhythm kind has a liveness theorem. |
| `rhythm_automaton_row_fits` | One automaton generation stays inside the bar: the new row has no bit at or beyond `steps` (`steps ≤ 32`). | a hit can never land on a step that does not exist, however long the automaton runs. |
| `rhythm_accent_only_on_hit` | An accent only falls on a hit. | accents cannot add a note on a rest. |
| `rhythm_rotate_keeps_hits` | A rotated bar (ROTATE) has exactly `hits` hits, like the plain one. | ROTATE never adds or loses a note. |
| `rhythm_rule_zero_dies` | Rule 0 kills the row: after one generation nothing plays. | rule 0 is silence; the reseed on a dead row is what brings the bar back. |
| `rhythm_rule_full_fills` | Rule 255 fills the bar: after one generation every step plays. | the RULE knob spans from silence (0) to every step (255). |
| `rhythm_rule_204_freezes` | Rule 204 freezes the bar: a row that fits the bar comes back unchanged every generation. | at rule 204 the automaton plays exactly the Euclidean bar it was seeded with. |
| `swing_tick_in_range` | Every tick is between 1/3 and 5/3 of a straight tick, at every swing setting. | swing cannot make a tick vanish (two steps firing at once) or stretch one past the next eighth. |
| `swing_keeps_time` | A tick of the first eighth plus a tick of the second is exactly two straight ticks, so a pair of eighths (12 ticks) takes exactly 24 straight ticks at any swing. | swing only moves notes within each pair of eighths; bar length and lane phase are unchanged. |
| `swing_quarter_note_exact` | A swung quarter note is exactly 24 straight ticks long at every setting, and each tick inside it is at least 3334 long, so ticks never coincide. | swing does not change the tempo, and an outgoing MIDI clock stays in step. |
| `divider_pulse_count` | A divide-by-`div` counter started at 0 gives exactly `ticks / div` pulses after `ticks` ticks. | the clock divider never drops or doubles a beat. |
| `divider_count_bounded` | The count stays below `div`. | the counter stays bounded however long it runs. |
| `euclid_hit_count` | A bar of `steps` steps with `hits` hits (`hits ≤ steps`) has exactly `hits` hits. | the pattern has exactly the density HITS asks for. |
| `euclid_last_step_hits` | The last step of a bar is a hit whenever `hits > 0`. | every Euclidean pattern ends on a hit; the ratchet's first sub-hit relies on this. |
| `euclid_window_balanced` | Any window of `len` steps, wherever it starts (wrapping across the bar line), contains `len * hits / steps` hits or one more. | the hits never bunch; this is Clough–Douthett maximal evenness for the pattern the firmware plays. |
| `euclid_windows_within_one` | Two windows of the same length differ by at most one hit. | any two bars, half-bars or beats carry the same number of hits or one apart. |
| `euclid_is_christoffel` | For `hits < steps`, step `k` is a hit exactly when `(k + 1) * hits` wraps modulo `steps`: the pattern is the lower Christoffel word of slope `hits / steps` in Berstel's form (`hits = steps` is every step). | known results on Christoffel words (balance, conjugates are the Euclidean rhythms, reversal is the upper word) apply to these patterns. |
| `euclid_bjorklund_is_rotation` | Bjorklund's algorithm (Toussaint's form) gives a rotation of `Euclid.hit`, for every bar of up to 32 steps and every hit count, checked case by case. | the firmware's floor-function pattern is the usual "Euclidean rhythm" up to rotation, which ROTATE reaches. |
| `euclid_major_scale_is_seven_of_twelve` | The major scale mask is the 7-of-12 Euclidean pattern started on step 6; the major pentatonic mask is the 5-of-12 pattern started on step 7. | the SCALE table and the Euclidean rhythm are one construction (Clough–Douthett). |
| `notes_start_valid` | A fresh note memory is valid for any span from 1 to 65535 and any loop length from 1 to 16. | the lane starts in a state the algorithms can rely on, whatever the seed. |
| `notes_choose_stays_in_range` | Whichever algorithm picks, the offset is below `span` and the memory stays valid. | no algorithm can pick outside the range or corrupt the memory the next pick depends on. |
| `notes_up_visits_every_position` | UP climbs one position a note and wraps: from position `p` the `i`-th note is at `(p + i) % span`, so the first `span` notes visit every position once. | an UP lane covers its whole range with no position skipped or repeated. |
| `notes_down_visits_every_position` | DOWN falls one position a note and wraps: from `p` the `i`-th note is at `(p + (span - 1) * (i + 1)) % span`, so the first `span` notes visit every position once. | a DOWN lane covers its whole range with no position skipped or repeated. |
| `notes_bounce_moves_one` | BOUNCE moves at most one position a note, for a span of at least 2. | a BOUNCE lane never leaps. |
| `notes_walk_bounded` | WALK moves at most `amount` positions a note (the step is drawn below `2 * amount + 1`). | AMOUNT bounds how far a WALK lane can jump between notes. |
| `notes_loop_repeats` | LOOP with MUTATE at 0 repeats the same `amount` notes: the memory never changes and the slot wraps. | MUTATE 0 is an exact loop. |
| `notes_markov_moves_at_most_three` | MARKOV moves at most three positions a note, jump or not (move classes are -3 to +3; a doubled move is clamped to that range). | a MARKOV lane never leaps, whatever it learnt from the keys or the style. |
| `notes_grammar_moves_at_most_two` | GRAMMAR moves at most two positions a note: its symbols step or skip, up or down. | a GRAMMAR lane never leaps, for any grammar and depth. |
| `notes_learn_keeps_valid` | `learn` (a key press) keeps the memory valid for any note: the step sequencer stores it in range, the markov chain counts it. | nothing played on the keys can corrupt the memory. |
| `notes_turing_locked_repeats` | TURING with FLIP at 0 is a locked loop: after `len` picks the register's `len`-bit window is unchanged, so the notes repeat every `len` picks (once the bits above the window, which the first picks still read, have been shifted out). | FLIP 0 is an exact loop of LENGTH notes; only FLIP changes it. |
| `notes_grammar_phrase_never_empty` | A grammar's phrase is non-empty at every depth. | the GRAMMAR source never has to fall back to a default symbol. |
| `notes_scale_tone_in_scale` | The `n`-th scale tone above `low` is in the scale whenever the scale has more than `n` notes in the five octaves above `low`. | the CHORD source climbs real scale (or chord) tones; the snap has nothing to fix. |
| `quantizer_snap_keeps_scale_notes` | A note already in the scale is unchanged by `snap`. | quantizing an in-key melody changes nothing. |
| `quantizer_snap_in_scale` | `snap` gives a note of the scale, for a non-empty 12-bit mask and a note of at least 6 (so the 6-semitone search down cannot run off the bottom). | the lane never plays a note outside the chosen key. |
| `quantizer_snap_is_near` | `snap` moves a note at most 6 semitones (same conditions as above). | quantizing keeps the shape of the melody. |
| `quantizer_snap_monotone` | `snap` is monotone: for two notes of at least 6 and a non-empty mask, the higher never snaps below the lower (same conditions as the other snap theorems). | quantizing can merge two notes onto one scale note but cannot reverse a line's direction. |
| `random_below_lt` | `Random.below` returns a value below `limit` (for `0 < limit ≤ 65535`). | a pick is always a valid index into a list of `limit` choices. |
| `random_never_stands_still` | No state maps to itself under `Random.next`: `next x = x` would need `(a - 1) * x ≡ -c` mod 2^32, but `a - 1` is a multiple of 4 and `c` is odd. | the generator can never get stuck on one value, whatever the seed. |
| `harmony_mask_never_empty` | The mask handed to a lane is non-empty and fits in 12 bits, for every scale, key, progression, chord step and follow mode, Tonnetz walks included. | `lane_note_in_scale` needs a non-empty 12-bit mask; a chord change can never leave a lane with nothing to play. |
| `harmony_follow_in_key` | On a table progression with chord follow 7TH or TRIAD, every note a lane may play is in the key's scale: the chord is stacked from the key's scale at the chord root, not a transposed shape. | chord follow on a table progression stays in key. |
| `harmony_progression_chord_has_root` | With chord follow 7TH or TRIAD the chord's root is among the lane's notes, for every scale and key, on tables and walks alike. | a following lane can play the root, not only upper notes of the chord. |
| `harmony_chord_root_in_key` | On a table progression every chord root is a note of the key's scale (below an octave). | progressions are written as degrees, so 1-4-5-1 is I IV V in major and i iv v in minor; a table chord never lands outside the key. |
| `harmony_walk_chord_is_triad` | On a Tonnetz walk (progressions 8 and up) with chord follow 7TH or TRIAD, a lane plays exactly the walk's triad transposed to the key: three notes, the chord the screen names. | walks leave the key on purpose, and the lane plays exactly the named triad. |
| `harmony_walk_keeps_two_notes` | Consecutive chords of any Tonnetz walk share exactly two pitch classes. | P, L and R each change one note of a triad, so a walk moves one note at a time. |
| `harmony_complement_outside_key` | COMPL (chord follow 3) plays exactly the notes outside the key's scale, for every scale, key and chord; the chromatic scale plays whole. | a COMPL lane never shares a note with a lane in the key. |
| `harmony_complement_interval_content` | The complement theorem (Lewin's generalisation of Babbitt's hexachord theorem) for any cycle `Z_n` and any set: the ordered count of pairs at distance `d` in the complement equals the count in the set plus `n - 2 * size`. | a scale and the notes it leaves out share their interval content, which is why COMPL sounds like the key it was cut from. |
| `harmony_hexachord_theorem` | Babbitt's hexachord theorem on the 12-bit masks: every six-note mask has the interval vector of its complement, checked for all 4096 masks. | the `n = 12`, `size = 6` instance of `harmony_complement_interval_content` on the masks the lanes play from. |
| `tonnetz_moves_are_involutions` | Each of P, L and R is an involution. | a walk can always be retraced; this is the first dihedral relation. |
| `tonnetz_group_has_order_24` | The group generated by P, L and R has exactly 24 elements: every word acts as one of the 24 listed elements, and no two of those act alike. | the walks live in a small, fully known group (the neo-Riemannian PLR group). |
| `tonnetz_simply_transitive` | The group acts simply transitively on the triads: from any triad exactly one element reaches any other. | every triad is reachable from every other, and a word's effect is fixed by where it sends one triad. |
| `tonnetz_commutes_with_transposition_and_inversion` | The PLR group commutes with every transposition and every inversion (Lewin's duality). | a walk sounds the same in every key, and a walk from a minor triad is the inversion of the walk from a major one. |
| `tonnetz_group_is_dihedral` | The dihedral relations: L R has order exactly 12, L has order 2, and L conjugates L R to its inverse R L. | with `tonnetz_group_has_order_24` this identifies the group as the dihedral group of order 24. |
| `tonnetz_walks_are_cycles` | From any start, the L R walk visits all 24 triads once and returns after 24 moves; the P L walk is a 6-cycle (hexatonic) and the P R walk an 8-cycle (octatonic). | L R is a Hamiltonian cycle on the Tonnetz; P L and P R are the two short cycles. |
| `arp_note_is_held` | Every note the arpeggiator starts is a held note raised by fewer than `octaves` octaves. | the arpeggiator never adds a note of its own, in any mode. |
| `arp_make_valid` | `Arp.make` gives a valid arpeggiator for any `div`. | the arpeggiator starts in a state the rest of the firmware can rely on. |
| `arp_set_valid` | `Arp.set` keeps a valid arpeggiator valid for any settings. | turning the ARP knobs mid-phrase cannot push a timer or counter out of range. |
| `arp_keys_valid` | Pressing, releasing or clearing keys keeps a valid arpeggiator valid. | the held set stays playable and bounded however many keys are pressed. |
| `arp_tick_valid` | A tick keeps a valid arpeggiator valid. | counters stay in range and the sounding note and its timer agree for any number of ticks. |
| `arp_every_note_on_has_a_note_off` | After any sequence of ticks, keys and setting changes from a fresh arpeggiator, note-ons equal note-offs plus the one note still sounding, which `silence` stops. | releasing the keys or stopping never leaves an arpeggio note hanging. |
| `arp_up_plays_pattern` | UP with `div = 1` from position 0 plays the pattern through in order: as many ticks as the pattern has notes start exactly the pattern. | UP plays each held note once, in order, per lap; the position returns to 0 so later laps read the same. |
| `machine_every_note_on_has_a_note_off` | Across the four lanes and the arpeggiator, after any lists of ticks, knob changes and keys from a quiet machine, note-ons equal note-offs plus what is still sounding, and `stop` leaves nothing sounding. | no stuck notes for the whole instrument, not one part at a time. |
| `lfo_modulate_in_range` | A modulated value is at most 100, for any base, depth and phase. | an LFO cannot push a chance, level or timbre setting out of range. |
| `lfo_triangle_symmetric` | `Lfo.triangle (~~~phase) = Lfo.triangle phase`: the triangle is symmetric about its peak. | the modulator rises and falls by the same path, with no jump at the turn. |
| `lfo_modulate_centred` | At the middle of the swing (phase 2^30) the modulator returns the base unchanged (for `base, depth ≤ 100`), and depth 0 never changes anything. | the knob's value is the centre of the motion, so an LFO does not shift the average; depth 0 gives exactly the set value. |
| `punch_nothing_held_changes_nothing` | With no key held every effect is the identity: tempo 100 percent, no re-strike, note unchanged, gate open at full gain, crush holding nothing, reverb and delay at their settings, no lane muted. | there is no effect state beyond the keys; releasing the last key restores the performance exactly. |
| `punch_note_in_range` | A punched note is at most 127, for any keys, shift and note. | OCTAVE and SHIFT cannot push a note past the range the voices accept (`play` drops notes above 127); edge notes are clamped instead. |
| `punch_tempo_in_range` | The clock speed is 50, 100 or 200 percent. | HALF and DOUBLE cannot stop the clock or run it away. |
| `punch_gate_half_open` | Over any whole period that does not cross the tick counter's end, the gate is open for exactly half the ticks. | GATE is an even square at the rate the knob says, however the period lines up with the bar. |
| `punch_gate_glides` | The gate gain stays between 0 and 32768 and moves toward its target by at most 512 a sample, landing on it exactly. | a chop is a 1.5 ms slope, so GATE never clicks, and the gain never exceeds unity. |
| `punch_crush_repeats` | A crushed sample is either the fresh sample or the held one. | CRUSH adds nothing new, so the output stays inside every bound the mix had. |
| `punch_restrikes_on_the_beat` | A non-zero re-strike period divides the quarter note (24 ticks). | STUTTER and ROLL land on the beat's divisions and come back to the beat. |
| `keys_off_is_itself` | QUANT off returns the key unchanged (clamped to 127). | OFF is exactly the plain keyboard. |
| `keys_in_range` | A quantized note is at most 127, for any mode, mask, key and note. | a high degree from the top of the keyboard is clamped at 127, not wrapped. |
| `keys_in_scale` | With QUANT on and a non-empty mask, every quantized note below 127 has its pitch class in the mask. | in SCALE or CHORD mode the keyboard cannot play a note outside the scale or chord. |
| `keys_keep_order` | Within an octave a higher key never plays a lower note, in any mode. | quantizing cannot turn a rising line into a falling one. |
| `keys_triad_three_an_octave` | With CHORD on a Tonnetz walk the lane's mask is a triad, and white key `w + 3` plays white key `w` an octave up. | the white keys are the chord of the moment, three to the octave. |
| `keys_triad_is_the_chord` | With CHORD on a Tonnetz walk, each of the white keys C E G plays a note of the walk's triad. | the first three white keys can only sound chord tones. |
| `keys_triad_white_keys_are_the_chord` | With CHORD on a Tonnetz walk, the pitch classes of white keys C E G together are exactly the walk's triad, in rising order from the key's root (so degree 0 is the triad's root only when the walk is on the tonic). | the first three white keys are the whole chord and nothing else, laid out low to high. |
| `punch_gate_never_amplifies` | The gate never amplifies: with gain at most 32768 (Q15 unity) and a sample within 524287, the output is no larger than the sample and within 524287. | a sample inside the limiter's range stays inside it through the gate and cannot wrap. |
| `punch_crush_keeps_limit` | The crush returns one of its two inputs, so a mix and a held sample both within 524287 give a sample within 524287. | CRUSH cannot wrap. |
| `punch_master_never_wraps` | The whole PUNCH audio path keeps the master within 524287, given a mix sample within 524287 (what `mix_machine_sample_bounded` delivers), a held sample within the same bound, any crush factor and index, and a gate gain of at most 32768. | with every punch-in on at once, nothing on the PUNCH page can wrap. |
| `clock_advance_never_wraps` | The clock accumulator never wraps: for a stall of up to 20 s, tempo up to 240 and a tempo factor up to 200 percent, starting from any residue below the longest swung tick, the 32-bit sum is the exact sum. | after a long main-loop stall (patch load, save, redraw) the clock makes up the missed time instead of jumping the song. |
| `clock_division_is_the_loop` | `ticksDue` and `remainder` describe the firmware's `while (acc >= len) { acc -= len; tick(); }` loop: ticks due times the length plus the remainder is the accumulator, and the remainder is below one tick. | every fact about `ticksDue` and `remainder` is a fact about the loop in `dinghy.c`. |
| `clock_half_time_is_half` | Over the same milliseconds from the same residue, HALF fires half the ticks of straight time to within one tick of rounding: `2 * half ≤ straight + 2` and `straight ≤ 2 * half + 1` (straight ticks of 10000, swing 0). | a bar under HALF is two bars long to the tick, so lanes, swing and chord changes stay in step. |
| `clock_double_time_is_double` | Over the same milliseconds from the same residue, DOUBLE fires twice the ticks of straight time to within one tick of rounding: `double ≤ 2 * straight + 1` and `2 * straight ≤ double + 2` (straight ticks of 10000, swing 0). | a bar under DOUBLE is half a bar long to the tick, so lanes, swing and chord changes stay in step. |

</details>

<details><summary><b>The voices</b>: 133 theorems</summary>

Braids' engines in Lean, the FM voice, the 808 and the filter. Table reads stay inside their tables, the shipped tables
meet what the proofs assume, and a sample is the arithmetic clipped, not wrapped, except where Braids itself overflows
(docs/LEAN-ENGINES.md).

| Theorem | Says | Protects against |
|---|---|---|
| `pitch_table_reads_inside` | Every pitch reads two neighbouring entries of the 97-entry phase step table, both inside it. | the table is C data read without a check; the clamp to note 128 and the fold into one octave keep the read inside for any 16-bit pitch, including the negative ones a detuned FM operator asks for. |
| `pitch_increment_bounded` | The step is below half a cycle per sample. | the table's top entry is above half a cycle, so the bound comes from the clamp, which puts every pitch at least one octave below the table; a step below half a cycle keeps the oscillators under Nyquist. |
| `tables_phase_reads_inside_257` | A phase reads two neighbouring entries of a 257-entry table, both inside it, for any phase. | the sine, bell, cutoff, damping and comb tables all have 257 entries, so every blend of them (`Analog.sineAt`, `Digital.lutAt`, `Analog.buzz`) stays inside without a check. |
| `tables_shape_reads_inside_257` | A 16-bit index reads two neighbouring entries of a 257-entry wave shaper, both inside it. | the overdrive and fold shapers have 257 entries; `Analog.shape` is safe for any index below 65536, which is why its callers mask or bound what they pass. |
| `tables_resonator_reads_inside_129` | A pitch, after the resonator's clamp, reads inside the 129-entry resonator tables. | without the clamp to 16383 a high note would read past them. |
| `tables_wave_reads_inside_129` | A wave phase, halved as the wavetable engines do, reads inside a 129-byte wave. | Braids' waves are 129 bytes, half what the phase could address; the halving keeps the read inside. |
| `tables_wave_line_reads_inside_129` | A wave phase, halved and then masked to fewer steps as the wave line's rough reading does, reads inside a 129-byte wave. | the mask can only lower the phase, so the rough reading stays inside like the plain one (`tables_wave_reads_inside_129`), for any mask. |
| `tables_formant_reads_inside_256` | A formant phase and an amplitude of 0 to 15 read inside the 256-entry formant tables (16 phases by 16 amplitudes). | the vowel's formant amplitudes are 4-bit by construction of its data, so no phase can read past the formant sine or square table. |
| `braids_data_increments_rising` | The phase step table rises from one entry to the next for every index the code reads (below 96: `pitch_table_reads_inside`); the entry after the last is the copy's tail, so it is excluded. | `pitch_increment_bounded` blends two neighbouring entries and needs the second to be the larger; this checks it against the data Braids ships. |
| `braids_data_increments_close` | Two neighbouring phase step entries differ by less than 2^27 for every index the code reads (below 96). | the blend multiplies that difference by a 4-bit fraction in signed 32-bit arithmetic, and 2^27 * 15 is the most that fits. |
| `braids_data_increments_top` | No phase step entry passes 2588618730, the table's last, at any index. | the setup shifts the entry down at least one octave, and this top puts the result below half a cycle (`pitch_increment_bounded`). |
| `braids_data_cutoff_rising` | The filter cutoff table rises from one entry to the next for every index a phase reads (below 256: `tables_phase_reads_inside_257`). | `filters_setup_cutoff_in_range` blends two neighbouring entries and needs the second to be the larger; this checks it against the data Braids ships. |
| `braids_data_cutoff_top` | No filter cutoff entry passes 25078, the table's last, at any index. | the swarm's high-pass coefficient is a blend of two entries, so this is its range, which the filters' sample theorems take. |
| `braids_data_rate_top` | No grain envelope rate entry passes 32768, the table's last, at any index. | `noise_setup_grain_rate_bounded` shifts the entry up three places and needs the result below 2^18 to keep the grain's envelope reads inside their table. |
| `braids_data_vowel_amplitudes_are_nibbles` | Every vowel formant amplitude is a nibble (at most 15), for any vowel and formant. | the formant tables are indexed by the phase's top nibble or-ed with the amplitude (`tables_formant_reads_inside_256`); an amplitude above 15 would read past them. |
| `braids_data_wavetable_steps_at_most_16` | Every wavetable definition has at most 16 steps, for any table index. | `wavetables_setup_table_in_table` multiplies the parameter by the step count and needs the pointer's step and the one after it inside the 17 steps of a definition; Braids ships 4, 8 or 16. |
| `fm_sine_bounded` | The sine is within ±32767 for every phase. | an operator never hands its modulators or the mix more than full scale; there is no table, and the polynomial is checked for every input. |
| `fm_sine_exact_at_quarters` | The sine is 0 at the start, 32767 at a quarter, 0 at a half and -32767 at three quarters (32767 is one). | an operator at rest is zero and a peak is exactly full scale, so the shapes' levels and depths mean what they say. |
| `fm_sine_continuous` | From one position to the next the quarter sine rises by at most two and falls by at most one (the fall is rounding), for every position. | the polynomial has no step, so no click or buzz of its own; checked at all 32767 positions. |
| `fm_operator_never_wraps` | An operator's output is its sine through its envelope, at most 32767 in size for any envelope up to one (2^24), and nothing wraps. | an operator's output is in range whatever its modulators did, so no depth setting can overflow it. |
| `fm_carry_never_amplifies` | A carrier's share is at most its output, for a level at most one (32767). | the mix of carriers is at most the sum of their levels, so a shape with levels summing to one cannot clip (`fm_shapes_in_range`). |
| `fm_saturate_in_range` | The voice's output sample is within ±32767, and a sum already in range passes unchanged. | the hold at full scale is a saturation, not a wrap. |
| `fm_envelope_only_falls` | The envelope one block on is no higher, and no lower than 15/16 of itself, for any rate below 65536 and envelope up to one; nothing wraps. | an operator's envelope only falls, by at most a sixteenth a block. |
| `fm_increment_below_nyquist` | An operator's increment is at most half a cycle a sample for any pitch and ratio. | an operator asked for more than Nyquist is held there instead of wrapping to a wrong pitch. |
| `fm_algorithms_well_founded` | In every algorithm a modulator is a higher-numbered operator than the one it modulates, and operator 1 always carries. | computing operators 4 down to 1, every modulator's output is already this sample's (no one-sample lag and no cycle except the declared feedback on 4), and every algorithm makes a sound. |
| `fm_shapes_in_range` | Every shape's settings are in the ranges the theorems above need: ratios at most 16 (4096 in Q8), levels at most one (32767), rates below 65536, and a shape's carrier levels sum to at most one. | with `fm_carry_never_amplifies` the eight shapes cannot clip at full envelope, and `fm_envelope_only_falls` applies to their rates. |
| `fm_harmonic_ratios_lock` | With both starting at phase 0, an operator at integer ratio `r` (Q8 value `r * 256`) has phase exactly `r` times the carrier's after any number of samples, modulo 2^32. | an integer ratio is exactly harmonic; the two phases never drift apart or beat. |
| `fm_integer_ratio_periodic` | The operator's waveform at integer ratio `r` is a function of the carrier's phase alone. | carrier plus operator is then periodic with the carrier, so the spectrum is exactly harmonic. |
| `fm_organ_and_bass_lock` | FM ORGAN (shape 54) and FM BASS (shape 50) use integer ratios on every operator; FM BELL (shape 49) does not. | the organ and bass are exactly harmonic by `fm_harmonic_ratios_lock`; the bell's ratios of 3.5, 7.2 and 1.4 are inharmonic by design. |
| `fm_sine_half_wave` | The sine half a cycle on is the negative of the sine: `sineAt (phase + 2^31) = -sineAt phase` for every phase (the quadrant moves by two, the place in the quarter is unchanged, the sign flips). | a half-wave-symmetric waveform has no DC and no even harmonics, so the polynomial's error sits at odd harmonics only. |
| `fm_sine_quarter_wave` | The sine is mirrored about the quarter points: `sineAt (0x7FFFFFFF - phase) = sineAt phase` for every phase. | the engine evaluates the polynomial on 0 to 32767 only and reads the other three quarters by mirror and sign; this symmetry is what makes that exact. |
| `fm_sine_pairs_cancel` | Two samples half a cycle apart cancel exactly: `sineAt p + sineAt (p + 2^31) = 0` as integers for every phase (the negation cannot wrap, the sine being within 32767). | this is the pairing behind `fm_sine_has_no_dc`. |
| `fm_sine_has_no_dc` | Any 256 samples of the sine spaced a 256th of a cycle apart sum to zero, from any starting phase: sample `k` and sample `k + 128` are half a cycle apart and cancel (`fm_sine_half_wave`). | a carrier at any pitch and phase adds no DC to the mix over a cycle, and the polynomial's error has no even harmonics. |
| `fm_envelope_after_bounded` | The envelope after `k` blocks at `rate` is at most its start times `((2^20 - rate) / 2^20)^k` plus 17 counts a block for rounding (both sides scaled by `2^20^k` to stay in whole numbers), for any start up to one (2^24) and rate below 65536; and it never passes one. | an envelope decays geometrically with time constant `2^20 / rate` blocks; rounding cannot pile up into a floor. |
| `fm_held_envelope_holds` | At rate 0 the envelope holds exactly. | `0` in the rate table means hold with no drift from rounding (the piano's body, every organ operator). |
| `fm_shape_tails` | For every shape's decaying operators, from a full envelope (2^24) at the table's rate: the first block at which the envelope is under a tenth, and under a hundredth, stepped block by block in the kernel, with the block before still above (a block is 16 samples, 0.36 ms at 44.1 kHz). | these are the decay times a player hears, computed from the arithmetic the chip runs. |
| `fm_no_operator_idle` | In every algorithm every operator either carries or modulates some operator; none of the four is wired to nothing. | an operator that neither sounds nor modulates would be a quarter of the voice computed every sample for nothing. |
| `fm_algorithms_distinct` | The eight algorithms are pairwise different: any two differ in some modulation link or in which operators carry. | no two positions of the algorithm knob wire the operators the same way. |
| `fm_every_shape_uses_four_operators` | In every shape every operator is either a carrier of the shape's algorithm or has nonzero depth and modulates some operator in it; no shape has a silent modulator. | a modulator with depth zero would run its sine and envelope every sample for nothing. |
| `fm_sine_lipschitz` | The sine is Lipschitz in the phase: between two phases it moves by at most two per position (2^15 phase units) crossed, plus one more for the partial positions at either end. | a bounded phase step reads a bounded change in value, which is what bounds a modulator's slew and a carrier's frequency deviation (`fm_modulator_slew`, `fm_carrier_frequency_deviation`). |
| `fm_modulator_slew` | An unmodulated operator at increment `incM` and envelope `env` (at most one) changes by at most `2 (incM / 2^15 + 1) + 1` a sample: two per position its phase crosses, one for the envelope rounding. | a modulator's slew is proportional to its increment, which is what makes FM's frequency deviation proportional to the modulating frequency. |
| `fm_carrier_frequency_deviation` | A carrier at increment `incC` pushed by a modulator (`Fm.push 0 out depth`, `out` the modulator's output each sample): the push changes from one sample to the next by `depth` times the change in `out` (modulo 2^32), so the pushed phase advances by `incC` plus that term; the change in `out` is at most `2 (incM / 2^15 + 1) + 1` (`fm_modulator_slew`), so the change in the push, as an integer, is at most `depth` times that. | the carrier's peak frequency deviation is at most `depth (2 (incM / 2^15 + 1) + 1)` phase units a sample, proportional to modulation index times modulator frequency, as Carson's rule says. |
| `fm_cap_is_a_hold` | The cap is a saturation of the exact value: the increment is the product shifted by eight, or half a cycle, whichever is smaller. | above the keyboard an operator holds at Nyquist instead of wrapping to a wrong pitch; below it nothing is lost. |
| `fm_increment_exact_below_cap` | Below the cap the increment is the exact product shifted by eight: a product below 2^39 shifts to below 2^31, so neither the hold nor the narrowing to 32 bits changes it. | an operator's pitch is exactly the voice's times the shape's ratio, with no rounding beyond the Q8 shift. |
| `fm_no_cap_on_the_keyboard` | For MIDI notes 0 to 88 (up to E6, 1319 Hz) every operator's increment is the exact product of the voice's increment and its shape's ratio, shifted by eight; the Nyquist cap never engages. | every FM shape's ratios are exact across the playable keyboard; above it the engine saturates at Nyquist (`fm_cap_is_a_hold`). |
| `drum_noise_period` | The noise register from state 1 returns to 1 after exactly 65535 steps and not before: its period is 65535, every nonzero 16-bit state (the taps are a primitive polynomial, checked by walking the orbit in the kernel). | the noise behind the kick's click, the snare, the clap and the toms repeats only every 1.5 s, longer than any hit. |
| `drum_noise_never_dies` | A nonzero 16-bit noise state steps to a nonzero 16-bit state, checked for every state. | the glue seeds the register with 1 and never resets it; a register at zero would stay there. |
| `drum_noise_in_range` | The noise sample is within 32767 for any state. | the noise feeds the filters and the gains at the same scale as a sine, so the bounds below cover it. |
| `drum_one_pole_stays_between` | A one-pole step is exact, `y + (x - y) * a / 16384` rounded down, and lies between the state `y` and the input `x`, for a coefficient from 0 to 16384 and signals within 65535; so the high-pass (input minus low-pass) is within `|x| + |y|`, and nothing wraps. | the low-pass cannot overshoot and the high-pass built from it is bounded, which is what lets six squares and a noise pass through two filters without a 32-bit wrap. |
| `drum_envelope_only_falls` | The envelope one sample on is no higher, and no lower than 15/16 of itself less one count, for any rate below 65536 and envelope up to one; rate 0 holds exactly; nothing wraps. | a drum's envelope only falls, by at most a sixteenth a sample, and rate 0 is a hold. |
| `drum_sweep_lands` | The swept increment never rises and never goes below its target: from above it falls by `rate / 2^20` of the distance a sample, at or below it stays on the target; for any increment below half a cycle a sample and any rate below 8192, nothing wraps. | the kick's and toms' pitch sweeps land on the note with no undershoot, from a start up to five times above it. |
| `drum_sweep_start_below_nyquist` | A sweep's start is below half a cycle a sample for any tuning and colour. | `drum_sweep_lands` needs the swept increment below Nyquist, and the start is its highest value; a note above the 1.4 kHz hold starts on its tuning. |
| `drum_metal_sum_fits` | Six squares of ±5461 sum within 32766 for any six phases. | the hi-hats and the cymbal enter their filters in the same range as a sine or the noise, so the same filter and gain bounds cover them. |
| `drum_square_in_range` | A square is ±5461. | the cowbell's two squares sum within 10922, inside the bound the band filter needs. |
| `drum_gain_never_amplifies` | A gain is at most its level, for any envelope up to one and level up to 32767. | a shape's loudest moment is its level table, which `drum_output_never_wraps` relies on. |
| `drum_metal_chain_bounded` | Six squares through the band filter and the gain: the sum is within 32766 (`drum_metal_sum_fits`), the first low-pass state within 32767, the high-pass within 65534, the second low-pass within 65535 and the gained output within 262140, for filter coefficients from 0 to 16384 (Q14) and a gain up to 32767 (Q13); no stage wraps and the states handed on satisfy the same bounds. | the hi-hats and the cymbal are the most arithmetic of any shape, and no colour setting can overflow their filters. |
| `drum_output_never_wraps` | Every shape's mix, as `voices/drum_glue.c` composes it, is exact and within 524280 (under 2^19), for filter states within their bounds (first stage within 32767, second within 65535), coefficients from 0 to 16384 and gains up to 32767: the kick and toms (`Drum.tunedOut`), the snare (`Drum.snareOut`), the clap (`Drum.clapOut`), the hi-hats and cowbell (`Drum.bandOut`, with `drum_metal_chain_bounded` and `drum_square_in_range`) and the cymbal (`Drum.cymbalOut`); the sample out is the mix clipped to 16 bits, unchanged when already within 32767. | no drum's arithmetic wraps at any knob, note or phase; an overloaded shape clips. |
| `drum_shapes_in_range` | Every shape's tables are in the ranges the theorems above need: rates below 65536 at every timbre (`drum_envelope_only_falls`), sweep rates below 8192 (`drum_sweep_lands`), levels up to 32767 (`drum_gain_never_amplifies`) and filter coefficients up to 16384 (`drum_one_pole_stays_between`) at every colour. | the table values are checked against the bounds, so a knob at either end still meets every hypothesis. |
| `drum_tails` | Each shape's tail from a full envelope at its nominal rate, stepped sample by sample in the kernel: the first sample at which the envelope is under a hundredth, with the sample before still above. | these are the decay times a player hears, computed from the arithmetic the chip runs. |
| `analog_this_blep_range` | The correction a step edge adds to its own sample is between 0 and 16383. | the band-limiting correction cannot push a sample out of range. |
| `analog_next_blep_range` | The correction a step edge leaves for the next sample is between -16383 and 0. | the band-limiting correction cannot push a sample out of range. |
| `analog_triangle_half_range` | Each half of a triangle step lies between -16384 and 16383. | the two halves add without leaving the 16-bit range. |
| `analog_triangle_never_wraps` | The triangle's sample is exactly the sum of its two halves; nothing wraps. | the triangle cannot click from an overflow at any pitch or phase. |
| `analog_sine_between_entries` | The sine at any phase lies between the two table entries it blends. | the sine, and everything FM-modulated through it, stays within the table's range, so the cut to 16 bits in `Analog.sineAt` never changes a value. |
| `analog_phase_exact` | An oscillator's phase after `n` samples is exactly `phase + n * inc`, wrapped at 2^32. | the frequency is exactly `inc / 2^32` of the sample rate with no rounding error building up, so a long note does not drift. |
| `digital_mix_between_inputs` | A crossfade of two 16-bit values stays between them (give or take one rounding step toward zero), for any balance up to 65535. | the macro shapes and the wavetable engines mix with this; it cannot exceed its louder input, so it cannot wrap. |
| `digital_clip_never_wraps` | Braids' `CLIP` gives a value between -32767 and 32767, and the 16-bit sample written is exactly that value. | the engines that end in a clip (saw swarm, harmonics, FOF vowel, question mark) are limited by the clip only, never a wrap. |
| `digital_fm_never_wraps` | Each of the three FM engines (FM, feedback FM, chaotic FM) writes exactly the blended sine at its modulated phase; the cut to 16 bits changes nothing. | an FM sample is always a sine table value (`analog_sine_between_entries`), so no modulation depth, feedback or sync can overflow it. |
| `digital_ring_product_never_wraps` | The ring modulator's product of two 16-bit signals is their exact product divided by 65536, between -16384 and 16384; the multiplication never wraps and the cut to 16 bits changes nothing. | the ring modulator multiplies three full-scale sines in a row, and the soft clipper after them gets a value of at most half scale. |
| `digital_ring_mod_never_wraps` | The ring modulator writes exactly its soft-clipped triple product; the cut to 16 bits changes nothing. | the sample is always a value of the overdrive shaper, so it cannot overflow. |
| `digital_toy_never_wraps` | The toy's smoothing filter writes exactly the weighted average of its four held values, centred on zero (between -28208 and 27987); the unsigned subtraction wraps for a low average and the read as a 16-bit value undoes that wrap exactly. | the wrap Braids relies on is proved harmless; the sample is never off by 65536. |
| `blend_eight_between` | Blending two 16-bit entries by an 8-bit fraction (`Interpolate88`, `Analog.blend88`) lands between them. | a wave shaper's output stays within its table's range without relying on the 16-bit cut. |
| `blend_sixteen_between` | Blending two 16-bit values by a 16-bit fraction (`Interpolate824`) lands between them, for any two values. | every table read and wave crossfade uses this blend; the overflow in the original is proved harmless. |
| `filters_swarm_sum_range` | The sum of the swarm's seven saws lies between -28672 and 28665 at any phases. | the sum is offset by 32768 and read from the overdrive shaper with no mask; this keeps the read inside its 257 entries (`tables_shape_reads_inside_257`). |
| `filters_harmonic_glide_approaches` | A harmonic's amplitude moves toward its target and never passes it (shown for an amplitude below its target; the other direction is symmetric), for values within a quarter of the 32-bit range. | a fading harmonic cannot overshoot. |
| `filters_swarm_filter_never_wraps` | The saw swarm's high-pass writes exactly its clipped output, between -32767 and 32767. | the swarm's sample is limited by the clip only; a resonance peak cannot wrap. |
| `filters_windowed_carrier_never_wraps` | The windowed carrier of the digital filter engines is the exact product the formula means, for a 16-bit carrier and a window of 0 to 65535. | the digital filter engines never write a wrapped carrier; the overflow in the original is proved harmless. |
| `filters_vosim_never_wraps` | Vosim writes exactly its windowed formant sum, centred on zero; the two formants under the bell window never pass 49150 before the centring, so nothing wraps at any pitch or formant setting. | vosim cannot overflow for any formant frequencies. |
| `filters_harmonics_never_wraps` | The harmonics engine writes exactly its clipped sum, and the in-between sample exactly the average of that with the last sample. | the sum is limited by the clip only and the half-rate smoothing cannot wrap. |
| `filter_open_is_identity` | With the cutoff fully open (100) and no resonance the filter is inactive: a step returns the sample and the states unchanged, for any state, mode and sample. | these are the default settings on every voice, so every existing sound is bit for bit what it was. |
| `filter_states_stay_bounded` | The states and nodes stay within ±65536 and nothing in a sample wraps: a state after a sample is within ±65536 for any inputs (the hold); and with both states within ±65536, the sample within ±65536 and the coefficients in range (`g`, `a1`, `a2` at most 32767, `k` at most 16384) the band node before its hold is exactly `a1 ic1 / 2^15 + a2 ((x - ic2) / 2) / 2^14`, the held band node `v1` is within ±65536, the low-pass node `v2` is exactly `ic2 + g v1 / 2^15` and within ±131072, the high-pass output before its clip is exactly `x - k v1 / 2^13 - v2`, the raw output of every mode is within ±327680 (5 · 2^16), and both state updates `2 v - ic` are exact. | the filter's arithmetic saturates at twice full scale and never wraps, whatever the engine feeds it; the clip to ±32767 at the output is the only other thing that touches a sample. |
| `filter_coefficients_in_range` | The coefficients are in the ranges `filter_states_stay_bounded` needs and the cutoff sweep is monotone: every entry of the cutoff table is at most 32767 and the table rises from each setting to the next below 100; the damping is between 884 (0.108 in Q13) and 16384 (2.0) for any resonance setting; `a1` is at most 32767 for any `g` and `k`, and `a2` is at most `g` for any `g` at most 32767. | turning the cutoff up always opens the filter, and no cutoff or resonance setting hands the sample path a coefficient that could overflow a product. |
| `filter_settled_dc_holds` | A settled constant is a fixed point of the active filter: with the band state at rest (`ic1 = 0`) and the low-pass state at the sample (`ic2 = x`), a step gives low-pass output `x`, band and high outputs 0, and the same states again, for any cutoff and resonance and any sample within ±32767. | a steady level passes through the low-pass unchanged at any cutoff, with no drift from rounding, and the band and high outputs reject it. |
| `filter_lowpass_steps_toward_input` | A low-pass step with the band node at rest (`ic1 = 0`) lands between the low-pass state and the sample, within one count of rounding below: `min x ic2 - 1 ≤ v2 ≤ max x ic2`, for any `g` and `a2` at most 32767, any `a1`, and states and sample within ±65536. | the low-pass integrator only moves toward the input; a resonant peak comes from the band state, which is held. |
| `noise_particle_amplitude_fades` | Between hits, a particle burst only fades: its amplitude after a sample is at most what it was. | particle noise dies away between hits; the burst cannot grow by itself. |
| `noise_overdrive_index_in_table` | A signed 16-bit value plus 32768 is one of the overdrive curve's 65536 indices. | the filtered and twin-peaks noises read the curve by this index unchecked; it is the condition `tables_shape_reads_inside_257` needs. |
| `noise_corrected_never_wraps` | The filtered noise's gain correction is exact and within 16 bits: the mix clipped to ±32767, scaled by `gain` parts in 32768, for a gain from 0 to 32767. | the result indexes the overdrive curve; an oversized value would read outside it. |
| `noise_boost_never_wraps` | The twin peaks' boost is exact: the resonators' sum plus `makeup` parts in 8192 of itself, clipped to ±32767, for a sum within 65536 and a makeup gain from 0 to 8191. | the boost is the last arithmetic before the overdrive curve; it clips, not wraps. |
| `noise_resonate_never_wraps` | One resonator step is exact: the input scaled by `s` parts in 65536 with its sign kept, plus the last output times `c` parts in 32768, minus the one before times `q2` parts in 32768, clipped to ±32767. | a wrap in the resonators' feedback would be a burst of noise that never decays. |
| `noise_burst_never_wraps` | A particle burst's sample is exact: the noise word's low 16 bits as a signed number, times the amplitude, divided by 65536, which is within 16 bits. | this is the input to the three resonators, in the range they are proved for. |
| `noise_particle_never_wraps` | The particle noise's sample is exact: the three resonators' outputs added and clipped to ±32767, with nothing wrapping in the sum. | each resonator is clipped on its own, so the sum of three needs its own clip. |
| `noise_cloud_out_never_wraps` | The cloud's limiter is exact: the sample is the grains' sum clipped to -32768..32767. | the cut to 16 bits after the limit changes nothing. |
| `noise_grain_never_wraps` | A grain's share of the sample is exact: the sine at its new phase times its envelope entry, divided by 131072, which is within ±16384, so the cloud's limiter sees the exact sum of its four grains. | the cloud adds four of these every sample; a wrapped share would be a click. |
| `noise_grain_envelope_index_in_table` | A grain reads inside its 513-entry envelope when its envelope phase is at most 2^24 + 2^22 and its rate at most 2^18 per sample. | the envelope is a C array read without a bounds check. |
| `percussion_excite_decays` | Between hits an exciter's pulse stays at or below where it was and never below zero, for a pulse at most 2^19 (the loudest strike is 15 times 32768) and a decay at most 4096 (one, in 12 bits). | the exciter cannot grow on its own or go negative. |
| `percussion_decay_never_grows` | Between blocks a partial's new amplitude is at least zero and at most what it was, for an amplitude up to 32767, decays up to 65535 (the short one at most the long one) and any setting from 0 to 32767. | the decay cannot make a partial louder or flip its sign, so amplitudes stay in the range the partial arithmetic is proved for. |
| `percussion_bell_partial_never_wraps` | A bell partial's share of the sample is exact: the sine at its new phase times its amplitude, divided by 131072, for an amplitude from 0 to 32767 (Braids' bell partials start at most at 21872 and only decay). | eleven of these are added every sample of a bell; a wrapped share would be a click. |
| `percussion_drum_partial_never_wraps` | A drum partial's share of the sample is exact: the amplitude moves from `amplitude` toward `target` by `fade` parts in 32768, and the sine at its new phase times that, divided by 65536, is the share. | six of these are added every sample of a drum; a wrapped share would be a click. |
| `percussion_snare_never_wraps` | The snare's sample is exact: the two filtered exciters, each with a sixteenth of its raw pulse, at their gains, plus the filtered noise, clipped to ±32767. | the sum of three loud signals clips, not wraps. |
| `percussion_cymbal_never_wraps` | The cymbal's sample is exact: the metallic and white noises each clipped to ±32767, then the blend from the first toward the second by `xfade` parts in 32768, which lands between them and fits 16 bits. | the cymbal's blend cannot wrap at any blend setting. |
| `percussion_drum_noise_stays_bounded` | The drum's noise filter's three states stay within 16384 from one sample to the next, for noise of any size and a cutoff from 0 to 32768. | the filtered noise ring-modulates the drum's partials every sample; a growing state would wrap that product. |
| `percussion_drum_mix_never_wraps` | The drum's sample is exact: the first partial, the second and fourth ring-modulated by the filtered noise at the noise gain, and all partials at the harmonics gain, clipped to ±32767. | the ring modulation multiplies two signals and a gain; a louder second or fourth partial would pass 32 bits. |
| `physical_mix_never_wraps` | Braids' `Mix` of two 16-bit delay-line samples by a 16-bit fraction is exact: the weighted sum reaches at most 32768 * 65535 and stays inside 32 bits. | every delay-line read of the bowed string, blown pipe and flute uses this blend. |
| `physical_comb_never_wraps` | The comb filter's output and feedback samples are exact: the delayed sample is the blend of its two neighbours and each output is that arithmetic clipped to ±32767, for 16-bit input and line samples, a fraction from 0 to 65535 and a 16-bit resonance. | a wrapped sample in the comb's feedback would ring round the loop. |
| `physical_comb_resonance_index_in_table` | The comb filter's resonance curve read is inside the curve's 257 entries for every setting. | the curve is a C array read without a bounds check. |
| `physical_pluck_fill_never_wraps` | Filling a new string never wraps: each entry is a quarter of the old sample plus three quarters of the noise, which fits 16 bits for 16-bit inputs. | a pluck starts from this fill. |
| `physical_pluck_average_no_gain` | One step of the plucked string's loop stays within the larger of the two neighbours it averages, for 16-bit neighbours and a loss from 0 to 32768. | the Karplus-Strong loop feeds back into itself; a step with gain would make the string grow instead of decay. |
| `physical_pluck_read_never_wraps` | Reading the plucked string between two 16-bit entries gives exactly their blend at any phase. | this read is the plucked string's sample; the overflow in the original is harmless. |
| `physical_half_rate_never_wraps` | A half-rate engine's two samples are exact: the sample is the voices' sum clipped to ±32767, and the in-between sample is the mean of that and the previous 16-bit sample, rounded down. | the plucked and bowed strings hand every other sample through here. |
| `physical_bowed_never_wraps` | The bowed string's sample is exact: the body filter on the bridge sample (the blend of two 8-bit line samples times 256) and its two previous outputs, clipped to ±32767, for previous outputs within 2^18 (which `physical_bowed_body_stays_bounded` keeps true from one sample to the next). | the body filter runs on every sample of a bowed note. |
| `physical_bowed_lowpass_stays_bounded` | The bowed string's bridge low-pass state stays within 16 bits from one sample to the next, for 8-bit line samples and any fraction up to 65535. | this state feeds the string back to itself; a growing state would wrap the bow's arithmetic. |
| `physical_friction_index_in_table` | The bowed string's friction curve read is inside the curve's 257 entries, for a bow pressure up to 1024 and a bow-to-string speed difference up to 2^20 (Braids uses at most 172 and 2^17). | the curve is a C array read without a bounds check; the cap at 131071 before taking the top 8 bits keeps it inside. |
| `physical_blown_filter_stays_between` | The blown pipe's output filter lands between the bore's new sample and its own last output, so it fits 16 bits, for a coefficient from 0 to 4096 and a 16-bit last output. | this filter is the blown pipe's sample; it cannot add a wrapped value. |
| `physical_fluted_never_wraps` | The flute's sample is exact: the bore's blended 8-bit sample times 256, clipped to ±32767, for 8-bit line samples and any fraction up to 65535. | nothing on the flute's output path can wrap. |
| `physical_jet_index_in_table` | The flute's jet curve read is inside the curve's 257 entries for every jet value. | the curve is a C array read without a bounds check; the clamp to 0..65535 before taking the top 8 bits keeps it inside. |
| `physical_bowed_body_stays_bounded` | The body filter state the bowed string carries to the next sample is within 2^18 for any inputs. | with `physical_bowed_never_wraps` this closes the loop, so the body filter never wraps over a whole note. |
| `physical_comb_read_in_line` | The comb filter's two reads (`integral` and `integral + 1` samples back) are inside its 8192-entry line. | the glue indexes the line unchecked. |
| `physical_comb_write_in_line` | The comb filter's write position after a sample is inside its 8192-entry line. | the glue writes unmasked. |
| `physical_pluck_read_in_line` | The plucked string's read entry and its neighbour one further on are both within a string of `size` entries, the neighbour at most on the guard copy `dl[size]`. | the read blends two neighbours, which is why the line is one entry longer than the string. |
| `physical_pluck_next_in_line` | Where the plucked string's low-pass loop stops this sample, and each next entry it visits, are within a string of `size` entries. | the loop reads and writes `dl[write_ptr]` and `dl[next]` unchecked; with `size` zero the mask would be all ones. |
| `physical_pluck_fill_in_line` | Filling a new string writes inside a string of `size` entries when the fill counter started at or below `size`. | the glue indexes the line with the fill counter unchecked. |
| `physical_bowed_lines_in_line` | The bowed string's reads and writes are inside its lines: the bridge line is 1024 long, the neck line 4096. | both lines are `int8_t` arrays indexed unchecked, and the delays come from the pitch without a clamp. |
| `physical_blown_bore_in_line` | The blown pipe's read and write are inside its 2048-entry bore line. | the bore is indexed unchecked and the delay comes from the pitch without a clamp. |
| `physical_fluted_lines_in_line` | The flute's reads and writes are inside its lines: the bore line is 4096 long, the jet line 1024. | both lines are indexed unchecked and the delays come from the pitch without a clamp. |
| `vowels_fof_contribution_never_wraps` | Each formant filter of the FOF vowel contributes exactly its band-pass state times the amplitude (a 16-bit value) divided by 131072, between -8192 and 8191, with nothing wrapping. | the five contributions are summed in 32 bits in C and never pass 40960, so the clip after them is the only limit. |
| `vowels_fof_out_never_wraps` | The FOF vowel writes exactly its clipped filter sum, and the in-between sample exactly the average of that with the last sample. | the sum is limited by the clip only and the half-rate smoothing cannot wrap. |
| `vowels_question_drive_never_wraps` | The question mark's distortion term is exactly the square-law formula, between 0 and 65535, for a clipped sample and a drive of 0 to 32767; neither product wraps. | full drive cannot overflow and flip the sample's sign; the clip after it is the only limit. |
| `wavetables_wavetable_never_wraps` | A wavetable sample is exactly the sum of its two half-rate readings, each halved; nothing wraps. | the wavetable engine cannot overflow for any waves, phase or morph position. |
| `wavetables_crossfade_between_waves` | A crossfade of two waves at the same phase lies between the two waves' values there, for any two waves. | morphing cannot exceed the louder wave, even where the waves are far apart and Braids' C++ product wraps (`blend_sixteen_between`). |
| `wavetables_read_between_bytes` | A wave read lies between the two bytes it blends (each scaled to 16 bits), for any wave and phase. | a wave stays within its bytes' range; the overflow in the original is proved harmless. |
| `wavetables_wave_map_never_wraps` | A wave map sample is exactly the sum of its two half-rate readings, each already halved; nothing wraps. | the wave map engine cannot overflow for any square, phase or position in the square. |
| `wavetables_wave_line_never_wraps` | A wave line sample is exactly the average of its two half steps; nothing wraps. | the wave line engine cannot overflow for any waves, masks, crossfades or balance. |
| `wavetables_paraphonic_never_wraps` | A paraphonic sample is exactly the sum of its four voices divided by four; nothing wraps. | four full-scale voices added in 32 bits stay far inside the range at any chord, phase or morph position. |

</details>

<details><summary><b>Setting a voice up</b>: 42 theorems</summary>

Per-note and per-block setup: parameters land in range, smoothing does not overshoot, table reads are in bounds.

| Theorem | Says | Protects against |
|---|---|---|
| `voice_setup_pitch_in_range` | The pitch Braids gets for a MIDI note (`play` in `fw/firmware/src/dinghy.c` sends the note times 128) is exactly that below note 128, where the phase step clamps, and a timbre value of 0 to 32767 (the sounds' range, and what the envelope's boost is held to) reaches Braids unchanged. | Braids holds pitch and timbre in 16 bits; the firmware's range never reaches the cut, so no note plays the wrong pitch and no parameter reads past the tables. |
| `voice_setup_shape_in_table` | The shape the voice plays is one of Braids' 48, whatever index the firmware sends. | the macro oscillator picks its render function from a 48-entry table without a check. |
| `smooth_parameter_between` | A smoothed parameter lies between `start` and `target`, for parameters 0 to 32767 (Braids' range) and any crossfade position 0 to 32767, and nothing in the arithmetic wraps. | a moving knob glides the timbre between the two settings without overshoot or a wrapped jump. |
| `smooth_parameter_reaches_target` | When the block ends, the smoothed parameter is within `size` of its target: the last crossfade position is `32767 - 32767 % size` rather than 32768, so it stops just short. | the step from the end of one block to the start of the next is at most `size`, so block boundaries are inaudible. |
| `smooth_step_glide_bound` | While a block smooths the phase step from `previous` to `target`, the step never rises above the larger of the two nor falls more than `size` below the smaller. | a pitch glide cannot pass the note by more than 16 units of 2^32 per sample, under a millionth of a semitone. |
| `smooth_step_lands_near_target` | When the block ends, the smoothed phase step is at or below its target and within `size` of it: rising, it lands `(target - previous) % size` short; falling or level, between 1 and `size` below. | after every block the pitch is within 16 units of 2^32 per sample of the note asked for and never sharp. |
| `analog_setup_pulse_width_in_range` | For a non-negative parameter (Braids' parameters are 0 to 32767), the square's pulse turns on between 768/32768 and 32768/32768 of the cycle and the variable saw's second slope starts between 1024/32768 and 32767/32768 of it. | the sample code places its edge correction by dividing the distance to the edge by the phase step; an edge at phase 0 would be corrected twice and one past the cycle never reached. |
| `analog_setup_buzz_zone_in_table` | The buzz reads two of the 15 comb tables, both inside the set, for any pitch and parameter. | the comb tables are C data read without a check; the clamp to the last zone keeps a high or unclamped pitch from reading past them. |
| `digital_setup_fm_quantizer_in_table` | A non-negative parameter reads two neighbouring entries of the 129-entry FM ratio quantizer, both inside it. | the quantizer is C data read without a check, once per block for the three FM engines. |
| `digital_setup_increments_half_cycle` | Every phase step the setup hands to the FM, ring modulator, toy and digital modulation sample code is below half a cycle per sample. | a step at or above half a cycle would alias, and the modulators' detunes can reach pitches far outside the carrier's range. |
| `digital_setup_delay_in_table` | Every pitch reads two neighbouring entries of the 97-entry delay table, both inside it. | the table is C data read without a check; the clamp to note 128 and the fold into one octave keep the read inside for any 16-bit pitch, including the lowest a filtered comb pitch reaches. |
| `macro_setup_parameters_in_range` | Every parameter the macro oscillator hands an analog oscillator (morph's pulse width, the sine and triangle fold amounts) is between 0 and 32767, given a non-negative first parameter (Braids' parameters are 0 to 32767). | the pulse widths and fold tables are built for 0 to 32767; an out-of-range parameter would put a pulse edge outside the cycle or read a shaper past its end. |
| `macro_setup_cutoff_in_table` | Morph's low-pass cutoff, as a pitch, is 0 to 32767 for any pitch and parameter, and its two reads of the 257-entry cutoff table are inside it. | the filter table is C data read without a check, once per block for the morph engine. |
| `macro_setup_triple_intervals_in_table` | A triple oscillator's non-negative parameter reads two entries of the 65-entry interval table, both inside it. | the interval table is C data read without a check, twice per block for the four triple engines. |
| `filters_setup_cutoff_in_table` | The swarm's high-pass reads two neighbouring entries of the 257-entry cutoff table, both inside it, for every pitch and parameter. | the cutoff pitch is the oscillator's pitch plus the parameter, which can run far past the table; the clamp in `swarmHpCutoff` keeps the read inside. |
| `filters_setup_table_blend_le_top` | A table of 16-bit entries that rise from one to the next across its 257 entries and never pass `top` (at most 32767) blends to a value at most `top` at any phase (`Digital.lutAt`). | a cutoff or damping coefficient read this way is between 0 and the table's top entry, the range the filters' sample theorems assume; the cut to 16 bits inside the blend changes nothing. |
| `filters_setup_cutoff_in_range` | The swarm's high-pass coefficient is between 0 and 25078. | the coefficient multiplies the band-pass state on every sample; a positive 15-bit coefficient keeps that product in step with the original. |
| `noise_setup_cutoff_in_table` | The filtered noise's cutoff, damping and scale read two neighbouring entries of their 257-entry tables, both inside, for any pitch and parameter; the index is the top byte of the shifted value. | the three tables are C data read without a check, and the pitch can be any 16-bit value. |
| `noise_setup_gain_correction_in_range` | The filtered noise's gain correction is between 0 and 32767, the hypothesis of `noise_corrected_never_wraps`. | the correction multiplies every sample; above 32767 the product could leave 32 bits. |
| `noise_setup_grain_rate_in_table` | A grain's rate reads inside the 257-entry rate table for any parameter from 0 to 32767. | the table is C data read without a check; the index is the parameter's top eight bits. |
| `noise_setup_grain_rate_bounded` | A grain's rate is at most 2^18 per sample. | `noise_grain_envelope_index_in_table` needs the rate below 2^18 to keep a block's envelope reads inside the envelope table. |
| `noise_setup_grain_reset` | After the setup, a grain's rate is at most 2^18 and its envelope will not pass 2^24 + 2^22 within the block's 16 samples, given a block that started that way (the first block starts at 0). | these are the two hypotheses of `noise_grain_envelope_index_in_table`, so the envelope reads stay inside their table from the first block on. |
| `noise_setup_clock_period_positive` | The clocked noise's quantization step is between 2048 and 32768 for any held parameter from 0 to 32767. | the loop reduces every random value modulo this step (`Noise.clocked`); a step of 0 would be a division by zero in C, and the setup never asks for fewer than 2 steps. |
| `percussion_setup_partial_decay_in_table` | Every bell and drum partial's two decays are 16-bit, the short one at most the long one; these are the `decayFits` hypotheses of `percussion_decay_never_grows`. | a decay above 65535, or a short one above the long one, would make `Percussion.decay` a gain and the partials would grow. |
| `percussion_setup_amplitudes_in_range` | Every bell and drum partial starts within 16 bits, and the drum's second partial starts at or below 4096 and its fourth at or below 8192. | the drum ring-modulates its second and fourth partials by the noise and then by a gain; a louder start would pass 32 bits in the mix. |
| `percussion_setup_drum_cutoff_in_table` | The drum's noise filter reads its two cutoff entries inside the 257-entry cutoff table; the clamped cutoff, shifted by 16, has a top byte of at most 127. | the drum's cutoff is the pitch plus a parameter, and the clamp keeps that sum's table read inside the data. |
| `percussion_setup_gains_in_range` | The gains handed to the drum and snare mixes are in the ranges their sample theorems assume: the drum's noise gain 0 to 12888 and harmonics gain 0 to 16983 (`percussion_drum_mix_never_wraps`), the snare's two gains 0 to 22000 and 0 to 38383 (`percussion_snare_never_wraps`), for parameters from 0 to 32767. | the mixes multiply a signal by these gains and add; a gain outside its range could push the sum past 32 bits. |
| `physical_setup_pluck_size_valid` | A new plucked string meets the line theorems' hypotheses: its oversampling is at most 9 (`oversampled` in `physical_pluck_read_in_line` and `physical_pluck_next_in_line`; `pluckSize` and `pluckMask` are `1024 >>> shift` and `size - 1` by definition), and its fill count is at most its size (`fits` in `physical_pluck_fill_in_line`; the glue only fills while the count is nonzero, that theorem's `started`). | these numbers decide where the plucked string reads and writes its 1025-entry line. |
| `physical_setup_comb_delay_in_line` | The comb filter's whole-sample delay is at most 8192, its line's length. | the positions are masked, so a longer delay would not read outside the line but would read the wrong sample; the clamp is the only thing preventing it. |
| `physical_setup_envelope_pointer_in_table` | The bowing and blowing envelope pointers a block leaves behind read inside their envelopes through the next block: the bowed string's pointer is held to 1440, so its two reads (at half the pointer and half the pointer plus one) stay below the 752-entry bowing envelope for any advance up to 16 samples, and the flute's is held to 360, so its read stays below the 392-entry blowing envelope. | both envelopes are read unchecked at the pointer; the clamp after each block keeps a long note from running off the end. |
| `physical_setup_flute_body_in_table` | The blown pipe and the flute read their body filter inside its 128-entry table, for any pitch and parameter. | Braids indexes this table by the pitch in semitones, which can reach note 140; the clamp to 127 keeps the read inside. |
| `vowels_setup_vowel_index_in_table` | A parameter of 0 to 32767 selects a vowel from 0 to 7, and the vowel after it is at most 8, so both reads are inside the nine entries of `vowels_data`. | the vowel blends two neighbouring rows without a bounds check; the top three bits of the parameter never name the last row, so the row after exists. |
| `vowels_setup_consonant_index_in_table` | A strike's random sample selects a consonant from 0 to 7, inside the eight entries of `consonant_data`. | the consonant is read without a bounds check from the random generator; the mask to three bits keeps it inside. |
| `vowels_setup_fof_reads_in_table` | A parameter of 0 to 32767 selects a row of the FOF vowel's 5-by-5 grid from 0 to 3, and the row after it is at most 4, so the four corners the blend reads are inside the grid. | `fofBlend` reads the corner past the selected row and column; the top two bits of a parameter never select the last row, so that corner exists. |
| `vowels_setup_formant_amplitude_in_range` | The amplitude the vowel hands each formant is at most 15. | the formant tables are indexed by the phase's top nibble or-ed with the amplitude, and `tables_formant_reads_inside_256` needs the amplitude to be a nibble. |
| `vowels_setup_fof_amplitude_16bit` | The amplitude the FOF vowel hands its formant filters is a signed 16-bit value, for any parameters. | `vowels_fof_contribution_never_wraps` takes a 16-bit amplitude; the blend's final cut to 16 bits (the original's `int16_t` return) makes that so for every block. |
| `wavetables_setup_table_in_table` | The wavetable engine reads its wavetable's definition inside the table of 20 definitions, and the pointer's step and the one after it inside the 17 steps of a definition, for a held parameter from 0 to 32767. | both are C arrays read without a check; the 17th entry of each definition is there for the read past the last step. |
| `wavetables_setup_map_in_table` | The wave map reads its four corners inside the 256-entry map for parameters from 0 to 32767 and corners 0 or 1 away from the square's origin. | the map is a C array read without a check; the scaling to 15 squares keeps the corner after the last column or row inside the 16 by 16 grid. |
| `wavetables_setup_line_in_table` | The wave line reads the held parameter's wave and the scan's wave inside its 64-entry line, and the wave after the scan's at most one past it, for parameters from 0 to 32767 and a smoothed parameter from 0 to 65534; both parameters stay in those ranges for the next block. | the line is a C array read without a check; the ranges are the invariant that bounds every block's reads, starting from 0. |
| `wavetables_setup_paraphonic_in_table` | The paraphonic engine reads its chord and the one after it inside the 17 chords, and the first parameter's wave and the one after it inside the 33-entry short line, for parameters from 0 to 32767. | both are C arrays read without a check; the 17th chord and 33rd wave are there for the read past the last entry. |
| `wavetables_setup_wave_in_bank` | A wave numbered up to 255 reads its two bytes at any halved phase inside the 33024-byte bank of 129-byte waves (`wt_waves`, `WT_WAVES_SIZE` in `resources.h`). | the bank is read without a check through `Wavetables.waveByte`, which adds the wave's offset to the byte's index; 256 waves of 129 bytes is exactly the bank. |
| `wavetables_setup_increments_half_cycle` | Every detuned voice of the paraphonic engine steps below half a cycle per sample (`pitch_increment_bounded`). | the detune is added to the pitch before the table's clamp, so none of the four voices runs past Nyquist. |

</details>

<details><summary><b>The mix and the effects</b>: 28 theorems</summary>

The mix does not wrap, the reverb and delay stay inside their lines, their gains are below one so tails die away, and
their filters do not overshoot.

| Theorem | Says | Protects against |
|---|---|---|
| `mix_envelope_toward_gate` | A voice's level one sample later lies between its old level and its gate, so it stays between 0 and 130048 (the top of `play`'s gate), for `ATTACK` at most 1024 and `RELEASE` at most 250. | the click-removing glide cannot overshoot, and the level cannot wrap negative. |
| `mix_voice_sample_never_wraps` | A voice's sample for the mix is computed without wrap and is within 65024, for a gain of at most 2048 (the most `tools/gen_presets.py` writes) and a level of at most 130048; its share for the reverb bus (send at most 256) is within 130048. | six voices at full gain fit the stereo mix and the send bus without wrapping. |
| `mix_bus_never_wraps` | The stereo mix of up to six voice samples (each within 65024, from `mix_voice_sample_never_wraps`) plus the wet return is added without wrap: the dry sum is within 390144, the whole within 1077734144. | six voices and the reverb can only clip at the clip in `platform.c`, never wrap in the mix. |
| `mix_limit_fits_master` | After the limiter the mix is within 524287, so `platform.c`'s product with the master gain (at most 4088) fits in 32 bits for any input; a mix already within that range passes through unchanged. | the dry mix never reaches the limit (`mix_bus_never_wraps`), so the limiter only acts on an extreme wet return, where it keeps the master stage from wrapping. |
| `mix_in_never_wraps` | Adding one effect's return to a mix already within the limit is exact (no wrap), and the result is the sum clipped to 524287, for a wet sample within 2^29 + 2^21 and a gain up to 65500 (twice the largest RETURN). | `app_audio` does this for the delay and then the reverb; a loud return can only clip. |
| `mix_machine_sample_bounded` | The sample the master stage sees: the dry sum of up to six voice samples (each within 65024, from `mix_voice_sample_never_wraps`), then the delay's echo (a stored 16-bit sample), then the reverb's wet sample (within 2^29 + 2^21, from `reverb_wet_never_overflows`), each with a return gain up to 65500. | this joins the voice, delay, reverb and mix results into one statement about the whole `app_audio` path: the master stage sees the mix clipped at the limit, never a wrapped value. |
| `mix_pan_equal_power` | For every pan setting the two gains are between 0 and 1.0 and their squares add up to 1.0 within a tenth of a percent. | a panned sound is never louder on a side than it was and keeps its power as it moves. |
| `mix_pan_never_amplifies` | A voice's sample on one side is at most the sample in size, for any pan gain between 0 and 32767, and is computed without wrap for samples within 65024 (from `mix_voice_sample_never_wraps`). | panning only takes level away, so the bounds of `mix_machine_sample_bounded` still hold. |
| `reverb_position_in_ring` | A sample position is inside the shared delay memory for any write position, line start and offset. | no knob setting can make a read or write land outside the memory. |
| `reverb_lines_fit_and_do_not_overlap` | At every scale up to 400 (353 shipped), each delay line ends inside the memory and each line starts one sample after the previous one ends. | the ten lines never overlap and none runs off the end. |
| `reverb_gains_below_one` | For every decay-time setting the loop gain is positive and at most 0.98, and for every brightness setting the low-pass amount is positive and at most 0.97. | no knob position gives a gain of 1.0 or more. |
| `reverb_compress_saturates` | The value stored in the delay memory is the signal divided by 8, rounded towards zero, saturated at the 16-bit ends: from 262144 up it stores 32767, from -262152 down it stores -32768, and in between it is within 7 of the signal (times 8). | a loud signal in the loops clips instead of wrapping to the opposite sign. |
| `reverb_gain_never_amplifies` | A signal times a gain between 0 and 1.0 lies between zero and the signal. | the loop gain and the low-pass amount are such gains, so a pass round a loop cannot make a sample louder, rounding included. |
| `reverb_lowpass_stays_between` | One step of the low-pass lands between its old state and the new signal, for any amount from 0 to 1.0, when both are within a quarter of the 32-bit range (the loops hold at most 8.0). | the filter in each loop cannot overshoot or add level. |
| `reverb_interpolation_stays_between` | A read between two stored neighbours lies between them, for any fraction below 1.0, when both are within a quarter of the 32-bit range. | the interpolation of a modulated delay cannot add a spike. |
| `reverb_lfo_in_range` | The LFO's wobble is between 0 and 32767 (0 and 1.0 in Q15) at every phase. | a modulated delay stays between its base time and its base plus its depth. |
| `reverb_modulated_read_stays_in_line` | The two modulated reads, the first diffuser (10 samples plus up to 60, line 0 of 113) and the long delay of the second loop (4680 plus up to 100, line 9 of 4782), read a sample and its older neighbour that are both inside their own line, for any LFO value, at every scale from 192 to 400 (353 shipped; below 192 the long delay's two-sample margin is lost to rounding). | a modulated read past the end of its line would read the next line's samples, which the differential test could miss. |
| `reverb_round_trip_decays` | One trip round the undriven tank (through both loops) scales a sample by the decay gain squared plus at most one unit of rounding: in Q15, a sample read from a long delay comes back to it as at most `tail · decay² / 2^30 + 1`. | with nothing fed in, every trip makes the tail quieter, at any decay setting. |
| `reverb_wet_never_overflows` | The wet sample a loop hands to the mixer is exactly twice the sum the loop stores (no wrap in the doubling or in any addition before it), at most 16448.0 in size (2^29 + 2^21), the low-pass's new state stays within 8192.0 (2^28), and the mixer's return gain of up to 2.0 (`Mix.wetSample`) scales it with no wrap. | the reverb's output cannot wrap to the opposite sign on its way into the mix. |
| `reverb_tail_stays_in_memory` | A sample read from the memory after any number of trips round an undriven tank is a memory sample, at most 8.0 in size. | the 16-bit memory format caps a tail at any number of trips and any gains. |
| `reverb_tail_dies_away` | After `n` trips round an undriven tank, a sample is at most its starting size times the decay gain to the power `2n` (Q15, so divided by `2^30` per trip), plus 16385 (half a unit in Q15). | a tail at any level decays towards silence; rounding cannot accumulate into noise or a tone that never ends. |
| `delay_gains_in_range` | For every feedback setting the gain is between 0 and 0.95 (31129 in Q15), and for every tone setting the low-pass amount is between 0.2 and 1.0. | each echo is quieter than the one before at every knob position. |
| `delay_echo_shrinks` | With nothing new on the send, what goes back into the line is at most 95% of the echo plus one count of rounding, for every feedback setting (the most negative number excluded). | each pass round the line loses at least a twentieth, so the echoes decay at any setting. |
| `delay_samples_in_line` | The delay in samples is between 1 and 20479, so the echo is read from inside the line, never from the sample being written (offset 0) and never from a wrapped position. | no TIME or TEMPO setting makes a line read where it writes, a feedback path with no delay. |
| `delay_position_in_line` | A write position and an offset inside a line give a read position inside it, and the next write position is inside it. | with `delay_samples_in_line`, every read and write of the two lines is in bounds; the lines are not a power of two, so the wrap is by subtraction, not a mask. |
| `delay_notes_exact` | At 44.1 kHz the note values the lines are long enough for are exact, `60 * 44100 * numerator / (bpm * denominator)` samples: 1/32 and 1/16 at every tempo from 40 to 240, everything up to a dotted eighth from 97 bpm, every note value from 130 bpm. | the echo lands on the beat the setting names at the tempos it can be played at. |
| `delay_store_saturates` | A signal for the line saturates at the 16-bit ends instead of wrapping: from 32767 up it stores 32767, from -32768 down it stores -32768, and in between it stores the signal. | a send louder than full scale clips instead of flipping sign into a click that echoes. |
| `delay_echoes_die_away` | An echo going round the undriven line `n` times is at most its starting size times `(19/20)^n` plus 20 (the roundings of the hops, one each, kept below 20 by the same ratio), for every feedback setting; after enough hops it is within 20 counts of silence (a count is 1/32768). | the tail ends at every setting; rounding cannot accumulate into a hum. |

</details>

<details><summary><b>Patches</b>: 6 theorems</summary>

A saved patch loads back as saved, anything else in a slot is rejected, and every factory patch is in range.

| Theorem | Says | Protects against |
|---|---|---|
| `patch_decode_encode_round_trip` | Decoding an encoded patch gives the same patch, for every patch that fits (`Patch.Fits`). | a user slot restores exactly what was saved. |
| `patch_decode_only_fits` | Any patch `decode` accepts fits: every setting is in range. | a corrupt or foreign slot cannot load an out-of-range index that would read past a table; it loads as EMPTY instead. |
| `patch_decode_rejects_wrong_marker` | A slot whose first byte is not the marker 0xA7 never loads. | an unwritten or foreign slot is treated as empty rather than read as settings. |
| `patch_decode_rejects_wrong_size` | A slot that is not exactly 106 bytes long never loads. | a slot from a firmware with a different patch layout is rejected whole. |
| `patch_encode_size` | Every encoded patch is 106 bytes long. | the C side reads exactly `FM1_PATCH_BYTES` back from a flash slot. |
| `presets_all_fit` | Every factory patch in `Presets.all` satisfies `Patch.Fits`, checked value by value. | the firmware trusts its own patch table without the checks a loaded slot gets, and a generated patch that strays out of range fails the build. |

</details>
<!-- proofs:end -->

## System prerequisites

`make install` puts [elan](https://github.com/leanprover/elan) in `~/.elan` (no sudo), and elan fetches Lean
v4.35.0. From your package manager you need:

| Need | Why |
| --- | --- |
| `git`, `curl` | the elan installer |
| a C toolchain and libc headers | Lean and the host simulator link native executables |
| `python3` with `venv` | the build scripts (Pillow goes into `.venv`) |
| Linux x86-64 | JieLi's compiler is a Linux x86-64 binary; macOS and Windows are not supported |
| `bubblewrap` | the sandbox `lake comparator` uses (`make check`) |

Arch: `sudo pacman -S --needed git curl base-devel python bubblewrap`.
Debian / Ubuntu: `sudo apt install git curl build-essential python3 python3-venv bubblewrap`.
Fedora: `sudo dnf install git curl gcc make python3 bubblewrap`.
`bubblewrap` needs unprivileged user namespaces (`sysctl kernel.unprivileged_userns_clone` not 0).

## Targets

| Target | Does |
| --- | --- |
| `make install` | elan and Lean, `.venv`, the JieLi toolchain (SHA-256 pinned, into `vendor/`), `lake build` |
| `make run` | build the web simulator and serve it at http://localhost:8000/ |
| `make web` | build only, into `build/web/` |
| `make pitch` | the pitch deck, `build/pitch/index.html` (`docs/PITCH.md` is the run sheet) |
| `make test` | headless test of the web build in node: boot, sound, screen, LEDs, the watched theorems, the demos |
| `make test-exports` | every scalar Lean export run as compiled C, and the kernel asked whether it agrees |
| `make fw` | build `fw/build/dinghy.fwsc` (does not flash) |
| `make lean-check` | the Lean in `Firmware/` links for the chip with only the runtime in `rt/` |
| `make proofs` | regenerate `docs/PROOFS.md` and the Comparator challenge from the proof docstrings |
| `make comparator` | `lake comparator`: `Proofs/` proves every statement in `Challenge.lean` with standard axioms only (`PARANOID=1` adds the five external checkers) |
| `make perf` | instructions per sample on this machine (`docs/BUDGET.md`) |
| `make lint` | style and proof layout checks |
| `make check` | lint, lean-check, test-lean, test-exports, comparator |
| `make flash-deps` | the MIDI libraries `fw/tools/fm1_install.py` needs |

## Licence, releases, pins

- GPL-3.0 (`LICENSE`). `fw/` is Dinghy, vendored at a fixed commit (`fw/UPSTREAM.md`). Braids and Clouds code
  under `voices/` and `fx/` is MIT (`fw/LICENSING.md`).
- Releases carry `formalfred.fwsc`, identity `FM-1_960`, with the update loader, so another firmware can be
  installed over it. The Firmware Hub card is `fmhub.json` and `docs/card.png` (`tools/make_card.py`). It has
  no project or sample format and reads no other firmware's files.
- `lean-toolchain` pins Lean; there are no dependencies beyond core Lean.

## What is trusted

The proofs are about the Lean in `Firmware/`. `Challenge.lean` is the statements of `Proofs/` restated without
proofs (`tools/gen_challenge.py`); `lake comparator` checks in a sandbox that `Proofs/` proves each of them using
only `propext`, `Classical.choice` and `Quot.sound`. What the statements mean rests on the definitions in `Spec/`
and `Firmware/` and the English beside them, which are read, not proved; `lake check` replays the whole build
through the kernel (run by hand; `make check` runs Comparator, the GitHub workflow runs neither). `docs/PROOFS.md`
lists each theorem with the definitions its statement depends on. `Examples/` runs every theorem on concrete
inputs, so the hypotheses are known to be satisfiable, and `#guard`s that the specs reject bad inputs. No
`axiom`, no `native_decide` (`make lint` refuses both); `maxRecDepth` is raised in three proof files for big
`decide`s, `maxHeartbeats` never.

Not covered by the proofs:

- The statements themselves: `Lane.Valid`, `Patch.Fits`, `Machine`, `Reverb.loop` and the rest of `Spec/` say
  what is promised; `Examples/` shows each is satisfiable on real inputs, nothing shows they are the right thing
  to promise.
- `rt/lean_rt.c`, the Lean runtime for the chip (`docs/LEAN-ON-CHIP.md`).
- Lean's compiler to C, and JieLi's clang from C to the chip.
- The C left in `voices/` and `fx/`: Braids' per-block setup, the delay memories, and the loops that call the
  Lean steps (`docs/LEAN-ENGINES.md`, `docs/FX.md`). `make test-lean` checks the reverb glue calls the steps in
  the order `Reverb.loop` says, over 20000 samples, and compares the result against Clouds.
- Dinghy (`fw/`: platform, drivers, the update path) and `fw/firmware/src/dinghy.c`, which calls the Lean. The
  master gain and clip in `platform.c`.
- The hardware, and `web/web_host.c` in the simulator.
- 34 `@[extern] opaque` table readers for Braids' wavetables and lookup tables. Their only contract is the return
  type, so a theorem that mentions one holds whatever they return; the caller proves the index is in bounds
  (`*_reads_inside_*`), and those engine steps are tested against the C++.
- Five more readers (`incrementTable`, `Percussion.cutoffTable`, `rateTable`, `vowelAmplitudeAt`, `tableSteps`)
  are `@[extern] def`s whose Lean bodies are copies of Braids' tables (`Firmware/BraidsData.lean`, generated by
  `tools/gen_tables.py`, kept in step by `make lint`). The `braids_data_*` theorems are about the copies; that the
  C accessor reads the same table is trusted.

Two tests reach into that list. `make test-exports` compiles 354 of the 469 `@[export fm1_*]` functions to C (85
read the opaque tables and cannot be evaluated by the kernel; 30 take objects), runs them on random inputs, and
asks the kernel to confirm each value by `decide +kernel`: 2124 values a run, the compiled code against the
definitions the theorems are about. And `fw/firmware/src/watch.h` asserts twelve of the theorems on the running
machine, in the simulator and host builds, at the point `dinghy.c` takes the Lean's answer: notes in scale and on
a hit, note-ons balancing note-offs, mix and pan bounds, a swung quarter note being 24 ticks, the chord root in
key, a patch decoding back to its bytes. `make test` fails if one trips, and prints the count (tens of millions
over the smoke run and the 21 demos) and the failures, which must be zero.
