# The sequencers

Each lane is one `Lane` (`Firmware/Lane.lean`): a clock divider drives a rhythm source, each hit may play a
note, and a note source picks the pitch, which the scale then adjusts. The two sources are chosen on the SEQ
pages and combine freely: four rhythms by eleven note sources.

## Rhythm sources (SEQ > FEEL)

| FEEL | Knobs | What it does |
|---|---|---|
| EUCLID | (HITS, STEPS on RHYTHM) | `hits` spread as evenly as whole steps allow (`Euclid.hit`) |
| ROTATE | ROTATE, ACCENTS | the Euclidean bar turned by `rotate` steps; `accents` of the hits spread by a second Euclidean pattern over the hits are played louder, the rest softer |
| AUTOMAT | RULE | an elementary cellular automaton (rule 0 to 255) on a ring of `steps` cells, seeded from the Euclidean bar, one generation a bar; a dead row is reseeded. Rule 90 is the Sierpinski triangle, 30 is chaos, 204 freezes |
| RATCHET | RATCHET, SUBHITS | each hit split into `ratchet` (1 to 4) sub-hits, of which `subhits` play (the hit itself always); each sub-hit's gate is cut to its share of the step |

The circle on RHYTHM and FEEL shows the live bar: hits in the lane colour, accents bigger, the current step
white; the automaton's row changes every bar.

## Note sources (SEQ > NOTES)

| ALGO | Knobs | What it does |
|---|---|---|
| RANDOM | | a random position in the range |
| WALK | STEP | a random step of up to `step` positions, stopping at the ends |
| UP, DOWN | | climb or fall through the range and wrap |
| BOUNCE | | up and down |
| LOOP | LENGTH, MUTATE | replay a memory of `length` notes; each slot has `mutate` percent chance to be replaced when it plays |
| TURING | LENGTH, FLIP | a shift register of `length` bits; the recycled bit flips with `flip` percent chance; the low byte sets the pitch. FLIP 0 is a locked loop |
| STEP | LENGTH, MUTATE | LOOP whose memory you play in: with the lane chosen and STEP on, each key writes the next slot |
| MARKOV | STYLE, JUMP | a move of -3 to +3 positions chosen from the last move's row of weights: a style (STEPS, LEAPS, REPEATS, ARCS) until you play keys, which it learns from (REC forgets); JUMP doubles a move sometimes |
| GRAMMAR | GRAMMAR, DEPTH | an L-system (FIBO, CANTOR, THUE, ROUND) expanded `depth` levels; each symbol moves the line by a step or a third |
| CHORD | TONES, OCTAVE | climbs `tones` notes of the lane's scale from its bottom note (with chord follow, the chord); OCTAVE is the chance of an octave jump |

The keys teach only the chosen lane, and only STEP and MARKOV listen. REC gives a lane a new seed: a new random
loop, register and automaton row, and an unlearnt chain.

## What is proved (`docs/PROOFS.md`)

- Every source keeps the lane consistent (`lane_tick_valid`, `lane_set_rhythm_valid`, `lane_learn_valid`,
  `notes_choose_stays_in_range`, `notes_learn_keeps_valid`), so the whole-run promises hold for all of them:
  every note-on has a note-off, the clock never drifts, every note is in the scale.
- A note starts only on a step the rhythm marks as a hit (`lane_note_only_on_hit`); an accent only falls on a
  hit (`rhythm_accent_only_on_hit`); the automaton's row stays the size of the bar
  (`rhythm_automaton_row_fits`); the last step of a Euclidean bar always hits (`euclid_last_step_hits`).
- MARKOV never moves more than three positions, GRAMMAR more than two, WALK more than its STEP
  (`notes_markov_moves_at_most_three`, `notes_grammar_moves_at_most_two`, `notes_walk_bounded`); LOOP with no
  mutation repeats exactly (`notes_loop_repeats`), which STEP shares.
- TURING with FLIP 0 is an exact loop of LENGTH notes (`notes_turing_locked_repeats`).
- ROTATE keeps the number of hits (`rhythm_rotate_keeps_hits`); rule 0 is silence, rule 255 is every step, rule
  204 freezes the bar (`rhythm_rule_zero_dies`, `rhythm_rule_full_fills`, `rhythm_rule_204_freezes`); a patch's FEEL
  settings come back exactly when it loads (`lane_from_patch_keeps_feel`).
- Not proved: anything about which other rules live or die, or the markov chain's learnt weights beyond their
  range.

## In patches

The FEEL settings are saved with the lane (`Firmware/Patch.lean`, layout version 2: 22 bytes a lane, 98 a
patch; `patch_decode_encode_round_trip` covers them, and a slot with a rotation past its steps or more
accents than hits does not load). Version 1 slots from before no longer load.

## The arpeggiator (ARP)

`Firmware/Arp.lean`: the keys you hold, played one at a time in step with the clock whether the lanes run or
not, on the chosen lane's sound. MODE: OFF (the keys play straight), UP, DOWN, UPDOWN, RANDOM, PLAYED (in the
order pressed); RATE a note value; OCTAVES 1 to 3; GATE as a share of the step. ARP again on its page latches:
the notes keep going after the keys are let go, and the next phrase you play replaces them; PLAY stopping lets
them go. The keys still teach STEP and MARKOV lanes while the arpeggiator plays them.

Proved (`Proofs/Arp.lean`): every note it starts is one you are holding, raised by whole octaves
(`arp_note_is_held`); every op keeps it consistent; over any run of ticks, keys and settings every note-on has a
note-off (`arp_every_note_on_has_a_note_off`).

## The demo songs

The first seven patches (the DEMOS group of the browser, and the DEMO knob on GLO > BANKS, which steps through
them) each show the sequencers off; CLOCKWORK is the boot patch. Rendered by `tools/render_web.mjs`, none
clips (peaks -7 to -15 dBFS); nobody has listened to them.

| Demo | What it shows |
|---|---|
| CLOCKWORK (104, D dorian) | a locked TURING bass with an accent, a rule-30 AUTOMATON ticking on a dark plucked string, RATCHET stabs, a MARKOV bell on a turned bar |
| AIRPORTS (64, D pentatonic) | after Eno: bars of 7, 11, 13 and 5 steps (coprime: they realign every 5005 steps), a CHORD pad, a locked TURING flute, a MARKOV bell, a GRAMMAR pad that rests |
| PHASES (120, G pentatonic) | after Reich: the same locked twelve-note phrase on 12 and on 13 steps, drifting apart and back |
| SIERPINSKI (96, A lydian) | rule 90 draws its triangle on 32 steps, rule 110 crawls on 16, rule 30 boils underneath, a CHORD pad |
| MARKET (96, F dorian) | MARKOV in every style over a walking bass; play the keys and the chosen lane learns |
| FIBONACCI (80, C lydian) | the three GRAMMARS at three depths over a CHORD pad |
| RATCHETS (128, chromatic drums) | a four-on-the-floor kick, a RATCHET snare and hats, a TURING bass that doubles up |
