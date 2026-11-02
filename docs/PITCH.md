# The five-minute pitch

The deck is `site/pitch/`. `make pitch` renders it to `build/pitch/index.html` (it needs `ffmpeg`); the site carries
the same deck at `pitch/`. The theorem cards, the counts and the demo video are made at build time from `Proofs/`,
git and the web build, so build it after the last commit.

| Key | Does |
|---|---|
| → space | on the dark opening slide, starts the opening; after that the next card or line, then the next slide |
| ← | the slide before |
| N | the presenter's notes, as a band at the foot of the screen |
| S | starts the five-minute bar along the top (rose; black once the five minutes are up) and the clock in the corner |
| P | on slides 7, 8 and 9: the video plays or pauses; R starts it again. On slide 1, R plays the opening again |

## The demos that run themselves

`tools/make_pitch.py` drives the simulator (the firmware as WebAssembly, `tools/render_web.mjs`) through three scripts
and records the screen and the sound as WebM. **THE WALKS** (44 s): TONNETZ walking the 24 triads with the HARMONY page shown, HEXATONIC, BLACK KEYS. **ELECTRIC** (40 s), the ballad on the FM voice: QUANT set to SCALE and
a line played on the white keys; REC with THROW, WASH and HALF time, each let go; PLAY. **NIGHT DRIVE**
(41 s), the electronic track: the 808 kick and snare, the filtered FM bass and the filtered saw lead, the snare and
lead taken out on the PUNCH page and let back in; STUTTER, GATE, CRUSH, a BREAK drop; the bass's CUTOFF swept on the
FILTER page; DOUBLE and HALF; PLAY. On each slide the sentence under the picture and the lit card follow the video,
and the last sentence gives the number of theorem checks the watch made during the run and how many failed. The videos
stand in for a judge when there is none, and loop at a demo table. Buttons are ignored during Alfred's boot bow (the
first 3.3 s), so a script's first press comes after it.

## Setting up

- The FM-1 on a powered speaker (USB audio or the headphone jack), charged. The deck on the second screen.
- On the device: PRESETS, SELECT until the group is DEMOS, scroll to ELECTRIC, load it; SELECT until lane 1 is the
  chosen lane; PLAY. Leave it running.
- On the laptop: `make run` serving the simulator at http://localhost:8000/ with ELECTRIC loaded, in case the device
  fails. Its page shows the watch counters.
- The deck on slide 1. Press S as you start.

## The clock

| At | Slide | Do | Say |
|---|---|---|---|
| 0:00 | 1, the opening | →. Nothing for fifteen seconds. | "This is a sixty-dollar keyboard. Everything you are hearing is decided by Lean code on its chip, and the theorems about that code went through Lean's kernel this morning." |
| 0:25 | 2, the FM-1 | | The unit; two hundred firmwares in six weeks, nearly all AI-written C, down to a fart machine; the chip has no floating point and no debugger. "Ours was written the same way, in Lean, and the kernel checks the theorems on every build." |
| 0:55 | 3, the instrument | | A generative sequencer with a modular's oscillator in a $60 keyboard; the rules are the song. Why prove it: the promises are audible and a theorem covers every knob; fixed-point bugs are silent; no debugger. |
| 1:20 | 4, what it does | | Four pages: the sequencer, the engines, the effects, the PUNCH page. |
| 1:45 | 5, Lean on the chip | | One pipeline and no model: the theorems are about the definitions the chip runs. Two checks reach into the C: the compiled code against the kernel, and twelve theorems asserted while it runs. What stays in C is on the right. |
| 2:10 | 6, what is proved | | Five kinds of theorem: the music over a whole performance; music theory about the firmware's own tables; fixed-point arithmetic, the largest; the mix and effects; the patch format. |
| 2:35 | 7, the walks | P. | TONNETZ, HEXATONIC, BLACK KEYS: the chord progressions that are group theory, and what they sound like. |
| 3:20 | 8, ELECTRIC | P. Or a judge takes the device and → lights a card as you name it. | The ballad, a line played over it, punched in, stopped. |
| 4:05 | 9, NIGHT DRIVE | P. | The 808 and the filtered bass, the drop, the filter swept, stopped. The URL and `make install && make run` are on the label. |
| 4:50 | | PLAY on the device. | Silence, Alfred in the corner. |

Behind the clock: drop slide 4 (twenty-five seconds), then slide 3 (twenty-five); the videos can be stopped with P at any point.

## The three steps, button by button

ELECTRIC is in F, I V vi IV; lane 1 is the piano and lane 1 is the chosen lane. These are the three cards of slide 8.

1. **QUANT.** ARP with nothing held, ARP again: the QUANT page. Knob 1 to SCALE. Hand the device over: "Play
   anything, with both hands. A wrong note is not possible." The white keys are the degrees of F major; a black key
   plays as the white below it. Card 1, `keys_in_scale`.
2. **Punch.** REC: the PUNCH page, where the keys are effects. Ask for CRUSH (the ninth key from the left, A4),
   STUTTER (the third, G3) and WASH (the tenth, A#4), held together. "Now let go." The song is where it was. Card 2,
   `punch_nothing_held_changes_nothing`. REC again leaves the page.
3. **Stop.** "Stop it." PLAY. Silence at once; Alfred steps into the corner. Card 3,
   `run_every_note_on_has_a_note_off`.

The PUNCH page's keys, from the lowest: HALF, DOUBLE, STUTTER, ROLL, OCT-, OCT+, SHIFT, GATE, CRUSH, WASH, THROW,
BREAK, then MUTE 1 to 4, then ROLL 1 to 4. The screen names them, and a held key is lit.

## If something fails

- The device is silent or restarts: P on slide 7, 8 or 9 plays a recording, or the laptop's simulator takes the device's part
  with the same steps (`Z`.. is the lower octave, `Q`.. the upper; the page's buttons are the panel's).
- The speaker fails: the FM-1's own speaker carries a small room; move it nearer the judges.
- The deck fails: this page is the talk, and every theorem's sentence is in `docs/PROOFS.md`.

## Questions to expect

- *What is not proved?* The C glue (Braids' per-block setup, the delay lines, the loops that call the Lean), the
  drivers, Dinghy's platform, Lean's C backend, JieLi's clang, the 14 KB runtime: the README's "Trusted surface".
- *Is it a model?* No. The theorems are about the definitions that are compiled to the chip. `make test-exports`
  runs the compiled code and asks the kernel for the same values; the watch asserts twelve statements on the
  running firmware.
- *Was all of this done in the hackathon?* Yes, from the Dinghy template (a sine on the keys) on 31 October. The
  commit log is the timeline.
- *Does Comparator pass?* `make comparator` on every build; `PARANOID=1` adds five external checkers, and all accept.
