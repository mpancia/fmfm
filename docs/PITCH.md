# The five-minute pitch

The deck is `site/pitch/`. `make pitch` renders it to `build/pitch/index.html` (needs `ffmpeg`); the site carries
the same deck at `pitch/`. The theorem cards, the counts and the demo video are made at build time from `Proofs/`,
git and the web build, so build it after the last commit.

| Key | Does |
|---|---|
| → space | on the dark opening slide, starts the opening; after that the next card or line, then the next slide |
| ← | the slide before |
| N | the presenter's notes, as a band at the foot of the screen |
| S | starts the five-minute bar along the top (rose; black once the five minutes are up) and the clock in the corner |
| P | on slide 7: the film plays or pauses; R starts it again. On slide 1, R plays the opening again |

## The film

`make video` (`tools/make_video.py`) makes the song: four stem presets (STEM PAD, KEYS, DRUMS, LEAD; F major at 108,
vi-IV-I-V) each played by its own run of the simulator from the same instant, mixed as an arrangement with filter
sweeps, LFOs and punch-ins scripted on each, the four screens in a grid, and a chapter card with a theorem for each
part. `make pitch` copies it into the deck as slide 7. Buttons are ignored during Alfred's boot bow (the first 3.3 s),
so a script's first press comes after it.

## Setting up

- The FM-1 on a powered speaker (USB audio or the headphone jack), charged. The deck on the second screen.
- On the device: PRESETS, SELECT until the group is DEMOS, scroll to ELECTRIC, load it; SELECT until lane 1 is the
  chosen lane; PLAY. Leave it running.
- On the laptop: `make run` serving the simulator at http://localhost:8000/ with ELECTRIC loaded, in case the
  device fails. Its page shows the watch counters.
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
| 2:35 | 7, the song | P. | The film narrates itself; the URL and `make install && make run` are on the label. With a judge instead: hand the device over, QUANT on, "play anything", REC and any three keys, PLAY. |
| 4:50 | | PLAY on the device. | Silence, Alfred in the corner. |

Behind the clock: drop slide 4 (twenty-five seconds), then slide 3 (twenty-five). P stops a video at any point.

## The three steps, button by button

ELECTRIC is in F, I V vi IV; lane 1 is the piano and the chosen lane.

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

- The device is silent or restarts: P on slide 7 plays the film, or the laptop's simulator takes the
  device's part with the same steps (`Z`.. is the lower octave, `Q`.. the upper; the page's buttons are the
  panel's).
- The speaker fails: the FM-1's own speaker carries a small room; move it nearer the judges.
- The deck fails: this page is the talk, and every theorem's sentence is in `docs/PROOFS.md`.

## Questions to expect

- *What is not proved?* The C glue (Braids' per-block setup, the delay lines, the loops that call the Lean), the
  drivers, Dinghy's platform, Lean's C backend, JieLi's clang, the 14 KB runtime: the README's "What is trusted".
- *Is it a model?* No. The theorems are about the definitions compiled to the chip. `make test-exports` runs the
  compiled code and asks the kernel for the same values; the watch asserts twelve statements on the running
  firmware.
- *Was all of this done in the hackathon?* Yes, from the Dinghy template (a sine on the keys) on 31 October. The
  commit log is the timeline.
- *Does Comparator pass?* `make comparator` on every build; `PARANOID=1` adds five external checkers, and all accept.
