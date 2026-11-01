# FORMALFRED

A generative sequencer for the M-VAVE FM-1 pocket synth, with its sequencing logic proved in Lean 4 (Vibecheck
hackathon). Alfred the butler is the mascot.

**Site:** https://mpancia.github.io/fmfm/ has the web installer and the browser simulator. It is rebuilt from `main`
by `.github/workflows/site.yml` (`tools/make_site.py` assembles `site/` + `build/web` + the package).
See `docs/FM1.md` for research, hardware facts and flash safety.

```
make install && make run
```

Then open http://localhost:8000/ and click **Power on**. Four lanes start playing at once.

The panel is menu driven, in the manner of Mutable Dreams. Four buttons pick a group of pages, and pressing the
same button again moves to the group's next page. The four knobs set the four values shown on screen.

| Group | Pages (knobs 1 to 4) |
|---|---|
| HOME | overview of the four lanes: hits, steps, speed, chance |
| SEQ | RHYTHM: hits, steps, speed, chance, with the bar drawn as a circle (the hits joined, the current step bright). FEEL: the rhythm source (Euclid, rotate with accents, cellular automaton, ratchet) and its knobs. NOTES: the note source (random, walk, up, down, bounce, loop, turing, step, markov, grammar, chord) and its knobs, range. RANGE: scale, low note, chord follow. See `docs/SEQUENCERS.md` |
| EDIT | SOUND: shape, timbre, colour, level. ENVELOPE: attack, release, envelope-to-timbre. MIX: the four lane levels |
| GLO | HARMONY: key, scale lock, chord progression, bars per chord. SYSTEM: tempo, keys octave. MIDI: in and out channels. BANKS: patch, save slot |

| Control | Does |
|---|---|
| SELECT | choose a lane (in the browser: the sound or patch group) |
| PRESETS | open the browser and scroll: sounds (199) in EDIT, patches (128 factory, 8 user) elsewhere, grouped as ALL, DEMOS, SONGS, the moods and USER (SELECT picks the group). Sounds are grouped by engine (analog, filter, voice, FM, physical, percussion, wavetable, noise) or by type (tone, pluck, pad, drum); ALGO switches the grouping while the browser is open, SELECT picks the group |
| ALGORITHM | tempo |
| PLAY | start or stop the clock (stopping silences every lane) |
| SEL | mute the chosen lane |
| REC | roll a new variation of the chosen lane |
| SAVE | keep the patch in the slot chosen on GLO > BANKS |
| keys, OCT- OCT+ | play the chosen lane's sound by hand |

The FX button opens the sends: REVERB (Clouds' reverb, ported to Lean: SEND of the chosen lane, DECAY, BRIGHT,
RETURN), then DELAY (a tempo-synced echo on the same send: TIME as a note value, FEEDBK, TONE, RETURN). See
`docs/FX.md`.

Note algorithms (SEQ > NOTES), per lane: RANDOM, WALK (random steps of up to AMOUNT notes), UP, DOWN, BOUNCE, and
LOOP (a memory of AMOUNT notes that replays, with MUTATE percent chance of replacing a note each time).
Chord progressions (GLO > HARMONY) change the chord every bar or more; a lane follows them in SEQ > RANGE:
SCALE moves its scale to the chord root, TRIAD keeps only the chord's notes.

Each lane is a clock divider driving a Euclidean rhythm; every hit picks a random note in the lane's range and
snaps it to the scale. That logic is Lean, and `docs/PROOFS.md` lists what is proved about it.

The sound is Mutable Instruments' Braids, all 48 of its oscillator shapes, compiled from its own source
(`voices/`). `make audit` checks every factory sound.

The simulator runs the real firmware app (`fw/firmware/src/dinghy.c`) compiled to WebAssembly, with the FM-1's
screen, keys, buttons, knobs, audio and (in Chrome/Edge) MIDI in. No FM-1 needed. See `docs/SIMULATOR.md`.

## System prerequisites

`make install` installs [elan](https://github.com/leanprover/elan) into
`~/.elan` (no sudo) and elan downloads the exact Lean pinned in
`lean-toolchain` (v4.35.0). You need these from your system package manager:

| Need | Why |
| --- | --- |
| `git`, `curl` | elan installer, Lake dependency fetches |
| a C toolchain + libc headers | Lean and the firmware host simulator link native executables |
| `python3` with `venv` | firmware build scripts (Pillow is installed into `.venv`) |
| Linux x86-64 | JieLi's compiler is a Linux x86-64 binary (macOS/Windows: not supported here) |
| `bubblewrap` (Linux only) | sandbox used by `lake comparator` (`make check`) |

Arch / CachyOS: `sudo pacman -S --needed git curl base-devel python bubblewrap`
Debian / Ubuntu: `sudo apt install git curl build-essential python3 python3-venv bubblewrap`
Fedora: `sudo dnf install git curl gcc make python3 bubblewrap`

`bubblewrap` also needs unprivileged user namespaces
(`sysctl kernel.unprivileged_userns_clone` must not be `0`).

## Targets

| Target | Does |
| --- | --- |
| `make install` | elan + Lean, `.venv`, JieLi toolchain (SHA-256 pinned, into `vendor/`), `lake build` |
| `make run` | build the web simulator and serve it at http://localhost:8000/ (Power on, then play) |
| `make web` | build only: `build/web/` |
| `make test` | headless test of the web build in node (boot, sound, screen, LEDs) |
| `make fw` | build `fw/build/dinghy.fwsc` with the Lean code linked in (does not flash) |
| `make lean-check` | the Lean code in `Firmware/` links for the chip with only the small runtime in `rt/` |
| `make proofs` | list every proved theorem with what it claims and why (`docs/PROOFS.md`); regenerate the Comparator challenge |
| `make comparator` | `lake comparator`: `Proofs/` proves every statement of `Challenge.lean`, standard axioms only, kernel-checked in a sandbox (`PARANOID=1` adds the five external checkers) |
| `make perf` | the firmware on this computer, counting instructions a sample (`docs/BUDGET.md`: what fits the chip) |
| `make lint` | style checks, proof layout checks |
| `make check` | `make lint` + `make lean-check` + `make test-lean` + `make comparator` |
| `make flash-deps` | optional: MIDI libraries for `fw/tools/fm1_install.py` |

## Reproducibility

- `fw/` is Dinghy vendored at a fixed commit (`fw/UPSTREAM.md`), GPL-3.0.
- `lean-toolchain` pins Lean. `lakefile.toml` + `lake-manifest.json` pin
  dependencies (currently none: core Lean only). Never run `lake update`
  except on purpose.
- Secrets live in `.env`, which is git-ignored.

## Trusted surface

Proofs cover the Lean code in `Firmware/`. What is proved is listed in `docs/PROOFS.md`; the same statements are
in `Challenge.lean`, and `make comparator` (Lean 4.35's `lake comparator`) checks in a sandbox that `Proofs/`
proves each of them with no axiom but `propext`, `Classical.choice` and `Quot.sound`. `PARANOID=1` also runs
the five external checkers bundled with Lean (leanchecker-paranoid, lean4lean, nanoda, con-leche, con-ron);
all accept. They do not cover:

- `rt/lean_rt.c`: the small Lean runtime (allocator, freeing, arrays, panics). See `docs/LEAN-ON-CHIP.md`.
- Lean's compiler (Lean to C) and JieLi's clang (C to chip code).
- `voices/`: Braids (C++, tables regenerated for 44.1 kHz) and our wrapper. Every engine's sample arithmetic is
  Lean (`Firmware/Analog.lean` to `Macro.lean`), checked sample for sample against the original by `make test-lean`;
  the per-block setup, the delay lines and the glue loops are C and unproved (`docs/LEAN-ENGINES.md`). `make audit`
  checks levels; nobody has listened to it on hardware.
- `fx/delay_glue.c`: the delay line and its loop (the arithmetic is Lean, `Firmware/Delay.lean`); not heard.
- `fx/reverb_glue.c`: the reverb network and its delay memory (the arithmetic is Lean; the order of operations is C, copied
  from Clouds, and checked sample for sample against `Spec/Reverb.lean` by `make test-lean`, which also checks it
  against Clouds' original); not heard (`docs/FX.md`).
- `fw/` (Dinghy: platform, drivers, update path) and `fw/firmware/src/dinghy.c`, the C that calls the Lean code.
  Its mix loop (level glide, voice sample, reverb send and return) calls `Firmware/Mix.lean`, which
  `Proofs/Mix.lean` shows never wraps; the master gain and the clip in `fw/firmware/src/platform.c` stay C.
- The hardware, and `web/web_host.c` for the simulator.
- Lean's `Init` library compiled for the chip by `tools/build_lean_init.sh`.
