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
| SEQ | RHYTHM: hits, steps, speed, chance. NOTES: algorithm, amount, mutate, range. RANGE: scale, low note, chord follow |
| EDIT | SOUND: shape, timbre, colour, level. ENVELOPE: attack, release, envelope-to-timbre. MIX: the four lane levels |
| GLO | HARMONY: key, scale lock, chord progression, bars per chord. SYSTEM: tempo, keys octave. MIDI: in and out channels. BANKS: patch, save slot |

| Control | Does |
|---|---|
| SELECT | choose a lane (in the browser: sound family, or ten patches at a time) |
| PRESETS | open the browser and scroll: sounds (199) in EDIT, patches (122 factory, 8 user) elsewhere |
| ALGORITHM | tempo |
| PLAY | start or stop the clock (stopping silences every lane) |
| SEL | mute the chosen lane |
| REC | roll a new variation of the chosen lane |
| SAVE | keep the patch in the slot chosen on GLO > BANKS |
| keys, OCT- OCT+ | play the chosen lane's sound by hand |

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
| `bubblewrap` (Linux only) | sandbox used by `lake check` / `lake comparator` |

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
| `make proofs` | list every proved theorem with what it claims and why (`docs/PROOFS.md`) |
| `make lint` | style checks, proof layout checks |
| `make check` | `make lean-check` + `lake check` (kernel replay, standard axioms only) |
| `make flash-deps` | optional: MIDI libraries for `fw/tools/fm1_install.py` |

## Reproducibility

- `fw/` is Dinghy vendored at a fixed commit (`fw/UPSTREAM.md`), GPL-3.0.
- `lean-toolchain` pins Lean. `lakefile.toml` + `lake-manifest.json` pin
  dependencies (currently none: core Lean only). Never run `lake update`
  except on purpose.
- Secrets live in `.env`, which is git-ignored.

## Trusted surface

Proofs cover the Lean code in `Firmware/`. They do not cover:

- `rt/lean_rt.c`: the small Lean runtime (allocator, freeing, arrays, panics). See `docs/LEAN-ON-CHIP.md`.
- Lean's compiler (Lean to C) and JieLi's clang (C to chip code).
- `voices/`: Braids (C++, tables regenerated for 44.1 kHz) and our wrapper. Every engine's sample arithmetic is
  Lean (`Firmware/Analog.lean` to `Macro.lean`), checked sample for sample against the original by `make test-lean`;
  the per-block setup, the delay lines and the glue loops are C and unproved (`docs/LEAN-ENGINES.md`). `make audit`
  checks levels; nobody has listened to it on hardware.
- `fw/` (Dinghy: platform, drivers, update path) and `fw/firmware/src/dinghy.c`, the C that calls the Lean code.
- The hardware, and `web/web_host.c` for the simulator.
- Lean's `Init` library compiled for the chip by `tools/build_lean_init.sh`.
