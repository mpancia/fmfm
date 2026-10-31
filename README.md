# fmfm

Custom firmware for the M-VAVE FM-1 pocket synth, with the core logic in Lean 4 (Vibecheck hackathon).
See `docs/FM1.md` for research, hardware facts and flash safety.

```
make install && make run
```

Then open http://localhost:8000/ and click **Power on**. The simulator runs the real firmware app
(`fw/firmware/src/dinghy.c`) compiled to WebAssembly, with the FM-1's screen, keys, buttons, knobs, audio and
(in Chrome/Edge) MIDI in. No FM-1 needed. See `docs/SIMULATOR.md`.

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
- `fw/` (Dinghy: platform, drivers, update path) and `fw/firmware/src/dinghy.c`, the C that calls the Lean code.
- The hardware, and `web/web_host.c` for the simulator.
- Lean's `Init` library compiled for the chip by `tools/build_lean_init.sh`.
