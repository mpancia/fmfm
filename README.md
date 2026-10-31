# fmfm

Lean 4 project for the Vibecheck hackathon.

```
make install && make run
```

## System prerequisites

`make install` installs [elan](https://github.com/leanprover/elan) into
`~/.elan` (no sudo) and elan downloads the exact Lean pinned in
`lean-toolchain` (v4.35.0). You need these from your system package manager:

| Need | Why |
| --- | --- |
| `git`, `curl` | elan installer, Lake dependency fetches |
| a C toolchain + libc headers | Lean links native executables |
| `bubblewrap` (Linux only) | sandbox used by `lake check` / `lake comparator` |

Arch / CachyOS: `sudo pacman -S --needed git curl base-devel bubblewrap`
Debian / Ubuntu: `sudo apt install git curl build-essential bubblewrap`
Fedora: `sudo dnf install git curl gcc make bubblewrap`
macOS: `xcode-select --install` (no bubblewrap; `lake check` is Linux-only)

`bubblewrap` also needs unprivileged user namespaces
(`sysctl kernel.unprivileged_userns_clone` must not be `0`).

## Targets

| Target | Does |
| --- | --- |
| `make install` | install elan if missing, fetch pinned toolchain, `lake build` |
| `make run` | `lake exe fmfm` |
| `make check` | `lake check`: kernel replay, standard axioms only (Linux) |

## Reproducibility

- `lean-toolchain` pins Lean. `lakefile.toml` + `lake-manifest.json` pin
  dependencies (currently none: core Lean only). Never run `lake update`
  except on purpose.
- Secrets live in `.env`, which is git-ignored.

## Trusted surface

Nothing yet.
