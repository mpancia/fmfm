# M-VAVE FM-1: hardware and flashing

Sources: [aroum/fm1-custom-fw](https://github.com/aroum/fm1-custom-fw) (community hub, reverse-engineering notes),
[maxfridbe/mvave-fm1](https://github.com/maxfridbe/mvave-fm1) (build/flash notes),
[zvenson/dinghy](https://github.com/zvenson/dinghy) (the template vendored into `fw/`),
[Ars Technica](https://arstechnica.com/gadgets/2026/10/from-impulse-purchase-to-pocket-studio-the-m-vave-fm-1/).
We have not tested any of the hardware facts below ourselves.

## Hardware
JieLi AC7911B (pi32v2 RISC, **no FPU**), 1 MiB flash executed in place, 240x240 TFT, 27 keys, 14 buttons,
7 encoders, USB-MIDI/audio, TRS MIDI **in only**. No debug header, no recovery button.

## How the firmware works
- Toolchain: JieLi clang 4.0.1 `-target pi32v2` (Linux x86-64, runs natively). `tools/vendor.sh` fetches it.
- No signature checks on firmware. Install is over USB-MIDI SysEx (`fw/tools/fm1_install.py`) or Chrome WebMIDI.
- `fw/` is Dinghy, a finished platform (OTA updater, USB rescue, boot guard, MIDI, audio, LCD, keys). You edit
  `fw/firmware/src/dinghy.c` (`app_audio`, `app_main`).
- Chip rules, enforced by the build: integers only, no 64-bit division, hardware registers only in `hal/`.
  See `fw/docs/RULES.md`.

## Lean on this chip
See `docs/LEAN-ON-CHIP.md`.

## Flash safety (do before flashing anything)
1. Keep the unit on stock V15 first (V14 + custom firmware fails; community advice).
2. Take a full-flash backup with [MvaveFM1Unbricker](https://github.com/Quixotic7/MvaveFM1Unbricker)
   (`softkey`, `backup`; needs `sudo modprobe sg`). Store dumps in `backups/` (git-ignored).
3. Never write below `0x4000`. Never erase the whole chip.
4. Every firmware you ship must keep the update path and the OCT- rescue. Dinghy's platform has both; don't
   remove them.
5. Don't flash custom over custom; go via stock V15 or TransitFM1.
6. If nothing enumerates, recover with the RP2040 "FM-1 Transporter" dongle.

## Licence
`fw/` is GPL-3.0-only (Dinghy, from Felucca). Firmware built from it must be released as GPL-3.0 with source.
JieLi's toolchain is not redistributable, so `vendor/` is git-ignored.
