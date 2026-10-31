#!/bin/sh
# Fetch JieLi's pi32v2 toolchain and the three AC79 SDK files the Dinghy build needs
# into vendor/ (git-ignored: JieLi's licence forbids redistributing the toolchain).
# Every file is checked against a pinned SHA-256; a mismatch deletes the download.
# Layout produced:
#   vendor/toolchain/            JIELI_TOOLCHAIN  (contains pi32v2/ and common/)
#   vendor/ac79/cpu/wl82/tools/  AC79_SDK         (uboot.boot, cfg_tool.bin, cfg/eq_cfg_hw.bin)
set -eu
cd "$(dirname "$0")/.."
V=vendor
TC_VER=20250324.1
TC_FILE=jieli-linux-toolchains-$TC_VER.tar.xz
TC_URL=https://jl-update.oss-cn-shenzhen.aliyuncs.com/$TC_FILE
TC_SHA=f686586bcfb45e0f0bb27fd2b39c7a7f313cb4f0e88a66a14da621ffa8225958
SDK_URL=https://gitee.com/Jieli-Tech/fw-AC79_AIoT_SDK/raw/AC79NN_SDK_V1.2.1_2023-12-13/cpu/wl82/tools

fetch() { # url dest sha256
    if [ -f "$2" ] && echo "$3  $2" | sha256sum -c - >/dev/null 2>&1; then return; fi
    echo "fetch $1"
    # no -k: a TLS problem or geo-block is reported, never bypassed
    curl -fsSL --retry 3 --connect-timeout 30 -o "$2.part" "$1" ||
        { rm -f "$2.part"; echo "vendor.sh: cannot download $1 (blocked network? copy the file to $2 by hand)" >&2; exit 1; }
    echo "$3  $2.part" | sha256sum -c - >/dev/null 2>&1 ||
        { rm -f "$2.part"; echo "vendor.sh: SHA-256 mismatch for $2, discarded" >&2; exit 1; }
    mv "$2.part" "$2"
}

mkdir -p "$V/dl" "$V/ac79/cpu/wl82/tools/cfg"
fetch "$TC_URL" "$V/dl/$TC_FILE" "$TC_SHA"
fetch "$SDK_URL/uboot.boot" "$V/ac79/cpu/wl82/tools/uboot.boot" 4e3b4c220dc96641cb5a723f41e68ce41d5261ae9434bb33fbd7f2c59976ded4
fetch "$SDK_URL/cfg_tool.bin" "$V/ac79/cpu/wl82/tools/cfg_tool.bin" 276579954f076886a6a7694f65dc71c034a63a2c204b76749065c0ac7b010d1b
fetch "$SDK_URL/cfg/eq_cfg_hw.bin" "$V/ac79/cpu/wl82/tools/cfg/eq_cfg_hw.bin" 41167491bffed4651750719c973d2758adeb9021a5670d02d6a53c85ed80ea7d

if [ ! -x "$V/toolchain/pi32v2/bin/clang" ]; then
    rm -rf "$V/toolchain"; mkdir -p "$V/toolchain"
    tar -xJf "$V/dl/$TC_FILE" -C "$V/toolchain" --strip-components=1
fi
"$V/toolchain/pi32v2/bin/clang" --version | head -1
