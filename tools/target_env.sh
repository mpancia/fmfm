# Sourced by the build scripts. Sets, for $T (wasm32, pi32v2 or host, this computer):
#   CC  compiler command for Lean-generated C and rt/, CXX  the same for the Braids C++ in voices/,
#   AR  archiver, PREFIX  the Lean toolchain
export PATH="$HOME/.elan/bin:$PATH"
PREFIX=$(lean --print-prefix)
case $T in
  wasm32) CC="$PREFIX/bin/clang --target=wasm32 -ffreestanding -nostdlib -isystem $PREFIX/include/clang -I$PREFIX/include -I$PWD/rt"
          AR="$PREFIX/bin/llvm-ar"
          CXX="$PREFIX/bin/clang --target=wasm32 -x c++ -ffreestanding -nostdlib -isystem $PREFIX/include/clang" ;;
  pi32v2) CC="$PWD/vendor/toolchain/pi32v2/bin/clang -target pi32v2 -fno-builtin -DFM1_CHIP -I$PREFIX/include -I$PWD/rt"
          AR="$PWD/vendor/toolchain/common/bin/ar"
          CXX="$PWD/vendor/toolchain/pi32v2/bin/clang -target pi32v2 -x c++ -fno-builtin"
          [ -x "$PWD/vendor/toolchain/pi32v2/bin/clang" ] || { echo "no JieLi toolchain: run tools/vendor.sh"; exit 1; } ;;
  host)   CC="$PREFIX/bin/clang --target=i386-linux-gnu -m32 -msse2 -w -isystem $PREFIX/include/clang -isystem $PREFIX/include -I$PWD/rt"
          AR=ar                                   # Lean's clang, as the chip's is a clang; the system c++ links
          CXX="$PREFIX/bin/clang --target=i386-linux-gnu -m32 -x c++ -isystem $PREFIX/include/clang" ;;
  *) echo "unknown target '$T' (wasm32, pi32v2 or host)"; exit 1 ;;
esac
