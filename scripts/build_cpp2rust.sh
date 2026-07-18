#!/usr/bin/env bash
# Build cpp2rust (https://github.com/Cpp2Rust/cpp2rust — clang-AST C++→Rust
# translator, MIT) into ~/work/_verif-tools, for leanlift's optional
# deterministic C++ front-end: C++ →(cpp2rust)→ Rust →(Charon+Aeneas)→ Lean.
# Idempotent: re-running skips finished steps. Mirrors scripts/build_aeneas.sh.
#
# cpp2rust needs clang/libclang >= 21 (it uses the reworked type-system API:
# getCanonicalTagType, PredefinedSugarType, …). Distro clang 18 does NOT
# compile it. If no system clang-22 cmake package is found, this script
# downloads the official LLVM 22.1.8 release tarball (~1.7 GB, no sudo) into
# ~/work/_verif-tools/llvm22 and builds against that.
# Override the install root with LEANLIFT_CPP2RUST.
set -uo pipefail

ROOT="$HOME/work/_verif-tools"
C2R="${LEANLIFT_CPP2RUST:-$ROOT/cpp2rust}"
PIN="adab7fe07ed937b1b3b3cc63492fd05e515e89d7" # master 2026-07-16
LLVM_VER="22.1.8"
LLVM_TARBALL="LLVM-$LLVM_VER-Linux-X64.tar.xz"
mark() { printf '\n========== %s ==========\n' "$1"; }

mkdir -p "$ROOT"

mark "1/5 clone cpp2rust (pin $PIN)"
[ -d "$C2R/.git" ] || git clone https://github.com/Cpp2Rust/cpp2rust "$C2R"
cd "$C2R" || exit 1
git fetch -q origin "$PIN" 2>/dev/null
git checkout -q "$PIN" || { echo "checkout of pin FAILED"; exit 1; }

mark "2/5 locate a clang >= 21 toolchain"
CMAKE_TOOLCHAIN_ARGS=()
if [ -d /usr/lib/llvm-22/lib/cmake/clang ] && [ -e /usr/lib/llvm-22/lib/libclangBasic.a ]; then
  echo "using system llvm-22"
  CMAKE_TOOLCHAIN_ARGS=(-DLLVM_DIR=/usr/lib/llvm-22/lib/cmake/llvm -DClang_DIR=/usr/lib/llvm-22/lib/cmake/clang)
else
  LLVM_LOCAL="$ROOT/llvm22/LLVM-$LLVM_VER-Linux-X64"
  if [ ! -x "$LLVM_LOCAL/bin/clang++" ]; then
    echo "downloading LLVM $LLVM_VER release tarball (~1.7 GB)…"
    mkdir -p "$ROOT/llvm22" && cd "$ROOT/llvm22"
    curl -sLO "https://github.com/llvm/llvm-project/releases/download/llvmorg-$LLVM_VER/$LLVM_TARBALL" \
      || { echo "download FAILED"; exit 1; }
    tar xf "$LLVM_TARBALL" && rm -f "$LLVM_TARBALL"
    cd "$C2R" || exit 1
  fi
  echo "using $LLVM_LOCAL"
  CMAKE_TOOLCHAIN_ARGS=(-DLLVM_DIR="$LLVM_LOCAL/lib/cmake/llvm" -DClang_DIR="$LLVM_LOCAL/lib/cmake/clang")
fi

mark "3/5 configure (cmake -GNinja, Release)"
cmake -S . -B build -GNinja -DCMAKE_BUILD_TYPE=Release "${CMAKE_TOOLCHAIN_ARGS[@]}" \
  || { echo "cmake configure FAILED"; exit 1; }

mark "4/5 build the translator"
ninja -C build cpp2rust || { echo "build FAILED"; exit 1; }

mark "5/5 build the libcc2rs runtime (for the safe pointer model)"
if [ -d libcc2rs ] && command -v cargo >/dev/null; then
  ( cd libcc2rs && cargo build --release ) || echo "libcc2rs build failed (non-fatal: scalar kernels don't need it)"
fi

mark "DONE"
ls -la "$C2R/build/cpp2rust/cpp2rust" && echo "cpp2rust built OK at $C2R/build/cpp2rust/cpp2rust"
