#!/usr/bin/env bash
# Build Charon + Aeneas from source into ~/work/_verif-tools (the sound Rust→Lean
# pipeline for leanlift's Rust front-end). Idempotent: re-running skips finished
# steps. Mirrors the spike's REPRODUCE_VERIFICATION.md Track B. ~20–40 min.
set -uo pipefail

ROOT="$HOME/work/_verif-tools"
AENEAS="$ROOT/aeneas"
mark() { printf '\n========== %s ==========\n' "$1"; }

mkdir -p "$ROOT"
cd "$ROOT" || exit 1
eval "$(opam env)"

mark "1/6 clone aeneas"
[ -d "$AENEAS/.git" ] || git clone --depth 1 https://github.com/AeneasVerif/aeneas.git
cd "$AENEAS" || exit 1

mark "2/6 opam deps (into the 5.3.0 switch)"
opam install -y ppx_deriving visitors easy_logging zarith yojson core_unix \
  odoc ocamlgraph menhir ocamlformat.0.27.0 unionFind progress domainslib \
  || { echo "opam install FAILED"; exit 1; }

mark "3/6 clone + pin charon"
PIN="$(tail -1 charon-pin)"
echo "charon pin: $PIN"
[ -d "$AENEAS/charon/.git" ] || git clone https://github.com/AeneasVerif/charon
( cd charon && git checkout "$PIN" )

mark "4/6 build charon (installs pinned nightly; compiles the rustc driver)"
( cd charon && make build-charon-rust ) || { echo "charon build FAILED"; exit 1; }

mark "5/6 ensure gmake"
command -v gmake >/dev/null || brew install make

mark "6/6 build aeneas"
gmake check-charon || { echo "check-charon FAILED"; exit 1; }
gmake build        || { echo "aeneas build FAILED"; exit 1; }

mark "DONE"
ls -la "$AENEAS/bin/aeneas" && echo "aeneas built OK"
echo "charon: $AENEAS/charon/bin/charon"
