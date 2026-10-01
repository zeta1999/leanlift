#!/usr/bin/env bash
# Build Charon + Aeneas from source into ~/work/_verif-tools (the sound Rust→Lean
# pipeline for leanlift's Rust front-end). Idempotent: re-running skips finished
# steps. Mirrors the spike's REPRODUCE_VERIFICATION.md Track B. ~20–40 min.
#
# Host changes, all scoped:
#   * OCaml packages go into a DEDICATED opam switch ($AENEAS_SWITCH, default
#     `leanlift-aeneas`, OCaml 5.3.0), created if missing. The switch that is
#     active in the caller's shell is never modified.
#   * Charon's pinned Rust nightly comes from charon's own rust-toolchain file:
#     rustup installs that toolchain but does not change the default.
#   * Sources and binaries live under ~/work/_verif-tools.
# Works on macOS and Linux: it needs GNU make, which is `gmake` on macOS
# (installed with brew if absent) and `make` on Linux.
set -uo pipefail

ROOT="$HOME/work/_verif-tools"
AENEAS="$ROOT/aeneas"
SWITCH="${AENEAS_SWITCH:-leanlift-aeneas}"
OCAML="${AENEAS_OCAML:-ocaml-base-compiler.5.3.0}"
mark() { printf '\n========== %s ==========\n' "$1"; }

mkdir -p "$ROOT"
cd "$ROOT" || exit 1

mark "0/6 dedicated opam switch: $SWITCH"
if ! opam switch list --short 2>/dev/null | grep -qx "$SWITCH"; then
  opam switch create "$SWITCH" "$OCAML" --no-switch -y || { echo "opam switch create FAILED"; exit 1; }
fi
eval "$(opam env --switch="$SWITCH" --set-switch)"
echo "using switch: $(opam switch show)  ocaml: $(ocaml -version)"

mark "1/6 clone aeneas"
[ -d "$AENEAS/.git" ] || git clone --depth 1 https://github.com/AeneasVerif/aeneas.git
cd "$AENEAS" || exit 1

mark "2/6 opam deps (into $SWITCH only)"
opam install -y ppx_deriving ppx_deriving_yojson visitors easy_logging zarith \
  yojson core_unix odoc ocamlgraph menhir ocamlformat.0.27.0 unionFind progress \
  domainslib || { echo "opam install FAILED"; exit 1; }

mark "3/6 clone + pin charon"
PIN="$(tail -1 charon-pin)"
echo "charon pin: $PIN"
[ -d "$AENEAS/charon/.git" ] || git clone https://github.com/AeneasVerif/charon
( cd charon && git checkout "$PIN" )

mark "4/6 build charon (installs pinned nightly via its rust-toolchain file; compiles the rustc driver)"
( cd charon && make build-charon-rust ) || { echo "charon build FAILED"; exit 1; }

mark "5/6 GNU make"
if command -v gmake >/dev/null; then
  MAKE_BIN=gmake
elif make --version 2>/dev/null | grep -q "GNU Make"; then
  MAKE_BIN=make
elif command -v brew >/dev/null; then
  brew install make && MAKE_BIN=gmake
else
  echo "GNU make not found (need gmake or a GNU make named make)"; exit 1
fi
echo "using: $MAKE_BIN ($("$MAKE_BIN" --version | head -1))"

mark "6/6 build aeneas"
"$MAKE_BIN" check-charon || { echo "check-charon FAILED"; exit 1; }
"$MAKE_BIN" build        || { echo "aeneas build FAILED"; exit 1; }

mark "DONE"
ls -la "$AENEAS/bin/aeneas" && echo "aeneas built OK"
echo "charon: $AENEAS/charon/bin/charon"
echo "opam switch: $SWITCH  (use: eval \"\$(opam env --switch=$SWITCH)\")"
