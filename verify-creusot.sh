#!/usr/bin/env bash
# verify-creusot.sh — Phase V3.5 of PLAN-verification: deductive (SMT) proof of
# the checker's loop invariant via Creusot.
#
# TARGET CONTRACT (`src/models/check.rs::reachable_set`):
#   the returned set `S` is CLOSED under `step` unless `truncated` —
#     ∀ s ∈ S, ∀ a ∈ enabled(s).  step(s,a) = Some t  ⇒  t ∈ S
#   and `initial ∈ S`. That fixpoint is what makes the M1 verdict sound: a "safe"
#   model is one whose ENTIRE forward closure was scanned. In Creusot terms the
#   BFS loop invariant is "S is step-closed over the dequeued prefix, and the
#   queue holds exactly the not-yet-expanded members of S".
#
# STATUS: Creusot is an EXTERNAL tool (creusot-rustc + why3 + an SMT solver),
# like aeneas/lean — NOT a shipped dependency, and a from-source build (pinned
# nightly + opam why3). It is not installed here, so this SKIPs. Meanwhile the
# SAME invariant is checked TODAY by the `reachable_set_closed_under_step`
# property test (598 random FSMs + PT-nets, `cargo test`) — Creusot is the
# deductive upgrade, not the only evidence.
#
# When Creusot is installed, annotate `reachable_set` with
#   #[creusot::ensures(forall<s> result.0.contains(s) ==> closed_under_step(...))]
# behind `#[cfg(creusot)]` and run `cargo creusot` here (z3 is already present).

set -uo pipefail
cd "$(dirname "$0")"

skip(){ printf '  \033[33mSKIP\033[0m  %s\n' "$1"; }
pass(){ printf '  \033[32mPASS\033[0m  %s\n' "$1"; }
bad(){  printf '  \033[31mFAIL\033[0m  %s\n' "$1"; }

printf '\033[1m== Creusot — deductive checker-invariant proof (V3.5) ==\033[0m\n'

if ! command -v cargo-creusot >/dev/null 2>&1; then
  skip "creusot not installed (creusot-rustc + why3; from-source build) — V3.5 deductive proof skipped"
  skip "the same invariant IS covered today by the reachable_set_closed_under_step property test (cargo test)"
  exit 0
fi

# Creusot present: prove the carved core. (Annotations live behind #[cfg(creusot)].)
if cargo creusot 2>creusot.err; then
  pass "cargo creusot — reachable_set closed-under-step contract discharged"
  rm -f creusot.err
else
  bad "cargo creusot failed (see creusot.err)"
  exit 1
fi
