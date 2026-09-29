#!/usr/bin/env bash
# Dead-theorem gate for the [IRIS] lane.
#
# A theorem with no consumers gets no pressure from use: nothing ever tries to
# instantiate it, so an unsatisfiable premise never surfaces — it type-checks, is
# sorry-free, prints a clean axiom set, and proves nothing. Three adequacy
# theorems sat in exactly that state (see docs/TODO-concurrency.md, 2026-09-30).
#
# Rule: every theorem named in CiAxioms.lean's `#print axioms` list must either
#   (a) have at least one consumer in a .lean file (a use other than its own
#       declaration, the audit files, comments and docstrings), or
#   (b) carry a `headline:` tag on its CiAxioms line naming the theorem or example
#       that instantiates it (or arguing its satisfiability), e.g.
#         #print axioms Foo.bar   -- headline: instantiated by Foo.bar_example
#
# Exit 1 if any marquee theorem has zero consumers and no headline tag.
set -u
cd "$(dirname "$0")"
fail=0
while IFS= read -r line; do
  name=$(sed -E 's/^#print axioms +([^ ]+).*/\1/' <<<"$line")
  short=${name##*.}
  if grep -qE -- '--.*headline:' <<<"$line"; then continue; fi
  # consumers: uses of the short name in .lean sources, excluding the audit files,
  # its own declaration, and comment/docstring lines
  n=$(grep -rn --include='*.lean' -E "\b${short}\b" LeanliftIris \
        | grep -vE "^[^:]+:[0-9]+:\s*(theorem|lemma|def|instance|abbrev) +${short}\b" \
        | grep -vE "^[^:]+:[0-9]+:\s*(--|/-|\*|[A-Za-z\`].*\`${short}\`)" \
        | grep -v "PhaseA/Axioms.lean" \
        | grep -cE "\b${short}\b" || true)
  if [ "${n:-0}" -eq 0 ]; then
    echo "NO CONSUMERS: $name  (mark '-- headline: <instantiated by ...>' or add a use)"
    fail=1
  fi
done < <(grep -E '^#print axioms' CiAxioms.lean)
exit $fail
