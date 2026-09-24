#!/usr/bin/env bash
# Build the project and print the axioms behind the final theorem.
# Fails if the build fails, or if any axiom beyond the standard three is used
# (sorryAx counts as a failure; it is expected until L1, L2 and L3 are proved).
set -euo pipefail
cd "$(dirname "$0")/.."

lake build
out=$(lake env lean scripts/Axioms.lean)
echo "$out"

line=$(echo "$out" | grep "'A060841.conjecture1' depends on axioms:" || true)
if [ -z "$line" ]; then
  echo "FAIL: no axiom report for A060841.conjecture1" >&2
  exit 1
fi
extra=$(echo "$line" | sed 's/.*\[\(.*\)\].*/\1/' | tr ',' '\n' | tr -d ' ' \
  | grep -vxE 'propext|Classical\.choice|Quot\.sound' || true)
if [ -n "$extra" ]; then
  echo "FAIL: non-standard axioms: $(echo $extra)" >&2
  exit 1
fi
echo "OK: only standard axioms"
