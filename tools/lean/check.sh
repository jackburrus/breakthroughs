#!/usr/bin/env bash
# Build a problem's Lean project and print the axioms behind its final theorem.
# Run from the project root (problems/<id>/lean); each project's scripts/check.sh does that.
# The theorem is the one named by `#print axioms` in the project's scripts/Axioms.lean.
# Fails if the build fails, or if any axiom beyond the standard three is used
# (sorryAx counts as a failure; it is expected until every lemma is proved).
#
# Main.lean loads all of Mathlib (~3.3 GB resident, ~80 s here), so this takes a machine-wide
# lock: parallel provers, in any project, queue their full checks instead of thrashing memory.
set -euo pipefail
[ -f lakefile.toml ] && [ -f scripts/Axioms.lean ] \
  || { echo "check: run from a problem's lean/ directory (no lakefile.toml or scripts/Axioms.lean)" >&2; exit 2; }

lock="${BT_LAKE_SHARED:-$HOME/.cache/breakthroughs-lake}/check.lock"
if [ -z "${BT_CHECK_LOCKED:-}" ] && command -v lockf >/dev/null; then
  mkdir -p "$(dirname "$lock")"
  BT_CHECK_LOCKED=1 exec lockf -k "$lock" "$0" "$@"
fi
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"

thm=$(sed -n 's/^#print axioms \([^ ]*\).*/\1/p' scripts/Axioms.lean | head -1)
[ -n "$thm" ] || { echo "FAIL: no '#print axioms' line in scripts/Axioms.lean" >&2; exit 1; }

lake build
out=$(lake env lean scripts/Axioms.lean)
echo "$out"

line=$(echo "$out" | grep "'$thm' depends on axioms:" || true)
if [ -z "$line" ]; then
  echo "FAIL: no axiom report for $thm" >&2
  exit 1
fi
extra=$(echo "$line" | sed 's/.*\[\(.*\)\].*/\1/' | tr ',' '\n' | tr -d ' ' \
  | grep -vxE 'propext|Classical\.choice|Quot\.sound' || true)
if [ -n "$extra" ]; then
  echo "FAIL: non-standard axioms: $(echo $extra)" >&2
  exit 1
fi
echo "OK: only standard axioms"
