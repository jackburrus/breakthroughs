#!/usr/bin/env bash
# Build this project and fail unless its final theorem uses only the standard axioms.
# Details: tools/lean/check.sh (shared by every problem).
cd "$(dirname "$0")/.." && exec ../../../tools/lean/check.sh "$@"
