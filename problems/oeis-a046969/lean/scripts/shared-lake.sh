#!/usr/bin/env bash
# Link this project's .lake/packages to the shared prebuilt dependency tree.
# Usage and details: tools/lean/shared-lake.sh (shared by every problem).
cd "$(dirname "$0")/.." && exec ../../../tools/lean/shared-lake.sh "$@"
