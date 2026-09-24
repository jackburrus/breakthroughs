#!/usr/bin/env bash
# Share one prebuilt dependency tree (Mathlib, formal-conjectures, ...) between worktrees.
#
#   scripts/shared-lake.sh [link]   point .lake/packages at the shared tree for this pin,
#                                   building and publishing it first if it does not exist yet
#   scripts/shared-lake.sh unlink   replace the link with a private copy (APFS clone, cheap)
#   scripts/shared-lake.sh status   show what .lake/packages is and where the shared tree is
#
# The shared tree lives at $BT_LAKE_SHARED/<pin> (default ~/.cache/breakthroughs-lake), where
# <pin> hashes lake-manifest.json and lean-toolchain, so a pin bump gets a fresh tree.
# It is made read-only once published: builds only read it, so any number of worktrees can use
# it at once, and anything that tries to write into it (a rebuild, `lake update`) fails loudly
# instead of corrupting it for everyone. Each worktree still builds its own A060841 modules in
# its own .lake/build. Sharing one copy also lets the OS page cache hold one copy of the
# Mathlib .olean files for all provers instead of one per worktree.
#
# If publishing fails, the worktree is left with a normal private build (the fallback).
set -euo pipefail
cd "$(dirname "$0")/.."

root="${BT_LAKE_SHARED:-$HOME/.cache/breakthroughs-lake}"
pin=$(cat lake-manifest.json lean-toolchain | shasum -a 256 | cut -c1-16)
shared="$root/$pin"
local_pkgs=".lake/packages"
upstream_mod='FormalConjectures.OEIS.«60841»'

log() { echo "shared-lake: $*" >&2; }

# Build the dependencies privately: the normal path, and the fallback.
private_build() {
  log "building dependencies privately (Mathlib from cache, never compiled)"
  lake exe cache get
  lake build "$upstream_mod"
}

publish() {
  mkdir -p "$root"
  # mkdir is atomic: exactly one worktree publishes, the others wait for .ready.
  if ! mkdir "$shared.lock" 2>/dev/null; then
    log "another worktree is publishing $shared; waiting (if it crashed, remove $shared.lock)"
    while [ ! -e "$shared/.ready" ]; do
      [ -d "$shared.lock" ] || { log "publisher gave up; see $shared.lock"; return 1; }
      sleep 5
    done
    return 0
  fi
  if do_publish; then rm -rf "$shared.lock"; else rm -rf "$shared.lock"; return 1; fi
}

do_publish() {
  [ -e "$shared/.ready" ] && return 0
  if [ -L "$local_pkgs" ] || ! lake build --no-build "$upstream_mod" >/dev/null 2>&1; then
    [ -L "$local_pkgs" ] && rm "$local_pkgs"
    private_build || return 1
  fi
  log "publishing $local_pkgs to $shared"
  [ -d "$shared/packages" ] && chmod -R u+w "$shared/packages" && rm -rf "$shared/packages"
  mkdir -p "$shared"
  cp -cR "$local_pkgs" "$shared/packages" 2>/dev/null || cp -R "$local_pkgs" "$shared/packages" \
    || return 1
  chmod -R a-w "$shared/packages"
  touch "$shared/.ready"
}

link() {
  if [ -L "$local_pkgs" ] && [ "$(readlink "$local_pkgs")" = "$shared/packages" ] \
      && [ -e "$shared/.ready" ]; then
    log "already linked to $shared/packages"
  else
    [ -e "$shared/.ready" ] || publish
    mkdir -p .lake
    rm -rf "$local_pkgs"
    ln -s "$shared/packages" "$local_pkgs"
    log "linked $local_pkgs -> $shared/packages"
  fi
  # Confirm the shared tree is complete for this pin without writing to it.
  if ! lake build --no-build "$upstream_mod" >/dev/null 2>&1; then
    log "shared tree is not up to date for this pin; falling back to a private build"
    unlink_shared
    private_build
    return 1
  fi
}

unlink_shared() {
  if [ -L "$local_pkgs" ]; then
    target=$(readlink "$local_pkgs")
    rm "$local_pkgs"
    cp -cR "$target" "$local_pkgs" 2>/dev/null || cp -R "$target" "$local_pkgs"
    chmod -R u+w "$local_pkgs"
    log "replaced link with a private copy of $target"
  else
    log "$local_pkgs is not a link; nothing to do"
  fi
}

case "${1:-link}" in
  link) link ;;
  unlink) unlink_shared ;;
  status)
    echo "pin:    $pin"
    echo "shared: $shared ($([ -e "$shared/.ready" ] && echo ready || echo missing))"
    if [ -L "$local_pkgs" ]; then echo "local:  link -> $(readlink "$local_pkgs")"
    elif [ -d "$local_pkgs" ]; then echo "local:  private copy"
    else echo "local:  missing"; fi
    ;;
  *) echo "usage: $0 [link|unlink|status]" >&2; exit 2 ;;
esac
