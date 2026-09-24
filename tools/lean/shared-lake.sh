#!/usr/bin/env bash
# Share one prebuilt dependency tree (Mathlib, formal-conjectures, ...) between worktrees and
# between problems. Run from a problem's Lean project root (problems/<id>/lean); each project's
# scripts/shared-lake.sh does that.
#
#   shared-lake.sh [link]   point .lake/packages at the shared tree for this pin, building and
#                           publishing it first if it does not exist yet
#   shared-lake.sh unlink   replace the link with a private copy (APFS clone, cheap)
#   shared-lake.sh status   show what .lake/packages is and where the shared tree is
#
# The shared tree lives at $BT_LAKE_SHARED/<pin> (default ~/.cache/breakthroughs-lake), where
# <pin> hashes lake-manifest.json (minus the root package's own name) and lean-toolchain, so
# problems pinned to the same formal-conjectures commit share one tree, and a pin bump gets a
# fresh one. The upstream module a project needs is the `FormalConjectures.*` import of its
# Main.lean. If the tree lacks it but has everything it imports, that one module is built into
# the tree (seconds); nothing else in the tree is ever rebuilt.
#
# The tree is made read-only once published: builds only read it, so any number of worktrees can
# use it at once, and anything that tries to write into it (a rebuild, `lake update`) fails loudly
# instead of corrupting it for everyone. Each worktree still builds its own modules in its own
# .lake/build. Sharing one copy also lets the OS page cache hold one copy of the Mathlib .olean
# files for all provers instead of one per worktree.
#
# If publishing fails, the worktree is left with a normal private build (the fallback).
set -euo pipefail
[ -f lakefile.toml ] && [ -f lake-manifest.json ] \
  || { echo "shared-lake: run from a problem's lean/ directory (no lakefile.toml here)" >&2; exit 2; }

root="${BT_LAKE_SHARED:-$HOME/.cache/breakthroughs-lake}"
# The root package's name (the one line indented by a single space) differs per problem but does
# not affect the dependency tree, so it is left out of the pin.
pin=$({ grep -v '^ "name":' lake-manifest.json; cat lean-toolchain; } | shasum -a 256 | cut -c1-16)
shared="$root/$pin"
local_pkgs=".lake/packages"
upstream_mod=$(sed -n 's/^import \(FormalConjectures\..*\)$/\1/p' ./*/Main.lean | head -1)
[ -n "$upstream_mod" ] \
  || { echo "shared-lake: no 'import FormalConjectures.…' line in */Main.lean" >&2; exit 2; }

log() { echo "shared-lake: $*" >&2; }

# Build the dependencies privately: the normal path, and the fallback.
private_build() {
  log "building dependencies privately (Mathlib from cache, never compiled)"
  lake exe cache get
  lake build "$upstream_mod"
}

# mkdir is atomic: exactly one worktree holds $shared.lock at a time.
take_lock() {
  mkdir -p "$root"
  if ! mkdir "$shared.lock" 2>/dev/null; then
    log "another worktree is writing $shared; waiting (if it crashed, remove $shared.lock)"
    until mkdir "$shared.lock" 2>/dev/null; do sleep 5; done
  fi
}

publish() {
  take_lock
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

# Build just $upstream_mod into the linked shared tree, when everything it imports is already
# there. Only formal-conjectures' build directory is made writable, and only meanwhile.
extend() {
  local src imports fc_build rc=0
  src="$local_pkgs/formal_conjectures/$(echo "$upstream_mod" | tr . / | tr -d '«»').lean"
  [ -f "$src" ] || { log "cannot find $src"; return 1; }
  # `+M` names module M alone; a bare name could mean a whole library.
  imports=$(sed -n 's/^\(public \)\{0,1\}import \([^ ]*\).*/+\2/p' "$src")
  # shellcheck disable=SC2086
  lake build --no-build $imports >/dev/null 2>&1 \
    || { log "the shared tree lacks the imports of $upstream_mod"; return 1; }
  take_lock
  if ! lake build --no-build "$upstream_mod" >/dev/null 2>&1; then
    log "building $upstream_mod into $shared"
    fc_build="$shared/packages/formal_conjectures/.lake/build"
    chmod -R u+w "$fc_build"
    lake build "$upstream_mod" || rc=1
    chmod -R a-w "$fc_build"
  fi
  rm -rf "$shared.lock"
  return "$rc"
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
  # Confirm the shared tree is complete for this project without writing to it.
  if ! lake build --no-build "$upstream_mod" >/dev/null 2>&1 \
      && ! { extend && lake build --no-build "$upstream_mod" >/dev/null 2>&1; }; then
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
    echo "needs:  $upstream_mod"
    if [ -L "$local_pkgs" ]; then echo "local:  link -> $(readlink "$local_pkgs")"
    elif [ -d "$local_pkgs" ]; then echo "local:  private copy"
    else echo "local:  missing"; fi
    ;;
  *) echo "usage: $0 [link|unlink|status]" >&2; exit 2 ;;
esac
