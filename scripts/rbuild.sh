#!/usr/bin/env bash
# rbuild.sh — run Lean builds of this project on the remote build box
# (the Pro, over Tailscale), keeping its tree in sync with this one.
#
# The remote holds its own .lake (seeded once from this machine, same
# toolchain + same /Users/kirancodes paths so traces validate); syncs never
# touch it, so local `lake env lean` work and remote full builds can't race.
#
# Usage:
#   scripts/rbuild.sh                    # sync + `lake build` (all cores)
#   scripts/rbuild.sh check              # sync + lake build + check_all.sh --skip-build
#   scripts/rbuild.sh files F1 [F2...]   # sync + parallel `lake env lean` per file
#   scripts/rbuild.sh sh <cmd...>        # sync + arbitrary command in project root
#   scripts/rbuild.sh sync               # sync only
#   scripts/rbuild.sh cove [cmd...]      # sync + run cmd (default `lake build`) in a
#                                        #   NEW window of the Pro's cove-kitty — the
#                                        #   cove-relay streams it back and it appears
#                                        #   in the local Cove as a ◈ remote termling
#
# Env knobs: RBUILD_HOST (default kirans-macbook-pro),
#            RBUILD_JOBS (parallel width for `files` mode, default 10).

set -uo pipefail
cd "$(dirname "$0")/.." || exit 2

# Prefer the LAN path (same Wi-Fi → tens of MB/s); fall back to the tailnet
# name, which may ride a DERP relay (~0.3 MB/s measured).
if [ -z "${RBUILD_HOST:-}" ]; then
  if ping -c1 -t2 Kirans-MacBook-Pro.local >/dev/null 2>&1; then
    RBUILD_HOST=Kirans-MacBook-Pro.local
  else
    RBUILD_HOST=kirans-macbook-pro
  fi
fi
HOST="$RBUILD_HOST"
JOBS="${RBUILD_JOBS:-10}"
RDIR="Documents/code/verified-semantic-abstraction"
# Non-interactive ssh gets no brew/elan PATH — set it explicitly. The
# caffeinate (keyed to the remote shell's lifetime) stops the Pro sleeping
# mid-build; the initial seed died to exactly that.
RENV='export PATH="$HOME/.elan/bin:/opt/homebrew/bin:$PATH"; (caffeinate -ims -w $$ &)'

fail() { echo "rbuild: FAIL: $*" >&2; exit 1; }

sync_tree() {
  echo "== rbuild: sync -> $HOST"
  # .lake and .git stay remote-owned; --delete keeps the trees mirrored.
  rsync -az --delete \
    --exclude '.lake' --exclude '.git' \
    ./ "$HOST:$RDIR/" || fail "rsync"
}

remote() { ssh "$HOST" "$RENV; cd $RDIR || exit 2; $*"; }

MODE="${1:-build}"
case "$MODE" in
  sync)
    sync_tree ;;
  build)
    sync_tree
    remote "lake build" || fail "remote lake build" ;;
  check)
    sync_tree
    remote "lake build" || fail "remote lake build"
    remote "bash scripts/check_all.sh --skip-build" || fail "remote check_all" ;;
  files)
    shift; [ $# -gt 0 ] || fail "files mode needs at least one .lean path"
    sync_tree
    printf '%s\n' "$@" | remote "xargs -P $JOBS -I% sh -c 'log=/tmp/rbuild.\$(echo % | tr / _).log; lake env lean % >\"\$log\" 2>&1 && echo \"OK   %\" || { echo \"FAIL %\"; cat \"\$log\"; }' | sort" \
      || fail "remote file check" ;;
  sh)
    shift; [ $# -gt 0 ] || fail "sh mode needs a command"
    sync_tree
    remote "$@" ;;
  cove)
    shift; CMD="${*:-lake build}"
    sync_tree
    # Launch in the Pro's cove-kitty; its cove-relay publishes the window to
    # wwid and the local cove-remote-auto mirrors it back as a ◈ shadow.
    ssh "$HOST" "/Applications/kitty.app/Contents/MacOS/kitten @ --to unix:/tmp/cove-kitty launch --type=os-window --title rbuild --cwd \"\$HOME/$RDIR\" /bin/zsh -c '$RENV; time ($CMD) 2>&1 | tee /tmp/rbuild-cove.log; exec /bin/zsh -i'" \
      || fail "cove launch — is cove-kitty running on $HOST?"
    echo "rbuild: launched on the Pro's cove — look for the ◈ rbuild shadow termling" ;;
  -h|--help)
    sed -n '2,18p' "$0" ;;
  *)
    fail "unknown mode '$MODE' (build|check|files|sh|sync)" ;;
esac
