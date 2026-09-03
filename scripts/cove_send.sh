#!/usr/bin/env bash
# cove_send.sh — drive a remote cove-kitty termling on the Pro (executes there).
# Sends the line, then a SEPARATE carriage return, so the target shell's
# bracketed-paste doesn't swallow the newline.
#
#   scripts/cove_send.sh <match> <cmd...>      # match = id:<n> | title:<t>
#   scripts/cove_send.sh id:2740 'lake build'
#   scripts/cove_send.sh --raw id:2740 $'\x03' # raw bytes, no Enter (e.g. Ctrl-C)
set -uo pipefail
HOST="${RBUILD_HOST:-Kirans-MacBook-Pro.local}"
SOCK="unix:/tmp/cove-kitty"
K="/Applications/kitty.app/Contents/MacOS/kitten @ --to $SOCK"
RAW=""; [ "${1:-}" = "--raw" ] && { RAW=1; shift; }
[ $# -ge 2 ] || { echo "usage: cove_send.sh [--raw] <match> <cmd...>" >&2; exit 2; }
MATCH="$1"; shift
B64=$(printf '%s' "$*" | base64)
ssh "$HOST" "printf '%s' '$B64' | base64 -d | $K send-text --match '$MATCH' --stdin"
[ -n "$RAW" ] || { sleep 0.2; ssh "$HOST" "printf '\r' | $K send-text --match '$MATCH' --stdin"; }
