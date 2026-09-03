#!/usr/bin/env bash
# cove_peers.sh — list the Pro's cove-kitty termlings (id, title, cwd).
set -uo pipefail
HOST="${RBUILD_HOST:-Kirans-MacBook-Pro.local}"
KITTEN="/Applications/kitty.app/Contents/MacOS/kitten"
ssh "$HOST" "$KITTEN @ --to unix:/tmp/cove-kitty ls" | python3 -c '
import json,sys
for w in json.load(sys.stdin):
  for t in w.get("tabs",[]):
    for win in t.get("windows",[]):
      print(win["id"], "\t", win.get("title",""), "\t", (win.get("cwd") or ""))
'
