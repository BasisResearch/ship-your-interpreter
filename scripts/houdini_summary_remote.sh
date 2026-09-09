#!/usr/bin/env bash
# houdini_summary_remote.sh — run the Houdini summary campaign on the Pro's
# dedicated cores, with a fresh local emission from a checked private backend.
#
# Emit is a ~10s Lean #eval, deterministic from the reflect olean; Houdini then
# reads the emitted files. Rebuild experiment oleans in a private directory,
# emit the campaign, ship it to the Pro, run Z3-only Houdini
# there (no Lean rebuild on the Pro), pull the verdicts back.
#
# Gotchas baked in:
#   * reach the Pro by TAILNET IP, not `*.local` — the LAN mDNS name silently
#     hangs every ssh/scp/rsync when the Pro dozes off Wi-Fi.
#   * ship a tar via scp, not rsync — openrsync / tar-over-ssh both flake here.
#   * run z3 4.15.4 (~/bin/z3), not brew's 5.1.0 — 5.1.0 returns `unknown`
#     where 4.15.4 proves `unsat`, and the miner silently drops any clause it
#     can't close, so every verdict comes back UNKNOWN.
#   * extra args are passed through to the driver.  To skip mining and re-check
#     verdicts off an existing clauses.json, that is `--phase check` -- a BARE
#     `check` is silently ignored by the arg parser and you get both phases.
#   * -j must not exceed the core count by much: z3 calls are CPU-bound, and a
#     mining check that runs past --timeout wall-clock returns `unknown` and its
#     clause is dropped. ~ncores is the sweet spot, NOT 2x.
set -euo pipefail
cd "$(dirname "$0")/.."
PRO="${PRO_HOST:-100.78.85.47}"          # tailnet IP; NOT Kirans-MacBook-Pro.local
RDIR="Documents/code/verified-semantic-abstraction"
STAGE="${HOUDINI_STAGE:-/tmp/bmc-remote}"
JOBS="${JOBS:-10}"                        # ~= Pro core count; see gotcha above
TIMEOUT="${TIMEOUT:-30}"
Z3_EXPECT="${Z3_EXPECT:-4.15.4}"          # asserted on the Pro before launching

# The legacy transport cannot establish typed-certificate authority or the
# complete source snapshot. Reject that path before remote writes or launch.
refuse_typed_campaign() {
  cat >&2 <<'UNSUPPORTED'
houdini_summary_remote: typed certificate authority transport is unsupported.
Use the local driver with --segment-authority DIR and an independent export
from the fingerprint-checked Lean build. Legacy campaigns remain supported.
UNSUPPORTED
  exit 2
}
has_typed_certificates() {
  [ -f "$STAGE/segment-certificates.tsv" ] &&
    awk 'NR > 1 && NF {found=1} END {exit !found}' "$STAGE/segment-certificates.tsv"
}
for argument in "$@"; do
  case "$argument" in
    --segment-authority|--segment-authority=*) refuse_typed_campaign;;
  esac
done
if has_typed_certificates; then refuse_typed_campaign; fi

[ -n "${VSA_PRIVATE_BUILD:-}" ] || {
  echo "ERROR: VSA_PRIVATE_BUILD must identify the current private Lean build" >&2
  exit 2
}
python3 -B scripts/check_validation.py --backend "$VSA_PRIVATE_BUILD" --verify-backend-only || {
  echo "ERROR: private Lean backend is missing or stale" >&2
  exit 2
}

# Fresh experiment objects cannot inherit stale imports from a previous emit.
LEAN_OUT=$(mktemp -d /tmp/vsa-houdini-emission.XXXXXX)
mkdir -p "$LEAN_OUT/experiments/smt"
relean() {
  echo "== olean: compiling $1 into $LEAN_OUT"
  lake env sh -c 'LEAN_PATH="$1:$2${LEAN_PATH:+:$LEAN_PATH}" lean -o "$3" "$4"' \
    houdini-emission "$VSA_PRIVATE_BUILD" "$LEAN_OUT" \
    "$LEAN_OUT/experiments/smt/$1.olean" "experiments/smt/$1.lean" \
    || { echo "ERROR: experiments/smt/$1.lean does not elaborate" >&2; exit 1; }
}
relean ReflectSpan
relean ReflectResiduals

echo "== emit: fresh campaign at $STAGE"
python3 - "$STAGE" "$LEAN_OUT/Emit.lean" <<'PYTHON'
import json
from pathlib import Path
import sys

Path(sys.argv[2]).write_text(
    "import experiments.smt.ReflectResiduals\n#emit_bmc "
    + json.dumps(sys.argv[1], ensure_ascii=False) + " 60\n"
)
PYTHON
lake env sh -c 'LEAN_PATH="$1:$2${LEAN_PATH:+:$LEAN_PATH}" lean "$3"' \
  houdini-emission "$VSA_PRIVATE_BUILD" "$LEAN_OUT" "$LEAN_OUT/Emit.lean" | tail -1
if has_typed_certificates; then refuse_typed_campaign; fi
echo "== campaign: $(($(wc -l < "$STAGE/summaries.tsv")-1)) summaries, $(ls "$STAGE/queries" | wc -l | tr -d ' ') queries"

echo "== ship campaign ($(du -sh "$STAGE" | cut -f1)) + script to $PRO (tar via scp)"
tar czf /tmp/bmc-campaign.tgz -C "$STAGE" .
scp -q /tmp/bmc-campaign.tgz "$PRO:/tmp/bmc-campaign.tgz"
scp -q scripts/houdini_summary.py scripts/segment_certificates.py scripts/verdict_receipts.py "$PRO:$RDIR/scripts/"
# The driver refuses to answer when the campaign's `src/` provenance copy does
# not match the tree's ReflectSpan/ReflectResiduals -- rightly, since a verdict
# against a different encoder is a verdict about another program.  The Pro's
# checkout is not what we emit from, so ship the two sources it compares
# against, or the guard fires on a difference that is only the Pro being stale.
scp -q experiments/smt/ReflectSpan.lean experiments/smt/ReflectResiduals.lean \
    "$PRO:$RDIR/experiments/smt/"
# REFUSE to clobber a live run.  A campaign takes HOURS, and a `pgrep` that
# comes back empty is not proof it died — one did here, while the job was in
# fact still mining, and the untar below then swapped the queries out from under
# it.  Check for the process itself and stop rather than corrupt the run.
if ssh "$PRO" "pgrep -f houdini_summary.py > /dev/null" 2>/dev/null; then
  echo "ERROR: a Houdini campaign is ALREADY RUNNING on $PRO." >&2
  echo "  Watch it:  ssh $PRO 'tail -f /tmp/houdini.log'" >&2
  echo "  Or kill it: ssh $PRO 'pkill -f houdini_summary.py; pkill -x z3'" >&2
  exit 1
fi
ssh "$PRO" "cd $RDIR && rm -rf experiments/smt/bmc && mkdir -p experiments/smt/bmc && tar xzf /tmp/bmc-campaign.tgz -C experiments/smt/bmc"

# ASSERT the z3 version, do not merely print it.  4.15.4 proves `unsat` where
# 5.1.0 returns `unknown`, and the miner drops every clause it cannot close, so
# the wrong binary on `$PATH` turns the whole campaign into UNKNOWN without one
# error line.  The launch below already echoed `z3 --version` into the log and
# nothing ever read it, which is a record of the failure, not a guard against
# it.  `Z3_EXPECT=` overrides when a run deliberately wants another build.
z3v=$(ssh "$PRO" "zsh -lc 'export PATH=\$HOME/bin:\$PATH; z3 --version'" 2>/dev/null | head -1)
case "$z3v" in
  *"$Z3_EXPECT"*) ;;
  *) echo "ERROR: z3 on $PRO is '${z3v:-<not found>}', expected $Z3_EXPECT." >&2
     echo "  ~/bin/z3 must come first on the Pro's PATH; brew's 5.1.0 answers" >&2
     echo "  'unknown' where 4.15.4 proves 'unsat', and every clause the miner" >&2
     echo "  cannot close is silently dropped, so the run reports UNKNOWN" >&2
     echo "  throughout and looks like a hard campaign.  Set Z3_EXPECT to override." >&2
     exit 1 ;;
esac

echo "== run Houdini on $PRO at -j$JOBS --timeout $TIMEOUT with $z3v (${*:-both phases})"
# nohup + setsid on the REMOTE side: a campaign runs for tens of minutes, and a
# foreground ssh hands the job a SIGHUP the moment the link drops (the Pro
# dozing off Wi-Fi is enough).  That is how the previous run died after mining
# without ever writing verdicts.tsv.  Detach it, then poll the log.
ssh "$PRO" "cd $RDIR && rm -f /tmp/houdini.log /tmp/houdini.done && nohup zsh -lc 'export PATH=\$HOME/bin:\$PATH; z3 --version; time python3 -u scripts/houdini_summary.py experiments/smt/bmc --require-valid -j$JOBS --timeout $TIMEOUT ${*:-}; echo \$? > /tmp/houdini.done' > /tmp/houdini.log 2>&1 < /dev/null & sleep 1"
sleep 5
if ! ssh "$PRO" "pgrep -f houdini_summary.py > /dev/null" 2>/dev/null; then
  echo "ERROR: the remote job did not start. Remote log:" >&2
  ssh "$PRO" "cat /tmp/houdini.log" >&2
  exit 1
fi
echo "== detached and confirmed running; polling (tail /tmp/houdini.log on the Pro to watch)"
while ! ssh -o ConnectTimeout=10 "$PRO" "test -f /tmp/houdini.done" 2>/dev/null; do
  sleep 60
  ssh -o ConnectTimeout=10 "$PRO" "tail -1 /tmp/houdini.log" 2>/dev/null || echo "  (link down, retrying)"
done
ssh "$PRO" "cat /tmp/houdini.log" | tail -20

# READ the exit status.  The launch has always written it (`echo $? >
# /tmp/houdini.done`) and nothing ever read it: the poll loop only tested that
# the file EXISTS, and the pull below hid a missing `verdicts.tsv` behind
# `2>/dev/null || true`.  A campaign that died mid-check therefore printed
# "verdicts → ..." over an empty file and read as a completed run.
rc=$(ssh "$PRO" "cat /tmp/houdini.done" 2>/dev/null | tr -cd '0-9')
[ -n "$rc" ] || { echo "ERROR: $PRO recorded no exit status for this run." >&2; exit 1; }
if [ "$rc" -ne 0 ]; then
  echo "ERROR: houdini_summary.py exited $rc on $PRO (log above); no verdicts pulled." >&2
  echo "  Full log: ssh $PRO 'cat /tmp/houdini.log'" >&2
  exit "$rc"
fi

ssh "$PRO" "cat $RDIR/experiments/smt/bmc/verdicts.tsv" > /tmp/bmc-remote-verdicts.tsv \
  || { echo "ERROR: the run exited 0 but left no verdicts.tsv on $PRO." >&2; exit 1; }
[ -s /tmp/bmc-remote-verdicts.tsv ] \
  || { echo "ERROR: verdicts.tsv on $PRO is empty." >&2; exit 1; }
echo "== verdicts ($(($(wc -l < /tmp/bmc-remote-verdicts.tsv) - 1)) fields) → /tmp/bmc-remote-verdicts.tsv"
