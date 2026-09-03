#!/usr/bin/env bash
# houdini_summary_remote.sh — run the Houdini summary campaign on the Pro's
# dedicated cores (the Air's are busy with the running agent), reusing the
# local agent's emit if it is up to date.
#
# Emit is a ~10s Lean #eval, deterministic from the reflect olean; Houdini then
# reads the emitted files. So: verify the olean is current, (re)emit only if the
# source changed, ship the campaign to the Pro, run Z3-only Houdini there
# (no Lean rebuild on the Pro), pull the verdicts back.
#
# Gotchas baked in:
#   * reach the Pro by TAILNET IP, not `*.local` — the LAN mDNS name silently
#     hangs every ssh/scp/rsync when the Pro dozes off Wi-Fi.
#   * ship a tar via scp, not rsync — openrsync / tar-over-ssh both flake here.
#   * run z3 4.15.4 (~/bin/z3), not brew's 5.1.0 — 5.1.0 returns `unknown`
#     where 4.15.4 proves `unsat`, and the miner silently drops any clause it
#     can't close, so every verdict comes back UNKNOWN.
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
mt() { stat -f %m "$1" 2>/dev/null || echo 0; }

src=$(printf '%s\n' "$(mt experiments/smt/ReflectResiduals.lean)" "$(mt experiments/smt/ReflectSpan.lean)" | sort -rn | head -1)
[ "$(mt experiments/smt/ReflectResiduals.olean)" -ge "$src" ] || {
  echo "ERROR: reflect olean is STALE vs its sources — rebuild it first:" >&2
  echo "  lake env lean -o experiments/smt/ReflectResiduals.olean experiments/smt/ReflectResiduals.lean" >&2
  exit 1; }

if [ "$(mt "$STAGE/obligations")" -lt "$src" ]; then
  echo "== emit: source newer than staged campaign, re-emitting to $STAGE"
  # `#emit_bmc`, not `#emit_campaign`: the latter is the older DAG emitter and
  # leaves `writes/` EMPTY, which the driver used to read as an empty footprint
  # and therefore a VALID verdict.  60 rounds is what makes all 52 spans complete.
  printf 'import experiments.smt.ReflectResiduals\n#emit_bmc "%s" 60\n' "$STAGE" > /tmp/emit_rc.lean
  LEAN_PATH="$PWD:$(lake env printenv LEAN_PATH 2>/dev/null)" lake env lean /tmp/emit_rc.lean | tail -1
else
  echo "== emit: reusing up-to-date campaign at $STAGE"
fi
echo "== campaign: $(($(wc -l < "$STAGE/summaries.tsv")-1)) summaries, $(ls "$STAGE/queries" | wc -l | tr -d ' ') queries"

echo "== ship campaign ($(du -sh "$STAGE" | cut -f1)) + script to $PRO (tar via scp)"
tar czf /tmp/bmc-campaign.tgz -C "$STAGE" .
scp -q /tmp/bmc-campaign.tgz "$PRO:/tmp/bmc-campaign.tgz"
scp -q scripts/houdini_summary.py "$PRO:$RDIR/scripts/"
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

echo "== run Houdini on $PRO at -j$JOBS --timeout $TIMEOUT with z3 4.15.4 (${*:-both phases})"
# nohup + setsid on the REMOTE side: a campaign runs for tens of minutes, and a
# foreground ssh hands the job a SIGHUP the moment the link drops (the Pro
# dozing off Wi-Fi is enough).  That is how the previous run died after mining
# without ever writing verdicts.tsv.  Detach it, then poll the log.
ssh "$PRO" "cd $RDIR && rm -f /tmp/houdini.log /tmp/houdini.done && nohup zsh -lc 'export PATH=\$HOME/bin:\$PATH; z3 --version; time python3 -u scripts/houdini_summary.py experiments/smt/bmc -j$JOBS --timeout $TIMEOUT ${*:-}; echo \$? > /tmp/houdini.done' > /tmp/houdini.log 2>&1 < /dev/null & sleep 1"
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

ssh "$PRO" "cat $RDIR/experiments/smt/bmc/verdicts.tsv" > /tmp/bmc-remote-verdicts.tsv 2>/dev/null || true
echo "== verdicts → /tmp/bmc-remote-verdicts.tsv"
