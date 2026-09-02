#!/bin/zsh
# fleet_run.sh <batch-id> [model] — run ONE field-discharge batch in a COW clone
# via a single sequential opencode worker. Run batches ONE AT A TIME (opencode
# misbehaves in parallel); the coordinator harvests + wires + gates afterwards.
#
#   scripts/fleet_run.sh B1-leaves
#   scripts/fleet_run.sh B5-execarms 'openrouter/~z-ai/glm-latest'
#
# Harvest afterwards from $CLONE/Vsa/Sim/rows/Field_*.lean and
# $CLONE/experiments/logs/fleet-$BATCH.md. NEVER rm the clone before harvest.
set -euo pipefail
BATCH="$1"
MODEL="${2:-openrouter/~z-ai/glm-latest}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BRIEF="$ROOT/experiments/fleet/briefs/$BATCH.md"
CLONE="/tmp/vsa-fleet-$BATCH"

[[ -f "$BRIEF" ]] || { echo "no brief: $BRIEF (run scripts/fleet_briefs.py)"; exit 1; }
[[ -e "$CLONE" ]] && { echo "clone exists: $CLONE (harvest or remove it first)"; exit 1; }

# Guard: the proof ELF must never change, anywhere.
SHA_BEFORE=$(shasum -a 256 "$ROOT/c/while-riscv-htif.elf" | cut -d' ' -f1)

echo "cloning (APFS COW, warm oleans) -> $CLONE"
cp -Rc "$ROOT" "$CLONE"

# Headless opencode auto-rejects "ask" permissions; the global config also
# injects a lean LSP (lake serve = racing builds, Law 5). Override both in the
# throwaway clone only.
cat > "$CLONE/opencode.json" << 'OCEOF'
{
  "$schema": "https://opencode.ai/config.json",
  "permission": { "edit": "allow", "bash": "allow" },
  "lsp": { "lean": { "disabled": true } }
}
OCEOF

echo "launching opencode ($MODEL) on $BATCH — sequential, one lean process"
cd "$CLONE"
opencode run -m "$MODEL" --title "vsa-fleet-$BATCH" "$(cat "$BRIEF")" || true

echo "--- worker done; harvest summary ---"
ls -la "$CLONE"/Vsa/Sim/rows/Field_*.lean 2>/dev/null || echo "(no field files produced)"
[[ -f "$CLONE/experiments/logs/fleet-$BATCH.md" ]] && tail -20 "$CLONE/experiments/logs/fleet-$BATCH.md"

SHA_AFTER=$(shasum -a 256 "$ROOT/c/while-riscv-htif.elf" | cut -d' ' -f1)
[[ "$SHA_BEFORE" == "$SHA_AFTER" ]] || { echo "FATAL: proof ELF changed in main repo!"; exit 2; }
echo "proof ELF unchanged ✓. Clone kept at $CLONE for harvest."
