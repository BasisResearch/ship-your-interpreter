#!/usr/bin/env bash
# Run only with exclusive compiler access. Objects remain outside the repository.
set -euo pipefail

draft_dir="$(cd "$(dirname "$0")" && pwd)"
repo_dir="$(cd "$draft_dir/../../.." && pwd)"
backend_dir="${1:-/private/tmp/vsa-full-build.sQd0gM}"
cd "$repo_dir"
python3 -B -c 'from pathlib import Path; import sys; from scripts.check_validation import verify_backend; verify_backend(Path.cwd(), Path(sys.argv[1]))' "$backend_dir"

output_dir="$(mktemp -d /private/tmp/vsa-env-get-frame.XXXXXX)"
printf 'Proof-check directory: %s\n' "$output_dir"
mkdir "$output_dir/source" "$output_dir/objects" "$output_dir/logs" "$output_dir/audits"
cp "$draft_dir"/*.lean "$output_dir/source/"
cp "$draft_dir/axioms.json" "$output_dir/source/axioms.json"
cp "$backend_dir/build-private-manifest.json" "$output_dir/backend-manifest.json"
shasum -a 256 "$output_dir/source"/*.lean "$output_dir/source/axioms.json" > "$output_dir/sources.sha256"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$output_dir/started.txt"

modules=(
  SharedReadGeometry
  EnvGetSegments EnvGetCallFrame EnvGetCompareFrame EnvGetScanCompare
  EnvGetScanState EnvGetScanBranch EnvGetScanDecision EnvGetScanAdvance
  EnvGetScanLoop EnvGetScanOutcome EnvGetParentBranch EnvGetCountHead
  EnvGetScanStart EnvGetFrameScan EnvGetOwnedNames EnvGetOwnedFrameState
  EnvGetFrameParent EnvGetLookupData EnvGetLookupTransport EnvGetLookupLoop EnvGetFootprint
  TransportEnv_getRange EnvGetPrologueData EnvGetPrologueFramed EnvGetLookupEntry
  EnvGetLookupSource EnvGetCopyLog EnvGetRestore EnvGetCopyData
  EnvGetCopyFramed
  EnvGetHitTail EnvGetHitGeometry
  EnvGetOutputTransport EnvGetLookupReturn
  EvalVarCallFrame EvalVarLookupEntry
  EvalVarTailShape EvalVarTailFacts EvalVarTailData EvalVarTailFramed
  EvalVarLookupTail
  EvalVarReturn EvalVarArm
  ArmEntryRetained
  FixedImage_Env_get EnvGetEntryTransport StoreRuntimeData EnvGetRuntimeData
  EvalVarEntryReturn EvalVarProduct RuntimeEntryCore EvalRuntimeEntry
  SharedGeometryBoundary
)
python3 -B -c 'from pathlib import Path; import json, sys; expected = json.loads(Path(sys.argv[1]).read_text()); sys.exit(0 if set(expected) == set(sys.argv[2:]) else "Axiom manifest does not match the checked modules")' \
  "$output_dir/source/axioms.json" "${modules[@]}"
for module in "${modules[@]}"; do
  printf 'Checking %s\n' "$module"
  started="$SECONDS"
  status=0
  lake env sh -c 'LEAN_PATH="$1:$2${LEAN_PATH:+:$LEAN_PATH}" exec lean -R "$3" -o "$1/$4.olean" "$3/$4.lean"' \
    env-get-frame-check "$output_dir/objects" "$backend_dir" "$output_dir/source" "$module" \
    > "$output_dir/logs/$module.log" 2>&1 || status=$?
  printf '%s\t%s\t%s\n' "$module" "$status" "$((SECONDS - started))" >> "$output_dir/checks.tsv"
  if [ "$status" -ne 0 ]; then
    cat "$output_dir/logs/$module.log"
    exit "$status"
  fi
  python3 -B -c 'from pathlib import Path; import json, sys; from scripts.proof_slice import audit_axioms; expected = json.loads(Path(sys.argv[1]).read_text()); report = audit_axioms(Path(sys.argv[2]).read_text(), expected[sys.argv[3]]); Path(sys.argv[4]).write_text(json.dumps(report, indent=2) + "\n")' \
    "$output_dir/source/axioms.json" "$output_dir/logs/$module.log" "$module" "$output_dir/audits/$module.json"
done

cmp "$output_dir/backend-manifest.json" "$backend_dir/build-private-manifest.json"
python3 -B -c 'from pathlib import Path; import sys; from scripts.check_validation import verify_backend; verify_backend(Path.cwd(), Path(sys.argv[1]))' "$backend_dir"
shasum -a 256 -c "$output_dir/sources.sha256"
shasum -a 256 "$output_dir/objects"/*.olean "$output_dir/logs"/*.log "$output_dir/audits"/*.json > "$output_dir/artifacts.sha256"
date -u '+%Y-%m-%dT%H:%M:%SZ' > "$output_dir/finished.txt"
printf '%s\n' 'Compilation and exact axiom audits passed.'
