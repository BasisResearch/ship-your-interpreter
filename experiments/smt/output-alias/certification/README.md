# Output-alias execution certificates

To check the existing repository proofs, run from the repository root:

```sh
python3 scripts/build_private.py \
  --output-root /private/tmp/vsa-full-build.sQd0gM \
  --include-executable --resume
```

This full-source build is authoritative. Regeneration is unnecessary for checking
the landed Lean sources. The remaining instructions reproduce their generation
and packaging into a checkout.

These scripts regenerate the concrete execution proof from untrusted trace rows.
The resulting modules prove a complete dense-memory execution, including the
actual HTIF halt with output `"\n\n"` and exit zero. The source program produces
`"\n"`. `OutputAliasRefutation.lean` composes these facts with the closed `Loaded`
witness under `BeforeAstOwnership.interpRunLayout`. Its `RemainingWork` conclusion
is `RemainingWork BeforeAstOwnership.interpRunLayout → False`;
`RemainingWork` is a type, not a proposition.

Before the ownership migration, these proofs passed the 1,403-module repository build and
a separate type/axiom audit with only `propext`, `Classical.choice`, and
`Quot.sound`. The recorded evidence is in `verification/receipt.json` and
`verification/axioms.log`. These archived source hashes precede the migration.
The new ownership boundary excludes this snapshot. Regeneration requires the
final full-source gate below.

## Paths and prerequisites

Run from the repository root with its pinned Lean toolchain and Python 3.12+.
Keep the sources fixed throughout the run. Run Lean builds serially.
The command sequence writes regenerated proof modules into the checkout.
Choose a fresh artifact directory outside the checkout:

```sh
set -eu
export VSA_ALIAS_REPO="$PWD"
export VSA_ALIAS_ARTIFACTS="$(mktemp -d /private/tmp/vsa-alias-certification.XXXXXX)"
export VSA_ALIAS_SCRIPTS="$VSA_ALIAS_REPO/experiments/smt/output-alias/certification"
export VSA_ALIAS_REPLAY="$VSA_ALIAS_REPO/experiments/smt/output-alias/snapshot-replay"
export VSA_ALIAS_DEPS="/private/tmp/vsa-full-build.sQd0gM"
export VSA_ALIAS_CERTS="$VSA_ALIAS_ARTIFACTS/certificates"
export VSA_ALIAS_COMPOSITION="$VSA_ALIAS_ARTIFACTS/composition"
```

`build_certificates.py` and `package_composition.py` are the portable scratch
builder and composition packager distributed beside this README. The retained
build root must pass its current source/dependency fingerprint checks.

## Generate the inputs and unit sources

Refresh the retained dependency tree with `--resume`. The driver checks recursive
source and toolchain fingerprints. Preserve this cache; use a different build
root only when the cache is missing/corrupt or a separate cold audit is approved.

```sh
python3 scripts/build_private.py --output-root "$VSA_ALIAS_DEPS" --include-executable --resume \
  > "$VSA_ALIAS_ARTIFACTS/dependencies.log" 2>&1

lake env sh -c 'LEAN_PATH="$VSA_ALIAS_DEPS${LEAN_PATH:+:$LEAN_PATH}" lean --run "$VSA_ALIAS_REPLAY/FullTrace.lean" 20000 --trace' \
  > "$VSA_ALIAS_ARTIFACTS/trace.jsonl" \
  2> "$VSA_ALIAS_ARTIFACTS/trace.stderr"

python3 "$VSA_ALIAS_REPLAY/partition_trace.py" \
  --repo "$VSA_ALIAS_REPO" \
  --trace "$VSA_ALIAS_ARTIFACTS/trace.jsonl" \
  --output "$VSA_ALIAS_ARTIFACTS/partition.json"

python3 "$VSA_ALIAS_SCRIPTS/generate_certificates.py" \
  --partition "$VSA_ALIAS_ARTIFACTS/partition.json" \
  --trace "$VSA_ALIAS_ARTIFACTS/trace.jsonl" \
  --output "$VSA_ALIAS_CERTS"
```

The default selection is units 001–285, plus common Data. Unit 000 is supplied
by `OutputAliasPrefix`. The trace has 1,861 instruction rows. Sparse replay only
supplies candidate data; the generated proofs check the dense `snapshotMem`
using `snapshot_lookup` and exact write logs.

Store entries use the full source GPR value. The generator checks that masking
it to the actual store width matches the recorded value. This matters for four
`SW` writes of `0xffffffff` whose source register is `0xffffffffffffffff`.
The segment subdivision limits, instruction-kind normalization, and bounded
new-write comparisons preserve Lean's default proof limits.

## Compile every unit and create the scratch manifest

The portable builder produces the manifest consumed by the packager. It requires
an explicit backend directory already built or refreshed from current sources.
The fresh artifact directory above contains no stale scratch records.
Compilation must finish before packaging starts.

```sh
lake env python3 "$VSA_ALIAS_SCRIPTS/build_certificates.py" \
  --certificates "$VSA_ALIAS_CERTS" --backend "$VSA_ALIAS_DEPS" \
  > "$VSA_ALIAS_ARTIFACTS/unit-build.log" 2>&1

python3 "$VSA_ALIAS_SCRIPTS/package_certificates.py" \
  --repo "$VSA_ALIAS_REPO" \
  --scratch "$VSA_ALIAS_CERTS" \
  --receipt "$VSA_ALIAS_ARTIFACTS/package-receipt.json"
```

The builder defaults to Data followed by units 001–285. A record is written only
after exit-zero compilation without `sorryAx`; a failed compilation removes its
record. Matching source/Data fingerprints plus an existing object permit reuse.
That reuse does not check backend import fingerprints. After a backend change,
use a fresh certificate output directory for an independent scratch campaign.

The packager requires all 285 unit records and Data, matching source fingerprints,
nonempty compiled objects, and compiler logs. It rejects prohibited proof tokens
and unexpected axioms. Data is copied unchanged. Every unit body, including
internal subproofs and axiom reports, is preserved byte-for-byte. Imports are
merged into `Vsa.Sim.OutputAliasRun.Data` and `Part00`–`Part14`, twenty units per
part except the final five. Part headers include a justified R7 discipline
exception: the counted existentials are independent reached-state endpoints
whose posts use named `TraceHolds` fields, not anonymous representation towers.

## Compose and run the authoritative integration gate

```sh
python3 "$VSA_ALIAS_SCRIPTS/compose_trace.py" \
  --certificates "$VSA_ALIAS_CERTS" \
  --refutation "$VSA_ALIAS_SCRIPTS/TraceRefutation.lean" \
  --output "$VSA_ALIAS_COMPOSITION" \
  --group-size 15 --packaged-imports

python3 "$VSA_ALIAS_SCRIPTS/package_composition.py" \
  --composition "$VSA_ALIAS_COMPOSITION" \
  --repo "$VSA_ALIAS_REPO"

python3 scripts/build_private.py --output-root "$VSA_ALIAS_DEPS" --include-executable --resume \
  > "$VSA_ALIAS_ARTIFACTS/full-integration.log" 2>&1
```

Composition produces nineteen bounded groups, the complete run, and the
refutation. The packager consolidates these into `OutputAliasRun/Groups.lean`,
`OutputAliasRun.lean`, and `OutputAliasRefutation.lean`. The Groups header receives
the same justified R7 exception. Apart from that comment, consolidation reproduces
the original three output modules exactly.
All theorem bodies are preserved. The packager does not certify the sources itself.

The final build discovers every current `Vsa` module, including the packaged
proofs and their actual imports. Its recursive source/toolchain fingerprints,
exit-zero compilation, and compiler axiom reports are the integration evidence.
A failed or interrupted gate leaves integration incomplete. Inspect
`full-integration.log`, the private `logs/` directory, and
`build-private-manifest.json`; do not infer success from artifact existence.

## Receipts and trust boundaries

- `verification/receipt.json` records the completed repository integration and
  seven final theorem type/axiom checks. The directory includes the complete
  retained manifest and build log. Its result refutes the historical physical
  boundary. The proof-closure goal remains incomplete.
- `generator-roundtrip.json` records the archived comparison: Data and all 285
  generated unit files matched the campaign sources byte-for-byte.
- `package-receipt.json` records every source/log hash, the scratch manifest hash,
  package hashes, imports, preserved body hashes, and explicit wrapper/header changes.
- `composition/generation-manifest.json` records the composer inputs and outputs.
- `composition/package-composition-receipt.json` records the consolidation inputs
  and three output hashes, distinguishing the Groups header comment from preserved
  proof bodies. Its status remains `packaged_unchecked`.

The scratch fingerprint is exactly
`sha256(source_bytes + sha256(Data_source_bytes).hexdigest().encode())`.
It **does not fingerprint imported backend modules**. A scratch PASS record is
therefore insufficient to establish current repository proof validity.
Archived hashes establish identity with recorded artifacts, not independent
correctness. The final retained full-source build checks the current package
against its actual dependencies. The proof uses no sparse-to-dense simulation
assumption and does not trust the replay as a machine-semantic premise.
