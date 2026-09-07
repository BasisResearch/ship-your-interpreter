"""Bind completed Houdini runs to their inputs; receipts are not proof certificates.

A receipt records completion even when individual checks are UNKNOWN or REFUTED.
Consumers must still interpret each verdict and its assumptions. Hashes detect
stale artifacts, not malicious replacement of both artifacts and their receipt.
"""

from __future__ import annotations

import csv
import json
import os
import tempfile
from dataclasses import dataclass
from pathlib import Path

if __package__:
    from .segment_certificates import sha256, unique_object, validate_sources
else:
    from segment_certificates import sha256, unique_object, validate_sources

SCHEMA = "vsa.houdini-verdict.v1"
ROOT = Path(__file__).resolve().parents[1]
CAMPAIGN_FILES = (
    "pre.smt2",
    "source-provenance.tsv",
    "spans.tsv",
    "summaries.tsv",
    "query-capabilities.tsv",
    "residual-capabilities.tsv",
    "residual-holes.tsv",
    "query-summaries.tsv",
    "summary-deps.tsv",
    "query-effects.tsv",
    "residual-extensions.tsv",
    "functional-callees.tsv",
    "lean-certificates.tsv",
    "segment-certificates.tsv",
    "semantic-helpers.tsv",
    "semantic-helper-certificates.tsv",
    "assumed.tsv",
    "opaque.tsv",
    "clause-drop.tsv",
)
CAMPAIGN_DIRS = ("queries", "obligations", "writes", "certificates", "src")
MINED_FILES = ("clauses.json", "assumed-final.tsv")
META_COLUMNS = {
    "query",
    "residual",
    "instance",
    "capability",
    "assumed_dependencies",
    "opaque_dependencies",
    "unencoded_dimensions",
    "full_contract_status",
}


def receipt_path(verdict: Path) -> Path:
    """Return the sidecar path without changing the verdict suffix.

    >>> receipt_path(Path("verdicts.tsv")).name
    'verdicts.tsv.receipt.json'
    """
    return Path(str(verdict) + ".receipt.json")


def input_hashes(
    campaign: Path,
    pins: Path | None = None,
    authority: Path | None = None,
    *,
    mined: bool = True,
) -> dict[str, str]:
    """Recompute the whole relevant inventory, detecting additions and removals."""
    paths = {campaign / name for name in CAMPAIGN_FILES}
    if mined:
        paths.update(campaign / name for name in MINED_FILES)
    for name in CAMPAIGN_DIRS:
        paths.update((campaign / name).rglob("*"))
    if pins is not None:
        if not pins.is_dir():
            raise ValueError("receipt consistency-pins directory is missing")
        paths.update(pins.rglob("*.smt2"))
    if authority is not None:
        if not authority.is_dir():
            raise ValueError("receipt segment-authority directory is missing")
        paths.update(
            authority / name
            for name in ("segment-authority.json", "source-provenance.tsv")
        )
    paths.update(
        ROOT / "scripts" / name
        for name in (
            "houdini_summary.py",
            "segment_certificates.py",
            "verdict_receipts.py",
        )
    )
    return {
        str(path.absolute()): sha256(path) for path in sorted(paths) if path.is_file()
    }


def atomic_text(path: Path, text: str) -> None:
    """Replace one artifact only after its complete bytes have been written."""
    with tempfile.NamedTemporaryFile(
        mode="w",
        dir=path.parent,
        prefix=path.name + ".",
        delete=False,
    ) as stream:
        temporary = Path(stream.name)
        try:
            stream.write(text)
            stream.close()
            os.replace(temporary, path)
        finally:
            temporary.unlink(missing_ok=True)


@dataclass(frozen=True)
class VerdictRun:
    """A run whose old receipt was invalidated before any validation began."""

    verdict: Path
    campaign: Path
    pins: Path | None
    authority: Path | None
    initial_inputs: dict[str, str]

    @classmethod
    def begin(
        cls,
        verdict: Path,
        campaign: Path,
        pins: Path | None = None,
        authority: Path | None = None,
    ) -> VerdictRun:
        verdict, campaign = verdict.absolute(), campaign.resolve()
        receipt_path(verdict).unlink(missing_ok=True)
        pins = pins.resolve() if pins is not None else None
        authority = authority.resolve() if authority is not None else None
        return cls(
            verdict,
            campaign,
            pins,
            authority,
            input_hashes(campaign, pins, authority, mined=False),
        )

    def inputs(self) -> dict[str, str]:
        return input_hashes(self.campaign, self.pins, self.authority)

    def complete(
        self,
        invocation: dict,
        checks: list[tuple[str, str]],
        checked_inputs: dict[str, str],
    ) -> None:
        """Publish only if static and post-mining inputs still match the run."""
        if (
            self.initial_inputs
            != input_hashes(
                self.campaign,
                self.pins,
                self.authority,
                mined=False,
            )
            or checked_inputs != self.inputs()
        ):
            raise ValueError("Houdini inputs changed during validation")
        required = [
            self.campaign / name
            for name in ("pre.smt2", "clauses.json", "source-provenance.tsv")
        ]
        if any(str(path) not in checked_inputs for path in required):
            raise ValueError("receipt requires pre, clauses, and source provenance")
        data = {
            "schema": SCHEMA,
            "status": "completed",
            "full_contract_status": "NOT-CHECKED",
            "campaign_root": str(self.campaign),
            "consistency_pins_root": str(self.pins) if self.pins else None,
            "segment_authority_root": str(self.authority) if self.authority else None,
            "invocation": invocation,
            "checks": [list(pair) for pair in sorted(set(checks))],
            "verdict": {"path": str(self.verdict), "sha256": sha256(self.verdict)},
            "inputs": checked_inputs,
            "source_provenance_sha256": checked_inputs[str(required[2])],
        }
        atomic_text(receipt_path(self.verdict), json.dumps(data, indent=2) + "\n")


def verify_verdict_receipt(verdict: Path, campaign: Path) -> dict:
    """Verify completion, exact input/output bytes, scope, and current sources.

    Raise ValueError on absent, stale, malformed, or incomplete evidence.
    Individual result validity is deliberately left to the consumer.
    """
    try:
        return _verify_verdict_receipt(verdict.absolute(), campaign.resolve())
    except (OSError, KeyError, TypeError, UnicodeError) as error:
        raise ValueError(f"invalid Houdini verdict receipt: {error}") from error


def _verify_verdict_receipt(verdict: Path, campaign: Path) -> dict:
    data = json.loads(
        receipt_path(verdict).read_text(), object_pairs_hook=unique_object
    )
    if not isinstance(data, dict) or set(data) != {
        "schema",
        "status",
        "full_contract_status",
        "campaign_root",
        "consistency_pins_root",
        "segment_authority_root",
        "invocation",
        "checks",
        "verdict",
        "inputs",
        "source_provenance_sha256",
    }:
        raise ValueError("malformed Houdini verdict receipt")
    if (
        data["schema"] != SCHEMA
        or data["status"] != "completed"
        or data["full_contract_status"] != "NOT-CHECKED"
        or data["campaign_root"] != str(campaign)
        or data["verdict"] != {"path": str(verdict), "sha256": sha256(verdict)}
        or not isinstance(data["invocation"], dict)
        or data["invocation"].get("phase") not in {"both", "check"}
    ):
        raise ValueError("receipt does not bind a completed validation invocation")
    roots = []
    for name in ("consistency_pins_root", "segment_authority_root"):
        value = data[name]
        if value is not None and (
            not isinstance(value, str) or not Path(value).is_absolute()
        ):
            raise ValueError(f"invalid receipt {name}")
        roots.append(Path(value) if value is not None else None)
    current = input_hashes(campaign, *roots)
    if data["inputs"] != current:
        raise ValueError("receipt input inventory or hash mismatch")
    for name in ("pre.smt2", "clauses.json", "source-provenance.tsv"):
        if str(campaign / name) not in current:
            raise ValueError(f"receipt missing required input {name}")
    digest = current[str(campaign / "source-provenance.tsv")]
    if data["source_provenance_sha256"] != digest:
        raise ValueError("receipt provenance hash mismatch")
    validate_sources(campaign, ROOT, "source-provenance.tsv", digest)
    if roots[1] is not None:
        validate_sources(
            roots[1],
            ROOT,
            "source-provenance.tsv",
            sha256(roots[1] / "source-provenance.tsv"),
        )
    with verdict.open(newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        if (
            reader.fieldnames is None
            or not META_COLUMNS <= set(reader.fieldnames)
            or len(reader.fieldnames) != len(set(reader.fieldnames))
        ):
            raise ValueError("receipt verdict has invalid columns")
        rows = list(reader)
    seen = set()
    checks: list[list[str]] = []
    for row in rows:
        if (
            None in row
            or None in row.values()
            or not row["query"]
            or row["query"] in seen
            or row["full_contract_status"] != "NOT-CHECKED"
        ):
            raise ValueError("receipt verdict has invalid or duplicate rows")
        seen.add(row["query"])
        checks.extend(
            [row["query"], name]
            for name, value in row.items()
            if name not in META_COLUMNS and value != "N/A"
        )
    if not checks or data["checks"] != sorted(checks):
        raise ValueError("receipt check scope does not match verdict")
    return data
