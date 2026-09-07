"""Validate emitted segment descriptors before consumers use their frame facts.

Hashes bind artifacts to one emitted source snapshot; they are not signatures.
The explicit authority directory must come from a fingerprint-checked Lean
export, independently of the mutable campaign. Its canonical contracts supply
the theorem/effect binding. Campaign metadata cannot select that authority.
"""

from __future__ import annotations

import csv
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
ABI_GPRS = (2, 3, 4, 8, 9, *range(18, 28))
CERTIFICATE_COLUMNS = (
    "query",
    "field",
    "entry",
    "stop",
    "stop_policy",
    "certificate_path",
    "certificate_sha256",
    "query_sha256",
    "theorem",
)
EFFECT_COLUMNS = (
    "query",
    "field",
    "register_writes",
    "direct_memory_writes",
    "direct_write_rows",
    "output",
    "theorem",
    "provenance",
)
SOURCE_ROOTS = (
    "Vsa",
    "riscv-lean/lean_emulator",
    "riscv-lean/Lean_RV64D_executable",
    "riscv-lean/lean-sail",
    ".lake/packages/ELFSage",
    ".lake/packages/Cli",
)
SOURCE_FILES = (
    "Vsa.lean",
    "experiments/smt/ReflectSpan.lean",
    "experiments/smt/ReflectResiduals.lean",
    "lakefile.toml",
    "lake-manifest.json",
    "lean-toolchain",
    "c/while-riscv-htif.elf",
)


class CertificateError(ValueError):
    """An emitted artifact cannot authorize a frame claim."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CertificateError(message)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_table(
    path: Path, columns: tuple[str, ...] | None = None
) -> list[dict[str, str]]:
    with path.open(newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        if reader.fieldnames is None:
            raise CertificateError(f"{path.name}: missing header")
        if columns is not None:
            require(tuple(reader.fieldnames) == columns, f"{path.name}: wrong columns")
        require(
            len(set(reader.fieldnames)) == len(reader.fieldnames),
            f"{path.name}: duplicate columns",
        )
        rows = list(reader)
    require(
        all(None not in row and None not in row.values() for row in rows),
        f"{path.name}: malformed row",
    )
    return rows


def keyed(rows: list[dict[str, str]], key: str) -> dict[str, dict[str, str]]:
    result = {}
    for row in rows:
        require(key in row and bool(row[key]), f"missing {key}")
        require(row[key] not in result, f"duplicate {key}: {row[key]}")
        result[row[key]] = row
    return result


def exact_keys(value: object, keys: set[str], where: str) -> dict:
    if not isinstance(value, dict) or set(value) != keys:
        raise CertificateError(f"{where}: wrong keys")
    return value


def unique_object(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def checked_digest(value: object, where: str) -> str:
    if not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{64}", value) is None:
        raise CertificateError(f"{where}: invalid digest")
    return value


def identifier(value: object, where: str) -> str:
    if (
        not isinstance(value, str)
        or re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.]*", value) is None
    ):
        raise CertificateError(f"{where}: invalid identifier")
    return value


def pc(value: object, where: str) -> int:
    if not isinstance(value, str) or re.fullmatch(r"0x[0-9a-fA-F]+", value) is None:
        raise CertificateError(f"{where}: invalid PC")
    result = int(value, 16)
    require(result < 2**64 and result % 4 == 0, f"{where}: invalid instruction address")
    return result


@dataclass(frozen=True)
class SegmentCertificate:
    query: str
    field: str
    entry: int
    stop: int
    preserved_gprs: tuple[int, ...]
    theorem: str
    precondition: str
    postcondition: str

    def effect_row(self) -> dict[str, str]:
        """The legacy inventory projection of this checked ABI/empty-write descriptor."""
        return dict(
            zip(
                EFFECT_COLUMNS,
                (
                    self.query,
                    self.field,
                    "preserves-abi",
                    "none",
                    "0",
                    "preserved",
                    self.theorem,
                    f"Lean:{self.theorem}",
                ),
            )
        )

    def matches_effect(self, row: dict) -> bool:
        return all(row.get(key) == value for key, value in self.effect_row().items())


def validate_sources(
    directory: Path, repo_root: Path, manifest: str, digest: str
) -> None:
    require(manifest == "source-provenance.tsv", "unexpected provenance manifest")
    path = directory / manifest
    require(
        sha256(path) == checked_digest(digest, "provenance"),
        "provenance manifest digest mismatch",
    )
    sources = keyed(read_table(path, ("path", "snapshot", "sha256")), "path")
    expected = set(SOURCE_FILES)
    for relative_root in SOURCE_ROOTS:
        root = repo_root / relative_root
        require(root.is_dir(), f"missing source root: {relative_root}")
        for current, directories, files in os.walk(root):
            directories[:] = [
                name for name in directories if name not in {".git", ".lake"}
            ]
            for name in files:
                if name.endswith(".lean") or name in {
                    "lakefile.toml",
                    "lake-manifest.json",
                }:
                    expected.add(
                        (Path(current) / name).relative_to(repo_root).as_posix()
                    )
    require(set(sources) == expected, "source provenance inventory mismatch")
    for relative, row in sources.items():
        require(
            row["snapshot"] == "src-tree/" + relative,
            f"{relative}: unexpected snapshot path",
        )
        expected_hash = checked_digest(row["sha256"], relative)
        require(
            sha256(repo_root / relative) == expected_hash,
            f"{relative}: current source mismatch",
        )
        require(
            sha256(directory / row["snapshot"]) == expected_hash,
            f"{relative}: snapshot mismatch",
        )


def load_segment_certificates(
    directory: str | Path,
    *,
    repo_root: Path = ROOT,
    authority_dir: str | Path | None = None,
) -> dict[str, SegmentCertificate]:
    """Load exact descriptors, or raise without granting any partial authority."""
    directory = Path(directory)
    try:
        return _load_segment_certificates(directory, Path(repo_root), authority_dir)
    except (OSError, UnicodeError, json.JSONDecodeError, KeyError, TypeError) as error:
        raise CertificateError(
            f"invalid segment certificate artifacts: {error}"
        ) from error


def _load_segment_certificates(
    directory: Path, repo_root: Path, authority_dir: str | Path | None
) -> dict[str, SegmentCertificate]:
    manifest_path = directory / "segment-certificates.tsv"
    if not manifest_path.exists():
        return {}
    records = keyed(read_table(manifest_path, CERTIFICATE_COLUMNS), "query")
    if not records:
        return {}
    if authority_dir is None:
        raise CertificateError(
            "typed certificates require an independent segment authority"
        )
    authority_path = Path(authority_dir).resolve()
    campaign_path = directory.resolve()
    require(
        not authority_path.is_relative_to(campaign_path)
        and not campaign_path.is_relative_to(authority_path),
        "segment authority must be separate from the mutable campaign",
    )
    for artifact in ("segment-authority.json", "source-provenance.tsv"):
        require(
            (authority_path / artifact).resolve().is_relative_to(authority_path),
            "authority artifact escapes its trusted directory",
        )
    authority = exact_keys(
        json.loads(
            (authority_path / "segment-authority.json").read_text(),
            object_pairs_hook=unique_object,
        ),
        {"schema", "provenance_manifest", "provenance_sha256", "contracts"},
        "segment authority",
    )
    require(
        authority["schema"] == "vsa.segment-authority.v1",
        "unsupported authority schema",
    )
    validate_sources(
        authority_path,
        repo_root,
        authority["provenance_manifest"],
        authority["provenance_sha256"],
    )
    require(isinstance(authority["contracts"], list), "invalid authority contracts")
    contract_keys = {
        "query",
        "field",
        "entry",
        "stop",
        "stop_policy",
        "effect",
        "theorem",
        "precondition",
        "postcondition",
    }
    authority_contracts = {}
    for item in authority["contracts"]:
        contract = exact_keys(item, contract_keys, "authority contract")
        name = identifier(contract["query"], "authority query")
        require(name not in authority_contracts, f"duplicate authority query: {name}")
        authority_contracts[name] = contract
    capabilities = keyed(read_table(directory / "query-capabilities.tsv"), "query")
    spans = keyed(read_table(directory / "spans.tsv"), "field")
    effects = keyed(
        read_table(directory / "query-effects.tsv", EFFECT_COLUMNS), "query"
    )
    certificates = {}
    checked_provenance = set()
    for query, row in records.items():
        identifier(query, "query")
        require(
            row["certificate_path"] == f"certificates/{query}.json",
            f"{query}: wrong certificate path",
        )
        certificate_path = directory / row["certificate_path"]
        require(
            sha256(certificate_path)
            == checked_digest(row["certificate_sha256"], query),
            f"{query}: certificate digest mismatch",
        )
        raw = exact_keys(
            json.loads(certificate_path.read_text(), object_pairs_hook=unique_object),
            {
                "schema",
                "query",
                "field",
                "entry",
                "stop",
                "stop_policy",
                "effect",
                "theorem",
                "precondition",
                "postcondition",
                "query_sha256",
                "provenance_manifest",
                "provenance_sha256",
            },
            query,
        )
        require(
            raw["schema"] == "vsa.segment-certificate.v1",
            f"{query}: unsupported schema",
        )
        for key in (
            "query",
            "field",
            "entry",
            "stop",
            "stop_policy",
            "query_sha256",
            "theorem",
        ):
            require(raw[key] == row[key], f"{query}: {key} identity mismatch")
        require(
            query in authority_contracts
            and {key: raw[key] for key in contract_keys} == authority_contracts[query],
            f"{query}: contract disagrees with independent Lean authority",
        )
        field = identifier(raw["field"], "field")
        entry, stop = pc(raw["entry"], "entry"), pc(raw["stop"], "stop")
        require(raw["stop_policy"] == "before-pc", f"{query}: unsupported stop policy")
        require(
            query in capabilities and query in spans and query in effects,
            f"{query}: missing identity row",
        )
        span, capability = spans[query], capabilities[query]
        require(
            capability["field"] == field == span["residual"], f"{query}: field mismatch"
        )
        require(
            capability["instance"] == span["instance"], f"{query}: instance mismatch"
        )
        require(
            pc(span["entry"], "span entry") == entry
            and pc(span["stop"], "span stop") == stop,
            f"{query}: span mismatch",
        )
        require(span["ret_exit"] == "false", f"{query}: stop policy mismatch")
        require(
            span["complete"] == "true" and span["summaries"] == "0",
            f"{query}: incomplete or summarized span",
        )
        require(
            sha256(directory / "queries" / f"{query}.smt2")
            == checked_digest(raw["query_sha256"], query),
            f"{query}: query digest mismatch",
        )
        effect = exact_keys(
            raw["effect"], {"registers", "writes", "output_preserved"}, "effect"
        )
        registers = exact_keys(effect["registers"], {"kind", "gprs"}, "registers")
        require(
            registers["kind"] == "abi"
            and isinstance(registers["gprs"], list)
            and all(type(reg) is int for reg in registers["gprs"])
            and tuple(registers["gprs"]) == ABI_GPRS,
            f"{query}: unsupported register footprint",
        )
        require(
            effect["writes"] == [] and effect["output_preserved"] is True,
            f"{query}: unsupported memory/output effect",
        )
        writes = read_table(
            directory / "writes" / f"{query}.tsv", ("guard", "width", "addr")
        )
        require(
            all(item["width"] == "0" for item in writes),
            f"{query}: nonempty write footprint",
        )
        certificate = SegmentCertificate(
            query,
            field,
            entry,
            stop,
            tuple(registers["gprs"]),
            identifier(raw["theorem"], "theorem"),
            identifier(raw["precondition"], "precondition"),
            identifier(raw["postcondition"], "postcondition"),
        )
        require(
            certificate.matches_effect(effects[query]),
            f"{query}: effect projection mismatch",
        )
        provenance = (
            raw["provenance_manifest"],
            checked_digest(raw["provenance_sha256"], "provenance"),
        )
        require(isinstance(provenance[0], str), "invalid provenance path")
        if provenance not in checked_provenance:
            validate_sources(directory, repo_root, *provenance)
            checked_provenance.add(provenance)
        certificates[query] = certificate
    return certificates
