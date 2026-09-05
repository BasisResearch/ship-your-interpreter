#!/usr/bin/env python3
"""Build a strict residual-by-semantic-dimension evidence ledger.

The ledger reports emitted evidence.  It does not promote a partial SMT model,
a trace, or metadata to a proof of the full Lean proposition.

>>> dimensions_for("store-output-ghost-index")
('store-env', 'output')
>>> dimensions_for("recursive call child")
('recursive-seq-loop', 'call')
"""

from __future__ import annotations

import argparse
import csv
import json
import tempfile
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path


DIMENSIONS = (
    "store-env",
    "recursive-seq-loop",
    "call",
    "output",
    "allocation",
    "helper-relation",
)

_DIMENSION_WORDS = {
    "store-env": ("store", "environment", "env-", "env_", "phi", "binding"),
    "recursive-seq-loop": (
        "recursive", "stitch", "sequence", "seq", "loop", "iteration", "status"
    ),
    "call": ("call", "callee", "argument", "argc", "arg-", "arg_", "abi", "native"),
    "output": ("output", "stream", "console", "print"),
    "allocation": ("alloc", "malloc", "arena", "closure", "frame-index"),
    "helper-relation": (
        "helper", "relation", "value-shadow", "cstring", "lookup", "update",
        "truth", "strcmp", "semantic-boundary",
    ),
}

_SEMANTIC_CAPABILITIES = {"partial-projection", "indexed-error-projection"}
_BOUNDARY_CAPABILITIES = {"machine-only", "machine-boundary"}
_VALID_CAPABILITIES = _SEMANTIC_CAPABILITIES | _BOUNDARY_CAPABILITIES

# This mixed projection is the first split proof/fuzzer client.  Its machine
# leaves are fixed by the native-assert post; the other four ABI leaves must be
# present as exact Lean certificate exclusions instead.
_REQUIRED_MACHINE_MUTATIONS = {
    "hCallAssertOk": {
        "null-kind", "null-payload", "x2", "output-array", "output-length",
    },
}


class LedgerError(ValueError):
    """An emitted coverage artifact is incomplete or contradictory."""


@dataclass(frozen=True)
class Evidence:
    kind: str
    source: str
    detail: str


def dimensions_for(text: str) -> tuple[str, ...]:
    """Map artifact vocabulary to the fixed semantic dimensions."""
    lowered = text.lower()
    return tuple(
        dimension
        for dimension in DIMENSIONS
        if any(word in lowered for word in _DIMENSION_WORDS[dimension])
    )


def _read_tsv(path: Path, required: set[str]) -> list[dict[str, str]]:
    if not path.is_file():
        raise LedgerError(f"missing artifact: {path}")
    with path.open(newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        fields = set(reader.fieldnames or ())
        missing = required - fields
        if missing:
            raise LedgerError(f"{path}: missing columns {sorted(missing)}")
        rows = list(reader)
    if any(any(value is None for value in row.values()) for row in rows):
        raise LedgerError(f"{path}: malformed row")
    return rows


def _unique(rows: list[dict[str, str]], keys: tuple[str, ...], source: Path) -> None:
    seen: set[tuple[str, ...]] = set()
    for row in rows:
        key = tuple(row[key_name] for key_name in keys)
        if not all(key):
            raise LedgerError(f"{source}: empty key {keys}")
        if key in seen:
            raise LedgerError(f"{source}: duplicate row {key}")
        seen.add(key)


def _is_valid(verdict: str) -> bool:
    return verdict.startswith("VALID") and not verdict.startswith("VALID[Lean:")


def _query_dimensions(
    query: str,
    residual: str,
    extensions: dict[str, list[dict[str, str]]],
) -> set[str]:
    text = " ".join(
        [query, residual]
        + [" ".join(row.values()) for row in extensions.get(query, ())]
    )
    result = set(dimensions_for(text))
    # A validated residual_relation is always a helper-to-Lean relation at
    # minimum.  More specific dimensions require emitted names/predicates.
    result.add("helper-relation")
    return result


def _post_dimensions(post: str) -> set[str]:
    if post in {"storerepr", "outside_stack_arena"}:
        return {"store-env"}
    if post == "out":
        return {"output"}
    if post.startswith("abi_"):
        return {"call"}
    if "alloc" in post or "arena" in post:
        return {"allocation"}
    if "seq" in post or "loop" in post:
        return {"recursive-seq-loop"}
    if post in {"valuerepr_tag", "residual_relation"}:
        return {"helper-relation"}
    return set(dimensions_for(post))


def _check_required_machine_mutations(residual: str, found: set[str]) -> None:
    required = _REQUIRED_MACHINE_MUTATIONS.get(residual)
    if required is not None and found != required:
        raise LedgerError(
            f"wrong machine mutation leaves for {residual}: "
            f"expected={sorted(required)}, found={sorted(found)}"
        )


def _load_verdicts(paths: list[Path]) -> dict[str, dict[str, str]]:
    merged: dict[str, dict[str, str]] = {}
    origins: dict[str, Path] = {}
    for path in paths:
        rows = _read_tsv(
            path, {"query", "residual", "instance", "capability"}
        )
        _unique(rows, ("query",), path)
        for row in rows:
            query = row["query"]
            if query not in merged:
                merged[query] = row
                origins[query] = path
                continue
            prior = merged[query]
            for key in set(prior) | set(row):
                old = prior.get(key, "")
                new = row.get(key, "")
                if old in {"", "N/A"}:
                    prior[key] = new
                elif new not in {"", "N/A", old}:
                    raise LedgerError(
                        f"contradictory verdict cell {query}.{key}: "
                        f"{old} in {origins[query]}, {new} in {path}"
                    )
    return merged


def _validated_certificates(
    certificates: list[dict[str, str]],
    certificates_path: Path,
    query_by_name: dict[str, dict[str, str]],
    verdicts: dict[str, dict[str, str]],
) -> dict[tuple[str, str], str]:
    """Match every certificate to its exact emitted Lean verdict cell."""
    result: dict[tuple[str, str], str] = {}
    for row in certificates:
        query = row["residual"]
        post = row["post"]
        theorem = row["theorem"]
        key = (query, post)
        if query not in query_by_name:
            raise LedgerError(f"Lean certificate names unknown query {query}")
        if not theorem or post == "residual_relation":
            raise LedgerError(f"invalid Lean certificate {query}.{post}")
        expected = f"VALID[Lean:{theorem}]"
        actual = verdicts.get(query, {}).get(post, "")
        if actual != expected:
            raise LedgerError(
                f"{certificates_path}: certificate/verdict mismatch for "
                f"{query}.{post}: expected {expected}, got {actual or '<missing>'}"
            )
        result[key] = theorem

    # A verdict label alone is not a certificate.  Reject labels which do not
    # have the exact query/post/theorem row above.
    for query, verdict in verdicts.items():
        for post, value in verdict.items():
            if not value.startswith("VALID[Lean:"):
                continue
            theorem = result.get((query, post))
            if theorem is None or value != f"VALID[Lean:{theorem}]":
                raise LedgerError(
                    f"unmanifested Lean verdict {query}.{post}: {value}"
                )
    return result


def build_ledger(
    campaign: Path,
    verdict_paths: list[Path],
    fuzz_paths: list[Path],
    only: set[str] | None = None,
) -> dict[str, object]:
    """Validate artifacts and return a complete Cartesian coverage matrix."""
    residual_caps_path = campaign / "residual-capabilities.tsv"
    query_caps_path = campaign / "query-capabilities.tsv"
    spans_path = campaign / "spans.tsv"
    holes_path = campaign / "residual-holes.tsv"
    extensions_path = campaign / "residual-extensions.tsv"
    certificates_path = campaign / "lean-certificates.tsv"

    residual_caps = _read_tsv(
        residual_caps_path,
        {"field", "machine_instances", "semantic_projection", "full_residual"},
    )
    query_caps = _read_tsv(
        query_caps_path, {"query", "field", "instance", "capability"}
    )
    spans = _read_tsv(spans_path, {"field", "residual", "instance"})
    holes = _read_tsv(holes_path, {"field", "dimension", "reason"})
    extensions = _read_tsv(
        extensions_path, {"query", "field", "name", "predicate"}
    )
    certificates = _read_tsv(
        certificates_path, {"residual", "post", "theorem"}
    )

    _unique(residual_caps, ("field",), residual_caps_path)
    _unique(query_caps, ("query",), query_caps_path)
    _unique(spans, ("field",), spans_path)
    _unique(holes, ("field", "dimension"), holes_path)
    _unique(extensions, ("query", "name"), extensions_path)
    _unique(certificates, ("residual", "post"), certificates_path)

    capability_targets = {row["field"] for row in residual_caps}
    full_hole_targets = {
        row["field"] for row in holes if row["dimension"] == "full-lean-proposition"
    }
    if only is None and capability_targets != full_hole_targets:
        raise LedgerError(
            "target inventory mismatch: "
            f"capability-only={sorted(capability_targets - full_hole_targets)} "
            f"hole-only={sorted(full_hole_targets - capability_targets)}"
        )
    targets = full_hole_targets if only is None else set(only)
    if not targets <= full_hole_targets:
        raise LedgerError(
            f"unknown scoped targets: {sorted(targets - full_hole_targets)}"
        )
    if not targets <= capability_targets:
        raise LedgerError(
            "scoped targets have no emitted capability row: "
            f"{sorted(targets - capability_targets)}"
        )
    residual_caps = [row for row in residual_caps if row["field"] in targets]
    query_caps = [row for row in query_caps if row["field"] in targets]
    selected_queries = {row["query"] for row in query_caps}
    spans = [row for row in spans if row["field"] in selected_queries]
    holes = [row for row in holes if row["field"] in targets]
    extensions = [row for row in extensions if row["query"] in selected_queries]
    certificates = [
        row for row in certificates if row["residual"] in selected_queries
    ]

    query_by_name = {row["query"]: row for row in query_caps}
    span_by_name = {row["field"]: row for row in spans}
    span_names = set(span_by_name)
    if set(query_by_name) != span_names:
        raise LedgerError(
            "query/span mismatch: "
            f"capability-only={sorted(set(query_by_name) - span_names)} "
            f"span-only={sorted(span_names - set(query_by_name))}"
        )
    for row in query_caps:
        if row["capability"] not in _VALID_CAPABILITIES:
            raise LedgerError(
                f"{query_caps_path}: invalid capability {row['capability']}"
            )
        if row["field"] not in targets and row["capability"] != "machine-boundary":
            raise LedgerError(f"query {row['query']} names unknown residual {row['field']}")
        span = span_by_name[row["query"]]
        if span["residual"] != row["field"] or span["instance"] != row["instance"]:
            raise LedgerError(f"query/span metadata mismatch for {row['query']}")

    queries_by_residual: dict[str, list[dict[str, str]]] = defaultdict(list)
    for row in query_caps:
        queries_by_residual[row["field"]].append(row)
    for row in residual_caps:
        field = row["field"]
        if row["semantic_projection"] not in {"yes", "no"}:
            raise LedgerError(f"{field}: invalid semantic_projection value")
        if row["full_residual"] not in {"yes", "no"}:
            raise LedgerError(f"{field}: invalid full_residual value")
        try:
            advertised_instances = int(row["machine_instances"])
        except ValueError as error:
            raise LedgerError(f"{field}: invalid machine_instances") from error
        if advertised_instances < 0:
            raise LedgerError(f"{field}: negative machine_instances")
        actual_instances = len(queries_by_residual[field])
        if advertised_instances != actual_instances:
            raise LedgerError(
                f"{field}: machine_instances={advertised_instances}, actual={actual_instances}"
            )
        advertised_semantic = row["semantic_projection"] == "yes"
        actual_semantic = any(
            query["capability"] in _SEMANTIC_CAPABILITIES
            for query in queries_by_residual[field]
        )
        if advertised_semantic != actual_semantic:
            raise LedgerError(f"{field}: false semantic_projection capability claim")
        if row["full_residual"] == "yes" and any(
            hole["field"] == field for hole in holes
        ):
            raise LedgerError(f"{field}: full_residual contradicts explicit holes")

    extensions_by_query: dict[str, list[dict[str, str]]] = defaultdict(list)
    for row in extensions:
        if row["query"] not in query_by_name:
            raise LedgerError(f"extension names unknown query {row['query']}")
        if row["field"] != query_by_name[row["query"]]["field"]:
            raise LedgerError(f"extension/query residual mismatch for {row['query']}")
        extensions_by_query[row["query"]].append(row)

    verdicts = _load_verdicts(verdict_paths)
    for query, row in verdicts.items():
        if query not in query_by_name:
            raise LedgerError(f"verdict names unknown query {query}")
        capability = query_by_name[query]
        if row["residual"] != capability["field"]:
            raise LedgerError(f"verdict/query residual mismatch for {query}")
        if row["capability"] != capability["capability"]:
            raise LedgerError(f"verdict/query capability mismatch for {query}")
    semantic_queries = {
        row["query"]
        for row in query_caps
        if row["capability"] in _SEMANTIC_CAPABILITIES
    }
    missing_verdicts = semantic_queries - set(verdicts)
    if missing_verdicts:
        raise LedgerError(f"missing semantic verdicts: {sorted(missing_verdicts)}")
    false_claims = sorted(
        query
        for query in semantic_queries
        if not _is_valid(verdicts[query].get("residual_relation", ""))
    )
    if false_claims:
        raise LedgerError(f"semantic projection not validated: {false_claims}")

    evidence: dict[tuple[str, str], list[Evidence]] = defaultdict(list)
    for query in sorted(semantic_queries):
        verdict = verdicts[query]
        residual = query_by_name[query]["field"]
        for dimension in _query_dimensions(
            query, residual, extensions_by_query
        ):
            evidence[(residual, dimension)].append(
                Evidence("smt-executable", query, verdict["residual_relation"])
            )
        for post, value in sorted(verdict.items()):
            if post == "residual_relation":
                continue
            if _is_valid(value):
                for dimension in _post_dimensions(post):
                    evidence[(residual, dimension)].append(
                        Evidence("smt-executable", f"{query}.{post}", value)
                    )

    validated_certificates = _validated_certificates(
        certificates, certificates_path, query_by_name, verdicts
    )
    for row in certificates:
        query = row["residual"]
        residual = query_by_name[query]["field"]
        certificate_dimensions = _post_dimensions(row["post"])
        if not certificate_dimensions:
            raise LedgerError(
                f"unclassified Lean certificate post {query}.{row['post']}"
            )
        for dimension in certificate_dimensions:
            evidence[(residual, dimension)].append(
                Evidence(
                    "lean-certified", f"{query}.{row['post']}", row["theorem"]
                )
            )

    fuzz_seen: set[tuple[Path, tuple[tuple[str, str], ...]]] = set()
    fuzz_queries: dict[str, list[str]] = defaultdict(list)
    audited_dimensions: dict[str, set[str]] = defaultdict(set)
    for path in fuzz_paths:
        rows = _read_tsv(
            path,
            {
                "field", "residual_post", "agree", "mutations_expected",
                "mutations_killed", "certificates_excluded",
            },
        )
        findings_path = Path(str(path) + ".findings")
        if findings_path.is_file():
            findings = _read_tsv(findings_path, set())
            if findings:
                raise LedgerError(f"fuzzer findings are nonempty: {findings_path}")
        mutation_path = Path(str(path) + ".mutations.tsv")
        mutations = _read_tsv(
            mutation_path,
            {"field", "post", "mutation", "provenance", "result"},
        )
        _unique(mutations, ("field", "post", "mutation"), mutation_path)
        mutations_by_query: dict[str, list[dict[str, str]]] = defaultdict(list)
        declared_audit_queries = set()
        for mutation in mutations:
            query = mutation["field"]
            if query not in query_by_name:
                raise LedgerError(f"mutation audit names unknown query {query}")
            result = mutation["result"]
            if result == "killed":
                if mutation["post"] != "residual_relation" or \
                        mutation["provenance"] != "independent-trace-oracle":
                    raise LedgerError(
                        f"invalid machine mutation provenance: {query}."
                        f"{mutation['mutation']}"
                    )
            elif result == "excluded-lean-certificate":
                theorem = validated_certificates.get((query, mutation["post"]))
                if theorem is None or mutation["provenance"] != theorem:
                    raise LedgerError(
                        f"invalid certificate exclusion: {query}."
                        f"{mutation['post']}"
                    )
            else:
                raise LedgerError(
                    f"invalid mutation result {query}.{mutation['mutation']}: {result}"
                )
            mutations_by_query[query].append(mutation)
        for row in rows:
            query = row["field"]
            # Multiple executions of one query in one trace are legitimate.
            # Only an exactly duplicated evidence row is malformed.
            key = (path, tuple(sorted(row.items())))
            if key in fuzz_seen:
                raise LedgerError(f"{path}: duplicate fuzz row {query}")
            fuzz_seen.add(key)
            if query not in query_by_name:
                raise LedgerError(f"fuzzer names unknown query {query}")
            if row["agree"] != "yes" or row["residual_post"] != "yes":
                raise LedgerError(
                    f"failed fuzz evidence {path}:{query}: "
                    f"agree={row['agree']}, residual_post={row['residual_post']}"
                )
            try:
                expected = int(row["mutations_expected"])
                killed = int(row["mutations_killed"])
                excluded = int(row["certificates_excluded"])
            except ValueError as error:
                raise LedgerError(f"invalid mutation counts for {query}") from error
            audited = mutations_by_query[query]
            killed_rows = [item for item in audited if item["result"] == "killed"]
            excluded_rows = [
                item for item in audited
                if item["result"] == "excluded-lean-certificate"
            ]
            expected_certificates = {
                post for certificate_query, post in validated_certificates
                if certificate_query == query
            }
            excluded_certificates = {item["post"] for item in excluded_rows}
            if expected < 0 or killed != expected or len(killed_rows) != expected:
                raise LedgerError(
                    f"incomplete machine mutation audit for {query}: "
                    f"expected={expected}, killed={killed}, rows={len(killed_rows)}"
                )
            _check_required_machine_mutations(
                query_by_name[query]["field"],
                {item["mutation"] for item in killed_rows},
            )
            if excluded != len(excluded_rows) or \
                    excluded_certificates != expected_certificates:
                raise LedgerError(
                    f"incomplete certificate exclusion audit for {query}: "
                    f"expected={sorted(expected_certificates)}, "
                    f"found={sorted(excluded_certificates)}"
                )
            if expected or excluded:
                declared_audit_queries.add(query)
            if expected:
                audited_dimensions[query].update(
                    dimension
                    for item in killed_rows
                    for dimension in dimensions_for(item["mutation"])
                )
                fuzz_queries[query].append(
                    f"{path}:{row.get('trace', '?')}@{row.get('step', '?')}"
                )
        if set(mutations_by_query) != declared_audit_queries:
            raise LedgerError(
                f"{mutation_path}: mutation/trace query mismatch: "
                f"mutation-only="
                f"{sorted(set(mutations_by_query) - declared_audit_queries)} "
                f"trace-only="
                f"{sorted(declared_audit_queries - set(mutations_by_query))}"
            )

    # A phase3b pass covers the executable residual relation, not separately
    # certified Lean posts.  In particular, ABI certificate rows are never
    # relabelled as fuzz evidence merely because the same query has a trace.
    for query, sources in fuzz_queries.items():
        capability = query_by_name[query]["capability"]
        if capability not in _SEMANTIC_CAPABILITIES:
            continue
        residual = query_by_name[query]["field"]
        query_dimensions = (
            _query_dimensions(query, residual, extensions_by_query)
            | audited_dimensions[query]
        )
        for dimension in query_dimensions:
            if dimension not in _query_dimensions(
                query, residual, extensions_by_query
            ):
                evidence[(residual, dimension)].append(
                    Evidence(
                        "smt-executable", query,
                        verdicts[query]["residual_relation"],
                    )
                )
            evidence[(residual, dimension)].append(
                Evidence(
                    "fuzz-covered",
                    f"{query}.residual_relation",
                    ",".join(sources),
                )
            )

    # Make the exact leaf distinction machine-readable.  A certificate leaf
    # has no fuzz bit; SMT/fuzzer evidence belongs to residual_relation.
    leaves = []
    for query in sorted(semantic_queries):
        residual = query_by_name[query]["field"]
        query_dimensions = (
            _query_dimensions(query, residual, extensions_by_query)
            | audited_dimensions[query]
        )
        for dimension in sorted(
            query_dimensions
        ):
            leaves.append(
                {
                    "residual": residual,
                    "query": query,
                    "leaf": "residual_relation",
                    "dimension": dimension,
                    "smt_executable": True,
                    "lean_certified": False,
                    "fuzz_covered": query in fuzz_queries,
                }
            )
    for (query, post), theorem in sorted(validated_certificates.items()):
        residual = query_by_name[query]["field"]
        for dimension in sorted(_post_dimensions(post)):
            leaves.append(
                {
                    "residual": residual,
                    "query": query,
                    "leaf": post,
                    "dimension": dimension,
                    "smt_executable": False,
                    "lean_certified": True,
                    "fuzz_covered": False,
                    "theorem": theorem,
                }
            )

    # Detect the impossible status combination directly, rather than relying
    # on the presentation matrix to hide it.
    for leaf in leaves:
        if leaf["lean_certified"] and (
            leaf["smt_executable"] or leaf["fuzz_covered"]
        ):
            raise LedgerError(f"certificate falsely double-counted: {leaf}")

    specific_holes: dict[tuple[str, str], list[str]] = defaultdict(list)
    generic_holes: dict[str, list[str]] = defaultdict(list)
    for row in holes:
        if row["field"] not in targets:
            raise LedgerError(f"hole names unknown residual {row['field']}")
        if row["dimension"] == "full-lean-proposition":
            generic_holes[row["field"]].append(row["reason"])
            continue
        mapped = dimensions_for(row["dimension"] + " " + row["reason"])
        if not mapped:
            generic_holes[row["field"]].append(
                f"{row['dimension']}: {row['reason']}"
            )
        for dimension in mapped:
            specific_holes[(row["field"], dimension)].append(
                f"{row['dimension']}: {row['reason']}"
            )

    matrix = []
    for residual in sorted(targets):
        for dimension in DIMENSIONS:
            positive = evidence[(residual, dimension)]
            holes_here = specific_holes[(residual, dimension)]
            if not positive and not holes_here:
                holes_here = generic_holes[residual] or ["no emitted evidence"]
            kinds = sorted({item.kind for item in positive})
            if holes_here:
                kinds.append("explicit-hole")
            matrix.append(
                {
                    "residual": residual,
                    "dimension": dimension,
                    "classification": "+".join(kinds),
                    "smt_executable": any(
                        item.kind == "smt-executable" for item in positive
                    ),
                    "lean_certified": any(
                        item.kind == "lean-certified" for item in positive
                    ),
                    "fuzz_covered": any(
                        item.kind == "fuzz-covered" for item in positive
                    ),
                    "explicit_hole": bool(holes_here),
                    "evidence": [item.__dict__ for item in positive],
                    "holes": holes_here,
                }
            )
    expected_cells = len(targets) * len(DIMENSIONS)
    if len(matrix) != expected_cells:
        raise LedgerError(f"matrix incomplete: {len(matrix)}/{expected_cells}")
    classifications = defaultdict(int)
    for cell in matrix:
        classifications[cell["classification"]] += 1
    return {
        "schema": 1,
        "warning": "Evidence matrix only; it does not establish full faithfulness.",
        "summary": {
            "target_count": len(targets),
            "dimension_count": len(DIMENSIONS),
            "cell_count": len(matrix),
            "leaf_count": len(leaves),
            "classifications": dict(sorted(classifications.items())),
        },
        "targets": sorted(targets),
        "dimensions": list(DIMENSIONS),
        "leaves": leaves,
        "cells": matrix,
    }


def write_outputs(ledger: dict[str, object], tsv_path: Path, json_path: Path) -> None:
    cells = ledger["cells"]
    assert isinstance(cells, list)
    columns = (
        "residual", "dimension", "classification", "smt_executable",
        "lean_certified", "fuzz_covered", "explicit_hole", "evidence", "holes",
    )
    with tsv_path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=columns, delimiter="\t")
        writer.writeheader()
        for cell in cells:
            assert isinstance(cell, dict)
            row = dict(cell)
            for column in (
                "smt_executable", "lean_certified", "fuzz_covered",
                "explicit_hole",
            ):
                row[column] = "yes" if row[column] else "no"
            row["evidence"] = json.dumps(row["evidence"], sort_keys=True)
            row["holes"] = json.dumps(row["holes"], sort_keys=True)
            writer.writerow(row)
    json_path.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n")


def _write_tsv(path: Path, header: tuple[str, ...], rows: list[tuple[str, ...]]) -> None:
    with path.open("w", newline="") as stream:
        writer = csv.writer(stream, delimiter="\t", lineterminator="\n")
        writer.writerow(header)
        writer.writerows(rows)


def selfcheck() -> None:
    """Mutation tests for omissions, duplicates, and false coverage claims."""
    _check_required_machine_mutations(
        "hCallAssertOk",
        {"null-kind", "null-payload", "x2", "output-array", "output-length"},
    )
    try:
        _check_required_machine_mutations(
            "hCallAssertOk",
            {"null-kind", "null-payload", "output-array", "output-length"},
        )
    except LedgerError:
        pass
    else:
        raise AssertionError("omitted hCallAssertOk x2 mutation accepted")
    with tempfile.TemporaryDirectory(prefix="residual-ledger-") as directory:
        root = Path(directory)
        _write_tsv(root / "residual-capabilities.tsv",
                   ("field", "machine_instances", "semantic_projection", "full_residual"),
                   [("hCall", "1", "yes", "no"), ("hSeqSteps", "0", "no", "no")])
        _write_tsv(root / "query-capabilities.tsv",
                   ("query", "field", "instance", "capability"),
                   [("hCallQ", "hCall", "call-stage", "partial-projection")])
        _write_tsv(root / "spans.tsv", ("field", "residual", "instance"),
                   [("hCallQ", "hCall", "call-stage")])
        hole_rows = [
            ("hCall", "full-lean-proposition", "partial model"),
            ("hSeqSteps", "full-lean-proposition", "recursive family"),
            ("hSeqSteps", "recursive-stitching", "loop child is not encoded"),
        ]
        _write_tsv(root / "residual-holes.tsv", ("field", "dimension", "reason"), hole_rows)
        _write_tsv(root / "residual-extensions.tsv",
                   ("query", "field", "name", "predicate"),
                   [("hCallQ", "hCall", "child-call", "callee ABI")])
        certificate_rows = [
            ("hCallQ", "abi_frame_x1", "Vsa.Sim.exampleAbi_closed")
        ]
        _write_tsv(
            root / "lean-certificates.tsv",
            ("residual", "post", "theorem"),
            certificate_rows,
        )
        verdict = root / "verdicts.tsv"
        verdict_header = (
            "query", "residual", "instance", "capability",
            "residual_relation", "abi_frame_x1",
        )
        _write_tsv(
            verdict,
            verdict_header,
            [("hCallQ", "hCall", "call-stage", "partial-projection",
              "VALID-PROJECTION", "N/A")],
        )
        certificate_verdict = root / "verdicts-certificate.tsv"
        _write_tsv(
            certificate_verdict,
            verdict_header,
            [("hCallQ", "hCall", "call-stage", "partial-projection",
              "N/A", "VALID[Lean:Vsa.Sim.exampleAbi_closed]")],
        )
        verdict_paths = [verdict, certificate_verdict]
        fuzz = root / "fuzz.tsv"
        fuzz_header = (
            "field", "trace", "residual_post", "agree",
            "mutations_expected", "mutations_killed", "certificates_excluded",
        )
        _write_tsv(
            fuzz,
            fuzz_header,
            [("hCallQ", "trace-1", "yes", "yes", "1", "1", "1")],
        )
        mutation_path = Path(str(fuzz) + ".mutations.tsv")
        mutation_header = ("field", "post", "mutation", "provenance", "result")
        mutation_rows = [
            ("hCallQ", "residual_relation", "machine-result",
             "independent-trace-oracle", "killed"),
            ("hCallQ", "abi_frame_x1", "x1",
             "Vsa.Sim.exampleAbi_closed", "excluded-lean-certificate"),
        ]
        _write_tsv(mutation_path, mutation_header, mutation_rows)
        _write_tsv(Path(str(fuzz) + ".findings"), ("kind", "where", "detail"), [])
        ledger = build_ledger(root, verdict_paths, [fuzz])
        assert len(ledger["cells"]) == 2 * len(DIMENSIONS)
        matrix_tsv = root / "matrix.tsv"
        matrix_json = root / "matrix.json"
        write_outputs(ledger, matrix_tsv, matrix_json)
        assert len(_read_tsv(matrix_tsv, {"residual", "dimension"})) == 12
        assert json.loads(matrix_json.read_text())["summary"]["cell_count"] == 12
        certificate_leaves = [
            leaf for leaf in ledger["leaves"]
            if leaf["leaf"] == "abi_frame_x1"
        ]
        assert certificate_leaves == [{
            "residual": "hCall",
            "query": "hCallQ",
            "leaf": "abi_frame_x1",
            "dimension": "call",
            "smt_executable": False,
            "lean_certified": True,
            "fuzz_covered": False,
            "theorem": "Vsa.Sim.exampleAbi_closed",
        }]

        mutations = []
        mutations.append(("omitted-target-hole", lambda: _write_tsv(
            root / "residual-holes.tsv", ("field", "dimension", "reason"),
            hole_rows[:1] + hole_rows[2:])))
        mutations.append(("duplicate-query", lambda: _write_tsv(
            root / "query-capabilities.tsv", ("query", "field", "instance", "capability"),
            [("hCallQ", "hCall", "a", "partial-projection"),
             ("hCallQ", "hCall", "b", "partial-projection")])))
        for name, mutate in mutations:
            mutate()
            try:
                build_ledger(root, verdict_paths, [fuzz])
            except LedgerError:
                pass
            else:
                raise AssertionError(f"mutation accepted: {name}")
            # Restore the valid fixture.
            _write_tsv(root / "query-capabilities.tsv",
                       ("query", "field", "instance", "capability"),
                       [("hCallQ", "hCall", "call-stage", "partial-projection")])
            _write_tsv(root / "residual-holes.tsv", ("field", "dimension", "reason"), hole_rows)

        _write_tsv(
            root / "lean-certificates.tsv",
            ("residual", "post", "theorem"),
            [("hCallQ", "abi_frame_x1", "Vsa.Sim.falseClaim")],
        )
        try:
            build_ledger(root, verdict_paths, [fuzz])
        except LedgerError:
            pass
        else:
            raise AssertionError("false Lean certificate accepted")
        _write_tsv(
            root / "lean-certificates.tsv",
            ("residual", "post", "theorem"),
            certificate_rows,
        )

        _write_tsv(
            root / "lean-certificates.tsv",
            ("residual", "post", "theorem"),
            [],
        )
        try:
            build_ledger(root, verdict_paths, [fuzz])
        except LedgerError:
            pass
        else:
            raise AssertionError("omitted Lean certificate accepted")
        _write_tsv(
            root / "lean-certificates.tsv",
            ("residual", "post", "theorem"),
            certificate_rows,
        )

        _write_tsv(
            fuzz,
            fuzz_header,
            [("hCallQ", "trace-1", "yes", "no", "1", "1", "1")],
        )
        try:
            build_ledger(root, verdict_paths, [fuzz])
        except LedgerError:
            pass
        else:
            raise AssertionError("failed fuzz row accepted as coverage")
        _write_tsv(
            fuzz,
            fuzz_header,
            [("hCallQ", "trace-1", "yes", "yes", "1", "1", "1")],
        )

        _write_tsv(mutation_path, mutation_header, mutation_rows[1:])
        try:
            build_ledger(root, verdict_paths, [fuzz])
        except LedgerError:
            pass
        else:
            raise AssertionError("omitted machine mutation accepted")
        _write_tsv(mutation_path, mutation_header, mutation_rows)

        _write_tsv(root / "residual-capabilities.tsv",
                   ("field", "machine_instances", "semantic_projection", "full_residual"),
                   [("hCall", "1", "yes", "no"), ("hSeqSteps", "0", "yes", "no")])
        try:
            build_ledger(root, verdict_paths, [fuzz])
        except LedgerError:
            pass
        else:
            raise AssertionError("false semantic coverage claim accepted")

        _write_tsv(root / "residual-capabilities.tsv",
                   ("field", "machine_instances", "semantic_projection", "full_residual"),
                   [("hCall", "1", "yes", "no"), ("hSeqSteps", "0", "no", "no")])
        bad_verdict = root / "verdicts-bad.tsv"
        _write_tsv(bad_verdict,
                   verdict_header,
                   [("hCallQ", "hCall", "call-stage", "partial-projection",
                     "REFUTED", "N/A")])
        try:
            build_ledger(root, verdict_paths + [bad_verdict], [fuzz])
        except LedgerError:
            pass
        else:
            raise AssertionError("contradictory verdict accepted")
    print("[selfcheck] omissions, duplicates, and false coverage claims rejected")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    build = subparsers.add_parser("build")
    build.add_argument("--campaign", type=Path, required=True)
    build.add_argument("--verdict", action="append", type=Path, required=True)
    build.add_argument("--fuzz", action="append", type=Path, default=[])
    build.add_argument(
        "--only", action="append", default=[],
        help="restrict a focused campaign to these residuals",
    )
    build.add_argument("--out-tsv", type=Path, required=True)
    build.add_argument("--out-json", type=Path, required=True)
    subparsers.add_parser("selfcheck")
    arguments = parser.parse_args()
    if arguments.command == "selfcheck":
        selfcheck()
        return
    try:
        ledger = build_ledger(
            arguments.campaign,
            arguments.verdict,
            arguments.fuzz,
            set(arguments.only) if arguments.only else None,
        )
    except LedgerError as error:
        parser.error(str(error))
    write_outputs(ledger, arguments.out_tsv, arguments.out_json)
    print(
        f"wrote {len(ledger['cells'])} residual/dimension cells to "
        f"{arguments.out_tsv} and {arguments.out_json}"
    )


if __name__ == "__main__":
    main()
