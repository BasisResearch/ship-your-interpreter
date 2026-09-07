#!/usr/bin/env python3
"""Consolidate generated composition sources without changing their proof bodies.

Generation is not proof checking. Compile the resulting repository modules with
scripts/build_private.py before treating them as checked execution evidence.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path

NAMESPACE = "Vsa.Sim.OutputAliasLoaded"
R7_MARKER = "-- discipline: allow(R7-conj-tower-def) Generated independent transition endpoints; each post is the named TraceHolds structure. Existentials bind reached configurations for Steps composition, not anonymous representation towers."


@dataclass(frozen=True)
class Output:
    """One repository-relative output and its exact UTF-8 source bytes."""

    relative: Path
    content: bytes


def body(source: str, label: str) -> str:
    """Extract the existing namespace body with the original whitespace rule."""
    start = "namespace " + NAMESPACE + "\n"
    finish = "end " + NAMESPACE
    if source.count(start) != 1 or source.count(finish) != 1:
        raise ValueError(f"{label}: expected one complete namespace block")
    if re.search(r"\b(?:sorryAx|sorry|native_decide|bv_decide)\b", source):
        raise ValueError(f"{label}: prohibited proof token")
    return source.split(start, 1)[1].rsplit(finish, 1)[0].strip()


def module(imports: list[str], chunks: list[str], note: str = "") -> bytes:
    """Render the original consolidated module format exactly."""
    return (
        "\n".join("import " + name for name in sorted(set(imports)))
        + "\n\n"
        + note
        + "open Vsa.Machine Vsa.Refine Vsa.While\nnamespace "
        + NAMESPACE
        + "\n\n"
        + "\n\n".join(chunks)
        + "\n\nend "
        + NAMESPACE
        + "\n"
    ).encode("utf-8")


def prepare(composition: Path) -> tuple[list[Output], dict[str, str]]:
    """Read and validate all inputs before preparing the three output modules."""
    names = [f"AliasTraceGroup{i:03}.lean" for i in range(1, 20)]
    found = sorted(path.name for path in composition.glob("AliasTraceGroup*.lean"))
    if found != names:
        raise ValueError("expected exactly composition groups 001 through 019")
    names += [
        "AliasTraceComplete.lean",
        "TraceRefutation.lean",
        "AliasTraceRefuted.lean",
    ]
    sources = {name: (composition / name).read_text(encoding="utf-8") for name in names}
    bodies = {name: body(source, name) for name, source in sources.items()}
    imports = [
        line[7:]
        for name in names[:19]
        for line in sources[name].splitlines()
        if line.startswith("import ")
    ]
    if not imports or any(
        re.fullmatch(r"Vsa\.Sim\.OutputAliasRun\.Part(?:0[0-9]|1[0-4])", name) is None
        for name in imports
    ):
        raise ValueError(
            "group imports must use the packaged Part00 through Part14 modules"
        )
    outputs = [
        Output(
            Path("Vsa/Sim/OutputAliasRun/Groups.lean"),
            module(imports, [bodies[name] for name in names[:19]]).replace(
                b"\n\n", b"\n" + R7_MARKER.encode("utf-8") + b"\n\n", 1
            ),
        ),
        Output(
            Path("Vsa/Sim/OutputAliasRun.lean"),
            module(
                ["Vsa.Sim.OutputAliasRun.Groups"],
                [bodies["AliasTraceComplete.lean"]],
                "/-! Complete dense-state execution of the admitted output-alias program. -/\n\n",
            ),
        ),
        Output(
            Path("Vsa/Sim/OutputAliasRefutation.lean"),
            module(
                ["Vsa.Sim.OutputAliasRun", "Vsa.Sim.EndToEnd"],
                [bodies["TraceRefutation.lean"], bodies["AliasTraceRefuted.lean"]],
                "/-! The historical physical boundary admits an incompatible execution. The admitted source\n"
                "program prints one newline; its complete machine execution prints two. -/\n\n",
            ),
        ),
    ]
    fingerprints = {
        name: hashlib.sha256(source.encode("utf-8")).hexdigest()
        for name, source in sources.items()
    }
    return outputs, fingerprints


def main() -> None:
    """Parse explicit paths, consolidate sources, and save a generation receipt."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--composition", required=True, type=Path)
    parser.add_argument("--repo", required=True, type=Path)
    args = parser.parse_args()
    repo = args.repo.resolve()
    composition = args.composition.resolve()
    if not (repo / "Vsa/Sim/OutputAliasLoaded.lean").is_file():
        parser.error("--repo must name the repository containing OutputAliasLoaded")
    outputs, fingerprints = prepare(composition)
    for output in outputs:
        target = repo / output.relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists() or target.read_bytes() != output.content:
            target.write_bytes(output.content)
    receipt = {
        "status": "packaged_unchecked",
        "proof_bodies_preserved": True,
        "body_sha256": {
            name: hashlib.sha256(
                body((composition / name).read_text(encoding="utf-8"), name).encode(
                    "utf-8"
                )
            ).hexdigest()
            for name in fingerprints
        },
        "wrapper_header_changes": {
            "imports": "consolidated into repository modules",
            "groups_comments": [R7_MARKER],
            "proof_body_changes": False,
            "body_edge_whitespace": "original consolidation strips namespace body edges",
        },
        "inputs_sha256": fingerprints,
        "outputs_sha256": {
            str(output.relative): hashlib.sha256(output.content).hexdigest()
            for output in outputs
        },
        "required_gate": "retained full-source integration build",
    }
    (composition / "package-composition-receipt.json").write_text(
        json.dumps(receipt, indent=2) + "\n", encoding="utf-8"
    )
    print("Packaged Groups, complete run, and refutation; integration build required.")


if __name__ == "__main__":
    main()
