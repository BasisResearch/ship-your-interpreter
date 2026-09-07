"""Generate bounded Lean composition modules; never invoke the compiler.

Run after generating AliasTrace001 through AliasTrace285. The generated
build-order.txt lists modules in dependency order, including the conditional
refutation copied from TraceRefutation.lean. Generation is not proof checking.
"""

import argparse
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Group:
    """An inclusive interval of transition certificates."""

    number: int
    first: int
    last: int

    @property
    def module(self) -> str:
        """Return the generated module name."""
        return f"AliasTraceGroup{self.number:03}"


def groups_for(size: int) -> list[Group]:
    """Partition the 284 transitions into bounded groups.

    >>> groups_for(15)[-1]
    Group(number=19, first=271, last=284)
    """
    if not 10 <= size <= 20:
        raise ValueError("group size must be between 10 and 20")
    return [
        Group(number, first, min(first + size - 1, 284))
        for number, first in enumerate(range(1, 285, size), start=1)
    ]


def lean_module(imports: list[str], body: list[str]) -> str:
    """Wrap a proof body in the shared trace namespace."""
    return "\n".join(
        [
            *(f"import {name}" for name in imports),
            "",
            "open Vsa.Machine Vsa.Refine Vsa.While",
            "namespace Vsa.Sim.OutputAliasLoaded",
            "",
            *body,
            "",
            "end Vsa.Sim.OutputAliasLoaded",
            "",
        ]
    )


def unit_module(index: int, packaged: bool) -> str:
    """Return the selected module containing a transition or halt theorem."""
    if packaged:
        return f"Vsa.Sim.OutputAliasRun.Part{(index - 1) // 20:02}"
    return f"AliasTrace{index:03}"


def group_source(group: Group, packaged: bool = False) -> str:
    """Compose one group without unfolding any machine data."""
    body = [
        f"theorem runGroup{group.number:03} {{c : Config}}",
        f"    (h : TraceHolds traceD{group.first:03} c) :",
        f"    ∃ c', Steps c c' ∧ TraceHolds traceD{group.last + 1:03} c' := by",
    ]
    for index in range(group.first, group.last + 1):
        previous = "h" if index == group.first else f"h{index - 1:03}"
        body.append(
            f"  obtain ⟨c{index:03}, s{index:03}, h{index:03}⟩ := "
            f"run{index:03} {previous}"
        )
        if index == group.first:
            body.append(f"  have path{index:03} : Steps c c{index:03} := s{index:03}")
        else:
            body.append(
                f"  have path{index:03} : Steps c c{index:03} := "
                f"path{index - 1:03}.trans s{index:03}"
            )
    body.extend(
        [
            f"  exact ⟨c{group.last:03}, path{group.last:03}, h{group.last:03}⟩",
            "",
            f"#print axioms runGroup{group.number:03}",
        ]
    )
    return lean_module(
        list(
            dict.fromkeys(
                unit_module(index, packaged)
                for index in range(group.first, group.last + 1)
            )
        ),
        body,
    )


def complete_source(groups: list[Group], packaged: bool = False) -> str:
    """Attach the initial segment and final HTIF halt to all groups."""
    body = [
        'theorem snapshot_halts_twoLF : Halts snapshotConfig "\\n\\n" 0 := by',
        "  obtain ⟨c000, path000, h000⟩ := traceStart",
    ]
    for group in groups:
        number = group.number
        body.extend(
            [
                f"  obtain ⟨c{number:03}, s{number:03}, h{number:03}⟩ := "
                f"runGroup{number:03} h{number - 1:03}",
                f"  have path{number:03} : Steps snapshotConfig c{number:03} := "
                f"path{number - 1:03}.trans s{number:03}",
            ]
        )
    last = groups[-1].number
    body.extend(
        [
            f"  obtain ⟨σf, hh, ho⟩ := run285 h{last:03}",
            f"  refine ⟨c{last:03}, σf, path{last:03}, hh, ?_⟩",
            '  change String.join σf.sailOutput.toList = "\\n\\n"',
            "  rw [ho]",
            "  rfl",
            "",
            "#print axioms snapshot_halts_twoLF",
        ]
    )
    return lean_module(
        [*(group.module for group in groups), unit_module(285, packaged)], body
    )


def refuted_source() -> str:
    """Apply the conditional refutation to the complete machine certificate."""
    return lean_module(
        ["AliasTraceComplete", "TraceRefutation"],
        [
            "open Vsa.Sim.LayoutInstance",
            "",
            "theorem snapshot_not_interpSim : ¬ InterpSim BeforeAstOwnership.interpRunLayout :=",
            "  not_interpSim_of_alias_halt snapshot_halts_twoLF",
            "",
            "theorem snapshot_not_remainingWork :",
            "    (EndToEnd.RemainingWork BeforeAstOwnership.interpRunLayout → False) :=",
            "  not_remainingWork_of_alias_halt snapshot_halts_twoLF",
            "",
            "theorem snapshot_not_behavioralCorrespondence :",
            "    ¬ (∀ p c, Loaded BeforeAstOwnership.interpRunLayout p c →",
            "      (∀ out, BigStep p out ↔ Halts c out 0) ∧",
            "      (Diverges c → ¬ ∃ out, BigStep p out)) :=",
            "  not_behavioralCorrespondence_of_alias_halt snapshot_halts_twoLF",
            "",
            "#print axioms snapshot_not_interpSim",
            "#print axioms snapshot_not_remainingWork",
            "#print axioms snapshot_not_behavioralCorrespondence",
        ],
    )


def generate(
    certificates: Path,
    output: Path,
    refutation: Path,
    size: int,
    packaged: bool = False,
) -> None:
    """Write proof sources and provenance without trusting compiler artifacts."""
    groups = groups_for(size)
    inputs = [certificates / "AliasTraceData.lean", refutation]
    inputs.extend(
        certificates / f"AliasTrace{index:03}.lean" for index in range(1, 286)
    )
    fingerprints = {
        str(path.resolve()): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in inputs
    }
    generated = {group.module: group_source(group, packaged) for group in groups}
    generated["AliasTraceComplete"] = complete_source(groups, packaged)
    generated["TraceRefutation"] = refutation.read_text()
    generated["AliasTraceRefuted"] = refuted_source()
    output.mkdir(parents=True, exist_ok=True)
    for name, source in generated.items():
        (output / f"{name}.lean").write_text(source)
    (output / "build-order.txt").write_text("\n".join(generated) + "\n")
    provenance = {
        "status": "generated_unchecked",
        "group_size": size,
        "transition_units": 284,
        "halt_unit": 285,
        "imports": "packaged" if packaged else "individual",
        "inputs_sha256": fingerprints,
        "generated_sha256": {
            name: hashlib.sha256(source.encode()).hexdigest()
            for name, source in generated.items()
        },
    }
    (output / "generation-manifest.json").write_text(
        json.dumps(provenance, indent=2) + "\n"
    )
    print(
        f"Generated {len(groups)} groups and 3 final modules in {output} (unchecked)."
    )


def main() -> None:
    """Parse the CLI and generate the composition sources."""
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificates", type=Path, default=here / "certificates")
    parser.add_argument("--output", type=Path, default=here / "composition")
    parser.add_argument(
        "--refutation", type=Path, default=here / "TraceRefutation.lean"
    )
    parser.add_argument("--group-size", type=int, default=15)
    parser.add_argument("--packaged-imports", action="store_true")
    args = parser.parse_args()
    generate(
        args.certificates,
        args.output,
        args.refutation,
        args.group_size,
        args.packaged_imports,
    )


if __name__ == "__main__":
    main()
