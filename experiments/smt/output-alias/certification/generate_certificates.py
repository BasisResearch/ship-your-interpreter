#!/usr/bin/env python3
"""Generate Lean certificates from the fixed output-alias trace partition.

The JSON inputs are untrusted. Generated theorems require Lean compilation;
this script does not establish execution correctness. Unit zero is supplied by
OutputAliasPrefix. The default selection is every remaining unit, 1 through 285.

Example:
    python3 generate_certificates.py --partition trace-segments.json \
        --trace result.jsonl --output certificates
"""

from __future__ import annotations

import argparse
import json
from collections.abc import Iterable
from dataclasses import dataclass
from pathlib import Path
from typing import NotRequired, TypedDict, cast, get_args, get_origin, get_type_hints


class Register(TypedDict):
    """One observed register value and its memory-map presence flag."""

    register: int
    value: int
    present: bool


class Store(TypedDict):
    """An ordinary store with the recorded width-truncated value."""

    row: int
    address: int
    width: int
    value: int


class Load(TypedDict):
    """The effective byte values consumed by a load."""

    bytes: list[int]


class Decoded(TypedDict):
    """Lean syntax for an observed control-transfer terminator."""

    record: str


class Instruction(TypedDict):
    """Instruction fields used by the certificate renderer."""

    row: int
    pc: int
    word: int
    word_hex: str
    decode_batch: str | None
    load: Load | None
    store: Store | None
    htif_payload_writes: int
    body_kind: NotRequired[str | None]
    immediate21: NotRequired[int]
    immediate12: NotRequired[int]
    base_register: NotRequired[int]
    link_register: NotRequired[int]
    decoded: NotRequired[Decoded]


class Terminator(TypedDict):
    """A decoded control transfer associated with one trace row."""

    row: int
    decoded: Decoded


class Block(TypedDict):
    """A reflected instruction body and optional terminator."""

    body: list[Instruction]
    terminator: Terminator | None


class Unit(TypedDict):
    """An ordered segment or explicit instruction seam."""

    id: int
    kind: str
    row_start: int
    count: int
    entry_pc: int
    end_pc: int
    entry_gregs: list[tuple[int, int]]
    instructions: list[Instruction]
    ordinary_store_prefix_start: int
    ordinary_store_prefix_end: int
    seam_kind: NotRequired[str]
    blocks: NotRequired[list[Block]]
    loads: NotRequired[list[Load]]


class Partition(TypedDict):
    """The partition fields consumed by this generator."""

    ordinary_store_log: list[Store]
    units: list[Unit]


class TraceRow(TypedDict):
    """Concrete source-register and output data for a pre-step state."""

    instruction_word: int
    gprs: list[Register]
    output_before: str
    htif_payload_writes: int
    pc: int


class TraceDocument(TypedDict):
    """The replay document's complete ordered trace."""

    trace: list[TraceRow]


def validate_shape(value: object, expected: object, location: str) -> None:
    """Validate the consumed JSON schema before typed rendering.

    Extra audit metadata is permitted. Missing required fields and malformed
    consumed fields fail before any generated file is written.
    """
    import types
    from typing import is_typeddict

    origin = get_origin(expected)
    if origin is types.UnionType:
        for option in get_args(expected):
            try:
                validate_shape(value, option, location)
            except ValueError:
                continue
            return
        raise ValueError(f"{location}: value does not match {expected}")
    if is_typeddict(expected):
        if not isinstance(value, dict):
            raise ValueError(f"{location}: expected an object")
        fields = get_type_hints(expected, include_extras=True)
        for key, field_type in fields.items():
            optional = get_origin(field_type) is NotRequired
            if optional:
                field_type = get_args(field_type)[0]
            if key not in value:
                if optional:
                    continue
                raise ValueError(f"{location}: missing {key}")
            validate_shape(value[key], field_type, f"{location}.{key}")
        return
    if origin in (list, tuple):
        if not isinstance(value, list):
            raise ValueError(f"{location}: expected an array")
        parameters = get_args(expected)
        if origin is tuple and len(value) != len(parameters):
            raise ValueError(f"{location}: wrong tuple length")
        for index, item in enumerate(value):
            subtype = parameters[index] if origin is tuple else parameters[0]
            validate_shape(item, subtype, f"{location}[{index}]")
        return
    if type(value) is not expected:
        raise ValueError(f"{location}: expected {expected}, got {type(value)}")


def read_inputs(
    partition_path: Path, trace_path: Path
) -> tuple[Partition, list[TraceRow]]:
    """Read and validate the fixed 286-unit input schema."""
    raw_partition: object = json.loads(partition_path.read_text(encoding="utf-8"))
    raw_trace: object = json.loads(trace_path.read_text(encoding="utf-8"))
    validate_shape(raw_partition, Partition, "partition")
    validate_shape(raw_trace, TraceDocument, "trace")
    partition = cast(Partition, raw_partition)
    trace = cast(TraceDocument, raw_trace)["trace"]
    if [unit["id"] for unit in partition["units"]] != list(range(286)):
        raise ValueError("expected exactly the ordered unit IDs 0 through 285")
    for unit in partition["units"]:
        if not 0 <= unit["row_start"] < len(trace):
            raise ValueError(f"unit {unit['id']}: row_start outside trace")
        for instruction in unit["instructions"]:
            row = instruction["row"]
            if not 0 <= row < len(trace):
                raise ValueError(f"unit {unit['id']}: instruction row outside trace")
            if instruction["word"] != trace[row]["instruction_word"]:
                raise ValueError(f"unit {unit['id']}: trace instruction mismatch")
    return partition, trace


def bv(n: int, w: int = 64) -> str:
    """Render a Lean hexadecimal bitvector literal."""
    return f"0x{n:x}#{w}"


def greg(xs: list[tuple[int, int]]) -> str:
    """Render the ordered general-register pins."""
    return "[" + ", ".join((f"({n}, {bv(v)})" for n, v in xs)) + "]"


def named(i: int) -> str:
    """Return the public trace-state name for a unit."""
    return f"traceD{i:03}"


def imp(mods: Iterable[str]) -> str:
    """Render sorted imports and the shared Lean namespace."""
    return (
        "".join((f"import {m}\n" for m in sorted(set(mods))))
        + "\nopen LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr\nnamespace Vsa.Sim.OutputAliasLoaded\n\n"
    )


@dataclass
class CertificateGenerator:
    """Render certificates without mutable process-global input paths."""

    data: Partition
    trace: list[TraceRow]
    output: Path

    @property
    def units(self) -> list[Unit]:
        """Return the complete ordered partition, including the supplied prefix."""
        return self.data["units"]

    def store_value(self, entry: Store) -> int:
        """Recover the full source register, checking its width-masked store value."""
        row = self.trace[entry["row"]]
        rs2 = row["instruction_word"] >> 20 & 31
        value = (
            0
            if rs2 == 0
            else next((x["value"] for x in row["gprs"] if x["register"] == rs2))
        )
        assert value % (1 << 8 * entry["width"]) == entry["value"]
        return value

    def base(self) -> None:
        """Write common trace data and the checked initial-state bridge."""
        s = imp(["Vsa.Sim.OutputAliasPrefix", "Vsa.Sim.OutputAliasTraceCheck"])
        s += "/- Untrusted trace data. Only checked transition theorems give it meaning. -/\n"
        s += (
            "def traceStores : List WEntry :=\n  ["
            + ",\n   ".join(
                (
                    f"(0x{x['address']:x}, {x['width']}, {bv(self.store_value(x))})"
                    for x in self.data["ordinary_store_log"]
                )
            )
            + "]\n\n"
        )
        for u in self.units:
            row = self.trace[u["row_start"]]
            out = row["output_before"]
            assert set(out) <= {"\n"}
            s += (
                f"def {named(u['id'])} : TraceData :=\n  {{ pc := {bv(u['entry_pc'])},\n    regs := {greg(u['entry_gregs'])},\n    log := traceStores.take {u['ordinary_store_prefix_start']},\n    out := #["
                + ", ".join(('"\\n"' for _ in out))
                + f"], payload := {bv(row['htif_payload_writes'], 4)} }}\n\n"
            )
        s += "theorem traceStart : ∃ c, Steps snapshotConfig c ∧ TraceHolds traceD001 c := by\n  obtain ⟨c, hs, hp⟩ := snapshot_firstTrace\n  exact ⟨c, hs, hp.rebase (by constructor <;> first | rfl | decide)⟩\n\n#print axioms traceStart\nend Vsa.Sim.OutputAliasLoaded\n"
        (self.output / "AliasTraceData.lean").write_text(s)

    def render_unit(
        self,
        i: int,
        u: Unit | None = None,
        tag: str | None = None,
        ds: str | None = None,
        de: str | None = None,
    ) -> str:
        """Render one reflected segment or explicit instruction seam."""
        u = self.units[i] if u is None else u
        tag = f"{i:03}" if tag is None else tag
        ds = named(i) if ds is None else ds
        de = named(i + 1) if de is None else de
        providers = {x["decode_batch"] for x in u["instructions"] if x["decode_batch"]}
        imports = [
            "AliasTraceData",
            "Vsa.Sim.OutputAliasCalls",
            "Vsa.Sim.OutputAliasDecode",
            "Vsa.Sim.DeriveCase",
        ] + list(providers)
        if u.get("seam_kind") == "htif_store":
            imports.append("Vsa.Sim.OutputAliasPutchar")
        if u.get("seam_kind") == "unsupported":
            imports.append("Vsa.Sim.OutputAliasTraceAlu")
        if u.get("seam_kind") == "htif_halt":
            imports.append("Vsa.Sim.OutputAliasTraceHalt")
        s = imp(imports)

        def provider(x: Instruction) -> str:
            """Select the exact instruction-word decode theorem."""
            return (
                ("DecodeTable" if x["decode_batch"] else "OutputAliasDecode")
                + ".decode_"
                + x["word_hex"]
            )

        if u["kind"] == "segment":
            seg = f"traceSeg{tag}"
            lds = f"traceLds{tag}"
            s += f"#derive_case {seg} chain\n"
            for ix, b in enumerate(u["blocks"]):
                s += (
                    "  ["
                    + ",\n   ".join(
                        (f"({bv(x['pc'])}, {bv(x['word'], 32)})" for x in b["body"])
                    )
                    + "]"
                )
                if b["terminator"]:
                    s += "\n    terminator " + b["terminator"]["decoded"]["record"]
                if ix + 1 < len(u["blocks"]):
                    s += " ;;"
                s += "\n"
            s += (
                f"\ndef {lds} : List (List (BitVec 8)) :=\n  ["
                + ",\n   ".join(
                    (
                        "[" + ", ".join((bv(b, 8) for b in x["bytes"])) + "]"
                        for x in u["loads"]
                    )
                )
                + "]\n\n"
            )
            s += f"theorem facts{tag} : ChainFacts (writeLog snapshotMem {ds}.log)\n    (writeLog snapshotMem {ds}.log) {ds}.regs {lds} {seg} := by\n"
            kinds = []
            for j, x in enumerate((x for b in u["blocks"] for x in b["body"])):
                k = f"kind{j}"
                kinds.append(k)
                s += f"  have {k} : (mkLine {bv(x['pc'])} {bv(x['word'], 32)}).kind = MKind.{x['body_kind']} := by decide\n"
            s += f"  simp only [{seg}, ChainFacts, BBlockFacts, ProgFactsM,\n    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]\n"
            s += (
                "  repeat' apply And.intro\n  all_goals first\n    | exact True.intro\n"
            )
            for p in sorted({provider(x) for x in u["instructions"]}):
                s += f"    | exact {p}\n"
            s += (
                "    | (simp only ["
                + ", ".join(kinds + ["stepMemM"])
                + ", applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)\n    | decide\n\n"
            )
            s += f"theorem run{tag} {{c : Config}} (h : TraceHolds {ds} c) :\n    ∃ c', Steps c c' ∧ TraceHolds {de} c' := by\n"
            s += f"  obtain ⟨c', hs, hp⟩ := h.segment {seg} {lds} (by decide) facts{tag} (by decide) (by decide)\n"
            if i < 96:
                s += "  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩\n"
            else:
                row_start = min((x["row"] for x in u["instructions"]))
                row_end = max((x["row"] for x in u["instructions"])) + 1
                prefix = sum(
                    (x["row"] < row_start for x in self.data["ordinary_store_log"])
                )
                end = sum((x["row"] < row_end for x in self.data["ordinary_store_log"]))
                count = end - prefix
                result = f"(evalBlocks {seg} (SegEvalState.init {ds}.regs {lds})).log"
                s += "  refine ⟨c', hs, hp.rebase ?_⟩\n"
                s += "  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }\n"
                s += f"  change traceStores.take {prefix} ++ {result} = traceStores.take {end}\n"
                s += f"  have hw : {result} = (traceStores.drop {prefix}).take {count} := by decide\n"
                s += "  rw [hw]\n"
                s += "  exact List.take_add.symm\n"
        elif u["seam_kind"] == "jal_call":
            x = u["instructions"][0]
            w = x["word"]
            bytes = [w >> 8 * k & 255 for k in range(4)]
            im = x["immediate21"]
            args = " ".join((bv(b, 8) for b in bytes))
            s += f"theorem facts{tag} : TraceCallFacts {ds} {bv(w, 32)}\n    (instruction.JAL ({bv(im, 21)}, gprIdx 1)) {args} where\n"
            for k in range(4):
                s += f"  byte{k} := by rw [snapshot_logRead]; decide\n"
            for n in ["lower", "upper", "aligned", "uncompressed", "word"]:
                s += f"  {n} := by decide\n"
            s += f"  decode := {provider(x)}\n\n"
            s += f"theorem run{tag} {{c : Config}} (h : TraceHolds {ds} c) :\n    ∃ c', Steps c c' ∧ TraceHolds {de} c' := by\n"
            s += f"  obtain ⟨c', hs, hp⟩ := h.jal {bv(w, 32)} {bv(im, 21)} {args} facts{tag} (by decide) (by decide)\n"
            s += "  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩\n"
        elif u["seam_kind"] == "jalr_call":
            x = u["instructions"][0]
            w = x["word"]
            imm = x["immediate12"]
            rs1 = x["base_register"]
            reg_values = dict(u["entry_gregs"])
            assert x["link_register"] == 1 and w >> 7 & 31 == 1
            assert w & 127 == 103 and w >> 12 & 7 == 0
            assert 1 <= rs1 <= 31 and rs1 == w >> 15 & 31
            assert imm == w >> 20 and rs1 in reg_values
            vrs1 = reg_values[rs1]
            bvals = [w >> 8 * k & 255 for k in range(4)]
            args = " ".join((bv(b, 8) for b in bvals))
            s += f"theorem facts{tag} : TraceCallFacts {ds} {bv(w, 32)}\n"
            s += f"    (instruction.JALR ({bv(imm, 12)}, gprIdx {rs1}, gprIdx 1)) {args} where\n"
            for k in range(4):
                s += f"  byte{k} := by rw [snapshot_logRead]; decide\n"
            for field in ["lower", "upper", "aligned", "uncompressed", "word"]:
                s += f"  {field} := by decide\n"
            s += f"  decode := {provider(x)}\n\n"
            s += f"theorem run{tag} {{c : Config}} (h : TraceHolds {ds} c) :\n"
            s += f"    ∃ c', Steps c c' ∧ TraceHolds {de} c' := by\n"
            s += f"  obtain ⟨c', hs, hp⟩ := h.jalr {bv(w, 32)} {bv(imm, 12)} {rs1} {bv(vrs1)}\n"
            s += f"    {args} facts{tag}\n"
            s += "    (by decide) (by decide) (by decide) (by decide) (by decide)\n"
            s += "  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩\n"
        elif u["seam_kind"] == "htif_store":
            x = u["instructions"][0]
            store = x["store"]
            reg_values = dict(u["entry_gregs"])
            assert x["pc"] == 2147483740 and x["word"] == 3405263907
            assert store["address"] == 2147593472 and store["width"] == 8
            byte = store["value"] & 255
            assert store["value"] == 72339069014638592 | byte
            assert x["htif_payload_writes"] == 0
            assert reg_values[16] == 2147594328
            assert reg_values[15] == store["value"]
            assert u["end_pc"] == 2147483744
            assert u["ordinary_store_prefix_start"] == u["ordinary_store_prefix_end"]
            s += f"theorem run{tag} {{c : Config}} (h : TraceHolds {ds} c) :\n"
            s += f"    ∃ c', Steps c c' ∧ TraceHolds {de} c' := by\n"
            s += f"  obtain ⟨c', hs, hp⟩ := h.putchar {bv(byte, 8)}\n"
            s += "    (by decide) (by decide) (by decide) (by decide)\n"
            s += "    (by decide) (by decide) (by decide) (by decide)\n"
            s += "  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩\n"
        elif u["seam_kind"] == "unsupported":
            x = u["instructions"][0]
            assert x["pc"] in [2147494108, 2147493880]
            reg = 10 if x["pc"] == 2147494108 else 11
            method = "sltiu_800028dc" if reg == 10 else "sltu_800027f8"
            value = dict(u["entry_gregs"])[reg]
            s += f"theorem run{tag} {{c : Config}} (h : TraceHolds {ds} c) :\n"
            s += f"    ∃ c', Steps c c' ∧ TraceHolds {de} c' := by\n"
            s += f"  obtain ⟨c', hs, hp⟩ := h.{method} {bv(value)}\n"
            s += "    (by decide) (by decide) (by decide)\n"
            s += "    (by decide) (by decide) (by decide) (by decide)\n"
            s += "  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩\n"
        elif u["seam_kind"] == "htif_halt":
            assert i == len(self.units) - 1
            s += f"theorem run{tag} {{c : Config}} (h : TraceHolds {ds} c) :\n"
            s += '    ∃ σf, Halted c 0 σf ∧ σf.sailOutput = #["\\n", "\\n"] := by\n'
            s += "  exact h.halted0 (by decide) (by decide) (by decide) (by decide)\n"
            s += "    (by decide) (by decide) (by decide) (by decide)\n"
        else:
            raise ValueError(u.get("seam_kind"))
        s += f"\n#print axioms run{tag}\nend Vsa.Sim.OutputAliasLoaded\n"
        return s

    def row_data(self, name: str, rowno: int) -> str:
        """Render a state at an internal segment subdivision."""
        row = self.trace[rowno]
        pins = [(x["register"], x["value"]) for x in row["gprs"]]
        assert all((x["present"] for x in row["gprs"]))
        prefix = sum((x["row"] < rowno for x in self.data["ordinary_store_log"]))
        out = row["output_before"]
        assert set(out) <= {"\n"}
        return (
            f"def {name} : TraceData :=\n  {{ pc := {bv(row['pc'])},\n    regs := {greg(pins)},\n    log := traceStores.take {prefix},\n    out := #["
            + ", ".join(('"\\n"' for _ in out))
            + f"], payload := {bv(row['htif_payload_writes'], 4)} }}\n\n"
        )

    def unit(self, i: int) -> None:
        """Write a public unit, subdividing long segments at established limits."""
        u = self.units[i]
        # These bounds keep the generated proofs within default Lean limits.
        direct_limit = 8 if i == 193 or i >= 210 else 16
        body_limit = 4 if i == 193 or i >= 210 else 8
        if u["kind"] != "segment" or u["count"] <= direct_limit:
            s = self.render_unit(i)
        else:
            chunks = []
            for b in u["blocks"]:
                body = b["body"]
                while len(body) > body_limit:
                    chunks.append({"body": body[:body_limit], "terminator": None})
                    body = body[body_limit:]
                chunks.append({"body": body, "terminator": b["terminator"]})
            parts = []
            imports = set()
            states = []
            for j, b in enumerate(chunks):
                rows = [x["row"] for x in b["body"]]
                if b["terminator"]:
                    rows.append(b["terminator"]["row"])
                assert rows
                instructions = [x for x in u["instructions"] if x["row"] in rows]
                assert len(instructions) == len(rows)
                ds = named(i) if j == 0 else f"traceD{i:03}_{j:02}"
                de = (
                    named(i + 1) if j == len(chunks) - 1 else f"traceD{i:03}_{j + 1:02}"
                )
                if j:
                    states.append(self.row_data(ds, rows[0]))
                sub = {
                    **u,
                    "blocks": [b],
                    "instructions": instructions,
                    "loads": [x["load"] for x in instructions if x.get("load")],
                }
                part = self.render_unit(i, sub, f"{i:03}_{j:02}", ds, de)
                imports.update(
                    (
                        line[7:]
                        for line in part.splitlines()
                        if line.startswith("import ")
                    )
                )
                part = part.split("namespace Vsa.Sim.OutputAliasLoaded\n", 1)[1]
                part = part.rsplit("end Vsa.Sim.OutputAliasLoaded", 1)[0]
                parts.append(part)
            s = imp(imports) + "".join(states) + "".join(parts)
            s += f"theorem run{i:03} {{c : Config}} (h : TraceHolds {named(i)} c) :\n"
            s += f"    ∃ c', Steps c c' ∧ TraceHolds {named(i + 1)} c' := by\n"
            for j in range(len(chunks)):
                prev = "h" if j == 0 else f"h{j - 1}"
                s += f"  obtain ⟨c{j}, s{j}, h{j}⟩ := run{i:03}_{j:02} {prev}\n"
            chain = "s0"
            for j in range(1, len(chunks)):
                chain = f"({chain}).trans s{j}"
            last = len(chunks) - 1
            s += f"  exact ⟨c{last}, {chain}, h{last}⟩\n"
            s += f"\n#print axioms run{i:03}\nend Vsa.Sim.OutputAliasLoaded\n"
        (self.output / f"AliasTrace{i:03}.lean").write_text(s)


def main() -> None:
    """Generate common data and selected units; defaults to all 285 proofs."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--partition", required=True, type=Path)
    parser.add_argument("--trace", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument(
        "units", nargs="*", type=int, help="unit IDs 1–285; default all"
    )
    args = parser.parse_args()
    selection = args.units or list(range(1, 286))
    if len(set(selection)) != len(selection) or any(
        not 1 <= i <= 285 for i in selection
    ):
        parser.error("unit IDs must be unique and between 1 and 285")
    partition, trace = read_inputs(args.partition, args.trace)
    generator = CertificateGenerator(partition, trace, args.output)
    # Validate every full-width store before the first output write.
    for store in partition["ordinary_store_log"]:
        generator.store_value(store)
    args.output.mkdir(parents=True, exist_ok=True)
    generator.base()
    for i in selection:
        generator.unit(i)
    print(f"Generated Data and {len(selection)} unit files in {args.output}")


if __name__ == "__main__":
    main()
