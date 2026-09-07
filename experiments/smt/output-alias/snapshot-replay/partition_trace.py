#!/usr/bin/env python3
"""Partition untrusted Sail rows for SegEvalSound and explicit seam proofs.

Usage: python3 partition_trace.py --repo REPO --trace result.jsonl --output segments.json
No instruction is rewritten. genseg.lib supplies disassembly and terminator decoding.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

MASK64 = (1 << 64) - 1
TOHOST = 0x8001AD00
RAM_LO = 0x80000000
RAM_HI = 0x100000000


def require(test: bool, message: str) -> None:
    if not test:
        raise ValueError(message)


def integer(value: object, label: str) -> int:
    require(type(value) is int, f"{label}: expected integer")
    return int(value)


def object_value(value: object, label: str) -> dict[str, object]:
    require(isinstance(value, dict), f"{label}: expected object")
    require(all(isinstance(k, str) for k in value), f"{label}: nonstring key")
    return value


def list_value(value: object, label: str) -> list[object]:
    require(isinstance(value, list), f"{label}: expected array")
    return value


def gregs(value: object) -> tuple[int, ...]:
    items = list_value(value, "gprs")
    require(len(items) == 31, "expected all 31 GPRs")
    values = [0]
    for index, item in enumerate(items, 1):
        record = object_value(item, "gpr")
        require(record["register"] == index and record["present"] is True,
                f"GPR x{index} absent or out of order")
        v = integer(record["value"], "gpr value")
        require(0 <= v <= MASK64, "GPR outside uint64")
        values.append(v)
    return tuple(values)


def pins(values: tuple[int, ...]) -> list[list[int]]:
    return [[n, values[n]] for n in range(1, 32)]


@dataclass(frozen=True)
class Row:
    index: int
    pc: int
    word: int
    regs: tuple[int, ...]
    successor: int
    output_changed: bool
    load_address: int | None
    load_bytes: tuple[int, ...]
    load_present: tuple[bool, ...]
    payload_count: int

    @classmethod
    def parse(cls, index: int, raw: object) -> Row:
        d = object_value(raw, "row")
        require(d["steps"] == index, "trace steps must start at zero and be contiguous")
        word = integer(d["instruction_word"], "instruction word")
        pc = integer(d["pc"], "PC")
        raw_bytes = list_value(d["instruction_bytes"], "instruction bytes")
        require(len(raw_bytes) == 4 and word & 3 == 3, "requires four-byte instructions")
        for offset, raw_byte in enumerate(raw_bytes):
            byte = object_value(raw_byte, "instruction byte")
            require(byte["address"] == pc + offset and byte["present"] is True,
                    "instruction byte absent or misaddressed")
            require(byte["effective"] == (word >> (8 * offset)) & 255,
                    "instruction word differs from traced bytes")
        load_address = None
        values: list[int] = []
        present: list[bool] = []
        if d["load"] is not None:
            load = object_value(d["load"], "load")
            load_address = integer(load["address"], "load address")
            for offset, raw_byte in enumerate(list_value(load["bytes"], "load bytes")):
                byte = object_value(raw_byte, "load byte")
                require(byte["address"] == load_address + offset, "bad load byte address")
                value = integer(byte["effective"], "load byte value")
                require(0 <= value < 256 and type(byte["present"]) is bool, "bad load byte")
                require(byte["present"] or value == 0, "absent byte must read zero")
                values.append(value)
                present.append(byte["present"])
            require(load["width"] == len(values), "bad load width")
        return cls(index, pc, word, gregs(d["gprs"]), integer(d["next_pc"], "next PC"),
                   d["output_changed"] is True, load_address, tuple(values), tuple(present),
                   integer(d["htif_payload_writes"], "payload count"))


def body_kind(word: int) -> str | None:
    """Conservative shape census matching current BlockDecode.decodeM.

    This annotation is not a decoder proof. Lean must check mkLine/ChainOK.
    """
    op, f3, f7, f6 = word & 127, (word >> 12) & 7, word >> 25, word >> 26
    if op == 0x13:
        if f3 == 5:
            return {0: "srli", 16: "srai"}.get(f6)
        return {0: "addi", 1: "slli", 2: "slti", 4: "xori", 6: "ori", 7: "andi"}.get(f3)
    if op == 0x33:
        if f3 == 0:
            return {0: "add", 32: "sub"}.get(f7)
        if f3 == 2:
            return "slt"
        return {1: "sll", 4: "xor", 5: "srl", 6: "or", 7: "and"}.get(f3) if f7 == 0 else None
    if op == 3:
        return {1: "lh", 2: "lw", 3: "ld", 4: "lbu", 5: "lhu", 6: "lwu"}.get(f3)
    if op == 0x23:
        return {0: "sb", 1: "sh", 2: "sw", 3: "sd"}.get(f3)
    if op == 0x1B:
        if f3 == 5:
            return {0: "srliw", 32: "sraiw"}.get(f7)
        return {0: "addiw", 1: "slliw"}.get(f3)
    if op == 0x3B:
        if f3 == 0:
            return {0: "addw", 32: "subw"}.get(f7)
        if f3 == 5:
            return {0: "srlw", 32: "sraw"}.get(f7)
        return "sllw" if f3 == 1 and f7 == 0 else None
    return {0x17: "auipc", 0x37: "lui"}.get(op)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def partition(repo: Path, trace_path: Path) -> dict[str, object]:
    spec = importlib.util.spec_from_file_location("genseg_trace_lib", repo / "scripts/genseg/lib.py")
    require(spec is not None and spec.loader is not None, "cannot load genseg.lib")
    lib = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(lib)
    disasm = lib.parse_disasm(str(repo / "experiments/disasm.txt"))
    index = lib.DecodeIndex(str(repo / "scripts/decode_index.tsv"))
    data = object_value(json.loads(trace_path.read_text()), "trace document")
    require(data["halted"] is True and data["exit_code"] == 0, "expected actual successful halt")
    rows = [Row.parse(i, raw) for i, raw in enumerate(list_value(data["trace"], "trace"))]
    require(len(rows) == data["steps"] and bool(rows), "incomplete trace")
    final = object_value(data["final_full_state"], "final state")
    final_regs = gregs(final["gprs"])
    final_pc = integer(final["pc"], "final PC")
    for row in rows:
        require(row.successor == (rows[row.index + 1].pc if row.index + 1 < len(rows) else final_pc),
                f"broken successor at {row.index}")
        require(row.pc in disasm and disasm[row.pc].word == row.word,
                f"actual instruction differs from disassembly at {row.pc:#x}")

    units: list[dict[str, object]] = []
    unsupported: list[dict[str, object]] = []
    missing_decode_table: list[dict[str, object]] = []
    ordinary_stores: list[dict[str, object]] = []
    absent_loads: list[dict[str, object]] = []
    current_rows: list[dict[str, object]] = []
    blocks: list[dict[str, object]] = []
    body: list[dict[str, object]] = []
    segment_store_start = 0

    def finish_block(terminator: dict[str, object] | None = None) -> None:
        nonlocal body
        if body or terminator is not None:
            blocks.append({"body": body, "terminator": terminator})
            body = []

    def append_unit(kind: str, records: list[dict[str, object]], **extra: object) -> None:
        first, last = int(records[0]["row"]), int(records[-1]["row"])
        end_regs = rows[last + 1].regs if last + 1 < len(rows) else final_regs
        units.append({"id": len(units), "kind": kind, "row_start": first, "row_end": last + 1,
                      "count": last + 1 - first, "entry_pc": rows[first].pc,
                      "end_pc": rows[last].successor, "entry_gregs": pins(rows[first].regs),
                      "end_gregs": pins(end_regs), "instructions": records, **extra})

    def flush_segment() -> None:
        nonlocal current_rows, blocks, segment_store_start
        finish_block()
        if current_rows:
            append_unit("segment", current_rows, blocks=blocks,
                        loads=[r["load"] for r in current_rows if r["load"] is not None],
                        ordinary_store_log=ordinary_stores[segment_store_start:],
                        ordinary_store_prefix_start=segment_store_start,
                        ordinary_store_prefix_end=len(ordinary_stores))
        current_rows, blocks = [], []
        segment_store_start = len(ordinary_stores)

    for row in rows:
        w, ins = row.word, disasm[row.pc]
        op, rd, rs1, rs2, f3 = w & 127, (w >> 7) & 31, (w >> 15) & 31, (w >> 20) & 31, (w >> 12) & 7
        record: dict[str, object] = {"row": row.index, "pc": row.pc, "word": w,
            "word_hex": f"{w:08x}", "mnemonic": ins.mnem, "operands": ins.ops,
            "decode_batch": index.batch(w), "load": None, "store": None,
            "successor_pc": row.successor, "htif_payload_writes": row.payload_count}
        reasons: list[str] = []
        if not index.has(w):
            missing_decode_table.append({"row": row.index, "pc": row.pc, "word": w})
            record["decode_table_obligation"] = "missing table entry; prove DecodeFact separately"
        if op == 3:
            width = {0: 1, 1: 2, 2: 4, 3: 8, 4: 1, 5: 2, 6: 4}.get(f3)
            address = (row.regs[rs1] + lib.sext(w >> 20, 12)) & MASK64
            require(width is not None and address == row.load_address and width == len(row.load_bytes),
                    f"load annotation disagrees with encoding at row {row.index}")
            geometry = {"ram": RAM_LO <= address and address + width <= RAM_HI,
                        "htif_disjoint": address + width <= TOHOST or TOHOST + 8 <= address,
                        "aligned": address % width == 0}
            record["load"] = {"row": row.index, "address": address, "width": width,
                "bytes": list(row.load_bytes), "present": list(row.load_present), "geometry": geometry}
            if not (geometry["ram"] and geometry["htif_disjoint"]):
                reasons.append("load_geometry")
            if not all(row.load_present):
                absent_loads.append({"row": row.index, "pc": row.pc, "address": address,
                                     "width": width, "absent_count": row.load_present.count(False)})
        else:
            require(row.load_address is None, "load annotation on non-LOAD instruction")
        store: dict[str, object] | None = None
        if op == 0x23:
            width = {0: 1, 1: 2, 2: 4, 3: 8}.get(f3)
            require(width is not None, f"unsupported store width at row {row.index}")
            imm = ((w >> 25) << 5) | ((w >> 7) & 31)
            address = (row.regs[rs1] + lib.sext(imm, 12)) & MASK64
            value = row.regs[rs2] & ((1 << (8 * width)) - 1)
            store = {"row": row.index, "address": address, "width": width, "value": value,
                     "bytes": [(value >> (8 * j)) & 255 for j in range(width)]}
            record["store"] = store
            if not (RAM_LO <= address and address + width <= RAM_HI and address % width == 0):
                reasons.append("store_geometry")
        final_row = row.index == len(rows) - 1
        seam_kind = None
        if op in (0x6F, 0x67) and rd != 0:
            seam_kind = "jal_call" if op == 0x6F else "jalr_call"
            record["link_register"] = rd
            record["link_value"] = (row.pc + 4) & MASK64
            if op == 0x6F:
                immediate = lib._jal_imm(w)
                target = (row.pc + lib.sext(immediate, 21)) & MASK64
                record["immediate21"] = immediate
            else:
                base_reg, immediate = lib._jalr_fields(w)
                target = ((row.regs[base_reg] + lib.sext(immediate, 12)) & MASK64) & ~1
                record["base_register"] = base_reg
                record["immediate12"] = immediate
            require(row.successor == target, "call successor disagrees with encoding")
            record["target"] = target
            post_regs = rows[row.index + 1].regs if not final_row else final_regs
            require(post_regs[rd] == record["link_value"], "call link register mismatch")
        elif store is not None and int(store["address"]) < TOHOST + 16:
            seam_kind = "low_store"
            if store["address"] == TOHOST:
                seam_kind = "htif_halt" if final_row else "htif_store"
            record["memory_effect"] = "requires explicit machine seam; encoded store is not an ordinary RAM log"
        elif final_row:
            seam_kind = "final_halt"
        if seam_kind is None and op not in (0x63, 0x6F, 0x67):
            kind = body_kind(w)
            record["body_kind"] = kind
            record["lean_body"] = f"mkLine {lib.bv64(row.pc)} {lib.bv32(w)}"
            if kind is None:
                reasons.append("unsupported_decodeM_shape")
            if op != 0x23 and rd == 0:
                reasons.append("body_destination_x0_KindOK")
        if reasons:
            unsupported.append({"row": row.index, "pc": row.pc, "word": w, "reasons": reasons})
            seam_kind = seam_kind or "unsupported"
        if row.output_changed and seam_kind is None:
            raise ValueError(f"ordinary segment changes output at row {row.index}")
        if seam_kind is not None:
            flush_segment()
            append_unit("seam", [record], seam_kind=seam_kind, obligations=reasons,
                        final_step_is_halted=final_row,
                        result_kind="Halted" if final_row else "Step",
                        ordinary_store_prefix_start=len(ordinary_stores),
                        ordinary_store_prefix_end=len(ordinary_stores))
            continue
        current_rows.append(record)
        if op in (0x63, 0x6F, 0x67):
            if op == 0x63:
                taken_term = lib.decode_terminator(ins, taken=True)
                fall_term = lib.decode_terminator(ins, taken=False)
                require(row.successor in (taken_term["target"], fall_term["target"]), "invalid branch successor")
                require(taken_term["target"] != fall_term["target"], "ambiguous branch polarity")
                term = taken_term if row.successor == taken_term["target"] else fall_term
            else:
                term = lib.decode_terminator(ins)
                if term["kind"] == "jr":
                    target = ((row.regs[term["rs1"]] + lib.sext(term["imm12"], 12)) & MASK64) & ~1
                    require(row.successor == target, "invalid indirect jump successor")
                    term["observed_target"] = target
                else:
                    require(row.successor == term["target"], "invalid jump successor")
            record["terminator"] = term
            finish_block({"row": row.index, "decoded": term, "pre_gregs": pins(row.regs)})
            if op == 0x67:
                flush_segment()
        else:
            require(row.successor == (row.pc + 4) & MASK64, "ordinary body not sequential")
            body.append(record)
            if store is not None:
                ordinary_stores.append(store)
    flush_segment()
    covered = [i for unit in units for i in range(int(unit["row_start"]), int(unit["row_end"]))]
    require(covered == list(range(len(rows))), "partition does not cover each row once in order")
    require(units[-1]["kind"] == "seam" and units[-1]["final_step_is_halted"] is True,
            "final step must be handled by Halted, not Steps")
    return {"schema": "vsa-trace-segments-v1", "trusted": False, "lean_proofs_compiled": False,
        "generator_sha256": sha(Path(__file__)), "source_trace_sha256": sha(trace_path), "decoder_sha256": sha(repo / "scripts/genseg/lib.py"),
        "disasm_sha256": sha(repo / "experiments/disasm.txt"),
        "block_decode_sha256": sha(repo / "Vsa/Sim/BlockDecode.lean"),
        "trace_rows": len(rows), "coverage_complete_ordered_exactly_once": True,
        "summary": dict(Counter(str(u.get("seam_kind", u["kind"])) for u in units)),
        "unsupported": unsupported, "missing_decode_table": missing_decode_table,
        "absent_sparse_loads": absent_loads,
        "ordinary_store_log": ordinary_stores, "units": units,
        "final_state": final, "exit_code": data["exit_code"],
        "note": "Untrusted certificate data. Keep all row words unchanged. Lean must check ChainFacts/ChainOK and every explicit seam. The final row proves Halted, not Step."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--trace", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = partition(args.repo.resolve(), args.trace)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"rows": result["trace_rows"], "units": result["summary"],
                      "unsupported": result["unsupported"],
                      "missing_decode_table_rows": len(result["missing_decode_table"]),
                      "ordinary_stores": len(result["ordinary_store_log"])}, indent=2))


if __name__ == "__main__":
    main()
