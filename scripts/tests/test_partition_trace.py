"""Trace classification regressions. Synthetic rows are not execution certificates."""

import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "experiments/smt/output-alias/snapshot-replay/partition_trace.py"
SPEC = importlib.util.spec_from_file_location("partition_trace_under_test", SOURCE)
assert SPEC is not None and SPEC.loader is not None
partition_trace = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = partition_trace
SPEC.loader.exec_module(partition_trace)


class PartitionTraceTests(unittest.TestCase):
    def setUp(self) -> None:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.repo = Path(directory.name)
        for relative in ("scripts/genseg/lib.py", "Vsa/Sim/BlockDecode.lean"):
            target = self.repo / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(ROOT / relative)
        (self.repo / "experiments").mkdir()

    def classify(
        self, mnemonic: str, funct3: int, address: int, *, store: bool = False
    ) -> dict[str, Any]:
        width = 1 << (funct3 & 3)
        word = (
            ((2 << 20) | (1 << 15) | (funct3 << 12) | 0x23)
            if store
            else ((1 << 15) | (funct3 << 12) | (2 << 7) | 3)
        )
        pc = 0x80000100
        final_word = 0x00000193  # addi x3,x0,0; synthetic final row for classification.
        (self.repo / "experiments/disasm.txt").write_text(
            f"{pc:x}: {word:08x} {mnemonic} x2,0(x1)\n"
            f"{pc + 4:x}: {final_word:08x} addi x3,x0,0\n"
        )
        (self.repo / "scripts/decode_index.tsv").write_text(
            f"{word:08x}\tTest\n{final_word:08x}\tTest\n"
        )
        registers = [
            {"register": index, "present": True, "value": address if index == 1 else 0}
            for index in range(1, 32)
        ]
        rows = []
        for index, instruction in enumerate((word, final_word)):
            row_pc = pc + 4 * index
            rows.append(
                {
                    "steps": index,
                    "pc": row_pc,
                    "instruction_word": instruction,
                    "next_pc": row_pc + 4,
                    "gprs": registers,
                    "instruction_bytes": [
                        {
                            "address": row_pc + offset,
                            "present": True,
                            "effective": (instruction >> (8 * offset)) & 255,
                        }
                        for offset in range(4)
                    ],
                    "load": {
                        "address": address,
                        "width": width,
                        "bytes": [
                            {
                                "address": address + offset,
                                "present": False,
                                "effective": 0,
                            }
                            for offset in range(width)
                        ],
                    }
                    if index == 0 and not store
                    else None,
                    "output_changed": False,
                    "htif_payload_writes": 0,
                }
            )
        trace = self.repo / "trace.json"
        trace.write_text(
            json.dumps(
                {
                    "halted": True,
                    "exit_code": 0,
                    "steps": len(rows),
                    "trace": rows,
                    "final_full_state": {"gprs": registers, "pc": pc + 8},
                }
            )
        )
        return partition_trace.partition(self.repo, trace)

    def test_unaligned_and_page_crossing_sparse_loads_form_segments(self) -> None:
        for mnemonic, funct3 in (
            ("lh", 1),
            ("lw", 2),
            ("ld", 3),
            ("lhu", 5),
            ("lwu", 6),
        ):
            for address in (0x80020001, 0x80020FFF):
                with self.subTest(mnemonic=mnemonic, address=address):
                    result = self.classify(mnemonic, funct3, address)
                    self.assertEqual(result["unsupported"], [])
                    self.assertEqual(result["units"][0]["kind"], "segment")
                    load = result["units"][0]["loads"][0]
                    self.assertFalse(load["geometry"]["aligned"])
                    self.assertEqual(
                        result["absent_sparse_loads"][0]["absent_count"], load["width"]
                    )
                    self.assertTrue(result["coverage_complete_ordered_exactly_once"])
                    self.assertFalse(result["trusted"])
                    self.assertFalse(result["lean_proofs_compiled"])

    def test_unaligned_stores_remain_seams(self) -> None:
        for mnemonic, funct3 in (("sh", 1), ("sw", 2), ("sd", 3)):
            with self.subTest(mnemonic=mnemonic):
                result = self.classify(mnemonic, funct3, 0x80020001, store=True)
                self.assertEqual(result["units"][0]["kind"], "seam")
                self.assertEqual(
                    result["unsupported"][0]["reasons"], ["store_geometry"]
                )
                self.assertEqual(result["ordinary_store_log"], [])

    def test_loads_outside_ram_or_overlapping_htif_remain_seams(self) -> None:
        for address in (0x4000, 0xFFFFFFFD, partition_trace.TOHOST - 1):
            with self.subTest(address=address):
                result = self.classify("lw", 2, address)
                self.assertEqual(result["units"][0]["kind"], "seam")
                self.assertEqual(result["unsupported"][0]["reasons"], ["load_geometry"])


if __name__ == "__main__":
    unittest.main()
