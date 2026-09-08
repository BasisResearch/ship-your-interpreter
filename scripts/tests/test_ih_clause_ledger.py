"""Tests for the clause-field evidence ledger."""

import io
import json
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

from scripts import ih_clause_ledger as ledger
from scripts import residual_coverage_ledger as base

STATUS_HEADER = ("clause", "field", "status", "hook_backend", "census", "evidence")


class LedgerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        base._write_tsv(self.root / "ih_clause_status.tsv", STATUS_HEADER, [
            ("T", "hInt", "WIRED", "", "FOUND", "T.lean:10"),
            ("T", "hStr", "HOOK", "missing", "", ""),
            ("T", "hVar", "HOOK", "exists", "", ""),
            ("T", "hFn", "MANUAL", "", "", ""),
        ])
        (self.root / "ih_clause_status.json").write_text(json.dumps(
            {"clauses": {"T": {"pred": "ownExtra", "notes": "shared-byte ownership clause"}}}))

    def cells(self, **kwargs):
        built = ledger.build(self.root, **kwargs)
        return {(c["field"], c["kind"]): c for c in built["cells"]}, built

    def test_status_only_marks_lean_bridge_and_holes(self) -> None:
        cells, built = self.cells()
        self.assertEqual(built["cell_count"], 16)
        self.assertTrue(cells[("hInt", "lean-bridge")]["covered"])
        self.assertEqual(cells[("hInt", "lean-bridge")]["verdict"], "wired:census-FOUND")
        self.assertEqual(cells[("hInt", "lean-bridge")]["evidence"], "T.lean:10")
        self.assertTrue(cells[("hVar", "lean-bridge")]["covered"])
        self.assertEqual(cells[("hVar", "lean-bridge")]["verdict"], "hook-lemma")
        self.assertFalse(cells[("hStr", "lean-bridge")]["covered"])
        self.assertEqual(cells[("hStr", "lean-bridge")]["hole"], ledger.HOLES["lean-bridge"])
        for kind in ("execution", "smt", "oracle"):
            self.assertFalse(cells[("hInt", kind)]["covered"])
            self.assertEqual(cells[("hInt", kind)]["hole"], ledger.HOLES[kind])
        self.assertEqual(cells[("hInt", "smt")]["dimensions"], "memory-ownership")
        self.assertEqual(built["covered"], {"execution": 0, "smt": 0, "oracle": 0,
                                            "lean-bridge": 2})

    def test_fuzz_suggest_and_execution_artifacts(self) -> None:
        base._write_tsv(self.root / "ih_clause_fuzz.tsv",
                        ("clause", "field", "verdict", "detail", "evidence"), [
                            ("T", "hInt", "NOT-REFUTED", "wiring", "T.lean:10"),
                            ("T", "hStr", "UNSUPPORTED", "outside fragment", ""),
                            ("T", "hFn", "REFUTED", "witness", "probe.log"),
                        ])
        base._write_tsv(self.root / "ih_clause_suggest.tsv",
                        ("clause", "field", "outcome", "lean_candidate", "houdini",
                         "autoprove", "draft", "evidence"), [
                            ("T", "hStr", "DIRECT", "from_old:x", "ENCODE-GAP: y",
                             "ENCODE-GAP: y", "Draft_T.lean", "Draft_T.log"),
                            ("T", "hFn", "WITH-IH", "", "IH-FOUND: s", "ENCODE-GAP: y",
                             "Draft_T.lean", ""),
                        ])
        execution = self.root / "exec.tsv"
        base._write_tsv(execution, ("clause", "field", "verdict", "evidence"),
                        [("T", "hInt", "TRACE-AGREES", "trace.json")])
        cells, built = self.cells(execution=execution)
        self.assertTrue(cells[("hInt", "smt")]["covered"])
        self.assertEqual(cells[("hFn", "smt")]["verdict"], "REFUTED")
        self.assertFalse(cells[("hStr", "smt")]["covered"])
        self.assertEqual(cells[("hStr", "smt")]["hole"], "outside fragment")
        self.assertTrue(cells[("hStr", "lean-bridge")]["covered"])
        self.assertEqual(cells[("hStr", "lean-bridge")]["verdict"], "draft:from_old:x")
        self.assertEqual(cells[("hStr", "lean-bridge")]["evidence"], "Draft_T.log")
        self.assertFalse(cells[("hStr", "oracle")]["covered"])
        self.assertTrue(cells[("hFn", "oracle")]["covered"])
        self.assertEqual(cells[("hFn", "oracle")]["verdict"], "IH-FOUND")
        self.assertFalse(cells[("hFn", "lean-bridge")]["covered"])
        self.assertTrue(cells[("hInt", "execution")]["covered"])
        self.assertFalse(cells[("hStr", "execution")]["covered"])
        tsv, js = self.root / "out.tsv", self.root / "out.json"
        ledger.write_outputs(built, tsv, js)
        lines = tsv.read_text().splitlines()
        self.assertEqual(lines[0].split("\t"), list(ledger.COLUMNS))
        self.assertEqual(len(lines), 17)
        self.assertIn("\tyes\t", lines[1])
        self.assertEqual(json.loads(js.read_text())["covered"]["smt"], 2)

    def test_inconsistent_artifacts_are_rejected(self) -> None:
        base._write_tsv(self.root / "ih_clause_fuzz.tsv", ("clause", "field", "verdict"),
                        [("T", "hNope", "REFUTED")])
        with self.assertRaisesRegex(ledger.ClauseLedgerError, "unknown fields"):
            ledger.build(self.root)
        base._write_tsv(self.root / "ih_clause_fuzz.tsv", ("clause", "field", "verdict"),
                        [("T", "hInt", "REFUTED"), ("T", "hInt", "REFUTED")])
        with self.assertRaisesRegex(ledger.ClauseLedgerError, "duplicate"):
            ledger.build(self.root)
        (self.root / "ih_clause_fuzz.tsv").unlink()
        base._write_tsv(self.root / "ih_clause_suggest.tsv", ("clause", "outcome"), [])
        with self.assertRaisesRegex(ledger.ClauseLedgerError, "missing columns"):
            ledger.build(self.root)
        (self.root / "ih_clause_status.tsv").unlink()
        with self.assertRaisesRegex(ledger.ClauseLedgerError, "run ih_clause_status"):
            ledger.build(self.root)

    def test_main(self) -> None:
        captured = io.StringIO()
        with redirect_stdout(captured):
            code = ledger.main(["build", "--dir", str(self.root)])
        self.assertEqual(code, 0)
        self.assertIn("IH clause ledger: 4 field(s)", captured.getvalue())
        self.assertTrue((self.root / "ih_clause_ledger.tsv").is_file())
        (self.root / "ih_clause_status.tsv").unlink()
        with redirect_stdout(io.StringIO()):
            self.assertEqual(ledger.main(["build", "--dir", str(self.root)]), 2)


if __name__ == "__main__":
    unittest.main()
