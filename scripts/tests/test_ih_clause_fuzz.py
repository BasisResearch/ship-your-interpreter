"""Tests for the clause-step refutation driver."""

import io
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest.mock import patch

from scripts import build_private
from scripts import ih_clause_fuzz as fuzz
from scripts import ih_clause_model as model


class FuzzFieldTests(unittest.TestCase):
    def setUp(self) -> None:
        loaded = model.load_model()
        self.trivial = loaded["Trivial"]
        self.footprint = loaded["Footprint"]

    def test_wired_field_is_not_refuted_with_module_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            row = fuzz.fuzz_field(self.trivial, self.trivial.field("hInt"), Path(directory),
                                  None, False)
            self.assertEqual(row["verdict"], "NOT-REFUTED")
            self.assertEqual(row["engine"], "lean-wiring")
            self.assertTrue(row["evidence"].startswith(self.trivial.path + ":"))
            statement = Path(row["statement"])
            self.assertTrue(statement.is_file())
            self.assertIn("def Step_hInt (_L : Layout) : Prop :=", statement.read_text())

    def test_unwired_field_is_unsupported_by_fragment(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            row = fuzz.fuzz_field(self.footprint, self.footprint.field("hCall"),
                                  Path(directory), None, False)
            self.assertEqual(row["verdict"], "UNSUPPORTED")
            self.assertEqual(row["engine"], "fragment")
            self.assertIn("outside the address-map fragment", row["detail"])
            row = fuzz.fuzz_field(self.footprint, self.footprint.field("hCall"),
                                  Path(directory), Path("/backend"), False)
            self.assertEqual(row["engine"], "fragment")

    def test_lean_mode_maps_fuzzer_verdicts(self) -> None:
        expected = {"REFUTED": "REFUTED", "INCONCLUSIVE": "NOT-REFUTED",
                    "UNDECIDABLE": "UNSUPPORTED", "BACKEND-INVALID": "UNSUPPORTED"}
        for raw, verdict in expected.items():
            with self.subTest(raw=raw), tempfile.TemporaryDirectory() as directory, \
                    patch.object(fuzz, "run_fuzzer", return_value=(raw, f"statement_fuzz: {raw}")):
                row = fuzz.fuzz_field(self.footprint, self.footprint.field("hVar"),
                                      Path(directory), Path("/backend"), True)
                self.assertEqual(row["verdict"], verdict)
                self.assertEqual(row["engine"], "statement_fuzz")
                self.assertIn(raw, row["detail"])
                self.assertTrue(row["evidence"].endswith("Footprint_hVar.fuzz.log"))

    def test_run_fuzzer_refuses_stale_backend(self) -> None:
        with patch("scripts.check_validation.verify_backend",
                   side_effect=build_private.BuildError("stale private backend: X")):
            verdict, detail = fuzz.run_fuzzer(Path("/s.lean"), "P", Path("/backend"),
                                              Path("/log"))
        self.assertEqual(verdict, "BACKEND-INVALID")
        self.assertIn("stale private backend", detail)


class MainTests(unittest.TestCase):
    def test_main_writes_artifacts_and_exit_codes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            with redirect_stdout(io.StringIO()):
                code = fuzz.main(["--output", directory])
            self.assertEqual(code, 0)
            rows = (Path(directory) / "ih_clause_fuzz.tsv").read_text().splitlines()
            self.assertEqual(rows[0].split("\t"), list(fuzz.COLUMNS))
            fields = sum(len(i.fields) for i in model.load_model().values())
            self.assertEqual(len(rows), fields + 1)
            self.assertEqual(len(list((Path(directory) / "statements").glob("*.lean"))), fields)
            with redirect_stdout(io.StringIO()):
                self.assertEqual(fuzz.main(["--output", directory, "--field", "hNope"]), 2)
            with patch.object(fuzz, "fuzz_field", return_value={
                    "clause": "Trivial", "field": "hInt", "status": "WIRED",
                    "verdict": "REFUTED", "engine": "x", "detail": "", "statement": "",
                    "evidence": "e"}), redirect_stdout(io.StringIO()):
                self.assertEqual(fuzz.main(["--output", directory, "--clause", "Trivial",
                                            "--field", "hInt"]), 1)

    def test_lean_requires_backend(self) -> None:
        with self.assertRaises(SystemExit):
            fuzz.main(["--lean"])


if __name__ == "__main__":
    unittest.main()
