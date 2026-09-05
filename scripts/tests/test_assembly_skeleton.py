"""Regression checks for inherited assembly-record fields."""

import contextlib
import io
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from experiments import gen_assembly_skeleton


class AssemblySkeletonTests(unittest.TestCase):
    """Keep the generated assembly aligned with its inherited source record."""

    def test_core_includes_base_fields_once(self) -> None:
        _, base = gen_assembly_skeleton.parse("TermResidualsBase")
        _, core = gen_assembly_skeleton.parse()
        base_names = [name for name, _, _ in base]
        core_names = [name for name, _, _ in core]
        self.assertEqual(core_names, [*base_names, "hDivCorr"])
        self.assertEqual(len(core_names), len(set(core_names)))
        self.assertIn("hSeqSteps", core_names)
        self.assertNotIn("hSeqNil", core_names)

    def test_generated_artifacts_match_source(self) -> None:
        expected_lean = Path(gen_assembly_skeleton.OUT).read_text(encoding="utf-8")
        expected_tsv = Path(gen_assembly_skeleton.TSV).read_text(encoding="utf-8")
        with tempfile.TemporaryDirectory() as directory:
            lean = Path(directory) / "AssemblySkeleton.lean"
            ledger = Path(directory) / "assembly_skeleton.tsv"
            with (
                patch.object(gen_assembly_skeleton, "OUT", str(lean)),
                patch.object(gen_assembly_skeleton, "TSV", str(ledger)),
                contextlib.redirect_stdout(io.StringIO()),
            ):
                gen_assembly_skeleton.emit(*gen_assembly_skeleton.parse())
            self.assertEqual(lean.read_text(encoding="utf-8"), expected_lean)
            self.assertEqual(ledger.read_text(encoding="utf-8"), expected_tsv)


if __name__ == "__main__":
    unittest.main()
