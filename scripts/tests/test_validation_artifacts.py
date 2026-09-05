"""Keep validation reports outside the source tree."""

import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import cegis_cure, smt_check, statement_fuzz


class ValidationArtifactTests(unittest.TestCase):
    """Check report destinations and retained Lean inputs."""

    def test_report_destinations_are_outside_repository(self) -> None:
        repo = Path(__file__).resolve().parents[2]
        for destination in (
            statement_fuzz.LOG,
            smt_check.LOG,
            cegis_cure.CURESDIR,
        ):
            with self.subTest(destination=destination):
                self.assertFalse(Path(destination).resolve().is_relative_to(repo))

    def test_trace_advice_uses_lean_candidate(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            candidate = Path(directory) / "sample.lean"
            with patch.object(cegis_cure, "INVDIR", directory):
                self.assertEqual(cegis_cure.filter_trace(None, "sample"), (None, ""))
                candidate.write_text("example : True := True.intro\n", encoding="utf-8")
                self.assertEqual(
                    cegis_cure.filter_trace(None, "sample"),
                    (True, "mined artifact present (sample.lean)"),
                )

    def test_smt_acceptance_lean_input_exists(self) -> None:
        repo = Path(__file__).resolve().parents[2]
        self.assertTrue((repo / "experiments/invariants/io_write_loop.lean").is_file())


if __name__ == "__main__":
    unittest.main()
