"""Check generator drift detection without altering reviewed proof sources."""

import contextlib
import io
import tempfile
import unittest
from pathlib import Path

from scripts import gen_allocator_cases as generator


class DriftTests(unittest.TestCase):
    def test_check_rejects_missing_output_without_creating_it(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "AllocatorCases.lean"
            with contextlib.redirect_stderr(io.StringIO()):
                result = generator.main(["--check", "--output", str(output)])
            self.assertEqual(result, 1)
            self.assertFalse(output.exists())

    def test_check_rejects_changed_output_without_rewriting_it(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "AllocatorCases.lean"
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(generator.main(["--output", str(output)]), 0)
            changed = output.read_text().replace("aux.mCall", "aux.mEvalArgs", 1)
            output.write_text(changed)
            errors = io.StringIO()
            with contextlib.redirect_stderr(errors):
                result = generator.main(["--check", "--output", str(output)])
            self.assertEqual(result, 1)
            self.assertEqual(output.read_text(), changed)
            self.assertIn("aux.mCall", errors.getvalue())

    def test_check_accepts_current_output(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "AllocatorCases.lean"
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(generator.main(["--output", str(output)]), 0)
                self.assertEqual(
                    generator.main(["--check", "--output", str(output)]), 0
                )


if __name__ == "__main__":
    unittest.main()
