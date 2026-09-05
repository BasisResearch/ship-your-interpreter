"""Tests for the term-routing generator manifest contract."""

from pathlib import Path
import tempfile
import unittest

import scripts.gen_m4_term_row as generator


class GenM4TermRowTests(unittest.TestCase):
    def test_tracked_output_matches_template(self) -> None:
        self.assertEqual(generator.OUTPUT.read_text(), generator.render())

    def test_missing_template_row_is_rejected(self) -> None:
        self.assert_validation_error(
            "name\tkey\tshape\tsimD\tentry\tvalue\n"
            "hKnown\tknown\tleaf_direct\tsim\t-\tvalue\n"
            "hMissing\tmissing\tleaf_direct\tsim\t-\tvalue\n",
            "theorem eval_known_row : True := by trivial\n",
            "template omits TSV rows: missing",
        )

    def test_extra_template_row_is_rejected(self) -> None:
        self.assert_validation_error(
            "name\tkey\tshape\tsimD\tentry\tvalue\n"
            "hKnown\tknown\tleaf_direct\tsim\t-\tvalue\n",
            "theorem eval_known_row : True := by trivial\n"
            "theorem eval_extra_row : True := by trivial\n",
            "template has undeclared rows: extra",
        )

    def assert_validation_error(self, tsv_text: str, template_text: str, expected: str) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tsv = root / "rows.tsv"
            template = root / "TermRouting.lean"
            tsv.write_text(tsv_text)
            template.write_text(template_text)
            with self.assertRaisesRegex(ValueError, expected):
                generator.render(tsv, template)


if __name__ == "__main__":
    unittest.main()
