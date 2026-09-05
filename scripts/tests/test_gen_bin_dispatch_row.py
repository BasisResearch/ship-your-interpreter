"""Regression test for the generated binary-dispatch row."""

import unittest
from pathlib import Path

from scripts import gen_bin_dispatch_row


class BinDispatchRowGenerationTests(unittest.TestCase):
    """Keep the checked-in row synchronized with its generator."""

    def test_checked_in_row_matches_generator(self) -> None:
        root = Path(gen_bin_dispatch_row.ROOT)
        expected = (
            root / "Vsa" / "Sim" / "rows" / "BinDispatchRow.lean"
        ).read_text(encoding="utf-8")

        self.assertEqual(
            gen_bin_dispatch_row.render().rstrip("\n"), expected.rstrip("\n")
        )


if __name__ == "__main__":
    unittest.main()
