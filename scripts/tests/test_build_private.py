"""Tests for the serialized private Lean build driver."""

import tempfile
import unittest
from pathlib import Path

from scripts import build_private


class BuildPrivateTests(unittest.TestCase):
    """Test graph parsing and resume-safety primitives."""

    def test_header_parser_handles_nested_comments_and_quoted_components(self) -> None:
        text = """/- outer /- nested -/ comment -/
import Vsa.Base Vsa.Sim.Code.«__divdi3» -- trailing
/- between -/
import Vsa.Other
namespace Vsa
import Vsa.TooLate
"""
        self.assertEqual(
            build_private.parse_header_imports(text),
            ("Vsa.Base", "Vsa.Sim.Code.__divdi3", "Vsa.Other"),
        )

    def test_topological_order_is_stable_and_dependency_first(self) -> None:
        modules = {
            "Vsa.C": build_private.Module("Vsa.C", Path("Vsa/C.lean"), ("Vsa.A",)),
            "Vsa.B": build_private.Module("Vsa.B", Path("Vsa/B.lean"), ("Vsa.A",)),
            "Vsa.A": build_private.Module("Vsa.A", Path("Vsa/A.lean"), ()),
        }
        self.assertEqual(
            [module.name for module in build_private.topological_order(modules)],
            ["Vsa.A", "Vsa.B", "Vsa.C"],
        )

    def test_topological_order_rejects_cycles(self) -> None:
        modules = {
            "Vsa.A": build_private.Module("Vsa.A", Path("Vsa/A.lean"), ("Vsa.B",)),
            "Vsa.B": build_private.Module("Vsa.B", Path("Vsa/B.lean"), ("Vsa.A",)),
        }
        with self.assertRaisesRegex(build_private.BuildError, "import cycle"):
            build_private.topological_order(modules)

    def test_output_root_must_be_outside_repository(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            repo = base / "repo"
            repo.mkdir()
            with self.assertRaisesRegex(build_private.BuildError, "outside repository"):
                build_private.validate_output_root(repo, repo / "private")
            outside = base / "private"
            self.assertEqual(
                build_private.validate_output_root(repo, outside), outside.resolve()
            )

    def test_dependency_change_invalidates_downstream_fingerprint(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            (repo / "Vsa").mkdir()
            source_a = repo / "Vsa" / "A.lean"
            source_b = repo / "Vsa" / "B.lean"
            source_a.write_text("def a := 1\n", encoding="utf-8")
            source_b.write_text("import Vsa.A\ndef b := a\n", encoding="utf-8")
            modules = {
                "Vsa.A": build_private.Module("Vsa.A", Path("Vsa/A.lean"), ()),
                "Vsa.B": build_private.Module("Vsa.B", Path("Vsa/B.lean"), ("Vsa.A",)),
            }
            order = build_private.topological_order(modules)
            before = build_private.module_fingerprints(repo, order, "context")
            source_a.write_text("def a := 2\n", encoding="utf-8")
            after = build_private.module_fingerprints(repo, order, "context")
            self.assertNotEqual(before["Vsa.A"], after["Vsa.A"])
            self.assertNotEqual(before["Vsa.B"], after["Vsa.B"])


if __name__ == "__main__":
    unittest.main()
