"""Legacy theorem strings cannot prove posts or exempt mutants from checking."""

import csv
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock

from scripts import difftest, houdini_summary


class LegacyLeanDeclarationTests(unittest.TestCase):
    def test_incomplete_declaration_post_cannot_skip_completeness(self) -> None:
        consistency = Mock(return_value="sat")
        for complete in ("false", None, ""):
            self.assertEqual(
                houdini_summary.declared_lean_post_verdict(complete, consistency),
                "INCOMPLETE(frontier-not-empty)",
            )
        consistency.assert_not_called()

    def test_vacuous_declaration_post_cannot_skip_consistency(self) -> None:
        consistency = Mock(return_value="unsat")
        self.assertEqual(
            houdini_summary.declared_lean_post_verdict("true", consistency),
            "VACUOUS(assumptions-inconsistent)",
        )
        consistency.assert_called_once_with()

    def test_consistent_or_unknown_declaration_post_remains_unproved(self) -> None:
        for result in ("sat", "unknown", "timeout"):
            with self.subTest(result=result):
                self.assertEqual(
                    houdini_summary.declared_lean_post_verdict("true", lambda: result),
                    "UNKNOWN(untyped-lean-certificate)",
                )

    def test_forged_or_expected_theorem_labels_cannot_claim_lean_validity(self) -> None:
        for theorem in ("Vsa.Sim.nativeAssertInternalAbi_closed", "Forged.theorem"):
            with self.subTest(theorem=theorem):
                self.assertEqual(
                    houdini_summary.label_projection_verdict(
                        "abi_frame_x1", f"VALID[Lean:{theorem}]"
                    ),
                    "UNKNOWN(untyped-lean-certificate)",
                )
        rows = [
            {"residual": query, "post": post, "theorem": theorem}
            for (query, post), theorem in houdini_summary.LEAN_POST_CERTIFICATES.items()
        ]
        rows[0]["theorem"] = "Forged.theorem"
        with self.assertRaises(ValueError):
            houdini_summary.validate_lean_certificate_rows(rows)

    def test_matching_or_forged_legacy_records_never_authorize_exclusions(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "query-capabilities.tsv").write_text(
                "query\tfield\tinstance\tcapability\n"
                "hCallAssertOk\thCallAssertOk\tnative\tpartial-projection\n"
            )
            for theorem in ("Vsa.Sim.nativeAssertInternalAbi_closed", "Forged.theorem"):
                with self.subTest(theorem=theorem):
                    posts = [
                        "abi_frame_x1",
                        "abi_frame_x8",
                        "abi_frame_x9",
                        "abi_frame_x18",
                    ]
                    (root / "lean-certificates.tsv").write_text(
                        "residual\tpost\ttheorem\n"
                        + "".join(
                            f"hCallAssertOk\t{post}\t{theorem}\n" for post in posts
                        )
                    )
                    verdict = root / "verdict.tsv"
                    verdict.write_text(
                        "query\t"
                        + "\t".join(posts)
                        + "\n"
                        + "hCallAssertOk\t"
                        + "\t".join(f"VALID[Lean:{theorem}]" for _ in posts)
                        + "\n"
                    )
                    authority, findings = difftest.phase3b_lean_certificates(
                        directory, [verdict]
                    )
                    self.assertEqual(authority, {})
                    self.assertTrue(findings)

if __name__ == "__main__":
    unittest.main()
