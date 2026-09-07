"""Legacy theorem strings cannot prove posts or exempt mutants from checking."""

import csv
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock

from scripts import difftest, houdini_summary, residual_coverage_ledger
from scripts.tests import test_residual_coverage_ledger as ledger_fixtures


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

    def test_every_assert_mutant_is_evaluated_and_abi_survivors_are_visible(
        self,
    ) -> None:
        entry, _ = difftest._premise_fixture("hCallAssertOk")
        destination = entry.regs.sel(10)
        exit_state = difftest._with_mem_value(entry, destination, 4, 0)
        exit_state = difftest._with_mem_value(exit_state, destination + 8, 8, 0)
        definitions = []
        for width in (4, 8):
            bytes_ = " ".join(
                f"(select m (bvadd a #x{offset:016x}))"
                for offset in reversed(range(width))
            )
            value = f"(concat {bytes_})"
            if width == 4:
                value = f"((_ zero_extend 32) {value})"
            definitions.append(
                f"(define-fun ld{width} ((m Mem) (a BV64)) BV64 {value})"
            )
        definitions.append("(define-fun state_exit () MState s0)")
        evaluator = difftest.Ev(
            difftest.Query("\n".join(definitions)), entry, lambda *_: None
        )
        post = difftest.parse_all(houdini_summary.native_assert_machine_post())[0][1]
        killed, survived = difftest.audit_assert_post_mutants(
            entry, exit_state, evaluator, post
        )
        self.assertEqual(
            set(killed),
            {"null-kind", "null-payload", "x2", "output-array", "output-length"},
        )
        self.assertEqual(set(survived), {"x1", "x8", "x9", "x18"})
        self.assertEqual(set(killed + survived), difftest._ASSERT_OK_MACHINE_MUTATIONS)
        self.assertIs(evaluator.env["state_exit"], exit_state)
        with self.assertRaises(residual_coverage_ledger.LedgerError):
            residual_coverage_ledger._check_required_machine_mutations(
                "hCallAssertOk", set(killed)
            )

    def test_ledger_rejects_old_metadata_mutant_exclusions(self) -> None:
        fixture = ledger_fixtures.ResidualCoverageLedgerTests()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        verdict = fixture.add_query()
        fuzz = fixture.add_trace(mutations=True)
        with verdict.open(newline="") as stream:
            row = next(csv.DictReader(stream, delimiter="\t"))
        row["abi_frame_x1"] = "VALID[Lean:Declared.only]"
        fixture.write(verdict.name, tuple(row), [tuple(row.values())])
        fixture.write(
            "lean-certificates.tsv",
            ("residual", "post", "theorem"),
            [("hInt", "abi_frame_x1", "Declared.only")],
        )
        mutation = Path(str(fuzz) + ".mutations.tsv")
        fixture.write(
            mutation.name,
            ("field", "post", "mutation", "provenance", "result"),
            [
                (
                    "hInt",
                    "abi_frame_x1",
                    "x1",
                    "Declared.only",
                    "excluded-lean-certificate",
                )
            ],
        )
        with self.assertRaisesRegex(
            residual_coverage_ledger.LedgerError, "cannot exclude mutant"
        ):
            residual_coverage_ledger.build_ledger(
                fixture.root, [verdict], [fuzz], surface=fixture.surface
            )


if __name__ == "__main__":
    unittest.main()
