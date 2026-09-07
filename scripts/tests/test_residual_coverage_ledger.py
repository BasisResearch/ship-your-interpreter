"""Reject incomplete proof inventories and cross-kind evidence promotion."""

import tempfile
from unittest.mock import patch
import unittest
from collections.abc import Sequence
from pathlib import Path

from scripts import residual_coverage_ledger as ledger


class ResidualCoverageLedgerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.surface = ledger.completion_surface(Path(__file__).resolve().parents[2])
        self.cap_header = (
            "field",
            "machine_instances",
            "semantic_projection",
            "full_residual",
            "capability_class",
        )
        self.cap_rows = [
            (
                field,
                "0",
                "no",
                "no",
                "non-finite"
                if field == "hDivCorr"
                else "composite-family"
                if field == "hErrFam"
                else "lean-only",
            )
            for field in sorted(self.surface.targets)
        ]
        self.write("residual-capabilities.tsv", self.cap_header, self.cap_rows)
        self.write(
            "residual-holes.tsv",
            ("field", "dimension", "reason"),
            [
                (field, "full-lean-proposition", "no checked supplier")
                for field in sorted(self.surface.targets)
            ],
        )
        self.write(
            "query-capabilities.tsv", ("query", "field", "instance", "capability"), []
        )
        self.write("spans.tsv", ("field", "residual", "instance", "complete"), [])
        self.write(
            "residual-extensions.tsv", ("query", "field", "name", "predicate"), []
        )
        self.write("lean-certificates.tsv", ("residual", "post", "theorem"), [])

    def write(
        self, name: str, header: tuple[str, ...], rows: Sequence[tuple[str, ...]]
    ) -> None:
        ledger._write_tsv(self.root / name, header, rows)

    def build(self, only: set[str] | None = None) -> ledger.LedgerResult:
        return ledger.build_ledger(self.root, [], [], only, surface=self.surface)

    def test_require_complete_rejects_an_incomplete_report(self) -> None:
        report = self.build()
        arguments = ["ledger", "build", "--campaign", str(self.root),
                     "--verdict", str(self.root / "verdict.tsv"), "--require-complete",
                     "--out-tsv", str(self.root / "matrix.tsv"),
                     "--out-json", str(self.root / "matrix.json")]
        with patch("sys.argv", arguments), patch.object(ledger, "build_ledger", return_value=report):
            with self.assertRaises(SystemExit) as failure:
                ledger.main()
        self.assertEqual(failure.exception.code, 1)
        self.assertTrue((self.root / "matrix.json").is_file())

    def test_production_ledger_rejects_unreceipted_verdict(self) -> None:
        verdict = self.add_query()
        with self.assertRaisesRegex(ledger.LedgerError, "verdict provenance failed"):
            ledger.build_ledger(self.root, [verdict], [])

    def test_initial_state_dimensions_remain_explicit_holes(self) -> None:
        result = self.build()
        for dimension in ("memory-ownership", "memory-access", "entry-state"):
            cells = [cell for cell in result["cells"] if cell["dimension"] == dimension]
            self.assertEqual(len(cells), len(self.surface.targets))
            self.assertTrue(all(cell["explicit_hole"] for cell in cells))
        self.assertFalse(result["completion_surface"]["complete"])
        self.assertEqual(result["completion_surface"]["full_contract_status"], "NOT-CHECKED")

    def test_conditional_solver_result_is_not_unconditional_evidence(self) -> None:
        for verdict in ("CONDITIONAL-MACHINE", "CONDITIONAL-PROJECTION", "VALID[assumed helper]"):
            self.assertFalse(ledger._is_valid(verdict))

    def add_query(self) -> Path:
        rows = [row for row in self.cap_rows if row[0] != "hInt"]
        rows.append(("hInt", "1", "yes", "no", "finite-projection"))
        self.write("residual-capabilities.tsv", self.cap_header, rows)
        self.write(
            "query-capabilities.tsv",
            ("query", "field", "instance", "capability"),
            [("hInt", "hInt", "leaf", "partial-projection")],
        )
        self.write(
            "spans.tsv",
            ("field", "residual", "instance", "complete"),
            [("hInt", "hInt", "leaf", "true")],
        )
        self.write(
            "verdict.tsv",
            ("query", "residual", "instance", "capability", "residual_relation"),
            [("hInt", "hInt", "leaf", "partial-projection", "VALID-PROJECTION")],
        )
        return self.root / "verdict.tsv"

    def add_trace(self, mutations: bool) -> Path:
        count = "1" if mutations else "0"
        self.write(
            "fuzz.tsv",
            (
                "field",
                "trace",
                "residual_post",
                "agree",
                "mutations_expected",
                "mutations_killed",
                "certificates_excluded",
            ),
            [("hInt", "trace-1", "yes", "yes", count, count, "0")],
        )
        self.write("fuzz.tsv.findings", ("kind", "where", "detail"), [])
        self.write(
            "fuzz.tsv.mutations.tsv",
            ("field", "post", "mutation", "provenance", "result"),
            [
                (
                    "hInt",
                    "residual_relation",
                    "output-length",
                    "independent-trace-oracle",
                    "killed",
                )
            ]
            if mutations
            else [],
        )
        return self.root / "fuzz.tsv"

    def test_source_census_includes_actual_indexed_work(self) -> None:
        self.assertEqual(len(self.surface.term_fields), 63)
        self.assertEqual(self.surface.div_fields, ("Reflect", "entry", "iter", "arms"))
        self.assertEqual(self.surface.err_fields, ("program",))

    def test_total_inventory_has_no_invented_evidence(self) -> None:
        result = self.build()
        self.assertEqual(
            len(result["cells"]), len(self.surface.targets) * len(ledger.DIMENSIONS)
        )
        self.assertEqual(result["leaves"], [])
        for cell in result["cells"]:
            for name in (
                "machine_execution_covered",
                "smt_projection_valid",
                "independent_oracle_covered",
                "mutations_killed",
                "lean_bridge_compiled",
                "full_residual_compiled",
            ):
                self.assertFalse(cell[name])

    def test_scoped_run_cannot_hide_missing_inventory(self) -> None:
        self.write(
            "residual-capabilities.tsv",
            self.cap_header,
            [row for row in self.cap_rows if row[0] != "hInitSome"],
        )
        with self.assertRaisesRegex(ledger.LedgerError, "inventory mismatch"):
            self.build({"hInt"})

    def test_proof_claim_without_compiled_witness_is_rejected(self) -> None:
        rows = [row for row in self.cap_rows if row[0] != "hInitNone"]
        rows.append(("hInitNone", "0", "no", "yes", "lean-only"))
        self.write("residual-capabilities.tsv", self.cap_header, rows)
        with self.assertRaisesRegex(ledger.LedgerError, "no checked theorem witness"):
            self.build()

    def test_zero_query_cannot_claim_finite_capability(self) -> None:
        rows = [row for row in self.cap_rows if row[0] != "hInitNone"]
        rows.append(("hInitNone", "0", "no", "no", "finite-projection"))
        self.write("residual-capabilities.tsv", self.cap_header, rows)
        with self.assertRaisesRegex(ledger.LedgerError, "contradicts query inventory"):
            self.build()

    def test_missing_findings_is_not_a_clean_fuzz_run(self) -> None:
        verdict = self.add_query()
        fuzz = self.add_trace(False)
        (self.root / "fuzz.tsv.findings").unlink()
        with self.assertRaisesRegex(ledger.LedgerError, "missing artifact"):
            ledger.build_ledger(self.root, [verdict], [fuzz], surface=self.surface)

    def test_trace_coverage_does_not_imply_mutations_or_proof(self) -> None:
        verdict = self.add_query()
        fuzz = self.add_trace(False)
        result = ledger.build_ledger(self.root, [verdict], [fuzz], surface=self.surface)
        leaf = next(leaf for leaf in result["leaves"] if leaf["query"] == "hInt")
        self.assertTrue(leaf["machine_execution_covered"])
        self.assertTrue(leaf["independent_oracle_covered"])
        self.assertFalse(leaf["mutations_killed"])
        self.assertFalse(leaf["lean_bridge_compiled"])
        self.assertFalse(leaf["full_residual_compiled"])

    def test_mutation_dimension_does_not_imply_smt_coverage(self) -> None:
        verdict = self.add_query()
        fuzz = self.add_trace(True)
        result = ledger.build_ledger(self.root, [verdict], [fuzz], surface=self.surface)
        leaf = next(leaf for leaf in result["leaves"] if leaf["dimension"] == "output")
        self.assertTrue(leaf["mutations_killed"])
        self.assertFalse(leaf["smt_projection_valid"])
        cell = next(
            cell
            for cell in result["cells"]
            if cell["residual"] == "hInt" and cell["dimension"] == "output"
        )
        self.assertFalse(cell["smt_executable"])

    def test_mismatched_verdict_instance_is_rejected(self) -> None:
        verdict = self.add_query()
        verdict.write_text(verdict.read_text().replace("\tleaf\t", "\tother\t"))
        with self.assertRaisesRegex(ledger.LedgerError, "instance mismatch"):
            ledger.build_ledger(self.root, [verdict], [], surface=self.surface)

    def test_incomplete_machine_span_is_rejected(self) -> None:
        verdict = self.add_query()
        path = self.root / "spans.tsv"
        path.write_text(path.read_text().replace("true", "false"))
        with self.assertRaisesRegex(ledger.LedgerError, "incomplete machine span"):
            ledger.build_ledger(self.root, [verdict], [], surface=self.surface)

    def test_stray_span_cannot_be_hidden_by_scope(self) -> None:
        self.write(
            "spans.tsv",
            ("field", "residual", "instance", "complete"),
            [("unknown", "unknown", "leaf", "true")],
        )
        with self.assertRaisesRegex(
            ledger.LedgerError, "query/span inventory mismatch"
        ):
            self.build({"hInt"})

    def test_machine_verdict_cannot_be_promoted_to_semantic_projection(self) -> None:
        verdict = self.add_query()
        verdict.write_text(
            verdict.read_text().replace("VALID-PROJECTION", "VALID-MACHINE")
        )
        with self.assertRaisesRegex(
            ledger.LedgerError, "semantic projection not validated"
        ):
            ledger.build_ledger(self.root, [verdict], [], surface=self.surface)

    def test_matching_theorem_names_do_not_establish_compiled_certificate(self) -> None:
        self.add_query()
        self.write(
            "lean-certificates.tsv",
            ("residual", "post", "theorem"),
            [("hInt", "abi_frame_x1", "Arbitrary.uncheckedTheorem")],
        )
        self.write(
            "verdict.tsv",
            (
                "query",
                "residual",
                "instance",
                "capability",
                "residual_relation",
                "abi_frame_x1",
            ),
            [
                (
                    "hInt",
                    "hInt",
                    "leaf",
                    "partial-projection",
                    "VALID-PROJECTION",
                    "VALID[Lean:Arbitrary.uncheckedTheorem]",
                )
            ],
        )
        result = ledger.build_ledger(
            self.root, [self.root / "verdict.tsv"], [], surface=self.surface
        )
        leaf = next(leaf for leaf in result["leaves"] if leaf["leaf"] == "abi_frame_x1")
        self.assertTrue(leaf["lean_certificate_declared"])
        self.assertFalse(leaf["lean_certified"])
        self.assertFalse(leaf["lean_bridge_compiled"])
        self.assertFalse(leaf["full_residual_compiled"])

    def test_invalid_success_labels_are_rejected(self) -> None:
        for value in (
            "VALID-ASSUMED",
            "VALID[assumed]",
            "VALID[timeout]",
            "VALID-but-unknown",
            "VALID[Lean:someTheorem]",
            "VALID[opaque]",
            "VALID[vacuous]",
        ):
            with self.subTest(value=value):
                self.assertFalse(ledger._is_valid(value))

    def test_malformed_extra_tsv_column_is_rejected(self) -> None:
        path = self.root / "malformed.tsv"
        path.write_text("field\nvalue\textra\n")
        with self.assertRaisesRegex(ledger.LedgerError, "malformed row"):
            ledger._read_tsv(path, {"field"})


if __name__ == "__main__":
    unittest.main()
