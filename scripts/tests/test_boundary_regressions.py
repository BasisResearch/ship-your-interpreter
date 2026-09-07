"""Validate real Sail regression artifacts and fail-closed reporting.

Set BOUNDARY_REGRESSION_ARTIFACTS to a completed runner output directory. These
tests mutate actual Sail results; they do not implement a Python machine model.
The mandatory gate must run the Lean fixture before these artifact checks.
"""

from __future__ import annotations

import copy
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import boundary_regressions as regression


class AxiomReportTests(unittest.TestCase):
    """Require the exact checked theorem inventory in each fixture invocation."""

    def setUp(self) -> None:
        self.lines = [
            f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
            for name in sorted(regression.EXPECTED_AXIOM_REPORTS)
        ]

    def test_standard_subsets_and_axiom_free_reports(self) -> None:
        self.assertEqual(
            len(regression.validate_axiom_reports("\n".join(self.lines))), 12
        )
        for suffix in (
            "depends on axioms: []",
            "depends on axioms: [Quot.sound]",
            "does not depend on any axioms",
        ):
            lines = [
                f"'{name}' {suffix}"
                for name in sorted(regression.EXPECTED_AXIOM_REPORTS)
            ]
            with self.subTest(suffix=suffix):
                self.assertEqual(
                    len(regression.validate_axiom_reports("\n".join(lines))), 12
                )

    def test_missing_duplicate_unrelated_and_malformed_reports_fail(self) -> None:
        for lines in (
            self.lines[:-1],
            self.lines + self.lines[:1],
            self.lines + ["'Other.theorem' depends on axioms: []"],
            self.lines + ["malformed axiom report"],
            [line.replace("Quot.sound", "unsafeAxiom") for line in self.lines],
            [line.replace("Quot.sound", "sorryAx") for line in self.lines],
        ):
            with (
                self.subTest(last=lines[-1]),
                self.assertRaises(regression.RegressionError),
            ):
                regression.validate_axiom_reports("\n".join(lines))

    def test_successful_process_with_missing_reports_fails(self) -> None:
        result = subprocess.CompletedProcess(
            ["lean"], 0, "\n".join(self.lines[:-1]), ""
        )
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "fixture.log"
            with patch.object(regression.subprocess, "run", return_value=result):
                with self.assertRaisesRegex(
                    regression.RegressionError, "missing axiom reports"
                ):
                    regression.run_checked(["lean"], regression.REPO, log)
            self.assertEqual(log.read_text(), result.stdout)


class BoundaryInputTests(unittest.TestCase):
    """Reject changes to the deterministic fixture and its proof boundary."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.receipt = regression.check_lock(
            regression.REPO, regression.REPO / regression.LOCK
        )

    def test_complete_case_inventory(self) -> None:
        self.assertEqual(self.receipt["case_ids"], list(regression.CASE_IDS))
        with self.assertRaises(regression.RegressionError):
            regression.validate_results({})

    def test_proof_boundary_and_elf_are_pinned(self) -> None:
        for name in (
            "c/while-riscv-htif.elf",
            str(regression.FIXTURE),
            "Vsa/Sim/LayoutInstance.lean",
            "Vsa/Sim/NativeNameAudit/Loaded.lean",
            "Vsa/Sim/NativeNameAudit/InitialExclusion.lean",
            "Vsa/Sim/NativeNameAudit/ControlLoaded.lean",
            "scripts/boundary_regressions.py",
            "Vsa/Sim/AstAccessAudit/AccessOwnedExclusion.lean",
            "Vsa/Sim/OutputAliasOwnedExclusion.lean",
            "riscv-lean/Lean_RV64D_executable/LeanRV64DExecutable/Platform.lean",
        ):
            with self.subTest(name=name):
                self.assertEqual(len(self.receipt["inputs"][name]), 64)

    def test_fingerprint_drift_fails(self) -> None:
        bad = copy.deepcopy(self.receipt)
        bad["inputs"][str(regression.FIXTURE)] = "0" * 64
        with tempfile.TemporaryDirectory() as directory:
            lock = Path(directory) / "lock.json"
            lock.write_text(json.dumps(bad))
            with self.assertRaisesRegex(
                regression.RegressionError, "fingerprint drift"
            ):
                regression.check_lock(regression.REPO, lock)


@unittest.skipUnless(
    os.environ.get("BOUNDARY_REGRESSION_ARTIFACTS"),
    "actual Sail artifacts required; run boundary_regressions.py first",
)
class ActualSailRegressionTests(unittest.TestCase):
    """Inspect and mutate the four actual interpreter outputs."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.directory = Path(os.environ["BOUNDARY_REGRESSION_ARTIFACTS"])
        cls.rows = regression.load_verified_results(cls.directory)

    def retained_copy(self, directory: Path) -> dict:
        """Link actual immutable artifacts and copy their receipt for mutation."""
        summary = json.loads((self.directory / "summary.json").read_text())
        for filename in summary["artifacts"]:
            (directory / filename).symlink_to(self.directory / filename)
        (directory / "summary.json").write_text(json.dumps(summary))
        return summary

    def test_stale_source_receipt_fails(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            directory = Path(name)
            summary = self.retained_copy(directory)
            summary["inputs"][str(regression.FIXTURE)] = "0" * 64
            (directory / "summary.json").write_text(json.dumps(summary))
            with self.assertRaisesRegex(regression.RegressionError, "source receipt"):
                regression.load_verified_results(directory)

    def test_artifact_hash_drift_fails(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            directory = Path(name)
            self.retained_copy(directory)
            path = directory / "ast_unreadable.json"
            path.unlink()
            path.write_text(json.dumps(self.rows["ast_unreadable"]) + "\n\n")
            with self.assertRaisesRegex(
                regression.RegressionError, "artifact fingerprint drift"
            ):
                regression.load_verified_results(directory)

    def test_rehashed_missing_axiom_report_fails(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            directory = Path(name)
            summary = self.retained_copy(directory)
            path = directory / "native_name_alias.log"
            lines = path.read_text().splitlines()
            path.unlink()
            path.write_text("\n".join(lines[1:]) + "\n")
            summary["artifacts"][path.name] = regression.build_private.hash_file(path)
            (directory / "summary.json").write_text(json.dumps(summary))
            with self.assertRaisesRegex(
                regression.RegressionError, "missing axiom reports"
            ):
                regression.load_verified_results(directory)

    def test_actual_sail_outcomes(self) -> None:
        checked = regression.validate_results(self.rows)
        self.assertEqual(len(checked), 4)
        self.assertTrue(checked[-1]["matches_source_output"])
        self.assertFalse(checked[2]["matches_source_output"])
        self.assertFalse(checked[1]["matches_source_termination"])
        self.assertEqual(self.rows["native_name_alias"]["steps"], 3813)

    def test_current_boundary_classification(self) -> None:
        checked = regression.validate_results(self.rows)
        self.assertEqual(regression.current_findings(checked), [])
        for case, row in self.rows.items():
            for field in ("current_boundary_status", "current_admission", "current_exclusion"):
                changed = copy.deepcopy(row)
                changed[field] = "unproved"
                with self.subTest(case=case, field=field):
                    with self.assertRaisesRegex(regression.RegressionError, "boundary proof"):
                        regression.check_result(case, changed)

    def test_admitted_mismatch_is_a_current_finding(self) -> None:
        checked = regression.validate_results(self.rows)
        control = checked[-1]
        for field in ("matches_source_output", "matches_source_termination"):
            changed = dict(control, **{field: False})
            with self.subTest(field=field):
                self.assertEqual(regression.current_findings([changed]), ["stable_control"])

    def test_dropped_case_fails(self) -> None:
        for case in regression.CASE_IDS:
            rows = dict(self.rows)
            del rows[case]
            with self.subTest(case=case), self.assertRaises(regression.RegressionError):
                regression.validate_results(rows)

    def test_unexpected_error_and_fuel_fail(self) -> None:
        for status in ("fuel_exhausted", "unexpected_error"):
            row = copy.deepcopy(self.rows["native_name_alias"])
            row["status"] = status
            with (
                self.subTest(status=status),
                self.assertRaises(regression.RegressionError),
            ):
                regression.check_result("native_name_alias", row)
        row = copy.deepcopy(self.rows["native_name_alias"])
        row["terminal_event"]["error"] = "different exception"
        with self.assertRaises(regression.RegressionError):
            regression.check_result("native_name_alias", row)

    def test_missing_trace_and_terminal_attempt_fail(self) -> None:
        row = copy.deepcopy(self.rows["ast_unreadable"])
        row["trace"].pop()
        with self.assertRaises(regression.RegressionError):
            regression.check_result("ast_unreadable", row)
        row = copy.deepcopy(self.rows["ast_unreadable"])
        del row["terminal_event"]
        with self.assertRaises(regression.RegressionError):
            regression.check_result("ast_unreadable", row)

    def test_wrong_control_output_fails(self) -> None:
        row = copy.deepcopy(self.rows["stable_control"])
        row["final_full_state"]["output"] = "\n"
        with self.assertRaises(regression.RegressionError):
            regression.check_result("stable_control", row)

    def test_source_oracle_drift_fails(self) -> None:
        row = copy.deepcopy(self.rows["ast_output_alias"])
        row["expected_source_output"] = "\n\n"
        with self.assertRaises(regression.RegressionError):
            regression.check_result("ast_output_alias", row)

    def test_sparse_replay_cannot_claim_dense_execution(self) -> None:
        row = copy.deepcopy(self.rows["native_name_alias"])
        row["replay_establishes_dense_loaded_execution"] = True
        with self.assertRaises(regression.RegressionError):
            regression.check_result("native_name_alias", row)


if __name__ == "__main__":
    unittest.main()
