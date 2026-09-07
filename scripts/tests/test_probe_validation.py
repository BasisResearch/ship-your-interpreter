"""Validation must distinguish checked results from missing or failed probes."""

import io
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from scripts import smt_check, statement_fuzz


class ProbeValidationTests(unittest.TestCase):
    def test_lean_cannot_use_an_unverified_backend(self):
        with patch.dict(statement_fuzz.os.environ, {}, clear=True):
            for tool in (statement_fuzz, smt_check):
                with self.subTest(tool=tool.__name__), patch.object(tool.subprocess, "run") as run:
                    code, output = tool.run_lean("import Vsa")
                    self.assertNotEqual(code, 0)
                    self.assertIn("BACKEND-INVALID", output)
                    run.assert_not_called()

    def test_failed_lean_is_not_survival(self):
        for code in (1, 2, 124, -9):
            with self.subTest(code=code):
                verdict, _ = statement_fuzz.classify(code, "compiler failed")
                self.assertNotIn(verdict, {"SURVIVED", "REFUTED"})
                self.assertNotEqual(statement_fuzz.verdict_exit_status(verdict), 0)

    def test_exact_axiom_report_is_required(self):
        valid = "'VsaFuzzProbe.probe' depends on axioms: [propext,\n Quot.sound]"
        self.assertEqual(statement_fuzz.classify(0, valid)[0], "REFUTED")
        for output in (
            "'unrelated' does not depend on any axioms",
            valid + "\n" + valid,
            valid.replace("Quot.sound", "sorryAx"),
            valid.replace("Quot.sound", "untrustedAxiom"),
            "",
        ):
            with self.subTest(output=output):
                self.assertEqual(statement_fuzz.classify(0, output)[0], "INCONCLUSIVE")

    def test_unsupported_statement_is_not_survival(self):
        with patch.object(statement_fuzz, "extract_nested", return_value=None):
            verdict = statement_fuzz.fuzz_semantic(
                "", "P", True, False, "", io.StringIO(), body_override="unrecognized"
            )
        self.assertEqual(verdict, "UNDECIDABLE")

    def test_empty_generated_battery_is_rejected(self):
        for count in (0, -1):
            with self.assertRaises(ValueError):
                statement_fuzz.gen_battery(count, io.StringIO())

    def test_positive_acceptance_needs_successful_proof(self):
        def failed_positive(source, **_):
            if "#print axioms refute_Pre" in source:
                import re

                name = re.search(r"#print axioms (refute_Pre\w+)", source)[1]
                return 0, f"'VsaFuzzAcceptance.{name}' does not depend on any axioms"
            if "#print axioms Amd" in source:
                return 124, "TIMEOUT"
            return 0, ""

        with patch.object(statement_fuzz, "run_lean", side_effect=failed_positive):
            self.assertFalse(statement_fuzz.acceptance(io.StringIO()))

    def test_solver_error_cannot_be_an_unsat_result(self):
        for result in (
            subprocess.CompletedProcess([], 1, "unsat\n", ""),
            subprocess.CompletedProcess([], 0, 'unsat\n(error "bad query")\n', ""),
            subprocess.CompletedProcess([], 0, "unsat\nsat\n", ""),
            subprocess.CompletedProcess([], 0, "unsat\n", "solver failure"),
        ):
            with self.subTest(result=result), tempfile.TemporaryDirectory() as directory:
                with patch.object(smt_check, "LOGDIR", directory), patch.object(
                    smt_check.subprocess, "run", return_value=result
                ):
                    self.assertTrue(smt_check.run_z3("(check-sat)").startswith("SOLVER-ERROR"))

    def test_unsat_does_not_request_model(self):
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(smt_check, "LOGDIR", directory), patch.object(
                smt_check.subprocess,
                "run",
                return_value=subprocess.CompletedProcess([], 0, "unsat\n", ""),
            ) as run:
                self.assertEqual(smt_check.run_z3("(check-sat)\n(get-model)"), "unsat\n")
                self.assertEqual(run.call_count, 1)

    def test_inconsistent_premises_are_not_validated(self):
        context = smt_check.EncCtx()
        with patch.object(smt_check, "load", return_value=([], "", "", "")), patch.object(
            smt_check, "encode_statement", return_value=(context, ["false"], "true")
        ), patch.object(smt_check, "run_z3", return_value="unsat"):
            verdict, _ = smt_check.smt_check("validate", "unused", "P", io.StringIO())
        self.assertEqual(verdict, "VACUOUS")
        self.assertNotEqual(smt_check.verdict_exit_status("validate", verdict), 0)

    def test_unknown_empty_and_opaque_implications_do_not_pass(self):
        for verdicts in ({}, {"p": "UNKNOWN"}, {"p": "MODULO-OPAQUE"}, {"p": "VACUOUS"}):
            with self.subTest(verdicts=verdicts):
                self.assertEqual(smt_check.implication_status(verdicts, "FAIL"), "INCOMPLETE")
        self.assertEqual(smt_check.implication_status({"p": "HOLDS"}, "FAIL"), "OK")

    def test_opaque_antecedent_does_not_produce_counterexample(self):
        context = smt_check.EncCtx()
        with patch.object(smt_check, "run_z3") as run:
            verdict, _ = smt_check._implies_check(context, [None], "false", io.StringIO(), 10)
        self.assertEqual(verdict, "MODULO-OPAQUE")
        run.assert_not_called()

    def test_replay_cannot_reuse_an_unrelated_theorem_report(self):
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(smt_check, "LOGDIR", directory), patch.object(
                smt_check, "run_lean", return_value=(0, "'helper' does not depend on any axioms")
            ):
                self.assertEqual(smt_check._run_replay("theorem refuted : False := by contradiction")[0], "GAP")


if __name__ == "__main__":
    unittest.main()
