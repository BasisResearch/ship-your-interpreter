"""Failed solvers, incomplete encodings and helper assumptions cannot certify runs."""

import contextlib
import csv
import hashlib
import io
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import houdini_summary as houdini
from scripts import segment_certificates


class HoudiniSolverTests(unittest.TestCase):
    def test_only_one_clean_answer_is_a_verdict(self) -> None:
        cases = [
            (0, "unsat\n", "", "unsat"),
            (0, "sat\n", "", "sat"),
            (0, "unknown\n", "", "unknown"),
            (0, "timeout\n", "", "unknown"),
            (1, "unsat\n", "", "error"),
            (-9, "sat\n", "", "error"),
            (0, "unsat\n", "fatal error", "error"),
            (0, "unsat\nsat\n", "", "error"),
            (0, "unsatisfactory\n", "", "error"),
            (0, 'unsat\n(error "bad declaration")', "", "error"),
            (0, "", "", "error"),
        ]
        for code, stdout, stderr, expected in cases:
            with self.subTest(code=code, stdout=stdout, stderr=stderr):
                result = subprocess.CompletedProcess(["z3"], code, stdout, stderr)
                self.assertEqual(houdini.solver_answer(result), expected)

    def test_wall_timeout_cannot_accept_partial_unsat(self) -> None:
        expired = subprocess.TimeoutExpired(["z3"], 6, output="unsat\n")
        with patch.object(houdini.subprocess, "run", side_effect=expired) as run:
            self.assertEqual(houdini.z3("(check-sat)", 1), "unknown")
            self.assertEqual(run.call_args.kwargs["timeout"], 6)

    def test_failed_multiquery_solver_cannot_discard_exit_guards(self) -> None:
        failure = subprocess.CompletedProcess(["z3"], 1, "unsat\n", "")
        query = "(declare-const g0 Bool)\n(assert (= g0 true))\n"
        with patch.object(houdini.subprocess, "run", return_value=failure):
            self.assertEqual(
                houdini.abstract_exit_feasibility(query, ["g0"], 1),
                {"g0": "unknown"},
            )

    def test_failed_model_process_cannot_supply_sp_delta(self) -> None:
        failure = subprocess.CompletedProcess(
            ["z3"], 1, "sat\n((delta #x0000000000000440))", ""
        )
        with patch.object(houdini.subprocess, "run", return_value=failure):
            self.assertIsNone(houdini.sp_delta("; @@POST@@", 1))

    def test_multiquery_solver_cannot_hide_unexpected_output(self) -> None:
        query = "(declare-const g0 Bool)\n(assert (= g0 true))\n"
        for output in ("unsat\ntimeout", "unsat\nunexpected diagnostic"):
            with (
                self.subTest(output=output),
                patch.object(
                    houdini.subprocess,
                    "run",
                    return_value=subprocess.CompletedProcess(["z3"], 0, output, ""),
                ),
            ):
                self.assertEqual(
                    houdini.abstract_exit_feasibility(query, ["g0"], 1),
                    {"g0": "unknown"},
                )


class HoudiniProjectionTests(unittest.TestCase):
    def test_consistency_errors_are_not_vacuity_single_or_multiple_exit(self) -> None:
        query = "; @@ASSUME@@\n(define-fun state_exit () MState s0)\n; @@POST@@"
        for split in (False, True):
            for consistency in ("error", "unknown"):
                with (
                    self.subTest(split=split, consistency=consistency),
                    patch.object(
                        houdini,
                        "projection_case_queries",
                        return_value=[("g0", "s0", query)] if split else [],
                    ),
                    patch.object(
                        houdini, "single_exit_internal_case_queries", return_value=[]
                    ),
                    patch.object(
                        houdini, "abstract_exit_feasibility", return_value={"g0": "sat"}
                    ),
                    patch.object(houdini, "assume_block", return_value=""),
                    patch.object(
                        houdini, "direct_single_exit_query", side_effect=lambda q, *_: q
                    ),
                    patch.object(
                        houdini,
                        "post_specific_backward_slice",
                        side_effect=lambda q, *_: q,
                    ),
                    patch.object(
                        houdini, "z3_projection", side_effect=["unsat", consistency]
                    ),
                ):
                    verdict = houdini.check_projection_cases(
                        query, "(assert false)", {}, "", 1
                    )
                    self.assertTrue(verdict.startswith("UNKNOWN"), verdict)

    def test_malformed_empty_write_query_cannot_validate_footprint(self) -> None:
        with patch.object(houdini, "z3", return_value="error"):
            self.assertEqual(houdini.footprint_check("", "", [], set(), {}, 1), "error")

    def test_dependency_qualification_preserves_existing_restrictions(self) -> None:
        original = "VALID[candidate-suffix](consistency-unproved)"
        qualified = houdini.qualify_projection_dependencies(original, "env_new_spec")
        self.assertIn(original, qualified)
        self.assertTrue(
            houdini.label_projection_verdict("sp", qualified).startswith("UNKNOWN")
        )

    def test_assumed_helpers_are_explicitly_conditional(self) -> None:
        for post, expected in (
            ("sp", "CONDITIONAL-MACHINE"),
            ("residual_relation", "CONDITIONAL-PROJECTION"),
        ):
            self.assertEqual(
                houdini.label_projection_verdict(post, "VALID[sp+0x440]", {"callee_1"}),
                expected + "[sp+0x440]",
            )
        self.assertEqual(
            houdini.label_projection_verdict("sp", "REFUTED", {"callee_1"}), "REFUTED"
        )

    def test_suffix_or_named_premise_cannot_look_unconditional(self) -> None:
        for detail in (
            "[candidate-suffix]",
            "[dependencies:env_new_spec]",
            "[modulo StackOK]",
            "[deferred:recursive-frame]",
            "[StoreRepr@1]",
        ):
            with self.subTest(detail=detail):
                self.assertEqual(
                    houdini.label_projection_verdict(
                        "residual_relation", "VALID" + detail
                    ),
                    "CONDITIONAL-PROJECTION" + detail,
                )

    def test_metadata_cannot_hide_transitive_injected_helper(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "queries").mkdir()
            (root / "obligations").mkdir()
            (root / "queries/q.smt2").write_text("(assert (= s1 (callee_1 s0)))")
            (root / "obligations/callee_1.smt2").write_text(
                f"(assert (= s1 ({houdini.MALLOC16_CALLEE} S0)))"
            )
            closure = houdini.actual_dependency_closures(root, {"q": []}, {})
            self.assertIn(houdini.MALLOC16_CALLEE, closure["q"])
            self.assertIn(
                houdini.MALLOC16_CALLEE, houdini.injected_contract_summaries()
            )
            self.assertLessEqual(
                set(houdini.SEMANTIC_FUNCTIONAL_CALLEES),
                houdini.injected_contract_summaries(),
            )


class HoudiniMiningGateTests(unittest.TestCase):
    def test_missing_duplicate_or_malformed_completion_never_mines(self) -> None:
        for header in (
            "",
            "; complete=false",
            "; complete=TRUE",
            "; complete=true\n; complete=false",
            "; complete=true\n; complete=true",
        ):
            with (
                self.subTest(header=header),
                tempfile.TemporaryDirectory() as directory,
            ):
                root = Path(directory)
                (root / "obligations").mkdir()
                (root / "obligations/callee_1.smt2").write_text(header + "\n; @@GOAL@@")
                with patch.object(houdini, "z3") as solver:
                    with self.assertRaisesRegex(SystemExit, "INCOMPLETE"):
                        houdini.mine(root, ["callee_1"], 1, 1, 2)
                    solver.assert_not_called()

    def test_solver_error_cannot_drop_clause_and_report_fixpoint(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "obligations").mkdir()
            (root / "obligations/callee_1.smt2").write_text(
                "; complete=true\n; @@ASSUME@@\n; @@GOAL@@"
            )
            with (
                patch.object(houdini, "CLAUSE_IDS", ["x"]),
                patch.object(houdini, "NEG", {"x": "(assert false)"}),
                patch.object(houdini, "assume_block", return_value=""),
                patch.object(houdini, "z3", return_value="error"),
                contextlib.redirect_stdout(io.StringIO()),
            ):
                with self.assertRaisesRegex(
                    SystemExit, "solver errors invalidate mining"
                ):
                    houdini.mine(root, ["callee_1"], 1, 1, 2)


class HoudiniResidualReportingTests(unittest.TestCase):
    def run_sp(
        self,
        complete: str = "true",
        applied: str = "",
        answers: tuple[str, ...] = ("sat", "unsat"),
        only_post: str = "sp",
        only: str | None = None,
        require_valid: bool = False,
    ) -> tuple[dict[str, str], int]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "queries").mkdir()
            (root / "queries/hInt.smt2").write_text(
                "; @@ASSUME@@\n" + applied + "\n; @@POST@@\n"
            )
            (root / "pre.smt2").write_text("(assert true)\n")
            (root / "clauses.json").write_text("{}\n")
            (root / "source-provenance.tsv").write_text("test fixture\n")
            for filename, content in {
                "summaries.tsv": "summary\n",
                "query-summaries.tsv": "query\tsummaries\nhInt\t\n",
                "query-capabilities.tsv": "query\tfield\tinstance\tcapability\nhInt\thInt\tsingle\tpartial-projection\n",
                "residual-holes.tsv": "field\tdimension\n",
                "spans.tsv": f"field\tcomplete\tentry\tregion_lo\nhInt\t{complete}\t0x1\t0x1\n",
            }.items():
                (root / filename).write_text(content)
            with contextlib.ExitStack() as stack:
                stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
                replacements = {
                    "check_provenance": lambda *_: None,
                    "check_campaign_manifest": lambda *_: None,
                    "prepare_clause_set": lambda *_args, **_kwargs: {},
                    "load_query_effects": lambda *_: {},
                    "load_lean_certificates": lambda *_: {},
                    "residual_posts": lambda *_: {},
                    "residual_pres": lambda *_: {},
                    "residual_suffixes": lambda *_: {},
                    "assume_block": lambda *_args, **_kwargs: "",
                    "sp_delta": lambda *_: 0x440,
                }
                for name, replacement in replacements.items():
                    stack.enter_context(patch.object(houdini, name, replacement))
                solver = stack.enter_context(
                    patch.object(houdini, "z3", side_effect=answers)
                )
                stack.enter_context(
                    patch.object(
                        houdini.sys,
                        "argv",
                        [
                            "houdini",
                            str(root),
                            "--phase",
                            "check",
                            "--only-post",
                            only_post,
                            "-j1",
                        ]
                        + (["--only", only] if only else [])
                        + (["--require-valid"] if require_valid else []),
                    )
                )
                try:
                    houdini.main()
                except SystemExit:
                    if require_valid:
                        output = houdini.verdict_output_path(
                            str(root), {only} if only else None, {only_post}
                        )
                        receipt = json.loads(Path(output + ".receipt.json").read_text())
                        self.assertEqual(receipt["invocation"]["strict_gate"], "failed")
                    raise
            output = houdini.verdict_output_path(
                str(root), {only} if only else None, {only_post}
            )
            with open(output) as stream:
                row = next(csv.DictReader(stream, delimiter="\t"))
            return row, solver.call_count

    def test_unknown_or_empty_selection_is_not_success(self) -> None:
        for options in (
            {"only": "missing"},
            {"only_post": "invented"},
            {"only_post": "residual_relation"},
        ):
            with self.subTest(options=options):
                with self.assertRaisesRegex(SystemExit, "selection|no residual checks"):
                    self.run_sp(
                        answers=(),
                        only=options.get("only"),
                        only_post=options.get("only_post", "sp"),
                    )

    def test_shifted_sp_with_unproved_consistency_stays_unknown(self) -> None:
        row, calls = self.run_sp(answers=("unknown", "sat", "unsat"))
        self.assertEqual(calls, 3)
        self.assertTrue(row["sp"].startswith("UNKNOWN"), row)
        self.assertIn("sp+0x440", row["sp"])
        self.assertIn("consistency-unproved", row["sp"])
        self.assertEqual(row["full_contract_status"], "NOT-CHECKED")

    def test_missing_completion_never_reaches_residual_solver(self) -> None:
        row, calls = self.run_sp(complete="", answers=())
        self.assertEqual(calls, 0)
        self.assertTrue(row["sp"].startswith("INCOMPLETE"))

    def test_unlisted_injected_helper_is_conditional_in_tsv(self) -> None:
        row, _ = self.run_sp(applied=f"(assert (= s1 ({houdini.MALLOC16_CALLEE} s0)))")
        self.assertEqual(row["sp"], "CONDITIONAL-MACHINE")
        self.assertIn(houdini.MALLOC16_CALLEE, row["assumed_dependencies"])
        self.assertEqual(row["full_contract_status"], "NOT-CHECKED")

    def test_strict_cli_accepts_unqualified_valid_projection(self) -> None:
        row, _ = self.run_sp(require_valid=True)
        self.assertEqual(row["sp"], "VALID-MACHINE")

    def test_strict_cli_rejects_diagnostic_results_after_receipting(self) -> None:
        for options in (
            {"answers": ("unknown", "unknown")},
            {"answers": ("sat", "sat", "sat")},
            {"applied": f"(assert (= s1 ({houdini.MALLOC16_CALLEE} s0)))"},
            {"answers": ("sat", "sat", "unsat")},
        ):
            with self.subTest(options=options):
                with self.assertRaisesRegex(SystemExit, "projection validation failed"):
                    self.run_sp(require_valid=True, **options)


class HoudiniStrictResultTests(unittest.TestCase):
    def test_strict_mode_requires_check_or_both_phase(self) -> None:
        for phase in (
            "mine",
            "bounded",
            "premises",
            "projections",
            "artifact-selfcheck",
        ):
            with (
                self.subTest(phase=phase),
                patch.object(
                    houdini.sys,
                    "argv",
                    ["houdini", "/unused", "--phase", phase, "--require-valid"],
                ),
                self.assertRaisesRegex(SystemExit, "requires --phase check or both"),
            ):
                houdini.main()

    def test_strict_mode_requires_exact_unqualified_validity(self) -> None:
        tasks = [("q", "post")]
        for verdict in ("VALID", "VALID-MACHINE", "VALID-PROJECTION"):
            self.assertEqual(
                houdini.validation_failures(tasks, [("q", "post", verdict)]), []
            )
        for verdict in (
            "",
            "UNKNOWN",
            "REFUTED",
            "CONDITIONAL-MACHINE",
            "CONDITIONAL-PROJECTION",
            "VALID[sp+0x440]",
            "VALID-PROJECTION[trace-pinned-consistency]",
            "VACUOUS",
            "INCOMPLETE",
            "VALID(consistency-unproved)",
            "N/A(invented)",
        ):
            with self.subTest(verdict=verdict):
                self.assertTrue(
                    houdini.validation_failures(tasks, [("q", "post", verdict)])
                )

    def test_missing_duplicate_or_empty_scope_fails(self) -> None:
        for tasks, results in (
            ([], []),
            ([("q", "sp")], []),
            ([("q", "sp")], [("other", "sp", "VALID")]),
            ([("q", "sp")], [("q", "sp", "VALID"), ("q", "sp", "VALID")]),
        ):
            self.assertTrue(houdini.validation_failures(tasks, results))

    def test_not_applicable_needs_real_valid_check_in_same_query(self) -> None:
        for na in ("N/A", "N/A(fragment)", "N/A(not-an-eval-arm)"):
            self.assertTrue(
                houdini.validation_failures([("q", "sp")], [("q", "sp", na)])
            )
            self.assertFalse(
                houdini.validation_failures(
                    [("q", "sp"), ("q", "memory")],
                    [("q", "sp", na), ("q", "memory", "VALID-MACHINE")],
                )
            )
            self.assertTrue(
                houdini.validation_failures(
                    [("q", "sp"), ("other", "memory")],
                    [("q", "sp", na), ("other", "memory", "VALID-MACHINE")],
                )
            )


class HoudiniBoundedTests(unittest.TestCase):
    def test_bounded_cli_checks_provenance_before_search(self) -> None:
        with (
            patch.object(
                houdini.sys, "argv", ["houdini", "/unused", "--phase", "bounded"]
            ),
            patch.object(houdini, "check_provenance", side_effect=SystemExit("stale")),
            patch.object(houdini, "bounded") as search,
            self.assertRaisesRegex(SystemExit, "stale"),
        ):
            houdini.main()
        search.assert_not_called()

    def test_bounded_cli_checks_manifest_before_search(self) -> None:
        with (
            patch.object(
                houdini.sys, "argv", ["houdini", "/unused", "--phase", "bounded"]
            ),
            patch.object(houdini, "check_provenance"),
            patch.object(
                houdini,
                "check_campaign_manifest",
                side_effect=SystemExit("bad manifest"),
            ),
            patch.object(houdini, "bounded") as search,
            self.assertRaisesRegex(SystemExit, "bad manifest"),
        ):
            houdini.main()
        search.assert_not_called()

    def test_empty_or_invalid_bounds_and_empty_inventory_fail(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            for bounds in ([], [0], [-1]):
                with self.subTest(bounds=bounds):
                    with self.assertRaisesRegex(
                        SystemExit, "positive, nonempty bounds"
                    ):
                        houdini.bounded(directory, 1, 1, bounds)
            with self.assertRaisesRegex(SystemExit, "query inventory is empty"):
                houdini.bounded(directory, 1, 1, [1])

    def test_bounds_increase_after_unsat_and_only_report_encoding_evidence(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "bounded").mkdir()
            (root / "bounded/q.smt2").write_text("; @@ASSUME@@\n; @@EXIT@@\n; @@POST@@")
            (root / "pre.smt2").write_text("(assert true)")
            with (
                patch.object(houdini, "POSTS", {"sp": "(assert false)"}),
                patch.object(houdini, "z3", side_effect=["unsat", "sat"]) as solver,
                contextlib.redirect_stdout(io.StringIO()),
            ):
                houdini.bounded(directory, 1, 1, [1, 2, 3])
            self.assertEqual(solver.call_count, 2)
            with (root / "bounded-verdicts.tsv").open() as stream:
                row = next(csv.DictReader(stream, delimiter="\t"))
            self.assertEqual(row["sp"], "BOUNDED-ENCODING-SAT(k=2)")
            self.assertEqual(row["full_contract_status"], "NOT-CHECKED")


class HoudiniManifestTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root / "queries").mkdir()
        (self.root / "queries/q.smt2").write_text("; query")
        self.files = {
            "spans.tsv": "field\tresidual\tinstance\tcomplete\nq\thInt\tsingle\ttrue\n",
            "query-capabilities.tsv": "query\tfield\tinstance\tcapability\nq\thInt\tsingle\tpartial-projection\n",
            "query-summaries.tsv": "query\tsummaries\nq\t\n",
            "residual-capabilities.tsv": "field\n",
            "residual-holes.tsv": "field\tdimension\n",
            "lean-certificates.tsv": "residual\tpost\ttheorem\n",
            "functional-callees.tsv": "target\tname\tmode\tresult\tmemory\n"
            "0x80004640\t__muldi3\tground-functional-post\tbvmul(a0,a1)\tread-only\n"
            "0x800046a4\t__divdi3\tground-functional-post\tbvsdiv(a0,a1)\tread-only\n"
            "0x80004728\t__moddi3\tground-functional-post\tbvsrem(a0,a1)\tread-only\n",
        }
        for name, text in self.files.items():
            (self.root / name).write_text(text)

    def test_valid_identity_inventory(self) -> None:
        houdini.check_campaign_manifest(self.root)

    def test_duplicate_rows_never_silently_replace_identity(self) -> None:
        for name in (
            "spans.tsv",
            "query-capabilities.tsv",
            "query-summaries.tsv",
            "functional-callees.tsv",
        ):
            with self.subTest(manifest=name):
                original = self.files[name]
                (self.root / name).write_text(
                    original + original.splitlines()[1] + "\n"
                )
                with self.assertRaisesRegex(SystemExit, "duplicate"):
                    houdini.check_campaign_manifest(self.root)
                (self.root / name).write_text(original)

    def test_mismatched_residual_or_capability_is_rejected(self) -> None:
        path = self.root / "query-capabilities.tsv"
        original = self.files[path.name]
        for old, new in (
            ("hInt", "hBool"),
            ("single", "other"),
            ("partial-projection", "full-proof"),
        ):
            with self.subTest(field=old):
                path.write_text(original.replace(old, new))
                with self.assertRaisesRegex(SystemExit, "capability identity"):
                    houdini.check_campaign_manifest(self.root)
        path.write_text(original)

    def test_query_dependency_omission_cannot_skip_a_query(self) -> None:
        (self.root / "query-summaries.tsv").write_text("query\tsummaries\n")
        with self.assertRaisesRegex(SystemExit, "does not match"):
            houdini.check_campaign_manifest(self.root)

    def test_missing_completeness_does_not_mean_complete(self) -> None:
        path = self.root / "spans.tsv"
        path.write_text(self.files[path.name].replace("true", ""))
        with self.assertRaisesRegex(SystemExit, "completeness"):
            houdini.check_campaign_manifest(self.root)


class HoudiniSourceFreshnessTests(unittest.TestCase):
    def test_boundary_and_model_changes_fail_without_any_certificate(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "repo"
            campaign = Path(directory) / "campaign"
            legacy = {
                "ReflectSpan.lean": "experiments/smt/ReflectSpan.lean",
                "ReflectResiduals.lean": "experiments/smt/ReflectResiduals.lean",
                "NativeBodyAssert.lean": "Vsa/Sim/rows/NativeBodyAssert.lean",
                "EvalCallNative2.lean": "Vsa/Sim/EvalCallNative2.lean",
                "proof.elf": "c/while-riscv-htif.elf",
            }
            sources = [
                *legacy.values(),
                "Vsa/Sim/LayoutInstance.lean",
                "Vsa/MemReprWithin.lean",
                "Vsa/Sim/InitValues.lean",
            ]
            rows = []
            for relative in sources:
                source = root / relative
                snapshot = campaign / "src-tree" / relative
                source.parent.mkdir(parents=True, exist_ok=True)
                snapshot.parent.mkdir(parents=True, exist_ok=True)
                source.write_bytes(b"original source")
                snapshot.write_bytes(source.read_bytes())
                rows.append(
                    (
                        relative,
                        "src-tree/" + relative,
                        hashlib.sha256(source.read_bytes()).hexdigest(),
                    )
                )
            (campaign / "src").mkdir()
            for name, relative in legacy.items():
                (campaign / "src" / name).write_bytes((root / relative).read_bytes())
            with (campaign / "source-provenance.tsv").open("w") as stream:
                writer = csv.writer(stream, delimiter="\t")
                writer.writerow(("path", "snapshot", "sha256"))
                writer.writerows(rows)
            with (
                patch.object(
                    houdini, "__file__", str(root / "scripts/houdini_summary.py")
                ),
                patch.object(segment_certificates, "SOURCE_ROOTS", ("Vsa",)),
                patch.object(
                    segment_certificates,
                    "SOURCE_FILES",
                    tuple(
                        relative
                        for relative in sources
                        if not relative.startswith("Vsa/")
                    ),
                ),
            ):
                houdini.check_provenance(campaign)
                for relative in sources[-3:]:
                    with self.subTest(source=relative):
                        (root / relative).write_bytes(b"changed boundary or model")
                        with self.assertRaisesRegex(SystemExit, "source mismatch"):
                            houdini.check_provenance(campaign)
                        (root / relative).write_bytes(b"original source")
                (campaign / "source-provenance.tsv").unlink()
                with self.assertRaisesRegex(SystemExit, "source provenance"):
                    houdini.check_provenance(campaign)


if __name__ == "__main__":
    unittest.main()
