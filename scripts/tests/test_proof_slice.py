"""Check scoped-cache selection and rejection of incomplete proof evidence."""

import json
import tempfile
import unittest
from argparse import ArgumentTypeError
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from unittest.mock import patch

from scripts import build_private as build
from scripts import field_census as census
from scripts import proof_checkpoint as checkpoint
from scripts import proof_slice as proof


class ProofSliceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        root = Path(self.temp.name)
        self.repo, self.backend, self.output = (
            root / name for name in ("repo", "base", "out")
        )
        (self.repo / "Vsa").mkdir(parents=True)
        self.backend.mkdir()
        (self.repo / "Vsa/A.lean").write_text("theorem t : True := True.intro\n")
        (self.repo / "Vsa/B.lean").write_text("import Vsa.A\n")
        (self.repo / "Vsa.lean").write_text("import Vsa.B\n")
        (self.repo / "VsaRun.lean").write_text("import Vsa\n")
        self.modules = build.discover_modules(self.repo, True)
        self.fingerprints = build.module_fingerprints(
            self.repo,
            build.topological_order(self.modules),
            build.input_context(self.repo),
        )
        build.write_manifest(self.backend / build.MANIFEST_NAME, self.fingerprints)
        for module in self.modules.values():
            path = build.output_path(self.backend, module)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b"cached object")

    def run_check(
        self,
        *,
        plan_only: bool = False,
        progress: checkpoint.Checkpoint | None = None,
    ) -> Path | None:
        with redirect_stdout(StringIO()):
            return proof.execute(
                self.repo,
                self.backend,
                self.output,
                ["Vsa.B"],
                ["Vsa.A.t"],
                None,
                None,
                plan_only,
                progress=progress,
            )

    def test_selection_includes_dependencies_and_excludes_dependents(self) -> None:
        self.assertEqual(
            [module.name for module in proof.select_modules(self.modules, ["Vsa.B"])],
            ["Vsa.A", "Vsa.B"],
        )
        with self.assertRaisesRegex(build.BuildError, "unknown selected"):
            proof.select_modules(self.modules, ["Vsa.Missing"])

    def test_changed_dependency_invalidates_its_consumer(self) -> None:
        (self.repo / "Vsa/A.lean").write_text("theorem t : 1 = 1 := rfl\n")
        current = build.module_fingerprints(
            self.repo,
            build.topological_order(self.modules),
            build.input_context(self.repo),
        )
        actions = proof.plan_modules(
            proof.select_modules(self.modules, ["Vsa.B"]),
            current,
            self.backend,
            self.output,
        )
        self.assertEqual([item.action for item in actions], ["build", "build"])

    def test_leaf_and_shared_edits_preserve_unaffected_cache_entries(self) -> None:
        (self.repo / "Vsa/Z.lean").write_text("def z := 0\n")
        (self.repo / "Vsa.lean").write_text("import Vsa.B Vsa.Z\n")
        modules = build.discover_modules(self.repo)
        order = build.topological_order(modules)
        baseline = build.module_fingerprints(
            self.repo, order, build.input_context(self.repo)
        )
        build.write_manifest(self.backend / build.MANIFEST_NAME, baseline)
        build.output_path(self.backend, modules["Vsa.Z"]).write_bytes(
            b"independent object"
        )
        for name, expected in (
            ("Vsa.B", {"Vsa.B", "Vsa"}),
            ("Vsa.A", {"Vsa.A", "Vsa.B", "Vsa"}),
        ):
            with self.subTest(changed=name):
                source = self.repo / modules[name].source
                original = source.read_text()
                source.write_text(original + "-- additive helper edit\n")
                current = build.module_fingerprints(
                    self.repo, order, build.input_context(self.repo)
                )
                actions = proof.plan_modules(order, current, self.backend, self.output)
                self.assertEqual(
                    {item.name for item in actions if item.action == "build"}, expected
                )
                source.write_text(original)

    def test_manifest_without_object_requires_rebuild(self) -> None:
        build.output_path(self.backend, self.modules["Vsa.A"]).unlink()
        actions = proof.plan_modules(
            proof.select_modules(self.modules, ["Vsa.B"]),
            self.fingerprints,
            self.backend,
            self.output,
        )
        self.assertEqual([item.action for item in actions], ["build", "reuse-backend"])

    def test_stale_overlay_uses_current_backend(self) -> None:
        self.output.mkdir()
        build.write_manifest(self.output / build.MANIFEST_NAME, {"Vsa.A": "stale"})
        actions = proof.plan_modules(
            [self.modules["Vsa.A"]], self.fingerprints, self.backend, self.output
        )
        self.assertEqual(actions[0].action, "reuse-backend")

    def test_output_cannot_overlap_backend_or_repository(self) -> None:
        for output in (
            self.backend,
            self.backend / "nested",
            self.backend.parent,
            self.repo / "out",
        ):
            with self.subTest(output=output), self.assertRaises(build.BuildError):
                proof.check_roots(self.repo, self.backend, output)

    def test_audit_requires_exact_safe_declarations(self) -> None:
        valid = "'Vsa.A.t' depends on axioms: [propext,\nQuot.sound]"
        self.assertEqual(
            proof.audit_axioms(valid, ["Vsa.A.t"]),
            {"Vsa.A.t": ["propext", "Quot.sound"]},
        )
        invalid = [
            "",
            valid + "\n" + valid,
            valid.replace("propext", "unknownAxiom"),
            valid + "\nwarning: declaration uses `sorry`",
            valid + "\nX.lean:1: error: failed",
            valid + "\n'Vsa.other' does not depend on any axioms",
        ]
        for transcript in invalid:
            with self.subTest(transcript=transcript), self.assertRaises(ValueError):
                proof.audit_axioms(transcript, ["Vsa.A.t"])
        with self.assertRaisesRegex(ValueError, "duplicate requested"):
            proof.audit_axioms(valid, ["Vsa.A.t", "Vsa.A.t"])

    def test_plan_does_not_compile_or_create_output(self) -> None:
        with patch.object(build, "compile_module") as compile_module:
            self.assertIsNone(self.run_check(plan_only=True))
            compile_module.assert_not_called()
        self.assertFalse(self.output.exists())

    def test_audit_preserves_apostrophes_in_declaration_names(self) -> None:
        transcript = (
            "'Vsa.A.mk' depends on axioms: [propext]\n"
            "'Vsa.A.mk'' depends on axioms: [Quot.sound]\n"
            "'Vsa.A.mk''' does not depend on any axioms\n"
        )
        expected = {
            "Vsa.A.mk": ["propext"],
            "Vsa.A.mk'": ["Quot.sound"],
            "Vsa.A.mk''": [],
        }
        self.assertEqual(proof.audit_axioms(transcript, list(expected)), expected)
        with self.assertRaisesRegex(ValueError, "missing or unexpected"):
            proof.audit_axioms(transcript, ["Vsa.A.mk"])
        with self.assertRaisesRegex(ValueError, "nonstandard axioms"):
            proof.audit_axioms(
                transcript.replace("Quot.sound", "unsafeAxiom"), list(expected)
            )

    def test_audit_identifier_allows_trailing_primes_and_rejects_injection(
        self,
    ) -> None:
        for name in ("Vsa.A.mk", "Vsa.A.mk'", "Vsa.A.mk''"):
            with self.subTest(name=name):
                self.assertEqual(census.lean_identifier(name), name)
        for name in ("'", "Vsa..mk'", "Vsa.A.mk'\n#print axioms other", "Vsa.A.mk';"):
            with self.subTest(name=name), self.assertRaises(ArgumentTypeError):
                census.lean_identifier(name)

    def test_failed_audit_cannot_leave_success_receipt(self) -> None:
        def fail(_repo: Path, _backend: Path, source: Path) -> census.LeanResult:
            source.with_suffix(".olean").write_bytes(b"unusable output")
            return census.LeanResult(1, "error: wrong supplier type")

        with patch.object(census, "run_lean", side_effect=fail):
            with self.assertRaisesRegex(build.BuildError, "proof check failed"):
                self.run_check()
        self.assertFalse(list(self.output.rglob("receipt.json")))

    def test_changed_source_rejects_successful_audit(self) -> None:
        def mutate(_repo: Path, _backend: Path, source: Path) -> census.LeanResult:
            source.with_suffix(".olean").write_bytes(b"checked output")
            (self.repo / "Vsa/A.lean").write_text(
                "theorem changed : True := True.intro\n"
            )
            return census.LeanResult(0, "'Vsa.A.t' does not depend on any axioms")

        with patch.object(census, "run_lean", side_effect=mutate):
            with self.assertRaisesRegex(build.BuildError, "source changed"):
                self.run_check()
        self.assertFalse(list(self.output.rglob("receipt.json")))

    def test_changed_cached_object_rejects_successful_audit(self) -> None:
        def mutate(_repo: Path, _backend: Path, source: Path) -> census.LeanResult:
            source.with_suffix(".olean").write_bytes(b"checked output")
            build.output_path(self.backend, self.modules["Vsa.A"]).write_bytes(
                b"changed object"
            )
            return census.LeanResult(0, "'Vsa.A.t' does not depend on any axioms")

        with patch.object(census, "run_lean", side_effect=mutate):
            with self.assertRaisesRegex(build.BuildError, "object changed"):
                self.run_check()
        self.assertFalse(list(self.output.rglob("receipt.json")))

    def checkpoint(
        self, role: str, premises: list[dict[str, str]]
    ) -> checkpoint.Checkpoint:
        description = {
            "target_obligation": "requested_case",
            "target_type": "True",
            "consumer": "Vsa.A.t",
            "role": role,
            "remaining_premises": premises,
        }
        if role == "prerequisite":
            description["consumer_type"] = "True"
        path = Path(self.temp.name) / "checkpoint.json"
        path.write_text(json.dumps(description))
        return checkpoint.read_checkpoint(path)

    def test_receipt_distinguishes_prerequisite_conditional_and_complete(self) -> None:
        cases = (
            ("prerequisite", [], "prerequisite"),
            ("target", [{"name": "child", "type": "True"}], "conditional"),
            ("target", [], "complete"),
        )
        for role, premises, status in cases:
            with self.subTest(status=status):
                progress = self.checkpoint(role, premises)

                def accepted(
                    _repo: Path, _backend: Path, source: Path
                ) -> census.LeanResult:
                    self.assertIn(progress.source(), source.read_text())
                    source.with_suffix(".olean").write_bytes(
                        b"synthetic checked application"
                    )
                    return census.LeanResult(
                        0,
                        "'Vsa.A.t' does not depend on any axioms\n"
                        f"'{checkpoint.WITNESS}' does not depend on any axioms",
                    )

                with patch.object(census, "run_lean", side_effect=accepted):
                    receipt = self.run_check(progress=progress)
                assert receipt is not None
                report = json.loads(receipt.read_text())
                self.assertEqual(report["checkpoint"]["status"], status)
                self.assertEqual(report["checkpoint"]["remaining_premises"], premises)
                self.assertEqual(
                    report["checkpoint"]["checked_application"], checkpoint.WITNESS
                )
                self.assertFalse(report["full_library_checked"])
                self.assertEqual(report["counts"]["build"], 0)
                self.assertEqual(sum(report["counts"].values()), 2)
                timing = report["timing_seconds"]
                self.assertTrue(all(value >= 0 for value in timing.values()))
                self.assertAlmostEqual(
                    timing["total"],
                    sum(value for key, value in timing.items() if key != "total"),
                )
                self.assertEqual(timing["dependency_compile"], 0)

    def test_auditing_helper_without_application_cannot_complete_target(self) -> None:
        progress = self.checkpoint("target", [])

        def helper_only(_repo: Path, _backend: Path, source: Path) -> census.LeanResult:
            source.with_suffix(".olean").write_bytes(b"synthetic helper object")
            return census.LeanResult(0, "'Vsa.A.t' does not depend on any axioms")

        with patch.object(census, "run_lean", side_effect=helper_only):
            with self.assertRaisesRegex(ValueError, "missing or unexpected"):
                self.run_check(progress=progress)
        self.assertFalse(list(self.output.rglob("receipt.json")))

    def test_wrong_consumer_type_or_unsafe_application_cannot_leave_receipt(
        self,
    ) -> None:
        for status, transcript in (
            (1, "error: type mismatch"),
            (
                0,
                "'Vsa.A.t' does not depend on any axioms\n"
                f"'{checkpoint.WITNESS}' depends on axioms: [sorryAx]",
            ),
        ):
            with self.subTest(status=status):

                def rejected(
                    _repo: Path, _backend: Path, source: Path
                ) -> census.LeanResult:
                    source.with_suffix(".olean").write_bytes(
                        b"rejected synthetic object"
                    )
                    return census.LeanResult(status, transcript)

                with patch.object(census, "run_lean", side_effect=rejected):
                    with self.assertRaises((ValueError, build.BuildError)):
                        self.run_check(progress=self.checkpoint("target", []))
                self.assertFalse(list(self.output.rglob("receipt.json")))

    def test_build_counts_and_timing_record_rebuild_then_reuse(self) -> None:
        (self.repo / "Vsa/A.lean").write_text("theorem t : True := by trivial\n")

        def compile_fake(_repo: Path, output: Path, module: build.Module) -> None:
            target = build.output_path(output, module)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(b"synthetic rebuilt object")

        def accepted(_repo: Path, _backend: Path, source: Path) -> census.LeanResult:
            source.with_suffix(".olean").write_bytes(b"synthetic audit object")
            return census.LeanResult(0, "'Vsa.A.t' does not depend on any axioms")

        with (
            patch.object(
                build, "compile_module", side_effect=compile_fake
            ) as compile_module,
            patch.object(census, "run_lean", side_effect=accepted),
        ):
            first = self.run_check()
            assert first is not None
            report = json.loads(first.read_text())
            self.assertEqual(report["counts"]["build"], 2)
            self.assertEqual(set(report["build_seconds"]), {"Vsa.A", "Vsa.B"})
            self.assertEqual(
                report["timing_seconds"]["dependency_compile"],
                sum(report["build_seconds"].values()),
            )
            compile_module.reset_mock()
            second = self.run_check()
            assert second is not None
            self.assertEqual(
                json.loads(second.read_text())["counts"]["reuse-output"], 2
            )
            compile_module.assert_not_called()


class AuditSourceStructureTests(unittest.TestCase):
    def test_structure_selects_the_residual_record(self) -> None:
        default = proof.audit_source(["M"], [], "hInt", "s")
        self.assertIn(
            f"census_probe {census.STRUCTURE} hInt at {census.LAYOUT} using s", default
        )
        clause = proof.audit_source(
            ["M"], [], "hInt", "s", "Vsa.Sim.IHClause.T.Residuals"
        )
        self.assertIn("census_probe Vsa.Sim.IHClause.T.Residuals hInt at", clause)
        self.assertNotIn(census.STRUCTURE, clause)
        with self.assertRaisesRegex(ValueError, "requires a supplier"):
            proof.audit_source(["M"], [], "hInt", None)


if __name__ == "__main__":
    unittest.main()
