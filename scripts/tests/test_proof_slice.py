"""Check scoped-cache selection and rejection of incomplete proof evidence."""

import tempfile
import unittest
from argparse import ArgumentTypeError
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from unittest.mock import patch

from scripts import build_private as build
from scripts import field_census as census
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

    def run_check(self, *, plan_only: bool = False) -> Path | None:
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


if __name__ == "__main__":
    unittest.main()
