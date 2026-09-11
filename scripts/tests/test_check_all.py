"""Tests for the ordering and modes of the repository-wide check gate."""

import os
import shutil
import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[2]
CHECK_ALL = REPOSITORY / "scripts" / "check_all.sh"
SOURCE_STAGES = (
    "gen_term_case_bundle",
    "gen_allocator_cases",
    "gen_m4_term_row",
    "gen_ih_clause",
    "gen_footprint_row",
    "check_discipline",
    "ih_clause_status",
)
COMPILED_STAGES = {"build", "freshness", "boundary", "axioms"}


class CheckAllTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary_directory = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary_directory.name)
        (self.root / "scripts").mkdir()
        (self.root / "Vsa").mkdir()
        (self.root / "bin").mkdir()
        shutil.copy2(CHECK_ALL, self.root / "scripts" / "check_all.sh")
        (self.root / "Vsa" / "Main.lean").write_text(
            "theorem fixture_ok : True := by trivial\n", encoding="utf-8"
        )
        self.trace_path = self.root / "trace"
        self._install_python_stubs()
        self._install_lake_stub()

    def tearDown(self) -> None:
        self.temporary_directory.cleanup()

    def _write_executable(self, path: Path, source: str) -> None:
        path.write_text(textwrap.dedent(source).lstrip(), encoding="utf-8")
        path.chmod(0o755)

    def _install_python_stubs(self) -> None:
        stub = """
            import os
            from pathlib import Path
            import sys

            name = Path(__file__).stem
            if name == "check_validation":
                if "--build-backend" in sys.argv:
                    stage = "build"
                elif "--output" in sys.argv:
                    stage = "boundary"
                else:
                    stage = "freshness"
            else:
                stage = name
            with Path(os.environ["CHECK_ALL_TRACE"]).open("a", encoding="utf-8") as trace:
                trace.write(stage + "\\n")
            if os.environ.get("FAIL_STAGE") == stage:
                raise SystemExit(1)
        """
        names = (
            "gen_term_case_bundle",
            "gen_allocator_cases",
            "gen_m4_term_row",
            "gen_ih_clause",
            "gen_footprint_row",
            "check_discipline",
            "ih_clause_status",
            "check_validation",
        )
        for name in names:
            (self.root / "scripts" / f"{name}.py").write_text(
                textwrap.dedent(stub), encoding="utf-8"
            )

    def _install_lake_stub(self) -> None:
        self._write_executable(
            self.root / "bin" / "lake",
            """
            #!/usr/bin/env python3
            import os
            from pathlib import Path
            import sys

            with Path(os.environ["CHECK_ALL_TRACE"]).open("a", encoding="utf-8") as trace:
                trace.write("axioms\\n")
            axiom_file = Path(sys.argv[-1])
            for line in axiom_file.read_text(encoding="utf-8").splitlines():
                if line.startswith("#print axioms "):
                    name = line.removeprefix("#print axioms ")
                    print(f"'{name}' does not depend on any axioms")
            """,
        )

    def _run(
        self,
        *arguments: str,
        fail_stage: str | None = None,
        include_backend: bool = True,
    ) -> subprocess.CompletedProcess[str]:
        environment = os.environ.copy()
        environment["PATH"] = f"{self.root / 'bin'}{os.pathsep}{environment['PATH']}"
        environment["CHECK_ALL_TRACE"] = str(self.trace_path)
        if include_backend:
            environment["VSA_PRIVATE_BUILD"] = str(self.root / "backend")
        else:
            environment.pop("VSA_PRIVATE_BUILD", None)
        if fail_stage is not None:
            environment["FAIL_STAGE"] = fail_stage
        return subprocess.run(
            ["bash", "scripts/check_all.sh", *arguments],
            cwd=self.root,
            env=environment,
            capture_output=True,
            text=True,
            check=False,
        )

    def _trace(self) -> list[str]:
        if not self.trace_path.exists():
            return []
        return self.trace_path.read_text(encoding="utf-8").splitlines()

    def assert_no_compiled_stage(self) -> None:
        self.assertTrue(COMPILED_STAGES.isdisjoint(self._trace()), self._trace())

    def test_each_generator_failure_aborts_before_compiled_stages(self) -> None:
        for generator in SOURCE_STAGES[:5]:
            with self.subTest(generator=generator):
                self.trace_path.unlink(missing_ok=True)
                result = self._run(fail_stage=generator)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assert_no_compiled_stage()

    def test_discipline_failure_aborts_before_compiled_stages(self) -> None:
        result = self._run(fail_stage="check_discipline")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("discipline violation", result.stderr)
        self.assert_no_compiled_stage()

    def test_each_forbidden_form_aborts_before_compiled_stages(self) -> None:
        bad_sources = {
            "sorry": "theorem bad : True := by sorry\n",
            "native_decide": "theorem bad : True := by native_decide\n",
            "bv_decide": "theorem bad : True := by bv_decide\n",
            "axiom": "axiom bad : True\n",
        }
        source = self.root / "Vsa" / "Main.lean"
        for token, contents in bad_sources.items():
            with self.subTest(token=token):
                self.trace_path.unlink(missing_ok=True)
                source.write_text(contents, encoding="utf-8")
                result = self._run()
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn(token, result.stderr)
                self.assert_no_compiled_stage()

    def test_valid_fixture_reaches_every_compiled_stage(self) -> None:
        result = self._run()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(
            self._trace(),
            [*SOURCE_STAGES, "build", "freshness", "boundary", "axioms"],
        )

    def test_skip_build_still_checks_freshness_boundary_and_axioms(self) -> None:
        result = self._run("--skip-build")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(
            self._trace(), [*SOURCE_STAGES, "freshness", "boundary", "axioms"]
        )

    def test_skip_build_cannot_bypass_fingerprint_check(self) -> None:
        result = self._run("--skip-build", fail_stage="freshness")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("stale or incomplete private build", result.stderr)
        self.assertEqual(self._trace(), [*SOURCE_STAGES, "freshness"])

    def test_static_only_needs_no_backend_and_runs_no_compiled_stage(self) -> None:
        result = self._run("--static-only", include_backend=False)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self._trace(), list(SOURCE_STAGES))
        self.assertIn(
            "source-only checks passed; compiled checks NOT RUN", result.stdout
        )

    def test_informational_summary_failure_does_not_abort(self) -> None:
        result = self._run(fail_stage="ih_clause_status")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("clause status unavailable (informational", result.stdout)
        self.assertTrue(COMPILED_STAGES.issubset(self._trace()))


if __name__ == "__main__":
    unittest.main()
