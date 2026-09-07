"""Tests for the serialized private Lean build driver."""

import tempfile
import unittest
import subprocess
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from unittest.mock import patch

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

    def test_rejected_compiler_output_preserves_previous_object(self) -> None:
        cases = (
            (1, "error: compilation failed"),
            (0, "warning: declaration uses `sorry`"),
            (0, "warning: declaration uses 'sorry'"),
            (0, "warning: declaration uses `admit`"),
            (0, "depends on axioms: [sorryAx]"),
        )
        for returncode, diagnostic in cases:
            with (
                self.subTest(diagnostic=diagnostic),
                tempfile.TemporaryDirectory() as directory,
            ):
                root = Path(directory)
                module = build_private.Module("Vsa.A", Path("Vsa/A.lean"), ())
                target = build_private.output_path(root, module)
                target.parent.mkdir(parents=True)
                target.write_bytes(b"previous synthetic object")

                def run(command, **kwargs):
                    Path(command[7]).write_bytes(b"rejected synthetic object")
                    return subprocess.CompletedProcess(
                        command, returncode, diagnostic, ""
                    )

                with patch.object(build_private.subprocess, "run", side_effect=run):
                    with self.assertRaises(build_private.BuildError):
                        build_private.compile_module(root, root, module)
                self.assertEqual(target.read_bytes(), b"previous synthetic object")
                self.assertEqual(
                    build_private.log_path(root, module).read_text(), diagnostic
                )
                self.assertEqual(list(target.parent.iterdir()), [target])

    def test_successful_compiler_must_produce_an_object(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            module = build_private.Module("Vsa.A", Path("Vsa/A.lean"), ())
            with patch.object(
                build_private.subprocess,
                "run",
                return_value=subprocess.CompletedProcess([], 0, "", ""),
            ):
                with self.assertRaisesRegex(
                    build_private.BuildError, "produced no object"
                ):
                    build_private.compile_module(root, root, module)
            self.assertFalse(build_private.output_path(root, module).exists())

    def test_accepted_compiler_output_replaces_previous_object(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            module = build_private.Module("Vsa.A", Path("Vsa/A.lean"), ())
            target = build_private.output_path(root, module)
            target.parent.mkdir(parents=True)
            target.write_bytes(b"previous synthetic object")

            def run(command, **kwargs):
                self.assertEqual(target.read_bytes(), b"previous synthetic object")
                Path(command[7]).write_bytes(b"accepted synthetic object")
                return subprocess.CompletedProcess(
                    command, 0, "warning: unused variable", ""
                )

            with patch.object(build_private.subprocess, "run", side_effect=run):
                build_private.compile_module(root, root, module)
            self.assertEqual(target.read_bytes(), b"accepted synthetic object")
            self.assertEqual(list(target.parent.iterdir()), [target])

    def test_failed_rebuild_retains_unrelated_cache_entries(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            repo, backend = root / "repo", root / "cache"
            (repo / "Vsa").mkdir(parents=True)
            (repo / "Vsa/A.lean").write_text("def a := 1\n")
            (repo / "Vsa/B.lean").write_text("import Vsa.A\ndef b := a\n")
            (repo / "Vsa/Z.lean").write_text("def z := 3\n")
            (repo / "Vsa.lean").write_text("import Vsa.B Vsa.Z\n")
            compiled = []

            def compile_ok(repo, backend, module):
                compiled.append(module.name)
                target = build_private.output_path(backend, module)
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(b"synthetic object")

            def compile_fail_b(repo, backend, module):
                if module.name == "Vsa.B":
                    raise build_private.BuildError("synthetic rejection")
                compile_ok(repo, backend, module)

            def run(compiler):
                with patch.object(
                    build_private, "compile_module", side_effect=compiler
                ):
                    with redirect_stdout(StringIO()):
                        build_private.build(
                            repo,
                            backend,
                            include_executable=False,
                            list_only=False,
                            resume=True,
                        )

            run(compile_ok)
            before = build_private.load_manifest(backend / build_private.MANIFEST_NAME)
            (repo / "Vsa/A.lean").write_text("def a := 2\n")
            with self.assertRaisesRegex(
                build_private.BuildError, "synthetic rejection"
            ):
                run(compile_fail_b)
            failed = build_private.load_manifest(backend / build_private.MANIFEST_NAME)
            self.assertEqual(failed["Vsa.Z"], before["Vsa.Z"])
            self.assertNotEqual(failed["Vsa.A"], before["Vsa.A"])
            self.assertNotIn("Vsa.B", failed)
            compiled.clear()
            run(compile_ok)
            self.assertEqual(compiled, ["Vsa.B", "Vsa"])

    def test_interruption_after_installation_cannot_reuse_old_fingerprint(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            repo, backend = root / "repo", root / "cache"
            repo.mkdir()
            source = repo / "Vsa.lean"
            source.write_text("def a := 1\n")
            installed = False
            interrupt = False
            write_manifest = build_private.write_manifest

            def compile_ok(repo, backend, module):
                nonlocal installed
                target = build_private.output_path(backend, module)
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(source.read_bytes())
                installed = True

            def publish(path, entries):
                if interrupt and installed:
                    raise OSError(
                        "synthetic interruption before fingerprint publication"
                    )
                write_manifest(path, entries)

            def run():
                with patch.object(
                    build_private, "compile_module", side_effect=compile_ok
                ):
                    with patch.object(
                        build_private, "write_manifest", side_effect=publish
                    ):
                        with redirect_stdout(StringIO()):
                            build_private.build(
                                repo,
                                backend,
                                include_executable=False,
                                list_only=False,
                                resume=True,
                            )

            run()
            source.write_text("def a := 2\n")
            installed = False
            interrupt = True
            with self.assertRaisesRegex(OSError, "synthetic interruption"):
                run()
            self.assertNotIn(
                "Vsa",
                build_private.load_manifest(backend / build_private.MANIFEST_NAME),
            )
            source.write_text("def a := 1\n")
            installed = False
            interrupt = False
            run()
            self.assertTrue(installed)
            self.assertEqual((backend / "Vsa.olean").read_bytes(), source.read_bytes())


if __name__ == "__main__":
    unittest.main()
