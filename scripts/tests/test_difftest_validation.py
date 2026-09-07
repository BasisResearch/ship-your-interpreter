"""Reject incomplete differential-test inputs without running Lean, C, or Z3."""

import os
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from scripts import difftest


class DifftestValidationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name)
        self.trace = self.directory / "case.trace.tsv"
        self.image = SimpleNamespace(word=lambda _pc: 0x00B53023)  # sd a1,0(a0)
        self.symbols = patch.object(
            difftest, "elf_symbols", return_value={"tohost": 0x8001AD00}
        )
        self.symbols.start()
        self.addCleanup(self.symbols.stop)

    def row(self, command: int = 1) -> str:
        registers = [0] * 31
        registers[9] = 0x8001AD00
        registers[10] = command
        columns = ["T", "0", "80000190", "80000194"]
        columns += [f"{value:x}" for value in registers]
        columns += ["S8", "8001ad00", "0", "0", "O", "0", "0", "256"]
        return "\t".join(columns) + "\n"

    def test_nonzero_source_exit_requires_real_matching_htif_command(self) -> None:
        self.trace.write_text(self.row(3))
        result = difftest.trace_completion(str(self.trace), self.image, 1)
        self.assertEqual(result, difftest.TraceCompletion(rows=1, exit_code=1))
        with self.assertRaisesRegex(ValueError, "disagrees"):
            difftest.trace_completion(str(self.trace), self.image, 0)

    def test_fuel_sail_error_empty_and_putchar_are_not_complete(self) -> None:
        cases = (
            (self.row() + "TRACE-FUEL-OUT\n", "step budget"),
            (
                self.row() + "Error while running the sail program!: Unreachable\n",
                "Sail error",
            ),
            (self.row() + "TRACE-RUN-FAILED\n", "did not complete"),
            ("", "no execution rows"),
            (self.row(0x010100000000000A), "not an HTIF exit"),
        )
        for content, message in cases:
            with self.subTest(message=message):
                self.trace.write_text(content)
                with self.assertRaisesRegex(ValueError, message):
                    difftest.trace_completion(str(self.trace), self.image, 0)

    def test_failed_process_trace_cannot_be_reused_as_success(self) -> None:
        def emulate(_command: list[str], **kwargs: object) -> SimpleNamespace:
            kwargs["stderr"].write(self.row())
            return SimpleNamespace(returncode=1)

        with (
            patch.object(difftest.subprocess, "run", side_effect=emulate),
            patch.object(difftest, "Image", return_value=self.image),
        ):
            with self.assertRaisesRegex(ValueError, "disagrees"):
                difftest.run_trace("case.elf", str(self.trace))
        with self.assertRaisesRegex(ValueError, "did not complete"):
            difftest.trace_completion(str(self.trace), self.image)

    def test_timeout_preserves_rows_and_marks_trace_unusable(self) -> None:
        def timeout(command: list[str], **kwargs: object) -> None:
            kwargs["stderr"].write(self.row())
            raise subprocess.TimeoutExpired(command, 1)

        with patch.object(difftest.subprocess, "run", side_effect=timeout):
            with self.assertRaises(subprocess.TimeoutExpired):
                difftest.run_trace("case.elf", str(self.trace), timeout=1)
        self.assertIn("T\t0", self.trace.read_text())
        with self.assertRaisesRegex(ValueError, "did not complete"):
            difftest.trace_completion(str(self.trace), self.image)

    def test_empty_trace_directory_and_zero_sampling_are_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "no trace files"):
            difftest.trace_files(str(self.directory))
        with self.assertRaisesRegex(ValueError, "positive"):
            difftest.phase3_samples([], None, 0)

    def test_unmatched_selection_cannot_remove_every_obligation(self) -> None:
        rows = [{"field": "q", "residual": "field"}]
        for selection in ({"typo"}, {"q", "typo"}, set()):
            with self.subTest(selection=selection):
                with self.assertRaisesRegex(ValueError, "unmatched"):
                    difftest.select_span_rows(rows, selection)
        self.assertEqual(difftest.select_span_rows(rows, {"field"}), rows)
        with self.assertRaisesRegex(ValueError, "no selected"):
            difftest.select_span_rows([], None)

    def test_unobserved_and_unpaired_claimed_clauses_are_failures(self) -> None:
        rows = [
            {
                "summary": "callee_x",
                "clause": "sp_restore",
                "claimed": "mined",
                "holds": 0,
                "refuted": 0,
                "instances": 1,
                "nopair": 1,
            }
        ]
        mined = {"callee_x": ["sp_restore"], "loop_y": ["ra_restore"]}
        findings = difftest.phase2_findings(rows, mined)
        self.assertEqual(
            {finding[1] for finding in findings},
            {"callee_x/sp_restore", "loop_y/ra_restore"},
        )
        self.assertEqual(difftest.phase2_findings([], {})[0][0], "NO-CLAUSES")

    def test_missing_clause_file_is_not_an_empty_success(self) -> None:
        with self.assertRaises(FileNotFoundError):
            difftest.phase2_report({}, self.image, str(self.directory))

    def test_empty_phase3_has_a_failure_finding(self) -> None:
        (self.directory / "preamble.smt2").write_text("")
        with (
            patch.object(difftest, "EncTable"),
            patch.object(difftest, "mmio_region", return_value=(0, 0)),
        ):
            findings, *_ = difftest.phase3([], self.image, str(self.directory))
        self.assertEqual(findings[0][0], "NO-SAMPLES")

    def test_z3_failure_or_timeout_cannot_accept_true_stdout(self) -> None:
        (self.directory / "preamble.smt2").write_text("")
        trace = SimpleNamespace(
            n=2, pc=[0x80000190, 0x80000194], mk=[0, 0], name="case", step=[0, 1]
        )
        table = SimpleNamespace(get=lambda _pc: ("alu", []))
        failures = (
            SimpleNamespace(returncode=1, stdout="true\n", stderr=""),
            SimpleNamespace(returncode=0, stdout="true\n", stderr="error"),
            subprocess.TimeoutExpired("z3", 1),
        )
        for failure in failures:
            with (
                self.subTest(failure=failure),
                patch.object(difftest, "EncTable", return_value=table),
                patch.object(difftest, "mmio_region", return_value=(0, 0)),
                patch.object(difftest, "phase3_block", return_value=([], "ok0", [])),
                patch.object(difftest.subprocess, "run") as run,
            ):
                if isinstance(failure, Exception):
                    run.side_effect = failure
                else:
                    run.return_value = failure
                findings, _, checked, _, _ = difftest.phase3(
                    [trace], self.image, str(self.directory), jobs=1
                )
                self.assertEqual(checked, 1)
                self.assertTrue(any("Z3ERR" in finding[2] for finding in findings))

    def test_corpus_rejects_duplicate_basename_and_oversize_program(self) -> None:
        with self.assertRaisesRegex(ValueError, "distinct"):
            difftest.build_corpus(["a/x.wl", "b/x.wl"], str(self.directory))
        script = self.directory / "large.wl"
        script.write_bytes(b"oversized")
        reference = self.directory / "reference.wl"
        reference.write_bytes(b"x")
        proof = SimpleNamespace(segs=[(0, 0, 1)], raw=b"x")
        with (
            patch.object(difftest, "REF_SCRIPT", str(reference)),
            patch.object(difftest, "Image", return_value=proof),
        ):
            with self.assertRaisesRegex(ValueError, "exceeds script capacity"):
                difftest.build_corpus(
                    [str(script)], str(self.directory), workdir=str(self.directory)
                )

    def test_failed_build_is_not_silently_dropped(self) -> None:
        script = self.directory / "input.wl"
        script.write_bytes(b"x")
        (self.directory / "tests").mkdir()
        proof = SimpleNamespace(segs=[(0, 0, 2)], raw=b"x\0")
        with (
            patch.object(difftest, "REF_SCRIPT", str(script)),
            patch.object(difftest, "Image", return_value=proof),
            patch.object(
                difftest.subprocess,
                "run",
                return_value=SimpleNamespace(returncode=1, stdout="", stderr="bad"),
            ),
        ):
            with self.assertRaisesRegex(RuntimeError, "build failed"):
                difftest.build_corpus(
                    [str(script)], str(self.directory), workdir=str(self.directory)
                )

    def test_narrow_non_script_mutation_is_rejected(self) -> None:
        proof = SimpleNamespace(segs=[(0x1000, 0, 6)], raw=b"Ax\0BCD")
        image = SimpleNamespace(
            segs=proof.segs,
            raw=b"Ay\0XCD",
            byte=lambda address: b"Ay\0XCD"[address - 0x1000],
        )
        with patch.object(
            difftest, "elf_symbols", return_value={"_script_start": 0x1001}
        ):
            with self.assertRaisesRegex(ValueError, "non-script byte"):
                difftest.validate_corpus_image(proof, image, b"y")
            image.raw = b"Ay\0BCD"
            image.byte = lambda address: image.raw[address - 0x1000]
            difftest.validate_corpus_image(proof, image, b"y")


class DifftestDriverFailureTests(unittest.TestCase):
    def test_child_failure_stops_phases_and_stale_elf_is_not_traced(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "scripts").mkdir()
            shutil.copyfile(
                Path(difftest.ROOT) / "scripts/difftest.sh",
                root / "scripts/difftest.sh",
            )
            binary = root / "bin"
            binary.mkdir()
            for command, body in (
                ("lake", "exit 0"),
                (
                    "shasum",
                    "echo b146c6edb76ea9a0f0f30be381f8176ed2de9717e1ae9b37feff4b2b9ca1d0f0 proof",
                ),
            ):
                stub = binary / command
                stub.write_text(f"#!/bin/sh\n{body}\n")
                stub.chmod(0o755)
            python = binary / "python3"
            python.write_text(
                f"#!{sys.executable}\n"
                "import os, pathlib, sys\n"
                "args = sys.argv[1:]\n"
                "with open(os.environ['CALLS'], 'a') as f: f.write(' '.join(args) + '\\n')\n"
                "if len(args)>1 and args[1]=='corpus':\n"
                "    out=pathlib.Path(args[args.index('--out')+1])\n"
                "    for src in args[2:args.index('--out')]: (out/(pathlib.Path(src).stem+'.elf')).write_text('elf')\n"
                "if len(args)>1 and args[1]=='trace':\n"
                "    pathlib.Path(args[args.index('--out')+1]).write_text('trace')\n"
                "    sys.exit(1 if pathlib.Path(args[2]).stem=='bad' else 0)\n"
            )
            python.chmod(0o755)
            emulator = (
                root / "riscv-lean/lean_emulator/.lake/build/bin/lean_riscv_emulator"
            )
            emulator.parent.mkdir(parents=True)
            emulator.write_text("#!/bin/sh\nexit 99\n")
            emulator.chmod(0o755)
            authority = root / "authority"
            authority.mkdir()
            (authority / "segment-authority.json").write_text("{}")
            output = root / "output"
            (output / "elfs").mkdir(parents=True)
            (output / "elfs/stale.elf").write_text("stale")
            calls = root / "calls"
            result = subprocess.run(
                [
                    "bash",
                    str(root / "scripts/difftest.sh"),
                    "--out",
                    str(output),
                    "--segment-authority",
                    str(authority),
                    "bad.wl",
                    "good.wl",
                ],
                env=dict(
                    os.environ,
                    PATH=f"{binary}:{os.environ['PATH']}",
                    CALLS=str(calls),
                    DIFFTEST_JOBS="2",
                    VSA_PRIVATE_BUILD=str(root / "private backend"),
                    VSA_EMULATOR_RECEIPT=str(root / "emulator-receipt.json"),
                ),
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("emulator runs failed", result.stderr)
            called = calls.read_text()
            self.assertIn("bad.elf", called)
            self.assertIn("good.elf", called)
            self.assertNotIn("stale.elf", called)
            self.assertNotIn("phase1", called)


class EmulatorReceiptTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.repo = self.base / "repo"
        self.project = self.repo / "riscv-lean/lean_emulator"
        self.project.mkdir(parents=True)
        (self.repo / "lean-toolchain").write_text("toolchain-version")
        (self.project / "lean-toolchain").write_text("toolchain-version")
        (self.project / "Main.lean").write_text("def main := pure ()")
        self.dependency = self.repo / "riscv-lean/dependency"
        self.dependency.mkdir()
        (self.dependency / "Runtime.lean").write_text("def runtime := 1")
        (self.project / "lake-manifest.json").write_text(
            json.dumps(
                {
                    "packagesDir": ".lake/packages",
                    "packages": [{"type": "path", "dir": "../dependency"}],
                }
            )
        )
        self.binary = self.project / ".lake/build/bin/lean_riscv_emulator"
        self.receipt = self.base / "receipt.json"
        self.tools = {
            name: {"path": f"/toolchain/{name}", "sha256": name}
            for name in ("lean", "lake")
        }
        self.toolchain_patch = patch.object(
            difftest, "emulator_toolchain", return_value=self.tools
        )
        self.toolchain_patch.start()
        self.addCleanup(self.toolchain_patch.stop)

    def build(self) -> None:
        def compile_binary(*_args: object, **_kwargs: object) -> None:
            self.binary.parent.mkdir(parents=True, exist_ok=True)
            self.binary.write_bytes(b"compiled binary")
            self.binary.chmod(0o755)

        with patch.object(
            difftest.subprocess, "run", side_effect=compile_binary
        ) as run:
            difftest.build_emulator(
                self.repo, self.receipt, {"PATH": "/bin", "LEAN_PATH": "/stale"}
            )
        self.assertEqual(
            run.call_args.args[0],
            [
                "/toolchain/lake",
                "--rehash",
                "--no-cache",
                "build",
                "lean_riscv_emulator",
            ],
        )
        self.assertNotIn("LEAN_PATH", run.call_args.kwargs["env"])
        self.assertEqual(run.call_args.kwargs["env"]["LEAN_NUM_THREADS"], "1")

    def test_existing_executable_without_receipt_is_rejected(self) -> None:
        self.binary.parent.mkdir(parents=True)
        self.binary.write_bytes(b"old binary")
        self.binary.chmod(0o755)
        with self.assertRaises(FileNotFoundError):
            difftest.verify_emulator_receipt(self.repo, self.receipt)

    def test_actual_build_receipt_detects_source_dependency_toolchain_and_binary_drift(
        self,
    ) -> None:
        self.build()
        self.assertEqual(
            difftest.verify_emulator_receipt(self.repo, self.receipt), self.binary
        )
        for path in (
            self.project / "Main.lean",
            self.dependency / "Runtime.lean",
            self.repo / "lean-toolchain",
            self.binary,
        ):
            with self.subTest(path=path):
                original = path.read_bytes()
                path.write_bytes(original + b"changed")
                with self.assertRaisesRegex(ValueError, "stale"):
                    difftest.verify_emulator_receipt(self.repo, self.receipt)
                path.write_bytes(original)
        with patch.object(
            difftest,
            "emulator_toolchain",
            return_value={"lean": {"sha256": "different"}, "lake": self.tools["lake"]},
        ):
            with self.assertRaisesRegex(ValueError, "stale"):
                difftest.verify_emulator_receipt(self.repo, self.receipt)

    def test_failed_or_drifting_build_cannot_mint_receipt(self) -> None:
        self.build()
        self.assertTrue(self.receipt.exists())
        with patch.object(
            difftest.subprocess,
            "run",
            side_effect=subprocess.CalledProcessError(1, "lake"),
        ):
            with self.assertRaises(subprocess.CalledProcessError):
                difftest.build_emulator(self.repo, self.receipt, {})
        self.assertFalse(self.receipt.exists())

        def mutate(*_args: object, **_kwargs: object) -> None:
            (self.dependency / "Runtime.lean").write_text("changed during build")

        with patch.object(difftest.subprocess, "run", side_effect=mutate):
            with self.assertRaisesRegex(ValueError, "changed during"):
                difftest.build_emulator(self.repo, self.receipt, {})
        self.assertFalse(self.receipt.exists())

    def test_source_inventory_detects_new_files_and_uses_resolved_git_dependency(
        self,
    ) -> None:
        package = self.project / ".lake/packages/Dependency"
        package.mkdir(parents=True)
        source = package / "Foreign.c"
        source.write_text("int foreign = 1;")
        manifest = {
            "packagesDir": ".lake/packages",
            "packages": [{"type": "git", "name": "Dependency", "subDir": None}],
        }
        (self.project / "lake-manifest.json").write_text(json.dumps(manifest))
        self.build()
        self.assertEqual(
            difftest.verify_emulator_receipt(self.repo, self.receipt), self.binary
        )
        source.write_text("int foreign = 2;")
        with self.assertRaisesRegex(ValueError, "stale"):
            difftest.verify_emulator_receipt(self.repo, self.receipt)


class DirectTraceReceiptTests(unittest.TestCase):
    def arguments(self, output: Path, receipt: str | None = None) -> SimpleNamespace:
        return SimpleNamespace(
            elf="case.elf",
            out=str(output),
            trace_pcs=None,
            max_steps=None,
            emulator_receipt=receipt,
        )

    def test_missing_and_stale_receipts_prevent_direct_execution(self) -> None:
        with (
            patch.dict(os.environ, {}, clear=True),
            patch.object(difftest, "run_trace") as run,
        ):
            with self.assertRaisesRegex(ValueError, "receipt"):
                difftest.cmd_trace(self.arguments(Path("unused")))
            with patch.object(
                difftest, "verify_emulator_receipt", side_effect=ValueError("stale")
            ):
                with self.assertRaisesRegex(ValueError, "stale"):
                    difftest.cmd_trace(self.arguments(Path("unused"), "receipt.json"))
            run.assert_not_called()

    def test_environment_receipt_is_checked_before_and_after_execution(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "case.trace.tsv"
            with (
                patch.dict(os.environ, {"VSA_EMULATOR_RECEIPT": "receipt.json"}),
                patch.object(difftest, "verify_emulator_receipt") as verify,
                patch.object(difftest, "run_trace") as run,
            ):
                difftest.cmd_trace(self.arguments(output))
                self.assertEqual(verify.call_count, 2)
                run.assert_called_once()

    def test_drift_during_execution_invalidates_trace_for_phase_only_reuse(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "case.trace.tsv"
            output.write_text("diagnostic rows\n")
            with (
                patch.object(
                    difftest,
                    "verify_emulator_receipt",
                    side_effect=[None, ValueError("stale")],
                ),
                patch.object(difftest, "run_trace"),
            ):
                with self.assertRaisesRegex(ValueError, "stale"):
                    difftest.cmd_trace(self.arguments(output, "receipt.json"))
            self.assertIn("TRACE-RUN-FAILED", output.read_text())


class DifftestFreshBackendDriverTests(unittest.TestCase):
    def test_stale_backend_or_emulator_stops_before_lake_and_private_path_is_quoted(
        self,
    ) -> None:
        for failure in ("backend", "emulator", "lean-path"):
            with (
                self.subTest(failure=failure),
                tempfile.TemporaryDirectory() as directory,
            ):
                root = Path(directory)
                (root / "scripts").mkdir()
                shutil.copyfile(
                    Path(difftest.ROOT) / "scripts/difftest.sh",
                    root / "scripts/difftest.sh",
                )
                binary = root / "bin"
                binary.mkdir()
                calls = root / "calls"
                python = binary / "python3"
                python.write_text(
                    f"#!{sys.executable}\n"
                    + "import os, sys\n"
                    + "args=sys.argv[1:]\n"
                    + "with open(os.environ['CALLS'],'a') as f: f.write(' '.join(args)+'\\n')\n"
                    + "if os.environ['FAILURE']=='backend' and args[0].endswith('check_validation.py'): sys.exit(2)\n"
                    + "if os.environ['FAILURE']=='emulator' and 'verify-emulator' in args: sys.exit(2)\n"
                )
                python.chmod(0o755)
                lake = binary / "lake"
                lake.write_text('#!/bin/sh\nshift\nexec "$@"\n')
                lake.chmod(0o755)
                lean = binary / "lean"
                lean.write_text(
                    '#!/bin/sh\nprintf "LEAN_PATH=%s\\n" "$LEAN_PATH" >> "$CALLS"\nexit 99\n'
                )
                lean.chmod(0o755)
                hasher = binary / "shasum"
                hasher.write_text(
                    "#!/bin/sh\necho b146c6edb76ea9a0f0f30be381f8176ed2de9717e1ae9b37feff4b2b9ca1d0f0 proof\n"
                )
                hasher.chmod(0o755)
                authority = root / "authority"
                authority.mkdir()
                (authority / "segment-authority.json").write_text("{}")
                backend = root / "private build with spaces"
                result = subprocess.run(
                    [
                        "bash",
                        str(root / "scripts/difftest.sh"),
                        "--out",
                        str(root / "out space"),
                        "--segment-authority",
                        str(authority),
                        "--emulator-receipt",
                        str(root / "receipt"),
                        "test.wl",
                    ],
                    env=dict(
                        os.environ,
                        PATH=f"{binary}:{os.environ['PATH']}",
                        CALLS=str(calls),
                        FAILURE=failure,
                        VSA_PRIVATE_BUILD=str(backend),
                        LEAN_PATH="/stale/local",
                    ),
                    text=True,
                    capture_output=True,
                    check=False,
                )
                self.assertNotEqual(result.returncode, 0)
                logged = calls.read_text()
                if failure == "lean-path":
                    self.assertIn(f"LEAN_PATH={backend}:", logged)
                    self.assertIn(":/stale/local", logged)
                else:
                    self.assertNotIn("LEAN_PATH=", logged)
                    self.assertIn("stale", result.stderr)


if __name__ == "__main__":
    unittest.main()
