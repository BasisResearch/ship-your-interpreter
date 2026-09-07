"""The required gate must reject stale builds and detected boundary failures."""

import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import build_private, check_validation


class ValidationGateTests(unittest.TestCase):
    def test_backend_requires_all_current_modules_and_outputs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Vsa").mkdir()
            (root / "Vsa/A.lean").write_text("def a := 1\n")
            (root / "Vsa.lean").write_text("import Vsa.A\n")
            (root / "VsaRun.lean").write_text("import Vsa\n")
            backend = root / "backend"
            backend.mkdir()
            order = build_private.topological_order(build_private.discover_modules(root, True))
            fingerprints = build_private.module_fingerprints(
                root, order, build_private.input_context(root)
            )
            build_private.write_manifest(backend / build_private.MANIFEST_NAME, fingerprints)
            for module in order:
                output = build_private.output_path(backend, module)
                output.parent.mkdir(parents=True, exist_ok=True)
                output.write_bytes(b"test object")
            check_validation.verify_backend(root, backend)
            (root / "Vsa/A.lean").write_text("def a := 2\n")
            with self.assertRaisesRegex(build_private.BuildError, "stale private backend"):
                check_validation.verify_backend(root, backend)

    def test_skip_build_cannot_bypass_fingerprint_check(self):
        with tempfile.TemporaryDirectory() as directory:
            environment = dict(check_validation.os.environ, VSA_PRIVATE_BUILD=directory)
            result = subprocess.run(
                ["bash", "scripts/check_all.sh", "--skip-build"],
                cwd=Path(__file__).resolve().parents[2], env=environment,
                capture_output=True, text=True, check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("stale private backend", result.stderr)

    def test_known_finding_is_not_a_green_gate(self):
        for boundary_code, test_code in ((1, 0), (0, 1), (2, 0)):
            with self.subTest(boundary_code=boundary_code, test_code=test_code):
                with patch.object(check_validation, "verify_backend"), patch.object(
                    check_validation.subprocess, "run", side_effect=[
                        subprocess.CompletedProcess([], 0),
                        subprocess.CompletedProcess([], boundary_code),
                        subprocess.CompletedProcess([], test_code),
                    ]
                ) as run:
                    result = check_validation.main(["--backend", "/tmp/cache", "--output", "/tmp/run"])
                self.assertNotEqual(result, 0)
                self.assertNotIn("--self-test", run.call_args_list[1].args[0])
                self.assertIn("BOUNDARY_REGRESSION_ARTIFACTS", run.call_args.kwargs["env"])

    def test_failed_full_library_inventory_stops_validation(self):
        for status in (1, 2, -9):
            with self.subTest(status=status), patch.object(
                check_validation, "verify_backend"
            ), patch.object(
                check_validation.subprocess, "run",
                return_value=subprocess.CompletedProcess([], status),
            ) as run:
                result = check_validation.main(
                    ["--backend", "/tmp/cache", "--output", "/tmp/run"]
                )
                self.assertEqual(result, 2)
                run.assert_called_once()
                command = run.call_args.args[0]
                self.assertIn("scripts/field_census.py", command)
                self.assertIn("--inventory-only", command)
                self.assertIn("/tmp/run-census", command)


if __name__ == "__main__":
    unittest.main()
