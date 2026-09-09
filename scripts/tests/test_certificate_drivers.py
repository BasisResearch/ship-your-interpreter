"""Campaign wrappers reject unsupported authority before build or remote work."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


class CertificateDriverTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name)
        self.bin = self.directory / "bin"
        self.bin.mkdir()
        self.calls = self.directory / "calls"
        for command in ("lake", "ssh", "scp", "shasum"):
            stub = self.bin / command
            stub.write_text(
                '#!/bin/sh\nprintf "%s\\n" "$0" >> "$DRIVER_CALLS"\nexit 99\n'
            )
            stub.chmod(0o755)
        self.environment = dict(
            os.environ,
            PATH=f"{self.bin}:{os.environ['PATH']}",
            DRIVER_CALLS=str(self.calls),
            HOUDINI_STAGE=str(self.directory / "stage"),
        )
        self.environment.pop("VSA_PRIVATE_BUILD", None)

    def run_script(
        self, script: str, *arguments: str
    ) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["bash", str(ROOT / "scripts" / script), *arguments],
            env=self.environment,
            text=True,
            capture_output=True,
            check=False,
        )

    def test_local_driver_requires_independent_authority_before_build(self) -> None:
        result = self.run_script("difftest.sh")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("--segment-authority DIR is required", result.stderr)
        self.assertFalse(self.calls.exists())

    def test_remote_explicit_authority_refuses_before_remote_work(self) -> None:
        result = self.run_script(
            "houdini_summary_remote.sh", "--segment-authority", "/trusted receipt"
        )
        self.assertEqual(result.returncode, 2)
        self.assertIn("authority transport is unsupported", result.stderr)
        self.assertFalse(self.calls.exists())

    def test_remote_typed_campaign_refuses_before_build_or_shipping(self) -> None:
        stage = Path(self.environment["HOUDINI_STAGE"])
        stage.mkdir()
        (stage / "segment-certificates.tsv").write_text("query\tfield\nq\tf\n")
        result = self.run_script("houdini_summary_remote.sh")
        self.assertEqual(result.returncode, 2)
        self.assertIn("authority transport is unsupported", result.stderr)
        self.assertFalse(self.calls.exists())

    def test_legacy_remote_campaign_is_not_rejected_by_authority_gate(self) -> None:
        stage = Path(self.environment["HOUDINI_STAGE"])
        stage.mkdir()
        (stage / "segment-certificates.tsv").write_text("query\tfield\n\n")
        result = self.run_script("houdini_summary_remote.sh")
        self.assertNotIn("authority transport is unsupported", result.stderr)
        self.assertEqual(result.returncode, 2)
        self.assertIn("VSA_PRIVATE_BUILD must identify", result.stderr)
        self.assertFalse(self.calls.exists())

    def test_remote_invalid_backend_refuses_before_build_or_shipping(self) -> None:
        self.environment["VSA_PRIVATE_BUILD"] = str(self.directory / "missing")
        result = self.run_script("houdini_summary_remote.sh")
        self.assertEqual(result.returncode, 2)
        self.assertIn("private Lean backend is missing or stale", result.stderr)
        self.assertFalse(self.calls.exists())


if __name__ == "__main__":
    unittest.main()
