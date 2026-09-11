"""Opt-in Lean checks for checkpoint evidence, using only temporary projects.

Run with exclusive compiler access:
``VSA_NATIVE_CHECKPOINT_TESTS=1 python3 -B -m unittest
scripts.tests.test_proof_checkpoint_native``.
"""

import json
import os
import tempfile
import unittest
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path

from scripts import build_private as build
from scripts import proof_checkpoint as checkpoint
from scripts import proof_slice as proof

ENABLED = os.environ.get("VSA_NATIVE_CHECKPOINT_TESTS") == "1"


@unittest.skipUnless(ENABLED, "requires explicit serial Lean validation")
class NativeCheckpointTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.temp = tempfile.TemporaryDirectory(prefix="vsa-checkpoint-native-")
        cls.addClassCleanup(cls.temp.cleanup)
        root = Path(cls.temp.name)
        cls.repo = root / "repo"
        cls.backend = root / "backend"
        cls.output = root / "output"
        cls.repo.mkdir()
        cls.backend.mkdir()
        (cls.repo / "Vsa").mkdir()
        (cls.repo / "lean-toolchain").write_text(
            (proof.ROOT / "lean-toolchain").read_text()
        )
        (cls.repo / "lakefile.toml").write_text('name = "CheckpointFixture"\n')
        (cls.repo / "Vsa.lean").write_text(
            "namespace WorkflowFixture\n"
            "theorem helper : True := True.intro\n"
            "theorem conditional : True → True := fun h => h\n"
            "theorem dependent : (n : Nat) → n = n → True := fun _ _ => True.intro\n"
            "theorem final : True := helper\n"
            "axiom rejectedAxiom : False\n"
            "theorem unsafeConsumer : False := rejectedAxiom\n"
            "end WorkflowFixture\n"
        )
        (cls.repo / "VsaRun.lean").write_text("import Vsa\n")
        # Lake may create its empty manifest. Establish it before fingerprinting.
        (cls.repo / "lake-manifest.json").write_text(
            '{"version":"1.1.0","packagesDir":".lake/packages",'
            '"packages":[],"name":"CheckpointFixture","lakeDir":".lake"}\n'
        )
        build.write_manifest(cls.backend / build.MANIFEST_NAME, {})

    def run_checkpoint(
        self,
        consumer: str,
        *,
        target_type: str = "True",
        role: str = "target",
        premises: list[dict[str, str]] | None = None,
    ) -> dict:
        description = {
            "target_obligation": "native_fixture_target",
            "target_type": target_type,
            "consumer": "WorkflowFixture." + consumer,
            "role": role,
            "remaining_premises": premises or [],
        }
        if role == "prerequisite":
            description["consumer_type"] = "True"
        path = Path(self.temp.name) / "checkpoint.json"
        path.write_text(json.dumps(description))
        progress = checkpoint.read_checkpoint(path)
        with redirect_stdout(StringIO()):
            receipt = proof.execute(
                self.repo,
                self.backend,
                self.output,
                ["Vsa"],
                [],
                None,
                None,
                False,
                progress=progress,
            )
        assert receipt is not None
        return json.loads(receipt.read_text())

    def test_complete_target_has_checked_application(self) -> None:
        report = self.run_checkpoint("final")
        self.assertEqual(report["checkpoint"]["status"], "complete")
        self.assertEqual(report["axioms"][checkpoint.WITNESS], [])

    def test_conditional_target_retains_premise(self) -> None:
        report = self.run_checkpoint(
            "conditional", premises=[{"name": "child", "type": "True"}]
        )
        self.assertEqual(report["checkpoint"]["status"], "conditional")

    def test_dependent_premises_elaborate_at_exact_type(self) -> None:
        report = self.run_checkpoint(
            "dependent",
            premises=[
                {"name": "n", "type": "Nat"},
                {"name": "same", "type": "n = n"},
            ],
        )
        self.assertEqual(report["checkpoint"]["status"], "conditional")

    def test_helper_does_not_close_different_target(self) -> None:
        report = self.run_checkpoint("helper", target_type="False", role="prerequisite")
        self.assertEqual(report["checkpoint"]["status"], "prerequisite")

    def test_wrong_type_and_free_parameter_leave_no_success_receipt(self) -> None:
        for consumer, type_ in (("conditional", "True"), ("final", "UnknownGoal")):
            with self.subTest(consumer=consumer, target_type=type_):
                before = set(self.output.rglob("receipt.json"))
                with self.assertRaises(build.BuildError):
                    self.run_checkpoint(consumer, target_type=type_)
                self.assertEqual(before, set(self.output.rglob("receipt.json")))

    def test_nonstandard_axiom_leaves_no_success_receipt(self) -> None:
        before = set(self.output.rglob("receipt.json"))
        with self.assertRaisesRegex(ValueError, "nonstandard axioms"):
            self.run_checkpoint("unsafeConsumer", target_type="False")
        self.assertEqual(before, set(self.output.rglob("receipt.json")))
