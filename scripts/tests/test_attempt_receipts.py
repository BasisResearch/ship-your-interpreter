"""Tests for immutable Lean attempt evidence and duplicate measurement."""

import copy
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import attempt_receipts as receipts
from scripts import build_private

SHA_A = "a" * 64
SHA_B = "b" * 64
SHA_C = "c" * 64


def complete_snapshot(
    *, dependency: str = SHA_B, toolchain: str = SHA_A
) -> receipts.BuildSnapshot:
    tool = receipts.FileFingerprint("/tool/lean", "/tool/lean", toolchain, 1, None)
    source = receipts.FileFingerprint(
        "/repo/Vsa/A.lean", "/repo/Vsa/A.lean", SHA_A, 1, None
    )
    object_ = receipts.FileFingerprint(
        "/backend/Vsa/A.olean", "/backend/Vsa/A.olean", SHA_C, 1, None
    )
    manifest = receipts.FileFingerprint(
        "/backend/manifest", "/backend/manifest", SHA_A, 1, None
    )
    environment = receipts.ArtifactInventory(
        "lean-toolchain-lib", "/toolchain/lib/lean", SHA_C, 1, 1, None
    )
    module = receipts.DependencyFingerprint(
        "Vsa.A", source, dependency, dependency, object_, True
    )
    return receipts.BuildSnapshot(
        "2026-09-11T00:00:00+00:00",
        ("Vsa.A",),
        SHA_C,
        (tool,),
        manifest,
        (module,),
        (),
        (environment,),
        "",
        (),
    )


def attempt_inputs(
    candidate: str = "by exact h",
) -> tuple[tuple[str, ...], receipts.Blob, tuple[receipts.CandidateInput, ...]]:
    target = "N.Residuals.hCall"
    source = receipts.Blob.from_text(
        "import Vsa.A\ntheorem draft : True := by exact True.intro\n"
    )
    item = receipts.CandidateInput(
        target,
        "N.draft_hCall_1",
        "exact:h",
        receipts.Blob.from_text("True"),
        receipts.Blob.from_text(candidate),
    )
    return (target,), source, (item,)


def completed_receipt(
    *, candidate: str = "by exact h", snapshot: receipts.BuildSnapshot | None = None
) -> dict[str, object]:
    targets, source, candidates = attempt_inputs(candidate)
    evidence = snapshot or complete_snapshot()
    return receipts.make_receipt(
        targets=targets,
        source=source,
        candidates=candidates,
        before=evidence,
        after=evidence,
        started_at="2026-09-11T00:00:00+00:00",
        finished_at="2026-09-11T00:00:01+00:00",
        wall_seconds=1.0,
        returncode=1,
        diagnostics="error: failed",
        failure_class="compiler_diagnostic",
        rerun_reason=None,
    )


class ComparisonKeyTests(unittest.TestCase):
    def test_key_changes_with_each_semantic_input(self) -> None:
        targets, source, candidates = attempt_inputs()
        original = receipts.comparison_payload(
            targets, source, candidates, complete_snapshot()
        )
        assert original is not None
        key = receipts.comparison_key(original)
        self.assertEqual(key, receipts.comparison_key(copy.deepcopy(original)))

        variants = []
        target = copy.deepcopy(original)
        target["targets"][0] = "N.Residuals.hInt"
        variants.append(target)
        statement = copy.deepcopy(original)
        statement["candidates"][0]["statement_sha256"] = SHA_B
        variants.append(statement)
        candidate = copy.deepcopy(original)
        candidate["candidates"][0]["candidate_sha256"] = SHA_B
        variants.append(candidate)
        dependency = copy.deepcopy(original)
        dependency["dependency_fingerprints"]["Vsa.A"] = SHA_C
        variants.append(dependency)
        toolchain = copy.deepcopy(original)
        toolchain["toolchain_fingerprints"]["/tool/lean"] = SHA_C
        variants.append(toolchain)
        self.assertTrue(all(receipts.comparison_key(item) != key for item in variants))

    def test_missing_or_unencodable_inputs_have_no_key(self) -> None:
        targets, source, candidates = attempt_inputs()
        payload = receipts.comparison_payload(
            targets, source, candidates, complete_snapshot()
        )
        assert payload is not None
        missing = copy.deepcopy(payload)
        missing["dependency_fingerprints"] = {}
        self.assertIsNone(receipts.comparison_key(missing))
        unencodable = copy.deepcopy(payload)
        unencodable["targets"] = {"N.Residuals.hCall"}
        self.assertIsNone(receipts.comparison_key(unencodable))
        malformed_hash = copy.deepcopy(payload)
        malformed_hash["candidates"][0]["statement_sha256"] = 3
        self.assertIsNone(receipts.comparison_key(malformed_hash))
        unavailable = receipts.fingerprint_file(Path(tempfile.gettempdir()))
        self.assertIsNone(unavailable.sha256)
        self.assertEqual(unavailable.error, "not a regular file")

    def test_input_drift_withholds_comparison_key(self) -> None:
        receipt = completed_receipt(snapshot=complete_snapshot())
        self.assertIsNotNone(receipt["comparable_key"])
        targets, source, candidates = attempt_inputs()
        changed = receipts.make_receipt(
            targets=targets,
            source=source,
            candidates=candidates,
            before=complete_snapshot(),
            after=complete_snapshot(dependency=SHA_C),
            started_at="2026-09-11T00:00:00+00:00",
            finished_at="2026-09-11T00:00:01+00:00",
            wall_seconds=1.0,
            returncode=0,
            diagnostics="",
            failure_class="success",
            rerun_reason="dependency rebuild",
        )
        self.assertIsNone(changed["comparable_key"])
        self.assertIn(
            "comparison inputs changed during the attempt",
            changed["non_comparable_reasons"],
        )


class ClassificationTests(unittest.TestCase):
    def test_failure_classes_are_explicit(self) -> None:
        cases = (
            (0, "", "success"),
            (
                1,
                "maximum number of heartbeats exceeded",
                "deterministic_heartbeat_timeout",
            ),
            (None, "", "wall_clock_timeout"),
            (1, "connection reset", "explicit_transient_failure"),
            (1, "stale private backend", "stale_or_missing_dependency"),
            (1, "X.lean:1:1: error: type mismatch", "compiler_diagnostic"),
        )
        for returncode, diagnostic, expected in cases:
            with self.subTest(expected=expected):
                self.assertEqual(
                    receipts.classify_result(returncode, diagnostic), expected
                )


class ReceiptOutputTests(unittest.TestCase):
    def test_receipts_are_append_only_and_duplicate_measurement_is_reproducible(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            receipt = completed_receipt()
            first = receipts.write_receipt(root, receipt)
            original = first.read_bytes()
            second = receipts.write_receipt(root, receipt)
            changed = receipts.write_receipt(
                root, completed_receipt(candidate="by trivial")
            )
            malformed = copy.deepcopy(receipt)
            malformed.pop("build_after")
            receipts.write_receipt(root, malformed)

            incomplete_snapshot = complete_snapshot()
            incomplete_snapshot = receipts.BuildSnapshot(
                **{
                    **incomplete_snapshot.__dict__,
                    "problems": ("actual Lean compiler path is unavailable",),
                }
            )
            receipts.write_receipt(
                root, completed_receipt(snapshot=incomplete_snapshot)
            )

            self.assertNotEqual(first, second)
            self.assertEqual(first.read_bytes(), original)
            self.assertEqual(first.stat().st_mode & 0o222, 0)
            self.assertTrue(changed.is_file())
            report = receipts.measure_receipts(root)
            self.assertEqual(report["receipt_files"], 5)
            self.assertEqual(report["comparable_receipts"], 3)
            self.assertEqual(report["non_comparable_receipts"], 1)
            self.assertEqual(len(report["invalid_receipts"]), 1)
            self.assertEqual(report["duplicate_attempts_beyond_first"], 1)
            self.assertEqual(report["duplicate_failed_attempts_beyond_first"], 1)


class BuildSnapshotTests(unittest.TestCase):
    def test_package_without_compiled_library_is_incomplete(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            package = repo / "dependency"
            package.mkdir()
            (package / "lakefile.toml").write_text('name = "dependency"\n')
            (repo / "lake-manifest.json").write_text(
                '{"version":"1.1.0","packagesDir":".lake/packages","packages":['
                '{"type":"path","name":"dependency","dir":"dependency",'
                '"configFile":"lakefile.toml"}]}\n'
            )
            inventories, problems = receipts._package_artifacts(repo)
            self.assertEqual(len(inventories), 1)
            self.assertIn(
                "Lake package dependency has no compiled library artifacts", problems
            )

    def test_snapshot_records_complete_transitive_dependency_build(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            repo, backend = root / "repo", root / "backend"
            (repo / "Vsa").mkdir(parents=True)
            backend.mkdir()
            (repo / "Vsa/A.lean").write_text("def a := 1\n")
            (repo / "Vsa/B.lean").write_text("import Vsa.A\ndef b := a\n")
            (repo / "Vsa.lean").write_text("import Vsa.B\n")
            (repo / "VsaRun.lean").write_text("import Vsa\n")
            (repo / "lean-toolchain").write_text("leanprover/lean4:v4.19.0\n")
            (repo / "lakefile.toml").write_text('name = "test"\n')
            (repo / "lake-manifest.json").write_text(
                '{"version":"1.1.0","packagesDir":".lake/packages","packages":[]}\n'
            )
            shim = root / ".elan/bin/elan"
            shim.parent.mkdir(parents=True)
            shim.write_bytes(b"shim")
            toolchain = root / "toolchain"
            actual_lean = toolchain / "bin/lean"
            actual_lake = toolchain / "bin/lake"
            actual_lean.parent.mkdir(parents=True)
            actual_lean.write_bytes(b"lean")
            actual_lake.write_bytes(b"lake")
            library = toolchain / "lib/lean"
            library.mkdir(parents=True)
            (library / "Init.olean").write_bytes(b"init")

            modules = build_private.discover_modules(repo, include_executable=True)
            order = build_private.topological_order(modules)
            expected = build_private.module_fingerprints(
                repo, order, build_private.input_context(repo)
            )
            build_private.write_manifest(
                backend / build_private.MANIFEST_NAME, expected
            )
            for name in ("Vsa.A", "Vsa.B"):
                path = build_private.output_path(backend, modules[name])
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(name.encode())

            def executable_path(command: str) -> str | None:
                return str(shim)

            def elan_which(command: list[str], **_kwargs: object):
                selected = actual_lean if command[-1] == "lean" else actual_lake
                return receipts.subprocess.CompletedProcess(
                    command, 0, f"{selected}\n", ""
                )

            with (
                patch.object(receipts.shutil, "which", side_effect=executable_path),
                patch.object(receipts.subprocess, "run", side_effect=elan_which),
            ):
                snapshot = receipts.capture_build_snapshot(
                    repo, backend, "import Vsa.B\n\n#check b\n", ""
                )
            self.assertEqual(
                [item.module for item in snapshot.dependencies], ["Vsa.A", "Vsa.B"]
            )
            self.assertTrue(all(item.current for item in snapshot.dependencies))
            self.assertEqual(snapshot.problems, ())

            failed_resolution = receipts.subprocess.CompletedProcess(
                ["elan", "which", "lean"], 1, "", "unknown toolchain"
            )
            with (
                patch.object(receipts.shutil, "which", side_effect=executable_path),
                patch.object(
                    receipts.subprocess, "run", return_value=failed_resolution
                ),
            ):
                shim_snapshot = receipts.capture_build_snapshot(
                    repo, backend, "import Vsa.B\n\n#check b\n", ""
                )
            self.assertTrue(
                any(
                    problem.startswith("elan which lean returned")
                    for problem in shim_snapshot.problems
                )
            )

            (repo / "Vsa/A.lean").write_text("import External.Package\ndef a := 1\n")
            modules = build_private.discover_modules(repo, include_executable=True)
            order = build_private.topological_order(modules)
            expected = build_private.module_fingerprints(
                repo, order, build_private.input_context(repo)
            )
            build_private.write_manifest(
                backend / build_private.MANIFEST_NAME, expected
            )
            with (
                patch.object(receipts.shutil, "which", side_effect=executable_path),
                patch.object(receipts.subprocess, "run", side_effect=elan_which),
            ):
                external = receipts.capture_build_snapshot(
                    repo, backend, "import Vsa.B\n\n#check b\n", ""
                )
            self.assertEqual(external.external_imports, ("External.Package",))
            self.assertEqual(external.problems, ())
            targets, source, candidates = attempt_inputs()
            self.assertIsNotNone(
                receipts.comparison_payload(targets, source, candidates, external)
            )


if __name__ == "__main__":
    unittest.main()
