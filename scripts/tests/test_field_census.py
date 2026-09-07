"""Fault-injection tests for compiled supplier-census evidence."""

import json
import signal
import subprocess
import tempfile
import unittest
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from unittest.mock import MagicMock, patch

from scripts import field_census as census


def record(marker: str, **data) -> str:
    return marker + " " + json.dumps(data) + "\n"


FIELD = census.Field("inherited", "Parent.inherited")
INVENTORY = record("VSA_CENSUS_FIELD", field=FIELD.name, projection=FIELD.projection)
FOUND = record("VSA_CENSUS_RESULT", field=FIELD.name, status="FOUND", axioms=[])


class FieldCensusTests(unittest.TestCase):
    def test_found_requires_success_object_and_exact_checked_record(self) -> None:
        cases = [
            (0, FOUND, True, "FOUND"),
            (0, "warning: unused variable\n" + FOUND, True, "FOUND"),
            (1, FOUND, True, "INVALID_EVIDENCE"),
            (0, FOUND, False, "INVALID_EVIDENCE"),
            (0, FOUND + FOUND, True, "INVALID_EVIDENCE"),
            (0, FOUND.replace('"inherited"', '"other"'), True, "INVALID_EVIDENCE"),
            (
                0,
                FOUND.replace('"axioms": []', '"axioms": ["untrusted"]'),
                True,
                "INVALID_EVIDENCE",
            ),
            (
                0,
                FOUND.replace('"axioms": []', '"axioms": "propext"'),
                True,
                "INVALID_EVIDENCE",
            ),
            (0, "Try this: exact existing_supplier\n", True, "INVALID_EVIDENCE"),
            (0, "VSA_CENSUS_RESULT {broken\n", True, "INVALID_EVIDENCE"),
            (0, FOUND + "Probe.lean:1:0: error: failed\n", True, "INVALID_EVIDENCE"),
            (None, FOUND, True, "TIMEOUT"),
        ]
        for code, text, exists, expected in cases:
            with self.subTest(code=code, text=text, exists=exists):
                result = census.classify(FIELD, census.LeanResult(code, text), exists)
                self.assertEqual(result.verdict, expected)

    def test_incomplete_proof_warnings_invalidate_probe_and_inventory(self) -> None:
        for warning in (
            "warning: declaration uses `sorry`\n",
            "warning: declaration uses 'sorry'\n",
            "warning: declaration uses `admit`\n",
            "depends on axioms: [sorryAx]\n",
        ):
            with self.subTest(warning=warning):
                result = census.classify(
                    FIELD, census.LeanResult(0, warning + FOUND), True
                )
                self.assertEqual(result.verdict, "INVALID_EVIDENCE")
                with self.assertRaises(ValueError):
                    census.extract_fields(
                        census.LeanResult(0, warning + INVENTORY), True
                    )

    def test_search_miss_requires_only_expected_search_errors(self) -> None:
        miss = "Probe.lean:1:0: error: `exact?` could not close the goal. Try `apply?` to see partial suggestions.\n⊢ False\n"
        for code, text, expected in (
            (1, miss, "NO_MATCH"),
            (0, miss, "INVALID_EVIDENCE"),
            (-9, miss, "INVALID_EVIDENCE"),
            (
                1,
                miss + "Probe.lean:2:0: error: unknown identifier\n",
                "INVALID_EVIDENCE",
            ),
            (1, miss + FOUND, "INVALID_EVIDENCE"),
            (
                1,
                "Probe.lean:1:0: error: maximum recursion depth reached\n",
                "INVALID_EVIDENCE",
            ),
        ):
            with self.subTest(code=code, text=text):
                self.assertEqual(
                    census.classify(
                        FIELD, census.LeanResult(code, text), False
                    ).verdict,
                    expected,
                )

    def test_inventory_rejects_incomplete_or_malformed_evidence(self) -> None:
        for code, text, exists in (
            (1, INVENTORY, True),
            (0, INVENTORY, False),
            (0, "", True),
            (0, INVENTORY + INVENTORY, True),
            (0, "VSA_CENSUS_FIELD {}\n", True),
            (0, "VSA_CENSUS_FIELD []\n", True),
            (0, "VSA_CENSUS_FIELD {broken\n", True),
            (0, INVENTORY.replace('"inherited"', "42"), True),
            (0, INVENTORY.replace('"inherited"', '"bad-field"'), True),
            (0, INVENTORY.replace('"Parent.inherited"', '"bad projection"'), True),
            (0, INVENTORY + "Inventory.lean:1:0: error: failed\n", True),
        ):
            with self.subTest(code=code, text=text, exists=exists):
                with self.assertRaises(ValueError):
                    census.extract_fields(census.LeanResult(code, text), exists)
        self.assertEqual(
            census.extract_fields(census.LeanResult(0, INVENTORY), True), [FIELD]
        )

    def test_timeout_kills_group_and_drains_output_even_if_group_already_exited(
        self,
    ) -> None:
        for race in (False, True):
            with self.subTest(race=race), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                source = root / "Probe.lean"
                source.write_text("synthetic input")
                source.with_suffix(".olean").write_bytes(b"stale synthetic object")
                process = MagicMock()
                process.__enter__.return_value = process
                process.pid = 1234
                process.communicate.side_effect = [
                    subprocess.TimeoutExpired("mock", 240),
                    ("partial output", None),
                ]
                with (
                    patch.object(
                        census.subprocess, "Popen", return_value=process
                    ) as spawn,
                    patch.object(
                        census.os,
                        "killpg",
                        side_effect=ProcessLookupError() if race else None,
                    ) as kill,
                ):
                    result = census.run_lean(root, root / "backend", source)
                self.assertIsNone(result.returncode)
                self.assertEqual(result.output, "partial output")
                kill.assert_called_once_with(1234, signal.SIGKILL)
                self.assertEqual(process.communicate.call_count, 2)
                self.assertTrue(spawn.call_args.kwargs["start_new_session"])
                self.assertFalse(source.with_suffix(".olean").exists())
                self.assertEqual(
                    source.with_suffix(".log").read_text(), "partial output"
                )

    def test_cancellation_kills_group_and_reraises(self) -> None:
        for cancellation in (KeyboardInterrupt(), SystemExit(130)):
            with (
                self.subTest(cancellation=type(cancellation).__name__),
                tempfile.TemporaryDirectory() as directory,
            ):
                root = Path(directory)
                source = root / "Probe.lean"
                source.write_text("synthetic input")
                process = MagicMock()
                process.__enter__.return_value = process
                process.pid = 1234
                process.communicate.side_effect = [
                    cancellation,
                    ("cancelled output", None),
                ]
                with (
                    patch.object(census.subprocess, "Popen", return_value=process),
                    patch.object(census.os, "killpg") as kill,
                    self.assertRaises(type(cancellation)),
                ):
                    census.run_lean(root, root / "backend", source)
                kill.assert_called_once_with(1234, signal.SIGKILL)
                self.assertEqual(process.communicate.call_count, 2)
                self.assertEqual(
                    source.with_suffix(".log").read_text(), "cancelled output"
                )

    def test_inventory_only_imports_full_library_and_reports_unprobed_fields(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            repo = root / "repo"
            repo.mkdir()
            backend = root / "backend"
            backend.mkdir()
            (backend / census.build_private.MANIFEST_NAME).write_text("{}\n")
            support = root / "FieldCensus.lean"
            support.write_text("import Lean\n")
            modules = {name: None for name in ("Vsa", "Vsa.OutsideAggregate")}

            def run(_repo, _backend, source):
                content = source.read_text()
                self.assertIn("import Vsa.OutsideAggregate\n", content)
                source.with_suffix(".olean").write_bytes(b"synthetic inventory object")
                source.with_suffix(".log").write_text(INVENTORY)
                return census.LeanResult(0, INVENTORY)

            with (
                patch.object(census, "ROOT", repo),
                patch.object(census, "SUPPORT", support),
                patch.object(census.check_validation, "verify_backend") as verify,
                patch.object(
                    census.build_private, "discover_modules", return_value=modules
                ),
                patch.object(census, "run_lean", side_effect=run) as compiler,
                redirect_stdout(StringIO()),
            ):
                status = census.main(
                    [
                        "--backend",
                        str(backend),
                        "--output",
                        str(root / "reports"),
                        "--inventory-only",
                    ]
                )
            self.assertEqual(status, 0)
            self.assertEqual(verify.call_count, 2)
            self.assertEqual(compiler.call_count, 1)
            (report_path,) = (root / "reports").glob("run-*/report.json")
            report = json.loads(report_path.read_text())
            self.assertEqual(
                report["inventory"],
                [{"name": FIELD.name, "projection": FIELD.projection}],
            )
            self.assertEqual(report["results"], [])
            self.assertEqual(report["module_count"], 2)
            self.assertIn("Inventory.lean", report["artifacts_sha256"])
            self.assertIn("Inventory.olean", report["artifacts_sha256"])
            tsv = report_path.with_name("fields.tsv").read_text()
            self.assertIn("inherited\tParent.inherited\tINVENTORIED\tnot probed", tsv)

    def test_stale_backend_rejected_before_any_compiler_runs(self) -> None:
        with (
            patch.object(
                census.check_validation,
                "verify_backend",
                side_effect=census.build_private.BuildError("stale backend"),
            ),
            patch.object(census, "run_lean") as compiler,
            redirect_stdout(StringIO()),
        ):
            self.assertEqual(
                census.main(["--backend", "/tmp/backend", "--output", "/tmp/reports"]),
                2,
            )
        compiler.assert_not_called()


if __name__ == "__main__":
    unittest.main()
