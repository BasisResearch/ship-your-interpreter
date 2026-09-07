"""A previous TSV cannot outlive failed validation or changed validation inputs."""

import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import houdini_summary as houdini
from scripts import verdict_receipts as receipts


class VerdictReceiptTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.campaign = self.root / "campaign"
        self.campaign.mkdir()
        self.verdict = self.campaign / "verdicts.tsv"
        (self.campaign / "queries").mkdir()
        for name, value in {
            "pre.smt2": "(assert true)",
            "clauses.json": "{}",
            "source-provenance.tsv": "fixture",
            "query-capabilities.tsv": "fixture",
            "queries/hInt.smt2": "(check-sat)",
        }.items():
            (self.campaign / name).write_text(value)
        self.text = (
            "query\tresidual\tinstance\tcapability\tassumed_dependencies\t"
            "opaque_dependencies\tunencoded_dimensions\tfull_contract_status\tsp\n"
            "hInt\thInt\tsingle\tmachine-only\t\t\t\tNOT-CHECKED\tVALID-MACHINE\n"
        )
        self.source_check = self.enterContext(
            patch.object(receipts, "validate_sources")
        )

    def complete(
        self,
        pins: Path | None = None,
        authority: Path | None = None,
    ) -> receipts.VerdictRun:
        run = receipts.VerdictRun.begin(self.verdict, self.campaign, pins, authority)
        self.verdict.write_text(self.text)
        run.complete({"phase": "check"}, [("hInt", "sp")], run.inputs())
        return run

    def test_completed_receipt_binds_invocation_and_checks(self) -> None:
        self.complete()
        result = receipts.verify_verdict_receipt(self.verdict, self.campaign)
        self.assertEqual(result["status"], "completed")
        self.assertEqual(result["invocation"], {"phase": "check"})
        self.assertEqual(result["checks"], [["hInt", "sp"]])
        self.assertEqual(result["full_contract_status"], "NOT-CHECKED")
        self.source_check.assert_called_once()

    def test_unchanged_old_tsv_has_no_authority_after_failed_invocation(self) -> None:
        self.complete()
        original = self.verdict.read_bytes()
        with (
            patch.object(
                houdini.sys, "argv", ["houdini", str(self.campaign), "--phase", "check"]
            ),
            patch.object(houdini, "check_provenance", side_effect=SystemExit("stale")),
            self.assertRaisesRegex(SystemExit, "stale"),
        ):
            houdini.main()
        self.assertEqual(self.verdict.read_bytes(), original)
        self.assertFalse(receipts.receipt_path(self.verdict).exists())
        with self.assertRaises(ValueError):
            receipts.verify_verdict_receipt(self.verdict, self.campaign)

    def test_changed_or_removed_inputs_reject_receipt(self) -> None:
        for name in (
            "pre.smt2",
            "clauses.json",
            "queries/hInt.smt2",
            "source-provenance.tsv",
            "query-capabilities.tsv",
        ):
            for action in ("change", "remove"):
                with self.subTest(name=name, action=action):
                    target = self.campaign / name
                    original = target.read_bytes()
                    self.complete()
                    if action == "change":
                        target.write_bytes(original + b"changed")
                    else:
                        target.unlink()
                    with self.assertRaisesRegex(ValueError, "input.*mismatch"):
                        receipts.verify_verdict_receipt(self.verdict, self.campaign)
                    target.write_bytes(original)

    def test_new_optional_input_is_not_hidden_by_old_inventory(self) -> None:
        self.complete()
        (self.campaign / "assumed.tsv").write_text("new assumption")
        with self.assertRaisesRegex(ValueError, "input.*mismatch"):
            receipts.verify_verdict_receipt(self.verdict, self.campaign)

    def test_changed_verdict_or_scope_rejects_receipt(self) -> None:
        self.complete()
        self.verdict.write_text(self.text.replace("VALID-MACHINE", "UNKNOWN"))
        with self.assertRaisesRegex(ValueError, "completed validation"):
            receipts.verify_verdict_receipt(self.verdict, self.campaign)
        self.complete()
        path = receipts.receipt_path(self.verdict)
        data = json.loads(path.read_text())
        data["checks"] = [["hInt", "invented"]]
        path.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "scope"):
            receipts.verify_verdict_receipt(self.verdict, self.campaign)

    def test_inputs_changing_during_validation_never_get_receipt(self) -> None:
        for name, after_mining in (("pre.smt2", False), ("clauses.json", True)):
            with self.subTest(name=name):
                run = receipts.VerdictRun.begin(self.verdict, self.campaign)
                checked = run.inputs()
                target = self.campaign / name
                target.write_text("changed")
                if not after_mining:
                    checked = run.inputs()
                self.verdict.write_text(self.text)
                with self.assertRaisesRegex(ValueError, "changed during"):
                    run.complete({"phase": "both"}, [("hInt", "sp")], checked)
                self.assertFalse(receipts.receipt_path(self.verdict).exists())

    def test_mining_may_change_clauses_before_checks(self) -> None:
        run = receipts.VerdictRun.begin(self.verdict, self.campaign)
        (self.campaign / "clauses.json").write_text('{"callee_1": []}')
        checked = run.inputs()
        self.verdict.write_text(self.text)
        run.complete({"phase": "both"}, [("hInt", "sp")], checked)
        receipts.verify_verdict_receipt(self.verdict, self.campaign)

    def test_external_pins_and_authority_are_bound(self) -> None:
        pins, authority = self.root / "pins", self.root / "authority"
        pins.mkdir()
        authority.mkdir()
        pin = pins / "hInt.smt2"
        pin.write_text("pin")
        contract = authority / "segment-authority.json"
        contract.write_text("contract")
        (authority / "source-provenance.tsv").write_text("source")
        for changed in (pin, contract):
            self.complete(pins, authority)
            receipts.verify_verdict_receipt(self.verdict, self.campaign)
            changed.write_text(changed.read_text() + " changed")
            with self.assertRaisesRegex(ValueError, "input.*mismatch"):
                receipts.verify_verdict_receipt(self.verdict, self.campaign)

    def test_current_source_changes_reject_unchanged_manifest(self) -> None:
        self.complete()
        self.source_check.side_effect = ValueError("current source mismatch")
        with self.assertRaisesRegex(ValueError, "current source mismatch"):
            receipts.verify_verdict_receipt(self.verdict, self.campaign)

    def test_receipt_never_claims_all_checks_valid(self) -> None:
        self.text = self.text.replace("VALID-MACHINE", "UNKNOWN")
        self.complete()
        result = receipts.verify_verdict_receipt(self.verdict, self.campaign)
        self.assertEqual(result["full_contract_status"], "NOT-CHECKED")

    def test_malformed_or_incomplete_receipt_is_rejected(self) -> None:
        for key, value in (
            ("status", "started"),
            ("checks", []),
            ("invocation", {"phase": "mine"}),
            ("inputs", []),
            ("campaign_root", "/elsewhere"),
            ("segment_authority_root", []),
        ):
            with self.subTest(key=key):
                self.complete()
                path = receipts.receipt_path(self.verdict)
                data = json.loads(path.read_text())
                data[key] = value
                path.write_text(json.dumps(data))
                with self.assertRaises(ValueError):
                    receipts.verify_verdict_receipt(self.verdict, self.campaign)


if __name__ == "__main__":
    unittest.main()
