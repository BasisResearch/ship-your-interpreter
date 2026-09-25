"""Reject incomplete progress descriptions before a compiler can be launched."""

import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import proof_checkpoint as checkpoint
from scripts import proof_slice as proof


class CheckpointTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name) / "checkpoint.json"
        self.description = {
            "target_obligation": "remainingWork_closed",
            "target_type": "RemainingWork interpRunLayout",
            "consumer": "Vsa.Sim.remainingWork_closed",
            "role": "target",
            "remaining_premises": [],
        }

    def read(self) -> checkpoint.Checkpoint:
        self.path.write_text(json.dumps(self.description))
        return checkpoint.read_checkpoint(self.path)

    def test_target_check_uses_requested_type_without_new_premises(self) -> None:
        value = self.read()
        self.assertEqual(value.checked_type, "(RemainingWork interpRunLayout)")
        self.assertEqual(value.status, "complete")
        self.assertIn(
            "set_option autoImplicit false in\n"
            "def VsaProofSliceCheckpoint.checkedConsumer : ((RemainingWork interpRunLayout)) :=\n"
            "  Vsa.Sim.remainingWork_closed\n",
            value.source(),
        )

    def test_conditional_type_retains_dependent_premises(self) -> None:
        self.description["remaining_premises"] = [
            {"name": "n", "type": "Nat"},
            {"name": "capacity", "type": "Enough n"},
        ]
        value = self.read()
        self.assertEqual(value.status, "conditional")
        self.assertEqual(
            value.checked_type,
            "(n : (Nat)) → (capacity : (Enough n)) → (RemainingWork interpRunLayout)",
        )

    def test_helper_type_cannot_replace_target_acceptance_type(self) -> None:
        self.description["consumer_type"] = "True"
        with self.assertRaisesRegex(ValueError, "exactly these keys"):
            self.read()
        self.description["role"] = "prerequisite"
        value = self.read()
        self.assertEqual(value.status, "prerequisite")
        self.assertEqual(value.checked_type, "True")

    def test_type_placeholders_and_command_injection_fail_before_checking(self) -> None:
        for type_ in (
            "_",
            "∀ n : _, n = n",
            "?m",
            "(True",
            "True)",
            "True := by trivial",
            "True\n#print axioms other",
            "True /- comment -/",
            "True\u2028axiom bad : False",
            'Output "unterminated',
        ):
            with self.subTest(type=type_):
                with self.assertRaises(ValueError):
                    checkpoint.exact_type(type_)
        self.assertEqual(checkpoint.exact_type('Output "a(b)"'), 'Output "a(b)"')
        self.assertEqual(checkpoint.exact_type('Output "a\\"b"'), 'Output "a\\"b"')

    def test_explicit_type_validation_applies_to_all_type_fields(self) -> None:
        self.description["remaining_premises"] = [{"name": "child", "type": "_"}]
        with self.assertRaises(ValueError):
            self.read()
        self.description["remaining_premises"] = []
        self.description["role"] = "prerequisite"
        self.description["consumer_type"] = "_"
        with self.assertRaises(ValueError):
            self.read()

    def test_rejects_missing_empty_or_mistyped_fields(self) -> None:
        for key in list(self.description):
            for invalid in (None, "", []):
                if key == "remaining_premises" and invalid == []:
                    continue
                with self.subTest(key=key, invalid=invalid):
                    original = self.description[key]
                    self.description[key] = invalid
                    with self.assertRaises(ValueError):
                        self.read()
                    self.description[key] = original
        del self.description["remaining_premises"]
        with self.assertRaises(ValueError):
            self.read()

    def test_rejects_invalid_consumer_and_premise_names(self) -> None:
        for consumer in ("by trivial", "X\n#print axioms other", checkpoint.WITNESS):
            with self.subTest(consumer=consumer):
                self.description["consumer"] = consumer
                with self.assertRaises(ValueError):
                    self.read()
        self.description["consumer"] = "Valid.consumer'"
        for premises in (
            [{"name": "a.b", "type": "True"}],
            [{"name": "a", "type": ""}],
            [{"name": "a", "type": "True"}, {"name": "a", "type": "False"}],
            [{"type": "True"}],
        ):
            with self.subTest(premises=premises):
                self.description["remaining_premises"] = premises
                with self.assertRaises(ValueError):
                    self.read()

    def test_invalid_checkpoint_aborts_before_build_or_output(self) -> None:
        self.path.write_text("{}")
        with patch.object(proof, "execute") as execute:
            result = proof.main(
                [
                    "--backend",
                    str(self.path.parent / "backend"),
                    "--output",
                    str(self.path.parent / "output"),
                    "--module",
                    "Vsa.Sim.LayoutInstance",
                    "--checkpoint",
                    str(self.path),
                ]
            )
            self.assertEqual(result, 2)
            execute.assert_not_called()
        self.assertFalse((self.path.parent / "output").exists())


if __name__ == "__main__":
    unittest.main()
