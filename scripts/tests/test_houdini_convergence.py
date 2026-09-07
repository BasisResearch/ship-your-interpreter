"""Unstable or scoped mining cannot authorize residual checks."""

import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from scripts import houdini_summary as houdini


class HoudiniConvergenceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def prepare(self, phase: str, **options):
        with contextlib.redirect_stdout(io.StringIO()):
            return houdini.prepare_clause_set(
                self.root, ["callee_1", "callee_2"], 1, 1, 3, phase, **options
            )

    def test_nonconverged_mine_or_both_saves_progress_and_fails(self) -> None:
        for phase in ("mine", "both"):
            with (
                self.subTest(phase=phase),
                patch.object(
                    houdini,
                    "mine",
                    return_value=({"callee_1": ["x"], "callee_2": []}, False, {}),
                ),
            ):
                with self.assertRaisesRegex(
                    SystemExit, "No residual checks authorized"
                ):
                    self.prepare(phase)
                self.assertEqual(
                    json.loads((self.root / "clauses.json").read_text()),
                    {"callee_1": ["x"], "callee_2": []},
                )

    def test_check_revalidates_every_summary_even_with_a_forged_receipt(self) -> None:
        (self.root / "clauses.json").write_text('{"callee_1": []}')
        (self.root / "convergence.json").write_text('{"converged": true}')
        for changed_source in (False, True):
            if changed_source:
                (self.root / "obligation.smt2").write_text("changed source")
            with (
                self.subTest(changed_source=changed_source),
                patch.object(
                    houdini,
                    "mine",
                    return_value=({"callee_1": [], "callee_2": []}, True, {}),
                ) as mine,
            ):
                self.prepare("check")
                mine.assert_called_once_with(
                    self.root, ["callee_1", "callee_2"], 1, 1, 3, warm=True
                )

    def test_check_refuses_nonconverged_revalidation(self) -> None:
        (self.root / "clauses.json").write_text("{}")
        with patch.object(
            houdini,
            "mine",
            return_value=({"callee_1": [], "callee_2": ["x"]}, False, {}),
        ):
            with self.assertRaises(SystemExit):
                self.prepare("check")

    def test_scoped_mining_cannot_flow_directly_to_check(self) -> None:
        for phase in ("check", "both"):
            with self.subTest(phase=phase), patch.object(houdini, "mine") as mine:
                with self.assertRaisesRegex(SystemExit, "exploratory"):
                    self.prepare(phase, only_summary={"callee_1"})
                mine.assert_not_called()
        with patch.object(houdini, "mine", return_value=({"callee_1": []}, True, {})):
            self.prepare("mine", only_summary={"callee_1"})
        with patch.object(
            houdini, "mine", return_value=({"callee_1": [], "callee_2": []}, True, {})
        ) as mine:
            self.prepare("check")
            self.assertEqual(mine.call_args.args[1], ["callee_1", "callee_2"])

    def test_dependency_frontier_cannot_skip_final_all_clause_validation(self) -> None:
        # callee_2 initially succeeds, then fails after callee_1 loses its clause.
        # Deliberately omit their edge from summary-deps.tsv.
        (self.root / "obligations").mkdir()
        for name in ("callee_1", "callee_2"):
            (self.root / "obligations" / f"{name}.smt2").write_text(
                f"; {name}\n; complete=true\n; @@ASSUME@@\n; @@GOAL@@\n"
            )
        (self.root / "summary-deps.tsv").write_text(
            "summary\tdeps\ncallee_1\t\ncallee_2\t\n"
        )
        answers = iter(["sat", "unsat", "sat"])
        with (
            patch.object(houdini, "CLAUSE_IDS", ["x"]),
            patch.object(houdini, "NEG", {"x": "goal"}),
            patch.object(houdini, "assume_block", return_value=""),
            patch.object(
                houdini, "z3", side_effect=lambda *_args, **_kwargs: next(answers)
            ) as solver,
            contextlib.redirect_stdout(io.StringIO()),
        ):
            clauses, converged, _ = houdini.mine(
                self.root, ["callee_1", "callee_2"], 1, 1, 3
            )
        self.assertTrue(converged)
        self.assertEqual(clauses, {"callee_1": [], "callee_2": []})
        self.assertEqual(solver.call_count, 3)

    def test_last_round_drop_does_not_claim_convergence(self) -> None:
        (self.root / "obligations").mkdir()
        (self.root / "obligations/callee_1.smt2").write_text(
            "; complete=true\n; @@ASSUME@@\n; @@GOAL@@\n"
        )
        with (
            patch.object(houdini, "CLAUSE_IDS", ["x"]),
            patch.object(houdini, "NEG", {"x": "goal"}),
            patch.object(houdini, "assume_block", return_value=""),
            patch.object(houdini, "z3", return_value="sat"),
            contextlib.redirect_stdout(io.StringIO()),
        ):
            _, converged, _ = houdini.mine(self.root, ["callee_1"], 1, 1, 1)
        self.assertFalse(converged)

    def test_local_stability_still_requires_an_all_clause_round(self) -> None:
        (self.root / "obligations").mkdir()
        summaries = ["callee_1", "callee_2", "callee_3"]
        for name in summaries:
            (self.root / "obligations" / f"{name}.smt2").write_text(
                "; complete=true\n; @@ASSUME@@\n; @@GOAL@@\n"
            )
        (self.root / "summary-deps.tsv").write_text(
            "summary\tdeps\ncallee_1\t\ncallee_2\tcallee_1\ncallee_3\t\n"
        )
        # The recorded dependent stabilizes, but an omitted dependent fails
        # when the mandatory full round checks it against the weaker clauses.
        answers = iter(["sat", "unsat", "unsat", "unsat", "unsat", "sat", "unsat"])
        with (
            patch.object(houdini, "CLAUSE_IDS", ["x"]),
            patch.object(houdini, "NEG", {"x": "goal"}),
            patch.object(houdini, "assume_block", return_value=""),
            patch.object(
                houdini, "z3", side_effect=lambda *_args, **_kwargs: next(answers)
            ) as solver,
            contextlib.redirect_stdout(io.StringIO()),
        ):
            clauses, converged, _ = houdini.mine(self.root, summaries, 1, 1, 4)
        self.assertTrue(converged)
        self.assertEqual(clauses, {"callee_1": [], "callee_2": ["x"], "callee_3": []})
        self.assertEqual(solver.call_count, 7)


if __name__ == "__main__":
    unittest.main()
