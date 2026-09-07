"""Internal status registers must not inherit an entry return-buffer premise."""

import contextlib
import csv
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import warnings

from scripts import difftest, houdini_summary as houdini


SRET_PRE = """; `EvalEntry.sret_ram` / `sret_align`
(assert (bvule #x0000000080000000 (select (rr s0) #x000000000000000a)))
(assert (= (bvand (select (rr s0) #x000000000000000a) #x0000000000000007) #x0000000000000000))
"""
BASE_PRE = "(assert true)\n"
QUERIES = ("hInt", "hSWhileRetBodyReturn", "hSWhileLoopBodyReturn")


class HoudiniQueryPreconditionTests(unittest.TestCase):
    def setUp(self) -> None:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        (self.root / "pre.smt2").write_text(BASE_PRE + SRET_PRE)

    def test_concrete_statuses_satisfy_internal_pre_but_not_entry_sret_pre(
        self,
    ) -> None:
        entry, _ = difftest._premise_fixture("hCallAssertOk")
        for name, status in ((QUERIES[1], 3), (QUERIES[2], 0), (QUERIES[2], 2)):
            with self.subTest(query=name, status=status):
                state = difftest._with_reg_value(entry, 10, status)
                evaluator = difftest.Ev(
                    difftest.Query("(define-fun state_exit () MState s0)"),
                    state,
                    lambda *_: None,
                )

                def satisfies(pre: str) -> bool:
                    assertions = "\n".join(
                        line for line in pre.splitlines() if not line.startswith(";")
                    )
                    return all(
                        evaluator.ev(form[1]) for form in difftest.parse_all(assertions)
                    )

                self.assertFalse(satisfies(houdini.pre_block(self.root)))
                self.assertTrue(
                    satisfies(houdini.projection_pre_block(self.root, name))
                )
        pointer_state = difftest._with_reg_value(entry, 10, 0x90000000)
        evaluator = difftest.Ev(
            difftest.Query("(define-fun state_exit () MState s0)"),
            pointer_state,
            lambda *_: None,
        )
        entry_pre = houdini.projection_pre_block(self.root, "hInt")
        self.assertEqual(entry_pre, BASE_PRE + SRET_PRE)
        assertions = "\n".join(
            line for line in entry_pre.splitlines() if not line.startswith(";")
        )
        self.assertTrue(
            all(evaluator.ev(form[1]) for form in difftest.parse_all(assertions))
        )

    def test_every_residual_route_uses_the_same_query_precondition(self) -> None:
        (self.root / "clauses.json").write_text("{}\n")
        (self.root / "source-provenance.tsv").write_text("test fixture\n")
        (self.root / "queries").mkdir()
        (self.root / "summaries.tsv").write_text("summary\n")
        (self.root / "query-summaries.tsv").write_text(
            "query\tsummaries\n" + "".join(f"{name}\t\n" for name in QUERIES)
        )
        (self.root / "query-capabilities.tsv").write_text(
            "query\tfield\tinstance\tcapability\n"
            + "".join(
                f"{name}\t{name}\tsingle\tpartial-projection\n" for name in QUERIES
            )
        )
        (self.root / "residual-holes.tsv").write_text("field\tdimension\n")
        (self.root / "spans.tsv").write_text(
            "field\tcomplete\tentry\tregion_lo\n"
            + "".join(f"{name}\ttrue\t0x1\t0x1\n" for name in QUERIES)
        )
        for name in QUERIES:
            (self.root / "queries" / f"{name}.smt2").write_text(
                f"; query={name}\n; @@ASSUME@@\n; @@POST@@\n"
            )

        def query_name(text: str) -> str:
            return text.splitlines()[0].removeprefix("; query=")

        def expected_pre(name: str) -> str:
            return BASE_PRE + SRET_PRE if name == "hInt" else BASE_PRE

        def solver(text: str, _timeout: int) -> str:
            name = query_name(text)
            self.assertEqual(SRET_PRE in text, name == "hInt")
            self.assertIn(BASE_PRE, text)
            return "unsat" if "(assert false)" in text else "sat"

        def projection(text, _post, _clauses, pre, *_args):
            self.assertEqual(pre, expected_pre(query_name(text)))
            return "VALID"

        def iv(text, _clauses, _timeout, pre, _writes):
            self.assertEqual(pre, expected_pre(query_name(text)))
            return None

        def footprint(text, *_args, pre):
            self.assertEqual(pre, expected_pre(query_name(text)))
            return "VALID"

        declarations = {(name, "abi_frame_x1"): "Metadata.only" for name in QUERIES}
        for only_declarations in (False, True):
            argv = ["houdini", str(self.root), "--phase", "check", "-j1"]
            if only_declarations:
                argv += ["--only-post", "abi_frame_x1"]
            with contextlib.ExitStack() as stack:
                stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
                stack.enter_context(warnings.catch_warnings())
                warnings.simplefilter("ignore", ResourceWarning)
                replacements = {
                    "check_provenance": lambda *_: None,
                    "check_campaign_manifest": lambda *_: None,
                    "prepare_clause_set": lambda *_args, **_kwargs: {},
                    "load_query_effects": lambda *_: {},
                    "load_lean_certificates": lambda *_: declarations,
                    "residual_posts": lambda *_: dict.fromkeys(
                        QUERIES, "(assert false)"
                    ),
                    "residual_pres": lambda *_: {},
                    "residual_suffixes": lambda *_: {},
                    "assume_block": lambda *_args, **_kwargs: "",
                    "z3": solver,
                    "iv_discharge": iv,
                    "footprint_check": footprint,
                    "check_projection_cases": projection,
                    "POSTS": {"sp": "(assert false)"},
                    "FOOTPRINT_POSTS": {"outside_stack_arena": ""},
                }
                for name, replacement in replacements.items():
                    stack.enter_context(patch.object(houdini, name, replacement))
                stack.enter_context(patch.object(houdini.sys, "argv", argv))
                houdini.main()
            output = houdini.verdict_output_path(
                str(self.root), None, {"abi_frame_x1"} if only_declarations else None
            )
            with open(output) as stream:
                rows = list(csv.DictReader(stream, delimiter="\t"))
            self.assertEqual(len(rows), len(QUERIES))
            for row in rows:
                self.assertEqual(row["full_contract_status"], "NOT-CHECKED")
                self.assertEqual(
                    row["abi_frame_x1"], "UNKNOWN(untyped-lean-certificate)"
                )
                if not only_declarations:
                    self.assertEqual(row["sp"], "VALID-MACHINE")
                    self.assertEqual(row["outside_stack_arena"], "VALID-MACHINE")
                    self.assertTrue(row["residual_relation"].startswith("VALID"))


if __name__ == "__main__":
    unittest.main()
