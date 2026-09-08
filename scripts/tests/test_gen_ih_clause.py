"""Tests for the induction-hypothesis clause generator."""

from pathlib import Path
import contextlib
import io
import tempfile
import unittest

import scripts.gen_ih_clause as generator


HEADER = "name\tpred\timports\tmotives\tsteps\tnotes\n"
HEADER_KIND = "name\tkind\tpred\timports\tmotives\tsteps\tnotes\n"


def write_tsv(directory: Path, body: str, header: str = HEADER) -> Path:
    tsv = directory / "clauses.tsv"
    tsv.write_text("# comment\n" + header + body)
    return tsv


class SchemaTests(unittest.TestCase):
    def test_tracked_table_parses(self) -> None:
        clauses = generator.load_clauses()
        names = [clause.name for clause in clauses]
        self.assertIn("Trivial", names)
        self.assertIn("Footprint", names)
        trivial = next(c for c in clauses if c.name == "Trivial")
        self.assertEqual(trivial.kind, "extra")
        self.assertEqual(generator.parse_tag(trivial.tag("hBinary")),
                         ("from_old", "trivialStep_of_old"))
        footprint = next(c for c in clauses if c.name == "Footprint")
        self.assertEqual((footprint.kind, footprint.pred), ("extraM", "footExtra noArenaFoot"))

    def test_kind_column_is_optional_and_validated(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (clause,) = generator.load_clauses(write_tsv(root, "Demo\tp\t-\t-\t-\t\n"))
            self.assertEqual(clause.kind, "extra")
            (clause,) = generator.load_clauses(
                write_tsv(root, "Demo\textraM\tp\t-\t-\t-\t\n", HEADER_KIND))
            self.assertEqual(clause.kind, "extraM")
            with self.assertRaisesRegex(ValueError, "kind must be one of"):
                generator.load_clauses(write_tsv(root, "Demo\tbogus\tp\t-\t-\t-\t\n", HEADER_KIND))
            with self.assertRaisesRegex(ValueError, "header row"):
                generator.load_clauses(write_tsv(root, "Demo\tp\t-\t-\t-\t\n", ""))
            with self.assertRaisesRegex(ValueError, "bad header columns"):
                generator.load_clauses(write_tsv(root, "Demo\tp\n", "name\tpred\tzzz\n"))

    def test_row_fields_and_defaults(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            tsv = write_tsv(Path(directory),
                            "Demo\tfun _ _ _ _ _ _ _ => True\tVsa.Sim.X, Vsa.Sim.Y\t"
                            "ExecS=True\thBinary=generic:footprint;*=manual\tnote\n")
            (clause,) = generator.load_clauses(tsv)
        self.assertEqual(clause.imports, ["Vsa.Sim.X", "Vsa.Sim.Y"])
        self.assertEqual(clause.motive_body("ExecS"), "True")
        self.assertIsNone(clause.motive_body("Call"))
        self.assertEqual(clause.tag("hBinary"), "generic:footprint")
        self.assertEqual(clause.tag("hInt"), "manual")

    def test_invalid_rows_are_rejected(self) -> None:
        cases = {
            "lowercase\tp\t-\t-\t-\t\n": "CamelCase",
            "Dup\tp\t-\t-\t-\t\nDup\tp\t-\t-\t-\t\n": "duplicate clause names",
            "Bad\tp\t-\tNope=True\t-\t\n": "motives key",
            "Bad\tp\t-\t-\t*=bogus:x\t\n": "unknown step tag kind",
            "Bad\tp\t-\t-\t*=generic\t\n": "needs a payload",
            "Bad\tp\t-\t-\t*=manual:x\t\n": "manual takes no payload",
            "Bad\tp\t-\t-\thInt=manual;hInt=manual\t\n": "duplicate key",
            "Short\tp\t-\n": "expected 6 columns",
        }
        for body, message in cases.items():
            with self.subTest(body=body), tempfile.TemporaryDirectory() as directory:
                tsv = write_tsv(Path(directory), body)
                with self.assertRaisesRegex(ValueError, message):
                    generator.load_clauses(tsv)


class CaseStructureTests(unittest.TestCase):
    def test_cases_come_from_the_assembly_signature(self) -> None:
        cases, signatures = generator.load_cases()
        self.assertEqual(len(cases), 50)
        self.assertEqual(sorted(signatures), sorted(generator.RELATIONS))
        by_name = {case.name: case for case in cases}
        binary = by_name["hBinary"]
        self.assertEqual([c.relation for c in binary.children], ["EvalE", "EvalE"])
        self.assertEqual(binary.conclusion.relation, "EvalE")
        self.assertEqual(binary.constructor, "EvalE.binary")
        call = by_name["hCall"]
        self.assertEqual([c.relation for c in call.children], ["EvalE", "EvalArgs", "Call"])
        self.assertEqual(by_name["hSeqNil"].children, [])
        self.assertEqual(by_name["hSeqNil"].conclusion.relation, "ExecSeq")
        self.assertEqual(signatures["EvalE"][-1][0], ["_h"])

    def test_field_type_orders_hypotheses(self) -> None:
        cases, _ = generator.load_cases()
        binary = next(case for case in cases if case.name == "hBinary")
        lines = generator.field_type(binary).splitlines()
        self.assertTrue(lines[0].startswith("∀ (st : SpecSt)"))
        heads = [line.strip().split(" ")[0] for line in lines[1:]]
        self.assertEqual(heads, [
            "Vsa.Sim.TermSimAssembly.mEvalE", "Vsa.Sim.TermSimAssembly.mEvalE",
            "Vsa.Sim.TermSimAssembly.mEvalE", "mEvalE", "mEvalE", "mEvalE"])


class EmissionTests(unittest.TestCase):
    def test_tracked_outputs_match_generator(self) -> None:
        for name, text in generator.render_all().items():
            target = generator.OUTPUT_DIR / f"IHClause_{name}.lean"
            self.assertEqual(target.read_text(), text, name)

    def test_emission_is_deterministic(self) -> None:
        self.assertEqual(generator.render_all(), generator.render_all())

    def test_unwired_fields_and_hooks(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            tsv = write_tsv(Path(directory),
                            "Demo\tfun _ _ _ _ _ _ _ => True\t-\t-\t"
                            "hBinary=generic:fp;hInt=exact:someLemma;*=manual\t\n")
            text = generator.render_all(tsv)["Demo"]
        self.assertIn("namespace Vsa.Sim.IHClause.Demo", text)
        self.assertIn("import Vsa.Sim.ExitFootprint\n", text)
        self.assertIn("def extra : EvalExtra := fun _ _ _ _ _ _ _ => True", text)
        self.assertIn("def extraM : EvalExtraM := fun N A SL φf φc _ sret _ => extra", text)
        self.assertIn("theorem ofWith", text)
        self.assertIn("  EvalIHWithM extraM st d env e st' v\n", text)
        self.assertIn("structure Residuals (_L : Layout) : Prop where", text)
        self.assertIn("-- IHCLAUSE-HOOK Demo hBinary generic:fp", text)
        self.assertIn("theorem Residuals.ofUnwired (L : Layout)\n    (hStr :", text)
        self.assertIn("  hInt :=\n    someLemma", text)
        self.assertNotIn("theorem closed", text)
        self.assertNotIn("  hSExpr :", text)  # ExecS motive is True: no field

    def test_relation_override_adds_fields(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            tsv = write_tsv(Path(directory),
                            "Demo\tfun _ _ _ _ _ _ _ => True\t-\tExecS=st' = st'\t"
                            "hSExpr=manual\t\n")
            text = generator.render_all(tsv)["Demo"]
        self.assertIn("def mExecS (st : SpecSt)", text)
        self.assertIn("  st' = st'\n", text)
        self.assertIn("  hSExpr :", text)
        self.assertIn("  hSBrk :", text)

    def test_extraM_clause_has_no_embedding(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            tsv = write_tsv(Path(directory), "Demo\textraM\tfootExtra noArenaFoot\t-\t-\t*=manual\t\n",
                            HEADER_KIND)
            text = generator.render_all(tsv)["Demo"]
        self.assertIn("def extraM : EvalExtraM := footExtra noArenaFoot", text)
        self.assertNotIn("def extra :", text)
        self.assertNotIn("theorem ofWith", text)
        self.assertIn("  EvalIHWithM extraM st d env e st' v\n", text)

    def test_step_for_trivial_parent_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            tsv = write_tsv(Path(directory),
                            "Demo\tfun _ _ _ _ _ _ _ => True\t-\t-\thSExpr=manual\t\n")
            with self.assertRaisesRegex(ValueError, "non-True parent motive"):
                generator.render_all(tsv)


class CheckModeTests(unittest.TestCase):
    def test_check_detects_drift(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tsv = write_tsv(root, "Demo\tfun _ _ _ _ _ _ _ => True\t-\t-\t*=manual\t\n")
            out = root / "rows"
            base = ["--tsv", str(tsv), "--output-dir", str(out)]
            with contextlib.redirect_stdout(io.StringIO()), \
                    contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(generator.main(base), 0)
                self.assertEqual(generator.main(base + ["--check"]), 0)
                target = out / "IHClause_Demo.lean"
                target.write_text(target.read_text() + "-- drift\n")
                errors = io.StringIO()
                with contextlib.redirect_stderr(errors):
                    self.assertEqual(generator.main(base + ["--check"]), 1)
                self.assertIn("IHClause_Demo.lean is stale", errors.getvalue())
                self.assertIn("-- drift", errors.getvalue())
                target.unlink()
                self.assertEqual(generator.main(base + ["--check"]), 1)
                self.assertEqual(generator.main(base + ["--clause", "Nope"]), 2)

    def test_stdout_writes_nothing(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tsv = write_tsv(root, "Demo\tfun _ _ _ _ _ _ _ => True\t-\t-\t*=manual\t\n")
            out = root / "rows"
            captured = io.StringIO()
            with contextlib.redirect_stdout(captured):
                code = generator.main(["--tsv", str(tsv), "--output-dir", str(out), "--stdout"])
            self.assertEqual(code, 0)
            self.assertIn("namespace Vsa.Sim.IHClause.Demo", captured.getvalue())
            self.assertFalse(out.exists())


if __name__ == "__main__":
    unittest.main()
