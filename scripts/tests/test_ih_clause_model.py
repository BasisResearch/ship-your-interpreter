"""Tests for the shared clause-field model behind the Level-4 automation."""

import io
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

from scripts import gen_ih_clause as generator
from scripts import ih_clause_model as model

HEADER = "name\tpred\timports\tmotives\tsteps\tnotes\n"


def write_tsv(directory: Path, body: str) -> Path:
    tsv = directory / "clauses.tsv"
    tsv.write_text(HEADER + body)
    return tsv


class SourceHelpersTests(unittest.TestCase):
    def test_strip_comments_keeps_lines_and_strings(self) -> None:
        source = 'theorem a\n/- b\n/- c -/ d -/ theorem b -- x\ntheorem c : "-- s" := x\n'
        stripped = model.strip_comments(source)
        self.assertEqual(stripped.count("\n"), source.count("\n"))
        self.assertNotIn("-- x", stripped)
        self.assertIn('"-- s"', stripped)
        self.assertIn("theorem b", stripped)

    def test_support_vocabulary(self) -> None:
        self.assertIn("trueExtra", model.trivial_predicates())
        self.assertEqual(model.from_old_dischargers()[0], "trivialStep_of_old")
        self.assertEqual(model.dischargers_at_motive_shape(), {"trivialStep_of_old"})
        self.assertTrue(model.predicate_is_trivial("fun _ _ _ _ _ _ _ => True", set()))
        self.assertTrue(model.predicate_is_trivial("trueExtra", {"trueExtra"}))
        self.assertTrue(model.predicate_is_trivial("fun _ _ _ _ _ _ _ _ _ => True", set()))
        self.assertFalse(model.predicate_is_trivial("footExtra noArenaFoot", {"trueExtra"}))
        self.assertEqual(model.trivial_predicates(), {"trueExtra"})

    def test_parse_wiring_reads_filled_and_passthrough_fields(self) -> None:
        text = ("theorem Residuals.ofUnwired (L : Layout)\n    (hStr :\n      ∀ x, x)\n"
                "    : Residuals L where\n  hInt :=\n    fun _st hOld =>\n      lemma hOld\n"
                "  hStr := hStr\n  hBool := exactLemma\n\n#print axioms of_residuals\n")
        wiring = model.parse_wiring(text)
        self.assertEqual(wiring["hInt"], ("fun _st hOld => lemma hOld", 5))
        self.assertEqual(wiring["hBool"], ("exactLemma", 9))
        self.assertNotIn("hStr", wiring)
        self.assertEqual(model.parse_wiring("no such theorem"), {})


class ModelTests(unittest.TestCase):
    def test_tracked_clauses(self) -> None:
        loaded = model.load_model()
        trivial, footprint = loaded["Trivial"], loaded["Footprint"]
        self.assertEqual(trivial.module_state, "current")
        self.assertTrue(trivial.closed)
        self.assertEqual(trivial.counts()["WIRED"], 15)
        self.assertEqual(footprint.counts()["HOOK"] + footprint.counts()["WIRED"], 15)
        self.assertEqual(footprint.field("hCall").status, "HOOK")
        self.assertFalse(footprint.closed)
        self.assertEqual(footprint.guard, "")
        self.assertEqual(footprint.field("hInt").wiring, "Vsa.Sim.IHClauseGeneric.footprint.hInt")
        guarded = loaded["FootprintNA"]
        self.assertEqual(guarded.guard, "Vsa.Sim.IHClauseGeneric.noAllocExpr e = true")
        self.assertEqual(guarded.counts()["WIRED"], 13)
        self.assertEqual(guarded.counts()["HOOK"], 2)
        self.assertEqual(guarded.field("hCall").status, "WIRED")
        self.assertEqual(guarded.field("hBinary").hook_lemma,
                         "Vsa.Sim.IHClauseGeneric.footprintNA.hBinary")
        self.assertEqual(guarded.field("hNeg").hypothesis_names, ["old_1", "hOld", "ih_1", "hg"])
        self.assertTrue(guarded.field("hNeg").from_old_term("d").endswith("hOld _ih_1 _hg =>\n    d hOld"))
        self.assertIn("noAllocExpr e = true → EvalIHWithM extraM",
                      model.fragment_reason(guarded.field("hNeg"), guarded))
        self.assertTrue(guarded.field("hInt").wiring.startswith("fun st d env n hOld _hg =>"))
        field = trivial.field("hBinary")
        self.assertEqual(field.projection, "Vsa.Sim.IHClause.Trivial.Residuals.hBinary")
        self.assertEqual(field.module, "Vsa.Sim.rows.IHClause_Trivial")
        self.assertEqual(field.children, 2)
        self.assertEqual(field.hypothesis_names, ["old_1", "old_2", "hOld", "ih_1", "ih_2"])
        self.assertTrue(field.wiring.endswith("trivialStep_of_old hOld"))
        self.assertGreater(field.wiring_line, 0)
        self.assertEqual(footprint.field("hCall").hook_lemma,
                         "Vsa.Sim.IHClauseGeneric.footprint.hCall")
        self.assertIn("open Vsa.While", footprint.opens)
        with self.assertRaisesRegex(KeyError, "no field"):
            trivial.field("hSExpr")
        with self.assertRaisesRegex(ValueError, "unknown clause"):
            model.load_model(clauses=["Nope"])

    def test_missing_or_stale_module_marks_wired_fields_stale(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tsv = write_tsv(root, "Demo\ttrueExtra\t-\t-\thInt=from_old:trivialStep_of_old;"
                                  "hStr=exact:someLemma;hBool=manual;*=generic:fp\tnote\n")
            loaded = model.load_model(tsv, output_dir=root)["Demo"]
            self.assertEqual(loaded.module_state, "missing")
            self.assertEqual(loaded.field("hInt").status, "STALE")
            self.assertEqual(loaded.field("hStr").status, "STALE")
            self.assertEqual(loaded.field("hBool").status, "MANUAL")
            self.assertEqual(loaded.field("hNull").status, "HOOK")
            with redirect_stdout(io.StringIO()):
                generator.main(["--tsv", str(tsv), "--output-dir", str(root)])
            loaded = model.load_model(tsv, output_dir=root)["Demo"]
            self.assertEqual(loaded.module_state, "current")
            self.assertEqual(loaded.field("hInt").status, "WIRED")
            self.assertEqual(loaded.field("hStr").wiring, "someLemma")
            (root / "IHClause_Demo.lean").write_text(
                (root / "IHClause_Demo.lean").read_text() + "-- drift\n")
            loaded = model.load_model(tsv, output_dir=root)["Demo"]
            self.assertEqual(loaded.module_state, "stale")
            self.assertEqual(loaded.field("hInt").status, "STALE")

    def test_from_old_term_and_statement_module(self) -> None:
        loaded = model.load_model()
        info = loaded["Footprint"]
        field = info.field("hBinary")
        term = field.from_old_term("trivialStep_of_old")
        self.assertTrue(term.startswith("fun _st _d _env _op _l _r"))
        self.assertIn("_old_1 _old_2 hOld _ih_1 _ih_2 =>", term)
        self.assertTrue(term.endswith("trivialStep_of_old hOld"))
        text = model.statement_module(info, field, "Step_hBinary")
        self.assertTrue(text.startswith("import Vsa.Sim.rows.IHClause_Footprint\n"))
        self.assertIn("namespace Vsa.Sim.IHClause.Footprint", text)
        self.assertIn("def Step_hBinary (_L : Layout) : Prop :=\n  ∀ (st : SpecSt)", text)
        self.assertIn("end Vsa.Sim.IHClause.Footprint", text)
        reason = model.fragment_reason(field, info)
        self.assertIn("EvalIHWithM extraM", reason)
        self.assertIn("kind `extraM`, predicate `footExtra noArenaFoot`", reason)
        self.assertEqual(loaded["Trivial"].kind, "extra")
        self.assertTrue(field.from_old_term("d", ".toM").endswith("(d hOld).toM"))
        self.assertTrue(field.from_old_term("d", "ofWith").endswith("ofWith (d hOld)"))
        rows = model.field_rows(loaded)
        self.assertEqual(len(rows), sum(len(i.fields) for i in loaded.values()))
        self.assertNotIn("field_type", rows[0])


if __name__ == "__main__":
    unittest.main()
