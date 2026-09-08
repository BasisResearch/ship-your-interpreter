"""Tests for the clause residual status, hook probes and candidate drafts."""

import io
import json
import sys
import tempfile
import types
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest.mock import patch

from scripts import field_census as census
from scripts import ih_clause_model as model
from scripts import ih_clause_status as status

MISSING = ("Probe.lean:3:14: error(lean.unknownIdentifier): Unknown constant "
           "`Vsa.Sim.IHClauseGeneric.footprint.hInt`\n")
EXISTS = "'Vsa.Sim.IHClauseGeneric.footprint.hStr' depends on axioms: [propext]\n"
UNCLEAN = "'Vsa.Sim.IHClauseGeneric.footprint.hBool' depends on axioms: [propext, sorryAx]\n"


class ParsingTests(unittest.TestCase):
    def test_axiom_reports_unknown_constants_and_errors(self) -> None:
        output = MISSING + EXISTS + UNCLEAN + "'N.clean' does not depend on any axioms\n"
        reports = status.axiom_reports(output)
        self.assertEqual(reports["Vsa.Sim.IHClauseGeneric.footprint.hStr"], ["propext"])
        self.assertEqual(reports["N.clean"], [])
        self.assertTrue(status.clean(reports["N.clean"]))
        self.assertFalse(status.clean(reports["Vsa.Sim.IHClauseGeneric.footprint.hBool"]))
        self.assertEqual(status.unknown_constants(output),
                         {"Vsa.Sim.IHClauseGeneric.footprint.hInt"})
        self.assertEqual(status.error_lines(output),
                         [(3, "Unknown constant `Vsa.Sim.IHClauseGeneric.footprint.hInt`")])

    def test_candidate_and_target_parsing(self) -> None:
        self.assertEqual(status.parse_candidate("from_old:x"), ("from_old", "x"))
        self.assertEqual(status.parse_target("hInt=valuerepr-copy:str"),
                         ("hInt", "valuerepr-copy:str"))
        for bad in ("manual", "generic:x", "bogus:y"):
            with self.assertRaises(Exception):
                status.parse_candidate(bad)
        with self.assertRaises(Exception):
            status.parse_target("hInt")


class HookProbeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.info = model.load_model(clauses=["Footprint"])["Footprint"]

    def test_probe_hooks_classifies_each_lemma(self) -> None:
        with patch.object(status, "run_lean",
                          return_value=census.LeanResult(1, MISSING + EXISTS + UNCLEAN)):
            verdicts = status.probe_hooks(self.info, Path("/backend"), Path("/out"))
        self.assertEqual(verdicts["Vsa.Sim.IHClauseGeneric.footprint.hInt"], "missing")
        self.assertEqual(verdicts["Vsa.Sim.IHClauseGeneric.footprint.hStr"], "exists")
        self.assertEqual(verdicts["Vsa.Sim.IHClauseGeneric.footprint.hBool"], "exists-unclean")
        self.assertEqual(verdicts["Vsa.Sim.IHClauseGeneric.footprint.hCall"], "unknown")

    def test_source_scan_finds_theorem_under_namespace(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Vsa").mkdir()
            (root / "Vsa/G.lean").write_text(
                "namespace Vsa.Sim.IHClauseGeneric.footprint\n"
                "theorem hStr : True := trivial\n-- theorem hInt\nend Vsa.Sim\n")
            status._SOURCE_INDEX.clear()
            self.assertTrue(status.declared_in_source(
                "Vsa.Sim.IHClauseGeneric.footprint.hStr", root))
            self.assertFalse(status.declared_in_source(
                "Vsa.Sim.IHClauseGeneric.footprint.hInt", root))
            self.assertFalse(status.declared_in_source("Other.ns.hStr", root))
            status._SOURCE_INDEX.clear()

    def test_census_probe_source_uses_wiring(self) -> None:
        info = model.load_model(clauses=["Trivial"])["Trivial"]
        text = status.census_probe_source(info, info.field("hInt"), census.LAYOUT)
        self.assertIn("import Vsa.Sim.rows.IHClause_Trivial", text)
        self.assertIn("census_probe Vsa.Sim.IHClause.Trivial.Residuals hInt at", text)
        self.assertIn("using fun _st _d _env _n hOld => trivialStep_of_old hOld", text)


class DraftTests(unittest.TestCase):
    def setUp(self) -> None:
        self.info = model.load_model(clauses=["Footprint"])["Footprint"]

    def test_draft_source_line_ranges_cover_each_theorem(self) -> None:
        field = self.info.field("hInt")
        drafts = {"hInt": status.candidates(field, ["trivialStep_of_old"], [("exact", "foo")],
                                            "extraM")}
        self.assertEqual([c.label for c in drafts["hInt"]],
                         ["exact:Vsa.Sim.IHClauseGeneric.footprint.hInt",
                          "from_old:trivialStep_of_old", "from_old:.toM∘trivialStep_of_old",
                          "exact:foo"])
        self.assertTrue(drafts["hInt"][2].term.endswith("(trivialStep_of_old hOld).toM"))
        wrapped = status.candidates(field, ["d"], [], "extra")
        self.assertTrue(wrapped[2].term.endswith("ofWith (d hOld)"))
        shaped = status.candidates(field, ["d"], [], "extraM", frozenset({"d"}))
        self.assertEqual([c.label for c in shaped][1:], ["from_old:d"])
        source, ranges = status.draft_source(self.info, drafts)
        lines = source.splitlines()
        for name, (start, end) in ranges.items():
            index = int(name.rsplit("_", 1)[1])
            self.assertEqual(lines[start - 1],
                             f"/-- `hInt` candidate {index}: `{drafts['hInt'][index - 1].label}`. -/")
            self.assertEqual(lines[end - 1], "")
            self.assertEqual(lines[end - 2], f"#print axioms {name}")
        self.assertTrue(source.rstrip().endswith("end Vsa.Sim.IHClause.Footprint"))

    def test_evaluate_drafts_attributes_errors_by_line(self) -> None:
        field = self.info.field("hInt")
        drafts = {"hInt": status.candidates(field, ["trivialStep_of_old"], [])}
        _, ranges = status.draft_source(self.info, drafts)
        first_start = ranges["draft_hInt_1"][0]
        ns = self.info.namespace
        output = (f"D.lean:{first_start + 3}:2: error: Unknown identifier `x`\n"
                  f"'{ns}.draft_hInt_1' depends on axioms: [sorryAx]\n"
                  f"'{ns}.draft_hInt_2' depends on axioms: [propext]\n")
        result = status.evaluate_drafts(self.info, drafts, output, ranges)
        self.assertEqual(result["hInt"]["candidate"], "from_old:trivialStep_of_old")
        self.assertIn("Unknown identifier", result["hInt"]["detail"])
        failing = status.evaluate_drafts(self.info, drafts, "", ranges)
        self.assertEqual(failing["hInt"]["candidate"], "")
        self.assertIn("no axiom report", failing["hInt"]["detail"])

    def test_outcome_mapping(self) -> None:
        self.assertEqual(status.outcome("from_old:x", True, "ENCODE-GAP: y", "ENCODE-GAP: y"),
                         "DIRECT")
        self.assertEqual(status.outcome("", False, "PROVABLE-DIRECT: z", "ENCODE-GAP: y"),
                         "DIRECT")
        self.assertEqual(status.outcome("", False, "IH-FOUND: s", "ENCODE-GAP: y"), "WITH-IH")
        self.assertEqual(status.outcome("", True, "ENCODE-GAP: y", "ENCODE-GAP: y"), "FAILED")
        self.assertEqual(status.outcome("", False, "IH-NOT-FOUND: y", "ENCODE-GAP: y"), "FAILED")
        self.assertEqual(status.outcome("", False, "ENCODE-GAP: y", "ENCODE-GAP: y"),
                         "UNSUPPORTED")

    def test_bounded_engines_register_temporarily(self) -> None:
        houdini = types.ModuleType("houdini_ih")
        houdini.FIELD_REGISTRY = {}
        houdini.run_field = lambda key: {"verdict": "ENCODE-GAP",
                                         "detail": houdini.FIELD_REGISTRY[key][0]}
        autoprove = types.ModuleType("autoprove")
        autoprove.FIELD_MAP = {}
        autoprove.run_field = lambda key, **kw: {"verdict": "ENCODE-GAP", "detail": str(kw)}
        with patch.dict(sys.modules, {"houdini_ih": houdini, "autoprove": autoprove}):
            result = status.bounded_engines("IHClause.X.hInt", "encode-gap:why", "lemma")
        self.assertEqual(result["houdini"], "ENCODE-GAP: encode-gap:why")
        self.assertIn("'do_transcribe': False", result["autoprove"])
        self.assertEqual(houdini.FIELD_REGISTRY, {})
        self.assertEqual(autoprove.FIELD_MAP, {})

    def test_suggest_without_backend_is_unsupported_and_writes_draft(self) -> None:
        with tempfile.TemporaryDirectory() as directory, \
                patch.object(status, "bounded_engines",
                             return_value={"houdini": "ENCODE-GAP: a", "autoprove": "ENCODE-GAP: a"}):
            rows = status.suggest(self.info, None, Path(directory), ["trivialStep_of_old"], [],
                                  {}, {"trueExtra"})
            self.assertEqual(len(rows), 15)
            self.assertTrue(all(r["outcome"] == "UNSUPPORTED" for r in rows))
            self.assertTrue(all(r["encoding"].startswith("encode-gap:the step concludes")
                                for r in rows))
            self.assertIn("footExtra noArenaFoot", rows[0]["encoding"])
            trivial = model.load_model(clauses=["Trivial"])["Trivial"]
            info = model.ClauseInfo(**{**trivial.__dict__, "fields": tuple(
                f.__class__(**{**f.__dict__, "status": "MANUAL"}) for f in trivial.fields)})
            rows = status.suggest(info, None, Path(directory), [], [], {}, {"trueExtra"})
            self.assertTrue(all(r["encoding"].startswith("encode-gap:predicate retains")
                                for r in rows))
            self.assertTrue((Path(directory) / "drafts/Draft_Footprint.lean").is_file())
            self.assertFalse(list((Path(directory) / "drafts").glob("*.log")))


class MainTests(unittest.TestCase):
    def test_summary_prints_without_writing(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            captured = io.StringIO()
            with redirect_stdout(captured):
                code = status.main(["--summary", "--no-source-scan", "--output", directory,
                                    "--clause", "Trivial"])
            self.assertEqual(code, 0)
            self.assertIn("Trivial", captured.getvalue())
            self.assertIn("WIRED 15", captured.getvalue())
            self.assertFalse((Path(directory) / "ih_clause_status.tsv").exists())

    def test_output_writes_tsv_and_json(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            captured = io.StringIO()
            with redirect_stdout(captured):
                code = status.main(["--no-source-scan", "--output", directory])
            self.assertEqual(code, 0)
            rows = (Path(directory) / "ih_clause_status.tsv").read_text().splitlines()
            self.assertEqual(rows[0].split("\t"), list(status.STATUS_COLUMNS))
            self.assertEqual(len(rows), 31)
            report = json.loads((Path(directory) / "ih_clause_status.json").read_text())
            self.assertIsNone(report["backend"])
            self.assertEqual(len(report["status"]), 30)
            self.assertEqual(report["clauses"]["Trivial"]["module_state"], "current")

    def test_unknown_clause_fails(self) -> None:
        with redirect_stdout(io.StringIO()):
            self.assertEqual(status.main(["--summary", "--clause", "Nope"]), 2)


if __name__ == "__main__":
    unittest.main()
