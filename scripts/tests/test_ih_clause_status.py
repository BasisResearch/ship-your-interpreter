"""Tests for the clause residual status, hook probes and candidate drafts."""

import base64
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
           "`Vsa.Sim.IHClauseGeneric.footprint.hCall`\n")
EXISTS = "'Vsa.Sim.IHClauseGeneric.footprint.hVar' depends on axioms: [propext]\n"
UNCLEAN = "'Vsa.Sim.IHClauseGeneric.footprint.hBinary' depends on axioms: [propext, sorryAx]\n"


class ParsingTests(unittest.TestCase):
    def test_axiom_reports_unknown_constants_and_errors(self) -> None:
        output = MISSING + EXISTS + UNCLEAN + "'N.clean' does not depend on any axioms\n"
        reports = status.axiom_reports(output)
        self.assertEqual(reports["Vsa.Sim.IHClauseGeneric.footprint.hVar"], ["propext"])
        self.assertEqual(reports["N.clean"], [])
        self.assertTrue(status.clean(reports["N.clean"]))
        self.assertFalse(status.clean(reports["Vsa.Sim.IHClauseGeneric.footprint.hBinary"]))
        self.assertEqual(status.unknown_constants(output),
                         {"Vsa.Sim.IHClauseGeneric.footprint.hCall"})
        self.assertEqual(status.error_lines(output),
                         [(3, "Unknown constant `Vsa.Sim.IHClauseGeneric.footprint.hCall`")])

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
        self.assertEqual(verdicts["Vsa.Sim.IHClauseGeneric.footprint.hCall"], "missing")
        self.assertEqual(verdicts["Vsa.Sim.IHClauseGeneric.footprint.hVar"], "exists")
        self.assertEqual(verdicts["Vsa.Sim.IHClauseGeneric.footprint.hBinary"], "exists-unclean")
        self.assertEqual(verdicts["Vsa.Sim.IHClauseGeneric.footprint.hAssign"], "unknown")

    def test_source_scan_finds_theorem_under_namespace(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Vsa").mkdir()
            (root / "Vsa/G.lean").write_text(
                "namespace Vsa.Sim.IHClauseGeneric.footprint\n"
                "theorem hVar : True := trivial\n-- theorem hCall\nend Vsa.Sim\n")
            status._SOURCE_INDEX.clear()
            self.assertTrue(status.declared_in_source(
                "Vsa.Sim.IHClauseGeneric.footprint.hVar", root))
            self.assertFalse(status.declared_in_source(
                "Vsa.Sim.IHClauseGeneric.footprint.hCall", root))
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
        field = self.info.field("hCall")
        drafts = {"hCall": status.candidates(field, ["trivialStep_of_old"], [("exact", "foo")],
                                            "extraM")}
        self.assertEqual([c.label for c in drafts["hCall"]],
                         ["exact:Vsa.Sim.IHClauseGeneric.footprint.hCall",
                          "from_old:trivialStep_of_old", "from_old:.toM∘trivialStep_of_old",
                          "exact:foo"])
        self.assertTrue(drafts["hCall"][2].term.endswith("(trivialStep_of_old hOld).toM"))
        wrapped = status.candidates(field, ["d"], [], "extra")
        self.assertTrue(wrapped[2].term.endswith("ofWith (d hOld)"))
        shaped = status.candidates(field, ["d"], [], "extraM", frozenset({"d"}))
        self.assertEqual([c.label for c in shaped][1:], ["from_old:d"])
        source, ranges = status.draft_source(self.info, drafts)
        lines = source.splitlines()
        for name, (start, end) in ranges.items():
            index = int(name.rsplit("_", 1)[1])
            self.assertEqual(lines[start - 1],
                             f"/-- `hCall` candidate {index}: `{drafts['hCall'][index - 1].label}`. -/")
            self.assertEqual(lines[end - 1], "")
            self.assertEqual(lines[end - 2], f"#print axioms {name}")
        self.assertTrue(source.rstrip().endswith("end Vsa.Sim.IHClause.Footprint"))

    def test_evaluate_drafts_attributes_errors_by_line(self) -> None:
        field = self.info.field("hCall")
        drafts = {"hCall": status.candidates(field, ["trivialStep_of_old"], [], "extraM")}
        _, ranges = status.draft_source(self.info, drafts)
        first_start = ranges["draft_hCall_1"][0]
        ns = self.info.namespace
        output = (f"D.lean:{first_start + 3}:2: error: Unknown identifier `x`\n"
                  f"'{ns}.draft_hCall_1' depends on axioms: [sorryAx]\n"
                  f"'{ns}.draft_hCall_2' depends on axioms: [propext]\n")
        result = status.evaluate_drafts(self.info, drafts, output, ranges)
        self.assertEqual(result["hCall"]["candidate"], "from_old:trivialStep_of_old")
        self.assertIn("Unknown identifier", result["hCall"]["detail"])
        failing = status.evaluate_drafts(self.info, drafts, "", ranges)
        self.assertEqual(failing["hCall"]["candidate"], "")
        self.assertIn("no axiom report", failing["hCall"]["detail"])

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
            self.assertEqual(
                len(rows), sum(f.status in ("HOOK", "MANUAL", "STALE") for f in self.info.fields))
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

    def test_suggest_receipts_mocked_lean_failure_with_exact_inputs(self) -> None:
        receipt_tool = status.attempt_receipts
        digest = "a" * 64
        file_ = receipt_tool.FileFingerprint("/tool", "/tool", digest, 1, None)
        dependency = receipt_tool.DependencyFingerprint(
            "Vsa.A", file_, digest, digest, file_, True
        )
        environment = receipt_tool.ArtifactInventory(
            "lean-toolchain-lib", "/toolchain/lib/lean", digest, 1, 1, None
        )
        snapshot = receipt_tool.BuildSnapshot(
            "2026-09-11T00:00:00+00:00",
            (self.info.module,),
            digest,
            (file_,),
            file_,
            (dependency,),
            (),
            (environment,),
            "",
            (),
        )
        engine_result = {"houdini": "ENCODE-GAP: a", "autoprove": "ENCODE-GAP: a"}
        with (
            tempfile.TemporaryDirectory() as directory,
            patch.object(status, "run_lean", return_value=census.LeanResult(
                1, "maximum number of heartbeats exceeded"
            )),
            patch.object(status, "bounded_engines", return_value=engine_result),
            patch.object(receipt_tool, "capture_build_snapshot", return_value=snapshot),
        ):
            rows = status.suggest(
                self.info,
                Path("/backend"),
                Path(directory),
                ["trivialStep_of_old"],
                [],
                {},
                {"trueExtra"},
                rerun_reason="confirm deterministic failure",
            )
            paths = list((Path(directory) / "attempts").glob("attempt-*.json"))
            self.assertEqual(len(paths), 1)
            receipt = json.loads(paths[0].read_text())
            self.assertEqual(
                receipt["result"]["failure_class"], "deterministic_heartbeat_timeout"
            )
            diagnostics = receipt["result"]["diagnostics"]
            self.assertEqual(
                base64.b64decode(diagnostics["utf8_base64"]).decode(),
                "maximum number of heartbeats exceeded",
            )
            self.assertEqual(receipt["rerun_reason"], "confirm deterministic failure")
            self.assertIsNotNone(receipt["comparable_key"])
            self.assertTrue(all(row["attempt_receipt"] == str(paths[0]) for row in rows))
            candidate = next(
                item
                for item in receipt["generated"]["candidates"]
                if item["target"].endswith(".hCall") and item["label"].startswith("exact:")
            )
            encoded = candidate["candidate"]["utf8_base64"]
            self.assertEqual(
                base64.b64decode(encoded).decode(),
                model.indent(
                    status.candidates(
                        self.info.field("hCall"), ["trivialStep_of_old"], [], "extraM"
                    )[0].term,
                    2,
                ),
            )
            self.assertEqual(
                set(receipt["timing_seconds"]),
                {"environment_capture_before", "lean_wall", "environment_capture_after"},
            )

            def interrupted(_backend, output, name, _source):
                (output / f"{name}.log").write_text("partial compiler transcript\n")
                raise KeyboardInterrupt

            with (
                patch.object(status, "run_lean", side_effect=interrupted),
                patch.object(receipt_tool, "capture_build_snapshot", return_value=snapshot),
                self.assertRaises(KeyboardInterrupt),
            ):
                status.suggest(
                    self.info,
                    Path("/backend"),
                    Path(directory),
                    ["trivialStep_of_old"],
                    [],
                    {},
                    {"trueExtra"},
                )
            paths = list((Path(directory) / "attempts").glob("attempt-*.json"))
            self.assertEqual(len(paths), 2)
            cancelled = next(
                json.loads(path.read_text())
                for path in paths
                if json.loads(path.read_text())["result"]["failure_class"]
                == "explicit_transient_failure"
            )
            diagnostics = cancelled["result"]["diagnostics"]
            self.assertEqual(
                base64.b64decode(diagnostics["utf8_base64"]).decode(),
                "partial compiler transcript\n",
            )

            draft_log = Path(directory) / "drafts/Draft_Footprint.log"
            draft_log.write_text("old diagnostics that must not be reused\n")
            with (
                patch.object(
                    status, "run_lean", side_effect=OSError("compiler startup failed")
                ),
                patch.object(receipt_tool, "capture_build_snapshot", return_value=snapshot),
                self.assertRaises(OSError),
            ):
                status.suggest(
                    self.info,
                    Path("/backend"),
                    Path(directory),
                    ["trivialStep_of_old"],
                    [],
                    {},
                    {"trueExtra"},
                )
            receipts_ = [
                json.loads(path.read_text())
                for path in (Path(directory) / "attempts").glob("attempt-*.json")
            ]
            startup = next(
                receipt
                for receipt in receipts_
                if receipt["result"]["failure_class"] == "invocation_error"
            )
            diagnostics = startup["result"]["diagnostics"]
            self.assertEqual(
                base64.b64decode(diagnostics["utf8_base64"]).decode(),
                "compiler startup failed",
            )
            self.assertNotIn("old diagnostics", base64.b64decode(
                diagnostics["utf8_base64"]
            ).decode())

    def test_suggest_rejects_clean_candidate_when_build_inputs_drift(self) -> None:
        receipt_tool = status.attempt_receipts
        digest = "a" * 64
        changed_digest = "b" * 64
        file_ = receipt_tool.FileFingerprint("/tool", "/tool", digest, 1, None)
        dependency = receipt_tool.DependencyFingerprint(
            "Vsa.A", file_, digest, digest, file_, True
        )
        before = receipt_tool.BuildSnapshot(
            "2026-09-11T00:00:00+00:00",
            (self.info.module,),
            digest,
            (file_,),
            file_,
            (dependency,),
            (),
            (receipt_tool.ArtifactInventory(
                "lean-toolchain-lib", "/toolchain/lib/lean", digest, 1, 1, None
            ),),
            "",
            (),
        )
        after = receipt_tool.BuildSnapshot(
            **{
                **before.__dict__,
                "environment_artifacts": (
                    receipt_tool.ArtifactInventory(
                        "lean-toolchain-lib",
                        "/toolchain/lib/lean",
                        changed_digest,
                        1,
                        1,
                        None,
                    ),
                ),
            }
        )
        output = (
            f"'{self.info.namespace}.draft_hVar_1' "
            "does not depend on any axioms\n"
        )
        engine_result = {"houdini": "ENCODE-GAP: a", "autoprove": "ENCODE-GAP: a"}
        with (
            tempfile.TemporaryDirectory() as directory,
            patch.object(status, "run_lean", return_value=census.LeanResult(0, output)),
            patch.object(status, "bounded_engines", return_value=engine_result),
            patch.object(
                receipt_tool, "capture_build_snapshot", side_effect=[before, after]
            ),
        ):
            rows = status.suggest(
                self.info,
                Path("/backend"),
                Path(directory),
                ["trivialStep_of_old"],
                [],
                {},
                {"trueExtra"},
            )
            self.assertTrue(all(not row["lean_candidate"] for row in rows))
            self.assertTrue(
                all("stale or changing build inputs" in row["lean_detail"] for row in rows)
            )
            receipt_path = next(
                (Path(directory) / "attempts").glob("attempt-*.json")
            )
            receipt = json.loads(receipt_path.read_text())
            self.assertEqual(
                receipt["result"]["failure_class"], "stale_or_missing_dependency"
            )
            self.assertIsNone(receipt["comparable_key"])


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
            fields = sum(len(i.fields) for i in model.load_model().values())
            self.assertEqual(len(rows), fields + 1)
            report = json.loads((Path(directory) / "ih_clause_status.json").read_text())
            self.assertIsNone(report["backend"])
            self.assertEqual(len(report["status"]), fields)
            self.assertEqual(report["clauses"]["Trivial"]["module_state"], "current")

    def test_unknown_clause_fails(self) -> None:
        with redirect_stdout(io.StringIO()):
            self.assertEqual(status.main(["--summary", "--clause", "Nope"]), 2)


if __name__ == "__main__":
    unittest.main()
