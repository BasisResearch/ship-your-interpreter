"""Tests for the footprint-row generator."""

from pathlib import Path
import contextlib
import io
import tempfile
import unittest

import scripts.gen_footprint_row as generator


TRACKED = generator.TSV.read_text()


def tsv_with(directory: Path, **edits: dict[str, str]) -> Path:
    """The tracked table with per-arm cell edits applied."""
    lines = []
    columns = generator.COLUMNS
    for line in TRACKED.splitlines(True):
        if line.startswith("#") or line.startswith("arm\t") or not line.strip():
            lines.append(line)
            continue
        cells = line.rstrip("\n").split("\t")
        patch = edits.get(cells[0])
        if patch:
            for column, value in patch.items():
                cells[columns.index(column)] = value
        lines.append("\t".join(cells) + "\n")
    target = directory / "rows.tsv"
    target.write_text("".join(lines))
    return target


def write_raw(directory: Path, body: str) -> Path:
    target = directory / "rows.tsv"
    target.write_text("\t".join(generator.COLUMNS) + "\n" + body)
    return target


class SchemaTests(unittest.TestCase):
    def test_tracked_table_parses(self) -> None:
        rows = generator.load_rows()
        self.assertEqual([row.arm for row in rows],
                         ["add", "sub", "mul", "div", "mod", "lt", "le", "gt", "ge",
                          "neg", "not", "orTrue", "andFalse", "andTrue", "orFalse"])
        self.assertEqual({row.family for row in rows},
                         {"int", "intPilot", "unary", "logicalShort", "logicalFall"})
        by_arm = {row.arm: row for row in rows}
        self.assertEqual(by_arm["add"].module, "EvalAddRowFootprint")
        self.assertEqual(by_arm["add"].guards, [])
        self.assertEqual(by_arm["div"].guards,
                         [("hbNe", "b ≠ 0"), ("hOv", "¬(a = -2^63 ∧ b = -1)")])
        self.assertEqual(by_arm["mod"].guards, [("hbNe", "b ≠ 0")])
        self.assertEqual(by_arm["not"].shared, "truthyArgCellFoot")
        self.assertEqual(by_arm["andTrue"].node, "logFallNodeFoot Fl Fr 848")
        self.assertEqual(by_arm["orTrue"].cap, "OrTrue")

    def test_every_family_has_a_template(self) -> None:
        families = {row.family for row in generator.load_rows()}
        self.assertEqual(families, set(generator.TEMPLATES))
        self.assertEqual(set(generator.TEMPLATES), set(generator.SLOTS_FROM_TSV))

    def test_invalid_rows_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            cases = {
                "unknown family": ({"add": {"family": "bogus"}}, "unknown family"),
                "module mismatch": ({"add": {"module": "EvalOtherRowFootprint"}},
                                    "does not match the arm"),
                "bad guard": ({"div": {"guard": "hbNe"}}, "is not name=prop"),
            }
            for name, (edits, message) in cases.items():
                with self.subTest(name=name):
                    with self.assertRaisesRegex(ValueError, message):
                        generator.load_rows(tsv_with(root, **edits))
            raw = {
                "Add\tint\tEvalAddRowFootprint\n": "expected 15 columns",
                "\t".join(["1bad"] + ["-"] * 14) + "\n": "bad arm name",
            }
            for body, message in raw.items():
                with self.subTest(body=body):
                    with self.assertRaisesRegex(ValueError, message):
                        generator.load_rows(write_raw(root, body))
            duplicate = TRACKED + [l for l in TRACKED.splitlines(True)
                                   if l.startswith("add\t")][0]
            target = root / "dup.tsv"
            target.write_text(duplicate)
            with self.assertRaisesRegex(ValueError, "duplicate arms: add"):
                generator.load_rows(target)
            headerless = root / "nohdr.tsv"
            headerless.write_text("add\tint\tEvalAddRowFootprint\n".replace("add", "zz", 1))
            with self.assertRaisesRegex(ValueError, "header row"):
                generator.load_rows(headerless)


class EmissionTests(unittest.TestCase):
    def test_tracked_modules_match_the_generator(self) -> None:
        rows = {row.arm: row for row in generator.load_rows()}
        for arm, text in generator.render_all().items():
            self.assertEqual(rows[arm].path.read_text(), text, arm)

    def test_emission_is_deterministic(self) -> None:
        self.assertEqual(generator.render_all(), generator.render_all())

    def test_generated_modules_carry_the_declared_interface(self) -> None:
        rendered = generator.render_all()
        rows = {row.arm: row for row in generator.load_rows()}
        for arm, text in rendered.items():
            row = rows[arm]
            self.assertIn(f"theorem eval{row.cap}SimF", text, arm)
            self.assertIn(f"#print axioms eval{row.cap}SimF", text, arm)
            self.assertIn("set_option maxHeartbeats 4000000", text, arm)
            if row.supplier != "-":
                self.assertIn(f"theorem {row.supplier}", text, arm)
            if row.shared != "-":
                self.assertIn(f"exact {row.shared}_noArena h k hc", text, arm)

    def test_table_template_disagreement_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tsv = tsv_with(root, add={"cell": "wrongCellFoot"})
            with self.assertRaisesRegex(ValueError, "does not occur in the"):
                generator.render_all(tsv)
            tsv = tsv_with(root, andTrue={"result": "(.bool wrong)"})
            with self.assertRaisesRegex(ValueError, "does not occur in the"):
                generator.render_all(tsv)

    def test_new_arm_without_fragments_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            extra = "\t".join([
                "xor", "unary", "EvalXorRowFootprint", "(.int 0)", "-", "-", "-", "-",
                "xorCellFoot", "intCellFoot", "xorNodeFoot", "value_int", "evalXorIHF",
                "XorExtras", "new arm"]) + "\n"
            target = root / "rows.tsv"
            target.write_text(TRACKED + extra)
            with self.assertRaisesRegex(ValueError, "no value for slot"):
                generator.render_all(target)


class CheckModeTests(unittest.TestCase):
    def test_check_detects_drift(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            out = root / "rows"
            base = ["--tsv", str(generator.TSV), "--output-dir", str(out)]
            with contextlib.redirect_stdout(io.StringIO()), \
                    contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(generator.main(base), 0)
                self.assertEqual(generator.main(base + ["--check"]), 0)
                target = out / "EvalAddRowFootprint.lean"
                target.write_text(target.read_text() + "-- drift\n")
                errors = io.StringIO()
                with contextlib.redirect_stderr(errors):
                    self.assertEqual(generator.main(base + ["--check"]), 1)
                self.assertIn("EvalAddRowFootprint.lean is stale", errors.getvalue())
                self.assertIn("-- drift", errors.getvalue())
                target.unlink()
                self.assertEqual(generator.main(base + ["--check", "--arm", "add"]), 1)
                self.assertEqual(generator.main(base + ["--arm", "nope"]), 2)

    def test_stdout_writes_nothing(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory) / "rows"
            captured = io.StringIO()
            with contextlib.redirect_stdout(captured):
                code = generator.main(["--output-dir", str(out), "--stdout", "--arm", "neg"])
            self.assertEqual(code, 0)
            self.assertIn("theorem evalNegIHF", captured.getvalue())
            self.assertFalse(out.exists())


if __name__ == "__main__":
    unittest.main()
