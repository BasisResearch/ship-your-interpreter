"""Offline generation checks; never invoke Lean or a solver."""

import contextlib
import io
import json
import shutil
from pathlib import Path
import tempfile
import unittest

from scripts import gen_fixed_image as GEN

ROOT = Path(__file__).resolve().parents[2]


class GeneratorTests(unittest.TestCase):
    def copy_inputs(self, destination: Path) -> None:
        for relative in (
            "c/while-riscv-htif.elf",
            "Vsa/ElfBytes.lean",
            "Vsa/Sim/Code/Interp_run.lean",
            "Vsa/Sim/Code/Setjmp.lean",
        ):
            target = destination / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / relative, target)

    def test_fixed_sections_and_byte_mutation_rejection(self) -> None:
        raw = (ROOT / "c/while-riscv-htif.elf").read_bytes()
        sections = GEN.sections_from_elf(raw)
        self.assertEqual(sum(len(data) for _, data in sections.values()), 109808)
        changed = bytearray(raw)
        changed[0x1000] ^= 1
        with self.assertRaisesRegex(ValueError, "approved fixed image"):
            GEN.sections_from_elf(bytes(changed))

    def test_other_existing_function_projection_uses_same_generator(self) -> None:
        sections = GEN.sections_from_elf((ROOT / "c/while-riscv-htif.elf").read_bytes())
        image = {
            base + i: byte
            for base, data in sections.values()
            for i, byte in enumerate(data)
        }
        for module in (
            "Exec_stmt",
            "Eval_expr",
            "Value_truthy",
            "Env_new",
            "Main",
            "Exit",
        ):
            with self.subTest(module=module):
                text, count = GEN.projection_module(ROOT, module, image)
                self.assertGreater(count, 0)
                self.assertIn(f"FixedTextLoaded.{module}Loaded", text)

    def test_existing_code_byte_drift_is_rejected(self) -> None:
        sections = GEN.sections_from_elf((ROOT / "c/while-riscv-htif.elf").read_bytes())
        image = {
            base + i: byte
            for base, data in sections.values()
            for i, byte in enumerate(data)
        }
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            target = root / "Vsa/Sim/Code/Setjmp.lean"
            target.parent.mkdir(parents=True)
            source = (ROOT / "Vsa/Sim/Code/Setjmp.lean").read_text()
            match = GEN.BYTE_PIN.search(source)
            self.assertIsNotNone(match)
            assert match is not None
            wrong = f"{int(match[2], 16) ^ 1:02x}"
            target.write_text(source[: match.start(2)] + wrong + source[match.end(2) :])
            with self.assertRaisesRegex(ValueError, "differ from ELF"):
                GEN.projection_module(root, "Setjmp", image)

    def test_check_rejects_modified_output_without_overwriting_it(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.copy_inputs(root)
            with contextlib.redirect_stdout(io.StringIO()):
                # The default output follows the explicitly selected repository.
                GEN.main(["--repo", str(root)])
                GEN.main(["--repo", str(root), "--check"])
                output = root / "Vsa/Sim/Code"
                report = json.loads((output / "fixed-image-manifest.json").read_text())
                self.assertEqual(report["elf_sha256"], GEN.ELF_SHA256)
                self.assertEqual(report["schema"], "vsa.fixed-image-manifest.v1")
                self.assertNotIn("lean_compiled", report)
                target = output / "FixedImageData.lean"
                changed = target.read_text() + "\n-- changed after generation\n"
                target.write_text(changed)
                with self.assertRaisesRegex(ValueError, "output is stale"):
                    GEN.main(["--repo", str(root), "--check"])
                self.assertEqual(target.read_text(), changed)

    def test_embedded_elf_drift_rejected_before_any_output(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.copy_inputs(root)
            embedded = root / "Vsa/ElfBytes.lean"
            embedded.write_text(
                embedded.read_text().replace('"7f454c46', '"00454c46', 1)
            )
            output = root / "generated"
            with self.assertRaisesRegex(ValueError, "embedded elfHex"):
                GEN.main(["--repo", str(root), "--output", str(output)])
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
