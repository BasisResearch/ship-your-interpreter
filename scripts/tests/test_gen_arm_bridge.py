"""Regression tests for generated block-A arm bridges."""

import unittest
from pathlib import Path

from scripts import gen_arm_bridge


class ArmBridgeGenerationTests(unittest.TestCase):
    """Keep checked-in arm bridges synchronized with their TOML sources."""

    def test_checked_in_bridges_match_specs(self) -> None:
        """Render both arm specs exactly as checked in."""
        cases = (
            ("blockA_unary.toml", "BlockAUnaryArmGen.lean"),
            ("blockA_logical.toml", "BlockALogicalArmGen.lean"),
        )
        root = Path(gen_arm_bridge.ROOT)

        for spec_name, output_name in cases:
            with self.subTest(spec=spec_name):
                spec = gen_arm_bridge.lib.load_toml(
                    root / "scripts" / "arms" / spec_name
                )
                rendered = gen_arm_bridge.emit(gen_arm_bridge.norm(spec)).text()
                expected = (root / "Vsa" / "Sim" / "rows" / output_name).read_text(
                    encoding="utf-8"
                )
                self.assertEqual(rendered.rstrip("\n"), expected.rstrip("\n"))


if __name__ == "__main__":
    unittest.main()
