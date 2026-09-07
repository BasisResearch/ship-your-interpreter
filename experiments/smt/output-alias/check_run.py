#!/usr/bin/env python3
"""Validate scratch experiment inputs and, optionally, its JSON-lines output."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

ELF_SHA256 = "b146c6edb76ea9a0f0f30be381f8176ed2de9717e1ae9b37feff4b2b9ca1d0f0"


def check_inputs(repo: Path) -> dict[str, str]:
    elf = (repo / "c/while-riscv-htif.elf").read_bytes()
    digest = hashlib.sha256(elf).hexdigest()
    if digest != ELF_SHA256:
        raise ValueError(f"fixed ELF digest differs: {digest}")
    source = (repo / "Vsa/ElfBytes.lean").read_text()
    match = re.search(r'def elfHex\s*:\s*String\s*:=\s*"([0-9a-f]+)"', source)
    if match is None or bytes.fromhex(match[1]) != elf:
        raise ValueError("embedded ELF bytes differ from the fixed ELF")
    harness = Path(__file__).with_name("AliasMachine.lean")
    return {
        "elf_sha256": digest,
        "harness_sha256": hashlib.sha256(harness.read_bytes()).hexdigest(),
    }


def check_results(path: Path) -> dict[str, object]:
    rows = [
        json.loads(line)
        for line in path.read_text().splitlines()
        if line.startswith("{")
    ]
    boot = next(row for row in rows if "boot_steps" in row)
    if boot["fixed_image_changes"] != 0:
        raise ValueError("startup changed fixed image bytes")
    cases = {row["case"]: row for row in rows if "case" in row}
    if len(cases) != 2 or set(cases) != {"alias", "control"}:
        raise ValueError("expected exactly one alias and one control result")
    for name, expected in [("control", "\n"), ("alias", "\n\n")]:
        row = cases[name]
        if row["loaded_verified"] is not False:
            raise ValueError("execution output must not claim Loaded verification")
        if row["reached_interp_return"] is not True:
            raise ValueError(f"{name}: interp_run return was not reached")
        checks = row["initial_runtime_checks"]
        if any(check["passed"] is not True for check in checks["read_checks"]):
            raise ValueError(f"{name}: initial runtime read predicate failed")
        if not all(checks["good_state_read_checks"].values()):
            raise ValueError(f"{name}: GoodState executable register check failed")
        if checks["x13"] != 0 or row["return_a0"] != 0:
            raise ValueError(f"{name}: x13/return-a0 check failed")
        if checks["htif_payload_writes"] != 0 or not checks["htif_tohost_present"]:
            raise ValueError(f"{name}: initial HTIF boundary check failed")
        if (
            not checks["output_empty"]
            or checks["a1"] != 0x82000000
            or checks["a2"] != 2
        ):
            raise ValueError(
                f"{name}: initial output or argument boundary check failed"
            )
        if not checks["atexit_lock_present"] or not checks["buffer_present"]:
            raise ValueError(f"{name}: initial runtime byte presence failed")
        if row["fixed_image_changes"] != 0:
            raise ValueError(f"{name}: interpreter changed fixed image bytes")
        initial = row["initial_memory"]
        if initial["buffer"] != 0 or initial["buffer_next"] != 0:
            raise ValueError(f"{name}: buffer is not initially the empty C string")
        if initial["saved_main_ra"] != 0x80000038:
            raise ValueError(f"{name}: main saved return address differs")
        output = row["output"]
        if output != boot["boot_output"] + expected:
            raise ValueError(f"{name}: unexpected output {output!r}")
        println_events = [event for event in row["events"] if event["pc"] == 0x80002F7C]
        if len(println_events) != len(expected):
            raise ValueError(f"{name}: unexpected native println entry count")
        if row["final_memory"]["buffer"] != 10:
            raise ValueError(f"{name}: console byte did not become newline")
    return {
        "execution_check": "passed",
        "control_output_delta": "\n",
        "alias_output_delta": "\n\n",
        "loaded_verified": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--results", type=Path)
    args = parser.parse_args()
    receipt: dict[str, object] = check_inputs(args.repo)
    if args.results is not None:
        receipt.update(check_results(args.results))
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
