#!/usr/bin/env python3
"""Regenerate scripts/decode_index.tsv: instruction word -> DecodeTable module.

Scans Vsa/Sim/DecodeTable/Batch*.lean for `theorem decode_<8 hex digits>` and
emits one line per decode lemma:

    <word-hex8>\t<module>

e.g. `00008067\tVsa.Sim.DecodeTable.Batch01Part04`.

Spec/site files must import the Batch part that defines each decode lemma they
use *directly* (aggregate BatchNN.lean files exist but pull in far more than
needed); this index makes finding the right part mechanical.

Usage:  python3 scripts/gen_decode_index.py
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DECODE_DIR = ROOT / "Vsa" / "Sim" / "DecodeTable"
OUT = ROOT / "scripts" / "decode_index.tsv"

THEOREM_RE = re.compile(r"^theorem decode_([0-9a-f]{8})\b")


def main() -> int:
    if not DECODE_DIR.is_dir():
        print(f"error: {DECODE_DIR} not found", file=sys.stderr)
        return 1

    index: dict[str, str] = {}
    dupes: list[tuple[str, str, str]] = []

    for path in sorted(DECODE_DIR.glob("Batch*.lean")):
        module = f"Vsa.Sim.DecodeTable.{path.stem}"
        for line in path.read_text().splitlines():
            m = THEOREM_RE.match(line)
            if not m:
                continue
            word = m.group(1)
            if word in index and index[word] != module:
                dupes.append((word, index[word], module))
                continue
            index[word] = module

    if dupes:
        for word, first, second in dupes[:20]:
            print(f"warning: decode_{word} in both {first} and {second}; "
                  f"keeping {first}", file=sys.stderr)

    lines = [f"{word}\t{module}" for word, module in sorted(index.items())]
    OUT.write_text("\n".join(lines) + "\n")
    print(f"wrote {OUT} ({len(lines)} entries)")

    # Sanity anchors (known-good pairs).
    for word, mod in (("00008067", "Vsa.Sim.DecodeTable.Batch01Part04"),
                      ("fc010113", "Vsa.Sim.DecodeTable.Batch16Part01")):
        got = index.get(word)
        if got != mod:
            print(f"error: sanity check failed: {word} -> {got}, expected {mod}",
                  file=sys.stderr)
            return 1
    if len(lines) < 1000:
        print(f"error: sanity check failed: only {len(lines)} entries "
              f"(expected thousands)", file=sys.stderr)
        return 1
    print("sanity checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
