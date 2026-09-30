#!/usr/bin/env python3
"""Rewrite the ranges of every `#step_table` from a usage report.

    lake env lean scripts/step_usage.lean > usage.txt && python3 scripts/step_only.py usage.txt

Each table module keeps the addresses at which some lemma it declares is used; runs of
used addresses closer than GAP bytes are merged into one range.
"""
import collections, pathlib, re, sys

GAP = 16
used = collections.defaultdict(set)
for line in open(sys.argv[1]):
    m = re.fullmatch(r"(\S+)\.(\w+) \S+\.[A-Za-z]+_([0-9a-f]{8}) used\n", line)
    if m and m.group(1).endswith("StepTables"):
        used[m.group(2)].add(int(m.group(3), 16))

root = pathlib.Path(__file__).resolve().parent.parent / "VsaIris/Vsa/StepTables"
for path in sorted(root.glob("*.lean")):
    runs = []
    for pc in sorted(used[path.stem]):
        if runs and pc - runs[-1][1] <= GAP:
            runs[-1][1] = pc + 4
        else:
            runs.append([pc, pc + 4])
    pairs = [f"0x{lo:08x} 0x{hi:08x}" for lo, hi in runs]
    rows = ["  " + "  ".join(pairs[i:i + 4]) for i in range(0, len(pairs), 4)]
    src = path.read_text()
    new = re.sub(r"#step_table (\w+)[^\n]*\n(?:  [^\n]*\n)*",
                 lambda m: f"#step_table {m.group(1)}\n" + "\n".join(rows) + "\n", src)
    path.write_text(new)
    print(f"{path.stem}: {len(used[path.stem])} addresses, {len(runs)} ranges")
