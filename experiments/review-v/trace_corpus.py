#!/usr/bin/env python3
"""Build the review corpus and trace each build under the Lean emulator.

For every `wl/*.wl` (and the proof ELF itself, as `proof`): `patch_elf.py`
writes the build to `$REVIEW_V_WORK/elfs/<name>.elf`, and the emulator's
`--trace-all` rows go to `$REVIEW_V_WORK/traces/<name>.trace.tsv`, filtered as
they stream: every row up to `interp_run`'s entry (`0x800043ec`, what
`check_loaded.py` replays), then only the rows `check_loaded.py`'s P1 check
reads (stores into `stdout`'s `FILE`, and the entries of the newlib calls
whose preconditions take `StdioOK`).

Usage: python3 experiments/review-v/trace_corpus.py [--max-steps N] [-j J] [name ...]
The emulator is `riscv-lean/lean_emulator/.lake/build/bin/lean_riscv_emulator`,
or `$EMU`.
"""
import argparse, os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

S = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(S, "..", ".."))
WORK = os.environ.get("REVIEW_V_WORK", "/tmp/review-v-work")
EMU = os.environ.get("EMU", os.path.join(ROOT, "riscv-lean/lean_emulator/.lake/build/bin/lean_riscv_emulator"))
sys.path.insert(0, S)
import patch_elf

INTERP_RUN = "800043ec"
STDOUT_FILE = (0x8001bb20, 0x8001bb20 + 184)
# fputs, fputc, fwrite, fprintf, snprintf entries; exit's newlib interior.
CALLS = {"80006500", "800062e0", "80005260", "800061c0", "80005c44", "80004778"}


def trace(name, elf, max_steps):
    out = os.path.join(WORK, "traces", name + ".trace.tsv")
    stdout = os.path.join(WORK, "traces", name + ".out")
    with open(stdout, "wb") as fo, open(out, "w") as ft:
        p = subprocess.Popen([EMU, elf, "--trace-all", "--max-steps", str(max_steps)],
                             stdout=fo, stderr=subprocess.PIPE, text=True)
        entered = False
        for line in p.stderr:
            if not line.startswith("T\t"):
                ft.write(line)
                continue
            f = line.split("\t", 4)
            if not entered:
                ft.write(line)
                entered = f[2] == INTERP_RUN
                continue
            if f[2] in CALLS:
                ft.write(line)
                continue
            q = line.rstrip("\n").split("\t")
            if len(q) > 36 and q[35].startswith("S"):
                a = int(q[36], 16)
                if STDOUT_FILE[0] <= a + int(q[35][1:]) and a < STDOUT_FILE[1]:
                    ft.write(line)
        rc = p.wait()
    return name, rc


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-steps", type=int, default=5_000_000)
    ap.add_argument("-j", type=int, default=8)
    ap.add_argument("names", nargs="*")
    a = ap.parse_args()
    os.makedirs(os.path.join(WORK, "elfs"), exist_ok=True)
    os.makedirs(os.path.join(WORK, "traces"), exist_ok=True)
    jobs = []
    wl = sorted(f[:-3] for f in os.listdir(os.path.join(S, "wl")) if f.endswith(".wl"))
    names = a.names or wl + ["proof"]
    for n in names:
        elf = os.path.join(WORK, "elfs", n + ".elf")
        if n == "proof":
            subprocess.run(["cp", os.path.join(ROOT, "c/while-riscv-htif.elf"), elf], check=True)
        else:
            patch_elf.build(os.path.join(S, "wl", n + ".wl"), elf)
        jobs.append((n, elf))
    with ThreadPoolExecutor(a.j) as ex:
        for n, rc in ex.map(lambda j: trace(j[0], j[1], a.max_steps), jobs):
            print(n, "exit", rc, flush=True)


if __name__ == "__main__":
    main()
