# Decode every corpus program's AST from the binary's OWN parser output (the traced entry memory),
# using the witness generator's decoder, and emit a Lean file that runs the cost evaluator on each.
import sys, re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import gen_boot_witness as g
import os
WORK = Path(os.environ.get("VSA_BOOT_WORK", "/Users/kirancodes/vsa-b3-work"))
names = sorted(p.stem.replace(".entry-trace", "") for p in (WORK / "traces").glob("*.entry-trace.tsv"))
out = ["import Vsa.While.CostEval", "open Vsa.While", ""]
rows = []; defs = []
skip_eval = {"adv_big_ok", "adv_oom_term", "adv_oom_div"}
for n in names:
    try:
        log, entry = g.read_trace(WORK / "traces" / f"{n}.entry-trace.tsv")
    except SystemExit as e:
        print("skip", n, e); continue
    mem = g.entry_memory(WORK, n, log)
    stmts, count = int(entry[4 + 10], 16), int(entry[4 + 11], 16)
    term = g.ast_term(mem, stmts, count)
    deep = "set_option maxRecDepth 200000 in\n" if n in ("adv_nest","adv_nest_odd") else ""
    defs.append(f"{deep}def p_{n} : Program := {term}\n")
    rows.append(f'("{n}", p_{n})')
    print(n, "entry step", entry[1], "stores", len(log), "count", count)
out += defs; out.append("def progs : List (String × Program) := [" + ", ".join(rows) + "]")
out += ["",
 "def statusStr : Status → String | .normal => \"normal\" | .brk => \"brk\" | .cont => \"cont\" | .ret _ => \"ret\"",
 "def showRes : Res SOut → String",
 "  | .done o => s!\"done\\tstatus={statusStr o.status}\\tcost={o.n}\\tout={repr o.st.out}\"",
 "  | .stuck => \"stuck\"",
 "  | .fuel => \"fuel\"",
 f"def skip : List String := {list(skip_eval)!r}".replace("'", '"'),
 "def main : IO Unit := do",
 "  let fuel := 100000",
 "  for (n, p) in progs do",
 "    if skip.contains n then IO.println s!\"{n}\\tSKIPPED\" else",
 "    IO.println s!\"{n}\\t{showRes (execSeqEval fuel initSt 0 0 p)}\"",
 "    (← IO.getStdout).flush",
]
Path(sys.argv[1]).write_text("\n".join(out) + "\n")
