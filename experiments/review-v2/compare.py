# Compare the emulator's (output, exit) with the Lean semantics' evaluator result per corpus program.
import re, os, ast
S = os.environ.get("REVIEW_V2_WORK", "/tmp/review-v2-work")
emu = {}
for line in open(S + "/emu/results.txt"):
    m = re.match(r"(\S+) rc=(\d+)", line)
    if m: emu[m.group(1)] = int(m.group(2))
sem = {}
for line in open(S + "/corpus_all.out"):
    p = line.rstrip("\n").split("\t")
    sem[p[0]] = p[1:]
print(f"{'program':16s} {'emu rc':6s} {'emulator output':44s} | semantics")
agree = 0; rows = 0
for n in sorted(set(emu) | set(sem)):
    out = open(S + f"/emu/{n}.out", "rb").read().decode("utf-8", "replace") if os.path.exists(S + f"/emu/{n}.out") else None
    rc = emu.get(n)
    s = sem.get(n)
    verdict = "?"
    if s is None: verdict = "no semantics row"
    elif s[0] == "SKIPPED": verdict = "skipped (huge strings)"
    elif s[0] == "stuck": verdict = "OK: no BigStep; exit != 0" if rc not in (0, None) else f"MISMATCH rc={rc}"
    elif s[0] == "fuel": verdict = "fuel out"
    elif s[0] == "done":
        status = s[1].split("=")[1]; sout = ast.literal_eval(s[3][4:])
        if status == "normal":
            verdict = "OK: BigStep out == emulator, exit 0" if (rc == 0 and out == sout) else f"MISMATCH rc={rc} sem_out={sout!r}"
        else:
            verdict = f"OK: TopAbrupt ({status}); exit != 0" if rc not in (0, None) else f"MISMATCH rc={rc}"
    rows += 1; agree += verdict.startswith("OK")
    print(f"{n:16s} {str(rc):6s} {repr(out)[:44]:44s} | {verdict}")
print(f"{agree}/{rows} programs agree")
