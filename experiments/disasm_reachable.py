#!/usr/bin/env python3
"""Call-graph reachability from interp_run over experiments/disasm.txt.

PLAN-InterpSim scope: the proof covers code reachable from `interp_run`
(lexer/parser/libc startup are outside `Loaded`). This computes the
reachable function set (direct jal/j targets + tail jumps into function
entries), the unique instruction words within it (decode-table sizing),
and flags indirect-call sites (jalr) whose targets need manual closure
(native fn pointers, longjmp).
"""
import re, sys, collections, json

path = "experiments/disasm.txt"
func_re = re.compile(r"^([0-9a-f]{16}) <(.+)>:$")
inst_re = re.compile(r"^\s+([0-9a-f]+):\t([0-9a-f]{8})\s+\t(\S+)(?:\s+(.*))?$")
target_re = re.compile(r"([0-9a-f]+) <([^>+]+)(?:\+0x[0-9a-f]+)?>")

funcs = {}            # name -> dict(start, insts=[(addr, word, mnemonic, ops)])
addr2func = {}
cur = None
for line in open(path):
    m = func_re.match(line)
    if m:
        cur = m.group(2)
        funcs[cur] = {"start": int(m.group(1), 16), "insts": []}
        continue
    m = inst_re.match(line)
    if m and cur is not None:
        addr = int(m.group(1), 16)
        funcs[cur]["insts"].append((addr, m.group(2), m.group(3), m.group(4) or ""))
        addr2func[addr] = cur

# edges: jal/j/branches with symbol targets that are function entries
edges = collections.defaultdict(set)
indirect_sites = collections.defaultdict(list)   # func -> [(addr, mnemonic, ops)]
starts = {f["start"]: n for n, f in funcs.items()}
for name, f in funcs.items():
    for addr, word, mn, ops in f["insts"]:
        if mn in ("jal", "j", "beq", "bne", "blt", "bge", "bltu", "bgeu",
                  "beqz", "bnez", "blez", "bgez", "bltz", "bgtz", "ble", "bgt"):
            tm = target_re.search(ops)
            if tm:
                taddr = int(tm.group(1), 16)
                tname = starts.get(taddr)
                if tname and tname != name:
                    edges[name].add(tname)
        elif mn in ("jalr", "jr") and "ra" not in ops.split(",")[0:1]:
            indirect_sites[name].append((hex(addr), mn, ops))

root = "interp_run"
seen = set()
work = [root]
while work:
    n = work.pop()
    if n in seen or n not in funcs:
        continue
    seen.add(n)
    work.extend(edges[n] - seen)

# native fn pointers: the interpreter calls natives via jalr; close over
# the known native_* and runtime entry points that are address-taken.
address_taken = [n for n in funcs if n.startswith("native_")] + \
    [n for n in ("runtime_error", "longjmp", "setjmp") if n in funcs]
for n in address_taken:
    if n not in seen:
        work = [n]
        while work:
            k = work.pop()
            if k in seen or k not in funcs:
                continue
            seen.add(k)
            work.extend(edges[k] - seen)

words = collections.Counter()
n_insts = 0
for n in seen:
    for addr, word, mn, ops in funcs[n]["insts"]:
        words[word] += 1
        n_insts += 1

unreach = sorted(set(funcs) - seen)
print(f"reachable functions from {root} (+address-taken natives): {len(seen)} / {len(funcs)}")
print(f"reachable instructions: {n_insts} / {sum(len(f['insts']) for f in funcs.values())}")
print(f"unique words in reachable set: {len(words)}")
print(f"indirect-call sites inside reachable set: "
      f"{sum(len(v) for f, v in indirect_sites.items() if f in seen)}")
print("\nreachable function list (sorted):")
for n in sorted(seen, key=lambda n: funcs[n]["start"]):
    print(f"  {funcs[n]['start']:#x} {n} ({len(funcs[n]['insts'])})")
print("\nunreachable (outside proof scope), first 40:")
for n in unreach[:40]:
    print(f"  {n}")

json.dump({
    "reachable": sorted(seen),
    "unique_words": sorted(words),
    "indirect_sites": {f: v for f, v in indirect_sites.items() if f in seen},
}, open("experiments/disasm_reachable.json", "w"), indent=1)
print("\nwrote experiments/disasm_reachable.json")
