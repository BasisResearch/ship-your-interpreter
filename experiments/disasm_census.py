#!/usr/bin/env python3
"""Census of experiments/disasm.txt for the M2 decode table (PLAN-InterpSim §Tooling).

Emits: unique instruction words with counts and mnemonics, per-function
address/word extents, and totals — the sizing input for the decode-table
generator (one `ext_decode w = ast` lemma per unique word).
"""
import re, sys, collections, json

path = sys.argv[1] if len(sys.argv) > 1 else "experiments/disasm.txt"
func_re = re.compile(r"^([0-9a-f]{16}) <(.+)>:$")
inst_re = re.compile(r"^\s+([0-9a-f]+):\t([0-9a-f]{8})\s+\t(\S+)(?:\s+(.*))?$")

funcs = {}          # name -> (start, [addrs])
words = collections.Counter()
word_mnemonic = {}
mnemonics = collections.Counter()
cur = None
for line in open(path):
    m = func_re.match(line)
    if m:
        cur = m.group(2)
        funcs[cur] = [int(m.group(1), 16), 0]
        continue
    m = inst_re.match(line)
    if m and cur is not None:
        w = m.group(2)
        words[w] += 1
        word_mnemonic[w] = m.group(3)
        mnemonics[m.group(3)] += 1
        funcs[cur][1] += 1

print(f"functions: {len(funcs)}")
print(f"total instructions: {sum(words.values())}")
print(f"unique words: {len(words)}")
print(f"unique mnemonics: {len(mnemonics)}")
print("\ntop 20 mnemonics:")
for mn, c in mnemonics.most_common(20):
    print(f"  {mn:12s} {c}")
print("\ntop 20 most-repeated words:")
for w, c in words.most_common(20):
    print(f"  0x{w} {word_mnemonic[w]:12s} ×{c}")

with open("experiments/disasm_census.json", "w") as f:
    json.dump({
        "unique_words": {w: {"count": c, "mnemonic": word_mnemonic[w]}
                          for w, c in words.items()},
        "functions": {n: {"start": hex(s), "n_insts": k}
                      for n, (s, k) in funcs.items()},
    }, f, indent=1)
print("\nwrote experiments/disasm_census.json")
