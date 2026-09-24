#!/usr/bin/env python3
# Usage: python3 scripts/emit_derive_case.py scripts/malloc_fast_segs.json  (segments of MallocFastSegs.lean)
"""Emit a #derive_case chain from experiments/disasm.txt.
Spec: list of blocks; each block = (start, end_exclusive_body, term) where term is
None | ('br', taken:bool) | 'j' | 'jr' located at end_exclusive_body."""
import re, sys
W={}
for l in open('experiments/disasm.txt'):
    m=re.match(r'^\s+([0-9a-f]+):\t([0-9a-f]{8})\s+\t(\S+)(?:\s+(.*))?$',l)
    if m: W[int(m.group(1),16)]=int(m.group(2),16)
BOP={0:'BEQ',1:'BNE',4:'BLT',5:'BGE',6:'BLTU',7:'BGEU'}
def sx(v,b): return v
def term(pc,kind,taken=None):
    w=W[pc]; b=[(w>>(8*i))&0xff for i in range(4)]
    rs1=(w>>15)&31; rs2=(w>>20)&31
    bs=', '.join(f'0x{x:02x}#8' for x in b)
    if kind=='br':
        f3=(w>>12)&7
        imm=((w>>31)&1)<<12 | ((w>>7)&1)<<11 | ((w>>25)&0x3f)<<5 | ((w>>8)&0xf)<<1
        return f"⟨0x{pc:x}#64, 0x{w:08x}#32, {bs},\n      .br bop.{BOP[f3]} {'true' if taken else 'false'}, {rs1}, {rs2}, 0x{imm:03x}#13, 0#21, 0#12⟩"
    if kind=='j':
        imm=((w>>31)&1)<<20 | ((w>>12)&0xff)<<12 | ((w>>20)&1)<<11 | ((w>>21)&0x3ff)<<1
        return f"⟨0x{pc:x}#64, 0x{w:08x}#32, {bs},\n      .j, 0, 0, 0#13, 0x{imm:06x}#21, 0#12⟩"
    if kind=='jr':
        imm=(w>>20)&0xfff
        return f"⟨0x{pc:x}#64, 0x{w:08x}#32, {bs},\n      .jr, {rs1}, 0, 0#13, 0#21, 0x{imm:03x}#12⟩"
def emit(name, blocks):
    out=[f"#derive_case {name} chain"]
    parts=[]
    for (s,e,t) in blocks:
        body=[f"(0x{a:x}#64, 0x{W[a]:08x}#32)" for a in range(s,e,4)]
        txt="  ["+",\n   ".join(body)+"]"
        if t is not None:
            if isinstance(t,tuple): txt+=f"\n  terminator {term(e,'br',t[1])}"
            else: txt+=f"\n  terminator {term(e,t)}"
        parts.append(txt)
    out.append(" ;;\n".join(parts))
    return "\n".join(out)+"\n"
if __name__=='__main__':
    import json
    spec=json.load(open(sys.argv[1]))
    for name,blocks in spec.items():
        bl=[(int(s,16),int(e,16),(tuple(t) if isinstance(t,list) else t)) for s,e,t in blocks]
        print(emit(name,bl))
