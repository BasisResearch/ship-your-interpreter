#!/usr/bin/env python3
"""Check the fields of `Loaded interpRunLayout p c` (Vsa/Sim/LayoutInstance.lean,
Vsa/Sim/RuntimeOwnershipInitial.lean, Vsa/Sim/DlHeap.lean) against the REAL
configuration the Lean emulator reaches at interp_run's entry: memory =
ELF PT_LOAD bytes (exactly `initializeMemory`) + every store of the traced run
up to the entry step; registers = the entry row of the trace.

Two memory views: `sparse` (the actual Sail map: absent bytes are `none`) and
`dense` (absent RAM bytes read as `some 0`, the shape of the control snapshot).
"""
import sys, os, re, json
S = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(S, "..", ".."))
sys.path.insert(0, ROOT + "/scripts")
from difftest_lib import Image
# ELFs (`patch_elf.py`) and traces (`trace_corpus.py`) live outside the repository.
WORK = os.environ.get("REVIEW_V_WORK", "/tmp/review-v-work")
PROOF = ROOT + "/c/while-riscv-htif.elf"

# ---- constants from the Lean sources -------------------------------------
INTERP_RUN = 0x800043ec; SP_ENTRY = 0x87fffd00; GP_ENTRY = 0x8001b510
INTERP_OBJ = 0x87fffe10; MAIN_RA = 0x800045ec; MAIN_SAVED_RA = 0x87fffff8
IMPURE_S0 = 0x8001b970
STACK_LO, STACK_HI = 0x87800000, 0x88000000
TOHOST = 0x8001ad00
TEXT_BASE, TEXT_SIZE = 0x80000000, 101344
RODATA_BASE, RODATA_SIZE = 0x80018be0, 8464
SCRIPT_LEN = 453
ELF_WRITABLE = (0x8001ad00, 0x8001c168)
N = {"print": 0x80002ed4, "println": 0x80002f7c, "assert": 0x80002df4}
# ConsoleStream
C_IMPURE, C_REENT, C_STDOUT, C_BUF, C_SINIT, C_SWRITE = 0x8001b970, 0x8001b538, 0x8001bb20, 0x8001bb97, 0x80005d2c, 0x8000efd4
# ExitRuntimeData
E_ATEXIT, E_ATEXIT_LOCK, E_STDIO_H, E_STDIO_HV, E_GLUE, E_STDIN, E_STDERR, E_SCLOSE = 0x8001b9f8, 0x8001b978, 0x8001b9b0, 0x80005d18, 0x8001b520, 0x8001ba68, 0x8001bbd8, 0x8000f0c0
# DlHeap
AV = 0x8001ad10; BINBLOCKS = AV + 8; TOPADDR = AV + 16
SBRK_BASE, MAX_SBRKED, TOP_PAD, BRK, MALLINFO = 0x8001b960, 0x8001b9a0, 0x8001b9a8, 0x8001b990, 0x8001ba18
HEAP_START, HEAP_END = 0x8001c170, 0x87800000
NUM_BINS = 128
STATICS = [(0x800192c0, b"%lld\0\0\0\0"), (0x80019770, b".\0\0\0\0\0\0\0"),
           (0x8001a20c, bytes([0x0c, 0xdf, 0xfe, 0xff])), (0x8001a22c, bytes([0x38, 0xe4, 0xfe, 0xff])),
           (0x8001b880, (0x80012268).to_bytes(8, "little")), (0x8001b898, (0x80019770).to_bytes(8, "little")),
           (0x8001b8f8, b"\x01"), (0x8001b970, (0x8001b538).to_bytes(8, "little"))]

def bin_index(sz):
    q = sz // 512
    if q == 0: return sz // 8
    if q <= 4: return 56 + sz // 64
    if q <= 20: return 91 + sz // 512
    if q <= 84: return 110 + sz // 4096
    if q <= 340: return 119 + sz // 32768
    if q <= 1364: return 124 + sz // 262144
    return 126

class Mem:
    def __init__(self, d, dense):
        self.d = d; self.dense = dense
    def get(self, a):
        b = self.d.get(a)
        if b is None and self.dense and 0x80000000 <= a < 0x88000000: return 0
        return b
    def present(self, a): return a in self.d
    def readLE(self, a, n):
        v = 0
        for i in range(n):
            b = self.get(a + i)
            if b is None: return None
            v |= b << (8 * i)
        return v
    def r64(self, a): return self.readLE(a, 8)
    def r32(self, a): return self.readLE(a, 4)
    def cstr(self, a):
        """CString: bytes present, nonzero, < 128, NUL-terminated. Returns (str, ok, end)."""
        out = []; k = a
        while True:
            b = self.get(k)
            if b is None: return (bytes(out), False, k)
            if b == 0: return (bytes(out), True, k)
            if b >= 128: return (bytes(out), False, k)
            out.append(b); k += 1

def load(name):
    img = Image(WORK + f"/elfs/{name}.elf")
    d = {}
    for v, off, sz in img.segs:
        for i in range(sz): d[v + i] = img.raw[off + i]
    entry = None; nstores = 0
    with open(WORK + f"/traces/{name}.trace.tsv") as f:
        for line in f:
            if not line.startswith("T\t"): continue
            p = line.rstrip("\n").split("\t")
            pc = int(p[2], 16)
            if pc == INTERP_RUN:
                entry = p; break
            # p[4..34] = x1..x31; then optional mem op
            if len(p) > 35 and p[35].startswith("S"):
                wd = int(p[35][1:]); a = int(p[36], 16); post = int(p[38], 16)
                for i in range(wd): d[a + i] = (post >> (8 * i)) & 0xff
                nstores += 1
    assert entry is not None, "no entry row"
    regs = [0] + [int(x, 16) for x in entry[4:35]]
    outcount = int(entry[-3])
    return d, regs, int(entry[1]), nstores, outcount

def run(name, results):
    d, regs, step, nstores, outcount = load(name)
    R = {}
    def chk(field, ok, note=""):
        R.setdefault(field, []).append((bool(ok), note))
    for dense in (False, True):
        m = Mem(d, dense); tag = "dense" if dense else "sparse"
        def c(field, ok, note=""): chk(f"{field}[{tag}]", ok, note)
        # --- registers (view-independent, record once) ---
        if not dense:
            chk("pc", True, f"entry step {step}, {nstores} stores replayed")
            chk("interp_arg a0=inp", regs[10] == INTERP_OBJ, hex(regs[10]))
            chk("stmts_arg a1", True, hex(regs[11])); chk("count_arg a2", True, str(regs[12]))
            chk("repl_arg a3=0", regs[13] == 0, hex(regs[13]))
            chk("ra", regs[1] == MAIN_RA, hex(regs[1])); chk("sp", regs[2] == SP_ENTRY, hex(regs[2]))
            chk("gp", regs[3] == GP_ENTRY, hex(regs[3])); chk("s0_impure", regs[8] == IMPURE_S0, hex(regs[8]))
            chk("OutRepr output=''", outcount == 0, f"sailOutput chunks at entry: {outcount}")
            chk("stmts_align", regs[11] % 8 == 0); chk("stmts_ram", 0x80000000 <= regs[11] and regs[11] + 8 * regs[12] <= 2**32)
            chk("stmts_win", TOHOST + 16 <= regs[11]); chk("stmts_stack", regs[11] + 8 * regs[12] <= STACK_LO or SP_ENTRY <= regs[11])
            chk("stack_ok", STACK_LO + 176 + 1088 <= SP_ENTRY <= STACK_HI and SP_ENTRY % 16 == 0)
        stmts, count, inp = regs[11], regs[12], regs[10]
        c("main_ra", m.r64(MAIN_SAVED_RA) == 0x80000038, hex(m.r64(MAIN_SAVED_RA) or 0))
        # --- images ---
        img = Image(PROOF)
        bad = [a for a in range(TEXT_BASE, TEXT_BASE + TEXT_SIZE) if m.get(a) != img.byte(a)]
        c("text_image", not bad, f"{len(bad)} mismatching bytes")
        # P2: `FixedRodataLoaded` pins `.rodata` after the script and its NUL.
        bad = [a for a in range(RODATA_BASE + SCRIPT_LEN + 1, RODATA_BASE + RODATA_SIZE) if m.get(a) != img.byte(a)]
        inscript = [a for a in range(RODATA_BASE, RODATA_BASE + SCRIPT_LEN + 1) if m.get(a) != img.byte(a)]
        c("rodata_image", not bad, f"{len(bad)} mismatching pinned bytes [{RODATA_BASE+SCRIPT_LEN+1:#x},{RODATA_BASE+RODATA_SIZE:#x}); {len(inscript)} unpinned script bytes differ from the proof ELF")
        bad = [(a, i) for a, bs in STATICS for i in range(len(bs)) if m.get(a + i) != bs[i]]
        c("statics", not bad, f"{bad[:3]}")
        # --- console / exit runtime ---
        cs = {"impure": m.r64(C_IMPURE) == C_REENT, "stdout": m.r64(C_REENT + 16) == C_STDOUT,
              "sinit": m.r64(C_REENT + 72) == C_SINIT, "cursor": m.r64(C_STDOUT) == C_BUF,
              "readCount": m.r32(C_STDOUT + 8) == 0, "writeCount": m.r32(C_STDOUT + 12) == 0,
              # P1: `ConsoleBoot` (`ConsoleStreamAt false`): `_flags = 0x000a`, not yet oriented
              "flags": m.readLE(C_STDOUT + 16, 2) == 0x000a, "flag0": m.get(C_STDOUT + 16) == 0x0a,
              "flag1": m.get(C_STDOUT + 17) == 0x00, "fd": m.readLE(C_STDOUT + 18, 2) == 1,
              "base": m.r64(C_STDOUT + 24) == C_BUF, "bufSize": m.r32(C_STDOUT + 32) == 1,
              "lineBufSize": m.r32(C_STDOUT + 40) == 0, "cookie": m.r64(C_STDOUT + 48) == C_STDOUT,
              "writer": m.r64(C_STDOUT + 64) == C_SWRITE, "lock": m.r64(C_STDOUT + 160) == 0,
              "lockMode": m.r32(C_STDOUT + 176) == 0, "bufferByte": m.get(C_BUF) is not None}
        c("console (ConsoleBoot)", all(cs.values()), "failed: " + ",".join(k for k, v in cs.items() if not v))
        def idle(file, flags, fd):
            return {"flags": m.readLE(file + 16, 2) == flags, "fd": m.readLE(file + 18, 2) == fd,
                    "readCount": m.r32(file + 8) == 0, "savedReadCount": m.r32(file + 112) == 0,
                    "cookie": m.r64(file + 48) == file, "close": m.r64(file + 80) == E_SCLOSE,
                    "ungetc": m.r64(file + 88) == 0, "lineBuf": m.r64(file + 120) == 0,
                    "lock": m.r64(file + 160) == 0, "lockMode": m.r32(file + 176) == 0}
        ex = {"atexit": m.r64(E_ATEXIT) == 0, "atexitLock": m.r64(E_ATEXIT_LOCK) is not None,
              "stdioHandler": m.r64(E_STDIO_H) == E_STDIO_HV, "glueNext": m.r64(E_GLUE) == 0,
              "glueCount": m.r32(E_GLUE + 8) == 3, "glueFiles": m.r64(E_GLUE + 16) == E_STDIN,
              "stdoutClose": m.r64(C_STDOUT + 80) == E_SCLOSE, "stdoutUngetc": m.r64(C_STDOUT + 88) == 0,
              "stdoutLine": m.r64(C_STDOUT + 120) == 0}
        ex.update({"stdin." + k: v for k, v in idle(E_STDIN, 4, 0).items()})
        ex.update({"stderr." + k: v for k, v in idle(E_STDERR, 0x12, 2).items()})
        c("exit_runtime", all(ex.values()), "failed: " + ",".join(k for k, v in ex.items() if not v))
        c("BootHeapFacts.stderr", m.r64(C_REENT + 24) == E_STDERR, hex(m.r64(C_REENT + 24) or 0))
        # --- interp object ---
        genv = m.r64(inp)
        c("globals present", genv is not None and genv != 0, hex(genv or 0))
        c("call_depth=0", m.r32(inp + 8) == 0)
        c("interp_geom", inp % 8 == 0 and 0x80000000 <= inp and inp + 384 <= 2**32 and TOHOST + 16 <= inp)
        c("setjmp_geom (WinRAM inp+16)", (inp + 16) % 8 == 0 and inp + 16 + 112 <= 2**32)
        # --- stack bytes present ---
        present = sum(1 for a in range(STACK_LO, STACK_HI) if m.present(a)) if not dense else None
        if not dense:
            c("stack_bytes", present == STACK_HI - STACK_LO, f"{present} of {STACK_HI-STACK_LO} stack bytes present in the map")
            bss = sum(1 for a in range(0x8001b990, 0x8001c168) if m.present(a))
            c("bss present", bss == 0x8001c168 - 0x8001b990, f"{bss} of {0x8001c168-0x8001b990} .bss bytes present")
        else:
            c("stack_bytes", True, "dense view: all present by construction")
        # --- the store: global frame ---
        if genv:
            cnt, cap, pn, pv, par = m.r32(genv), m.r32(genv + 4), m.r64(genv + 8), m.r64(genv + 16), m.r64(genv + 24)
            names = []; vals = []
            okstore = cnt == 3 and par == 0 and pn and pv
            for i in range(cnt or 0):
                q = m.r64(pn + 8 * i); s, ok, _ = m.cstr(q) if q else (b"", False, 0)
                names.append((s.decode("latin-1"), ok, q))
                kind = m.r32(pv + 24 * i); p1 = m.r64(pv + 24 * i + 8); p2 = m.r64(pv + 24 * i + 16)
                vals.append((kind, p1, p2))
            exp = [("print", N["print"]), ("println", N["println"]), ("assert", N["assert"])]
            okstore = okstore and [n[0] for n in names] == [e[0] for e in exp] and all(n[1] for n in names)
            okstore = okstore and all(v[0] == 5 and v[2] == e[1] and m.cstr(v[1])[0].decode("latin-1") == e[0] for v, e in zip(vals, exp))
            c("store (FrameRepr initSt, natives)", okstore, f"count={cnt} cap={cap} pn={pn:#x} pv={pv:#x} parent={par} names={[(n[0],n[1]) for n in names]}")
            c("cap_canon (cap=8)", cap == 8, f"cap={cap}")
            c("arrays aligned", pn % 8 == 0 and pv % 8 == 0)
            # frame arrays as AstMutableByte regions
            frame_regions = [(genv, 32), (pn, 8 * (cap or 0)), (pv, 24 * (cap or 0))]
            key_exts = [(n[2], len(n[0]) + 1) for n in names]
        else:
            frame_regions = []; key_exts = []
        # --- the AST: decode per ExprRepr/StmtRepr ---
        ast_bytes = set(); shared = set(); errs = []
        def touch(a, n):
            for i in range(n): ast_bytes.add(a + i)
        def cstring(a, what):
            s, ok, end = m.cstr(a)
            if not ok: errs.append(f"{what}: bad CString at {a:#x} ({s[:20]!r})")
            for k in range(a, end + 1): shared.add(k); ast_bytes.add(k)
            return s.decode("latin-1")
        BIN = {11: "+", 12: "-", 13: "*", 14: "/", 15: "%", 17: "!=", 19: "==", 20: "<", 21: "<=", 22: ">", 23: ">="}
        def expr(a, depth=0):
            if depth > 2000: errs.append("expr too deep"); return "?"
            k = m.r32(a); touch(a, 8)
            if k is None: errs.append(f"expr kind absent at {a:#x}"); return "?"
            if k == 0: touch(a + 8, 8); v = m.r64(a + 8); return str(v - 2**64 if v >= 2**63 else v)
            if k == 1: touch(a + 8, 8); return repr(cstring(m.r64(a + 8), "str"))
            if k == 2: touch(a + 8, 4); return "true" if m.r32(a + 8) else "false"
            if k == 3: return "null"
            if k == 4: touch(a + 8, 8); return cstring(m.r64(a + 8), "var")
            if k == 5: touch(a + 8, 16); return f"({cstring(m.r64(a+8),'assign')} = {expr(m.r64(a+16), depth+1)})"
            if k in (6, 7):
                touch(a + 8, 24); op = m.r32(a + 8)
                if k == 6 and op not in BIN: errs.append(f"bad binop tok {op} at {a:#x}")
                if k == 7 and op not in (24, 25): errs.append(f"bad logop tok {op} at {a:#x}")
                o = BIN.get(op, {24: "&&", 25: "||"}.get(op, "?"))
                return f"({expr(m.r64(a+16), depth+1)} {o} {expr(m.r64(a+24), depth+1)})"
            if k == 8:
                touch(a + 8, 16); op = m.r32(a + 8)
                if op not in (12, 16): errs.append(f"bad unop tok {op} at {a:#x}")
                return f"({'-' if op == 12 else '!'}{expr(m.r64(a+16), depth+1)})"
            if k == 9:
                touch(a + 8, 20); f = m.r64(a + 8); args = m.r64(a + 16); argc = m.r32(a + 24)
                if argc >= 2**31: errs.append("argc >= 2^31")
                touch(args, 8 * argc)
                return f"{expr(f, depth+1)}({', '.join(expr(m.r64(args+8*i), depth+1) for i in range(argc))})"
            if k == 10:
                touch(a + 8, 32); nm = m.r64(a + 8); params = m.r64(a + 16); pc_ = m.r32(a + 24); body = m.r64(a + 32)
                name = cstring(nm, "fnname") if nm else ""
                touch(params, 8 * pc_)
                ps = [cstring(m.r64(params + 8 * i), "param") for i in range(pc_)]
                b = stmt(body, depth + 1)
                return f"fn {name}({', '.join(ps)}) {b}"
            errs.append(f"bad expr kind {k} at {a:#x}"); return "?"
        def stmt(a, depth=0):
            if depth > 2000: errs.append("stmt too deep"); return "?"
            k = m.r32(a); touch(a, 8)
            if k is None: errs.append(f"stmt kind absent at {a:#x}"); return "?"
            if k == 0: touch(a + 8, 8); return expr(m.r64(a + 8), depth + 1) + ";"
            if k == 1:
                touch(a + 8, 16); x = cstring(m.r64(a + 8), "vardecl"); q = m.r64(a + 16)
                return f"var {x}" + (f" = {expr(q, depth+1)};" if q else ";")
            if k == 2:
                touch(a + 8, 12); st = m.r64(a + 8); n = m.r32(a + 16); touch(st, 8 * n)
                return "{" + " ".join(stmt(m.r64(st + 8 * i), depth + 1) for i in range(n)) + "}"
            if k == 3:
                touch(a + 8, 24); cnd = expr(m.r64(a + 8), depth + 1); t = stmt(m.r64(a + 16), depth + 1); e = m.r64(a + 24)
                return f"if ({cnd}) {t}" + (f" else {stmt(e, depth+1)}" if e else "")
            if k == 4: touch(a + 8, 16); return f"while ({expr(m.r64(a+8), depth+1)}) {stmt(m.r64(a+16), depth+1)}"
            if k == 5:
                touch(a + 8, 32); i_, cn, sp_, b = m.r64(a + 8), m.r64(a + 16), m.r64(a + 24), m.r64(a + 32)
                return f"for ({stmt(i_, depth+1) if i_ else ';'} {expr(cn, depth+1) if cn else ''}; {expr(sp_, depth+1) if sp_ else ''}) {stmt(b, depth+1)}"
            if k == 6: touch(a + 8, 8); p = m.r64(a + 8); return "return" + (f" {expr(p, depth+1)};" if p else ";")
            if k == 7: return "break;"
            if k == 8: return "continue;"
            errs.append(f"bad stmt kind {k} at {a:#x}"); return "?"
        touch(stmts, 8 * count)
        src = " ".join(stmt(m.r64(stmts + 8 * i)) for i in range(count))
        c("ProgramRepr decodes", not errs, f"{len(errs)} errors: {errs[:3]}")
        R["_ast"] = src
        # shared/AST geometry
        allast = ast_bytes | shared
        def inreg(k, r): return r[0] <= k < r[0] + r[1]
        badw = [k for k in allast if ELF_WRITABLE[0] <= k < ELF_WRITABLE[1] or STACK_LO <= k < STACK_HI]
        c("ast_owned (AST off writable ELF/stack)", not badw, f"{len(badw)} bytes")
        badf = [k for k in allast if any(inreg(k, r) for r in frame_regions)]
        c("AST off global-frame header/arrays", not badf, f"{len(badf)} bytes")
        badg = [k for k in shared if not (0x8001acf0 <= k and k + 8 <= 2**32 and TOHOST + 16 <= k and not (STACK_LO <= k < STACK_HI))]
        c("SharedGeom", not badg, f"{len(badg)} shared bytes violate")
        lo, hi = (min(allast), max(allast)) if allast else (0, 0)
        c("AST location", True, f"AST bytes {len(allast)} in [{lo:#x}, {hi:#x}]; heap=[{HEAP_START:#x},{HEAP_END:#x}) rodata-literals={sum(1 for k in allast if RODATA_BASE<=k<RODATA_BASE+RODATA_SIZE)}")
        # --- dlmalloc HeapAt ---
        top = m.r64(TOPADDR); brkv = m.r64(BRK)
        H = {"sbrk_base": m.r64(SBRK_BASE) == HEAP_START, "brk_le": brkv is not None and brkv <= HEAP_END,
             "top_le": top is not None and brkv is not None and top <= brkv,
             "top_size%16": top is not None and brkv is not None and (brkv - top) % 16 == 0,
             "top_header": top is not None and m.r64(top + 8) == (brkv - top + 1),
             "top_pad": m.r64(TOP_PAD) == 0, "max_sbrked present": m.r64(MAX_SBRKED) is not None,
             "mallinfo present": m.r64(MALLINFO) is not None,
             "first_prev": m.r64(HEAP_START + 8) is not None and m.r64(HEAP_START + 8) % 2 == 1}
        H["top_room"] = top is not None and brkv is not None and top + 16 <= brkv
        H["brk_page"] = brkv is not None and brkv % 4096 == 0
        bb = m.r64(BINBLOCKS); H["binblocks<2^32"] = bb is not None and bb < 2**32
        # chunk walk
        chunks = []; p = HEAP_START; walk_ok = True
        while top is not None and p < top:
            h = m.r64(p + 8)
            if h is None or h % 4 >= 2: walk_ok = False; break
            sz = h // 4 * 4
            if sz < 32 or sz % 16: walk_ok = False; break
            h2 = m.r64(p + sz + 8)
            if h2 is None: walk_ok = False; break
            chunks.append((p, sz, h2 % 2 == 1)); p += sz
        H["walk"] = walk_ok and p == top
        H["coalesced"] = all(chunks[i][2] or chunks[i + 1][2] for i in range(len(chunks) - 1))
        H["footer"] = all(m.r64(a + sz) == sz for a, sz, iu in chunks if not iu)
        # bins
        bins = {}; binok = True
        for i in range(1, NUM_BINS):
            b = AV + 16 * i; first = m.r64(b + 16); qs = []; q = first; prev = b; steps = 0
            while q is not None and q != b and steps < 10000:
                if m.r64(q + 24) != prev: binok = False
                qs.append(q); prev = q; q = m.r64(q + 16); steps += 1
            if q is None or m.r64(b + 24) != prev: binok = False
            bins[i] = qs
        H["bins_list"] = binok
        free_addrs = {a for a, sz, iu in chunks if not iu}
        H["bin_free"] = all(q in free_addrs and (i <= 1 or bin_index(next(sz for a, sz, iu in chunks if a == q)) == i) for i, qs in bins.items() for q in qs)
        H["free_binned"] = all(sum(1 for i, qs in bins.items() if a in qs) == 1 for a in free_addrs)
        H["remainder<=1"] = len(bins[1]) <= 1
        H["binblocks bits"] = bb is not None and all((bb >> (i // 4)) & 1 for i, qs in bins.items() if i > 1 and qs)
        c("HeapAt", all(H.values()), "failed: " + ",".join(k for k, v in H.items() if not v) + f"; top={top and hex(top)} brk={brkv and hex(brkv)} chunks={len(chunks)} free={len(free_addrs)} nonempty bins={[(i,len(q)) for i,q in bins.items() if q]}")
        # AST inside in-use chunks (Reserved.live / HeapAt.live for shared bytes in the arena)
        def chunk_of(k):
            for a, sz, iu in chunks:
                if a + 16 <= k < a + sz + 8: return (a, sz, iu)
            return None
        badc = [k for k in allast if HEAP_START <= k < HEAP_END and (chunk_of(k) is None or not chunk_of(k)[2])]
        c("shared heap bytes in in-use payloads", not badc, f"{len(badc)} AST bytes in free chunks/headers/top")
        # frame blocks: whole in-use payloads, distinct, unshared
        if genv:
            blocks = [(genv, 32), (pn, 8 * cap), (pv, 24 * cap)]
            ok = True; notes = []
            for (b0, need) in blocks:
                ch = chunk_of(b0)
                if ch is None or not ch[2] or ch[0] + 16 != b0: ok = False; notes.append(f"{b0:#x} not a payload start")
                elif ch[1] - 8 < need: ok = False; notes.append(f"{b0:#x} too small")
                if any(b0 <= k < b0 + (ch[1] - 8 if ch else 0) for k in shared): ok = False; notes.append(f"{b0:#x} holds shared bytes")
            c("BootFrameChunks (whole in-use payloads, unshared)", ok and len(set(b for b, _ in blocks)) == 3, ";".join(notes))
            # binding keys: allocations of exactly len+1 inside in-use chunks
            okk = all(chunk_of(q) and chunk_of(q)[2] and chunk_of(q)[0] + 16 == q for q, n in key_exts)
            c("binding keys are whole payloads", okk, f"{[(hex(q), n) for q, n in key_exts]}")
    orient_check(name, d, chk)
    results[name] = R
    return R


# P1: `ORIENT`'s `sh _flags` sites (`VsaIris/Vsa/StdioOrient.lean`).
ORIENT_SH = {0x80005108: "_fwrite_r", 0x80006430: "_fputs_r", 0x8000a914: "_vfprintf_r", 0x8000f1c4: "__swbuf_r"}
CALLS = {0x80006500: "fputs", 0x800062e0: "fputc", 0x80005260: "fwrite", 0x800061c0: "fprintf",
         0x80005c44: "snprintf", 0x80004778: "exitHandlers"}
EXIT_HANDLERS = 0x80004778


def orient_check(name, d, chk):
    """After entry: every store to `stdout->_flags` before `exit`'s newlib
    interior is an `ORIENT` `sh` of `0x200a`, the first one from `0x000a`;
    at every newlib call the interpreter's `StdioOK` console fields hold at
    orientation `0x000a` or `0x200a` (`ConsoleStreamAt o`)."""
    m = Mem(dict(d), False)
    entered = False; calls = {}; bad_calls = []; stores = []; bad_stores = []; exited = False
    with open(WORK + f"/traces/{name}.trace.tsv") as f:
        for line in f:
            if not line.startswith("T\t"): continue
            p = line.rstrip("\n").split("\t")
            pc = int(p[2], 16)
            if not entered:
                entered = pc == INTERP_RUN
                continue
            if pc in CALLS and not exited:
                fl = m.readLE(C_STDOUT + 16, 2)
                ok = (fl in (0x000a, 0x200a) and m.r64(C_STDOUT) == C_BUF and m.r32(C_STDOUT + 12) == 0
                      and m.r64(C_STDOUT + 24) == C_BUF and m.r32(C_STDOUT + 176) == 0)
                key = (CALLS[pc], fl)
                calls[key] = calls.get(key, 0) + 1
                if not ok: bad_calls.append((CALLS[pc], p[1], hex(fl or 0)))
                if pc == EXIT_HANDLERS: exited = True
            if len(p) > 35 and p[35].startswith("S"):
                wd = int(p[35][1:]); a = int(p[36], 16); post = int(p[38], 16)
                before = m.readLE(C_STDOUT + 16, 2)
                for i in range(wd): m.d[a + i] = (post >> (8 * i)) & 0xff
                if a < C_STDOUT + 18 and C_STDOUT + 16 < a + wd and not exited:
                    after = m.readLE(C_STDOUT + 16, 2)
                    stores.append((p[1], ORIENT_SH.get(pc, hex(pc)), hex(before), hex(after)))
                    # A store that rewrites the same value (`__swrite`'s `_flags &= ~__SOFF`,
                    # `0x8000f00c`) is harmless; one that changes it must be `ORIENT`'s.
                    if before != after and (pc not in ORIENT_SH or after != 0x200a):
                        bad_stores.append(stores[-1])
    orients = [s for s in stores if s[2] != s[3]]
    chk("P1 flag stores are ORIENT (0x000a -> 0x200a), before exit", entered and not bad_stores and len(orients) <= 1
        and all(s[2] == "0xa" for s in orients),
        f"{len(stores)} stores ({len(stores) - len(orients)} rewrite the same value); changes: {orients}; bad: {bad_stores[:3]}")
    chk("P1 StdioOK console at every newlib call (flags 0x000a or 0x200a)", not bad_calls,
        "calls (name, flags): " + ", ".join(f"{k[0]}@{k[1]:#06x}x{v}" for k, v in sorted(calls.items(), key=str))
        + (f"; bad: {bad_calls[:3]}" if bad_calls else ""))

if __name__ == "__main__":
    names = sys.argv[1:] or sorted(f[:-len(".trace.tsv")] for f in os.listdir(WORK + "/traces") if f.endswith(".trace.tsv"))
    results = {}
    for n in names:
        try:
            R = run(n, results)
        except Exception as e:
            print(f"== {n}: EXCEPTION {e!r}"); continue
        print(f"== {n}")
        for k, v in R.items():
            if k == "_ast": continue
            for ok, note in v:
                print(f"  {'PASS' if ok else 'FAIL'} {k}: {note}")
        print(f"  AST: {R['_ast'][:200]}")
    json.dump(results, open(WORK + "/check_loaded.json", "w"), indent=1, default=str)
