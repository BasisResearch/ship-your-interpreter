#!/usr/bin/env python3
"""Generate the allocator's code bytes and its per-instruction step table.

Outputs (do not hand-edit):

* `VsaIris/Vsa/AllocCode.lean`: `allocText`, the code bytes of every
  allocator function (`FUNCS`) plus the `_impure_ptr` word, as a balanced
  append tree of 16-byte chunks. It also emits `alloc_at_<pc>` (the four code
  bytes at `pc`, the shape `chain_facts` consumes), `alloc_code_<pc>` (a jal
  site's code footprint lies in `allocText`) and `alloc_impure` (the
  `_impure_ptr` word).
* `VsaIris/Vsa/AllocSteps/Part<k>.lean`: per instruction, one `#derive_case`
  segment (two for a branch: taken `axT_`, fall-through `axF_`) and one step
  lemma `VsaIris.Sym.st_<pc>` over `AW` (`AllocRun.lean`). Its continuation is
  the successor's symbolic state. Each `jal` site also gets `JalExec`
  (`jalx_<pc>`).

Kinds: ALU, loads, stores, branches, `j`, `ret`, `jal`. `sltu`/`sltiu` (outside
`MKind`) get no step lemma. They are listed in the report and at the file
head.

Usage: python3 scripts/gen_alloc_steps.py [--target alloc|env]

`--target env` (lane H1) emits the same two outputs for `env.c`'s helpers
(`env_new`, `env_define`, `env_get`, `env_set`): `VsaIris/Interp/EnvCode.lean`
(`envText`, `env_at_<pc>`, `env_code_<pc>`, `env_impure`) and
`VsaIris/Interp/EnvSteps/Part<k>.lean` (`st_<pc>` over `EW`, `EnvRun.lean`).
The allocator is the default target.
"""
import re, pathlib, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
TARGETS = {
    'alloc': dict(
        P='alloc', RUN='AW',
        FUNCS=['malloc', 'free', 'realloc', '_malloc_r', '_free_r', '_realloc_r', '_malloc_trim_r',
               '_sbrk_r', '_sbrk', '__malloc_lock', '__malloc_unlock',
               '__retarget_lock_acquire_recursive', '__retarget_lock_release_recursive',
               '__errno', 'memcpy', 'memmove'],
        CODE_OUT='VsaIris/Vsa/AllocCode.lean', STEPS_DIR='VsaIris/Vsa/AllocSteps',
        STEPS_MOD='VsaIris.Vsa.AllocSteps', RUN_MOD='VsaIris.Vsa.AllocRun',
        CODE_DOC=['/-! The allocator\'s code bytes (`malloc`, `free`, `realloc`, `_malloc_r`, `_free_r`,',
                  '`_realloc_r`, `_malloc_trim_r`, `_sbrk_r`, `_sbrk`, the lock hooks, `__errno`, `memcpy`,',
                  '`memmove`) and the `_impure_ptr` word, as a balanced append tree of 16-byte chunks. -/'],
        WHO='The allocator\'s'),
    'env': dict(
        P='env', RUN='EW',
        FUNCS=['env_new', 'env_define', 'env_get', 'env_set'],
        CODE_OUT='VsaIris/Interp/EnvCode.lean', STEPS_DIR='VsaIris/Interp/EnvSteps',
        STEPS_MOD='VsaIris.Interp.EnvSteps', RUN_MOD='VsaIris.Interp.EnvRun',
        CODE_DOC=['/-! The code bytes of `env.c`\'s helpers (`env_new`, `env_define`, `env_get`,',
                  '`env_set`) and the `_impure_ptr` word, as a balanced append tree of 16-byte chunks. -/'],
        WHO='`env.c`\'s'),
}
TGT = 'alloc'
if '--target' in sys.argv:
    TGT = sys.argv[sys.argv.index('--target') + 1]
CFG = TARGETS[TGT]
P, RUN, FUNCS = CFG['P'], CFG['RUN'], CFG['FUNCS']
IMPURE = (0x8001b970, [0x38, 0xb5, 0x01, 0x80, 0, 0, 0, 0])
GPV = 0x8001b510
PER_FILE = 120

# ---------------------------------------------------------------- disassembly
W, FN, MN = {}, {}, {}
fn = None
for l in open(ROOT / 'experiments/disasm.txt'):
    m = re.match(r'^([0-9a-f]+) <(.*)>:$', l)
    if m:
        fn = m.group(2)
        continue
    m = re.match(r'^\s+([0-9a-f]+):\t([0-9a-f]{8})\s+\t(\S+)', l)
    if m and fn in FUNCS:
        pc = int(m.group(1), 16)
        W[pc] = int(m.group(2), 16)
        FN[pc] = fn
        MN[pc] = m.group(3)
PCS = sorted(W)

DEC = {}
for l in open(ROOT / 'scripts/decode_index.tsv'):
    w, mod = l.split()
    DEC[int(w, 16)] = mod

M64 = (1 << 64) - 1


def sext(v, b):
    return v - (1 << b) if v >> (b - 1) & 1 else v


def lit64(v):
    return f'0x{v & M64:x}#64'


def fields(w):
    return dict(op=w & 0x7f, rd=(w >> 7) & 31, f3=(w >> 12) & 7, rs1=(w >> 15) & 31,
                rs2=(w >> 20) & 31, f7=w >> 25,
                immI=sext(w >> 20, 12),
                immS=sext(((w >> 25) << 5) | ((w >> 7) & 31), 12),
                immB=sext(((w >> 31) & 1) << 12 | ((w >> 7) & 1) << 11 | ((w >> 25) & 0x3f) << 5
                          | ((w >> 8) & 0xf) << 1, 13),
                immJ=sext(((w >> 31) & 1) << 20 | ((w >> 12) & 0xff) << 12 | ((w >> 20) & 1) << 11
                          | ((w >> 21) & 0x3ff) << 1, 21),
                immU=sext(w & 0xfffff000, 32))


def src(r):
    if r == 0:
        return '(0#64)'
    if r == 3:
        return f'({lit64(GPV)})'
    return f'(R {r})'


def i12(v):
    return f'(0x{v & 0xfff:03x}#12)'


def sx12(v):
    return f'sign_extend (m := 64) {i12(v)}'


def classify(pc):
    """(class, info) for the instruction at pc. Values are stated in the form
    the reflected segment computes (`wvalM`), so `rfl` closes them."""
    w = W[pc]
    f = fields(w)
    op, f3, f7 = f['op'], f['f3'], f['f7']
    A, B = src(f['rs1']), src(f['rs2'])
    sh6 = (w >> 20) & 0x3f
    sh5 = (w >> 20) & 0x1f
    SH6 = f'(Sail.BitVec.extractLsb (0x{sh6:02x}#6) 5 0)'
    SH5 = f'(0x{sh5:02x}#5)'
    X32 = lambda e: f'(Sail.BitVec.extractLsb {e} 31 0)'
    if op == 0x13:  # OP-IMM
        i = f['immI']
        tbl = {0: f'{A} + {sx12(i)}', 7: f'{A} &&& {sx12(i)}', 6: f'{A} ||| {sx12(i)}',
               4: f'{A} ^^^ {sx12(i)}', 1: f'shift_bits_left {A} {SH6}', 2: f'sltiV {A} ({sx12(i)})'}
        if f3 in tbl:
            v = tbl[f3]
        elif f3 == 5 and (f7 >> 1) == 0:
            v = f'shift_bits_right {A} {SH6}'
        elif f3 == 5 and (f7 >> 1) == 0x10:
            v = f'shift_bits_right_arith {A} {SH6}'
        else:
            return ('unsupported', None)
        return ('alu', dict(rd=f['rd'], srcs=[f['rs1']], val=v))
    if op == 0x1b:  # OP-IMM-32
        i = f['immI']
        if f3 == 0:
            v = f'sign_extend (m := 64) {X32(f"({A} + {sx12(i)})")}'
        elif f3 == 1:
            v = f'sign_extend (m := 64) (shift_bits_left {X32(A)} {SH5})'
        elif f3 == 5 and f7 == 0:
            v = f'sign_extend (m := 64) (shift_bits_right {X32(A)} {SH5})'
        elif f3 == 5 and f7 == 0x20:
            v = f'sign_extend (m := 64) (shift_bits_right_arith {X32(A)} {SH5})'
        else:
            return ('unsupported', None)
        return ('alu', dict(rd=f['rd'], srcs=[f['rs1']], val=v))
    if op == 0x33:  # OP
        tbl = {(0, 0): f'{A} + {B}', (0, 0x20): f'{A} - {B}', (6, 0): f'{A} ||| {B}',
               (7, 0): f'{A} &&& {B}', (4, 0): f'{A} ^^^ {B}',
               (1, 0): f'shift_bits_left {A} (Sail.BitVec.extractLsb {B} 5 0)',
               (5, 0): f'shift_bits_right {A} (Sail.BitVec.extractLsb {B} 5 0)',
               (2, 0): f'sltV {A} {B}'}
        if (f3, f7) not in tbl:
            return ('unsupported', None)
        return ('alu', dict(rd=f['rd'], srcs=[f['rs1'], f['rs2']], val=tbl[(f3, f7)]))
    if op == 0x3b:  # OP-32
        tbl = {(0, 0): f'sign_extend (m := 64) ({X32(A)} + {X32(B)})',
               (0, 0x20): f'sign_extend (m := 64) ({X32(A)} - {X32(B)})'}
        if (f3, f7) not in tbl:
            return ('unsupported', None)
        return ('alu', dict(rd=f['rd'], srcs=[f['rs1'], f['rs2']], val=tbl[(f3, f7)]))
    U = f'(sign_extend (m := 64) ((0x{(w >> 12) & 0xfffff:05x}#20) +++ (0x000#12)))'
    if op == 0x37:
        return ('alu', dict(rd=f['rd'], srcs=[], val=U))
    if op == 0x17:
        return ('alu', dict(rd=f['rd'], srcs=[], val=f'(0x{pc:x}#64) + {U}'))
    if op == 0x03:  # loads
        kinds = {3: ('ld', 8), 2: ('lw', 4), 6: ('lwu', 4), 4: ('lbu', 1), 1: ('lh', 2), 5: ('lhu', 2)}
        if f3 not in kinds:
            return ('unsupported', None)
        k, wd = kinds[f3]
        return ('load', dict(rd=f['rd'], rs1=f['rs1'], imm=f['immI'], kind=k, width=wd))
    if op == 0x23:  # stores
        kinds = {3: ('sd', 8), 2: ('sw', 4), 0: ('sb', 1), 1: ('sh', 2)}
        k, wd = kinds[f3]
        return ('store', dict(rs1=f['rs1'], rs2=f['rs2'], imm=f['immS'], kind=k, width=wd))
    if op == 0x63:
        ops = {0: 'BEQ', 1: 'BNE', 4: 'BLT', 5: 'BGE', 6: 'BLTU', 7: 'BGEU'}
        return ('br', dict(op=ops[f3], rs1=f['rs1'], rs2=f['rs2'], imm=f['immB'],
                           tgt=(pc + f['immB']) & M64))
    if op == 0x6f:
        tgt = (pc + f['immJ']) & M64
        if f['rd'] == 0:
            return ('j', dict(imm=f['immJ'], tgt=tgt))
        if f['rd'] == 1:
            return ('jal', dict(imm=f['immJ'], tgt=tgt))
        return ('unsupported', None)
    if op == 0x67 and f['rd'] == 0 and f['rs1'] == 1 and f['immI'] == 0:
        return ('ret', {})
    return ('unsupported', None)


# ---------------------------------------------------------------- the code bytes
text = []
for pc in PCS:
    w = W[pc]
    for i in range(4):
        text.append((pc + i, (w >> (8 * i)) & 0xff))
for i, b in enumerate(IMPURE[1]):
    text.append((IMPURE[0] + i, b))
CH = 16
chunks = [text[i:i + CH] for i in range(0, len(text), CH)]
where = {a: j for j, c in enumerate(chunks) for (a, _) in c}
BYTE = dict(text)


def node_name(lo, hi):
    return f'{P}Chunk{lo}' if hi - lo == 1 else f'{P}Node{lo}_{hi}'


node_defs = []


def build(lo, hi):
    if hi - lo == 1:
        return
    mid = (lo + hi) // 2
    build(lo, mid)
    build(mid, hi)
    node_defs.append(f'def {node_name(lo, hi)} : List (Nat × BitVec 8) :=\n'
                     f'  {node_name(lo, mid)} ++ {node_name(mid, hi)}\n')


build(0, len(chunks))
ROOT_NODE = node_name(0, len(chunks))


def mem_proof(a):
    """Proof term of `(a, BYTE[a]) ∈ allocText`."""
    j = where[a]
    leaf = f'(by decide : ((0x{a:x} : Nat), (0x{BYTE[a]:02x}#8 : BitVec 8)) ∈ {P}Chunk{j})'
    path = []
    lo, hi = 0, len(chunks)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if j < mid:
            path.append(('L', node_name(mid, hi)))
            hi = mid
        else:
            path.append(('R', node_name(lo, mid)))
            lo = mid
    pf = leaf
    for side, other in reversed(path):
        pf = (f'List.mem_append_left {other} ({pf})' if side == 'L'
              else f'List.mem_append_right {other} ({pf})')
    return pf


C = ['-- Generated by scripts/gen_alloc_steps.py; do not edit.',
     'import VsaIris.Vsa.SymRun', '',
     *CFG['CODE_DOC'], '',
     'namespace VsaIris.Sym', '', 'open Vsa.MemRepr Vsa.Sim', '']
for j, c in enumerate(chunks):
    C.append(f'def {P}Chunk{j} : List (Nat × BitVec 8) :=')
    C.append('  [' + ', '.join(f'(0x{a:x}, 0x{b:02x}#8)' for a, b in c) + ']\n')
C += node_defs
C.append(f'/-- {CFG["WHO"]} code bytes: `(address, byte)`. -/')
C.append(f'def {P}Text : List (Nat × BitVec 8) := {ROOT_NODE}\n')
for pc in PCS:
    bs = [BYTE[pc + i] for i in range(4)]
    C.append(f'theorem {P}_at_{pc:08x} {{m : Mem}} (h : TextLoaded {P}Text m) :')
    C.append('    ' + ' ∧\n    '.join(f'm[(0x{pc + i:x} : Nat)]? = some (0x{bs[i]:02x} : BitVec 8)'
                                       for i in range(4)) + ' :=')
    C.append('  ⟨' + ',\n   '.join(f'h _ ({mem_proof(pc + i)})' for i in range(4)) + '⟩\n')
JALS = [pc for pc in PCS if classify(pc)[0] == 'jal']
for pc in JALS:
    bs = [BYTE[pc + i] for i in range(4)]
    code = ', '.join(f'0x{b:02x}#8' for b in bs)
    C.append(f'theorem {P}_code_{pc:08x} : ∀ p ∈ codeFoot 0x{pc:x} [{code}], (p.1, p.2.2) ∈ {P}Text := by')
    C.append('  intro p hp')
    C.append('  simp only [codeFoot, List.zipIdx, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,')
    C.append('    List.mem_cons, List.not_mem_nil, or_false] at hp')
    C.append('  rcases hp with rfl | rfl | rfl | rfl')
    for i in range(4):
        C.append(f'  · exact {mem_proof(pc + i)}')
    C.append('')
a0, ib = IMPURE
C.append('/-- The `_impure_ptr` word. -/')
C.append(f'theorem {P}_impure {{m : Mem}} (h : TextLoaded {P}Text m) :')
C.append(f'    LPins8 m ({lit64(GPV)} + {lit64(a0 - GPV)}).toNat [' + ', '.join(f'0x{b:02x}#8' for b in ib) + '] := by')
C.append(f'  rw [show ({lit64(GPV)} + {lit64(a0 - GPV)}).toNat = 0x{a0:x} by decide]')
C.append('  exact ⟨' + ',\n   '.join(f'by rw [h _ ({mem_proof(a0 + i)})]; rfl' for i in range(8)) + '⟩\n')
C.append('end VsaIris.Sym\n')
(ROOT / CFG['CODE_OUT']).write_text('\n'.join(C))

# ---------------------------------------------------------------- the step table


def ks_of(regs):
    return sorted({r for r in regs if r != 0})


def lst(xs):
    return '[' + ', '.join(str(x) for x in xs) + ']'


def hgp(ks):
    return '(fun _ => rfl)' if 3 in ks else '(fun h => absurd h (by decide))'


def hR(ks):
    """Each pinned register's final value, `finReg` on the left."""
    alts = ' | '.join(['rfl'] * len(ks))
    return ('(by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; '
            f'rcases hx with {alts} <;> first | rfl | exact absurd rfl hg)')


def hRo(ks, rd=None):
    if rd is None:
        return '(fun _ _ _ _ => rfl)'
    return f'(fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : {rd} ∈ {lst(ks)}))))'


HDR = """theorem st_{pc:08x} {{live : Nat → Prop}} {{S : Nat → Prop}}
    {{Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}} {{R : Nat → BitVec 64}} {{Mt : Mem}}
    (hlive : ∀ p ∈ allocText, live p.1)""".replace('allocText', f'{P}Text')
CF = f'chain_facts hm with "VsaIris.Sym.{P}_at_"'


def step(seg, ks, lds, LD, W, cover, tail, gp, hpc, R, Ro, hk, ind='  '):
    """The `swp_step` application for one segment."""
    t = f'; {tail}' if tail else ''
    return (f'{ind}swp_step {seg} {lst(ks)} {lds} {LD} {W} 0 rfl (by decide) (by decide) (by decide)\n'
            f'{ind}  {cover} hlive\n'
            f'{ind}  (fun m hm hLD => by unfold {seg} ChainFacts; {CF}{t})\n'
            f'{ind}  (by decide) (by decide) {gp} (by decide) {"hLDS" if LD != "[]" else "(fun a h => by cases h)"}\n'
            f'{ind}  {"hS" if W != "[]" else "(fun a h => by cases h)"} {hpc}\n'
            f'{ind}  {R}\n'
            f'{ind}  {Ro} rfl {hk}')


def ea_expr(rs1, imm):
    """The effective address, as the segment computes it (`gp`-relative ones
    are closed terms, decided in place)."""
    return f'({src(rs1)} + {sx12(imm)}).toNat', rs1 == 3


def emit(pc):
    cls, d = classify(pc)
    w = W[pc]
    bs = [(w >> (8 * i)) & 0xff for i in range(4)]
    nxt = f'0x{pc + 4:x}#64'
    segs, thm = [], []
    if cls == 'unsupported':
        return None, None
    single = f'def ax_{pc:08x} : List BBlock := [{{ body := [mkLine 0x{pc:x}#64 0x{w:08x}#32], term := none }}]'
    tinstr = lambda kind, rs1, rs2, i13, i21: (
        f'⟨0x{pc:x}#64, 0x{w:08x}#32, 0x{bs[0]:02x}#8, 0x{bs[1]:02x}#8, 0x{bs[2]:02x}#8, '
        f'0x{bs[3]:02x}#8, {kind}, {rs1}, {rs2}, 0x{i13 & 0x1fff:x}#13, 0x{i21 & 0x1fffff:x}#21, 0#12⟩')
    tdef = lambda name, kind, rs1, rs2, i13, i21: (
        f'def {name} : List BBlock := [⟨[], some ({tinstr(kind, rs1, rs2, i13, i21)} : TInstr)⟩]')
    NIL = '(fun a _ => trivial)'
    if cls == 'alu':
        segs.append(single)
        ks = ks_of(d['srcs'] + [d['rd']])
        thm.append(HDR.format(pc=pc) + f"""
    (hk : {RUN} live S Q {nxt} (upd R {d['rd']} ({d['val']})) Mt) :
    {RUN} live S Q 0x{pc:x}#64 R Mt :=
""" + step(f'ax_{pc:08x}', ks, '[]', '[]', '[]', NIL, '', hgp(ks), 'rfl', hR(ks), hRo(ks, d['rd']), 'hk'))
    elif cls == 'load':
        segs.append(single)
        ea, conc = ea_expr(d['rs1'], d['imm'])
        wd = d['width']
        ks = ks_of([d['rs1'], d['rd']])
        if conc and (GPV + d['imm']) & M64 == IMPURE[0]:
            lds = '[[' + ', '.join(f'0x{b:02x}#8' for b in IMPURE[1]) + ']]'
            val = 'bytesVal .ld [' + ', '.join(f'0x{b:02x}#8' for b in IMPURE[1]) + ']'
            thm.append(HDR.format(pc=pc) + f"""
    (hk : {RUN} live S Q {nxt} (upd R {d['rd']} ({val})) Mt) :
    {RUN} live S Q 0x{pc:x}#64 R Mt :=
""" + step(f'ax_{pc:08x}', ks, lds, '[]', '[]', NIL,
           f'exact ⟨(show LdOK {ea} 8 by decide), {P}_impure hm⟩', hgp(ks), 'rfl', hR(ks),
           hRo(ks, d['rd']), 'hk'))
        else:
            pin = {8: 'lpins8_img hLD', 4: 'lpins4_img hLD', 1: 'lpins1_img hLD', 2: 'lpins2_img hLD'}[wd]
            okh = '' if conc else f'\n    (hea : LdOK {ea} {wd})'
            okp = f'(show LdOK {ea} {wd} by decide)' if conc else 'hea'
            thm.append(HDR.format(pc=pc) + f"""{okh}
    (hLDS : ∀ b ∈ accAddrs {ea} {wd}, S b)
    (hk : {RUN} live S Q {nxt} (upd R {d['rd']} (ldv .{d['kind']} Mt {ea})) Mt) :
    {RUN} live S Q 0x{pc:x}#64 R Mt :=
""" + step(f'ax_{pc:08x}', ks, f'[bytesAt (imgM Mt) {ea} {wd}]', f'(accAddrs {ea} {wd})', '[]', NIL,
           f'exact ⟨{okp}, {pin}⟩', hgp(ks), 'rfl', hR(ks), hRo(ks, d['rd']), 'hk'))
    elif cls == 'store':
        segs.append(single)
        ea, conc = ea_expr(d['rs1'], d['imm'])
        wd = d['width']
        ks = ks_of([d['rs1'], d['rs2']])
        ok = f'StOKb {ea}' if d['kind'] == 'sb' else f'StOK {ea} {wd}'
        okh = '' if conc else f'\n    (hea : {ok})'
        okp = f'(show {ok} by decide)' if conc else 'hea'
        thm.append(HDR.format(pc=pc) + f"""{okh}
    (hS : ∀ b ∈ accAddrs {ea} {wd}, S b)
    (hk : {RUN} live S Q {nxt} R (writeLog Mt [({ea}, {wd}, {src(d['rs2'])})])) :
    {RUN} live S Q 0x{pc:x}#64 R Mt :=
""" + step(f'ax_{pc:08x}', ks, '[]', '[]', f'(accAddrs {ea} {wd})', '(fun a ha => outL_single _ ha)',
           f'exact {okp}', hgp(ks), 'rfl', hR(ks), hRo(ks), 'hk'))
    elif cls == 'br':
        A, B = src(d['rs1']), src(d['rs2'])
        cond = {'BEQ': f'{A} = {B}', 'BNE': f'{A} ≠ {B}', 'BLT': f'{A}.toInt < {B}.toInt',
                'BGE': f'{B}.toInt ≤ {A}.toInt', 'BLTU': f'{A}.toNat < {B}.toNat',
                'BGEU': f'{B}.toNat ≤ {A}.toNat'}[d['op']]
        gl = {'BEQ': 'guard_beq', 'BNE': 'guard_bne', 'BLT': 'guard_blt', 'BGE': 'guard_bge',
              'BLTU': 'guard_bltu', 'BGEU': 'guard_bgeu'}[d['op']]
        ks = ks_of([d['rs1'], d['rs2']])
        segs.append(tdef(f'axT_{pc:08x}', f'.br bop.{d["op"]} true', d['rs1'], d['rs2'], d['imm'], 0))
        segs.append(tdef(f'axF_{pc:08x}', f'.br bop.{d["op"]} false', d['rs1'], d['rs2'], d['imm'], 0))
        tgt = f'0x{d["tgt"]:x}#64'
        thm.append(HDR.format(pc=pc) + f"""
    (hT : {cond} → {RUN} live S Q {tgt} R Mt) (hF : ¬ ({cond}) → {RUN} live S Q {nxt} R Mt) :
    {RUN} live S Q 0x{pc:x}#64 R Mt := by
  by_cases hc : {cond}
  · exact
""" + step(f'axT_{pc:08x}', ks, '[]', '[]', '[]', NIL, f'exact ({gl} _ _).2 hc', hgp(ks), 'rfl',
           hR(ks), hRo(ks), '(hT hc)', '    ') + """
  · exact
""" + step(f'axF_{pc:08x}', ks, '[]', '[]', '[]', NIL, f'exact (guard_false ({gl} _ _)).2 hc', hgp(ks),
           'rfl', hR(ks), hRo(ks), '(hF hc)', '    '))
    elif cls == 'j':
        segs.append(tdef(f'ax_{pc:08x}', '.j', 0, 0, 0, d['imm']))
        thm.append(HDR.format(pc=pc) + f"""
    (hk : {RUN} live S Q 0x{d['tgt']:x}#64 R Mt) :
    {RUN} live S Q 0x{pc:x}#64 R Mt :=
""" + step(f'ax_{pc:08x}', [], '[]', '[]', '[]', NIL, '', '(fun h => nomatch h)', 'rfl',
           '(fun _ h => nomatch h)', hRo([]), 'hk'))
    elif cls == 'ret':
        segs.append(tdef(f'ax_{pc:08x}', '.jr', 1, 0, 0, 0))
        thm.append(HDR.format(pc=pc) + f"""
    (hal : (R 1).toNat % 4 = 0) (hk : {RUN} live S Q (R 1) R Mt) :
    {RUN} live S Q 0x{pc:x}#64 R Mt :=
""" + step(f'ax_{pc:08x}', [1], '[]', '[]', '[]', NIL,
           'show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; '
           'rw [ret_tgt _ hal]; exact hal', hgp([1]), '(ret_tgt _ hal)', hR([1]), hRo([1]), 'hk'))
    elif cls == 'jal':
        code = ', '.join(f'0x{b:02x}#8' for b in bs)
        hb = '\n'.join(f'  have hb{i} := hb (0x{pc + i:x}, .discard, 0x{bs[i]:02x}#8) (by simp [codeFoot])'
                       for i in range(4))
        imm = d['imm'] & 0x1fffff
        tgt = d['tgt']
        thm.append(f"""open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in
/-- `jal` at `0x{pc:x}` to `0x{tgt:x}`. -/
theorem jalx_{pc:08x} (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x{pc:x} [{code}], live p.1) :
    JalExec (vsaModel live) 0x{pc:x} [{code}] 0x{tgt:x}#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
{hb}
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x{pc:x}#64) vm (0x{w:08x}#32) (0x{imm:06x}#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x{pc:x}#64) 4)
      {' '.join(f'(0x{b:02x}#8)' for b in bs)}
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_{w:08x} (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x{pc:x}#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x{tgt:x}#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x{pc:x}#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x{pc:x} + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h
""")
        thm.append(HDR.format(pc=pc) + f"""
    (hk : {RUN} live S Q 0x{tgt:x}#64 (upd R VsaIris.ra (BitVec.ofNat 64 (0x{pc:x} + 4))) Mt) :
    {RUN} live S Q 0x{pc:x}#64 R Mt :=
  swp_jal 0x{pc:x} [{code}] 0x{tgt:x}#64
    (jalx_{pc:08x} live fun p hp => hlive _ ({P}_code_{pc:08x} p hp)) {P}_code_{pc:08x}
    (by decide) (by decide) rfl hk""")
    return segs, thm


unsupported = []
parts = []
cur_segs, cur_thms, cur_mods, cur_pcs = [], [], set(), []
for pc in PCS:
    segs, thms = emit(pc)
    if segs is None:
        unsupported.append(pc)
        continue
    cur_segs += segs
    cur_thms += thms
    cur_mods.add(DEC[W[pc]])
    cur_pcs.append(pc)
    if len(cur_pcs) >= PER_FILE:
        parts.append((cur_segs, cur_thms, cur_mods, cur_pcs))
        cur_segs, cur_thms, cur_mods, cur_pcs = [], [], set(), []
if cur_pcs:
    parts.append((cur_segs, cur_thms, cur_mods, cur_pcs))

outdir = ROOT / CFG['STEPS_DIR']
outdir.mkdir(exist_ok=True)
for old in outdir.glob('Part*.lean'):
    old.unlink()
for k, (segs, thms, mods, pcs) in enumerate(parts):
    L = ['-- Generated by scripts/gen_alloc_steps.py; do not edit.',
         f'import {CFG["RUN_MOD"]}', 'import Vsa.Sim.EnvNewSites'] + \
        [f'import {m}' for m in sorted(mods)] + ['',
         f'/-! {CFG["WHO"]} step table, `0x{pcs[0]:x}` to `0x{pcs[-1]:x}` (one lemma `st_<pc>` per',
         'instruction; see `scripts/gen_alloc_steps.py`). -/', '',
         'open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail', '',
         'namespace Vsa.Sim', ''] + segs + ['', 'end Vsa.Sim', '',
         'namespace VsaIris.Sym', '', 'open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast', ''] + \
        [t + '\n' for t in thms] + ['end VsaIris.Sym', '']
    (outdir / f'Part{k:02d}.lean').write_text('\n'.join(L))
agg = ['-- Generated by scripts/gen_alloc_steps.py; do not edit.'] + \
      [f'import {CFG["STEPS_MOD"]}.Part{k:02d}' for k in range(len(parts))] + ['']
(ROOT / (CFG['STEPS_DIR'] + '.lean')).write_text('\n'.join(agg))
print(f'{len(PCS)} instructions, {len(text)} bytes, {len(chunks)} chunks, {len(parts)} parts')
print('unsupported:', ', '.join(f'0x{pc:x} {MN[pc]}' for pc in unsupported))
