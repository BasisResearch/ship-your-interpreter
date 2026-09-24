"""RISC-V instruction classification shared by the step-table generators
(`gen_alloc_steps.py`, `gen_interp_steps.py`). `classify_word` returns
`(class, info)` with every value stated in the form the reflected segment
computes (`wvalM`), so `rfl` closes it. `gpv` is the fixed `gp` value when the
run treats `gp` as a read-only constant (the allocator); `None` reads `R 3`."""

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


def src(r, gpv=None):
    if r == 0:
        return '(0#64)'
    if r == 3 and gpv is not None:
        return f'({lit64(gpv)})'
    return f'(R {r})'


def i12(v):
    return f'(0x{v & 0xfff:03x}#12)'


def sx12(v):
    return f'sign_extend (m := 64) {i12(v)}'


def classify_word(pc, w, gpv=None):
    """(class, info) for the instruction at pc. Values are stated in the form
    the reflected segment computes (`wvalM`), so `rfl` closes them."""
    f = fields(w)
    op, f3, f7 = f['op'], f['f3'], f['f7']
    A, B = src(f['rs1'], gpv), src(f['rs2'], gpv)
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


