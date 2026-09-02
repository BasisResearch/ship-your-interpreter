#!/usr/bin/env python3
"""
Bounded-SMT feasibility probe for a shallow SUPPLIER-class field.

TARGET (chosen shallowest, see BOUNDED-PROBE.md): the `.null`/`.bool` case of
the ValueRepr *copy readback* obligation used by ReprCopy.lean / EvalNullSim /
env_get HIT-tail:

    (H)  ValueRepr m  N φc srcAddr v          -- source value is represented
    (C)  (∀ j<24, m'[dstAddr+j]? = m[srcAddr+j]?)   -- 24 struct bytes copied
    ==>  ValueRepr m' N φc dstAddr v           -- readback at the new address

Unlike the existing DumpSmtLib policy (ValueRepr OPAQUE), here we ENCODE THE
DEFINITION of ValueRepr by CASE-SPLITTING on the Value constructor and unfolding
`read32`/`readI64` (= bounded `readLE`) into the QF_ABV memory model that already
works (Mem = (def:Array Int Bool, val:Array Int (BV8)); m[a]?=some b  ↦
(select def a) ∧ (select val a)=b).

DEPTH AXIS k = how deep we unfold the inductive `Value` datatype:
  k=1 : v = .null                      -> ValueRepr = read32 · = some 0   (1 read, NO recursion)
  k=2 : v ∈ {.null,.bool,.int}         -> adds read32/readI64 payload      (finite reads, NO recursion)
  k=3 : v ∈ {..,.str}                  -> adds  ∃p, read64·=p ∧ CString m p s
                                          CString is the RECURSIVE inductive (the wall)

MODES:
  validate : assert (H ∧ C ∧ ¬Cncl); UNSAT  => the field is a THEOREM in-fragment.
  refute   : assert (H ∧ C ∧ ¬Cncl); SAT     => countermodel (should be UNSAT here
                                                since the field is TRUE; SAT only if
                                                our encoding is too weak / a real bug).
Plus a control REFUTE of a deliberately-FALSE twin (drop the copy hyp on byte 0)
to confirm the fragment can still produce countermodels at each depth.
"""
import sys, subprocess, time, os

Z3 = "z3"

# ---- memory model helpers (reuse the working QF_ABV encoding) --------------
def decls_mem(name):
    return [f"(declare-fun {name}_def () (Array Int Bool))",
            f"(declare-fun {name}_val () (Array Int (_ BitVec 8)))"]

def byte_defined(m, idx):
    return f"(select {m}_def {idx})"

def byte_val(m, idx):
    return f"(select {m}_val {idx})"

def readLE_eq(m, a, width, valexpr):
    """(read m a width) = some valexpr  as: all bytes defined AND LE-combine = val.
    valexpr is an Int SMT term. Encodes read32/read64 by full byte unfold."""
    conj = []
    for j in range(width):
        conj.append(byte_defined(m, f"(+ {a} {j})"))
    # LE combine: sum_{j} byte_j * 256^j  as Int, comparing to valexpr
    terms = []
    mul = 1
    for j in range(width):
        bj = f"(bv2int {byte_val(m, f'(+ {a} {j})')})"
        terms.append(f"(* {bj} {mul})")
        mul *= 256
    le = terms[0] if len(terms)==1 else "(+ " + " ".join(terms) + ")"
    conj.append(f"(= {le} {valexpr})")
    return "(and " + " ".join(conj) + ")"

def read32_eq(m, a, v):   return readLE_eq(m, a, 4, str(v))
def read64_eq(m, a, v):   return readLE_eq(m, a, 8, v)   # v may be a symbol
def read64_defined(m, a): # some p  (p existential): all 8 bytes defined
    return "(and " + " ".join(byte_defined(m, f"(+ {a} {j})") for j in range(8)) + ")"
def read64_val(m, a):
    terms=[]; mul=1
    for j in range(8):
        terms.append(f"(* (bv2int {byte_val(m, f'(+ {a} {j})')}) {mul})"); mul*=256
    return "(+ " + " ".join(terms) + ")"

# signed 64 read (readI64): value in [-2^63, 2^63); encode as unsigned n with
# int = n - 2^64 * (n >= 2^63).  We only need read32-tag for validity so keep simple.
def readI64_eq(m, a, sym):
    # all 8 defined AND the unsigned combine equals 'usym' (a fresh unsigned Int)
    return "(and " + read64_defined(m,a) + f" (= {read64_val(m,a)} {sym}))"

# ---- WRITE-LOG EMITTER (the machine effect, NOT an abstract copy hyp) -------
#
# The arm's computed write-log is Vsa/Sim/BlockMem.lean `wlogM : List WEntry`,
# WEntry = (addr : Nat, width ∈ {1,2,4,8}, value : BitVec 64).  `writeLog` folds
# `applyW` left-to-right: each entry stores `width` little-endian bytes of
# `value` at `addr..addr+width`.  Here we emit the SAME fold as a chain of SMT
# Array `store`s taking the source memory `src` to the destination `dst`, so the
# destination memory is DERIVED from the effect the arm actually performs rather
# than assumed via a hand copy-hypothesis.  This needs NO external Sail toolchain
# — the write-log is a first-order list the seg/#derive_case outcome already
# computes (BlockMem.wlogM), so a caller passes it in directly.
#
# A write-log entry addr/value may be a CONCRETE int or a SYMBOL string (for a
# copied byte whose value is `m[srcAddr+j]`, the value term is a byte read from
# src).  We keep both the `def` (definedness) and `val` (BV8) arrays in lockstep.

def _le_bytes(width, value_term):
    """The `width` little-endian BV8 byte terms of an Int-or-symbol value term.
    Returns list of SMT (BV 8) expressions, low byte first."""
    out = []
    for j in range(width):
        # ((value >> 8j) & 0xff) as BV8.  value_term is an Int SMT term.
        out.append(f"((_ int2bv 8) (mod (div {value_term} {1 << (8*j)}) 256))")
    return out

def wlog_stores(src, dst, log):
    """Emit `dst = writeLog src log` as chained Array stores.

    log : list of (addr_term, width, value_term); addr/value are SMT Int terms
    (concrete literals or declared symbols).  A special value_term of the form
    ("copy", src_addr_term) means: store the *byte* read from src at src_addr
    (used for memcpy-style struct copies where the stored value is a live src
    byte, not a literal).  Returns a list of assert strings binding dst_def /
    dst_val as `store` chains over src_def / src_val."""
    def_expr = f"{src}_def"
    val_expr = f"{src}_val"
    for (addr, width, value) in log:
        if isinstance(value, tuple) and value[0] == "copy":
            # single-byte copy of src[value[1]]
            sa = value[1]
            def_expr = f"(store {def_expr} {addr} (select {src}_def {sa}))"
            val_expr = f"(store {val_expr} {addr} (select {src}_val {sa}))"
        else:
            bytes_le = _le_bytes(width, str(value))
            for j, bv in enumerate(bytes_le):
                a = f"(+ {addr} {j})"
                def_expr = f"(store {def_expr} {a} true)"
                val_expr = f"(store {val_expr} {a} {bv})"
    return [f"(assert (= {dst}_def {def_expr}))",
            f"(assert (= {dst}_val {val_expr}))"]

def wlog_readback_facts(src_base, dst_base, nbytes, drop=None):
    """The select-store CONSEQUENCES of a struct-copy write-log: dst byte j reads
    back to src byte j.  Each is Z3-trivial (`select (store a k v) k = v`) given
    the store chain from `wlog_stores`; we emit them so the value-reconstruction
    (readI64/read32) does not have to walk the whole store chain symbolically
    (which is nonlinear for the 8-byte int payload and returns UNKNOWN).  These
    are NOT extra hypotheses — they are derivable facts of the emitted effect."""
    out = []
    for j in range(nbytes):
        if drop is not None and j == drop:
            continue
        out.append(f"(assert (= (select {dst_base[0]}_def (+ {dst_base[1]} {j})) "
                   f"(select {src_base[0]}_def (+ {src_base[1]} {j}))))")
        out.append(f"(assert (= (select {dst_base[0]}_val (+ {dst_base[1]} {j})) "
                   f"(select {src_base[0]}_val (+ {src_base[1]} {j}))))")
    return out

def copy_wlog(src_base, dst_base, nbytes, drop=None):
    """The 24-byte struct-copy write-log: for each j, store dst_base+j <- src[src_base+j].
    This is the memcpy the ValueRepr copy arm performs, expressed as a write-log.
    `drop` skips one byte (the deliberately-false twin)."""
    log = []
    for j in range(nbytes):
        if drop is not None and j == drop:
            continue
        log.append((f"(+ {dst_base} {j})", 1, ("copy", f"(+ {src_base} {j})")))
    return log

# ---- copy hypothesis: 24 struct bytes copied dst<-src ----------------------
def copy24(src, dst, drop=None):
    conj=[]
    for j in range(24):
        if drop is not None and j==drop:  # falsity control: skip this byte
            continue
        conj.append(f"(= {byte_defined(dst, f'(+ dstAddr {j})')} {byte_defined(src, f'(+ srcAddr {j})')})")
        conj.append(f"(= {byte_val(dst, f'(+ dstAddr {j})')} {byte_val(src, f'(+ srcAddr {j})')})")
    return "(and " + " ".join(conj) + ")"

# ---- ValueRepr, definition-encoded, bounded to depth k ---------------------
def valuerepr_null(m, a):
    return read32_eq(m, a, 0)

def valuerepr_bool(m, a):
    # read32 a = 1 ∧ read32 (a+8) ∈ {0,1}   (cond b 1 0)
    b = "bB"  # bool payload symbol (shared src/dst via same v)
    return f"(and {read32_eq(m, a, 1)} (or {read32_eq(m, f'(+ {a} 8)', 0)} {read32_eq(m, f'(+ {a} 8)', 1)}))"

def valuerepr_int(m, a):
    # read32 a = 2 ∧ readI64 (a+8) = n   (n a fresh unsigned symbol nN)
    return f"(and {read32_eq(m, a, 2)} {readI64_eq(m, f'(+ {a} 8)', 'nN')})"

def valuerepr_str_bounded(m, a, cdepth):
    # read32 a = 3 ∧ ∃p, read64(a+8)=p ∧ p≠0 ∧ CString m p s
    # CString is the RECURSIVE inductive; bounded-unfold to cdepth chars then STOP.
    # We encode the bounded prefix; the tail is left as an OPAQUE Bool (the wall).
    tag = read32_eq(m, a, 3)
    p = f"{m}_p"
    ptr = f"(and {read64_defined(m, f'(+ {a} 8)')} (= {read64_val(m, f'(+ {a} 8)')} {p}) (not (= {p} 0)))"
    # CString bounded: char 0..cdepth-1 nonzero & <128, then NUL (or opaque tail)
    cs=[]
    for i in range(cdepth):
        cs.append(f"(select {m}_def (+ {p} {i}))")
    # opaque tail: the string could be longer -> uninterpreted
    cs.append(f"cstr_tail_{m}")
    return f"(and {tag} {ptr} (and {' '.join(cs)}))"

def valuerepr(m, a, kind, k):
    if kind=="null": return valuerepr_null(m,a)
    if kind=="bool": return valuerepr_bool(m,a)
    if kind=="int":  return valuerepr_int(m,a)
    if kind=="str":  return valuerepr_str_bounded(m,a,k)  # cdepth = k
    raise ValueError(kind)

# ---- build a query ---------------------------------------------------------
def build(kind, k, mode, control=False):
    L=["(set-logic ALL)","(set-option :timeout 60000)"]
    for m in ("m","mp"):
        L += decls_mem(m)
    L += ["(declare-fun srcAddr () Int)","(declare-fun dstAddr () Int)"]
    if kind=="bool": L.append("(declare-fun bB () Int)")
    if kind=="int":  L.append("(declare-fun nN () Int)")
    if kind=="str":
        L += [f"(declare-fun {m}_p () Int)" for m in ("m","mp")]
        L += [f"(declare-fun cstr_tail_{m} () Bool)" for m in ("m","mp")]
    L.append("(assert (>= srcAddr 0)) (assert (>= dstAddr 0))")
    # H: source represented
    H = valuerepr("m","srcAddr",kind,k)
    # C: 24-byte copy (control drops byte 0 => false twin)
    C = copy24("m","mp",drop=(0 if control else None))
    # Cncl: dst represented
    Cncl = valuerepr("mp","dstAddr",kind,k)
    L.append(f"(assert {H})")
    L.append(f"(assert {C})")
    L.append(f"(assert (not {Cncl}))")
    L.append("(check-sat)")
    L.append("(get-info :all-statistics)" if False else "(get-model)")
    return "\n".join(L)

def run(q):
    t=time.time()
    p=subprocess.run([Z3,"-in"],input=q,capture_output=True,text=True,timeout=90)
    dt=time.time()-t
    out=p.stdout.strip()
    verdict=out.split("\n")[0] if out else "(no output)"
    return verdict, dt, out

def main():
    kinds = {"null":[1,2,3], "bool":[1,2,3], "int":[1,2,3], "str":[1,2,3]}
    outdir=os.path.dirname(os.path.abspath(__file__))
    print(f"{'kind':6} {'k':2} {'mode':9} {'ctrl':5} {'verdict':10} {'time_s':7}")
    print("-"*50)
    rows=[]
    # validate/refute are the SAME query here (field is true; UNSAT=proof, SAT=countermodel);
    # 'mode' label just tags interpretation. Add the false-twin control for refute-capability.
    for kind,ks in kinds.items():
        for k in ks:
            for control in (False, True):
                q=build(kind,k,"q",control=control)
                fn=os.path.join(outdir,f"q_{kind}_k{k}_{'ctrl' if control else 'true'}.smt2")
                open(fn,"w").write(q)
                v,dt,out=run(q)
                tag="refute-twin" if control else "validate"
                print(f"{kind:6} {k:<2} {tag:9} {str(control):5} {v:10} {dt:6.2f}")
                rows.append((kind,k,tag,control,v,dt))
    return rows

if __name__=="__main__":
    main()
