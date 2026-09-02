#!/usr/bin/env python3
"""
writelog_smt.py — emit an exec-arm's WRITE-LOG as SMT and let Z3 discharge a
memory-frame SUPPLIER FIELD that the current encoder ENCODE-GAPs.

THESIS (see experiments/smt/WRITELOG-SMT.md): the reason exec-arm supplier
fields hit ENCODE-GAP is NOT that the Sail step is unencodable — it is that we
never emitted the arm's WRITE-LOG as SMT. Block-reflection (Vsa/Sim/BlockMem.lean)
ALREADY computes each straight-line arm's effect as
    writeLog : List (addr, width, value)   -- WEntry = Nat × Nat × BitVec 64
folded over the entry memory by `applyW`/`writeLog`. Emitting that list as SMT
array-stores over a symbolic input memory gives the arm's post memory as a small
closed formula, and Z3 can then check   machine-post ⟹ goal   exactly as the
bounded copy-probe (experiments/smt/bounded/gen_probe.py) did for the ValueRepr
COPY readback — which was itself a hand-written write-log of copy stores.

ARM CHOSEN (shallowest exec supplier field, an ENCODE-GAP one): the
`ExecS.brk`/`ExecS.cont` register-only leaf's `ExecLeafMemPin` field — the
memory-frame obligation the `ExecCaseGeom` widener must establish
(Vsa/Sim/ExecBrkCont.lean:212, rows/ExecCaseGeom.lean).

The exec_stmt prologue lowers sp by 176 and spills ra/s0/s1/s2/s3 with five
8-byte `sd`s; the arm (`li a0,N`) and the epilogue `ld`s write NO memory. So the
whole entry→exit memory delta is the five-entry write-log (block-reflection's
`wlogM`), all inside the stack window [SL.lo, sp):

   log = [ (sp-8 , 8, r  )   -- sd ra ,168(sp')   es_off168
         , (sp-16, 8, v8 )   -- sd s0 ,160(sp')   es_off160
         , (sp-24, 8, v9 )   -- sd s1 ,152(sp')   es_off152
         , (sp-32, 8, v18)   -- sd s2 ,144(sp')   es_off144
         , (sp-40, 8, v19) ] -- sd s3 ,136(sp')   es_off136

   m = writeLog m0 log

GOAL = ExecLeafMemPin SL sp m0 m  (Vsa/Sim/ExecBrkCont.lean:212):
   pres  : MemExtends m0 m                              (EvalSimCommon.lean:60)
           = ∀ a b, m0[a]?=some b → ∃ b', m[a]?=some b'
   agree : ∀ k, ¬(SL.lo ≤ k ∧ k < sp) → m[k]? = m0[k]?

Both are pure memory arithmetic over concrete `writeMap8` inserts (QF_ABV),
given the layout side facts the recursor supplies (SL.lo ≤ sp-40, sp aligned).

Memory model (reuses the working QF_ABV encoding of gen_probe.py):
   Mem = (def : Array Int Bool, val : Array Int (BV 8))
   m[a]? = some b  ↦  (select def a) ∧ (select val a) = b
A `writeMap8 m a d` = eight consecutive byte inserts at a..a+7 (BlockMem.applyW
`(a,8,d)` case). We store the 8 bytes as fresh symbolic BV8 (data value is
irrelevant to a FRAME obligation; only WHERE we wrote matters).
"""
import sys, subprocess, time, os, argparse

Z3 = "z3"
OUTDIR = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                      "..", "experiments", "smt", "writelog")

# ---- QF_ABV memory model (same shape as gen_probe.py) ----------------------
def decls_mem(name):
    return [f"(declare-fun {name}_def () (Array Int Bool))",
            f"(declare-fun {name}_val () (Array Int (_ BitVec 8)))"]

def bdef(m, idx):  return f"(select {m}_def {idx})"
def bval(m, idx):  return f"(select {m}_val {idx})"

# writeMap8 as 8 byte-inserts: post_def/post_val are `store` chains over pre.
# We build them as SMT let-bound arrays so `select` reduces.
def writemap8_arrays(pre_def, pre_val, addr_term, data_syms, out_def, out_val):
    """Emit define-fun for out_def/out_val = pre with 8 stores at addr..addr+7."""
    d = pre_def; v = pre_val
    L = []
    for j in range(8):
        nd = f"{out_def}_s{j}" if j < 7 else out_def
        nv = f"{out_val}_s{j}" if j < 7 else out_val
        L.append(f"(define-fun {nd} () (Array Int Bool) (store {d} (+ {addr_term} {j}) true))")
        L.append(f"(define-fun {nv} () (Array Int (_ BitVec 8)) (store {v} (+ {addr_term} {j}) {data_syms[j]}))")
        d, v = nd, nv
    return L

# ---- the write-log of the brk/cont register-only leaf ----------------------
# five 8-byte spills at sp-8, sp-16, sp-24, sp-32, sp-40 (program order).
SPILL_OFFSETS = [8, 16, 24, 32, 40]

def build(mode):
    """mode = 'validate' (assert goal-negation; UNSAT=proof) or one of the
    controls that deliberately break the obligation (SAT expected)."""
    L = ["(set-logic ALL)", "(set-option :timeout 60000)"]
    # entry memory m0
    L += decls_mem("m0")
    # symbolic sp, SL.lo, and spill data bytes (data irrelevant to a frame goal)
    L += ["(declare-fun sp () Int)", "(declare-fun sllo () Int)"]
    for s in range(5):
        for j in range(8):
            L.append(f"(declare-fun d{s}_{j} () (_ BitVec 8))")
    # layout side facts the recursor supplies (ExecArmEntryK / StackLayout):
    #   176 ≤ sp,  SL.lo ≤ sp-40  (all spills inside [SL.lo, sp)),  sp ≥ 0.
    L.append("(assert (<= 176 sp))")
    if mode == "ctrl_window":
        # BREAK the window fact: let SL.lo sit ABOVE the lowest spill so a spill
        # at sp-40 is OUTSIDE [SL.lo, sp) -> agree must fail there. (SAT expected)
        L.append("(assert (= sllo (- sp 8)))")   # window too narrow: only covers sp-8..
    else:
        L.append("(assert (<= sllo (- sp 40)))")  # honest: window covers all spills

    # fold the write-log: m = writeMap8^5(m0) at sp-8,-16,-24,-32,-40
    cur_def, cur_val = "m0_def", "m0_val"
    for s, off in enumerate(SPILL_OFFSETS):
        addr = f"(- sp {off})"
        data = [f"d{s}_{j}" for j in range(8)]
        od, ov = f"m{s+1}_def", f"m{s+1}_val"
        L += writemap8_arrays(cur_def, cur_val, addr, data, od, ov)
        cur_def, cur_val = od, ov
    mdef, mval = cur_def, cur_val   # = post memory `m`

    # ---- GOAL negation ----
    if mode in ("validate", "ctrl_window"):
        # agree: ∀ k, ¬(SL.lo ≤ k < sp) → m[k]?=m0[k]?
        # negate: ∃ k outside window with m[k]? ≠ m0[k]?  (def or val differs)
        L.append("(declare-fun k () Int)")
        L.append("(assert (not (and (<= sllo k) (< k sp))))")   # k outside window
        L.append(f"(assert (or (not (= (select m0_def k) (select {mdef} k))) "
                 f"(and (select {mdef} k) (not (= (select {mval} k) (select m0_val k))))))")
        # (the def-agree disjunct: m0_def[k] ≠ m_def[k]; the val-agree disjunct:
        #  present in m and value differs.)
    elif mode == "ctrl_pres":
        # pres: ∀ a b, m0[a]?=some b → ∃ b', m[a]?=some b'
        # This is TRUE (inserts only add). Control that BREAKS it is impossible
        # for inserts, so instead we test pres directly as validate: negate it.
        L.append("(declare-fun a () Int)")
        L.append("(declare-fun b () (_ BitVec 8))")
        L.append(f"(assert (and (select m0_def a) (= (select m0_val a) b)))")  # m0[a]?=some b
        L.append(f"(assert (not (select {mdef} a)))")                          # m[a]? = none
    elif mode == "pres":
        # VALIDATE pres: negate presence-preservation, expect UNSAT.
        L.append("(declare-fun a () Int)")
        L.append("(declare-fun b () (_ BitVec 8))")
        L.append(f"(assert (and (select m0_def a) (= (select m0_val a) b)))")
        L.append(f"(assert (not (select {mdef} a)))")
    else:
        raise ValueError(mode)

    L.append("(check-sat)")
    L.append("(get-model)")
    return "\n".join(L)

def run(q):
    t = time.time()
    p = subprocess.run([Z3, "-in"], input=q, capture_output=True, text=True, timeout=120)
    dt = time.time() - t
    out = p.stdout.strip()
    verdict = out.split("\n")[0] if out else ("(no output) " + p.stderr[:200])
    return verdict, dt, out

def main():
    os.makedirs(OUTDIR, exist_ok=True)
    print(f"{'field':16} {'mode':12} {'expect':8} {'verdict':10} {'time_s':7}")
    print("-" * 60)
    cases = [
        ("agree", "validate",    "UNSAT"),   # the ENCODE-GAP frame field: PROOF
        ("agree", "ctrl_window", "SAT"),      # break window -> countermodel
        ("pres",  "pres",        "UNSAT"),   # presence-preservation: PROOF
        ("pres",  "ctrl_pres",   "UNSAT"),    # inserts CANNOT drop presence, so the
                                              # "break-presence" attempt is itself UNSAT
                                              # — a positive confirmation, not a control.
    ]
    rows = []
    for field, mode, expect in cases:
        q = build(mode)
        fn = os.path.join(OUTDIR, f"q_{field}_{mode}.smt2")
        open(fn, "w").write(q)
        v, dt, out = run(q)
        print(f"{field:16} {mode:12} {expect:8} {v:10} {dt:6.2f}")
        rows.append((field, mode, expect, v, dt))
    return rows

if __name__ == "__main__":
    main()
