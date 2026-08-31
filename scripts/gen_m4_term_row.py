#!/usr/bin/env python3
"""gen_m4_term_row.py — emit the M4 term-side case-routing file.

Model: scripts/gen_m5_error_routing.py.  Each `mEvalE`-motive minor premise of
`term_sim_of_cases`/`execSeq_sim_of_cases` (TermSimClose.lean) is `EvalIH …` by
definitional unfolding; a `<case>_row` marshals the landed simulation lemma into
that slot.  This generator reads scripts/m4_term_rows.tsv (one row per premise,
with a `shape` column) and emits Vsa/Sim/rows/TermRouting.lean.

Five shapes:
  * leaf_direct — the leaf's entry IS `EvalEntry`; apply `<simD>` directly with a
    `LeafWiden` residual.
  * leaf_bridge — bridge `EvalEntry → <Entry>` (the leaf's own entry struct) by a
    record built from the shared `EvalEntry` fields + the leaf's extra callee
    geometry residual, then apply `<simD>`.
  * rec_unary   — the landed recursive sim is already `EvalEntry → EvalExitD`; the
    row supplies its `<Op>Extras` + `hMcallPop` residual, extracting the operand
    pointer from the entry `ExprRepr` (neg: value-typed `.int n`; not: any `vsub`).
  * rec_logical1 — one-IH short-circuit logical case (andFalse/orTrue): like
    rec_unary but keyed to the LEFT operand pointer (node offset 16) and carrying
    the extra `aEnv3` x13-survival Steps-residual the logical sims take (the resid
    is ∃-quantified over `aEnv3` per entry config `c`).
  * rec_logical2 — two-IH logical case (andTrue/orFalse): rec_logical1 plus the
    RIGHT operand pointer (node offset 24) and the second IH; the `<Op>Extras`
    additionally take the mid/post spec states `st' st''` and both values.

The DEFERRED premises (eq/ne, env_define-gated, the ∀-op `hBinary` dispatch, the
call subsystem, and every ExecS/loop premise) are documented in the tsv header and
NOT emitted; see experiments/residual-unification-survey.md ledger.

NO sorry/axiom/native_decide/bv_decide; no Mathlib.
"""
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TSV = os.path.join(ROOT, "scripts/m4_term_rows.tsv")
OUT = os.path.join(ROOT, "Vsa/Sim/rows/TermRouting.lean")

# ---- per-entry-structure field data for leaf_bridge shapes -------------------
# For each leaf entry structure: the residual conjuncts (name → Lean prop, with
# `SL`,`sp`,`sret`,`c` in scope) and the entry-record field bindings.  The shared
# EvalEntry-projected fields are common to all leaves; only the callee-specific
# lines differ.
SHARED_ENTRY_FIELDS = [
    "good", "tick", "pc", "a0", "a1", "a2", "ra", "ra_align", "spReg", "stackOK",
    "minstret", "mem", "code", "expr", "store", "store_survives", "out", "frame",
    "code_stack_disjoint", "expr_stack_disjoint", "expr_align", "expr_ram", "expr_win",
    "sret_align", "sret_ram", "sret_win", "sret_vicode_disjoint", "sret_stack_disjoint",
    "sret_evalcode_disjoint", "stack_ram", "stack_win", "spill_defined",
]

LEAF_BRIDGE = {
    "EvalNullEntry": dict(
        resid_name="NullLeafResid",
        value_pat=".null",
        vbinds=[],                      # extra value binders (name, type)
        extra_ghosts="",                # extra resid ∀-ghosts after `sp r sret`
        ast="Expr.null", val="Value.null",
        show_ast=".null", show_val=".null",
        ctor="EvalE.null st d env",
        # residual conjuncts: (binder, prop)
        resid=[
            ("hvnc", "(sret.toNat + 24 ≤ 0x800027ec ∨ 0x800027f8 ≤ sret.toNat)"),
            ("hvns", "((0x800027f8 : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec)"),
            ("hvnl", "Value_nullLoaded c.σ.mem"),
            ("hns",  "Vsa.Sim.NullSlotPinned c.σ.mem"),
            ("htsd", "((0x80019f58 : Nat) + 16 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + 12)"),
        ],
        # callee-specific entry field bindings (name := source)
        extra_fields=[
            ("sret_vnullcode_disjoint", "hvnc"),
            ("vnullcode_stack_disjoint", "hvns"),
            ("value_null_code", "hvnl"),
            ("null_slot", "hns"),
            ("table_stack_disjoint", "htsd"),
        ],
    ),
    "EvalBoolEntry": dict(
        resid_name="BoolLeafResid",
        value_pat="(.bool b)",
        vbinds=[("b", "Bool")],
        extra_ghosts="",
        ast="(Expr.bool b)", val="(Value.bool b)",
        show_ast="(.bool b)", show_val="(.bool b)",
        ctor="EvalE.bool st d env b",
        resid=[
            ("hvbc", "(sret.toNat + 24 ≤ 0x800027f8 ∨ 0x8000280c ≤ sret.toNat)"),
            ("hvbs", "((0x8000280c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027f8)"),
            ("hvbl", "Value_boolLoaded c.σ.mem"),
            ("hbs",  "Vsa.Sim.BoolSlotPinned c.σ.mem"),
            ("htsd", "((0x80019f58 : Nat) + 16 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + 8)"),
        ],
        extra_fields=[
            ("sret_vboolcode_disjoint", "hvbc"),
            ("vboolcode_stack_disjoint", "hvbs"),
            ("value_bool_code", "hvbl"),
            ("bool_slot", "hbs"),
            ("table_stack_disjoint", "htsd"),
        ],
    ),
    # The str leaf: same bridge shape; the two str_* conjuncts are ∀-quantified
    # over the payload pointer read, so no CString readback is needed in the
    # bridge — the extra `aExpr` ghost is threaded into the residual instead.
    "EvalStrEntry": dict(
        resid_name="StrLeafResid",
        value_pat="(.str s)",
        vbinds=[("s", "String")],
        extra_ghosts=" aExpr",
        ast="(Expr.str s)", val="(Value.str s)",
        show_ast="(.str s)", show_val="(.str s)",
        ctor="EvalE.str st d env s",
        resid=[
            ("hssd", "(∀ p : Nat, read64 c.σ.mem (aExpr.toNat + 8) = some p →\n"
                     "      p + s.length < SL.lo ∨ sp.toNat ≤ p)"),
            ("hsrd", "(∀ p : Nat, read64 c.σ.mem (aExpr.toNat + 8) = some p →\n"
                     "      p ≠ 0 ∧ (sret.toNat + 16 ≤ p ∨ p + s.length < sret.toNat))"),
            ("hvsc", "(sret.toNat + 24 ≤ 0x8000281c ∨ 0x8000282c ≤ sret.toNat)"),
            ("hvss", "((0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000281c)"),
            ("hvsl", "Value_strLoaded c.σ.mem"),
            ("hsl",  "Vsa.Sim.StrSlotPinned c.σ.mem"),
            ("htsd", "((0x80019f58 : Nat) + 8 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + 4)"),
        ],
        extra_fields=[
            ("str_stack_disjoint", "hssd"),
            ("str_sret_disjoint", "hsrd"),
            ("sret_vstrcode_disjoint", "hvsc"),
            ("vstrcode_stack_disjoint", "hvss"),
            ("value_str_code", "hvsl"),
            ("str_slot", "hsl"),
            ("table_stack_disjoint", "htsd"),
        ],
    ),
}


# ---- per-row data for the rec_logical shapes ---------------------------------
# Keyed by TSV `key`.  `tval` = the required left-value truthiness, `res`/`resdot`
# = the produced Value (premise spelling / dot spelling), `ctor` = the EvalE
# constructor, `extras` = the sim's <Op>Extras structure.
REC_LOGICAL1 = {
    "orTrue": dict(extras="OrTrueExtras", opAst=".or", opTok="LogOp.or",
                   tval="true", res="Value.bool true", resdot=".bool true",
                   ctor="EvalE.orTrue"),
    "andFalse": dict(extras="AndFalseExtras", opAst=".and", opTok="LogOp.and",
                     tval="false", res="Value.bool false", resdot=".bool false",
                     ctor="EvalE.andFalse"),
}

REC_LOGICAL2 = {
    "orFalse": dict(extras="OrFalseExtras", opAst=".or", opTok="LogOp.or",
                    tval="false", ctor="EvalE.orFalse"),
    "andTrue": dict(extras="AndTrueExtras", opAst=".and", opTok="LogOp.and",
                    tval="true", ctor="EvalE.andTrue"),
}

# The shared `hMcallPop` residual conjunct (M6 Layout: pre-call memory populated).
MCALLPOP = [
    "    (∀ mcall : Mem,",
    "      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?) →",
    "      ∀ a : Nat, ∃ b, mcall[a]? = some b)",
]

# The `aEnv3` x13-survival Steps-residual the logical sims take (∃-quantified:
# the row picks the witness the residual provider supplies for the entry `c`).
X13RESID = [
    "    (∃ aEnv3 : BitVec 64, ∀ cm : Config, Steps c cm →",
    "      cm.σ.regs.get? Register.PC = some (0x8000355c#64) →",
    "      cm.σ.regs.get? Register.x13 = some aEnv3) ∧",
]


def load_tsv():
    rows = []
    for line in open(TSV):
        line = line.rstrip("\n")
        if not line or line.startswith("#"):
            continue
        p = line.split("\t")
        if p[0] == "name":
            continue
        rows.append(dict(name=p[0], key=p[1], shape=p[2], simD=p[3], entry=p[4],
                         value=p[5], notes=p[6] if len(p) > 6 else ""))
    return rows


def emit_header(A):
    A("import Vsa.Sim.EvalLeafD")
    A("import Vsa.Sim.EvalNegSim3")
    A("import Vsa.Sim.EvalLogical4")
    A("import Vsa.Sim.ValueEqualSpec2")
    A("import Vsa.Sim.TermCaseBundle")
    A("")
    A("/-!")
    A("# `TermRouting` — mechanical term-side case rows (step-3, GENERATED)")
    A("")
    A("Each `mEvalE`-motive minor premise of `term_sim_of_cases`/`execSeq_sim_of_cases`")
    A("(`TermSimClose.lean`) is `EvalIH …` by definitional unfolding.  A `<case>_row`")
    A("adapter marshals the corresponding landed simulation lemma into that slot.")
    A("")
    A("GENERATED by `scripts/gen_m4_term_row.py` from `scripts/m4_term_rows.tsv`.")
    A("DO NOT hand-edit.  NO `sorry`/`axiom`/`native_decide`/`bv_decide`.")
    A("-/")
    A("")
    A("open LeanRV64DExecutable Sail Vsa")
    A("open Register")
    A("open Vsa.Machine (MState Config Halts Steps)")
    A("open Vsa.Logic (Triple)")
    A("open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc")
    A("open Vsa.Sim.Code")
    A("open Vsa.Sim.TermSimAssembly")
    A("")
    A("namespace Vsa.Sim.Rows")
    A("")
    A("local notation \"SpecSt\" => Vsa.While.St")
    A("")


def emit_int_direct(A, row):
    A("/-- The `LeafWiden` exit-widening bundle for the int leaf, ∀-closed over ghosts. -/")
    A("def IntLeafResid (st : SpecSt) (n : Int) : Prop :=")
    A("  ∀ (g : (R : Register) → Option (RegisterType R))")
    A("    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)")
    A("    (sp r sret : BitVec 64) (m0 : Mem),")
    A("    Vsa.Sim.LeafWiden g N A SL φf φc st (.int n) sp r sret m0")
    A("")
    A(f"/-- Route `{row['name']}` → `{row['simD']}`. -/")
    A("theorem eval_int_row (hR : ∀ st n, IntLeafResid st n) :")
    A("    ∀ (st : SpecSt) (d : Nat) (env : Addr) (n : Int),")
    A("      mEvalE st d env (Expr.int n) st (Value.int n) (EvalE.int st d env n) := by")
    A("  intro st d env n")
    A("  show Vsa.Sim.EvalIH st d env (.int n) st (.int n)")
    A("  intro g N A SL φf φc sp r sret aEnv aExpr m0")
    A(f"  exact Vsa.Sim.{row['simD']} g N A SL φf φc st d env n sp r sret aEnv aExpr m0")
    A("    (EvalE.int st d env n) (hR st n g N A SL φf φc sp r sret m0)")
    A("")


def emit_leaf_bridge(A, row):
    d = LEAF_BRIDGE[row["entry"]]
    key = row["key"]
    resid = d["resid"]
    valpat = d["value_pat"]
    vbinds = d["vbinds"]
    vnames = " ".join(n for (n, _) in vbinds)
    vparams = "(st : SpecSt)" + "".join(f" ({n} : {t})" for (n, t) in vbinds)
    hRq = "st" + "".join(f" {n}" for (n, _) in vbinds)
    econstr = d["ctor"]
    A(f"/-- The {key}-leaf residual: the `LeafWiden` widening + the callee geometry")
    A(f"`{row['entry']}` carries beyond `EvalEntry`. -/")
    A(f"def {d['resid_name']} {vparams} : Prop :=")
    A("  ∀ (g : (R : Register) → Option (RegisterType R))")
    A("    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)")
    A(f"    (sp r sret{d['extra_ghosts']} : BitVec 64) (m0 : Mem) (c : Config),")
    for (_, prop) in resid:
        A(f"    {prop} ∧")
    A(f"    Vsa.Sim.LeafWiden g N A SL φf φc st {valpat} sp r sret m0")
    A("")
    A(f"/-- Route `{row['name']}` → `{row['simD']}`, bridging `EvalEntry → {row['entry']}`. -/")
    A(f"theorem eval_{key}_row (hR : ∀ {hRq}, {d['resid_name']} {hRq}) :")
    binderdecl = "".join(f" ({n} : {t})" for (n, t) in vbinds)
    A(f"    ∀ (st : SpecSt) (d : Nat) (env : Addr){binderdecl},")
    A(f"      mEvalE st d env {d['ast']} st {d['val']} ({econstr}) := by")
    A(f"  intro st d env{''.join(' ' + n for (n, _) in vbinds)}")
    A(f"  show Vsa.Sim.EvalIH st d env {d['show_ast']} st {d['show_val']}")
    residcall = f"hR {hRq} g N A SL φf φc sp r sret{d['extra_ghosts']} m0 c"
    A("  intro g N A SL φf φc sp r sret aEnv aExpr m0")
    A("  intro c hc")
    A(f"  obtain ⟨{', '.join(b for (b,_) in resid)}, hW⟩ := {residcall}")
    bparam = f"{vnames} " if vnames else ""
    A(f"  have hEntry : Vsa.Sim.{row['entry']} g N A SL φf φc st d env {bparam}sp r sret aEnv aExpr m0 c :=")
    # record: shared fields then extras
    lines = []
    for f in SHARED_ENTRY_FIELDS:
        lines.append(f"{f} := hc.{f}")
    for (f, src) in d["extra_fields"]:
        lines.append(f"{f} := {src}")
    # emit as one braced record split across lines
    A("    { " + ", ".join(lines[:6]) + ",")
    i = 6
    while i < len(lines):
        chunk = lines[i:i+6]
        term = " }" if i + 6 >= len(lines) else ","
        A("      " + ", ".join(chunk) + term)
        i += 6
    A(f"  exact Vsa.Sim.{row['simD']} g N A SL φf φc st d env {bparam}sp r sret aEnv aExpr m0")
    A(f"    ({econstr}) hW c hEntry")
    A("")


def emit_rec_unary(A, row):
    A("/-- The neg-case residual: `NegExtras` + `hMcallPop`, keyed to the operand pointer")
    A("witnessed by the entry `ExprRepr`. -/")
    A("def NegResid (st : SpecSt) (esub : Expr) : Prop :=")
    A("  ∀ (N : NativeAddrs) (A : Arena) (SL : StackLayout)")
    A("    (sp r sret aEnv aExpr aOperand : BitVec 64) (m0 : Mem),")
    A("    read64 m0 (aExpr.toNat + 16) = some aOperand.toNat →")
    A("    ExprRepr m0 aOperand.toNat esub →")
    A("    Vsa.Sim.NegExtras N A SL st esub sp sret aExpr aOperand m0 ∧")
    A("    (∀ mcall : Mem,")
    A("      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?) →")
    A("      ∀ a : Nat, ∃ b, mcall[a]? = some b)")
    A("")
    A(f"/-- Route `{row['name']}` → `{row['simD']}`. -/")
    A("theorem eval_neg_row (hR : ∀ st esub, NegResid st esub) :")
    A("    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (n : Int)")
    A("      (a : EvalE st d env e st' (Value.int n)),")
    A("      mEvalE st d env e st' (Value.int n) a →")
    A("      mEvalE st d env (Expr.unary UnOp.neg e) st' (Value.int (wrap64 (-n)))")
    A("        (EvalE.neg st d env e st' n a) := by")
    A("  intro st d env esub st' n hE ihE")
    A("  show Vsa.Sim.EvalIH st d env (.unary .neg esub) st' (.int (wrap64 (-n)))")
    A("  intro g N A SL φf φc sp r sret aEnv aExpr m0")
    A("  intro c hc")
    A("  have hexpr : ExprRepr c.σ.mem aExpr.toNat (.unary .neg esub) := hc.expr")
    A("  rw [hc.mem] at hexpr")
    A("  obtain ⟨p, hpay, hpexpr⟩ : ∃ p, read64 m0 (aExpr.toNat + 16) = some p ∧ ExprRepr m0 p esub := by")
    A("    cases hexpr with | unary _ _ hp hpe => exact ⟨_, hp, hpe⟩")
    A("  have hplt : p < 2 ^ 64 := Vsa.Sim.read64_lt m0 (aExpr.toNat + 16) p hpay")
    A("  obtain ⟨hNegX, hMcallPop⟩ := hR st esub N A SL sp r sret aEnv aExpr (BitVec.ofNat 64 p) m0")
    A("    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hplt]; exact hpay)")
    A("    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hplt]; exact hpexpr)")
    A(f"  exact Vsa.Sim.{row['simD']} g N A SL φf φc st st' d env esub n sp r sret aEnv aExpr")
    A("    (BitVec.ofNat 64 p) m0 ihE (EvalE.neg st d env esub st' n hE) c ⟨hc, hNegX, hMcallPop⟩")
    A("")


def emit_rec_not(A, row):
    A("/-- The not-case residual: `NotSimExtras` + `hMcallPop`, keyed to the operand pointer")
    A("witnessed by the entry `ExprRepr` (the operand value `vsub` is spec-level). -/")
    A("def NotResid (esub : Expr) (vsub : Value) : Prop :=")
    A("  ∀ (N : NativeAddrs) (A : Arena) (SL : StackLayout)")
    A("    (sp r sret aEnv aExpr aOperand : BitVec 64) (m0 : Mem),")
    A("    read64 m0 (aExpr.toNat + 16) = some aOperand.toNat →")
    A("    ExprRepr m0 aOperand.toNat esub →")
    A("    Vsa.Sim.NotSimExtras N A SL esub vsub sp sret aExpr aOperand m0 ∧")
    for ln in MCALLPOP:
        A(ln)
    A("")
    A(f"/-- Route `{row['name']}` → `{row['simD']}`. -/")
    A("theorem eval_not_row (hR : ∀ esub vsub, NotResid esub vsub) :")
    A("    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value)")
    A("      (a : EvalE st d env e st' v),")
    A("      mEvalE st d env e st' v a →")
    A("      mEvalE st d env (Expr.unary UnOp.not e) st' (Value.bool (!v.truthy))")
    A("        (EvalE.not st d env e st' v a) := by")
    A("  intro st d env esub st' vsub hE ihE")
    A("  show Vsa.Sim.EvalIH st d env (.unary .not esub) st' (.bool (!vsub.truthy))")
    A("  intro g N A SL φf φc sp r sret aEnv aExpr m0")
    A("  intro c hc")
    A("  have hexpr : ExprRepr c.σ.mem aExpr.toNat (.unary .not esub) := hc.expr")
    A("  rw [hc.mem] at hexpr")
    A("  obtain ⟨p, hpay, hpexpr⟩ : ∃ p, read64 m0 (aExpr.toNat + 16) = some p ∧ ExprRepr m0 p esub := by")
    A("    cases hexpr with | unary _ _ hp hpe => exact ⟨_, hp, hpe⟩")
    A("  have hplt : p < 2 ^ 64 := Vsa.Sim.read64_lt m0 (aExpr.toNat + 16) p hpay")
    A("  obtain ⟨hNotX, hMcallPop⟩ := hR esub vsub N A SL sp r sret aEnv aExpr (BitVec.ofNat 64 p) m0")
    A("    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hplt]; exact hpay)")
    A("    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hplt]; exact hpexpr)")
    A(f"  exact Vsa.Sim.{row['simD']} g N A SL φf φc st st' d env esub vsub sp r sret aEnv aExpr")
    A("    (BitVec.ofNat 64 p) m0 ihE (EvalE.not st d env esub st' vsub hE) c ⟨hc, hNotX, hMcallPop⟩")
    A("")


def emit_rec_logical1(A, row):
    d = REC_LOGICAL1[row["key"]]
    key = row["key"]
    Cap = key[0].upper() + key[1:]
    A(f"/-- The {key}-case residual: `{d['extras']}` + the `aEnv3` x13-survival")
    A("Steps-residual + `hMcallPop`, keyed to the LEFT-operand pointer witnessed by the")
    A("entry `ExprRepr` (logical node payload at offset 16). -/")
    A(f"def {Cap}Resid (el er : Expr) (vl : Value) : Prop :=")
    A("  ∀ (N : NativeAddrs) (A : Arena) (SL : StackLayout)")
    A("    (sp r sret aEnv aExpr aLeft : BitVec 64) (m0 : Mem) (c : Config),")
    A("    read64 m0 (aExpr.toNat + 16) = some aLeft.toNat →")
    A("    ExprRepr m0 aLeft.toNat el →")
    A(f"    Vsa.Sim.{d['extras']} N A SL el er vl sp sret aExpr aLeft m0 ∧")
    for ln in X13RESID:
        A(ln)
    for ln in MCALLPOP:
        A(ln)
    A("")
    A(f"/-- Route `{row['name']}` → `{row['simD']}`. -/")
    A(f"theorem eval_{key}_row (hR : ∀ el er vl, {Cap}Resid el er vl) :")
    A("    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value)")
    A(f"      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = {d['tval']}),")
    A("      mEvalE st d env l st' lv a →")
    A(f"      mEvalE st d env (Expr.logical {d['opTok']} l r) st' ({d['res']})")
    A(f"        ({d['ctor']} st d env l r st' lv a a_1) := by")
    A("  intro st d env el er st' vl hE hvl ihE")
    A(f"  show Vsa.Sim.EvalIH st d env (.logical {d['opAst']} el er) st' ({d['resdot']})")
    A("  intro g N A SL φf φc sp r sret aEnv aExpr m0")
    A("  intro c hc")
    A(f"  have hexpr : ExprRepr c.σ.mem aExpr.toNat (.logical {d['opAst']} el er) := hc.expr")
    A("  rw [hc.mem] at hexpr")
    A("  obtain ⟨p, hpay, hpexpr⟩ : ∃ p, read64 m0 (aExpr.toNat + 16) = some p ∧ ExprRepr m0 p el := by")
    A("    cases hexpr with | logical _ _ hl hle _ _ => exact ⟨_, hl, hle⟩")
    A("  have hplt : p < 2 ^ 64 := Vsa.Sim.read64_lt m0 (aExpr.toNat + 16) p hpay")
    A("  obtain ⟨hX, ⟨aEnv3, hx13⟩, hMcallPop⟩ := hR el er vl N A SL sp r sret aEnv aExpr")
    A("    (BitVec.ofNat 64 p) m0 c")
    A("    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hplt]; exact hpay)")
    A("    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hplt]; exact hpexpr)")
    A(f"  exact Vsa.Sim.{row['simD']} g N A SL φf φc st st' d env el er vl sp r sret aEnv aExpr")
    A(f"    (BitVec.ofNat 64 p) aEnv3 m0 hvl ihE ({d['ctor']} st d env el er st' vl hE hvl) c")
    A("    ⟨hc, hX, hx13, hMcallPop⟩")
    A("")


def emit_rec_logical2(A, row):
    d = REC_LOGICAL2[row["key"]]
    key = row["key"]
    Cap = key[0].upper() + key[1:]
    A(f"/-- The {key}-case residual: `{d['extras']}` (two-eval: takes the mid/post spec")
    A("states and BOTH values) + the `aEnv3` x13-survival Steps-residual + `hMcallPop`,")
    A("keyed to BOTH operand pointers witnessed by the entry `ExprRepr` (offsets 16/24). -/")
    A(f"def {Cap}Resid (st' st'' : SpecSt) (el er : Expr) (vl vr : Value) : Prop :=")
    A("  ∀ (N : NativeAddrs) (A : Arena) (SL : StackLayout)")
    A("    (sp r sret aEnv aExpr aLeft aRight : BitVec 64) (m0 : Mem) (c : Config),")
    A("    read64 m0 (aExpr.toNat + 16) = some aLeft.toNat →")
    A("    ExprRepr m0 aLeft.toNat el →")
    A("    read64 m0 (aExpr.toNat + 24) = some aRight.toNat →")
    A("    ExprRepr m0 aRight.toNat er →")
    A(f"    Vsa.Sim.{d['extras']} N A SL st' st'' el er vl vr sp sret aExpr aLeft aRight m0 ∧")
    for ln in X13RESID:
        A(ln)
    for ln in MCALLPOP:
        A(ln)
    A("")
    A(f"/-- Route `{row['name']}` → `{row['simD']}` (two IH premises). -/")
    A(f"theorem eval_{key}_row (hR : ∀ st' st'' el er vl vr, {Cap}Resid st' st'' el er vl vr) :")
    A("    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value)")
    A(f"      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = {d['tval']}) (a_2 : EvalE st' d env r st'' rv),")
    A("      mEvalE st d env l st' lv a → mEvalE st' d env r st'' rv a_2 →")
    A(f"      mEvalE st d env (Expr.logical {d['opTok']} l r) st'' (Value.bool rv.truthy)")
    A(f"        ({d['ctor']} st d env l r st' st'' lv rv a a_1 a_2) := by")
    A("  intro st d env el er st' st'' vl vr hEl hvl hEr ihL ihR")
    A(f"  show Vsa.Sim.EvalIH st d env (.logical {d['opAst']} el er) st'' (.bool vr.truthy)")
    A("  intro g N A SL φf φc sp r sret aEnv aExpr m0")
    A("  intro c hc")
    A(f"  have hexpr : ExprRepr c.σ.mem aExpr.toNat (.logical {d['opAst']} el er) := hc.expr")
    A("  rw [hc.mem] at hexpr")
    A("  obtain ⟨p, q, hpay, hpexpr, hqay, hqexpr⟩ :")
    A("      ∃ p q, read64 m0 (aExpr.toNat + 16) = some p ∧ ExprRepr m0 p el ∧")
    A("        read64 m0 (aExpr.toNat + 24) = some q ∧ ExprRepr m0 q er := by")
    A("    cases hexpr with | logical _ _ hl hle hr' hre => exact ⟨_, _, hl, hle, hr', hre⟩")
    A("  have hplt : p < 2 ^ 64 := Vsa.Sim.read64_lt m0 (aExpr.toNat + 16) p hpay")
    A("  have hqlt : q < 2 ^ 64 := Vsa.Sim.read64_lt m0 (aExpr.toNat + 24) q hqay")
    A("  obtain ⟨hX, ⟨aEnv3, hx13⟩, hMcallPop⟩ := hR st' st'' el er vl vr N A SL sp r sret aEnv aExpr")
    A("    (BitVec.ofNat 64 p) (BitVec.ofNat 64 q) m0 c")
    A("    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hplt]; exact hpay)")
    A("    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hplt]; exact hpexpr)")
    A("    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqlt]; exact hqay)")
    A("    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqlt]; exact hqexpr)")
    A(f"  exact Vsa.Sim.{row['simD']} g N A SL φf φc st st' st'' d env el er vl vr sp r sret aEnv aExpr")
    A("    (BitVec.ofNat 64 p) (BitVec.ofNat 64 q) aEnv3 m0 hvl ihL ihR")
    A(f"    ({d['ctor']} st d env el er st' st'' vl vr hEl hvl hEr) c ⟨hc, hX, hx13, hMcallPop⟩")
    A("")


def emit():
    rows = load_tsv()
    L = []
    A = L.append
    emit_header(A)
    A("/-! ## Leaf rows. -/")
    A("")
    for r in rows:
        if r["shape"] == "leaf_direct":
            emit_int_direct(A, r)
    for r in rows:
        if r["shape"] == "leaf_bridge":
            emit_leaf_bridge(A, r)
    A("/-! ## Recursive rows. -/")
    A("")
    for r in rows:
        if r["shape"] == "rec_unary":
            emit_rec_unary(A, r)
    for r in rows:
        if r["shape"] == "rec_not":
            emit_rec_not(A, r)
    for r in rows:
        if r["shape"] == "rec_logical1":
            emit_rec_logical1(A, r)
    for r in rows:
        if r["shape"] == "rec_logical2":
            emit_rec_logical2(A, r)
    A("end Vsa.Sim.Rows")
    A("")
    open(OUT, "w").write("\n".join(L))
    print(f"wrote {OUT} ({len(rows)} rows: "
          f"{', '.join(r['key'] for r in rows)})")


if __name__ == "__main__":
    emit()
