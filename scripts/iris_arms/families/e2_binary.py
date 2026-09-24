# Lane E2: the binary operators' case families (INTERP_DESIGN.md §6, §8).
# Loaded by gen_iris_cases.py (`FAMILIES_EXT`); rows in scripts/iris_arms/arms.d/e2-binary.tsv.

# Operator token the dispatch reads (`binOpTok`, `lexer.h`).
E2_TOK = {"add": 11, "sub": 12, "mul": 13, "div": 14, "mod": 15, "ne": 17, "eq": 19,
          "lt": 20, "le": 21, "gt": 22, "ge": 23}

# The single helper of a one-helper tail: spec name, hypothesis name, C name.
E2_HELPER = {"valueInt": ("valueIntSpec", "hvi", "value_int"),
             "valueBool": ("valueBoolSpec", "hvb", "value_bool")}

# Integer comparisons: the word `value_bool` receives and its reading as the
# source's `decide` (`BinArm.lean`, `cmp_*_bit`).
E2_CMP = {
    "lt": ("cmpRaw w1 u1 >>> 63", "cmp_lt_bit", "a < b"),
    "le": ("sltiV (cmpRaw w1 u1) 1#64", "cmp_le_bit", "a ≤ b"),
    "gt": ("sltV 0#64 (cmpRaw w1 u1)", "cmp_gt_bit", "a > b"),
    "ge": ("(cmpRaw w1 u1 ^^^ 0xffffffffffffffff#64) >>> 63", "cmp_ge_bit", "a ≥ b"),
}


def seg_split(name, facts, run):
    """A run with split points (`run <from> <to> @pc …`): the first `#ix_seg`
    stops at the first point, each `#ix_piece` continues the previous one's
    end state to the next point, and `#ix_tree` joins them into `name` (the
    shape of one `#ix_seg`). Each piece is its own declaration, so a long run
    stays within the elaboration budget. Returns the first segment's name and
    the text after its statement."""
    stops = [a[1:] for a in run.args[2:] if a.startswith("@")] + [run.args[1]]
    at = lambda pc: f"0x{int(pc, 0):08x}"
    tac = f"ix_run hlive using [{facts}]"
    if len(stops) == 1:
        return name, f"  by {tac} at {at(stops[0])}\n"
    out = [f"  by {tac} at {at(stops[0])}\n"]
    for k in range(1, len(stops)):
        out.append(f"#ix_piece {name}_{k + 1} from {name}_{k} by\n  {tac} at {at(stops[k])}\n")
    tree = f"{name}_{len(stops)}"
    for k in range(len(stops) - 1, 0, -1):
        tree = f"{name}_{k} [{tree}]"
    out.append(f"#ix_tree {name} := {tree}\n")
    return f"{name}_1", "\n".join(out)


def subst_binOne(arm, mode):
    """Family `binOne`: the binary arm on two ints whose tail is ONE helper
    call (`value_bool` for the integer comparisons). Lane G's prologue runs are
    reused; the row's own runs are the operator dispatch with the tail up to the
    helper's `jal` and the epilogue after it. Params: `op` (a key of `E2_CMP`)."""
    runs = run_steps(arm)
    helpers = [s for s in arm.steps if s.op == "helper"]
    if len(runs) != 4 or len(helpers) != 1 or [c.slot for c in arm.children] != [120, 144]:
        raise SystemExit(f"{arm.name}: family binOne needs 4 runs, 1 helper, child slots 120/144")
    j3 = int(helpers[0].args[1], 0)
    r4 = int(runs[3].args[0], 0)
    if r4 != j3 + 4 or int(runs[2].args[1], 0) != j3:
        raise SystemExit(f"{arm.name}: the last two runs must meet the helper call at {j3:#x}")
    op = arm.params["op"]
    spec, hname, cname = E2_HELPER[helpers[0].args[0]]
    argw, lem, rel = E2_CMP[op]
    r3name, r3tail = seg_split(f"{arm.name}T_run3", "h8, h2, h9, h19, hop, hKL, hKR, hsf", runs[2])
    return {"R3NAME": r3name, "R3TAIL": r3tail,
            "ARM": arm.name, "FAMILY": "binOne", "OP": "." + op, "TOK": str(E2_TOK[op]),
            "J3": f"{j3:08x}", "R4": f"{r4:08x}", "RES": "(" + arm.result.strip() + ")",
            "HSPEC": spec, "HNAME": hname, "HELPERC": cname, "ARGW": argw,
            "SUMEQ": f"({argw} != 0#64) = decide ({rel})",
            "SUMPF": f"rw [{lem}, hw1, hu1]"}


FAMILIES_EXT = {"binOne": subst_binOne}


# ------------------------------------------------------------------ partial mode
# `binP`: ONE partial case per operator, closed over every operand outcome. The
# prefix (both children through the Löb hypothesis) is lane G's, lifted to carry
# `errCtx`; after the right child the case splits on the operands' actual kinds
# (a disjunction lemma in `BinArm.lean`), one leftover per row, and `#ix_tree`
# joins the rows. Row kinds: `int1` (a success row whose tail is one helper call;
# its runs are the operator's total case's), `typeErr` (`int_operand`'s type error:
# `value_kind_name`, then `runtime_error`).

E2_TEMPLATES = TEMPLATES  # noqa: F821 (the loader's namespace)

# Per operator: the kind split, the type-error code, the success rows.
#   entry: the operator's arm (the jump table's target)
#   eL/eR: where `bne` sends a non-int left/right operand
#   vkn/rt: the shared `jal value_kind_name` / `jal runtime_error`
#   name: the operator's name string in `.rodata` (address, length)
E2_SEG_HDR = """#ix_seg {name} {{live : Nat → Prop}} (hlive : ∀ p ∈ interpText, live p.1)
    {{Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}} {{m Mt : Mem}} {{R : Nat → BitVec 64}}
    {{aX s sret w1 {kvar} : BitVec 64}}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 32 ≤ 0x100000000)
    (hx3 : aX.toNat + 32 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h8 : R 8 = aX) (h2 : R 2 = s + 18446744073709550528#64) (h9 : R 9 = sret) (h19 : R 19 = w1)
    (hop : ldv .lw m (aX + 8#64).toNat = {tok}#64)
{kfacts} :
    IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x8000351c#64 R Mt
"""

def e2_chain(name, stmt_hdr, facts, stops):
    """A run from `stmt_hdr`'s start state through `stops` (each piece its own
    declaration), joined by `#ix_tree` into `name`."""
    at = lambda pc: f"0x{pc:08x}"
    tac = f"ix_run hlive using [{facts}]"
    if len(stops) == 1:
        return stmt_hdr.replace("{name}", name) + f"  by {tac} at {at(stops[0])}\n"
    out = [stmt_hdr.replace("{name}", f"{name}_1") + f"  by {tac} at {at(stops[0])}\n"]
    for k in range(1, len(stops)):
        out.append(f"#ix_piece {name}_{k + 1} from {name}_{k} by\n  {tac} at {at(stops[k])}\n")
    tree = f"{name}_{len(stops)}"
    for k in range(len(stops) - 1, 0, -1):
        tree = f"{name}_{k} [{tree}]"
    out.append(f"#ix_tree {name} := {tree}\n")
    return "\n".join(out)


def e2_fill(name, subst):
    return fill((E2_TEMPLATES / name).read_text(), subst)  # noqa: F821


E2_HYPS = {
    "valueInt": "    (hvi : ⊢ ∀ p n, valueIntSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p n)\n",
    "valueBool": "    (hvb : ⊢ ∀ p b, valueBoolSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p b)\n",
}
E2_HVK = ("    (hvk : ⊢ ∀ p Mt v, valueKindNameSpec (GF := GF) (vsaModel live) (wpW (vsaModel live)) p Mt v) :\n")

E2_INT_PREP = """  unfold valOf
  icases Hv1 with %⟨hw0, hw1⟩
  icases Hv2 with %⟨hu0, hu1⟩
  have hk0 := ofNat_lo32 hw0
  have hk0' := ofNat_lo32 hu0"""


FAMILIES_WHOLE_EXT: dict = {}


# ------------------------------------------------------------------ `==` / `!=`
# One row in both modes (no kind test): the operands' copies go to
# `value_equal` (`ms_callValueEqual`, `BinEq.lean`), its bit (or its `seqz`) to
# `value_bool`. The total case's prefix is `binT_prefix` over general operand
# values; the partial case's is `binP_prefix` with no split.
E2_EQ = {
    # op: (dispatch entry, jal value_equal, jal value_bool, result, value_bool's word, its proof, bit)
    "eq": (0x800036e4, 0x8000371c, 0x80003728, "(.bool (lv.equal rv'))",
           "if Value.equal lv rv' then 1#64 else 0#64", "ix_reg; exact hr4", "lv.equal rv'"),
    "ne": (0x80003734, 0x8000376c, 0x80003778, "(.bool (!lv.equal rv'))",
           "if Value.equal lv rv' then 0#64 else 1#64",
           "ix_reg; rw [hr4]; cases Value.equal lv rv' <;> decide", "!lv.equal rv'"),
}

E2_RUN_HDR3 = """#ix_seg {name} {{live : Nat → Prop}} (hlive : ∀ p ∈ interpText, live p.1)
    {{Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}} {{m Mt : Mem}} {{R : Nat → BitVec 64}}
    {{aX s sret w1 : BitVec 64}}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 32 ≤ 0x100000000)
    (hx3 : aX.toNat + 32 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h8 : R 8 = aX) (h2 : R 2 = s + 18446744073709550528#64) (h9 : R 9 = sret) (h19 : R 19 = w1)
    (hop : ldv .lw m (aX + 8#64).toNat = {tok}#64) :
    IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x8000351c#64 R Mt
"""


def e2_mid_run(name, start, stop):
    """A short run between two calls: `sret` pinned in `s1`."""
    return f"""#ix_seg {name} {{live : Nat → Prop}} (hlive : ∀ p ∈ interpText, live p.1)
    {{Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}} {{m : Mem}} {{DA : List Nat}} {{Mt : Mem}}
    {{R : Nat → BitVec 64}} {{s sret : BitVec 64}}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h9 : R 9 = sret) :
    IW live m DA (InExt (s.toNat - 1088, 1088)) Q 0x{start:08x}#64 R Mt
  by ix_run hlive using [h9, hsf] at 0x{stop:08x}
"""


def e2_epi_run(name, start):
    """The epilogue from `start`: `ld s3,1048(sp); j 0x800033ec` and the frame's restores."""
    return f"""#ix_seg {name} {{live : Nat → Prop}} (hlive : ∀ p ∈ interpText, live p.1)
    {{Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}} {{m Mt : Mem}} {{R : Nat → BitVec 64}}
    {{aX s ret v8 v9 v18 v19 : BitVec 64}}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hal : ret.toNat % 4 = 0)
    (h2 : R 2 = s + 18446744073709550528#64)
    (hRA : ldv .ld Mt (s + 18446744073709550528#64 + 1080#64).toNat = ret)
    (hS0 : ldv .ld Mt (s + 18446744073709550528#64 + 1072#64).toNat = v8)
    (hS1 : ldv .ld Mt (s + 18446744073709550528#64 + 1064#64).toNat = v9)
    (hS2 : ldv .ld Mt (s + 18446744073709550528#64 + 1056#64).toNat = v18)
    (hS3 : ldv .ld Mt (s + 18446744073709550528#64 + 1048#64).toNat = v19) :
    IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x{start:08x}#64 R Mt
  by ix_run hlive using [h2, hRA, hS0, hS1, hS2, hS3, hsf, hal]
"""


def subst_binEq(arm, mode):
    """Family `binEq` (`==`, `!=`), both modes. Params: `op`."""
    op = arm.params["op"]
    entry, jve, jvb, res, argw, pins, bit = E2_EQ[op]
    tok = E2_TOK[op]
    sub = {"ARM": arm.name, "OP": "." + op, "RES": res, "JVE": f"{jve:08x}", "JVB": f"{jvb:08x}",
           "ARGW": argw, "PINS": pins, "SUMB": bit}
    if mode == "T":
        runs = "\n".join([
            e2_chain(f"{arm.name}T_run3", E2_RUN_HDR3.format(name="{name}", tok=tok),
                     "h8, h2, h9, h19, hop, hsf", [entry, jve]),
            e2_mid_run(f"{arm.name}T_run4", jve + 4, jvb),
            e2_epi_run(f"{arm.name}T_run5", jvb + 4)])
        text = e2_fill("binT_prefix.lean", {
            "IMPORTS": "import VsaIris.Interp.BinEq\n", "ARM": arm.name, "FAMILY": "binEq",
            "OP": "." + op, "ROWDOC": "of any operand kinds", "RUNS": runs,
            "VARS": "{lv rv' : Value}", "LV": "lv", "RV": "rv'", "RES": res, "COST": "nl + nr",
            "KTAIL": "k", "PREP": "",
            "HYPS": ("    (hve : ⊢ ∀ pa pb s a b st B, valueEqualSpec (GF := GF) (vsaModel live) N\n"
                     "      (twpW (vsaModel live)) pa pb s a b st B)\n"
                     "    (hsc : ⊢ strcmpSpecV (GF := GF) (vsaModel live) (twpW (vsaModel live)))\n"
                     "    (hvb : ⊢ ∀ p b, valueBoolSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p b)\n"
                     "    (hni : NativeInj N) :\n")})
        text += "\n" + e2_fill("binEq_T.lean", sub)
        text += (f"\n#ix_chain caseT_{arm.name} := [{arm.name}T_p1, {arm.name}T_p2, {arm.name}T_p3,\n"
                 f"  {arm.name}T_p4, {arm.name}T_p5, {arm.name}T_p6]\n\nend VsaIris.Interp\n")
        return text
    text = e2_fill("binP_prefix.lean", {
        "IMPORTS": f"import VsaIris.Interp.Case.{arm.name}T\n", "ARM": arm.name, "OP": "." + op,
        "ROWSDOC": "one row: `value_equal` takes every pair of kinds", "RUNS": "",
        "HYPS": ("    (hve : ⊢ ∀ pa pb s a b st B, valueEqualSpec (GF := GF) (vsaModel live) N\n"
                 "      (wpW (vsaModel live)) pa pb s a b st B)\n"
                 "    (hsc : ⊢ strcmpSpecV (GF := GF) (vsaModel live) (wpW (vsaModel live)))\n"
                 "    (hvb : ⊢ ∀ p b, valueBoolSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p b)\n"
                 "    (hni : NativeInj N) :\n"),
        "SPLIT": ""})
    text += "\n" + e2_fill("binEq_P.lean", sub)
    text += (f"\n#ix_tree caseP_{arm.name} := {arm.name}P_p1 [{arm.name}P_p2 [{arm.name}P_ok1 "
             f"[{arm.name}P_ok2 [{arm.name}P_ok3 [{arm.name}P_ok4]]]]]\n\nend VsaIris.Interp\n")
    return text


FAMILIES_WHOLE_EXT["binEq"] = subst_binEq


# ------------------------------------------------------------------ string comparisons
# Total mode, the string/string row of `<`, `<=`, `>`, `>=`: `strcmp` (callee spec
# `strcmpOrdSpec`, its result's sign class) and the operator's bit of that sign
# (`str_*_bit`, `BinArm.lean`) into `value_bool`.
E2_STRCMP_JAL = 0x80003b18
E2_STR = {
    # op: (jal value_bool, result, value_bool's word, its reading, the reading's lemma)
    "lt": (0x800036c8, "(.bool (decide (x < y)))", "R3 10 >>> 63", "decide (x < y)", "str_lt_bit"),
    "le": (0x80003b00, "(.bool (decide (x < y) || x == y))", "sltiV (R3 10) 1#64",
           "decide (x < y) || x == y", "str_le_bit"),
    "gt": (0x80003aec, "(.bool (decide (y < x)))", "sltV 0#64 (R3 10)", "decide (y < x)", "str_gt_bit"),
    "ge": (0x800036c8, "(.bool (decide (y < x) || x == y))",
           "(R3 10 ^^^ 0xffffffffffffffff#64) >>> 63", "decide (y < x) || x == y", "str_ge_bit"),
}
E2_CMP_ENTRY = 0x80003628


def e2_str_run3(arm, tok):
    hdr = E2_RUN_HDR3.format(name="{name}", tok=tok).replace(
        f"    (hop : ldv .lw m (aX + 8#64).toNat = {tok}#64) :",
        f"    (hop : ldv .lw m (aX + 8#64).toNat = {tok}#64)\n"
        "    (hKL : ldv .ld Mt (s.toNat - 1088) = 3#64)\n"
        "    (hKR : ldv .lw Mt (s + 18446744073709550528#64 + 144#64).toNat = 3#64) :")
    return e2_chain(f"{arm}T_run3", hdr, "h8, h2, h9, h19, hop, hKL, hKR, hsf",
                    [E2_CMP_ENTRY, E2_STRCMP_JAL])


def e2_str_run4(arm, tok, jvb):
    return f"""#ix_seg {arm}T_run4 {{live : Nat → Prop}} (hlive : ∀ p ∈ interpText, live p.1)
    {{Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}} {{m : Mem}} {{DA : List Nat}} {{Mt : Mem}}
    {{R : Nat → BitVec 64}} {{s sret : BitVec 64}}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h9 : R 9 = sret) (h2 : R 2 = s + 18446744073709550528#64)
    (hop : ldv .ld Mt (s.toNat - 1088) = {tok}#64) :
    IW live m DA (InExt (s.toNat - 1088, 1088)) Q 0x{E2_STRCMP_JAL + 4:08x}#64 R Mt
  by ix_run hlive using [h9, h2, hop, hsf] at 0x{jvb:08x}
"""


def subst_binStr(arm, mode):
    """Family `binStr` (total mode): the string/string row of a comparison.
    Params: `op`."""
    if mode != "T":
        raise NotImplementedError
    op = arm.params["op"]
    jvb, res, argw, bit, lem = E2_STR[op]
    tok = E2_TOK[op]
    runs = "\n".join([e2_str_run3(arm.name, tok), e2_str_run4(arm.name, tok, jvb),
                      e2_epi_run(f"{arm.name}T_run5", jvb + 4)])
    text = e2_fill("binT_prefix.lean", {
        "IMPORTS": "", "ARM": arm.name, "FAMILY": "binStr", "OP": "." + op,
        "ROWDOC": "of two strings", "RUNS": runs, "VARS": "{x y : String}",
        "LV": "(.str x)", "RV": "(.str y)", "RES": res, "COST": "nl + nr", "KTAIL": "k", "PREP": "",
        "HYPS": ("    (hsc : ⊢ strcmpOrdSpec (GF := GF) (vsaModel live) (twpW (vsaModel live)))\n"
                 "    (hvb : ⊢ ∀ p b, valueBoolSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p b) :\n")})
    text += "\n" + e2_fill("binStr_T.lean", {
        "ARM": arm.name, "OP": "." + op, "RES": res, "TOK": str(tok), "JSC": f"{E2_STRCMP_JAL:08x}",
        "JVB": f"{jvb:08x}", "ARGW": argw, "SUMB": bit, "SUMPF": lem})
    text += (f"\n#ix_chain caseT_{arm.name} := [{arm.name}T_p1, {arm.name}T_p2, {arm.name}T_p3,\n"
             f"  {arm.name}T_p4, {arm.name}T_p5]\n\nend VsaIris.Interp\n")
    return text


FAMILIES_WHOLE_EXT["binStr"] = subst_binStr


# ------------------------------------------------------------------ partial mode, per operator
# `binP`: ONE closed partial case per operator. After the right child the case
# splits on the operands' actual kinds (`intRows`/`cmpRows`, `BinArm.lean`), one
# leftover per row in the machine's order of tests, and `#ix_tree` joins the rows:
#   int1     a success row whose tail is one helper (the operator's total run lemmas)
#   str      the string/string row of a comparison (`binP_str`, `strcmp`)
#   typeErr  `int_operand`'s type error: `value_kind_name`, then `runtime_error`

# The kind facts a type-error run is decided by (binder, argument, proof bullet).
E2_KF = {
    "KLv": ("(hKL : ldv .ld Mt (s.toNat - 1088) = kL)", "?_", "ix_fwd; rw [hMt2]; ix_fwd", "hKL"),
    "KL2": ("(hKL : ldv .ld Mt (s.toNat - 1088) = 2#64)", "?_",
            "ix_fwd; rw [hMt2]; ix_fwd; exact ofNat_lo32 htl", "hKL"),
    "KRv": ("(hKR : ldv .lw Mt (s + 18446744073709550528#64 + 144#64).toNat = kR)", "?_", "ix_fwd", "hKR"),
    "KR3": ("(hKR : ldv .lw Mt (s + 18446744073709550528#64 + 144#64).toNat = 3#64)", "?_",
            "ix_fwd; exact ofNat_lo32 htr", "hKR"),
    "kl2": ("(hkl : kL ≠ 2#64)", "(kind_ne_int htl hL)", None, None),
    "kl3": ("(hkl3 : kL + 18446744073709551613#64 ≠ 0#64)", "(kind_ne_str htl hL3)", None, None),
    "kr2": ("(hkr : kR ≠ 2#64)", "(kind_ne_int htr hR)", None, None),
    "kr3": ("(hkr3 : kR + 18446744073709551613#64 ≠ 0#64)", "(kind_ne_str htr hR3)", None, None),
}
# A type-error row's variant: its kind facts, and whose kind name it prints
# (the value, its first word, the word's tag fact, the forwarding to its copy).
E2_TE = {
    "L": (["KLv", "kl2"], "lv"),
    "R": (["KL2", "KRv", "kr2"], "rv'"),
    "La": (["KLv", "kl2", "KRv", "kr3"], "lv"),
    "Lb": (["KLv", "kl2", "kl3", "KR3"], "lv"),
    "Ra": (["KL2", "KRv", "kr2", "kr3"], "rv'"),
    "Rb": (["KL2", "KR3"], "(.str y)"),
}
E2_SIDEW = {"lv": ("w0", "rw [hMt3]; e2_fwd hoff; rw [hMt2]; e2_fwd hoff", "htl"),
            "rv'": ("u0", "rw [hMt3]; e2_fwd hoff", "htr"),
            "(.str y)": ("u0", "rw [hMt3]; e2_fwd hoff", "htr")}

E2_CMP_SPLIT = ("cmpRows",
                "⟨a, b, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩ | ⟨hR3, hL⟩ | ⟨y, rfl, hL, hL3⟩ | "
                "⟨a, rfl, hR, hR3⟩ | ⟨a, y, rfl, rfl⟩",
                "int/int; string/string; a non-int left operand beside a non-string; a non-int, "
                "non-string left operand beside a string; an int beside a non-int, non-string; "
                "an int beside a string")
E2_DIV_SPLIT = ("divRows", "⟨a, b, rfl, rfl, hb0⟩ | ⟨a, rfl, rfl⟩ | hL | ⟨a, rfl, hR⟩",
                "int/int with a nonzero divisor; a zero divisor; a non-int left operand; an int "
                "beside a non-int right operand")
E2_INT_SPLIT = ("intRows", "⟨a, b, rfl, rfl⟩ | hL | ⟨a, rfl, hR⟩",
                "int/int; a non-int left operand; an int beside a non-int right operand")


def e2_cmp_op(op, eL, eR):
    name = {"lt": (0x800195c8, 1), "le": (0x800195d0, 2), "gt": (0x800195d8, 1),
            "ge": (0x80019380, 2)}[op]
    argw, lem, rel = E2_CMP[op]
    trun = f"Binary{op.capitalize()}IntT"
    return dict(entry=E2_CMP_ENTRY, vkn=0x80003e7c, rt=0x80003e98, name=name, rtload=True,
                split=E2_CMP_SPLIT,
                rows=[("ok", "int1", (trun, "valueBool", E2_STR[op][0], argw,
                                      f"({argw} != 0#64) = decide ({rel})", f"rw [{lem}, hw1, hu1]",
                                      "(.bool (decide (" + rel + ")))")),
                      ("st", "str", f"Binary{op.capitalize()}StrT"),
                      ("eL1", "typeErr", ("La", eL)), ("eL2", "typeErr", ("Lb", eL)),
                      ("eR1", "typeErr", ("Ra", eR)), ("eR2", "typeErr", ("Rb", eR))])


E2_POPS = {
    "sub": dict(entry=0x800038e0, vkn=0x80003b7c, rt=0x80003b9c, name=(0x800196e8, 1), rtload=False,
                split=E2_INT_SPLIT,
                rows=[("ok", "int1", ("BinarySubIntT", "valueInt", 0x8000391c, "w1 - u1",
                                      "(w1 - u1).toInt = ((wrap64 (a - b)))",
                                      "rw [toInt_sub_wrap, hw1, hu1]", "(.int ((wrap64 (a - b))))")),
                      ("eL", "typeErr", ("L", 0x80003eec)), ("eR", "typeErr", ("R", 0x80003ec4))]),
    "mul": dict(entry=0x80003834, vkn=0x80003c5c, rt=0x80003c7c, name=(0x80019418, 1), rtload=False,
                split=E2_INT_SPLIT,
                rows=[("ok", "arith", None), ("eL", "typeErr", ("L", 0x80003c80)),
                      ("eR", "typeErr", ("R", 0x80003c38))]),
    "div": dict(entry=0x800037dc, vkn=0x80003f38, rt=0x80003f58, name=(0x80019420, 1), rtload=False,
                split=E2_DIV_SPLIT,
                rows=[("ok", "arith", None), ("z", "zero", (0x80003d14, 0x80019428, 16, "division by zero")),
                      ("eL", "typeErr", ("L", 0x80003f5c)), ("eR", "typeErr", ("R", 0x80003f14))]),
    "mod": dict(entry=0x80003784, vkn=0x80003bf0, rt=0x80003c10, name=(0x80019440, 2), rtload=False,
                split=E2_DIV_SPLIT,
                rows=[("ok", "arith", None), ("z", "zero", (0x80003bc8, 0x80019448, 14, "modulo by zero")),
                      ("eL", "typeErr", ("L", 0x80003c14)), ("eR", "typeErr", ("R", 0x80003bcc))]),
    "lt": e2_cmp_op("lt", 0x80003e9c, 0x80003e54),
    "le": e2_cmp_op("le", 0x80003e9c, 0x80003e54),
    "gt": e2_cmp_op("gt", 0x80003e9c, 0x80003e54),
    "ge": e2_cmp_op("ge", 0x80003e9c, 0x80003e54),
}


def e2_te_run(arm, row, tok, variant, entry, target, vkn):
    kfs, _ = E2_TE[variant]
    kvars = [v for v, key in (("kL", "KLv"), ("kR", "KRv")) if key in kfs]
    binders = "    " + " ".join(E2_KF[k][0] for k in kfs)
    uses = ["h8", "h2", "h9", "h19", "hop"] + [E2_KF[k][3] for k in kfs if E2_KF[k][3]] + ["hsf"]
    hdr = E2_SEG_HDR.format(name="{name}", kvar=" ".join(kvars), tok=tok, kfacts=binders)
    return e2_chain(f"{arm}P_{row}_run", hdr, ", ".join(uses), [entry, target, vkn])


def e2_te_refine(arm, row, variant):
    kfs, _ = E2_TE[variant]
    named = []
    if "KLv" in kfs:
        named.append("(kL := BitVec.ofNat 64 (w0.toNat % 2 ^ 32))")
    if "KRv" in kfs:
        named.append("(kR := BitVec.ofNat 64 (u0.toNat % 2 ^ 32))")
    args = " ".join(E2_KF[k][1] for k in kfs)
    bullets = "".join(f"\n  · {E2_KF[k][2]}" for k in kfs if E2_KF[k][2])
    return (f"  refine {arm}P_{row}_run (aX := aX) (s := s) (sret := sret) (w1 := w1)\n"
            f"    {' '.join(named)} hlive hsf hs' hs2 hs3 hx1 hx2 hx3\n"
            f"    ?_ ?_ ?_ ?_ hn.op {args} ?_\n"
            "  · ix_keep [hkeep2, hkeep1]\n  · ix_keep [hkeep2, hkeep1]\n"
            "  · ix_keep [hkeep2, hkeep1]\n  · ix_keep [hkeep2]" + bullets)


def e2_rt_run2(arm, vkn, rt, rtload):
    facts, binders = ["hsf"], ""
    if rtload:
        facts = ["h2", "hop", "hsf"]
        binders = ("\n    (h2 : R 2 = s + 18446744073709550528#64)"
                   " (hop : ldv .ld Mt (s.toNat - 1088) = opn)")
    return f"""#ix_seg {arm}P_rt_run {{live : Nat → Prop}} (hlive : ∀ p ∈ interpText, live p.1)
    {{Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}} {{m : Mem}} {{DA : List Nat}} {{Mt : Mem}}
    {{R : Nat → BitVec 64}} {{s{" opn" if rtload else ""} : BitVec 64}}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0){binders} :
    IW live m DA (InExt (s.toNat - 1088, 1088)) Q 0x{vkn + 4:08x}#64 R Mt
  by ix_run hlive using [{", ".join(facts)}] at 0x{rt:08x}
"""


def e2_rt_refine(arm, d):
    if not d["rtload"]:
        return f"  refine {arm}P_rt_run hlive hsf hs' hs2 hs3 ?_"
    return (f"  have hop4 : ldv .ld M4 (s.toNat - 1088) = 0x{d['name'][0]:08x}#64 := by\n"
            "    rw [ldv_agree (fun j hj => hag4 _ (by simp only [VsaIris.InExt]; omega))]\n"
            "    rw [hMt3]; e2_fwd hoff\n"
            f"  refine {arm}P_rt_run (opn := 0x{d['name'][0]:08x}#64) hlive hsf hs' hs2 hs3 ?_ hop4 ?_\n"
            "  · ix_keep [hkeep4, hkeep2, hkeep1]")


def subst_binP(arm, mode):
    """Family `binP` (partial mode only): see the section comment. Params: `op`."""
    if mode != "P":
        raise NotImplementedError
    op = arm.params["op"]
    d = E2_POPS[op]
    tok = E2_TOK[op]
    runs, pieces, tree, imports = [], [], [], []
    hyps = ["    (hE : ErrEnv (GF := GF) N L Room inp live Core)\n"]
    for k, (row, kind, spec) in enumerate(d["rows"], start=1):
        if kind == "int1":
            trun, helper, j3, argw, sumeq, sumpf, res = spec
            imports.append(f"import VsaIris.Interp.Case.{trun}\n")
            hspec, hname, cname = E2_HELPER[helper]
            hyps.append(E2_HYPS[helper])
            pieces.append(e2_fill("binP_int1.lean", {
                "ARM": arm.name, "OP": "." + op, "ROW": row, "K": str(k), "TRUN": trun,
                "HELPERC": cname, "HNAME": hname, "HSPEC": hspec, "J3": f"{j3:08x}",
                "ARGW": argw, "SUMEQ": sumeq, "SUMPF": sumpf, "RES": res}))
            tree.append(f"{arm.name}P_{row}1 [{arm.name}P_{row}2]")
        elif kind == "str":
            imports.append(f"import VsaIris.Interp.Case.{spec}\n")
            hyps.append("    (hsc : ⊢ strcmpOrdSpec (GF := GF) (vsaModel live) (wpW (vsaModel live)))\n")
            jvb, res, argw, bit, lem = E2_STR[op]
            pieces.append(e2_fill("binP_str.lean", {
                "ARM": arm.name, "OP": "." + op, "ROW": row, "K": str(k), "STRT": spec, "RES": res,
                "TOK": str(tok), "JSC": f"{E2_STRCMP_JAL:08x}", "JVB": f"{jvb:08x}", "ARGW": argw,
                "SUMB": bit, "SUMPF": lem}))
            tree.append(f"{arm.name}P_{row}1 [{arm.name}P_{row}2 [{arm.name}P_{row}3]]")
        elif kind == "arith":
            trun = f"Binary{op.capitalize()}IntT"
            imports.append(f"import VsaIris.Interp.Case.{trun}\n")
            hyps.append(E2_HYPS["valueInt"])
            (jl, lib, nkeep, lx, ly, b10, b11, j3, res, resi, sumpf, zero) = E2_ARITH[op]
            pieces.append(e2_fill("binP_arith.lean", {
                "ARM": arm.name, "OP": "." + op, "ROW": row, "K": str(k), "TRUN": trun, "RES": res,
                "HSPEC": "valueIntSpec", "HNAME": "hvi", "HELPERC": "value_int", "J3": f"{j3:08x}",
                "ZEROHOLE": " ?_" if zero else "",
                "ZEROBULLET": ("\n  · ix_fwd; exact fun h => hb0 (by rw [← hu1, h]; rfl)" if zero else ""),
                "JL": f"{jl:08x}", "LIBIW": lib, "LX": lx, "LY": ly, "RETA": f"{jl + 4:08x}",
                "LIBHY": ("(fun h => hb0 (by rw [← hu1, h]; rfl)) " if zero else ""),
                "B10": b10, "B11": b11, "KEEPARGS": " ".join(["(by decide)"] * nkeep),
                "RESI": resi, "SUMPF": sumpf,
                "EVPF": "(by simp [binOpSem, hb0])" if zero else "rfl"}))
            tree.append(f"{arm.name}P_{row}1 [{arm.name}P_{row}2]")
        elif kind == "zero":
            rtz, fmt, flen, msg = spec
            kf = ("    (hKL : ldv .ld Mt (s.toNat - 1088) = 2#64)\n"
                  "    (hKR : ldv .lw Mt (s + 18446744073709550528#64 + 144#64).toNat = 2#64)\n"
                  "    (hZ : ldv .ld Mt (s + 18446744073709550528#64 + 152#64).toNat = 0#64)")
            hdr = E2_SEG_HDR.format(name="{name}", kvar="", tok=tok, kfacts=kf)
            runs.append(e2_chain(f"{arm.name}P_{row}_run", hdr,
                                 "h8, h2, h9, h19, hop, hKL, hKR, hZ, hsf", [d["entry"], rtz]))
            pieces.append(e2_fill("binP_zero.lean", {
                "ARM": arm.name, "OP": "." + op, "ROW": row, "K": str(k), "MSG": msg,
                "RT": f"{rtz:08x}", "FMT": f"{fmt:08x}", "FLEN": str(flen)}))
            tree.append(f"{arm.name}P_{row}1")
        else:
            variant, target = spec
            runs.append(e2_te_run(arm.name, row, tok, variant, d["entry"], target, d["vkn"]))
            v = E2_TE[variant][1]
            w0, hw64, htag = E2_SIDEW[v]
            pieces.append(e2_fill("binP_typeErr.lean", {
                "ARM": arm.name, "OP": "." + op, "ROW": row, "K": str(k),
                "ROWDOC": f"type error ({variant})", "REFINE": e2_te_refine(arm.name, row, variant),
                "W0": w0, "HW64": hw64, "HTAG": htag, "V": v, "VKN": f"{d['vkn']:08x}",
                "RT": f"{d['rt']:08x}", "OPNAME": f"{d['name'][0]:08x}", "OPLEN": str(d["name"][1]),
                "RTREFINE": e2_rt_refine(arm.name, d)}))
            tree.append(f"{arm.name}P_{row}1 [{arm.name}P_{row}2 [{arm.name}P_{row}3]]")
    runs.append(e2_rt_run2(arm.name, d["vkn"], d["rt"], d["rtload"]))
    # the helper hypotheses in a fixed order (the spec binders of every row, deduplicated)
    hyps = list(dict.fromkeys(hyps)) + [E2_HVK]
    lemma, pat, doc = d["split"]
    split = (f"  -- the rows ({doc})\n  rcases {lemma} lv rv' with {pat}\n" + E2_INT_PREP)
    text = e2_fill("binP_prefix.lean", {
        "IMPORTS": "".join(dict.fromkeys(imports)), "ARM": arm.name, "OP": "." + op,
        "ROWSDOC": doc, "RUNS": "\n".join(runs), "HYPS": "".join(hyps), "SPLIT": split})
    text += "\n" + "\n".join(pieces)
    text += (f"\n#ix_tree caseP_{arm.name} := {arm.name}P_p1 [{arm.name}P_p2 [\n  "
             + ",\n  ".join(tree) + "]]\n\nend VsaIris.Interp\n")
    return text


FAMILIES_WHOLE_EXT["binP"] = subst_binP


# ------------------------------------------------------------------ `*`, `/`, `%`, total mode
# `binArith`: the int/int row whose operation is libgcc's (`ProofArith.lean`),
# followed inside the arm's run (`iw_jal` + the routine's continuation lemma),
# then `value_int`.
E2_ARITH = {
    # op: (jal libgcc, its lemma, its keep-argument proofs, a0 := , a1 :=, proofs of the two
    #      argument pins, jal value_int, result, reading of the word, zero check?)
    "mul": (0x80003870, "mul_iw", 4, "u1", "w1", "ix_reg; ix_fwd", "ix_reg; ix_keep [hkeep2]",
            0x8000387c, "(.int ((wrap64 (a * b))))", "(wrap64 (a * b))",
            "rw [hq, toInt_mul_wrap, hw1, hu1, Int.mul_comm]", False),
    "div": (0x8000381c, "divdi3_iw", 6, "w1", "u1", "ix_reg; ix_keep [hkeep2]", "ix_reg; ix_fwd",
            0x80003828, "(.int ((wrap64 (a.tdiv b))))", "(wrap64 (a.tdiv b))", "rw [hq, hw1, hu1]", True),
    "mod": (0x800037c4, "moddi3_iw", 6, "w1", "u1", "ix_reg; ix_keep [hkeep2]", "ix_reg; ix_fwd",
            0x800037d0, "(.int ((wrap64 (a.tmod b))))", "(wrap64 (a.tmod b))", "rw [hq, hw1, hu1]", True),
}
E2_ARITH_ENTRY = {"mul": 0x80003834, "div": 0x800037dc, "mod": 0x80003784}


def subst_binArith(arm, mode):
    """Family `binArith` (total mode): `*`, `/`, `%` on two ints. Params: `op`."""
    if mode != "T":
        raise NotImplementedError
    op = arm.params["op"]
    (jl, lib, nkeep, lx, ly, b10, b11, j3, res, resi, sumpf, zero) = E2_ARITH[op]
    reta = jl + 4
    runs = run_steps(arm)
    r3name, r3tail = seg_split(f"{arm.name}T_run3",
                               "h8, h2, h9, h19, hop, hKL, hKR, hsf", runs[2])
    run3b = e2_mid_run(f"{arm.name}T_run3b", reta, j3).replace(f"#ix_seg {arm.name}T_run3b", f"\n#ix_seg {arm.name}T_run3b")
    keepargs = " ".join(["(by decide)"] * nkeep)
    hb0 = "\n    (hb0 : b ≠ 0)" if zero else ""
    return {
        "R3NAME": r3name, "R3TAIL": r3tail, "RUN3B": run3b, "ARM": arm.name, "OP": "." + op,
        "TOK": str(E2_TOK[op]), "J3": f"{j3:08x}", "R4": f"{j3 + 4:08x}", "RES": res,
        "HSPEC": "valueIntSpec", "HNAME": "hvi", "HELPERC": "value_int",
        "HBBIND": ("\n    (hb : ldv .ld Mt (s + 18446744073709550528#64 + 152#64).toNat ≠ 0#64)"
                   if zero else ""),
        "ZEROHOLE": " ?_" if zero else "",
        "ZEROBULLET": ("\n  · ix_fwd; exact fun h => hb0 (by rw [← hu1, h]; rfl)" if zero else ""),
        "JL": f"{jl:08x}", "LIBIW": lib, "LX": lx, "LY": ly, "RETA": f"{reta:08x}",
        "LIBHY": ("(fun h => hb0 (by rw [← hu1, h]; rfl)) " if zero else ""),
        "B10": b10, "B11": b11, "KEEPARGS": keepargs, "RESI": resi, "SUMPF": sumpf, "HB0": hb0}


FAMILIES_EXT["binArith"] = subst_binArith
