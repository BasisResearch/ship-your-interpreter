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
E2_POPS = {
    "sub": dict(entry=0x800038e0, eL=0x80003eec, eR=0x80003ec4, vkn=0x80003b7c, rt=0x80003b9c,
                name=(0x800196e8, 1),
                ok=("int1", "BinarySubIntT", "valueInt", 0x8000391c, "w1 - u1",
                    "(w1 - u1).toInt = ((wrap64 (a - b)))", "rw [toInt_sub_wrap, hw1, hu1]",
                    "(.int ((wrap64 (a - b))))")),
}

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

E2_KFACTS = {
    "L": ("kL", "    (hKL : ldv .ld Mt (s.toNat - 1088) = kL) (hkl : kL ≠ 2#64)",
          "h8, h2, h9, h19, hop, hKL, hsf"),
    "R": ("kR", "    (hKL : ldv .ld Mt (s.toNat - 1088) = 2#64)\n"
                "    (hKR : ldv .lw Mt (s + 18446744073709550528#64 + 144#64).toNat = kR) (hkr : kR ≠ 2#64)",
          "h8, h2, h9, h19, hop, hKL, hKR, hsf"),
}


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


def e2_rt_run(arm, vkn, rt):
    return f"""#ix_seg {arm}P_rt_run {{live : Nat → Prop}} (hlive : ∀ p ∈ interpText, live p.1)
    {{Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}} {{m : Mem}} {{DA : List Nat}} {{Mt : Mem}}
    {{R : Nat → BitVec 64}} {{s : BitVec 64}}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0) :
    IW live m DA (InExt (s.toNat - 1088, 1088)) Q 0x{vkn + 4:08x}#64 R Mt
  by ix_run hlive using [hsf] at 0x{rt:08x}
"""


def e2_fill(name, subst):
    return fill((E2_TEMPLATES / name).read_text(), subst)  # noqa: F821


E2_REFINE = {
    "L": """  refine {arm}P_{row}_run (aX := aX) (s := s) (sret := sret) (w1 := w1)
    (kL := BitVec.ofNat 64 (w0.toNat % 2 ^ 32)) hlive hsf hs' hs2 hs3 hx1 hx2 hx3
    ?_ ?_ ?_ ?_ hn.op ?_ (kind_ne_int htl hL) ?_
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2]
  · ix_fwd; rw [hMt2]; ix_fwd""",
    "R": """  refine {arm}P_{row}_run (aX := aX) (s := s) (sret := sret) (w1 := w1)
    (kR := BitVec.ofNat 64 (u0.toNat % 2 ^ 32)) hlive hsf hs' hs2 hs3 hx1 hx2 hx3
    ?_ ?_ ?_ ?_ hn.op ?_ ?_ (kind_ne_int htr hR) ?_
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2, hkeep1]
  · ix_keep [hkeep2]
  · ix_fwd; rw [hMt2]; ix_fwd; exact ofNat_lo32 htl
  · ix_fwd""",
}
E2_SIDE = {
    "L": ("w0", "rw [hMt3]; e2_fwd hoff; rw [hMt2]; e2_fwd hoff", "htl", "lv",
          "the left operand is not an int"),
    "R": ("u0", "rw [hMt3]; e2_fwd hoff", "htr", "rv'",
          "the right operand is not an int"),
}

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


def subst_binP(arm, mode):
    """Family `binP` (partial mode only): see the section comment. Params: `op`."""
    if mode != "P":
        raise NotImplementedError
    op = arm.params["op"]
    d = E2_POPS[op]
    tok = E2_TOK[op]
    rows = [("ok", d["ok"]), ("eL", "L"), ("eR", "R")]
    runs, pieces, tree, imports = [], [], [], []
    hyps = ["    (hE : ErrEnv (GF := GF) N L Room inp live Core)\n"]
    for k, (row, spec) in enumerate(rows, start=1):
        if row == "ok":
            kind, trun, helper, j3, argw, sumeq, sumpf, res = spec
            imports.append(f"import VsaIris.Interp.Case.{trun}\n")
            hspec, hname, cname = E2_HELPER[helper]
            hyps.append(E2_HYPS[helper])
            pieces.append(e2_fill("binP_int1.lean", {
                "ARM": arm.name, "OP": "." + op, "ROW": row, "K": str(k), "TRUN": trun,
                "HELPERC": cname, "HNAME": hname, "HSPEC": hspec, "J3": f"{j3:08x}",
                "ARGW": argw, "SUMEQ": sumeq, "SUMPF": sumpf, "RES": res}))
            tree.append(f"{arm.name}P_{row}1 [{arm.name}P_{row}2]")
        else:
            side = spec
            kvar, kfacts, facts = E2_KFACTS[side]
            hdr = E2_SEG_HDR.format(name="{name}", kvar=kvar, tok=tok, kfacts=kfacts)
            runs.append(e2_chain(f"{arm.name}P_{row}_run", hdr, facts,
                                 [d["entry"], d["e" + side], d["vkn"]]))
            w0, hw64, htag, v, doc = E2_SIDE[side]
            pieces.append(e2_fill("binP_typeErr.lean", {
                "ARM": arm.name, "OP": "." + op, "ROW": row, "K": str(k), "ROWDOC": doc,
                "REFINE": E2_REFINE[side].format(arm=arm.name, row=row),
                "W0": w0, "HW64": hw64, "HTAG": htag, "V": v, "VKN": f"{d['vkn']:08x}",
                "RT": f"{d['rt']:08x}", "OPNAME": f"{d['name'][0]:08x}", "OPLEN": str(d["name"][1])}))
            tree.append(f"{arm.name}P_{row}1 [{arm.name}P_{row}2 [{arm.name}P_{row}3]]")
    runs.append(e2_rt_run(arm.name, d["vkn"], d["rt"]))
    hyps.append(E2_HVK)
    split = ("  -- the rows: int/int, the left operand not an int, the right one not an int\n"
             "  rcases intRows lv rv' with ⟨a, b, rfl, rfl⟩ | hL | ⟨a, rfl, hR⟩\n" + E2_INT_PREP)
    text = e2_fill("binP_prefix.lean", {
        "IMPORTS": "".join(dict.fromkeys(imports)), "ARM": arm.name, "OP": "." + op,
        "ROWSDOC": "int/int, a non-int left operand, a non-int right operand",
        "RUNS": "\n".join(runs), "HYPS": "".join(hyps), "SPLIT": split})
    text += "\n" + "\n".join(pieces)
    text += (f"\n#ix_tree caseP_{arm.name} := {arm.name}P_p1 [{arm.name}P_p2 [\n  "
             + ",\n  ".join(tree) + "]]\n\nend VsaIris.Interp\n")
    return text


FAMILIES_WHOLE_EXT = {"binP": subst_binP}


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
