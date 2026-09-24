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
