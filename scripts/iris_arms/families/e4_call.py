# Lane E4: the call arm's case families (INTERP_DESIGN.md §6, §8 row "call").
# Loaded by gen_iris_cases.py (`FAMILIES_EXT`); rows in scripts/iris_arms/arms.d/e4-call.tsv.
# The arm's code is proved once in the shared layer (`VsaIris/Interp/Call*.lean`:
# the prefix `callPrefixT`/`callPrefixP`, the native tails, the errors, the
# closure tail); a case composes it with the row's semantic rule.

# The printing natives: spec, its `natOutSpec` form, entry, stack need, the
# printed text as a function of (store, arguments, console), and the console
# the rule reaches.
E4_OUT = {
    "print": ("nativePrintSpec", "nativePrintPC", "nativePrintNeed",
              "fun st vs o => o ++ printArgs st vs", "st2.out ++ printArgs st2.store vs"),
    "println": ("nativePrintlnSpec", "nativePrintlnPC", "nativePrintlnNeed",
                "fun st vs o => o ++ printArgs st vs ++ \"\\n\"",
                "st2.out ++ printArgs st2.store vs ++ \"\\n\""),
}


def e4_check(arm, mode):
    ops = [s.op for s in arm.steps]
    if ops[:3] != ["run", "child", "run"] or "loop" not in ops:
        raise SystemExit(f"{arm.name}: a call row starts run, child (the callee), run, loop (the arguments)")


def subst_callOut(arm, mode):
    """Family `callOut`: a printing native (`nf=print|println`)."""
    e4_check(arm, mode)
    if mode != "T":
        raise NotImplementedError(arm.name)
    nf = arm.params["nf"]
    spec, pc, need, out, outv = E4_OUT[nf]
    return {"ARM": arm.name, "NF": nf, "SPEC": spec, "PC": pc, "NEED": need, "OUT": out, "OUTV": outv}


def subst_callAssert(arm, mode):
    """Family `callAssert`: `assert` returning (`Call.assertOk`)."""
    e4_check(arm, mode)
    if mode != "T":
        raise NotImplementedError(arm.name)
    return {"ARM": arm.name}


def subst_callArm(arm, mode):
    """Family `callArm`: the whole call arm in partial mode (every outcome)."""
    e4_check(arm, mode)
    if mode != "P":
        raise NotImplementedError(arm.name)
    return {"ARM": arm.name}


FAMILIES_EXT = {"callOut": subst_callOut, "callAssert": subst_callAssert, "callArm": subst_callArm}
