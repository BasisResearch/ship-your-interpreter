"""Lane E3's case families (loaded by `scripts/gen_iris_cases.py`, which
provides `run_steps`, `Arm` and `Step`): the logical and unary arms of
`eval_expr`. Rows: `scripts/iris_arms/arms.d/e3-logical.tsv`."""
# ------------------------------------------------------------------ lane E3 families
# The logical (`EX_LOGICAL`, tag 7) and unary (`EX_UNARY`, tag 8) arms. The
# shared code (prologue and dispatch, the `value_truthy`/`value_bool` tail at
# 0x800035cc-0x800035dc, the epilogue) is literal in the templates; the
# functions below read the row-specific PCs off the steps and check the rest.
def _pcs(arm: Arm, op: str) -> list[int]:
    return [int(s.args[1], 0) for s in arm.steps if s.op == op]


def _starts(arm: Arm) -> list[int]:
    return [int(s.args[0], 0) for s in run_steps(arm)]


def _need(arm: Arm, ok: bool, what: str) -> None:
    if not ok:
        raise SystemExit(f"{arm.name}: family {arm.family}: {what}")


def _meet(arm: Arm) -> None:
    """Each run after a call starts right after that call's `jal`."""
    calls = [int(s.args[1], 0) for s in arm.steps if s.op in ("child", "helper", "abort")]
    starts = _starts(arm)[1:]
    _need(arm, [c + 4 for c in calls][:len(starts)] == starts and len(calls) - len(starts) <= 1,
          "each run must start after the previous call")


def subst_unNot(arm: Arm, mode: str) -> dict[str, str]:
    """Family `unNot`: `!e` (operand; `value_truthy` on its copy; `seqz`;
    `value_bool`)."""
    _meet(arm)
    _need(arm, _pcs(arm, "child") == [0x800035E8] and _pcs(arm, "helper") == [0x80003614, 0x80003620],
          "the operand at 0x800035e8, value_truthy at 0x80003614, value_bool at 0x80003620")
    return {"ARM": arm.name}


def subst_unNeg(arm: Arm, mode: str) -> dict[str, str]:
    """Family `unNeg`: `-e` on an int (operand; kind test; `neg`; `value_int`).
    Partial mode exports the non-int operand (the type-error row)."""
    _meet(arm)
    _need(arm, _pcs(arm, "child") == [0x800035E8] and _pcs(arm, "helper") == [0x800039D8],
          "the operand at 0x800035e8, value_int at 0x800039d8")
    return {"ARM": arm.name}


def _logCommon(arm: Arm) -> dict[str, str]:
    p = arm.params
    _meet(arm)
    _need(arm, _pcs(arm, "child")[0] == 0x80003568 and arm.children[0].slot == 120,
          "the left operand at 0x80003568 into sp+120")
    h = _pcs(arm, "helper")
    return {"ARM": arm.name, "LOP": p["lop"], "TRU": p["tru"], "TOK": p["tok"], "CTOR": p["ctor"],
            "BIT": "1" if p["tru"] == "true" else "0", "J2": f"{h[0]:08x}",
            "R3": f"{_starts(arm)[2]:08x}"}


def subst_logLong(arm: Arm, mode: str) -> dict[str, str]:
    """Family `logLong`: `l && r` with `l` truthy, `l || r` with `l` falsy
    (both operands, `value_truthy` on each copy, `value_bool`). Partial mode
    exports the other truthiness (the `logShort` row)."""
    d = _logCommon(arm)
    h, c = _pcs(arm, "helper"), _pcs(arm, "child")
    _need(arm, len(c) == 2 and h[1:] == [0x800035CC, 0x800035D8],
          "two operands; the shared tail value_truthy 0x800035cc, value_bool 0x800035d8")
    d.update({"J3": f"{c[1]:08x}", "SR": str(arm.children[1].slot), "R4": f"{_starts(arm)[3]:08x}"})
    return d


def subst_logShort(arm: Arm, mode: str) -> dict[str, str]:
    """Family `logShort`: `l && r` with `l` falsy, `l || r` with `l` truthy
    (left operand, `value_truthy`, `value_bool` of the constant). Params
    `from` (the `logLong` row whose export this row continues) and `opn` (the
    name of the operator's closed partial case)."""
    d = _logCommon(arm)
    h = _pcs(arm, "helper")
    _need(arm, len(_pcs(arm, "child")) == 1 and len(h) == 2, "one operand, two helpers")
    res = arm.result.removeprefix(".bool ").strip()
    _need(arm, res in ("true", "false"), "the result is a constant bool")
    d.update({"J3": f"{h[1]:08x}", "R4": f"{_starts(arm)[3]:08x}", "RES": res,
              "RB": "1" if res == "true" else "0", "LONG": arm.params["from"],
              "OPN": arm.params["opn"]})
    return d


def subst_unNegType(arm: Arm, mode: str) -> dict[str, str]:
    """Family `unNegType` (partial mode only): `-e` on a non-int operand
    (operand; failed kind test; `value_kind_name` on its copy; `runtime_error`,
    which aborts). Params `from` (the `unNeg` row whose export this row
    continues) and `opn` (the name of the operator's closed partial case)."""
    _meet(arm)
    _need(arm, _pcs(arm, "child") == [0x800035E8] and arm.steps[-1].op == "abort",
          "the operand at 0x800035e8; the last step is the runtime_error call")
    kn = _pcs(arm, "helper")
    _need(arm, len(kn) == 1, "one helper (value_kind_name)")
    return {"ARM": arm.name, "FROM": arm.params["from"], "OPN": arm.params["opn"],
            "J2": f"{kn[0]:08x}", "R3": f"{_starts(arm)[2]:08x}",
            "J3": f"{int(arm.steps[-1].args[1], 0):08x}"}


FAMILIES_EXT = {"unNegType": subst_unNegType, "unNot": subst_unNot, "unNeg": subst_unNeg, "logLong": subst_logLong,
                "logShort": subst_logShort}

