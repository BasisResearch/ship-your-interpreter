#!/usr/bin/env bash
# check_all.sh — the CI gate for the Vsa Lean development.
#
# Usage: scripts/check_all.sh [--skip-build]
#
# Stages (all must pass; exits nonzero with a message on the first failure):
#   (a) `lake build`                — the full tree compiles
#                                     (skipped with --skip-build, e.g. when
#                                     another process owns the build lock and
#                                     oleans are known-fresh);
#   (b) grep gate                   — no `sorry`, no `native_decide`, and no
#                                     `axiom` declarations anywhere under Vsa/
#                                     or in Vsa.lean.  Comments/docstrings and
#                                     string literals are stripped first, so
#                                     "NO sorry/native_decide" prose is fine;
#   (c) `#print axioms`             — every key top-level spec theorem depends
#                                     only on {propext, Classical.choice,
#                                     Quot.sound}.  Extend THEOREMS below as
#                                     capstones land (e.g. ssprint_iov2_spec
#                                     once SnprintfSpec20 is wired into
#                                     Vsa.lean).
#
# Dependencies: bash, grep, python3, lake/lean (elan toolchain).

set -uo pipefail
cd "$(dirname "$0")/.." || exit 2

SKIP_BUILD=0
for arg in "$@"; do
  case "$arg" in
    --skip-build) SKIP_BUILD=1 ;;
    -h|--help) echo "usage: $0 [--skip-build]"; exit 0 ;;
    *) echo "usage: $0 [--skip-build]" >&2; exit 2 ;;
  esac
done

fail() { echo "check_all: FAIL: $*" >&2; exit 1; }

# ---------------------------------------------------------------- (a) build
if [ "$SKIP_BUILD" -eq 0 ]; then
  echo "== stage a: lake build"
  lake build || fail "stage a: lake build failed"
else
  echo "== stage a: lake build SKIPPED (--skip-build)"
fi

# ------------------------------------------------------------ (b) grep gate
echo "== stage b: sorry / native_decide / axiom gate"
python3 - <<'PYEOF' || fail "stage b: forbidden token(s) found (see above)"
import pathlib, re, sys

files = sorted(pathlib.Path("Vsa").rglob("*.lean"))
if pathlib.Path("Vsa.lean").exists():
    files.append(pathlib.Path("Vsa.lean"))

def strip_comments_and_strings(src: str) -> str:
    """Blank out line comments (`--`), (nested) block comments (`/- -/`,
    incl. `/--`/`/-!` docstrings) and string literals, preserving newlines
    so line numbers survive."""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if depth > 0:
            if src.startswith("/-", i):
                depth += 1; i += 2; continue
            if src.startswith("-/", i):
                depth -= 1; i += 2; continue
            out.append("\n" if src[i] == "\n" else " "); i += 1; continue
        if src.startswith("/-", i):
            depth = 1; i += 2; continue
        if src.startswith("--", i):
            while i < n and src[i] != "\n":
                i += 1
            continue
        if src[i] == '"':
            out.append(" "); i += 1
            while i < n:
                if src[i] == "\\":
                    i += 2; continue
                if src[i] == '"':
                    i += 1; break
                out.append("\n" if src[i] == "\n" else " "); i += 1
            continue
        out.append(src[i]); i += 1
    return "".join(out)

bad = []
for f in files:
    code = strip_comments_and_strings(f.read_text(encoding="utf-8"))
    for lineno, line in enumerate(code.splitlines(), 1):
        for tok in ("sorry", "native_decide"):
            if re.search(rf"\b{tok}\b", line):
                bad.append(f"{f}:{lineno}: forbidden `{tok}`")
        if re.match(r"\s*axiom\b", line):
            bad.append(f"{f}:{lineno}: `axiom` declaration")
print(f"stage b: scanned {len(files)} .lean files")
if bad:
    print("\n".join(bad), file=sys.stderr)
    sys.exit(1)
PYEOF
echo "stage b: OK"

# ------------------------------------------------------- (c) #print axioms
echo "== stage c: #print axioms on the key spec theorems"
THEOREMS=(
  # strlen family (StrlenSpec / StrlenSpecU)
  Vsa.Sim.strlen_spec
  Vsa.Sim.strlen_full_spec
  # strcpy capstone (StrcpySpec)
  Vsa.Sim.strcpy_bytehead_from_head
  # newlib memmove forward path (SnprintfSpec18)
  Vsa.Sim.memmove_fwd_spec
  # __ssputs_r fast path (SnprintfSpec19)
  Vsa.Sim.ssputs_fast_spec
  # env_get HIT tail + found composition (EnvGetSpec6)
  Vsa.Sim.env_get_hit_tail
  Vsa.Sim.env_get_found_spec
  # snprintf %lld pipeline capstones
  Vsa.Sim.decimalLoop_spec                      # SnprintfSpec3
  Vsa.Sim.entryToDigits_spec                    # SnprintfSpec5
  Vsa.Sim.signToDigits_neg_spec                 # SnprintfSpec6
  Vsa.Sim.exitToPrint_spec                      # SnprintfSpec7
  Vsa.Sim.entryToPrint_neg_default_width_spec   # SnprintfSpec8
  Vsa.Sim.parseToPrintEntry_spec                # SnprintfSpec16
  Vsa.Sim.parseToPrint_neg_default_width_spec   # SnprintfSpec16
  Vsa.Sim.iov2ToSsprintCall_spec                # SnprintfSpec17
  Vsa.Sim.ssprint_iov2_spec                     # SnprintfSpec20
  Vsa.Sim.svfprintf_flushReturn_spec            # SnprintfSpec25 (flush return path)
  Vsa.Sim.iov2ToSvfprintfRet_spec               # SnprintfSpec26 (0x800078ac → svfprintf ret)
  Vsa.Sim.svfPrologue_spec                      # SnprintfSpec35 (0x80007654 → 0x80007728)
  Vsa.Sim.svfPrologueParse_spec                 # SnprintfSpec36 (0x80007654 → 0x80008534)
  Vsa.Sim.svfEntryToSsprintCall_spec            # SnprintfSpec37 (0x80007654 → 0x8000e908, PreSr)
  Vsa.Sim.svfprintf_lld_spec                    # SnprintfSpec38 (FULL svfprintf: ABI entry → ret, a0 = 1+n2)
  Vsa.Sim.svfprintf_buffer_eq_intToString       # SnprintfSpec39 (byte list = intToString.toUTF8)
  Vsa.Sim.svfprintf_lld_intToString_spec        # SnprintfSpec39 (svfprintf byte-for-byte capstone)
  Vsa.Sim.snprintfPreCall_spec                  # SnprintfSpec40 (snprintf entry → jal _svfprintf_r)
  Vsa.Sim.snprintfPostCall_spec                 # SnprintfSpec41 (svfprintf return → snprintf ret + NUL)
  Vsa.Sim.snprintf_lld_spec                     # SnprintfSpec42 (WRAPPER CAPSTONE: snprintf ABI entry → ret, buffer = intToString.toUTF8 ++ [0]; ALL v < 0)
  Vsa.Sim.fastToPrint_neg_spec                  # SnprintfSpec43 (single-digit fast path, neg arm: 0x80008100 → 0x8000782c)
  Vsa.Sim.entryToPrint_neg_any_spec             # SnprintfSpec44 (0x800080e4 → 0x8000782c, ANY negative magnitude)
  Vsa.Sim.entryToPrintNN_fast_spec              # SnprintfSpec45 (NONNEG single-digit arm: 0x800080e4 → 0x8000782c, no sign iovec)
  Vsa.Sim.exitToPrintNN_spec                    # SnprintfSpec46 (exit-restore + hops, NONNEG: beqz t5 taken, a6 = len)
  Vsa.Sim.armEntryNN_spec                       # SnprintfSpec47 (nonneg arm entry: 0x800080e4 → 0x80008100)
  Vsa.Sim.entryToPrintNN_any_spec               # SnprintfSpec48 (NONNEG arm, ANY magnitude → PRINT entry)
  Vsa.Sim.printToSsprintNN_spec                 # SnprintfSpec49 (1-iovec PRINT segment: 0x8000782c → 0x8000e908)
  Vsa.Sim.ssprint_iov1_spec                     # SnprintfSpec50 (__ssprint_r 1-iovec flush, ONE iteration)
  Vsa.Sim.svfprintf_flushReturn1_spec           # SnprintfSpec51 (1-iovec flush + return path → svfprintf ret)
  Vsa.Sim.svfEntryToSsprintCallNN_spec          # SnprintfSpec52 (0x80007654 → 0x8000e908, PreSr1, NONNEG)
  Vsa.Sim.svfprintf_lld_nn_spec                 # SnprintfSpec53 (FULL svfprintf, NONNEG: a0 = n1, digits only)
  Vsa.Sim.svfprintf_buffer_eq_intToString_nn    # SnprintfSpec54 (nonneg byte list = intToString.toUTF8)
  Vsa.Sim.snprintf_lld_nn_spec                  # SnprintfSpec54 (WRAPPER, NONNEG: buffer = intToString.toUTF8 ++ [0])
  Vsa.Sim.snprintf_lld_total_spec               # SnprintfSpec55 (THE TOTAL CAPSTONE: ALL v : BitVec 64)
  # M4 AST-transport (AstTransport) — ExprRepr/StmtRepr survive memory agreement over the AST footprint
  Vsa.Sim.exprRepr_agreeP                       # AstTransport (ExprRepr m a e → AgreeP over ExprFp → ExprRepr m' a e)
  Vsa.Sim.stmtRepr_agreeP                       # AstTransport (StmtRepr analog; recurses through ExprFp / StmtArrayFp)
  # M4 recursive-case glue (EvalRecCommon / EvalNegSim)
  Vsa.Sim.armTail_rec                           # EvalRecCommon (jal eval_expr ≫ IH ⇒ SubEvalReturn)
  Vsa.Sim.blockB_unary                          # EvalNegSim (EX_UNARY arm head + recursive call, IH-composed)
  Vsa.Sim.blockC_neg                            # EvalNegSim2 (neg post-call tail; Stage C hframeG refactor)
  Vsa.Sim.evalNegSim                            # EvalNegSim3 (EvalE.neg recursive case, EvalIH motive shape; conditional)
  Vsa.Sim.blockC_not                            # EvalNotSim (not post-call tail: value_truthy≫seqz≫value_bool)
  Vsa.Sim.evalNotSim                            # EvalNotSim (EvalE.not recursive case, EvalIH motive shape; conditional)
  Vsa.Sim.blockB_binary                         # EvalBinSim (EX_BINARY two-operand head; two recursive calls, IH-composed)
  Vsa.Sim.blockC_add                            # EvalBinSim2 (add-int dispatch tail + add path → PreEpilogueVD)
  Vsa.Sim.evalAddSim                            # EvalBinSim2 (EvalE.binary .add int pilot, EvalIH motive shape; conditional)
  Vsa.Sim.blockC_sub                            # EvalBinSim3 (sub-int dispatch tail + sub path → PreEpilogueVD)
  Vsa.Sim.evalSubSim                            # EvalBinSim3 (EvalE.binary .sub int, EvalIH motive shape; conditional)
  Vsa.Sim.blockC_lt                             # EvalBinSim4 (lt-int dispatch + shared cmp arm + value_bool → PreEpilogueVD)
  Vsa.Sim.evalLtSim                             # EvalBinSim4 (EvalE.binary .lt int, EvalIH motive shape; conditional)
  Vsa.Sim.blockB_logical                        # EvalAndSim (EX_LOGICAL arm head: env-spill + LEFT recursive call, IH-composed → SubEvalReturn)
  Vsa.Sim.blockC_andFalse                        # EvalAndSim (EX_LOGICAL short-circuit tail: op-dispatch + value_truthy + beqz-taken + value_bool → PreEpilogueVD .bool false)
  Vsa.Sim.evalAndSim                             # EvalAndSim (EvalE.andFalse short-circuit recursive case, EvalIH motive shape; conditional)
  Vsa.Sim.blockC_orTrue                          # EvalOrSim (EX_LOGICAL OR short-circuit tail: beq-taken op-dispatch + value_truthy + beqz-nottaken + value_bool → PreEpilogueVD .bool true)
  Vsa.Sim.evalOrTrueSim                          # EvalOrSim (EvalE.orTrue short-circuit recursive case, EvalIH motive shape; conditional)
  Vsa.Sim.blockC_andTrue                         # EvalLogical3 (EX_LOGICAL AND two-eval tail: op-dispatch + value_truthy(vl) + beqz-nottaken + RIGHT eval + blockC_logTail → PreEpilogueVD .bool vr.truthy)
  Vsa.Sim.evalAndTrueSim                         # EvalLogical3 (EvalE.andTrue two-eval recursive case, EvalIH motive shape, two IH premises; conditional)
  Vsa.Sim.blockC_orFalse                         # EvalLogical4 (EX_LOGICAL OR two-eval tail: op-dispatch + value_truthy(vl) + beqz-taken + RIGHT eval + blockC_logTail → PreEpilogueVD .bool vr.truthy)
  Vsa.Sim.evalOrFalseSim                         # EvalLogical4 (EvalE.orFalse two-eval recursive case, EvalIH motive shape, two IH premises; conditional)
  # Stage A0/A1 — neg block spine as composed Triples (BlockLogic)
  Vsa.Sim.negPrologue_triple                    # A0 (σ0→σ4 prologue as a Triple)
  Vsa.Sim.negLoadStore_triple                   # A0 (σ4→σ10 load/store as a Triple)
  Vsa.Sim.negTail_triple                        # A0 (σ10→σ15 tail as a Triple)
  Vsa.Sim.neg_blocks_triple                     # A1 (FULL 3-block spine σ0→σ15 as ONE composed Triple)
  # M4 statement family — ExecEntry/ExecExit foundation + first ExecSeq case
  Vsa.Sim.execSeqNil                             # ExecSimCommon (ExecSeq.nil: empty sequence → normal, store/output unchanged; zero-step identity Triple)
  Vsa.Sim.execBlockD                             # ExecBrkCont (shared exec_stmt epilogue: restore + addi sp,176 + ret → ExecExit; proven unconditionally)
  Vsa.Sim.execBlockA                             # ExecBrkCont (exec_stmt prologue+jump-table dispatch → ExecArmEntryK; port of blockA_k; UNCONDITIONAL, per-kind multiplier)
  Vsa.Sim.execBrkSim                             # ExecBrkCont (ExecS.brk: execBlockA ≫ li a0,1 ≫ execBlockD → ExecExit .brk; only slot-pin/table-disjoint geometry premises)
  Vsa.Sim.execContSim                            # ExecBrkCont (ExecS.cont: execBlockA ≫ cont epilogue-copy → ExecExit .cont; only slot-pin/table-disjoint geometry premises)
  Vsa.Sim.execExprSim                            # ExecExprRet (ExecS.expr: execBlockA ≫ jal eval_expr≫EvalIH (SubExecReturn glue) ≫ li a0,0/j/execBlockD → ExecExit .normal; conditional on slot-pin/table-disjoint + the recursion-glue residual hGlue)
  Vsa.Sim.armTail_rec_es                         # ExecRecCommon (statement-frame recursion multiplier: jal eval_expr from exec_stmt (176-byte frame) ≫ EvalIH → SubExecReturn; sp-176 port of armTail_rec, sub-sret at sp'+16; unblocks ret + all recursive stmt cases)
  Vsa.Sim.execExprGlue                           # ExecRecCommon (ExecS.expr arm setup ld a2,8(s0)/addi a0,sp,16/mv a3,s3/mv a1,s1 ≫ armTail_rec_es → SubExecReturn: DISCHARGES execExprSimC hGlue from concrete named residuals)
  Vsa.Sim.execExprSimC                           # ExecRecCommon (ExecS.expr → ExecExit .normal with hGlue discharged via execExprGlue; conditional only on execBlockA geometry + concrete sub-expr/code/headroom residuals, no opaque Triple premise)
  Vsa.Sim.execRetSim                             # ExecRet (ExecS.ret value-present: execBlockA ≫ jal eval_expr≫EvalIH (SubExecReturnR glue) ≫ 24-byte *retslot:=v copy (valueRepr_copy_of_writeWindow) ≫ inline li a0,3 epilogue → ExecExit (.ret v) with the retval disjunct; conditional on slot-pin/table-disjoint + retslot geometry + the recursion-glue residual hGlue; retNull is a follow-up)
  Vsa.Sim.execVarDeclSim                         # ExecVarDecl (ExecS.varInit: execBlockA ≫ varInit body glue (init-load, jal eval_expr≫EvalIH, value reload/copy, jal env_define — the Store.define callee) ≫ li a0,0/j/execBlockD → ExecExit ⟨st'.store.define env x v, st'.out⟩ .normal; tail mirrors execExprSim; conditional on slot-pin/table-disjoint + the body-glue residual hGlue (bundling the EvalIH and the env_define callee, which has no landed top-level Triple — M3 verified env_define's prologue only); varNull is a follow-up)
  Vsa.Sim.execSeqExit_extend                     # ExecSeqLoop (re-base an ExecSeqExit to earlier φ-maps by composing PhiExtends on the sole φ-dependent field `store`; the φ-threading helper for the loop rule; UNCONDITIONAL)
  Vsa.Sim.execSeqLoop                            # ExecSeqLoop (THE ExecSeq loop rule / reusable heart: list induction over the statement sequence composing per-iteration ExecSeqStep runs — consNormal loops back to the loop head p, consAbrupt exits to the continuation q, nil falls through — into the whole-sequence Triple ExecSeqEntry@p → ExecSeqExit@q; drives the block do-while at 0x800041a4; conditional on the per-iteration glue hstep (one exec_stmt run + loop control, ExecSeqStep) and the empty-sequence fallthrough hnil, the residual block-arm loop-body decode)
  Vsa.Sim.armExec_rec                            # ExecBlock (THE statement-recursion multiplier: jal exec_stmt at the block do-while recursive call 0x800041c4 ≫ ExecIH (one sub-exec_stmt run producing ExecExitD) → SubStmtReturn at the link 0x800041c8; statement-frame analog of armTail_rec_es swapping callee eval_expr→exec_stmt and returned-value handling → Status in a0 + retslot ValueRepr; assembles the sub-call ExecEntry, applies the IH, repackages ExecExitD; reused by every recursive statement case that re-enters exec_stmt (block-loop, if/while/for bodies); conditional on named geometry residuals — sub-statement StmtRepr/node geometry, sub-retslot geometry, recursion headroom, arena/code disjointness)
  Vsa.Sim.execBlockHnil                          # ExecBlock2 (the block do-while empty-sequence fallthrough p→q (li a0,0; j 0x8000409c): discharges execSeqLoop's hnil via execSeqNil as the identity Triple at the loop head; UNCONDITIONAL)
  Vsa.Sim.execBlockStep                          # ExecBlock2 (the block do-while ONE-ITERATION glue delivering execSeqLoop's hstep=ExecSeqStep: from the loop head 0x800041a4 for s::ss with the per-iteration geometry residual ExecStepGeom (hgeom) + head ExecIH (hIH), threads setup≫armExec_rec≫bnez status-split≫loop control into the normal/abrupt disjunction with the stFin φ-extension; conditional on the machine-iteration residual hbody (setup+control decode + StmtRepr-agreeP AST-transport across the sd-i spill, the recurring exprRepr_agreeP-class gap) and the frame-alloc φ-upgrade hphi)
  Vsa.Sim.execBlockSim                           # ExecBlock2 (THE first full sequencing case, ExecS.block: execBlockA (kind 2, arm 0x8000418c) ≫ env_new_spec (child scope inner = Store.allocFrame) ≫ execSeqLoop (fed execBlockStep hstep + execBlockHnil hnil, threaded UNCONDITIONALLY) ≫ block epilogue → Triple (ExecEntry (.block ss)) (ExecExit … status); composes the child-scope ExecSeq end-to-end; conditional on the arm-prologue residual hArm (execBlockA+env_new+loop-setup → ExecSeqEntry@p) and the epilogue residual hEpi (ExecSeqExit@q → ExecExit))
  Vsa.Sim.execIfNoneSim                           # ExecIf (the bounded ifStmt case, ExecS.ifNone: cond FALSY + no else → no sub-statement, .normal with cond output st'; execBlockA (kind 3, arm 0x800041e8) ≫ arm-body glue hGlue (cond eval jal eval_expr≫EvalIH, reload/copy, jal value_truthy=0 since v.truthy=false, beqz falsy branch TAKEN, ld s0,24(s0)/bnez else-absent NOT-taken → SubExecReturn at 0x800042d4) ≫ li a0,0/j 0x8000409c/execBlockD → ExecExit .normal; tail mirrors execExprSim; sidesteps the ifTrue/ifFalse re-dispatch (0x80004014) entirely; conditional on slot-pin/table-disjoint + the arm-body glue residual hGlue bundling the EvalIH + value_truthy + the falsy/else-absence discharges)
  Vsa.Sim.execPrologue                            # ExecDispatch (the re-dispatch infra: ExecEntry → ExecDispatchReady, the exec_stmt prologue steps 1-13 lifted verbatim from execBlockA — addi sp,-176, five s0/s1/s2/s3/ra spills, four ABI mv, li a6,8, auipc/addi a4 — landing at the dispatch PC 0x80004014 with aStmt':=aStmt, s':=s; transports the parent StmtRepr across the spills via stmtRepr_agreeP; UNCONDITIONAL modulo two honest caller-supplied residuals hfpDisj (the Stmt AST footprint ∉ [SL.lo,sp)) and hslotResIn (the jump table resolves kindOfStmt s to a 4-aligned stack-disjoint arm PC))
  Vsa.Sim.execDispatch                            # ExecDispatch (the re-dispatch infra: ExecDispatchReady → ∃armPC k ment, ExecArmEntryK, the jump-table dispatch steps 14-21 lifted from execBlockA — lw a5,0(s0) kind, bltu not-taken (kindOfStmt s'≤8), lwu/slli/add table+4*kind, lw signed slot, add arm PC, jr — re-deriving kind k=kindOfStmt s' from the carried StmtRepr via stmtRepr_kind; produces the SAME ExecArmEntryK as execBlockA; UNCONDITIONAL; ifTrue/ifFalse/while/for consume ExecDispatchReady+ExecDispatchIH to run their branch/body by re-dispatch in the shared frame — no 2nd prologue)
)

AXFILE="$(mktemp /tmp/vsa_axiom_check.XXXXXX)".lean
mv "${AXFILE%.lean}" "$AXFILE"
{
  echo "import Vsa"
  for t in "${THEOREMS[@]}"; do echo "#print axioms $t"; done
} > "$AXFILE"

AXOUT="$(lake env lean "$AXFILE" 2>&1)"
AXSTATUS=$?
if [ "$AXSTATUS" -ne 0 ]; then
  echo "$AXOUT" >&2
  fail "stage c: lean failed on $AXFILE (unknown theorem or elaboration error)"
fi

AX_OUT="$AXOUT" AX_EXPECTED="${#THEOREMS[@]}" python3 - <<'PYEOF' || fail "stage c: axiom audit failed (see above)"
import os, re, sys

allowed = {"propext", "Classical.choice", "Quot.sound"}
expected = int(os.environ["AX_EXPECTED"])
out = os.environ["AX_OUT"]
bad, seen = [], 0
for line in out.splitlines():
    m = re.search(r"'([^']+)' depends on axioms: \[([^\]]*)\]", line)
    if m:
        seen += 1
        axs = {a.strip() for a in m.group(2).split(",") if a.strip()}
        extra = axs - allowed
        if extra:
            bad.append(f"{m.group(1)}: disallowed axioms {sorted(extra)}")
        continue
    m = re.search(r"'([^']+)' does not depend on any axioms", line)
    if m:
        seen += 1
        continue
    if re.search(r"\berror\b", line, re.IGNORECASE):
        bad.append(f"lean error: {line.strip()}")
if seen != expected:
    bad.append(f"expected {expected} '#print axioms' reports, saw {seen}")
print(f"stage c: {seen}/{expected} theorems audited, allowed = {sorted(allowed)}")
if bad:
    print("\n".join(bad), file=sys.stderr)
    sys.exit(1)
PYEOF

rm -f "$AXFILE"
echo "stage c: OK"
echo "check_all: OK"
