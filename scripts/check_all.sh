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
  Vsa.Sim.execRetNullSim                          # ExecRetNull (ExecS.retNull, return; — the .ret none mirror of execRetSim: state UNCHANGED (st'=st), value fixed .null; the beqz a2@0x80004124 is TAKEN (stmt->expr=0) → the value_null bridge 0x800042f0 (addi a0,sp,16; jal value_null@0x800042f4; j 0x80004138) rejoins the SHARED ret copy+epilogue tail at 0x80004138 — LITERALLY the execRetSim tail with v:=.null; execBlockA (kind 6) head + the 24-byte *retslot:=null copy (valueRepr_copy_of_writeWindow) + inline li a0,3 epilogue → ExecExit (.ret .null) with the retval disjunct; conditional on slot-pin/table-disjoint + retslot geometry + the value_null-bridge glue residual hGlue (SubExecReturnR at 0x80004138 for st/.null, reusing ExecRet's SubExecReturnR))
  Vsa.Sim.execVarDeclSim                         # ExecVarDecl (ExecS.varInit: execBlockA ≫ varInit body glue (init-load, jal eval_expr≫EvalIH, value reload/copy, jal env_define — the Store.define callee) ≫ li a0,0/j/execBlockD → ExecExit ⟨st'.store.define env x v, st'.out⟩ .normal; tail mirrors execExprSim; conditional on slot-pin/table-disjoint + the body-glue residual hGlue (bundling the EvalIH and the env_define callee, which has no landed top-level Triple — M3 verified env_define's prologue only); varNull is a follow-up)
  Vsa.Sim.execVarDeclNullSim                      # ExecVarNull (ExecS.varNull, var x; — the .varDecl x none mirror of execVarDeclSim: state UNCHANGED bar the binding, value fixed .null; the beqz a2@0x800040dc is TAKEN (stmt->init=0) → the value_null bridge 0x800042fc (addi a0,sp,0x68; jal value_null@0x80004300; j 0x800040f0) rejoins the SHARED varDecl reload/env_define tail at 0x800040f0 — LITERALLY the execVarDeclSim tail with v:=.null; execBlockA (kind 1) head + the value_null body glue + li a0,0/j 0x8000409c/execBlockD → ExecExit ⟨st.store.define env x .null, st.out⟩ .normal; conditional on slot-pin/table-disjoint + the value_null-bridge body-glue residual hGlue (SubExecReturn at 0x80004118 for the DEFINED post-state / .null, bundling value_null + the env_define callee — no landed top-level Triple, M3 did its prologue only))
  Vsa.Sim.execSeqExit_extend                     # ExecSeqLoop (re-base an ExecSeqExit to earlier φ-maps by composing PhiExtends on the sole φ-dependent field `store`; the φ-threading helper for the loop rule; UNCONDITIONAL)
  Vsa.Sim.execSeqLoop                            # ExecSeqLoop (THE ExecSeq loop rule / reusable heart: list induction over the statement sequence composing per-iteration ExecSeqStep runs — consNormal loops back to the loop head p, consAbrupt exits to the continuation q, nil falls through — into the whole-sequence Triple ExecSeqEntry@p → ExecSeqExit@q; drives the block do-while at 0x800041a4; conditional on the per-iteration glue hstep (one exec_stmt run + loop control, ExecSeqStep) and the empty-sequence fallthrough hnil, the residual block-arm loop-body decode)
  Vsa.Sim.armExec_rec                            # ExecBlock (THE statement-recursion multiplier: jal exec_stmt at the block do-while recursive call 0x800041c4 ≫ ExecIH (one sub-exec_stmt run producing ExecExitD) → SubStmtReturn at the link 0x800041c8; statement-frame analog of armTail_rec_es swapping callee eval_expr→exec_stmt and returned-value handling → Status in a0 + retslot ValueRepr; assembles the sub-call ExecEntry, applies the IH, repackages ExecExitD; reused by every recursive statement case that re-enters exec_stmt (block-loop, if/while/for bodies); conditional on named geometry residuals — sub-statement StmtRepr/node geometry, sub-retslot geometry, recursion headroom, arena/code disjointness)
  Vsa.Sim.execBlockHnil                          # ExecBlock2 (the block do-while empty-sequence fallthrough p→q (li a0,0; j 0x8000409c): discharges execSeqLoop's hnil via execSeqNil as the identity Triple at the loop head; UNCONDITIONAL)
  Vsa.Sim.execBlockStep                          # ExecBlock2 (the block do-while ONE-ITERATION glue delivering execSeqLoop's hstep=ExecSeqStep: from the loop head 0x800041a4 for s::ss with the per-iteration geometry residual ExecStepGeom (hgeom) + head ExecIH (hIH), threads setup≫armExec_rec≫bnez status-split≫loop control into the normal/abrupt disjunction with the stFin φ-extension; conditional on the machine-iteration residual hbody (setup+control decode + StmtRepr-agreeP AST-transport across the sd-i spill, the recurring exprRepr_agreeP-class gap) and the frame-alloc φ-upgrade hphi)
  Vsa.Sim.execBlockSim                           # ExecBlock2 (THE first full sequencing case, ExecS.block: execBlockA (kind 2, arm 0x8000418c) ≫ env_new_spec (child scope inner = Store.allocFrame) ≫ execSeqLoop (fed execBlockStep hstep + execBlockHnil hnil, threaded UNCONDITIONALLY) ≫ block epilogue → Triple (ExecEntry (.block ss)) (ExecExit … status); composes the child-scope ExecSeq end-to-end; conditional on the arm-prologue residual hArm (execBlockA+env_new+loop-setup → ExecSeqEntry@p) and the epilogue residual hEpi (ExecSeqExit@q → ExecExit))
  Vsa.Sim.execIfNoneSim                           # ExecIf (the bounded ifStmt case, ExecS.ifNone: cond FALSY + no else → no sub-statement, .normal with cond output st'; execBlockA (kind 3, arm 0x800041e8) ≫ arm-body glue hGlue (cond eval jal eval_expr≫EvalIH, reload/copy, jal value_truthy=0 since v.truthy=false, beqz falsy branch TAKEN, ld s0,24(s0)/bnez else-absent NOT-taken → SubExecReturn at 0x800042d4) ≫ li a0,0/j 0x8000409c/execBlockD → ExecExit .normal; tail mirrors execExprSim; sidesteps the ifTrue/ifFalse re-dispatch (0x80004014) entirely; conditional on slot-pin/table-disjoint + the arm-body glue residual hGlue bundling the EvalIH + value_truthy + the falsy/else-absence discharges)
  Vsa.Sim.execPrologue                            # ExecDispatch (the re-dispatch infra: ExecEntry → ExecDispatchReady, the exec_stmt prologue steps 1-13 lifted verbatim from execBlockA — addi sp,-176, five s0/s1/s2/s3/ra spills, four ABI mv, li a6,8, auipc/addi a4 — landing at the dispatch PC 0x80004014 with aStmt':=aStmt, s':=s; transports the parent StmtRepr across the spills via stmtRepr_agreeP; UNCONDITIONAL modulo two honest caller-supplied residuals hfpDisj (the Stmt AST footprint ∉ [SL.lo,sp)) and hslotResIn (the jump table resolves kindOfStmt s to a 4-aligned stack-disjoint arm PC))
  Vsa.Sim.execDispatch                            # ExecDispatch (the re-dispatch infra: ExecDispatchReady → ∃armPC k ment, ExecArmEntryK, the jump-table dispatch steps 14-21 lifted from execBlockA — lw a5,0(s0) kind, bltu not-taken (kindOfStmt s'≤8), lwu/slli/add table+4*kind, lw signed slot, add arm PC, jr — re-deriving kind k=kindOfStmt s' from the carried StmtRepr via stmtRepr_kind; produces the SAME ExecArmEntryK as execBlockA; UNCONDITIONAL; ifTrue/ifFalse/while/for consume ExecDispatchReady+ExecDispatchIH to run their branch/body by re-dispatch in the shared frame — no 2nd prologue)
  Vsa.Sim.execIfTrueSim                           # ExecIf2 (ExecS.ifTrue, FIRST consumer of the re-dispatch IH: execBlockA (kind 3, arm 0x800041e8) ≫ arm-body glue hGlue (cond eval jal eval_expr≫EvalIH, reload/copy, jal value_truthy≠0 since v.truthy=true, beqz TRUTHY branch NOT-taken, ld s0,16(s0) s0:=stmt->then, j 0x80004014 → ExecDispatchReady for the then branch t at extended maps φfE/φcE) ≫ consume the branch ExecDispatchIH st' d env t st'' status → ExecExitD, whose ExecExit is the goal — NO 2nd prologue, NO execBlockD, the branch's own arm+epilogue+ret run in the shared frame; conditional on slot-pin/table-disjoint + hGlue (cond eval + truthy + re-dispatch reach) + hmaps (the block-hphi-analog frame-alloc φ-rebase φfE/φcE→φf/φc at the final st'' store size))
  Vsa.Sim.execIfFalseSim                          # ExecIf2 (ExecS.ifFalse, symmetric to execIfTrueSim: cond eval jal eval_expr≫EvalIH, jal value_truthy=0 since v.truthy=false, beqz FALSY branch TAKEN → 0x800042cc, ld s0,24(s0) s0:=stmt->else, bnez TAKEN (else present) → 0x80004014 → ExecDispatchReady for the else branch e; consume the branch ExecDispatchIH st' d env e st'' status → ExecExitD → the goal ExecExit; NO 2nd prologue; conditional on slot-pin/table-disjoint + hGlue + hmaps φ-rebase)
  Vsa.Sim.execWhileFalseSim                       # ExecWhile (ExecS.whileFalse, the bounded whileStmt case: cond FALSY → no body, .normal with cond output st'; STRUCTURALLY IDENTICAL to execIfNoneSim — execBlockA (kind 4, arm 0x8000403c) ≫ arm-body glue hGlue (cond eval jal eval_expr@0x8000404c≫EvalIH into sret sp'+80, reload/copy, jal value_truthy@0x8000406c=0 since v.truthy=false, beqz a0@0x80004070 FALSY branch TAKEN → SubExecReturn at 0x80004090) ≫ li a0,0@0x80004090/j 0x8000409c/execBlockD → ExecExit .normal; the whileStmt arm is a genuine machine loop (truthy → body via REAL jal exec_stmt@0x80004084, NOT re-dispatch → back-edge check 0x80004034: status==3 ret→propagate 0x80004150, else loop head 0x8000403c) but whileFalse exits before the body; conditional on slot-pin/table-disjoint + the arm-body glue residual hGlue)
  Vsa.Sim.execWhileExit                           # ExecWhile (the three NON-recursive whileStmt constructors — ExecS.whileFalse/whileBreak/whileRet — all exit the loop in ONE iteration; each discharged directly by the ExecWhileStep iteration's EXIT branch: cond-falsy beqz a0 exit / body-.brk bne a0,1 NOT-taken fall-through to 0x80004090 normal / body-.ret v 0x80004034 beq a0,3 TAKEN → ret epilogue 0x80004150; the body statuses .brk/.ret are ≠ .normal/.cont so the loop-back disjunct is contradictory and the exit disjunct fires; conditional on the per-iteration step hstep:ExecWhileStep + the exit witness ¬(bodyStatus=.normal∨.cont). The recursive whileLoop constructor — loop-back via the derivation IH on the strictly-smaller whileLoop sub-derivation — landed separately as execWhileLoopSim)
  Vsa.Sim.execExit_extend                         # ExecWhile2 (re-base an ExecExit to earlier φ-maps AND an earlier m0 baseline: compose the store/retval PhiExtends via PhiExtends.trans, and rebase the memFrame's second disjunct through a memory-agreement clause mNow[a]=m0[a] outside the stack window [SL.lo,sp) and the arena [A.lo,A.hi); the ExecExit analog of execSeqExit_extend extended with the memory rebase; unconditional)
  Vsa.Sim.execWhileLoopSim                        # ExecWhile2 (the RECURSIVE whileStmt constructor ExecS.whileLoop — the IH-taking loop-back lemma, NO self-recursion / NO termination_by: one ExecWhileStep iteration (its loop-back branch: cond truthy + body .normal/.cont → re-enter the head 0x8000403c at the intermediate state stMid with EXTENDED φ-maps, own memory baseline, and a memory-agreement clause vs m0) ≫ the recursive sub-while IH hWhileIH (the derivation on the strictly-smaller whileLoop premise ExecS stMid … (.whileStmt c b) st''' status', supplied by the Layer-4 mutual recursor, quantified over the extended maps + re-entry baseline) → ExecExit st''' status'; composed by execExit_extend (PhiExtends.trans + memory-agreement rebase back to entry φf/φc and m0), mirroring the execSeqLoop loop-back composition with the recursion as a HYPOTHESIS; conditional on hstep:ExecWhileStep + the loop-back witness hloop:(bodyStatus=.normal∨.cont) + hWhileIH)
  Vsa.Sim.execWhileSim                            # ExecWhile2 (all four whileStmt constructors unified as ONE Triple ExecEntry→ExecExit — dispatches on the ExecS derivation of .whileStmt c b: the three non-recursive exits whileFalse/whileBreak/whileRet route to execWhileExit (each passing any exit-shaped body status .brk, whose ExecWhileStep EXIT disjunct delivers the loop-exit ExecExit), and the recursive whileLoop routes to execWhileLoopSim (passing its body's .normal/.cont status); completes the while family; conditional on hstep:ExecWhileStep + the recursive sub-while IH hWhileIH)
  Vsa.Sim.execForExit                             # ExecFor (the three NON-recursive ForLoop constructors — condFalse/bodyBreak/bodyRet — all exit the forStmt loop in ONE iteration, mirror of execWhileExit; each discharged by the ExecForStep iteration's EXIT branch: cond-falsy beqz a0@0x800042a4 exit / body-.brk bne a0,1@0x800042c0 NOT-taken fall-through to 0x800042c4 normal / body-.ret v 0x80004260 beq a0,3 TAKEN → ret epilogue 0x80004150; body statuses .brk/.ret ≠ .normal/.cont so the loop-back disjunct is contradictory and the exit disjunct fires; over the child scope outer, conditional on the per-iteration step hstep:ExecForStep + the exit witness ¬(bodyStatus=.normal∨.cont). The forStmt arm 0x80004234 kind5: forStart env_new+init prologue lands at cond head 0x8000426c; ForCond eval_expr@0x80004280 (or skip if none=truthy), value_truthy@0x800042a0; truthy→body jal exec_stmt@0x800042b8 (ExecIH); ExecStep eval_expr@0x800042e8 on loop-back)
  Vsa.Sim.execForLoopSim                          # ExecFor (the RECURSIVE ForLoop constructor ForLoop.loop — the IH-taking loop-back lemma, NO self-recursion / NO termination_by, mirror of execWhileLoopSim: one ExecForStep iteration (its loop-back branch: ForCond truthy + body .normal/.cont + ExecStep → re-enter the cond head 0x8000426c at the intermediate state stMid with EXTENDED φ-maps, own memory baseline, and a memory-agreement clause vs m0) ≫ the recursive sub-for IH hForIH (the derivation on the strictly-smaller ForLoop.loop premise ForLoop stMid … (.forStmt …) st''' status', supplied by the Layer-4 mutual recursor, quantified over the extended maps + re-entry baseline) → ExecExit; composed by execExit_extend (PhiExtends.trans + memory-agreement rebase back to entry φf/φc and m0); conditional on hstep:ExecForStep + the loop-back witness hloop:(bodyStatus=.normal∨.cont) + hForIH)
  Vsa.Sim.execForLoopBody                         # ExecFor (all four ForLoop constructors unified as ONE Triple ExecEntry(.forStmt …)→ExecExit over the child scope outer — dispatches on the ForLoop derivation: the three non-recursive condFalse/bodyBreak/bodyRet route to execForExit (each passing any exit-shaped body status .brk, whose ExecForStep EXIT disjunct delivers the loop-exit ExecExit), and the recursive loop routes to execForLoopSim (passing its body's .normal/.cont status); the ForLoop analog of execWhileSim; the forStart prologue env_new+ExecInit bridge from the outer ExecEntry(.forStmt) to this loop head is a separate residual; conditional on hstep:ExecForStep + the recursive sub-for IH hForIH)
  Vsa.Sim.execForStartSim                         # ExecForStart (ExecS.forStart — the env_new+init bridge, CLOSING the ExecS statement family: allocates the child scope st.store.allocFrame(some env)=(store',outer) via env_new, runs the optional ExecInit ⟨store',st.out⟩ d outer init st', then hands to ForLoop st' d outer cnd step b st'' status; mirrors execBlockSim's env_new wiring — the arm-prologue residual hArm (execBlockA kind 5 arm 0x80004234 ≫ env_new allocating outer ≫ ExecInit via armExec_rec/ExecIH ≫ fall to the cond head 0x8000426c) bridges the outer ExecEntry(.forStmt) at env to the ForLoop-head ExecEntry(.forStmt) at outer for st', then execForLoopBody (unconditional on its hstep/hForIH) runs the loop to ExecExit, re-based by hEpi; conditional on hArm + hEpi + execForLoopBody's hstep:ExecForStep + hForIH; every ExecS constructor now has a landed conditional Triple)
  Vsa.Sim.evalArgsNil                             # CallEntry (OPENS the call subsystem: the EvalArgs.nil minor premise — an empty argument list is a no-op leaving the spec store/output unchanged, vs=[]. Zero-step identity Triple at the arg-loop continuation PC evalArgsContPC=0x80003254, the analog of execSeqNil on the statement side; the machine's argc≤0 branch (blez a5, 0x800031d8) has already fallen through the arg-eval loop to the fv-kind dispatch, so entry IS exit. UNCONDITIONAL. Foundation: CallEntry decodes the whole inline EX_CALL arm (0x800031b0; no separate call_value symbol) — callee eval (jal eval_expr sret sp+96), the arg-eval loop (0x800031dc, materialising a stack Value-array), the fv-kind dispatch (native kind5→0x800039e0 jalr a6 / closure kind4→0x80003288 env_new+param-bind+body ExecSeq at d+1+depth-guard blt), and fills the InductionScaffold EvalArgs/Call SegEntry/SegExit skeletons with real PCs)
  Vsa.Sim.callAssertOk                            # EvalCallNative (M4 native Call.assertOk: native assert, truthy arg → .null, NO output. The Call.assertOk minor premise as a machine Triple CallEntryP@callDispatchPC=0x80003254 ⇒ CallExitP@callJoinPC=0x800033ec with the spec state UNCHANGED. Native branch decoded: fv-kind dispatch (kind==5 VAL_NATIVE → 0x800039e0), the indirect jalr a6 resolved from ValueRepr(.native f) which pins read64 m (fvAddr+16)=some (N.addr f) so a6=N.addr .assert, and native_assert's truthy path 0x80002df4→ret: 24-byte args[0] Value copied to sp+16 buffer → value_truthy (non-zero) → beqz falls through → value_null writes .null into CALL sret → epilogue; falsy/arity arms are runtime_error/M5 (underivable), matching the assertOk premises vs=[v]∨[v,m] ∧ v.truthy=true. Native_assert code pins generated. CONDITIONAL on NativeAssertOkSpec — the named native-branch residual, discharged by threading the ~26-site native_assert internal run composing value_truthy_spec (on the sp+16 copy via valueRepr_copy_of_writeWindow) + value_null_spec + the dispatch/arm/join wrapper. Same deferral pattern as evalNegSim's NegExtras/hMcallPop)
  Vsa.Sim.nativeAssertInternal                    # EvalCallNative2 (M4 DISCHARGES the core of NativeAssertOkSpec: the native_assert INTERNAL run 0x80002df4→ret threaded straight-line against the generated 33-site battery NativeAssertSites, composing value_truthy_spec + value_null_spec_full — the blockC_not (Value copy → value_truthy → tail value-call) discharge shape, now for a native fn with its OWN 80-byte frame. naEntry (ABI a0=sret,a2=argc∈{1,2},a3=argsBase with args[0] a ValueRepr of a TRUTHY v) ⇒ naExit (ValueRepr sret .null, output UNCHANGED, callee-saved regs+sp restored, memory framed outside [fsp-80,fsp+40)∪[sret,sret+24)). Truthy path gated by the Call.assertOk premises: argc∈{1,2}⇒argc-1∈{0,1}⇒arity bltu NOT taken; v.truthy=true⇒value_truthy returns 1⇒beqz NOT taken⇒falls through to value_null. args[0] copied to the sp+16 truthy buffer via valueRepr_copy (byte-for-byte, sdData_sext_bytes), the 4 frame spills recovered in the epilogue via read64_writeMap8+sext_full+word8_toNat_recon. STILL RESIDUAL (the wrapper, deferred): the fv-kind dispatch 0x80003254 decode, native-arm 0x800039e0 marshal, indirect jalr a6=N.addr .assert (stepObs_jalr), and the SegEntry StoreRepr→ValueRepr(.native .assert)/arg-vector bridge that would land NativeAssertOkSpec and make callAssertOk unconditional. Axiom-clean.)
  Vsa.Sim.callPrint                               # EvalCallPrint (M4 native Call.print — the OUTPUT path term_sim's output-correctness rests on. The Call.print minor premise as a machine Triple CallEntryP@callDispatchPC=0x80003254 ⇒ CallExitP@callJoinPC=0x800033ec with the OUTPUT-APPENDED exit state ⟨st.store, st.out ++ printArgs st.store vs⟩ (store UNCHANGED, .null produced). Same native dispatch as callAssertOk (kind==5 → 0x800039e0, indirect jalr a6=N.addr .print) then native_print 0x80002ed4: blez argc skip; loop j 0x80002f08 enters body at the FIRST value (skips leading space); back-edge 0x80002f0c fputc(' ') separator for i≥1; body 0x80002f1c copies the 24-byte args[i] Value to sp then value_print(sp)=Value.display (int via %lld/snprintf, str/bool/null literal); bne i,argc loops; 0x80002f60 value_null→sret; ret. j-into-body ⇒ single spaces between values = printArgs=String.intercalate ' ' (vs.map (Value.display s)). Native_print code pins generated (42 sites). CONDITIONAL on NativePrintSpec — the named native-branch residual; discharge threads the print loop (measure=remaining args) composing each value_print render + each fputc against the HTIF console-write append primitive htif_store_putchar (Htif.lean: a tohost store pushes String.singleton (Char.ofNat c.toNat) to sailOutput) / mem_write_value_tohost_putchar (HtifLift). THE OUTPUT-APPEND CONTRACT: CallExitP carries OutRepr σ' ⟨st.store, st.out ++ printArgs st.store vs⟩ i.e. Machine.output σ' = st.out ++ printArgs st.store vs — the HTIF console grew by exactly the rendered args. Same deferral pattern as callAssertOk's NativeAssertOkSpec)
  Vsa.Sim.callPrintln                             # EvalCallPrint (M4 native Call.println — Call.print then a trailing newline. The Call.println minor premise as a machine Triple CallEntryP@0x80003254 ⇒ CallExitP@0x800033ec with exit state ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩ (store UNCHANGED, .null). Native dispatch (jalr a6=N.addr .println) → native_println 0x80002f7c: jal native_print (appends printArgs) then ld _impure_ptr; li a0,10 ('\n'); jal fputc (appends "\n"); value_null→sret; ret. Native_println code pins generated (17 sites). CONDITIONAL on NativePrintlnSpec = NativePrintSpec's loop threading plus the single trailing-newline HTIF append. Output-append contract: OutRepr σ' ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩)
  Vsa.Sim.evalArgsLoop                            # EvalArgs (M4 EvalArgs.cons loop rule: the argument-evaluation loop as list induction over the remaining arg list, the exact argument-side analog of execSeqLoop, minus the abrupt disjunction — EvalArgs always continues. Composes per-iteration EvalArgsStep (one jal eval_expr on args[i] consuming an EvalIH ≫ 24-byte copy into the stack Value-array slot sp+32+i*24+208 ≫ i++ back-edge to loop head evalArgsLoopPC=0x800031dc, post loops back for the tail with φ-maps extended + a mid-to-original memFrame invariant) into the whole-sequence Triple SegEntry@p → SegExit@evalArgsContPC=0x80003254. UNCONDITIONAL on the abstract hstep:EvalArgsStep + hnil (the evalArgsNil fall-through hop); the residual is hstep (the machine loop-body glue + recursive eval_expr). segExit_extend rebases SegExit across φ-maps + the mid memory. ArgVecRepr defined: the materialised stack Value-array ↔ vs:List Value (vs[i] a ValueRepr at base+24*i))
  Vsa.Sim.evalArgsCons                            # EvalArgs (M4 EvalArgs.cons minor premise via evalArgsLoop specialised to the full non-empty list e::es at the loop head; composes the head EvalE sub-derivation (threaded as the loop's per-iteration residual hstep) with the tail EvalArgs es recursion. CONDITIONAL on hstep+hnil, the execSeqLoop deferral discipline)
  Vsa.Sim.evalCallSim                             # EvalCall (M4 EvalE.call composition: the WHOLE inline EX_CALL arm callArmPC=0x800031b0 — no call_value symbol — as a machine Triple EvalEntry(.call f args) → EvalExit…v. Threads the three sub-relation results the mutual recursor supplies: the callee EvalIH on f, the EvalArgs args→vs derivation (machine sim = evalArgsLoop), and the Call fval vs→v derivation (machine sim = native/closure dispatch). CONDITIONAL on CallArmSpec — the named composite EX_CALL arm residual stated ABOVE the three sub-derivations (so its discharge may consume all three via armTail_rec/evalArgsLoop/the Call minor premise): blockA dispatch slot 6 ≫ callee armTail_rec (sret sp+96) ≫ evalArgsLoop ≫ fv-kind Call dispatch ≫ blockD_v epilogue. Composite analog of NativeAssertOkSpec)
  Vsa.Sim.TermSimAssembly.term_sim_of_cases       # TermSimAssembly (M4 CAPSTONE: the Layer-4 mutual-recursor ASSEMBLY. The full nine-motive @EvalE.rec application with the REAL simulation motives — mEvalE=EvalIH (EvalEntry→EvalExitD), mExecS=ExecIH (ExecEntry→ExecExitD), and mEvalArgs/mCall/mExecInit/mForLoop/mForCond/mExecStep/mExecSeq the SegEntry→SegExit Triples at the decoded call/args PCs — replacing the True-motive plumbing check of InductionScaffold. Takes all 50 minor premises as explicit hypotheses in the exact ∀-closed shape the recursor demands (constructor args incl sub-derivation proofs, then sub-IHs in motive shape, then the node's motive conclusion) and concludes mEvalE…t=EvalIH for an arbitrary EvalE derivation. TYPE-CHECKS iff the nine real motives compose through every constructor of the mutual family — the kernel-checked demonstration that the whole simulation induction assembles and pins EXACTLY the per-constructor obligations. Each hInt/hStr/…/hSeqConsAbrupt hypothesis is discharged, conditionally on that case's named residuals / M6-layout facts / the Call.closure crux, by the correspondingly named landed case theorem: EvalE leaves+neg/not/binary/logical/call/fn, EvalArgs.nil/cons, Call.assertOk (closure/print/println open), all 16 ExecS ctors, ExecSeq via execSeqLoop, ForLoop via execForLoopBody, with ForCond/ExecStep/ExecInit the loop-scaffold sub-relations. term_sim itself follows by instantiating at the whole-program entry once the M6 residual-unification interface closes)
  Vsa.Sim.evalFnSim                               # EvalFn (M4 EvalE.fn near-leaf closure allocation: .fn name params body allocates ClosureData⟨env,name,params,body⟩ capturing env → .closure a, post-store ⟨store',st.out⟩, no sub-expr. FIRST EvalE leaf with a genuinely non-identity φc-map (closures array grows by one; EvalExit's result/store existentials expose PhiExtends φc φc' (closures.size+1)). Machine = the EX_FN arm (own jump-table slot): dispatch ≫ allocClosure ≫ VAL_CLOSURE kind-4 build ≫ epilogue. CONDITIONAL on FnArmSpec — the named EX_FN arm residual fed the allocClosure fact hAlloc (analog of NativeAssertOkSpec/CallArmSpec); its discharge needs the EX_FN arm decode + an allocClosure callee contract (fresh closure record, PhiExtends on the closures array, the env_new_spec analog) + blockD_v)
  # ── M5 (stuck_sim) spec gadgets + first green pieces (ErrorSem) ──
  Vsa.While.stuck_of_trichotomy                   # ErrorSem (M5 OPEN: the classical-split ELIMINATION half of stuck_sim's spec side. From the Trichotomy obligation (∀p, (∃out,BigStep p out) ∨ BigStepErr p ∨ BigStepDiverges p) and ¬∃out BigStep, derives BigStepErr p ∨ BigStepDiverges p — the two disjuncts the forward error/divergence simulations map to Halts _ 70 / Diverges. Consumes the new mutual error judgment EvalErr/EvalArgsErr/CallErr/ExecErr/ForLoopErr/ExecSeqErr (mirroring the runtime_error call sites: env_get miss, binOpSem=none type/divzero, neg non-int, non-callable/arity/depth-cap, assert-fail, brk/cont escape) via BigStepErr := ExecSeqErr initSt 0 0 p, and the fuel-indexed Approx via BigStepDiverges := ∀n, Approx n initSt 0 0 p. Trichotomy proof deferred; this is the proved elimination step)
  Vsa.While.stuck_of_halts_nonzero                # ErrorSem (M5 first green Machine-side piece: any Halts c out e with e≠0 lands in stuck_sim's ∃out e, Halts c out e ∧ e≠0 disjunct. The exit-code faithfulness target of the error simulation — decoded path: runtime_error@0x80002da8 → longjmp(&in->on_error,1) → interp_run setjmp-cont 0x80004428 bnez a0 → 0x80004508 sets ret=1 → main bnez a0 → 0x80004600 fprintf+li a0,70 → ret → crt0 j exit → _exit HTIF store (70<<<1)|1 to tohost = htif_store_exit e=70. stuck_of_halts_70 specializes; stuck_of_diverges is the Diverges-disjunct counterpart)
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
