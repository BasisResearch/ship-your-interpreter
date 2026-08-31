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
  VSA_LAKE_JOBS="${VSA_LAKE_JOBS:-3}"
  echo "== stage a: lake build (jobs=$VSA_LAKE_JOBS)"
  BUILD_LOG=$(mktemp)
  lake -Kjobs="$VSA_LAKE_JOBS" build 2>&1 | tee "$BUILD_LOG" || fail "stage a: lake build failed"
  grep -q "Build completed successfully" "$BUILD_LOG" \
    || fail "stage a: lake build did not complete successfully"

  # -------- stage a2: per-module elab-budget gate (fast-reflection rule 7) --
  # Parses the per-job durations lake printed for whatever REBUILT in this run
  # (an edited module always rebuilds in the same run, so regressions are
  # caught at the commit that introduces them). Ceilings are wall-clock under
  # parallel load (~2.5-3x isolated `lake env lean`).
  #   HARD_S : fail the gate  (isolated ~60s+ — a new 30-min-cone file in the making)
  #   WARN_S : print a warning
  # Known-heavy modules pending their rewrite wave live in the allowlist file
  # scripts/elab-budget-allow.txt (one module name per line, comments with #).
  echo "== stage a2: per-module elab-budget gate"
  HARD_S="${HARD_S:-180}" WARN_S="${WARN_S:-90}" python3 - "$BUILD_LOG" <<'PYEOF' || fail "stage a2: module(s) over elab budget (raise only with a justification in scripts/elab-budget-allow.txt)"
import os, re, sys, pathlib

log = pathlib.Path(sys.argv[1]).read_text(errors="replace")
hard = float(os.environ["HARD_S"]); warn = float(os.environ["WARN_S"])
allow = set()
ap = pathlib.Path("scripts/elab-budget-allow.txt")
if ap.exists():
    for line in ap.read_text().splitlines():
        line = line.split("#")[0].strip()
        if line: allow.add(line)

viol, warned = [], []
for m in re.finditer(r"Built (\S+) \((\d+(?:\.\d+)?)(m?s)\)", log):
    mod, val, unit = m.group(1), float(m.group(2)), m.group(3)
    secs = val / 1000 if unit == "ms" else val
    if mod in allow: continue
    if secs >= hard: viol.append((secs, mod))
    elif secs >= warn: warned.append((secs, mod))

for s, mod in sorted(warned, reverse=True):
    print(f"  WARN  {s:7.1f}s  {mod}")
for s, mod in sorted(viol, reverse=True):
    print(f"  OVER  {s:7.1f}s  {mod}  (hard ceiling {hard:.0f}s)")
print(f"  gate: {len(viol)} over / {len(warned)} warned "
      f"(ceilings: hard {hard:.0f}s, warn {warn:.0f}s, parallel-load wall)")
sys.exit(1 if viol else 0)
PYEOF
  rm -f "$BUILD_LOG"
else
  echo "== stage a: lake build SKIPPED (--skip-build)"
fi

# ----------------------------------------- stage a3: generated-interface drift
echo "== stage a3: generated term-case bundle"
python3 scripts/gen_term_case_bundle.py --check \
  || fail "stage a3: Vsa/Sim/TermCaseBundle.lean is stale"

# ------------------------------------------------------------ (b) grep gate
echo "== stage a4: proof-discipline gate (exponentiating layer mandatory for new files)"
python3 scripts/check_discipline.py || fail "stage a4: discipline violation (see above)"
echo "stage a4: OK"

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
  # env_get PROLOGUE + full unconditional immediate-frame FOUND case (EnvGetSpec7/8/9)
  Vsa.Sim.env_get_prologue                        # EnvGetSpec7 (0x80002c10 → scan body entry)
  "Vsa.Sim.env_get_found_uncond'"                 # EnvGetSpec8 (prologue ≫ scan ≫ repack ≫ hit-tail, modulo hScanReady)
  Vsa.Sim.foundSt_scanReady                       # EnvGetSpec9 (hScanReady discharged: FrameRepr/ScanNames transport over spills)
  "Vsa.Sim.env_get_found_uncond''"                # EnvGetSpec9 (FULL immediate-frame FOUND case; only FoundSt + FrameStackDisj honest facts)
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
  # M4 leaf EvalE cases re-landed at EvalExitD (mEvalE motive shape; EvalLeafD)
  Vsa.Sim.evalIntSimD                           # EvalLeafD (EvalE.int leaf at EvalExitD)
  Vsa.Sim.evalNullSimD                          # EvalLeafD (EvalE.null leaf at EvalExitD)
  Vsa.Sim.evalBoolSimD                          # EvalLeafD (EvalE.bool leaf at EvalExitD)
  Vsa.Sim.evalStrSimD                           # EvalLeafD (EvalE.str leaf at EvalExitD)
  Vsa.Sim.evalVarSimD                           # EvalLeafD (EvalE.var leaf at EvalExitD)
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
  Vsa.Sim.blockC_le                             # rows/EvalLeRow (le-int dispatch + shared cmp arm + slti fixup + value_bool → PreEpilogueVD; reflective-token dispatch, no maxHeartbeats 8M)
  Vsa.Sim.evalLeSim                             # rows/EvalLeRow (EvalE.binary .le int, EvalIH motive shape; conditional)
  Vsa.Sim.blockC_gt                             # rows/EvalGtRow (gt-int dispatch + shared cmp arm + sgtz fixup + value_bool → PreEpilogueVD; reflective-token dispatch, no maxHeartbeats 8M)
  Vsa.Sim.evalGtSim                             # rows/EvalGtRow (EvalE.binary .gt int, EvalIH motive shape; conditional)
  Vsa.Sim.intPostToEpilogue                     # rows/IntPostEpilogue (SHARED binop value-int arm epilogue packaging: from a fully-transported epilogue-exit config @0x800033ec + int_post/store/value/frame facts, assemble the PreEpilogueVD existential blockD_v_rec consumes; boxed value is a parameter — consumed by blockC_mul (.int(wrap64(a*b))) and blockC_div (.int(wrap64(a.tdiv b))) in place of the inline ~30-conjunct final refine)
  Vsa.Sim.intBoxEpilogue                        # BinopTailGen (PHASE-4a derive_binop_all tail generator: the parameterised generic theorem reproducing the SHARED int-box binop value tail SUFFIX — from the value_int entry config τ0 (pay in x11, sret in x10, boxLink in x1, PC=0x8000280c) through value_int_spec ≫ ld s3,0x418(sp) ≫ j 0x800033ec → PreEpilogueVD. Builds int_pre with the VERDICT's entry-snapshot ghost gbox:=τ0.regs.get? INTERNALLY (frame rfl); the two suffix site lemmas (LdS3Site/JExitSite) enter as ∀-term args so their per-site decides stay in DivTailSites/MulTailSites; consumes Phase-0 StackSlotGeom + intPostToEpilogue. Instantiated by blockC_div (site_8000382c/30) and blockC_mul (site_80003880/84), replacing each arm's ~120-line hand tail marshalling)
  Vsa.Sim.boolBoxEpilogue                       # BoolBoxEpilogue (bool-box clone of intBoxEpilogue via value_bool_box: value_bool ≫ ld s3 ≫ j → PreEpilogueVD .bool bres; shared by eq/ne)
  Vsa.Sim.blockC_mul                            # rows/EvalMulRow (mul-int dispatch tail + __muldi3 libgcc-call seam → TwoSubReturn; Shape-D callee splice via muldi3_spec, sailOutput-tracked; epilogue via intPostToEpilogue)
  Vsa.Sim.evalMulSim                            # rows/EvalMulRow (EvalE.binary .mul int, EvalIH motive shape; conditional)
  Vsa.Sim.blockC_div                            # rows/EvalDivRow (div-int TwoSubReturn → PreEpilogueVD .int(wrap64(a.tdiv b)); reuses evalDivChain_dispatch for entry+dispatch 0x8000351c→0x8000381c, then INLINE __divdi3/value_int value tail via strong divdi3_spec + DivTailSites; div_wrap_bridge boxes res=Wl.tdiv Wr; caller supplies b≠0 + ¬(a=INT64_MIN∧b=-1); epilogue via intPostToEpilogue)
  Vsa.Sim.evalDivSim                            # rows/EvalDivRow (EvalE.binary .div int, EvalIH motive shape; blockB_binary≫blockC_div≫blockD_v_rec; conditional, carries b≠0 + no-overflow)
  Vsa.Sim.blockC_mod                            # rows/EvalModRow (mod-int clone of blockC_div over moddi3_spec/.tmod; no overflow guard)
  Vsa.Sim.evalModSim                            # rows/EvalModRow (EvalE.binary .mod int, EvalIH motive shape; conditional, carries b≠0)
  Vsa.Sim.blockC_eqne                           # rows/EvalEqNeRow (SHARED eq/ne core: from the value_equal-return VeReturn @ frame base sp-1088 run the op-parameterised middle (mv/seqz a1,a0 ; mv a0,s1 ; jal value_bool) then the SHARED boolBoxEpilogue → PreEpilogueVD .bool bres; eq/ne share this ENTIRE proof, differing only in firstSite/bwOf (mv vs seqz), the 3 middle-site PCs, the box constants, and bres)
  Vsa.Sim.blockC_eq                             # rows/EvalEqNeRow (thin instantiation of blockC_eqne with the eq site lemmas site_80003720/24/28/2c/30_ee + box constants (ldPC 0x8000372c, jImm 0x1ffcbc), bwOf=mv (id), result .bool(vl.equal vr))
  Vsa.Sim.blockC_ne                             # rows/EvalEqNeRow (thin instantiation of blockC_eqne with the ne site lemmas site_80003770/74/78/7c/80_ee + box constants (ldPC 0x8000377c, jImm 0x1ffc6c), bwOf=seqz, result .bool(!(vl.equal vr)))
  Vsa.Sim.evalEqSim                             # rows/EvalEqNeRow (EvalE.binary .eq, value-generic operands, EvalIH motive shape; blockB_binary≫blockC≫blockD_v_rec; conditional on the blockC bridge residual — operand-copy read-back from the reflected #derive_case dispatch + value_equal sailOutput invariance)
  Vsa.Sim.evalNeSim                             # rows/EvalEqNeRow (EvalE.binary .ne, value-generic; ne clone of evalEqSim, result .bool(!(vl.equal vr)))
  Vsa.Sim.eqDispatch_mem_frame                  # rows/EvalEqNeFront (eq-dispatch analogue of divDispatch_mem_frame: outside [base,base+0x108) the post-dispatch memory agrees with input m; every eqDispatch store is x2-relative off <=0x108; via evalBlocks_frame_offsets + writeLog_getElem_disjoint)
  Vsa.Sim.neDispatch_mem_frame                  # rows/EvalEqNeFront (ne sibling of eqDispatch_mem_frame, byte-identical block)
  Vsa.Sim.eqDispatch_log_trunc                  # rows/EvalEqNeFront (truncation: eqDispatch reflected log depends only on lds's first 6 loads; lds -> lds6 lds by rfl after six-case cons split; feeds the [b0..b5] readback for the existential dispatch lds)
  Vsa.Sim.neDispatch_log_trunc                  # rows/EvalEqNeFront (ne sibling truncation)
  Vsa.Sim.eqDispatch_bufa_repr_lds              # rows/EvalEqNeFront (readback wired to the existential dispatch lds: eqDispatch_log_trunc + eqDispatch_lpins feed eqDispatch_bufa_repr; lands ValueRepr vl at bufa on the EqDispatchPostS tower memory)
  Vsa.Sim.eqDispatch_bufb_repr_lds              # rows/EvalEqNeFront (readback wired to existential lds for bufb/vr)
  Vsa.Sim.neDispatch_bufa_repr_lds              # rows/EvalEqNeFront (ne sibling readback-at-lds for bufa/vl)
  Vsa.Sim.neDispatch_bufb_repr_lds              # rows/EvalEqNeFront (ne sibling readback-at-lds for bufb/vr)
  Vsa.Sim.eqnePreBridge                         # rows/EvalEqNeFront (front: jal value_equal @jalPC → ve_pre @0x8000285c; model divPreBridge; parameterised by jalPC/link so ONE bridge serves eq+ne)
  Vsa.Sim.veReturnBridge                        # rows/EvalEqNeFront (front: ve_str_post → VeReturn; reconciles x9=sret, eval-frame collapse, MemExtends)
  Vsa.Sim.blockC_eqne_front                     # rows/EvalEqNeFront (front: EqFrontData ⇒ eqnePreBridge ≫ value_equal_spec_full ≫ veReturnBridge → VeReturn; model blockC_div)
  Vsa.Sim.eqFrontData_of_readback               # rows/EvalEqNeFront (route (a): reassemble EqFrontData from EqFrontDataNoRepr + EqNeSrcPins + source reprs + payload disjointness; operand reprs DERIVED via eqDispatch_bufa/bufb_repr_lds rather than supplied as caller data — the div-parity lift of the front)
  Vsa.Sim.eqBlockC_bridge                       # rows/EvalEqNeFront (front: EqResid ⇒ blockC_eqne_front ≫ blockC_eq/blockC_ne → hblockC PreEpilogueVD; φ chain threaded; EqResid now div-parity — c2-based geometry + source reprs + disjointness + box, no post-dispatch reprs given)
  Vsa.Sim.evalEqSimD                            # rows/EvalEqNeFront (div-parity reseat of EvalE.binary .eq: hblockC residual replaced by an EqResid precondition, front closed to blockC_eq)
  Vsa.Sim.evalNeSimD                            # rows/EvalEqNeFront (div-parity reseat of EvalE.binary .ne; ne clone, result .bool(!(vl.equal vr)))
  Vsa.Sim.blockC_ge                            # rows/EvalGeRow (ge-int dispatch: three-beq fall-through + not;srli sign-bit → PreEpilogueVD .bool(a≥b); token 23, reuses lt ladder blocks + evalGeLadderD)
  Vsa.Sim.evalGeSim                             # rows/EvalGeRow (EvalE.binary .ge int, EvalIH motive shape; conditional)
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
  Vsa.Sim.execWhileStepOf                         # rows/LoopSteps (Shape-C step-contract PRODUCER for ExecWhileStep — the while analog of execBlockStep, closing the previously-UN-produced while re-dispatch loop's per-iteration hstep. From the loop-head ExecEntry(.whileStmt), consumes ONE mechanical machine-iteration body oracle hbody (the cond-eval-setup ≫ jal eval_expr [EvalIH] ≫ value_truthy ≫ jal exec_stmt [ExecIH] ≫ status-dispatch ≫ back-edge decode, packaged as the contract's loop-back∨exit post disjunction keyed on bodyStatus, φ-extension over the INTERMEDIATE stMid) + the frame-alloc φ-upgrade hphi (stMid-sized → stFin-sized extension) and re-emits the ExecWhileStep Triple. The two cond/body IHs stay INSIDE hbody as jal callees — mission point 3. Pure Triple/disjunction marshalling proven ONCE; residual = the body-chain oracle, a #derive_case+armTail_rec/armExec_rec+loopStep assembly gated on the same exprRepr_agreeP/mutual-recursor pieces execBlockStep's hbody awaits. Axiom-clean)
  Vsa.Sim.execForStepOf                           # rows/LoopSteps (Shape-C step-contract PRODUCER for ExecForStep — STRUCTURALLY IDENTICAL to execWhileStepOf over .forStmt at the child scope outer; one marshalling proof serves both re-dispatch loops [the shape-level reuse]. Same two inputs: hbody [the for loop-body decode: ForCond eval ≫ jal exec_stmt [ExecIH] ≫ ExecStep ≫ status-dispatch ≫ back-edge, loop-back∨exit post keyed on bodyStatus] + hphi [stMid→stFin φ-upgrade]. Residual = the body-chain oracle. Axiom-clean)
  Vsa.Sim.evalArgsStepOf                          # rows/LoopSteps (Shape-C step-contract PRODUCER for EvalArgsStep — the SIMPLER args-cons loop [no abrupt exit ⇒ single always-loop-back post, no bodyStatus keying]. Discharges the spec-side EvalE premise then forwards ONE body oracle hbody [arg-load ≫ jal eval_expr [EvalIH] ≫ 24-byte Value copy into the stack Value-array slot ≫ i++ ≫ bne back-edge, φ-extension over stMid] threading the stFin φ-upgrade hphi + the mid-to-original memFrame clause, re-emitting the EvalArgsStep Triple. The one arg EvalIH stays inside hbody. Residual = the body-chain oracle. Axiom-clean)
  Vsa.Sim.execWhileExit_of_bodyOracle            # rows/LoopSteps (WRAPPER demonstrating the substitution: execWhileExit with its abstract hstep:ExecWhileStep supplied by execWhileStepOf, leaving only the body-oracle mkBody + φ-glue mkPhi + the exit witness as residuals — no existing theorem statement changed. Shows the loop rules become fully closed on the mechanical per-shape oracle. Axiom-clean)
  Vsa.Sim.stmtRepr_survives_writeLog             # ReprStackSurvival (THE shared loop-body AST-repr transport, seq/while/for/args: a reflected body writeLog whose windows are WinsInSA (in the stack window or arena) with 1/4/8 widths preserves any StmtRepr whose footprint is disjoint from stack ∪ arena — the script region. Composes AstTransport.stmtRepr_agreeP over the OffStackArena agreement from BlockAdapter.writeLog_agreeP_disjoint. Closes the recurring exprRepr_agreeP-class gap that gated every loop body oracle. Axiom-clean)
  Vsa.Sim.exprRepr_survives_writeLog             # ReprStackSurvival (the ExprRepr twin of stmtRepr_survives_writeLog — loop-condition / arg-expression survival across a reflected in-window body writeLog. Axiom-clean)
  Vsa.Sim.stmtRepr_survives_spill                # ReprStackSurvival (the tightest single-writeMap8 form: the sd-i counter spill writeMap8 m tgt d at an in-window slot tgt (SL.lo ≤ tgt, tgt+8 ≤ sp) preserves StmtRepr with one omega side condition — the exact StmtRepr mcall conjunct armExec_rec demands after the spill, no writeLog plumbing. Axiom-clean)
  Vsa.Sim.exprRepr_survives_spill                # ReprStackSurvival (the ExprRepr twin of stmtRepr_survives_spill. Axiom-clean)
  Vsa.Sim.blockIter_stmtRepr_ready               # SeqBodyOracle (the seq body oracle's AST-repr seam APPLIED: from ExecStepGeom's pinned StmtRepr m0 + the loop stack-headroom geometry (SL.lo+2352 ≤ sp ⇒ spill slot sp-168 in-window) + the caller's deep footprint-disjointness hfpDisj (AST subtree ∈ script region, disjoint from [SL.lo,sp) — same fact ExecDispatch.execPrologue pushes to its caller), stmtRepr_survives_spill delivers StmtRepr (writeMap8 m0 (sp-168) d) — the exact StmtRepr mcall conjunct armExec_rec (ExecBlock.lean:224) needs. With this supplied, execBlockStep's hbody residual is PURELY the setup-site register decode + armExec_rec IH-seam + branch-control sites — no AST-repr transport remains. Fans to while/for/args verbatim. Axiom-clean)
  Vsa.Sim.execIfNoneSim                         # ExecIf (the bounded ifStmt case, ExecS.ifNone: cond FALSY + no else → no sub-statement, .normal with cond output st'; execBlockA (kind 3, arm 0x800041e8) ≫ arm-body glue hGlue (cond eval jal eval_expr≫EvalIH, reload/copy, jal value_truthy=0 since v.truthy=false, beqz falsy branch TAKEN, ld s0,24(s0)/bnez else-absent NOT-taken → SubExecReturn at 0x800042d4) ≫ li a0,0/j 0x8000409c/execBlockD → ExecExit .normal; tail mirrors execExprSim; sidesteps the ifTrue/ifFalse re-dispatch (0x80004014) entirely; conditional on slot-pin/table-disjoint + the arm-body glue residual hGlue bundling the EvalIH + value_truthy + the falsy/else-absence discharges)
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
  Vsa.Sim.halts_of_steps_halted                   # ErrorSim (M5 Part-A helper: prepend a finite Steps run to a Halted node → Halts c out e. The Halts-introduction plumbing the runtime_error→exit(70) chain assembles from its three finite sub-runs)
  Vsa.Sim.errorTailHalts                          # ErrorSim (M5 Part A capstone — the REUSABLE runtime_error→halt-70 chain. From a config at the jal runtime_error entry (runtime_error_spec precondition hre), threads runtime_error_spec (→ interp_run setjmp-cont 0x80004428, a0=1) ≫ ErrorTailChain HT (interp_run-cont/main/crt0/exit span 0x80004428→_exit store site, Triple residual) ≫ ExitStoreHalts HX (exit sd a5,tohost → htif_store_exit → Halted _ 70 machine bridge, the one genuine plumbing residual) → Halts c out 70. Reuses runtime_error_spec + htif_store_exit by name; a0=1 normalized by decide. CONDITIONAL on SnprintfContract SC + HT + HX + hre frame geometry)
  Vsa.Sim.errorSim_execSeq                        # ErrorSim (M5 Part B skeleton — the assembly for one error relation (ExecSeqErr): cases on the two constructors (head: first stmt errors; tail: head runs normal + tail errors) with error-motive ErrHalts c := ∃out, Halts c out 70, taking per-constructor site-reachability residuals hHead/hTail. Mirrors term_sim_of_cases; the tail sub-recursion + full six-relation @ExecSeqErr.rec widening exposed via hTail's ExecSeqErr→ErrHalts residual)
  Vsa.Sim.errorSim                                # ErrorSim (M5 Part B entry: BigStepErr p → ∃out, Halts c out 70, specializing errorSim_execSeq to the top-level ExecSeqErr initSt 0 0 p. Two whole-program residuals hHead/hTail)
  Vsa.Sim.stuck_of_bigStepErr                     # ErrorSim (M5 Part B → stuck_sim: composes errorSim (∃out, Halts c out 70) with stuck_of_halts_70 to discharge stuck_sim's Diverges ∨ ∃out e, Halts c out e ∧ e≠0 error disjunct. CONDITIONAL on the hHead/hTail per-error-site residuals)
  Vsa.Sim.exec_sd_tohost_exit                     # ErrorTail (M5 exit-store execute: execute (STORE imm rs2 rs1 8) at the _exit sd a5,tohost site, effective addr = tohostAddr, data = (70<<<1)|1 → post-state sigmaExit (htif_done:=true, htif_exit_code:=70). Routes execute_STORE_char → vmem_write_addr_w (w=8, abstract mem_write_value post-state) → mem_write_value_tohost_exit. UNCONDITIONAL modulo the sd register-reads/effective-addr geometry)
  Vsa.Sim.try_step_tohost_exit                    # ErrorTail (M5: try_step on the exit sd a5,tohost store via try_step_execute_char + exec_sd_tohost_exit; postlude PC:=pc+4, minstret+=1; returns false, HTIF exit latched in the try_step-final state sigmaExitFinal)
  Vsa.Sim.stepOnce_tohost_exit                    # ErrorTail (M5: the exit-store stepOnce HALTS inside itself — try_step performs the store (htif_done:=true), then the SAME stepOnce re-checks htif_done (Elf.lean:86) = true and returns .inl (some 70, u+1). No tick_clock. = Halted c 70 sigmaExitFinal)
  Vsa.Sim.exitStoreHalts                          # ErrorTail (M5 DISCHARGED — the one genuine machine residual. ∀c, ExitStorePreExit out c → ∃c' σf, Steps c c' ∧ Halted c' 70 σf ∧ output σf=out. Steps c c refl + the single halting stepOnce_tohost_exit; output unchanged (exit store touches only HTIF control regs). Backed by mem_write_value_tohost_exit/htif_store_exit as planned)
  Vsa.Sim.errorTailHalts_exit                     # ErrorTail (M5: errorTailHalts with ExitStoreHalts DISCHARGED — supplies exitStoreHalts concretely at ExitStorePre:=ExitStorePreExit, leaving only the ErrorTailChain decode span (0x80004428→_exit) as the single residual. CONDITIONAL on SnprintfContract SC + ErrorTailChain HT + hre frame geometry)
  Vsa.Sim.errorTailChain_of_segments              # ExitPath (M5: ErrorTailChain DECOMPOSED into a Triple.seq of the span's four decoded straight-line segments — InterpContSeg (0x80004428→0x800045ec: taken bnez a0=1, interp_run epilogue ret a0=1), MainErrorSeg (0x800045ec→0x80000038: taken bnez, fprintf(stderr NOT tohost so output unchanged)+li a0,70+main epilogue ret), Crt0ExitSeg (0x80000038→0x80000180: j exit; __call_exitprocs+stdio handler no tohost; mv a0,s0=70; jal _exit), ExitPrologSeg (0x80000180→sd a5,tohost: slli/srli/ori form (70<<<1)|1) — plus the entry-output pinning hEntryOut (output at the setjmp-cont = out, NOT named by ErrorTailChain's pre). Composed via Triple.seq/conseq; ra0=0x80004428. Converts the one opaque ErrorTailChain residual into four minimal per-segment residuals + the fprintf output-neutrality handling)
  Vsa.Sim.errorTailHalts_segments                 # ExitPath (M5: errorTailHalts with ErrorTailChain supplied from the four segment Triples via errorTailChain_of_segments — the runtime_error→exit(70) chain conditional only on SnprintfContract SC, the four decoded segment residuals h1..h4, the entry-output pinning hEntryOut, and the runtime_error_spec frame geometry hre at the concrete continuation ra0=0x80004428)
  Vsa.Sim.exitPrologSeg_of                         # ExitPathSeg (M5 DISCHARGED: ExitPrologSeg segment — Triple (AtExitProlog out) (ExitStorePreExit out). The _exit prologue 0x80000180→0x80000190: slli a4,a0,0x20 / srli a5,a4,0x1f / ori a5,a5,1 (form (70<<<1)|1 in a5 from a0=70, by decide) / auipc a4,0x1b (tohost base 0x8001b18c) → park at sd a5,tohost @0x80000190 with EA=tohostAddr, a5=(70<<<1)|1. Four stepObs_alu sites (esite_80000180..8000018c) threaded via Muldi3Spec obs_alu_* consumers; landing config satisfies ExitStorePreExit. CONDITIONAL on ExitPrologGeom out — the two facts AtExitProlog omits: _exitLoaded + htif_payload_writes=0)
  Vsa.Sim.exitPrologSeg                             # ExitPathSeg (M5: exitPrologSeg_of packaged as the ExitPrologSeg out segment residual of errorTailChain_of_segments, conditional on ExitPrologGeom)
  Vsa.Sim.errorSim_of_sites                         # ErrorSimFull (M5 FULL error-sim assembly — the six-relation widening of errorSim_execSeq. Applies @ExecSeqErr.rec with all six error motives = constant ErrHalts c := ∃out, Halts c out 70 (the recursor node + every sub-IH ignored, error-side analog of the term_sim_of_cases motives), taking all 42 error-constructor minor premises as explicit per-error-site residuals (EvalErr 15 + EvalArgsErr 2 + CallErr 7 + ExecErr 12 + ForLoopErr 4 + ExecSeqErr 2). Recursive error nodes (ExecSeqErr.tail/CallErr.body/EvalErr-ExecErr-ForLoopErr propagation) additionally receive the sub-node ErrHalts c as a recursor-supplied IH. Type-checks iff the six constant motives compose through every constructor of the mutual family. Concludes: an arbitrary ExecSeqErr node → ErrHalts c)
  Vsa.Sim.errorSimFull                              # ErrorSimFull (M5: full error simulation, program level — errorSim_of_sites specialized to BigStepErr p = ExecSeqErr initSt 0 0 p, yielding exists out, Halts c out 70. CONDITIONAL only on the 42 per-error-site residuals)
  Vsa.Sim.stuck_of_bigStepErrFull                  # ErrorSimFull (M5 to stuck_sim: composes errorSimFull with stuck_of_halts_70 to discharge stuck_sim Diverges-or-nonzero-halt error disjunct, for the FULL six-relation error judgment. CONDITIONAL on the 42 per-error-site residuals)
  # exponentiation abstraction stack, Wave A/B (experiments/exponentiation-plan.md)
  Vsa.Sim.geomFacts_of_layout                      # GeomFacts (L0: Layout → one GeomFacts record; every case projects its geometry residual O(1) — the M6 interface)
  Vsa.Sim.LayoutInstance.layoutGeomPredL           # LayoutInstance (M6: LayoutGeomPred for the concrete binary — interpRunCode [0x800043ec,0x80004588) / stackSL [0x87800000,0x88000000) / spEntry 0x88000000; three atoms by decide/omega on literals)
  Vsa.Sim.LayoutInstance.geomFactsL                # LayoutInstance (M6: the concrete GeomFacts — geomFacts_of_layout layoutGeomPredL; discharges the geometry residual of the final close, every Layer-4 case projects off it)
  Vsa.Sim.LayoutInstance.jumpTableDisjoint         # LayoutInstance (M6: below-HTIF dispatch jump table 0x80019f58+44 StackDisjoint from the C-stack scribble)
  Vsa.Sim.LayoutInstance.interpRunCodeDisjoint     # LayoutInstance (M6: below-HTIF interp_run code region StackDisjoint from the C-stack scribble)
  Vsa.Sim.LayoutInstance.layoutStaticsLoaded       # LayoutInstance (M6: statics handle — ImageStaticsLoaded → LldFmtLoaded + a static byte-pin, re-export of ImageDischarge)
  Vsa.Sim.segEval_sound                            # SegEvalSound (L1: reflected block-chain → Machine.Steps in SegEvalState normal form — canonical writeLog, computed regs/PC, one ChainOK decide per row)
  Vsa.Sim.FrameCalc.valueRepr_copy                 # FrameCalc (L2: canonical marshalling/frame calculus — logs compose by append; ValueRepr copy through one write window)
  Vsa.Sim.StepFrameOut.trans                       # StepFrameOut (L3: per-step register-frame + sailOutput preservation folded into one record; write-sets union by ++ in .trans, mirroring FrameCalc — replaces obs_CLASS_other×8 + hobs.out hand-threading)
  Vsa.Sim.abiFrame_of_wrChain                       # FrameMeta (METATHEOREM c: wrChain ∩ AbiPreserved = ∅ by one decide ⇒ ABI callee-saved frame carried — framed callee variants FREE)
  Vsa.Sim.memFrame_of_chain                         # FrameMeta (METATHEOREM d: memChain footprint predicate ⇒ memory-frame post, symbolic addresses supported)
  Vsa.Sim.bblocks_sound_framed                      # FrameMeta (packaged: block-chain soundness with ABI+footprint frames pre-collapsed; caller supplies two decides)
  Vsa.Sim.mv_dispatch_setup_abiFramed               # FrameMeta (DEMO on the real memmove dispatch segment: O(sites) hand-threading → one decide)
  Vsa.Sim.lookupG_runGM_snoc                        # SegReadback (ld-cell register readback peel — no deep rfl; T1.5a)
  Vsa.Sim.gholds_lookup_ld                          # SegReadback (row-facing readback companion to gholds_lookup; kills the 10-line hand-unfold pattern)
  Vsa.Sim.gcDemo_facts                              # SegReadback (seg_guard_close regression: chain_facts + guard fallback at maxRecDepth 4000)
  Vsa.Sim.Widen.footMono                            # WidenMeta (T1.2: the ONE parametric exit-widener; 4 of 5 zoo wideners now thin aliases)
  Vsa.Sim.evalExitD_of_widen                        # WidenMeta (Eval-family bridge from the parametric widener)
  Vsa.Sim.execExitD_of_widen                        # WidenMeta (Exec-family bridge)
  Vsa.Sim.execVarNullSimD                           # rows/ExecRecRows (PAYOFF: varNull at non-identity φf via the parametric widener)
  Vsa.Sim.Rows.exec_varNull_row                     # rows/ExecRecRows (NEW row: fills hSVarNull; residual = value_null+env_define body glue only)
  Vsa.Sim.execIH_of_exitSim                          # rows/ExecIHWiden (the ONE exit-sim → ExecIH combinator: widen-and-marshal proven once)
  Vsa.Sim.Rows.exec_ifNone_row                       # rows/ExecDispatchRows (fills hSIfNone)
  Vsa.Sim.Rows.exec_whileFalse_row                   # rows/ExecDispatchRows (fills hSWhileFalse)
  Vsa.Sim.Rows.exec_ifTrue_row                       # rows/ExecDispatchRows (fills hSIfTrue; branch ExecDispatchIH named residual)
  Vsa.Sim.Rows.exec_ifFalse_row                      # rows/ExecDispatchRows (fills hSIfFalse)
  Vsa.Sim.Rows.exec_block_row                        # rows/ExecDispatchRows (fills hSBlock; allocFrame φ-growth via the parametric widener)
  Vsa.Sim.Rows.exec_forStart_row                     # rows/ExecDispatchRows (fills hSForStart)
  Vsa.Sim.Rows.exec_whileBreak_row                   # rows/ExecDispatchRows (fills hSWhileBreak; shared WhileGeom)
  Vsa.Sim.Rows.exec_whileRet_row                     # rows/ExecDispatchRows (fills hSWhileRet)
  Vsa.Sim.Rows.exec_whileLoop_row                    # rows/ExecDispatchRows (fills hSWhileLoop)
  Vsa.Sim.ScaffoldRows.hInitNone_row                 # rows/ScaffoldRows (fills hInitNone via segIdentity — motive p,q amendment made it fillable)
  Vsa.Sim.ScaffoldRows.hFcNone_row                   # rows/ScaffoldRows (fills hFcNone)
  Vsa.Sim.ScaffoldRows.hEsNone_row                   # rows/ScaffoldRows (fills hEsNone; some-case residuals precisely typed as hInitSome_resid/hFcSome_resid/hEsSome_resid)
  Vsa.Sim.eval_int_row_ofBundle                     # TermBundles (T1.4 probe: a landed row re-expressed against the assembly bundles)
  Vsa.Sim.bin_add_cell_ofBundle                     # TermBundles (T1.4 probe: binary int cell drawing storeSize from TermGuards; 6 callee fields instantiate VERBATIM)
  Vsa.Sim.armPostGeomV_of_armPostGeom               # rows/ArmPostGeom (T1.1: ArmPostGeomV value-form+tblOff parametric core; int/tblOff=4 bridge)
  Vsa.Logic.Triple.dimap                             # TripleCat (profunctor action = the canonical conseq; equations hold by proof irrelevance, constructors carry the value)
  Vsa.Logic.PredIso.transportPre                     # TripleCat (adapter pair collapsed to one iso + transport)
  Vsa.Sim.callSegConseq_dimap                        # TripleCatDemos (callSegConseq seam via dimap)
  Vsa.Sim.bridgeNamesToVals_wired_dimap              # TripleCatDemos (Shape-A wired adapter as Triple.lmap; identity-post dropped)
  Vsa.Sim.transportLtResid                           # TripleCatDemos (LtResid↔ArmPostGeomV pair as PredIso.transportPre)
  Vsa.Sim.ltResid_of_armPostGeomV                   # rows/ArmPostGeom (T1.1 fan-out: 7/8 op residuals collapsed; EqResid honestly resisted — collapse point is EqNeBoxPre)
  Vsa.Sim.divResid_of_armPostGeomV                  # rows/ArmPostGeom (T1.1: seam-iso reverse adapter with libgcc extras as explicit hypotheses)
  Vsa.Sim.StepFrameOut.of_alu                      # StepFrameOut (L3: ALU-class smart constructor from a ReadsLikePost — composes hobs.1 + get?_sigmaPost_alu + sailOutput_sigmaPost_alu)
  Vsa.Sim.chainFrameOut_get_demo                   # ChainFrameOut (L3: chain_frame_out folds a whole straight-line run's per-step ReadsLikePost hyps into ONE StepFrameOut by syntactic sigmaPost_* head-dispatch + left-fold .trans; capstone exercises the 8-step fold + whole-run .get/.out over a ~44-elt unioned W (18ms decide). Retrofits blockC_mul's hframeG f_14…f_21 ladder → 3 chain_frame_out calls)
  Vsa.Sim.chainOut_demo                            # ChainFrameOut (L3: chain_out [ho…] = the whole-run sailOutput-invariance projection (σₙ.sailOutput = σ₀.sailOutput) from the same fold, with the unioned write-set W inferred/never-named — the one-line exponentiating replacement for a per-step hout ladder when threading output through a straight-line run)
  Vsa.Sim.heapPublicFrame_refl                     # ReallocSpec (L5: corrected realloc op interface — grow/null results over one allocator invariant + private footprint)
  Vsa.Sim.HeapOps.privFoot_disjoint                # HeapOps (L5: malloc+realloc packaged on one allocator ledger; privFoot disjoint from every live extent)
  Vsa.Sim.demoChain_row                            # DeriveCase (L3: #derive_case emits a chain def + name_seg run theorem in plain terms; a Wave-D row = one application + one kernel decide)
  Vsa.Sim.cmpFixupTail_facts                       # CmpArmSeg (EXPONENTIATION proof-of-method: the ge operator-fixup tail 0x36a4→0x36c8 (3 branches + not/srli/mv) auto-threaded via #derive_case; chain_facts discharges the whole ChainFacts bundle incl. the 3 branch guards from ONE loaded-image hyp)
  Vsa.Sim.cmpFixupTailRow                          # CmpArmSeg (the payoff: same fixup tail as a Triple via segToTriple in ~44 lines of proof content vs ~159 hand lines — the step-count/frame bookkeeping is auto-computed, gone. Template for div/mod/eq/ne + the full-ladder migration)
  Vsa.Sim.cmpDispatchRow                           # CmpDispatchSeg (SCALED to the WHOLE ge post-jr dispatch ladder 0x80003628→0x800036c8 as ONE #derive_case seg of 8 blocks + segToTriple: kind-ladder + operand loads + FIVE stack stores (non-empty out.log) + operator-beq ladder + not/srli/mv, ~15 lines of proof content vs the ~600-line hand evalGeLadderAB/C/D/EF+G. chain_facts reduces the 8-block ChainFacts bundle to exactly 7 auto-closing dispatch guards + 10 caller frame-window MemFacts)
  Vsa.Sim.divDispatchRow                           # DivDispatchSeg (first NEW binary-op leaf assembled on the combinator, NOT hand-cloned: the div arm 0x800037dc→0x8000381c as ONE #derive_case seg + segToTriple. Two int-kind bnes + the divisor-nonzero beqz (data-dependent b≠0 guard, left to caller by chain_facts) + the __divdi3 arg mvs; row exposes x10=Wl (dividend a), x11=Wr (divisor b))
  Vsa.Sim.divCallSeam                              # DivDispatchSeg (the libgcc __divdi3 seam via callSeg with the REAL divdi3_spec threaded as callee: dispatch ≫ __divdi3 ≫ value_int → .int (wrap64 (a.tdiv b)), mirror of blockC_mul/muldi3_spec)
  Vsa.Sim.binOpSem_div_int                         # DivDispatchSeg (spec-side div bridge: binOpSem .div (.int a) (.int b) = some (.int (wrap64 (a.tdiv b))) for b≠0)
  Vsa.Sim.modDispatchRow                           # ModDispatchSeg (mod arm 0x80003784→0x800037c4 as a #derive_case seg + segToTriple, direct clone of the div leaf: two int-kind bnes + divisor-nonzero beqz + __moddi3 arg mvs; row exposes x10=Wl, x11=Wr)
  Vsa.Sim.modCallSeam                              # ModDispatchSeg (libgcc __moddi3 seam via callSeg with the REAL moddi3_spec threaded as callee: dispatch ≫ __moddi3 ≫ value_int → .int (wrap64 (a.tmod b)), sibling of divCallSeam)
  Vsa.Sim.binOpSem_mod_int                         # ModDispatchSeg (spec-side mod bridge: binOpSem .mod (.int a) (.int b) = some (.int (wrap64 (a.tmod b))) for b≠0)
  Vsa.Sim.eqDispatchRow                            # EqNeDispatchSeg (eq arm 0x800036e4→0x8000371c spill-and-call-setup as a #derive_case seg + segToTriple: six operand reloads + two addi buf-pointer setups + six field spills, falls through to jal value_equal; row exposes x10=bufa=sp+0x40, x11=bufb=sp+0x20)
  Vsa.Sim.neDispatchRow                            # EqNeDispatchSeg (ne arm 0x80003734→0x8000376c, byte-identical block to eq shifted +0x50; seqz negation lives in the box suffix)
  Vsa.Sim.binOpSem_eq                              # EqNeDispatchSeg (spec-side eq bridge: binOpSem .eq l r = some (.bool (l.equal r)))
  Vsa.Sim.binOpSem_ne                              # EqNeDispatchSeg (spec-side ne bridge: binOpSem .ne l r = some (.bool (!(l.equal r))))
  Vsa.Sim.valueEqualCallSeam                       # EqNeDispatchSeg (value_equal seam via callSeg with the REAL value_equal_spec_full threaded (both str-str strcmp + 5 non-str branches): spill-setup ≫ jal value_equal ≫ value_bool; shared by eq/ne)
  Vsa.Sim.valueIntCallSeam                         # BoxSuffixSeams (item-3 box suffix for div/mod: the jal value_int box site via callSeg with the REAL value_int_spec threaded as callee — Triple P (int_pre) ≫ value_int ≫ Triple (int_post) Q; mirror of divCallSeam, shared by div/mod)
  Vsa.Sim.valueBoolCallSeam                        # BoxSuffixSeams (item-3 box suffix for eq/ne: the jal value_bool box site via callSeg with the REAL value_bool_spec_full threaded as callee — Triple P (boxBool_pre) ≫ value_bool ≫ Triple (boxBool_post) Q; shared by eq/ne, seqz negation staged in the prefix)
  Vsa.Sim.value_bool_box                           # BoxSuffixSeams (value_bool_spec_full restated over named boxBool_pre/boxBool_post predicates, the clean seam API mirroring int_pre/int_post)
  Vsa.Sim.divValueTail                             # BinOpValueTails (full div value tail: dispatch+jal ≫ __divdi3 ≫ stage ≫ value_int ≫ epilogue, BOTH divdi3_spec + value_int_spec threaded via divCallSeam ∘ valueIntCallSeam; residual = the 3 concrete machine bridges pre/stage/suf)
  Vsa.Sim.modValueTail                             # BinOpValueTails (full mod value tail, sibling of divValueTail: moddi3_spec then value_int_spec threaded)
  Vsa.Sim.eqNeValueTail                            # BinOpValueTails (full eq/ne value tail: spill+jal ≫ value_equal ≫ stage(+seqz for ne) ≫ value_bool ≫ epilogue, BOTH value_equal_spec_full + value_bool_spec_full threaded via valueEqualCallSeam ∘ valueBoolCallSeam; shared by eq/ne, residual = pre/stage/suf)
  Vsa.Sim.divSlot_routes                           # EvalDivChain (item-1 entry-linkage: PROVES by decide the derived div op-table slot bytes 58 98 fe ff @ opTableBase+12 route the jr@0x80003558 exactly to the div arm 0x800037dc — the load-bearing constant for the evalDivChain_run clone of evalGeChain_run; cross-checked vs GeSlotPinned/AddSlotPinned)
  Vsa.Sim.divSlot_writeMap8                         # EvalDivChain (DivSlotPinned survives a disjoint writeMap8, clone of geSlot_writeMap8 — lets the div slot pin ride through the arm stack stores)
  Vsa.Sim.evalDivChain_run                          # EvalDivChain (item-1 ENTRY LINKAGE for div: shared dispatch prefix + jr@0x80003558 routing 0x8000351c→0x800037dc as a faithful clone of evalGeChain_run reusing gtChainB1/B2a/B2b VERBATIM, 16 steps; swaps only token 23→14, index 12→3, slot 0x80019fb4→0x80019f90 (divLds2/DivSlotPinned), target 0x80003628→0x800037dc; lands the divDispL pins x16=2/x10=2/x2=v2/x9=sret/x17=Wr/x19=Wl that divDispatchRow's SegPre consumes)
  Vsa.Sim.frame_ld                                  # SegFrameFacts (EXPONENTIATING frame-window tool: discharges any base-relative 8-byte LOAD MemFacts residual (the chain_facts leftover) from ONE FrameBundle — bounds by omega, byte pins from pop, returns the read bytes for the seg's lds; replaces the per-window spill_addr/read64_bytes ritual every blockC_* row repeats. Shared across div/mod/eq/ne/ge — same 1088-byte frame — and any sp-relative window in the tree)
  Vsa.Sim.frame_sd                                  # SegFrameFacts (companion for STORE windows: sd MemFacts (bounds only) from the FrameBundle)
  Vsa.Sim.frame_ea                                  # SegFrameFacts (the folded address arithmetic: eaddrM of a base-relative small-offset op = base+off, from the FrameBundle no-wrap bound — the spill_addr step, once)
  Vsa.Sim.frameBundle_writeLog                      # SegFrameFactsAuto (a FrameBundle survives the chain's threaded stores: pop survives writeLog, so a later block's loads read their still-populated threaded memory with the SAME bundle)
  Vsa.Sim.frame_ld_read                             # SegFrameFactsAuto (a ld window MemFacts whose byte list is the EXPLICIT frame read [popByte m fb.pop (base+off), …] — depends on base/off only, never on L, so the tactic assigns the seg's lds element with no occurs-check and no L reduction)
  Vsa.Sim.frame_sd_auto                             # SegFrameFactsAuto (a sd window MemFacts — bounds only, over ANY threaded memory; offset read off a.imm)
  Vsa.Sim.frame_ld_read_thru                        # SegFrameFactsAuto (CROSS-BLOCK load reader: a threaded-memory (writeLog σ.mem log) ld window read from the UNDERLYING σ.mem (writeLog-free byte terms), pins collapsed to σ.mem by store/load-window disjointness (writeLog_getElem_disjoint); closes div's D2 loads)
  Vsa.Sim.wlogM_store_offsets                       # SegFrameFactsAuto (ABSTRACT THE READ OVER wlogM: every write-log entry of a frame block body has address base+off_st for that store's own offset — proved once by induction, so a use site bounds the store log WITHOUT reducing wlogM)
  Vsa.Sim.wlogM_below                               # SegFrameFactsAuto (store-window disjointness DERIVED from wlogM_store_offsets: stores lie above the load window, hgap decide-able on the concrete body; never reduces wlogM)
  Vsa.Sim.srcVal_stepGM_ne                          # SegFrameFactsAuto (a source read survives a stepGM writing a different register — the frame base pinned in x2 survives the whole block since no instruction writes x2)
  Vsa.Sim.srcVal_runGM_ne                           # SegFrameFactsAuto (Fix 1a: a source read survives the WHOLE block's runGM pin-list fold when no body element writes it — proved by induction, discharges every leaf's hsrc/guard srcVal in O(1) structural work via srcval_peel, never reducing the runGM tower; the lever that kills the div per-leaf blowup)
  Vsa.Sim.eqDispatch_facts                          # SegFrameFactsAuto (ACCEPTANCE 1: the whole eq arm's ChainFacts bundle — six ld reloads + six sd spills — discharged from ONE FrameBundle σ.mem sp via the seg_frame_facts tactic; axiom-clean, ~2s)
  Vsa.Sim.eqDispatchRow_frame                       # SegFrameFactsAuto (ACCEPTANCE 3: composes eqDispatch_facts into eqDispatchRow → a live Triple whose entry SegFramePre needs only a FrameBundle + loaded image (no hand-assembled lds/ChainFacts) — the item-1 SegPre composition)
  Vsa.Sim.divDispatch_facts                         # SegFrameFactsAuto (ACCEPTANCE 2: the whole div arm's FOUR-block ChainFacts (cross-block D2 loads under D1's stores) discharged from ONE FrameBundle σ.mem v2 + Wr≠0, no seal/heartbeat bump — the KILLED kernel deep-recursion. Two structural fixes: srcval_peel/srcVal_runGM_ne peels the runGM pin tower per leaf; sffPeelMemEq peels identity stepMemM layers by explicit chained-rfl congruence instead of g.change's isDefEq (which whnf'd the writeLog fold on the 3rd cross-block load — the real blowup). Leaves exactly the divisor-nonzero beqz guard, supplied as Wr≠0)
  Vsa.Sim.divDispatchRow_frame                      # SegFrameFactsAuto (composes divDispatch_facts into divDispatchRow → live Triple; the div (cross-block) analogue of eqDispatchRow_frame, item-1 SegPre composition with Wr≠0)
  Vsa.Sim.divDispatchPost_of_chainEnd               # EvalDivArm (reusable chain-end→dispatch glue: from a config at the .div arm entry 0x800037dc with the divDispL pins + FrameBundle m0 v2 + Wr≠0, builds SegFramePre and runs divDispatchRow_frame → DivDispatchPost @0x8000381c; the .div analogue of invoking eqDispatchRow_frame from a caller)
  Vsa.Sim.evalDivChain_dispatch                     # EvalDivArm (the FULL-SPAN .div item-1 bridge 0x8000351c→0x8000381c: chains evalDivChain_run (entry linkage thru jr@0x80003558) onto divDispatchPost_of_chainEnd, landing DivDispatchPost from the binary-op arm-entry battery; divisor Wr = bytesVal MKind.ld [d0..d7], caller supplies Wr≠0 + FrameBundle σ.mem v2. Residual = value tail (divValueTail: __divdi3/value_int seams) + blockD_v_rec epilogue)
  Vsa.Sim.divPreBridge                              # EvalDivValueTail (value-tail item-2 PRE bridge: from DivDispatchPost @0x8000381c (x10=Wl,x11=Wr staged) the single jal __divdi3 @0x8000381c links x1:=0x80003820 → divdi3_pre Wl Wr 0x80003820 mA, the divValueTail `pre` premise; built on the generated DivTailSites battery. Caller obligations = the three divdi3/udivdi3 loaded preds on post-dispatch mem mA + Wr.toInt≠0 + ¬(Wl=INT64_MIN∧Wr=-1) + x12/x13 scratch presence, mirroring blockC_mul feeding muldi3_pre)
  # ── PHASE 3: generic binop item-1 entry-linkage generator + fan-out (BinopChainGen / BinopChainInstances / ModDispatchStrong / EvalModArm / EqNeDispatchStrong / EvalEqNeArm) ──
  Vsa.Sim.evalBinopChain_run                        # BinopChainGen (THE GENERATOR: generic binary-op item-1 entry linkage 0x8000351c→armPC, faithful generalisation of evalDivChain_run reusing gtChainB1/B2a/B2b VERBATIM, parameterised by the FOUR data points (tokBytes, idx, slotAddr, slotBytes, armPC) via four per-op decide hypotheses (hTokVal/hIndexVal/hSlotAddr/hRoutes). The heavy 16-step block-soundness proof elaborates ONCE here (~670ms); each op instance costs ~one composition. SlotPinned/binopLds1/binopLds2 generalise DivSlotPinned/divLds1/divLds2)
  Vsa.Sim.evalDivChain_run_gen                      # BinopChainInstances (VALIDATION: reproduces evalDivChain_run's EXACT conclusion (0x8000351c→0x800037dc, divDispL pins) via evalBinopChain_run at div's 4 data points (token 14/idx 3/slot 0x80019f90/bytes 58 98 fe ff/arm 0x800037dc); elab ~20ms vs 692ms hand)
  Vsa.Sim.modDispatchRowS                           # ModDispatchStrong (STRONG mod dispatch row 0x80003784→0x800037c4 → ModDispatchPostS (div-strength: ∃x12/x13, tick<2, sailOutput=out0, callee-saved frame); verbatim clone of divDispatchRow, mod PCs + modDispLS incl (12,15) op-token pin)
  Vsa.Sim.modDispatch_facts                         # ModDispatchStrong (mod arm four-block ChainFacts from ONE FrameBundle + Wr≠0; clone of divDispatch_facts, mod byte-identical to div)
  Vsa.Sim.modDispatchRow_frame                      # ModDispatchStrong (composes modDispatch_facts into modDispatchRowS → live Triple from SegFramePre + Wr≠0 → ModDispatchPostS; mod analogue of divDispatchRow_frame)
  Vsa.Sim.modDispatchPost_of_chainEnd               # EvalModArm (chain-end→dispatch glue: mod arm entry 0x80003784 + modDispLS pins + FrameBundle + Wr≠0 → ModDispatchPostS @0x800037c4; clone of divDispatchPost_of_chainEnd)
  Vsa.Sim.evalModChain_dispatch                     # EvalModArm (FULL-SPAN .mod item-1 bridge 0x8000351c→0x800037c4: generic evalBinopChain_run at mod's 4 data points (token 15/idx 4/slot 0x80019f94/bytes 00 98 fe ff/arm 0x80003784) chained onto modDispatchPost_of_chainEnd → ModDispatchPostS; caller supplies Wr≠0 + FrameBundle σ.mem v2; elab ~43ms)
  Vsa.Sim.eqDispatchRowS                            # EqNeDispatchStrong (STRONG eq dispatch row 0x800036e4→0x8000371c → EqDispatchPostS (x10=bufa=sp+0x40, x11=bufb=sp+0x20, x2=sp, tick<2, sailOutput=out0, callee-saved frame); single-block, no divisor guard)
  Vsa.Sim.neDispatchRowS                            # EqNeDispatchStrong (STRONG ne dispatch row 0x80003734→0x8000376c → NeDispatchPostS; byte-identical to eq, shifted PCs)
  Vsa.Sim.eqDispatchRow_frameS                      # EqNeDispatchStrong (composes eqDispatch_facts into eqDispatchRowS → live Triple from SegFramePre → EqDispatchPostS)
  Vsa.Sim.neDispatch_facts                          # EqNeDispatchStrong (ne single-block ChainFacts from ONE FrameBundle; clone of eqDispatch_facts)
  Vsa.Sim.neDispatchRow_frameS                      # EqNeDispatchStrong (composes neDispatch_facts into neDispatchRowS → live Triple → NeDispatchPostS)
  Vsa.Sim.eqDispatchPost_of_chainEnd                # EvalEqNeArm (chain-end→dispatch glue: eq arm entry 0x800036e4 + x2=sp + FrameBundle → EqDispatchPostS @0x8000371c)
  Vsa.Sim.neDispatchPost_of_chainEnd                # EvalEqNeArm (chain-end→dispatch glue: ne arm entry 0x80003734 + x2=sp + FrameBundle → NeDispatchPostS @0x8000376c)
  Vsa.Sim.evalEqChain_dispatch                      # EvalEqNeArm (FULL-SPAN .eq item-1 bridge 0x8000351c→0x8000371c: generic evalBinopChain_run at eq's 4 data points (token 19/idx 8/slot 0x80019fa4/bytes 60 97 fe ff/arm 0x800036e4) chained onto eqDispatchPost_of_chainEnd → EqDispatchPostS; caller supplies FrameBundle σ.mem sp; elab ~35ms)
  Vsa.Sim.evalNeChain_dispatch                      # EvalEqNeArm (FULL-SPAN .ne item-1 bridge 0x8000351c→0x8000376c: generic evalBinopChain_run at ne's 4 data points (token 17/idx 6/slot 0x80019f9c/bytes b0 97 fe ff/arm 0x80003734) chained onto neDispatchPost_of_chainEnd → NeDispatchPostS; caller supplies FrameBundle σ.mem sp; elab ~35ms)
  # ── M5 (stuck_sim) divergence half + trichotomy (Trichotomy / DivergeSim) ──
  Vsa.While.approx_of_stepClosed                    # Trichotomy (M5 divergence CONSTRUCTION, UNCONDITIONAL: from a step-closed spine predicate R (each R-node takes one SeqStep = normal head ExecS into another R-node), every member node is Approx n for ALL n — the fuel recursion Nat.rec on n, Approx.zero base, Approx.step peel; the honest core of BigStepDiverges)
  Vsa.While.bigStepDiverges_of_stepClosed           # Trichotomy (M5: BigStepDiverges p from a step-closed spine containing the root (initSt,0,0,p); approx_of_stepClosed at the root, UNCONDITIONAL)
  Vsa.While.trichotomy_of_dispatch                  # Trichotomy (M5 THE TRICHOTOMY, conditional on the classical per-node dispatch NodeDispatch (T terminate ∨ E ExecSeqErr ∨ S one-normal-step) + two routing residuals hroot (root T→∃out BigStep) + hExclude (a Spine node never fires T/E, so NodeDispatch's S is forced and Spine is step-closed) → Trichotomy = ∀p, (∃out,BigStep)∨BigStepErr∨BigStepDiverges. Divergence arm via bigStepDiverges_of_stepClosed on the inductive Spine p predicate — UNCONDITIONAL given the residuals; Classical.em at the root T/E split)
  Vsa.Sim.stepsN_truncate                           # DivergeSim (M5: a StepsN m run with n≤m has a length-EXACTLY-n prefix ∃c'', StepsN n c c''; pure StepsN algebra, induction on n — truncates the ≥n divergence run to the exact length Diverges demands)
  Vsa.Sim.divStep_run                               # DivergeSim (M5 divergence fuel recursion, the TripleN-shaped core: from Approx n and a corresponding config Corr c st d env ss, a run of length ≥n exists; structural induction on the Approx derivation, DivStep supplies ≥1 machine step per Approx.step to a tail-corresponding config, StepsN.trans_add composes; conditional only on the ONE per-step residual DivStep)
  Vsa.Sim.divergenceSim                             # DivergeSim (M5 THE DIVERGENCE FORWARD SIMULATION: BigStepDiverges p → Diverges c at a corresponding entry Corr c initSt 0 0 p; per fuel n, divStep_run (≥n) then stepsN_truncate (exact n); conditional only on the per-step progress residual DivStep Corr — the progress-only analog of the M4 exec_stmt case Triples / the 42 error-site residuals)
  Vsa.Sim.stuck_of_divergenceSim                    # DivergeSim (M5: divergenceSim composed with the committed stuck_of_halts_70 analog stuck_of_diverges → stuck_sim's Diverges disjunct; the divergence-arm mirror of stuck_of_bigStepErrFull)
  Vsa.Sim.loopStep                                 # LoopStep (L4: machine-side loop-iteration core — segEval_sound + back-edge PC + WinsInSA memory agreement; a loop row = #derive_case chain(s) + callStep seams + ONE loopStep + spec-side φ-glue)
  Vsa.Sim.LoopScaffoldClose.execStepNone_samePC    # LoopScaffoldClose (honest no-op row at a shared PC; the current arbitrary-p/q recursor motive remains a shape defect)
  Vsa.Sim.realloc_grow2_arena                       # EnvDefineClose (L5 brick 1: the grow-path ledger merge — two sequential successful realloc grows over ONE HeapArena ledger compose; Grow2Exts is again a HeapArena from the two results' disjointness clauses + set-like-ledger erase algebra. AInv re-establishment stays the grow block's obligation)
  Vsa.Sim.heapPublicFrame_trans                    # EnvDefineClose (L5 brick 1: two sequential public-memory frames compose over concatenated except-extents — the two-call four-extent footprint)
  Vsa.Sim.envDefMallocSplice                        # EnvDefCompose (Shape-D: env_define's malloc call splice prefix ≫ MallocContract.spec ≫ suffix over the plan's MallocSpec = MallocContract hypothesis; residual = the 2 concrete machine bridges pre/suf)
  Vsa.Sim.envDefReallocNamesSplice                  # EnvDefCompose (Shape-D: env_define's grow-path realloc(names) splice prefix ≫ ReallocOps.grow ≫ suffix; ReallocOps a hypothesis; residual = pre/suf machine bridges)
  Vsa.Sim.envDefAppendContract                      # EnvDefCompose (Shape-D COMPOSED: whole append path strlen ≫ malloc ≫ memcpy ≫ store as one callSeg-chain over strlen_spec + MallocContract.spec + memcpy_spec, all real; residual = the 4 straight-line machine bridges strlenPre/mallocPre/memcpyPre/store)
  Vsa.Sim.memcpy_spec_framed_byte                   # MemcpySpecFramed (memcpy byte-route with ABI register frame carried through; strlen frame primitives reused verbatim)
  Vsa.Sim.envDefMemcpyFramed                        # EnvDefCompose (memcpyFramed premise DISCHARGED from memcpy_spec_framed_byte; EnvDefFrame reconstructed via write-footprint containment)
  Vsa.Sim.envDefMemcpyFramedSplice                  # EnvDefCompose (frame-carrying memcpy splice; envDefAppendContract's memcpy seam now threads EnvDefFrame)
  Vsa.Sim.capComputePrefix_run                      # EnvDefBridges2 (grow-path cap-compute prefix run: slliw/slli/sw/mv/jal, first slliw machine site)
  Vsa.Sim.bridgeCapCompute_closed                   # EnvDefBridges2 (3rd Shape-A bridge closed: cap-compute → ReallocPre at realloc entry; residuals hpTie/hnTie/hAInvStableCap named)
  Vsa.Sim.loaded_envdef_writeMap4                   # EnvDefBridges2 (Env_defineLoaded survives disjoint 4-byte stores; grow-path sw reusable)
  Vsa.Sim.namesToValsPrefix_run                     # EnvDefBridges3 (grow-path staging run lw;sd;ld;slli;add;slli;jal — 4th of the prefix-run family, first RTYPE add site)
  Vsa.Sim.bridgeNamesToVals_closed                  # EnvDefBridges3 (4th Shape-A bridge closed: GrowEnvEntry → ReallocPre(vals); struct pins survive realloc via HeapPublicFrame)
  Vsa.Sim.bridgeNamesToVals_wired                   # EnvDefBridges3 (conseq adapter producing envDefGrowContract's bridgeNamesToVals premise verbatim)
  Vsa.Sim.frameRepr_append                          # EnvDefBridges3 (FrameRepr extended by one bound slot — shared core for bridgeStore + env_define-update + Call.closure env-fold)
  Vsa.Sim.mallocArgRow                              # EnvDefSeg (DEMO: malloc-prefix body as #derive_case seg — 58 hand lines → 14; region was already 106/106 tabled)
  Vsa.Sim.strlenArgRow                              # EnvDefSeg (strlen-prefix body as seg; jal stays the callSeg seam by design — TKind excludes calls)
  Vsa.Sim.bridgeOfSeg                               # BridgeSeg (the mkBridge combinator: seg run + FrameMeta ABI frame + jal transport, 3 decides per bridge; 4.9x fewer lines, 4.5x faster)
  Vsa.Sim.jalStep_of_obs                            # BridgeSeg (jal-seam glue factored once: PC/link readbacks + gprGet nonRa + ABI frame across the jal)
  Vsa.Sim.capComputeSeg_run                         # EnvDefSeg (DEMO: capCompute prefix via bridgeOfSeg — 350 hand lines/6.8s → 72 lines/1.5s; first slliw seg)
  Vsa.Sim.appendHeadRow                             # EnvDefBridges4 (grow-path append-head span as branch-terminated seg row; ~35 lines via segToTriple)
  Vsa.Sim.appendStoreRow                            # EnvDefBridges4 (append store block: 18-instr seg, 5-store write-log at the finalize tail; FrameRepr marshalling = frameRepr_append residual)
  Vsa.Sim.updateStoreRow                            # EnvDefBridges4 (update-path HIT store block seg; scan loop stays the loopFromBody seam)
  Vsa.Sim.frameRepr_of_appendStore                  # EnvDefMarshal (append store post → Store.define-extended FrameRepr carrier)
  Vsa.Sim.bridgeStore_wired                         # EnvDefMarshal (bridgeStore discharged: store row ≫ FrameRepr marshalling ≫ epilogue seam)
  Vsa.Sim.bridgeAppendHead_wired                    # EnvDefMarshal (bridgeAppendHead discharged via realloc_grow2_arena/heapPublicFrame_trans)
  Vsa.Sim.frameRepr_of_updateStore                  # EnvDefMarshal (update HIT store post → Store.define-UPDATE FrameRepr carrier)
  Vsa.Sim.hUpdate_wired                             # EnvDefMarshal (hUpdate discharged modulo the env_get scan-loop seam)
  Vsa.Sim.env_define_append_spec                    # EnvDefMarshal (CAPSTONE: envDefAppendContract with bridgeStore BUILT; gates hAssign/hSVarInit/Call.closure/InterpInitSpec)
  Vsa.Sim.envDefGrowContract                        # EnvDefCompose (Shape-D COMPOSED: whole grow path cap' ≫ realloc(names) ≫ realloc(vals) ≫ append-head as one callSeg-chain over ReallocOps.grow twice; residual = the 3 machine bridges capCompute/namesToVals/appendHead + the grow2 arena/frame algebra in EnvDefineClose)
  Vsa.Sim.envDefContract                            # EnvDefCompose (Shape-D TOP-LEVEL: env_define = dispatch ≫ (update ⊕ append ⊕ grow) join; append/grow segments built from the *Contract theorems over the real allocator contracts; residual = dispatch (prologue proved + scan loop) + per-path bridges)
  Vsa.Sim.erow_demo_seg                            # ErrorSiteRows (M5 Wave-D pilot: a real #derive_case (L3) run theorem for the pure stack-spill body 0x800034d0→0x800034e0 preceding the jal runtime_error @0x800034e4 — an eval_expr error-site path — in SegEvalState normal form; pins recipe step 2 on a genuine error-site body)
  Vsa.Sim.errRow                                   # ErrorSiteRows (M5 Wave-D pilot: the error-row template — a site's marshalled segment Triple SitePre (RuntimeErrorAt g inp m0) + shared SC/HT + reachability hsite ⇒ ErrHalts c, the exact errorSimFull minor-premise shape; thin wrapper over the committed L6 errHalts_exists_of_site)
  Vsa.Sim.row_hNotCallable                         # ErrorSiteRows (M5 Wave-D pilot row: discharges the errorSimFull hNotCallable minor premise (CallErr.notCallable) via errRow — one application per site; conditional on SC/HT + the site's segment Triple T + reachability hsite)
  Vsa.Sim.row_hNegType                             # ErrorSiteRows (M5 Wave-D pilot row: discharges the errorSimFull hNegType minor premise (EvalErr.negType, negate-non-int type error) via errRow)
  Vsa.Sim.row_hAssertFail                          # ErrorSiteRows (M5 Wave-D pilot row: discharges the errorSimFull hAssertFail minor premise (CallErr.assertFail, failed assert) via errRow)
  Vsa.Sim.row_hVarUndef                            # ErrorSiteRows2 (M5 Wave-D batch 2 leaf row: errorSimFull hVarUndef minor premise (EvalErr.varUndef, read unbound variable) via errRow)
  Vsa.Sim.row_hAssignUnbound                       # ErrorSiteRows2 (M5 Wave-D batch 2 leaf row: errorSimFull hAssignUnbound minor premise (EvalErr.assignUnbound, assign to unbound name) via errRow)
  Vsa.Sim.row_hBinaryOp                            # ErrorSiteRows2 (M5 Wave-D batch 2 leaf row: errorSimFull hBinaryOp minor premise (EvalErr.binaryOp, binary-op type error / division-by-zero binOpSem=none) via errRow)
  Vsa.Sim.row_hArity                               # ErrorSiteRows2 (M5 Wave-D batch 2 leaf row: errorSimFull hArity minor premise (CallErr.arity, closure arity mismatch) via errRow)
  Vsa.Sim.row_hDepth                               # ErrorSiteRows2 (M5 Wave-D batch 2 leaf row: errorSimFull hDepth minor premise (CallErr.depth, call-depth exceeded) via errRow)
  Vsa.Sim.row_hEscape                              # ErrorSiteRows2 (M5 Wave-D batch 2 leaf row: errorSimFull hEscape minor premise (CallErr.escape, break/continue escaping a call body) via errRow)
  Vsa.Sim.row_hAssertArity                         # ErrorSiteRows2 (M5 Wave-D batch 2 leaf row: errorSimFull hAssertArity minor premise (CallErr.assertArity, assert wrong arity) via errRow)
  Vsa.Sim.row_hUnaryE                              # ErrorSiteRows2 (M5 Wave-D batch 2 propagation row: errorSimFull hUnaryE minor premise (EvalErr.unaryE, unary operand errors) via errRow — sub-IH ignored under constant motive)
  Vsa.Sim.row_hCallF                               # ErrorSiteRows2 (M5 Wave-D batch 2 propagation row: errorSimFull hCallF minor premise (EvalErr.callF, call callee-expr errors) via errRow)
  Vsa.Sim.row_hExpr                                # ErrorSiteRows2 (M5 Wave-D batch 2 propagation row: errorSimFull hExpr minor premise (ExecErr.expr, expression-statement expr errors) via errRow)
  Vsa.Sim.loopDemo                                 # LoopStep (L4 demo: fabricated `j .` self-loop, one kernel decide for the structural VC, abstract pins/decode)
  Vsa.Sim.stuckSim                                  # DivergeSim (M5 THE ASSEMBLED stuck_sim: stuck_of_trichotomy ∘ (error arm ⊕ divergence arm) — from Trichotomy + the two packaged forward-sim implications + ¬∃out BigStep p → the stuck_sim disjunction. Mirrors Vsa.Refine.InterpSim.stuck_sim's per-program body exactly)
  Vsa.Sim.errHalts_of_site                         # ErrorSites (L6: per-error-site combinator — Triple SitePre (RuntimeErrorAt …) ⇒ Halts c out 70 via errorTailHalts_exit; one composition per error row, SC/HT supplied once at L7/L8)
  # L7/L8 close skeleton — term/stuck_sim → refinement (conditional)
  Vsa.Sim.TermSimClose.execSeq_sim_of_cases         # TermSimClose (L7: ExecSeq-rooted twin of term_sim_of_cases — same 9 motives + 50 premises via @ExecSeq.rec, exposes mExecSeq)
  Vsa.Sim.TermSimClose.termSimClosed                # TermSimClose (L7: InterpSim.term_sim from the 50-premise M4 bundle + the program-entry bridge hEntryHalts)
  Vsa.Sim.ImageGeom.stackBounds                     # TermImageGeom (shared static image geometry + dynamic frame facts → StackBounds)
  Vsa.Sim.imageGeom_of_addResid                     # TermImageGeom (compatibility bridge from the first concrete binary residual)
  Vsa.Sim.addResid_stackBounds                      # TermImageGeom (first case-row consumer of the shared geometry carrier)
  Vsa.Sim.TermCaseBundle.term_sim_of_bundle         # TermCaseBundle (generated named interface for all 50 mutual-recursion case premises)
  Vsa.Sim.TermCaseBundle.execSeq_sim_of_bundle      # TermCaseBundle (ExecSeq-rooted assembly from the same named bundle)
  Vsa.Sim.TermCaseBundle.termSimClosed_of_bundle    # TermCaseBundle (term_sim from the named bundle + sole entry bridge)
  Vsa.Sim.armPostGeom_of_addResid                   # rows/ArmPostGeom (step-1 alias: AddResid to shared ArmPostGeom 11 AddSlotPinned)
  Vsa.Sim.addResid_of_armPostGeom                   # rows/ArmPostGeom (step-1 alias inverse: shared ArmPostGeom back to AddResid)
  Vsa.Sim.armPostGeom_of_subResid                   # rows/ArmPostGeom (step-1 alias: SubResid to shared ArmPostGeom 12 SubSlotPinned)
  Vsa.Sim.subResid_of_armPostGeom                   # rows/ArmPostGeom (step-1 alias inverse for sub)
  Vsa.Sim.Rows.eval_int_row                         # rows/TermRouting (leaf pilot: fills the hInt premise slot via evalIntSimD)
  Vsa.Sim.Rows.eval_null_row                        # rows/TermRouting (leaf-bridge: fills hNull via EvalEntry to EvalNullEntry then evalNullSimD)
  Vsa.Sim.Rows.eval_bool_row                        # rows/TermRouting (leaf-bridge: fills hBool via EvalEntry to EvalBoolEntry then evalBoolSimD)
  Vsa.Sim.Rows.eval_str_row                         # rows/TermRouting (leaf-bridge: fills hStr via EvalEntry to EvalStrEntry then evalStrSimD; payload-ptr conjuncts forall-quantified, no CString readback)
  Vsa.Sim.Rows.eval_neg_row                         # rows/TermRouting (recursive pilot: fills hNeg via evalNegSim with NegExtras residual)
  Vsa.Sim.Rows.eval_not_row                         # rows/TermRouting (rec_not: fills hNot via evalNotSim with NotSimExtras residual)
  Vsa.Sim.Rows.eval_orTrue_row                      # rows/TermRouting (rec_logical1: fills hOrTrue via evalOrTrueSim with OrTrueExtras + aEnv3 x13 residual)
  Vsa.Sim.Rows.eval_andFalse_row                    # rows/TermRouting (rec_logical1: fills hAndFalse via evalAndSim with AndFalseExtras + aEnv3 x13 residual)
  Vsa.Sim.Rows.eval_orFalse_row                     # rows/TermRouting (rec_logical2 two-IH: fills hOrFalse via evalOrFalseSim with OrFalseExtras + aEnv3 x13 residual)
  Vsa.Sim.Rows.eval_andTrue_row                     # rows/TermRouting (rec_logical2 two-IH: fills hAndTrue via evalAndTrueSim with AndTrueExtras + aEnv3 x13 residual)
  Vsa.Sim.Rows.eval_var_row                         # rows/EvalVarRow (conditional leaf_bridge: fills hVar via evalVarSimD; VarLeafResid carries the env_get_found Triple oracle)
  Vsa.Sim.Rows.eval_var_row_fills_hVar              # rows/EvalVarRow (slot-verify: eval_var_row inhabits the exact hVar recursor-premise type)
  Vsa.Sim.varBridge_prefix                          # rows/EvalVarBridge (4-instr eval-var-arm caller prefix 0x80003434→env_get entry, from existing site batteries)
  Vsa.Sim.varBridge                                 # rows/EvalVarBridge (ArmEntryK→VarPostCall = prefix ≫ callee via VarCallLinkage typed seam)
  Vsa.Sim.varLeafResid_of_rowResid                  # rows/EvalVarBridge (discharges VarLeafResid's env_get_found oracle from varBridge)
  Vsa.Sim.eval_var_row_closed                       # rows/EvalVarBridge (hVar row with the oracle BUILT; residual = VarCallLinkage: x13=penv datum + FoundSt-at-frame/mem-frame post)
  Vsa.Sim.env_get_found_framed                      # EnvGetSpec10 (env_get FOUND with memory-frame post: wrote only [out,out+24) ∪ callee spill window; + hit-name/first-match exposed)
  Vsa.Sim.foundSt_of_storeRepr                      # EnvGetMarshal (StoreRepr at looked-up frame + immediate first-match → FoundSt; residual = EnvGetCallerGeom machine bundle)
  Vsa.Sim.envGetContract_of_storeRepr               # EnvGetMarshal (combined marshalling incl. spec verdict via get?_immediate_hit; reusable for env_define call sites)
  Vsa.Sim.envGetFramed_triple                       # rows/EvalVarBridgeCallee (EnvGetEntryV → EnvGetFramedPost from the marshalling + framed post)
  Vsa.Sim.varCallLinkage_callee                     # rows/EvalVarBridgeCallee (VarCallLinkage.callee DISCHARGED modulo EnvGetCallerGeom/FrameStackDisj/VarPostRepack named caller premises)
  Vsa.Sim.execExitD_of_execExit                     # rows/ExecCaseGeom (ExecExit + ExecLeafWiden to ExecExitD; the statement shape-gap bridge, LeafWiden twin)
  Vsa.Sim.execBrkSimD                               # rows/ExecCaseGeom (ExecS.brk at ExecExitD via execBrkSim + ExecCaseGeom widener; the ExecIH motive shape)
  Vsa.Sim.execContSimD                              # rows/ExecCaseGeom (ExecS.cont at ExecExitD via execContSim + ExecCaseGeom widener)
  Vsa.Sim.Rows.exec_brk_row                         # rows/ExecRouting (statement leaf pilot: fills the hSBrk premise slot via execBrkSimD, GENERATED)
  Vsa.Sim.Rows.exec_cont_row                        # rows/ExecRouting (statement leaf: fills hSCont via execContSimD, GENERATED)
  Vsa.Sim.execExitD_of_execExit_rec                 # rows/ExecRecRows (recursive-shaped ExecExit→ExecExitD bridge: non-identity-φ widener ExecRecWiden)
  Vsa.Sim.execExprSimD                              # rows/ExecRecRows (ExecS.expr at ExecExitD via execExprSim + ExecRecWiden; sub-EvalIH by rfl)
  Vsa.Sim.execRetSimD                               # rows/ExecRecRows (ExecS.ret at ExecExitD via execRetSim; retslot geometry in ExecRetGeom)
  Vsa.Sim.execRetNullSimD                           # rows/ExecRecRows (ExecS.retNull at ExecExitD; hGlue = named value_null-bridge residual)
  Vsa.Sim.Rows.exec_expr_row                        # rows/ExecRecRows (recursive statement row: fills hSExpr)
  Vsa.Sim.Rows.exec_ret_row                         # rows/ExecRecRows (recursive statement row: fills hSRet)
  Vsa.Sim.Rows.exec_retNull_row                     # rows/ExecRecRows (statement row: fills hSRetNull modulo named hGlue)
  Vsa.Sim.evalExitD_of_evalExit_rec                 # rows/CallRows (eval-side rec-widener bridge: EvalExit ∧ EvalRecWiden → EvalExitD at non-identity φ)
  Vsa.Sim.evalCallSimD                              # rows/CallRows (evalCallSim relanded at EvalExitD via EvalRecWiden)
  Vsa.Sim.evalFnSimD                                # rows/CallRows (evalFnSim relanded at EvalExitD; φc grows by one closure)
  Vsa.Sim.Rows.eval_argsNil_row                     # rows/CallRows (fills hArgsNil; ArgsNilResid = loop→cont blez fall-through hop)
  Vsa.Sim.Rows.eval_argsCons_row                    # rows/CallRows (fills hArgsCons; ArgsConsResid = EvalArgsStep body oracle + nil hop)
  Vsa.Sim.Rows.eval_callPrint_row                   # rows/CallRows (fills hCallPrint; residual = NativePrintSpec)
  Vsa.Sim.Rows.eval_callPrintln_row                 # rows/CallRows (fills hCallPrintln; residual = NativePrintlnSpec)
  Vsa.Sim.Rows.eval_callAssertOk_row                # rows/CallRows (fills hCallAssertOk; residual = NativeAssertOkSpec)
  Vsa.Sim.Rows.eval_call_row                        # rows/CallRows (fills hCall; residual = CallArmSpec + EvalRecWiden)
  Vsa.Sim.Rows.eval_fn_row                          # rows/CallRows (fills hFn; residual = FnArmSpec + EvalRecWiden)
  Vsa.Sim.Rows.eval_callClosure_row                 # rows/CallClosureRow (fills hCallClosure — THE 50TH ROW; params-fold via storeChainList; depth guard threaded; body-IH by rfl)
  Vsa.Sim.Rows.eval_callClosure_row_fills_hCallClosure  # rows/CallClosureRow (slot-verify vs the verbatim hCallClosure premise)
  Vsa.Sim.Rows.argsConsResid_of_oracle              # rows/CallResidProviders (ArgsConsResid via evalArgsStepOf; residual = ArgsBodyOracle + ArgsPhiGlue + hnil)
  Vsa.Sim.Rows.argsNilResid_of_hop                  # rows/CallResidProviders (ArgsNilResid from the guarded ArgsNilHop — blez@0x800031d8 needs a5=0 pin SegEntry lacks)
  Vsa.Sim.Rows.nativePrintSpec_of_span              # rows/CallResidProviders (NativePrintSpec = shared NativeDispatchSpan + print NativeBodyContract)
  Vsa.Sim.Rows.nativePrintlnSpec_of_span            # rows/CallResidProviders (println = print body ≫ trailing fputc newline)
  Vsa.Sim.Rows.nativeAssertOkSpec_of_span           # rows/CallResidProviders (assertOk via the same shared dispatch span)
  Vsa.Sim.evalExit_rebase                           # rows/CallArmEpilogue (EvalExit rebase helper for the φc-widened epilogue)
  Vsa.Sim.blockD_v_phic                             # rows/CallArmEpilogue (φc-widened blockD_v: PhiExtends non-identity; unlocks CallArmSpec/FnArmSpec epilogues)
  Vsa.Sim.site_80004124_taken_es                    # rows/ExecRetNullGlue (beqz-TAKEN site battery for the retNull value_null bridge; assembly = named residual)
  Vsa.Sim.stepOnce_tohost_G                          # TermEntry (M4/M6: exit-store stepOnce halts, generic exit code e — exit-70 sibling generalized)
  Vsa.Sim.hPrologue_of                               # EntryHalts (M6: hPrologue = prologue-span ≫ mExecSeq (p q instantiated at loop head/normal exit) ≫ epilogue-span)
  Vsa.Sim.hEntryHalts_of                             # EntryHalts (M6: hEntryHalts discharged to EntryPrologueSpan + EntryEpilogueSpan via entryHalts; exact termSimClosed premise type)
  Vsa.Sim.restoreRetChain_run                        # EntryHaltsSpans (shared parameterised restore battery: icB1 body factored; exit-70 and exit-0 = two instances differing in latched a0)
  Vsa.Sim.entryEpilogueSpan_of                       # EntryHaltsSpans (EntryEpilogueSpan closed modulo EpilogueFrame — the concrete interpRunLayout frame-geometry discharge)
  Vsa.Sim.entryPrologueSpan_of                       # EntryHaltsSpans (EntryPrologueSpan from StoreInitSeam; setjmp first-return = REUSED setjmp_spec)
  Vsa.Sim.hEntryHalts_closed                         # EntryHaltsSpans (hEntryHalts CLOSED modulo StoreInitSeam + EpilogueFrame — the two honest program-entry seams)
  Vsa.Sim.epilogueControl_of_segExit                 # EntrySeams (4 of 5 EpilogueFrame control conjuncts = direct SegExit projections)
  Vsa.Sim.storeInitSeam_of_initRepr                  # EntrySeams (StoreInitSeam localized to InterpInitStoreRepr — the off-path interp_init store build, spans decoded)
  "Vsa.Sim.hEntryHalts_closed'"                      # EntrySeams (entry premise now rests ONLY on EpilogueSpill + InterpInitStoreRepr; NAME HAS A PRIME — must stay quoted in this bash array)
  Vsa.Sim.initStore_eq_initSt                        # InterpInit (env_new + 3x Store.define = initSt.store, by rfl, AXIOM-FREE)
  Vsa.Sim.interpInitStore_compose                    # InterpInit (env_new ≫ define print/println/assert ≫ epilogue store composition via InitSeg carriers)
  Vsa.Sim.interpInitStoreRepr_of_drive               # InterpInit (InterpInitStoreRepr CLOSED modulo the 4 InitSeg call seams + hRoutePrintln + the loop-head drive)
  Vsa.Sim.storeChainList                             # StoreSeg (variable-arity env-call fold — the Call.closure params-fold skeleton; subsumes InitSeg via Ent morphisms)
  Vsa.Sim.interpInitStore_compose_viaStoreSeg        # StoreSeg (DEMO: InterpInit's composition through storeChain3 with dimap-reindexed seams, R8-clean)
  Vsa.Sim.execVarDeclSimD                            # rows/ExecVarInitRow (varInit at ExecExitD via ExecRecWiden; define grows the binding list)
  Vsa.Sim.Rows.exec_varInit_row                      # rows/ExecVarInitRow (fills hSVarInit; env_define callee in the ExecVarInitGeom.hGlue oracle; slot-verified)
  Vsa.Sim.Rows.eval_assign_row                       # rows/EvalAssignRow (fills hAssign conditional on AssignArmSpec; arm decoded 0x8000347c-0x800034b8, callee env_set@0x80002cdc; slot-verified)
  Vsa.Sim.exitStoreHalts0                            # TermEntry (M4/M6: clean-exit(0) store → HTIF-halt-0 bridge; exit-0 twin of exitStoreHalts)
  Vsa.Sim.cleanExitTail                              # TermEntry (M4/M6: .normal-return continuation → Halts c out 0, via ExitTailChain0 + exitStoreHalts0)
  Vsa.Sim.entryHalts                                 # TermEntry (M4/M6: hEntryHalts discharged — clean-exit(0) entry bridge; conditional on prologue-bridge + tail-span residuals)
  Vsa.Sim.StuckSimClose.stuckSimClosed              # StuckSimClose (L8: InterpSim.stuck_sim per (p,c) from Trichotomy + divergence Corr/DivStep/entry + the 42 error-site residuals)
  Vsa.Sim.InterpSimBundle.errFamily_of_sites        # InterpSimBundle (M5 error family: ErrFamily L from the 42 per-error-site residuals, c-generalized)
  Vsa.Sim.errFamilyClosed                           # rows/ErrorRouting (herrFam: 42/42 premises routed onto the 19 errSite rows; residual = per-premise hsite + ErrShared SC/HT)
  Vsa.Sim.interpContSeg_of                          # ExitPathSpans (InterpContSeg discharged: interp_run setjmp-continuation -> AtMainRet)
  Vsa.Sim.InterpSimFinal.interpSim_conditional      # InterpSimFinal (ENDGAME CAPSTONE, field form: InterpSim L = ⟨hterm, hstuck⟩)
  Vsa.Sim.InterpSimFinal.stuckField_of_families     # InterpSimFinal (stuck_sim field from Trichotomy + DivFamily + ErrFamily)
  Vsa.Sim.InterpSimFinal.interpSimClosed_of_families # InterpSimFinal (ENDGAME CAPSTONE, families form: InterpSim L from term arm + M5 families)
  Vsa.Sim.InterpSimFinal.refinement_conditional     # InterpSimFinal (conditional refinement: full behavioral correspondence from the capstone)
  Vsa.Sim.TermAssembly.termCases_of_residuals       # TermAssembly (record fill: all 50 TermCases fields from the landed rows)
  Vsa.Sim.TermAssembly.hterm_of_residuals           # TermAssembly (the hterm arm via termSimClosed_of_bundle + hEntryHalts_closed')
  Vsa.Sim.TermAssembly.hdivFam_of_residuals         # TermAssembly (DivFamily via the DivCorrFamily reduction)
  Vsa.Sim.TermAssembly.divStep_vacuous              # TermAssembly (cheap DivStep arm — localizes the gap to the entry Corr)
  Vsa.Sim.TermAssembly.errFamily_ofShared           # TermAssembly (ErrFamily supplier: errFamilyClosed + ErrShared + 43 hsites)
  Vsa.Sim.TermAssembly.interpSim_of_residuals       # TermAssembly (ENDGAME CAPSTONE: InterpSim L from TermResiduals ALONE — the remaining project is this structure's fields)
  Vsa.Sim.TermAssembly.refinement_of_residuals      # TermAssembly (conditional refinement from TermResiduals)
  Vsa.Sim.Trichotomy.nodeDispatch_of_stmtDispatch   # Trichotomy (NodeDispatch from the sharper single-statement StmtDispatch atom; all seq plumbing discharged)
  Vsa.Sim.Trichotomy.bigStep_of_execSeq_normal      # Trichotomy (hroot normal-completion case fully discharged)
  Vsa.Sim.Trichotomy.trichotomy_of_stmtDispatch     # Trichotomy (htri REDUCED to StmtDispatch + hExclude — both pure While-layer, no Sail state)
  Vsa.Sim.DivFamily.divFamily_of_corr               # DivFamily (hdivFam ← DivCorrFamily: the named machine gate, supplied by the same forward-sim Triples as hterm)
  Vsa.While.hExclude_entails_false                  # While/StmtDispatch (SPEC BUG witness: the §1-§4 hExclude is unsatisfiable — Spine.base holds for every program)
  Vsa.While.stmtDispatch_eq_stmtDispatch3_false     # While/StmtDispatch (the landed StmtDispatch = StmtDispatch3 with divergence disjunct False — pinpoints the gap)
  Vsa.While.whileTrue_sapprox                       # While/StmtDispatch (while(true){} head still-running for EVERY fuel — the SApprox family works)
  Vsa.While.loopP_diverges                          # While/StmtDispatch (AMENDMENT DEMO: BigStepDiverges [while(true){}] now PROVED — the bug is fixed)
  Vsa.While.approx_of_nodeDispatch4                 # While/Trichotomy §5 (non-terminating non-erroring nodes are Approx n for all n; exclusion PROVED by contraposition)
  Vsa.While.trichotomy_of_dispatch4                 # While/Trichotomy §5 (repaired trichotomy: only NodeDispatch4 + hroot — hExclude eliminated)
  Vsa.While.nodeDispatch4_of_stmtDispatchD          # While/Trichotomy §5 (per-statement atom lifts to the 4-way node dispatch)
  Vsa.While.trichotomy_of_stmtDispatchD             # While/Trichotomy §5 (FINAL htri reduction: StmtDispatchD + hroot — both honestly provable)
  Vsa.While.progress                                # StmtDispatchClose (fuel-bounded classical mutual progress over all 6 judgments)
  Vsa.While.stmtDispatchD_holds                     # StmtDispatchClose (the classical mutual totality induction — no holes after the 3-rule amendment)
  Vsa.While.trichotomy_unconditional                # StmtDispatchClose (htri UNCONDITIONAL: CallErr.badClosure + BigStepErr TopAbrupt disjunction + ExecInit swallow; premise-free Trichotomy)
  Vsa.While.htri_unconditional                      # StmtDispatchClose (the htri slot of interpSimClosed_of_families, closed outright; M5 side gains hBadClosure + hTopAbrupt named routes)
  # M4 binary-op dispatcher (rows/BinArmBridge + rows/BinDispatchRow)
  Vsa.Sim.blockA_binaryArm                          # rows/BinArmBridge (op-independent EX_BINARY arm entry bridge: EvalEntry (.binary op) -> the blockB_binary ArmEntryK entry)
  Vsa.Sim.eval_binary_row                           # rows/BinDispatchRow (hBinary DISPATCHER: binOpSem-inversion routes all 10 int cells through binRow_<op>; 5 str cells + div-overflow = named EvalIH residual slots)
  binary_row_fills_hBinary                          # rows/BinDispatchProbe (slot-verify: eval_binary_row inhabits the exact hBinary recursor-premise type)
  Vsa.Sim.eval_binary_row_str_closed                # rows/BinStrCells (str cells factored: 6 loose hStr slots → StrCmpCellResid×4 thin + StrConcatCellResid; cmp route = strcmp seam + shared sign tail, concat blocked on stringify spec)
  Vsa.Sim.sTailLtRow                                # rows/StrCmpSignTail (lt sign-test tail seg row; gprGet posts, DivDispatchSeg idiom)
  Vsa.Sim.sTailGtRow                                # rows/StrCmpSignTail (gt sign-test tail; TAKEN-branch end-PC literal fixed +4)
  Vsa.Sim.sTailLeRow                                # rows/StrCmpSignTail (le sign-test tail)
  Vsa.Sim.strCmpCell_lt_of                          # rows/StrCmpBlockC (StrCmpCellResid provider; residual = StrArmMachineResid + StrCmpOrderBridge)
  Vsa.Sim.strCmpCell_le_of                          # rows/StrCmpBlockC (le provider)
  Vsa.Sim.strCmpCell_gt_of                          # rows/StrCmpBlockC (gt provider)
  Vsa.Sim.strCmpCell_ge_of                          # rows/StrCmpBlockC (ge provider; ge tail = landed cmpFixupTail)
  Vsa.Sim.strKindCheckRow                           # rows/StrArmChain (kind-3 branch span seg row)
  Vsa.Sim.strRejoinRow                              # rows/StrArmChain (strcmp-ret rejoin seg row: ld;mv;j → shared sign tail)
  Vsa.Sim.strArmFront                               # rows/StrArmChain (strcmp_full_spec ≫ rejoin ≫ SignTailLeg ≫ value_bool box, the blockC_eqne_front analogue)
  Vsa.Sim.strArmMachineResid_of                     # rows/StrArmChain (StrArmMachineResid = StrArmPrologue ≫ strArmFront; four op instances land)
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
    m = re.search(r"'(.*)' depends on axioms: \[([^\]]*)\]", line)
    if m:
        seen += 1
        axs = {a.strip() for a in m.group(2).split(",") if a.strip()}
        extra = axs - allowed
        if extra:
            bad.append(f"{m.group(1)}: disallowed axioms {sorted(extra)}")
        continue
    m = re.search(r"'(.*)' does not depend on any axioms", line)
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
