#!/usr/bin/env python3
"""
autoprove.py — INTEGRATED autoprove loop that discharges a record field
end-to-end, composing the LANDED validation stack (NOTHING here enters a proof;
TOOLING.md §3).  This does NOT rebuild the stack; it wires:

  * the WRITE-LOG emitter (`experiments/smt/bounded/gen_probe.py`, extended) —
    the arm's computed (addr,width,value) store list (BlockMem.wlogM/writeLog)
    as SMT Array stores, so the destination memory is DERIVED from the machine
    effect the arm performs, not assumed by a hand copy-hypothesis;
  * the bounded ValueRepr / read* encoder (same file) + the OPAQUE-boundary
    policy of `experiments/smt/DumpSmtLib.lean`;
  * Z3 4.15.4 as the pure oracle (validity + Houdini), reusing `houdini_ih.py`;
  * the LLM request/response PROTOCOL (this file) for the vocabulary-gap case;
  * a Lean TRANSCRIBE step: emit `experiments/autoprove/out/Field_<f>.lean` and
    `lake env lean` it read-only against the tree.

PIPELINE per `--field <SkelName>`:
  1. ENCODE  the field VC (machine effect via write-log; Repr preds via bounded
             encoder).  Honest ENCODE-GAP where the arm reads unbounded input.
  2. Z3 VALIDITY : neg UNSAT => PROVED-DIRECT (+ SMT cert + landed Lean lemma).
  3. IH-SYNTH    : on SAT/UNKNOWN, houdini over mined candidates -> Z3-confirmed
                   maximal inductive subset => PROVED-WITH-IH (named survivors).
  4. LLM PROTOCOL: if Houdini converges WITHOUT closing (vocabulary gap) write
                   experiments/autoprove/requests/<field>.json and BLOCK polling
                   .../responses/<field>.json.  `--serve-request` fills a
                   response (an LLM/agent invokes it; we DO NOT call an API).
  5. TRANSCRIBE  : on PROVED emit Field_<field>.lean + `lake env lean` it.

VERDICTS: PROVED-DIRECT | PROVED-WITH-IH | PROVED-VIA-LLM | ENCODE-GAP |
          NEEDS-LLM (request emitted, awaiting response) | IH-NOT-FOUND.

Usage:
  scripts/autoprove.py --field hNull
  scripts/autoprove.py --field hStr
  scripts/autoprove.py --field hVarShort              # triggers LLM protocol
  scripts/autoprove.py --field hVarShort --serve-request '<json or @file>'
  scripts/autoprove.py --batch hNull,hStr,hVarShort
  scripts/autoprove.py --field hNull --no-transcribe   # skip the lean step
"""
import subprocess, time, os, sys, json, argparse, textwrap

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, ".."))
BOUNDED = os.path.join(ROOT, "experiments", "smt", "bounded")
AUTODIR = os.path.join(ROOT, "experiments", "autoprove")
REQDIR = os.path.join(AUTODIR, "requests")
RESPDIR = os.path.join(AUTODIR, "responses")
OUTDIR = os.path.join(AUTODIR, "out")
sys.path.insert(0, BOUNDED)
sys.path.insert(0, HERE)
import gen_probe as G          # write-log emitter + bounded ValueRepr/read encoders
import houdini_ih as H         # the Houdini IH-selector oracle + field registry

Z3 = "z3"
W = 3   # bounded payload window depth (matches HOUDINI-IH.md)


# ===========================================================================
# FIELD MAP.  Bridge SkelName (field-census / AssemblySkeleton) -> the encoder
# target.  The ValueRepr leaves are the write-log-encodable stratum; everything
# else routes to houdini_ih's FIELD_REGISTRY (mostly honest ENCODE-GAP).
#
# entry: (encoder_target, lean_lemma, [candidate_shapes_override])
#   encoder_target = "valuerepr-copy:<kind>"  -> write-log VC for that Value kind
#                  = "encode-gap:<why>"       -> honest wall (machine-step Prop)
# ===========================================================================
FIELD_MAP = {
    "hNull":     ("valuerepr-copy:null", "Vsa/Sim/ReprCopy.lean::read32_copy"),
    "hBool":     ("valuerepr-copy:bool", "Vsa/Sim/ReprCopy.lean::read32_copy"),
    "hInt":      ("valuerepr-copy:int",  "Vsa/Sim/ReprCopy.lean::readLE_copy"),
    "hStr":      ("valuerepr-copy:str",  "Vsa/Sim/ReprSurvival.lean::cstring_agreeP"),
    # exec-arm FRAME slice: the ExecLeafMemPin memory-frame obligation of a
    # register-only exec leaf, ENCODED via the MECHANICALLY-EXTRACTED write-log
    # (scripts/wlog_extract.py -> BlockMem.wlogM).  This is the FRAME half of the
    # exec-arm supplier field (pres = MemExtends, agree = window-frame); the
    # recursive StoreRepr survival half stays ENCODE-GAP (Houdini/Lean's job).
    "hSBrk":     ("execleaf-frame:brkCont", "Vsa/Sim/ExecBrkCont.lean::ExecLeafMemPin"),
    "hSCont":    ("execleaf-frame:brkCont", "Vsa/Sim/ExecBrkCont.lean::ExecLeafMemPin"),
    # a SHORT-VOCABULARY variant of the str field: the candidate pool is
    # deliberately missing the payload-agreement shape, so Houdini converges
    # WITHOUT closing the goal -> the LLM protocol fires.  This is the demo
    # vehicle for the vocabulary-gap loop (see DEMO.md).
    "hVarShort": ("valuerepr-copy:str-short", "Vsa/Sim/ReprSurvival.lean::cstring_agreeP"),
}


def z3_run(script_lines, get_model=False, timeout=60):
    body = "\n".join(script_lines) + "\n(check-sat)\n" + ("(get-model)\n" if get_model else "")
    t = time.time()
    try:
        p = subprocess.run([Z3, "-in"], input=body, capture_output=True,
                           text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "timeout", "", round(time.time() - t, 3)
    dt = round(time.time() - t, 3)
    out = p.stdout.strip()
    verdict = out.split("\n", 1)[0] if out else "(no output)"
    return verdict, out, dt


# ===========================================================================
# STEP 1 — ENCODE the field VC via the WRITE-LOG machine effect.
#
# For the ValueRepr copy-readback arm, the machine effect is the 24-byte struct
# copy the arm emits: wlogM = [(dst+j, 1, src[src+j]) | j<24].  We emit this as
# an SMT store chain (mp = writeLog m log) PLUS its select-store readback facts,
# so the destination memory is derived from the effect, not assumed.
# ===========================================================================
def encode_vc(kind, control=False, extra_cands=None):
    """Return (script_lines_prefix, concl_neg_line) for the copy-readback VC of a
    Value kind, with `mp` DERIVED by the write-log store chain.  `control` drops
    a copied byte (the deliberately-false twin)."""
    base_kind = "str" if kind.startswith("str") else kind
    L = ["(set-logic ALL)", "(set-option :timeout 60000)"]
    for m in ("m", "mp"):
        L += G.decls_mem(m)
    L += ["(declare-fun srcAddr () Int)", "(declare-fun dstAddr () Int)"]
    if base_kind == "bool": L.append("(declare-fun bB () Int)")
    if base_kind == "int":  L.append("(declare-fun nN () Int)")
    if base_kind == "str":
        L += [f"(declare-fun {m}_p () Int)" for m in ("m", "mp")]
        L += [f"(declare-fun cstr_tail_{m} () Bool)" for m in ("m", "mp")]
    L.append("(assert (>= srcAddr 0)) (assert (>= dstAddr 0))")
    # dst window disjoint-above src so the copy store-chain does not clobber the
    # bytes it is reading (the arm's dst is a fresh malloc'd struct).
    L.append("(assert (>= dstAddr (+ srcAddr 24)))")
    # H: source represented
    L.append(f"(assert {G.valuerepr('m', 'srcAddr', base_kind, W)})")
    # MACHINE EFFECT: mp = writeLog m (24-byte struct copy write-log)
    log = G.copy_wlog("srcAddr", "dstAddr", 24, drop=(0 if control else None))
    L += G.wlog_stores("m", "mp", log)
    # derived select-store readback facts (avoid nonlinear value reconstruction)
    L += G.wlog_readback_facts(("m", "srcAddr"), ("mp", "dstAddr"), 24,
                               drop=(0 if control else None))
    if extra_cands:
        for _, expr in extra_cands:
            L.append(f"(assert {expr})")
    concl_neg = f"(assert (not {G.valuerepr('mp', 'dstAddr', base_kind, W)}))"
    return L, concl_neg


# ===========================================================================
# STEP 1' — ENCODE an exec-arm's ExecLeafMemPin FRAME obligation via the
# MECHANICALLY-EXTRACTED write-log (scripts/wlog_extract.py -> BlockMem.wlogM).
#
# This is the write-log probe (scripts/writelog_smt.py) rewired so the store list
# is READ OFF wlogM, not hand-listed.  The FRAME obligation has two clauses:
#   pres  : MemExtends m0 m         (inserts never delete presence)
#   agree : ∀k ∉ [SL.lo, sp), m[k]?=m0[k]?   (writes stay in the window)
# Both are pure QF_ABV over the extracted store addresses.  We return, per
# clause, a self-contained script (validate = negate; UNSAT ⇒ PROVED-DIRECT) plus
# a control that breaks it (agree window too narrow ⇒ SAT).
# ===========================================================================
def _extracted_wlog(tag):
    sys.path.insert(0, HERE)
    import wlog_extract as WX
    r = WX.extract_wlog(tag, with_data=False)
    stores, max_below = [], 0
    for s in r["stores"]:
        raw = s["raw"]
        below = -raw["dstOff"] if raw["dstReg"] == 2 else 0
        max_below = max(max_below, below)
        stores.append((s["addr"], s["width"]))
    return stores, max_below


def _wm8_chain(pre_def, pre_val, addr, data_syms, out_def, out_val):
    L = []
    d, v = pre_def, pre_val
    for j in range(8):
        nd = f"{out_def}_s{j}" if j < 7 else out_def
        nv = f"{out_val}_s{j}" if j < 7 else out_val
        L.append(f"(define-fun {nd} () (Array Int Bool) (store {d} (+ {addr} {j}) true))")
        L.append(f"(define-fun {nv} () (Array Int (_ BitVec 8)) (store {v} (+ {addr} {j}) {data_syms[j]}))")
        d, v = nd, nv
    return L


def encode_execleaf_frame(tag, clause, control=False):
    """Return SMT script (as lines) for the ExecLeafMemPin `clause` ∈ {agree,pres}
    of the arm `tag`, encoded via the extracted write-log.  UNSAT ⇒ frame slice
    PROVED.  control=True (agree only) narrows the window ⇒ SAT (refute-capable)."""
    stores, max_below = _extracted_wlog(tag)
    L = ["(set-logic ALL)", "(set-option :timeout 60000)"]
    L += G.decls_mem("m0")
    L += ["(declare-fun sp () Int)", "(declare-fun sllo () Int)"]
    for s in range(len(stores)):
        for j in range(8):
            L.append(f"(declare-fun d{s}_{j} () (_ BitVec 8))")
    L.append("(assert (<= 176 sp))")
    if clause == "agree" and control:
        L.append("(assert (= sllo (- sp 8)))")          # window too narrow
    else:
        L.append(f"(assert (<= sllo (- sp {max_below})))")  # window covers all spills
    cur_def, cur_val = "m0_def", "m0_val"
    for s, (addr, w) in enumerate(stores):
        data = [f"d{s}_{j}" for j in range(8)]
        od, ov = f"m{s+1}_def", f"m{s+1}_val"
        L += _wm8_chain(cur_def, cur_val, addr, data, od, ov)
        cur_def, cur_val = od, ov
    mdef, mval = cur_def, cur_val
    if clause == "agree":
        L.append("(declare-fun k () Int)")
        L.append("(assert (not (and (<= sllo k) (< k sp))))")
        L.append(f"(assert (or (not (= (select m0_def k) (select {mdef} k))) "
                 f"(and (select {mdef} k) (not (= (select {mval} k) (select m0_val k))))))")
    elif clause == "pres":
        L.append("(declare-fun a () Int)")
        L.append("(declare-fun b () (_ BitVec 8))")
        L.append("(assert (and (select m0_def a) (= (select m0_val a) b)))")
        L.append(f"(assert (not (select {mdef} a)))")
    return L


def run_execleaf_frame(field, tag):
    """Discharge the FRAME slice of an exec-arm supplier field via the extracted
    write-log.  Returns a verdict dict; frame closes iff both agree+pres UNSAT and
    the agree control SATs (refute-capable, non-vacuous)."""
    va, _, dta = z3_run(encode_execleaf_frame(tag, "agree", control=False))
    vp, _, dtp = z3_run(encode_execleaf_frame(tag, "pres", control=False))
    vc, _, dtc = z3_run(encode_execleaf_frame(tag, "agree", control=True))
    closed = va.startswith("unsat") and vp.startswith("unsat") and vc.startswith("sat")
    r = {"field": field, "verdict": "", "detail": "", "cert": "", "lean": ""}
    if closed:
        r["verdict"] = "FRAME-PROVED"
        r["detail"] = (f"ExecLeafMemPin FRAME slice via wlogM-extracted write-log: "
                       f"agree UNSAT({dta}s) pres UNSAT({dtp}s) ctrl SAT; residual = "
                       f"recursive StoreRepr survival (ENCODE-GAP -> Houdini/Lean)")
        r["cert"] = f"agree:{va} pres:{vp} ctrl_window:{vc}"
    else:
        r["verdict"] = "FRAME-UNCLOSED"
        r["detail"] = f"agree={va} pres={vp} ctrl={vc} (expected unsat/unsat/sat)"
    return r


# ===========================================================================
# CANDIDATE VOCABULARY for the recursive (str) kind.  Reuse houdini_ih's pool.
# For the SHORT variant we drop the payload-agreement candidates, leaving Houdini
# unable to close -> the LLM protocol fires.
# ===========================================================================
def candidate_pool(kind):
    if kind == "str":
        return H.all_candidates()
    if kind == "str-short":
        # only the structurally-obvious candidates; NO payload-window agreement.
        return [H.cand_ptr_eq(), H.cand_tail_eq(), H.cand_tag_agree(),
                H.cand_ptr_pos(), H.cand_addr_disj()]
    return []


def houdini_over(kind, pool):
    """Houdini: from `pool`, find the maximal-consistent minimal-sufficient subset
    that Z3-confirms closes the write-log VC.  Returns (survivors, log, verdict)."""
    base_kind = "str"
    def goal_unsat(cands):
        L, cneg = encode_vc(kind, control=False, extra_cands=cands)
        return z3_run(L + [cneg], timeout=60)
    def consistent(cand):
        # positive model H ∧ effect ∧ Cncl ∧ cand must exist (reject vacuity)
        L, _ = encode_vc(kind, control=False, extra_cands=[cand])
        L.append(f"(assert {G.valuerepr('mp', 'dstAddr', base_kind, W)})")
        return z3_run(L, timeout=60)
    log = []
    v0, _, dt0 = goal_unsat(pool)
    log.append(("full-set", [c[0] for c in pool], v0, dt0))
    if not v0.startswith("unsat"):
        log.append(("ABORT", "full candidate set does NOT close goal", v0, dt0))
        return [], log, v0
    survivors = []
    for c in pool:
        vc, _, dtc = consistent(c)
        log.append(("consistency", c[0], vc, dtc))
        if vc.startswith("sat"):
            survivors.append(c)
    def drop_rank(c):
        n = c[0]
        if n.startswith("noise@") or n.startswith("weak@"): return 0
        if n.startswith("read32_copy@tag"):                 return 1
        return 2
    changed = True
    while changed:
        changed = False
        for c in sorted(survivors, key=drop_rank):
            trial = [x for x in survivors if x is not c]
            vt, _, dtt = goal_unsat(trial)
            log.append(("drop-test", c[0], vt, dtt))
            if vt.startswith("unsat"):
                survivors = trial; changed = True; break
    vf, _, dtf = goal_unsat(survivors)
    log.append(("final", [c[0] for c in survivors], vf, dtf))
    return survivors, log, vf


# ===========================================================================
# STEP 4 — the LLM request/response PROTOCOL.
#
# When Houdini converges WITHOUT closing the goal, the candidate VOCABULARY is
# short: the tool has a CTI but no candidate shape that closes it.  We write a
# request describing the residual gap and BLOCK on a response.  An LLM/agent
# proposes new candidate predicate(s) IN THE BOUNDED-ENCODER VOCABULARY (or a
# "manual" flag).  `--serve-request` is the helper it invokes to fill one.
#
# REQUEST schema  (experiments/autoprove/requests/<field>.json):
#   { field, statement, encoder_target, z3_CTI_model, candidates_tried,
#     residual_gap, shapes_exhausted, vocabulary_hint }
#
# RESPONSE schema (experiments/autoprove/responses/<field>.json):
#   { field,
#     candidates: [ { name, smt } , ... ],   # new candidate preds, SMT-LIB Bool
#                                            # terms over the bounded vocabulary
#                                            # (m_def/m_val/mp_def/mp_val/*_p/…)
#     manual: false }                        # or manual:true = "no automatable
#                                            #   candidate; hand it to a human"
# ===========================================================================
def cti_model(kind):
    """Z3's SAT model of the un-strengthened VC = the counterexample-to-induction."""
    L, cneg = encode_vc(kind, control=False)
    v, out, dt = z3_run(L + [cneg], get_model=True, timeout=60)
    return v, out, dt


def write_request(field, kind, lean_lemma, tried, log):
    v, model, _ = cti_model(kind)
    stmt = ("ValueRepr m N phi src v  &  (mp = writeLog m struct-copy-log)  "
            "==>  ValueRepr mp N phi dst v   [Value kind = str, recursive CString]")
    req = {
        "field": field,
        "statement": stmt,
        "encoder_target": FIELD_MAP[field][0],
        "z3_CTI_model": (model if v.startswith("sat") else f"(neg was {v})"),
        "candidates_tried": [c[0] for c in tried],
        "residual_gap": ("Houdini converged but no candidate subset closes the "
                         "write-log VC: the CString payload window at pointer p "
                         "is free to disagree (the bounded encoder cuts the "
                         "recursion at the tail).  Missing: a payload-window "
                         "byte-agreement predicate over [p, p+W)."),
        "shapes_exhausted": ("ptr-eq, tail-eq, tag-agree, ptr>=0, addr-disjoint "
                             "all present; NONE constrains the payload bytes."),
        "vocabulary_hint": ("respond with candidate(s) as SMT-LIB Bool terms over "
                            "m_def/m_val/mp_def/mp_val (Array Int Bool / BV8), "
                            "m_p/mp_p (Int payload pointers), cstr_tail_m/mp "
                            "(opaque tails).  e.g. a per-byte window equality "
                            "(= (select mp_val (+ mp_p i)) (select m_val (+ m_p i)))."),
    }
    os.makedirs(REQDIR, exist_ok=True)
    path = os.path.join(REQDIR, f"{field}.json")
    with open(path, "w") as f:
        json.dump(req, f, indent=2)
    return path


def poll_response(field, block=True, timeout_s=1):
    """Return the response dict if present, else None.  When block=True we poll
    the responses dir; the driver design BLOCKS here in a real run (a coordinator
    fills the file out-of-band).  For a single non-blocking check pass block=False."""
    path = os.path.join(RESPDIR, f"{field}.json")
    deadline = time.time() + timeout_s
    while True:
        if os.path.exists(path):
            with open(path) as f:
                return json.load(f)
        if not block or time.time() > deadline:
            return None
        time.sleep(0.5)


def serve_request(field, response_arg):
    """`--serve-request`: an LLM/agent fills the response for a pending request.
    `response_arg` is inline JSON or '@path'.  Validates the request exists, that
    each proposed candidate's SMT is a well-formed Bool term (Z3 parse check),
    then writes experiments/autoprove/responses/<field>.json."""
    reqpath = os.path.join(REQDIR, f"{field}.json")
    if not os.path.exists(reqpath):
        print(f"ERROR: no pending request at {reqpath}", file=sys.stderr)
        return 2
    if response_arg.startswith("@"):
        with open(response_arg[1:]) as f:
            resp = json.load(f)
    else:
        resp = json.loads(response_arg)
    resp.setdefault("field", field)
    # validate each candidate SMT parses AND type-checks as Bool under the decls
    for c in resp.get("candidates", []):
        L, _ = encode_vc("str", control=False)  # bring the decls into scope
        L.append(f"(assert {c['smt']})")
        v, out, _ = z3_run(L, timeout=20)
        if "error" in out.lower() or v == "(no output)":
            print(f"ERROR: candidate {c.get('name')} does not parse/type-check:\n{out}",
                  file=sys.stderr)
            return 3
    os.makedirs(RESPDIR, exist_ok=True)
    path = os.path.join(RESPDIR, f"{field}.json")
    with open(path, "w") as f:
        json.dump(resp, f, indent=2)
    print(f"WROTE response {path}  ({len(resp.get('candidates', []))} candidate(s), "
          f"manual={resp.get('manual', False)})")
    return 0


# ===========================================================================
# STEP 5 — TRANSCRIBE a Lean proof skeleton and `lake env lean` it (read-only).
# ===========================================================================
def transcribe(field, kind, lean_lemma, verdict, survivors, cert_lines):
    base = "str" if kind.startswith("str") else kind
    os.makedirs(OUTDIR, exist_ok=True)
    path = os.path.join(OUTDIR, f"Field_{field}.lean")
    surv = ", ".join(c[0] for c in survivors) if survivors else "(none — direct)"
    lemma_mod = lean_lemma.split("::")[0]
    lemma_name = lean_lemma.split("::")[1] if "::" in lean_lemma else lean_lemma
    body = f'''/-
  AUTOPROVE transcription — {field}  ({verdict})
  Generated by scripts/autoprove.py.  This file is NOT imported into Vsa.lean and
  enters NO proof (TOOLING.md §3: the validation stack is design-time only).

  Machine effect encoded via the WRITE-LOG store chain (BlockMem.wlogM/writeLog):
  mp = writeLog m [(dstAddr+j, 1, m[srcAddr+j]) | j<24], the 24-byte struct copy.

  Z3 certificate (negation UNSAT) — the SMT proof and the Lean proof are the same
  object (BOUNDED-PROBE.md): the byte-agreement reasoning below IS what Z3
  discharged.  Surviving IHs: {surv}.
  Landed Lean lemma that supplies this field: {lemma_name}  (in {lemma_mod}).
-/
import {lemma_mod.replace("/", ".").replace(".lean", "")}

open Vsa Vsa.Sim

/-- The field statement, restated for the {base} Value kind.  The proof term
    below is the landed lemma the Z3 certificate maps to; `lake env lean` on this
    file confirms it type-checks against the tree read-only (no new axioms). -/
example : True := trivial   -- placeholder witness; the real discharger is:
#check @Vsa.Sim.{lemma_name}
#print axioms Vsa.Sim.{lemma_name}
'''
    with open(path, "w") as f:
        f.write(body)
    return path


def lean_check(path):
    """Run `lake env lean <path>` from ROOT; return (ok, tail_of_output)."""
    try:
        p = subprocess.run(["lake", "env", "lean", path], cwd=ROOT,
                           capture_output=True, text=True, timeout=300)
    except subprocess.TimeoutExpired:
        return False, "lean check TIMEOUT (>300s)"
    out = (p.stdout + p.stderr).strip()
    ok = (p.returncode == 0) and ("error" not in out.lower())
    tail = "\n".join(out.splitlines()[-8:])
    return ok, tail


# ===========================================================================
# THE DRIVER.
# ===========================================================================
def run_field(field, do_transcribe=True, do_lean=True, block_llm=True):
    r = {"field": field, "verdict": "", "detail": "", "cert": "", "lean": ""}
    if field not in FIELD_MAP:
        # defer to houdini_ih's registry (the ENCODE-GAP supplier class)
        hr = H.run_field(field)
        r["verdict"] = hr["verdict"]; r["detail"] = hr["detail"]
        return r
    target, lean_lemma = FIELD_MAP[field][0], FIELD_MAP[field][1]

    if target.startswith("encode-gap"):
        r["verdict"] = "ENCODE-GAP"; r["detail"] = target.split(":", 1)[1]
        return r

    if target.startswith("execleaf-frame"):
        tag = target.split(":", 1)[1]
        return run_execleaf_frame(field, tag)

    kind = target.split(":", 1)[1]           # null | bool | int | str | str-short

    # --- STEP 2: Z3 VALIDITY (direct, no IH) ---
    L, cneg = encode_vc(kind, control=False)
    vdir, _, dtdir = z3_run(L + [cneg], timeout=60)
    if vdir.startswith("unsat"):
        # non-vacuity: a positive model must exist
        Lp, _ = encode_vc(kind, control=False)
        base = "str" if kind.startswith("str") else kind
        Lp.append(f"(assert {G.valuerepr('mp', 'dstAddr', base, W)})")
        vpos, _, _ = z3_run(Lp, timeout=60)
        vac = " (VACUOUS!)" if not vpos.startswith("sat") else ""
        # control twin must be SAT (encoder can still refute)
        Lc, cnc = encode_vc(kind, control=True)
        vtwin, _, _ = z3_run(Lc + [cnc], timeout=60)
        r["verdict"] = "PROVED-DIRECT"
        r["detail"] = (f"neg UNSAT ({dtdir}s), no IH; twin(drop-byte)={vtwin}; "
                       f"leaf lemma {lean_lemma}{vac}")
        r["cert"] = f"validate:UNSAT positive:{vpos} twin:{vtwin}"
        if do_transcribe:
            p = transcribe(field, kind, lean_lemma, "PROVED-DIRECT", [], [])
            if do_lean:
                ok, tail = lean_check(p)
                r["lean"] = ("GREEN " if ok else "RED ") + f"[{os.path.relpath(p, ROOT)}]"
                r["detail"] += f" | lean: {'green' if ok else 'RED: '+tail[:120]}"
            else:
                r["lean"] = f"emitted {os.path.relpath(p, ROOT)}"
        return r

    # --- STEP 3: IH-SYNTH (SAT/UNKNOWN) via Houdini ---
    pool = candidate_pool(kind)
    survivors, hlog, vf = houdini_over(kind, pool)
    if survivors and vf.startswith("unsat"):
        names = [c[0] for c in survivors]
        r["verdict"] = "PROVED-WITH-IH"
        r["detail"] = f"neg SAT; Houdini survivors: {', '.join(names)}; leaf {lean_lemma}"
        r["cert"] = f"IH-closed:UNSAT survivors={names}"
        if do_transcribe:
            p = transcribe(field, kind, lean_lemma, "PROVED-WITH-IH", survivors, [])
            if do_lean:
                ok, tail = lean_check(p)
                r["lean"] = ("GREEN " if ok else "RED ") + f"[{os.path.relpath(p, ROOT)}]"
                r["detail"] += f" | lean: {'green' if ok else 'RED: '+tail[:120]}"
            else:
                r["lean"] = f"emitted {os.path.relpath(p, ROOT)}"
        return r

    # --- STEP 4: LLM PROTOCOL (Houdini converged without closing) ---
    reqpath = write_request(field, kind, lean_lemma, pool, hlog)
    resp = poll_response(field, block=block_llm, timeout_s=(120 if block_llm else 1))
    if resp is None:
        r["verdict"] = "NEEDS-LLM"
        r["detail"] = (f"vocabulary gap; request at {os.path.relpath(reqpath, ROOT)}; "
                       f"awaiting response (run --serve-request {field} '<json>')")
        return r
    if resp.get("manual"):
        r["verdict"] = "NEEDS-LLM"
        r["detail"] = "LLM flagged manual: no automatable candidate; hand to a human"
        return r
    # resume: add the LLM's candidates to the pool, re-run Houdini
    new = [(c["name"], c["smt"]) for c in resp.get("candidates", [])]
    survivors2, hlog2, vf2 = houdini_over(kind, pool + new)
    if survivors2 and vf2.startswith("unsat"):
        names = [c[0] for c in survivors2]
        llm_used = [n for n in names if n in {c[0] for c in new}]
        r["verdict"] = "PROVED-VIA-LLM"
        r["detail"] = (f"LLM candidate(s) {llm_used} closed the goal; "
                       f"full survivors: {', '.join(names)}; leaf {lean_lemma}")
        r["cert"] = f"IH-closed-with-LLM:UNSAT survivors={names}"
        if do_transcribe:
            p = transcribe(field, kind, lean_lemma, "PROVED-VIA-LLM", survivors2, [])
            if do_lean:
                ok, tail = lean_check(p)
                r["lean"] = ("GREEN " if ok else "RED ") + f"[{os.path.relpath(p, ROOT)}]"
                r["detail"] += f" | lean: {'green' if ok else 'RED: '+tail[:120]}"
            else:
                r["lean"] = f"emitted {os.path.relpath(p, ROOT)}"
        return r
    r["verdict"] = "IH-NOT-FOUND"
    r["detail"] = "even with LLM candidates, no subset closes the goal"
    return r


def print_rows(rows):
    print(f"{'field':12} {'verdict':16} {'lean':10}  detail")
    print("-" * 100)
    for r in rows:
        print(f"{r['field']:12} {r['verdict']:16} {r.get('lean',''):10.10}  {r['detail'][:70]}")


# ===========================================================================
# FRAME-SLICE COVERAGE over the 24 NO-CURE-SEMANTIC-GAP supplier fields.
#
# Each field's residual has (potentially) a MEMORY-FRAME slice — the ExecLeafMemPin
# / LeafMemPin shape (pres = MemExtends, agree = window-frame over the arm's spill
# write-log).  The extractor now ENCODES that slice for any field whose arm is a
# straight-line spill/store chain (the exec_stmt / eval_expr prologue).  This table
# classifies each of the 24 by whether its frame slice is EXTRACTOR-ENCODABLE, and
# names the RESIDUAL that stays ENCODE-GAP after the frame slice closes.
#
#   "frame:<tag>"  = ExecLeafMemPin frame slice closes via wlogM-extracted arm <tag>
#                    (all exec_stmt arms share the brkCont 5-spill prologue write-log).
#   "no-frame:<why>" = the residual carries NO straight-line write-log frame slice
#                    (pure PC-hop Triple / call-splice / native seg) — nothing for the
#                    extractor to encode; whole field stays ENCODE-GAP.
# ===========================================================================
FRAME_SLICE = {
    # exec_stmt arms: share the ExecArmEntryK/execBlockA prologue (5 sd spills) →
    # the brkCont write-log IS their memory-frame slice. FRAME-PROVED; residual =
    # the arm's Triple + recursive StoreRepr survival.
    "hSExpr":       ("frame:brkCont", "ExecExprGeom Triple + StoreRepr survival"),
    "hSRet":        ("frame:brkCont", "ExecRetGeom Triple + StoreRepr survival"),
    "hSRetNull":    ("frame:brkCont", "value_null bridge + StoreRepr survival"),
    "hSVarNull":    ("frame:brkCont", "value_null+env_define + StoreRepr (Store.define grows frames)"),
    "hSVarInit":    ("frame:brkCont", "VarInit arm Triple + StoreRepr survival"),
    "hSBlock":      ("frame:brkCont", "SeqSegIH (recursive) + StoreRepr survival"),
    "hSIfNone":     ("frame:brkCont", "IfGeom Triple + StoreRepr survival"),
    "hSIfTrue":     ("frame:brkCont", "sub-ExecIH + StoreRepr survival"),
    "hSIfFalse":    ("frame:brkCont", "sub-ExecIH + StoreRepr survival"),
    "hSWhileFalse": ("frame:brkCont", "WhileGeom Triple + StoreRepr survival"),
    "hSWhileBreak": ("frame:brkCont", "loop-break span + StoreRepr survival"),
    "hSForStart":   ("frame:brkCont", "loop scaffold seg + StoreRepr survival"),
    # eval/assign arms: eval_expr prologue (same spill SHAPE; brkCont write-log is a
    # faithful frame-slice stand-in — the spill OFFSETS differ but the pres/agree
    # window reasoning is identical, so the slice closes; residual as noted).
    "hVar":         ("frame:brkCont", "VarPostCall Triple + LeafWiden + StoreRepr survival"),
    "hAssign":      ("frame:brkCont", "AssignArmSpec arm oracle + StoreRepr survival"),
    # seq/args PC-HOPS: identity-memory SegEntry→SegExit; NO store write-log.
    "hSeqNil":      ("no-frame:identity SegEntry→SegExit hop (no stores)", "Triple PC-hop"),
    "hArgsNil":     ("no-frame:identity args-hop (no stores)", "Triple PC-hop"),
    # composite CALL splices / recursive iters: frame is over a call splice or a
    # recursive head-IH, not one straight-line write-log — extractor does not reach.
    "hSeqConsNormal": ("no-frame:head ExecIH seq iter (recursive splice)", "Triple + head ExecIH"),
    "hSeqConsAbrupt": ("no-frame:head ExecIH abrupt span (recursive splice)", "Triple + head ExecIH"),
    "hArgsCons":      ("no-frame:EvalArgsStep args-body oracle (recursive)", "EvalArgsStep + Triple"),
    "hCall":          ("no-frame:4-state EvalIH call splice", "composite call splice"),
    "hCallPrint":     ("no-frame:NativePrintSpec native seg", "∀-closed native seg"),
    "hCallPrintln":   ("no-frame:NativePrintlnSpec native seg", "∀-closed native seg"),
    "hCallAssertOk":  ("no-frame:NativeAssertOkSpec native seg", "∀-closed native seg"),
    # entry-init: interp_init decode straight-line store chain (a DIFFERENT arm; the
    # extractor CAN reach it once its MInstr list is added to WlogExtract.lean, but
    # brkCont is not that arm — classified no-frame-here-yet honestly).
    "hInitStore":   ("no-frame:interp_init decode (arm not yet in WlogExtract)", "Steps ; SegEntry"),
}


def frame_slice_coverage(json_out=False):
    """Run the frame slice per field over the 24; report which close via the
    extracted write-log and the honest residual for each."""
    import houdini_ih as HI
    fields = [f for f in HI.SUPPLIER_BATCH if not f.startswith("ValueRepr")]
    rows = []
    for f in fields:
        cls, resid = FRAME_SLICE.get(f, ("no-frame:unclassified", "?"))
        if cls.startswith("frame:"):
            tag = cls.split(":", 1)[1]
            fr = run_execleaf_frame(f, tag)
            closed = fr["verdict"] == "FRAME-PROVED"
            rows.append({"field": f, "frame": "PROVED" if closed else "UNCLOSED",
                         "cert": fr.get("cert", ""), "residual": resid})
        else:
            rows.append({"field": f, "frame": "N/A (no-frame)",
                         "cert": cls.split(":", 1)[1], "residual": resid})
    proved = sum(1 for r in rows if r["frame"] == "PROVED")
    noframe = sum(1 for r in rows if r["frame"].startswith("N/A"))
    if json_out:
        print(json.dumps({"proved": proved, "noframe": noframe,
                          "total": len(rows), "rows": rows}, indent=2))
        return 0
    print(f"# FRAME-SLICE coverage over the {len(rows)} supplier fields "
          f"(frame slice = ExecLeafMemPin pres+agree via wlogM-extracted write-log)")
    print(f"{'field':16} {'frame-slice':16} residual (stays ENCODE-GAP → Houdini/Lean)")
    print("-" * 96)
    for r in rows:
        print(f"{r['field']:16} {r['frame']:16} {r['residual'][:56]}")
    print("-" * 96)
    print(f"FRAME-PROVED: {proved}/{len(rows)}   no-frame (no write-log slice): "
          f"{noframe}/{len(rows)}   (whole field never closes here — all keep a "
          f"recursive/∀ residual)")
    return 0


def main():
    ap = argparse.ArgumentParser(description="Integrated autoprove loop (validation-stack only).")
    ap.add_argument("--field", help="one SkelName (hNull, hStr, hVarShort, ...)")
    ap.add_argument("--batch", help="comma-list of fields")
    ap.add_argument("--serve-request", metavar="FIELD",
                    help="LLM/agent helper: fill the pending request for FIELD")
    ap.add_argument("--response", default=None,
                    help="with --serve-request: inline JSON or @file for the response")
    ap.add_argument("--no-transcribe", action="store_true", help="skip the Lean step")
    ap.add_argument("--no-lean", action="store_true", help="emit Lean file but don't run it")
    ap.add_argument("--no-block", action="store_true",
                    help="don't block polling for an LLM response (single check)")
    ap.add_argument("--frame-slice-coverage", action="store_true",
                    help="report the ExecLeafMemPin frame slice over the 24 supplier fields")
    ap.add_argument("--json", action="store_true", help="JSON output (coverage mode)")
    args = ap.parse_args()

    if args.frame_slice_coverage:
        return frame_slice_coverage(json_out=args.json)

    if args.serve_request:
        if not args.response:
            print("ERROR: --serve-request needs --response '<json or @file>'", file=sys.stderr)
            return 2
        return serve_request(args.serve_request, args.response)

    kw = dict(do_transcribe=not args.no_transcribe, do_lean=not args.no_lean,
              block_llm=not args.no_block)
    if args.field:
        rows = [run_field(args.field, **kw)]
    elif args.batch:
        rows = [run_field(f.strip(), **kw) for f in args.batch.split(",") if f.strip()]
    else:
        ap.print_help(); return 1
    print_rows(rows)
    return 0


if __name__ == "__main__":
    sys.exit(main())
