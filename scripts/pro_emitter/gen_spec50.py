#!/usr/bin/env python3
"""Emit Vsa/Sim/SnprintfSpec50.lean — `ssprint_iov1_spec`: the 1-iovec
`__ssprint_r` flush (nonneg %lld arm: NO sign iovec, count 1, resid n1).

Derivation: SnprintfSpec20's source, transformed:
  * PreSr/St1Sr/St3Sr/post/SrRegions → *1 twins: the single iovec keeps the
    (s1, n1, bs1) ghost names, iov[1]/(s2,n2,bs2) fields dropped, count pin
    2 → 1, resid n1+n2 → n1;
  * tr_ssprint_entry → tr_ssprint_entry1 (same 16 sites; resid value n1);
  * tr_ssprint_iter1 → tr_ssprint_iter_1v: same 18 sites + the ssputs call,
    but count folds 1 → 0 (`lw_count1_sr`/`addiw_cnt1_sr`/`swData_zero_sr`),
    the `sub` at 0xe98c yields 0 (`BitVec.sub_self`), and the `bnez` at
    0xe998 is NOT taken → falls through to the tail at 0xe99c (St3-shaped
    post: cursor d+n1, capacity cap32−n1);
  * tr_ssprint_tail → tr_ssprint_tail1 (verbatim minus the copied2 clause).

All shared helpers (swData folds, srStackMem, NotWrittenSr, pins surgery,
sites) come from `import Vsa.Sim.SnprintfSpec20`.
"""
import pathlib
import re

SRC = pathlib.Path("Vsa/Sim/SnprintfSpec20.lean").read_text()


def block(start, end):
    i = SRC.index(start)
    j = SRC.index(end, i)
    return SRC[i:j]


def sub_must(text, old, new, count=0, name=""):
    if old not in text:
        raise SystemExit(f"MISSING [{name}]: {old[:90]!r}")
    return text.replace(old, new) if count == 0 else text.replace(old, new, count)


def drop_line(text, frag, name=""):
    lines = text.splitlines(keepends=True)
    out = [l for l in lines if frag not in l]
    if len(out) == len(lines):
        raise SystemExit(f"NO LINE DROPPED [{name}]: {frag!r}")
    return "".join(out)


WORD = lambda w: re.compile(r"(?<![A-Za-z0-9_])" + re.escape(w) + r"(?![A-Za-z0-9_'])")


def sum_to_n1(text):
    return text.replace("n1 + n2", "n1")


def strip_params(text):
    """Common ghost-parameter surgery for signatures and application sites."""
    text = text.replace(
        "(r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 : BitVec 64)",
        "(r q viov p d s1 vsp v8 v9 v18 v19 v20 v21 va0 : BitVec 64)")
    text = text.replace(
        "(r q _viov p d _s1 _s2 vsp v8 v9 v18 v19 v20 v21 _va0 : BitVec 64)",
        "(r q _viov p d _s1 vsp v8 v9 v18 v19 v20 v21 _va0 : BitVec 64)")
    text = text.replace("(n1 n2 : Nat)", "(n1 : Nat)")
    text = text.replace("(bs1 bs2 : Nat → BitVec 8)", "(bs1 : Nat → BitVec 8)")
    text = text.replace(
        "g r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 n1 n2 cap32 m0 bs1 bs2",
        "g r q viov p d s1 vsp v8 v9 v18 v19 v20 v21 va0 n1 cap32 m0 bs1")
    text = text.replace(
        "g r q viov p d s1 s2 vsp v8 v9 v18 v19 v20 v21 va0 n1 n2 cap32 m0\n        bs1 bs2",
        "g r q viov p d s1 vsp v8 v9 v18 v19 v20 v21 va0 n1 cap32 m0\n        bs1")
    return text


RENAMES = [
    ("SrRegions", "SrRegions1"),
    ("PreSr", "PreSr1"),
    ("St1Sr", "St1Sr1"),
    ("St3Sr", "St3Sr1"),
    ("ssprint_iov2_post", "ssprint_iov1_post"),
    ("tr_ssprint_entry", "tr_ssprint_entry1"),
    ("tr_ssprint_iter1", "tr_ssprint_iter_1v"),
    ("tr_ssprint_tail", "tr_ssprint_tail1"),
]


def rename(text):
    for old, new in RENAMES:
        text = WORD(old).sub(new, text)
    return text


OUT = []

# ------------------------------------------------------------- SrRegions1
sr = block("/-- Caller-level region facts", "/-! ## Pin-list surgery")
sr = sub_must(sr, "structure SrRegions (q viov p d s1 s2 vsp : BitVec 64) (n1 n2 : Nat)",
              "structure SrRegions (q viov p d s1 vsp : BitVec 64) (n1 : Nat)", name="sr-sig")
sr = sum_to_n1(sr)
for fld in ["n2_1 :", "n2_31 :", "s2_lo :", "s2_hi :", "s2_win :",
            "dst_src2 :", "sink_src2 :", "stack_src2 :", "q_src2 :"]:
    sr = drop_line(sr, fld, name=f"sr-{fld}")
OUT.append(rename(sr))

# ------------------------------------------------------------- PreSr1 / St1Sr1
pre = block("/-- Entry configuration at `0x8000e908`",
            "/-- Loop-head configuration at `0x8000e950` before iteration 1")
st1 = block("/-- Loop-head configuration at `0x8000e950` before iteration 1",
            "/-! ## Entry:")
for nm, txt in [("pre", pre), ("st1", st1)]:
    txt = strip_params(txt)
    txt = txt.replace("SrRegions q viov p d s1 s2 vsp n1 n2", "SrRegions q viov p d s1 vsp n1")
    txt = sub_must(txt, "(2#32)", "(1#32)", name=f"{nm}-count")
    txt = sum_to_n1(txt)
    for fld in ["hiov1b :", "hiov1l :", "hbs2 :"]:
        txt = drop_line(txt, fld, name=f"{nm}-{fld}")
    if nm == "pre":
        pre = txt
    else:
        st1 = txt
OUT.append(rename(pre))
OUT.append(rename(st1))

# ------------------------------------------------------------- St3Sr1
st3 = block("/-- Loop-exit configuration at `0x8000e99c`", "/-! ## Iteration 1:")
st3 = strip_params(st3)
st3 = st3.replace("SrRegions q viov p d s1 s2 vsp n1 n2", "SrRegions q viov p d s1 vsp n1")
st3 = sum_to_n1(st3)
st3 = drop_line(st3, "copied2 :", name="st3-copied2")
st3 = sub_must(st3, "cap32 - BitVec.ofNat 32 n1 - BitVec.ofNat 32 n2",
               "cap32 - BitVec.ofNat 32 n1", name="st3-cap")
OUT.append(rename(st3))

# ------------------------------------------------------------- entry
ent = block("theorem tr_ssprint_entry ", "/-! ## Mid-states")
ent = strip_params(ent)
ent = sum_to_n1(ent)
ent = sub_must(ent,
    "hcursor, hcap, hbs1, hbs2, hcaplt, hcap31, hmemeq, hgframe⟩ := hPre",
    "hcursor, hcap, hbs1, hcaplt, hcap31, hmemeq, hgframe⟩ := hPre", name="ent-obtain")
ent = sub_must(ent, "hresid, hiov0b, hiov0l, hiov1b, hiov1l,\n",
               "hresid, hiov0b, hiov0l,\n", name="ent-obtain2")
ent = drop_line(ent, "have hn21 := hreg.n2_1", name="ent-n2binds")
ent = sub_must(ent,
    "hcount, hresid, hiov0b, hiov0l, hiov1b, hiov1l, hcursor, hcap, hbs1, hbs2,",
    "hcount, hresid, hiov0b, hiov0l, hcursor, hcap, hbs1,", name="ent-refine")
OUT.append(rename(ent))

# ------------------------------------------------------------- iteration
it = block("theorem tr_ssprint_iter1 ", "/-! ## Iteration 2:")
# cut at the e998 step; we splice a NOT-taken seam + St3 assembly
CUT = "  -- === e998: bnez a3 TAKEN"
it_head = it[:it.index(CUT)]
it_head = strip_params(it_head)
it_head = sub_must(it_head,
    "Triple (St1Sr g", "Triple (St1Sr g", name="probe")  # no-op sanity
it_head = sub_must(it_head,
    "(St2Sr g r q viov p d s1 vsp v8 v9 v18 v19 v20 v21 va0 n1 cap32 m0 bs1)",
    "(St3Sr g r q viov p d s1 vsp v8 v9 v18 v19 v20 v21 va0 n1 cap32 m0 bs1)",
    name="it-st3") if False else it_head
# signature: St1Sr → St3Sr target (post-strip the param strings)
it_head = sub_must(it_head, "(St2Sr g", "(St3Sr g", name="it-target")
# obtain surgery
it_head = sub_must(it_head,
    "hreg, hcount, hresid, hiov0b, hiov0l, hiov1b, hiov1l, hcursor, hcap, hbs1, hbs2,\n"
    "    hcaplt, hcap31, hmemeq, hgframe⟩ := hSt",
    "hreg, hcount, hresid, hiov0b, hiov0l, hcursor, hcap, hbs1,\n"
    "    hcaplt, hcap31, hmemeq, hgframe⟩ := hSt", name="it-obtain")
# preamble binds
it_head = drop_line(it_head, "have hn21 := hreg.n2_1", name="it-n2binds")
it_head = drop_line(it_head, "have hs2lo := hreg.s2_lo", name="it-s2binds")
it_head = sub_must(it_head, "have hds1 := hreg.dst_src1; have hds2 := hreg.dst_src2",
                   "have hds1 := hreg.dst_src1", name="it-ds2")
it_head = sub_must(it_head,
    "have hsd := hreg.sink_dst; have hsstk := hreg.sink_stack; have hss2 := hreg.sink_src2",
    "have hsd := hreg.sink_dst; have hsstk := hreg.sink_stack", name="it-ss2")
it_head = sub_must(it_head,
    "have hstkd := hreg.stack_dst; have hstks1 := hreg.stack_src1; have hstks2 := hreg.stack_src2",
    "have hstkd := hreg.stack_dst; have hstks1 := hreg.stack_src1", name="it-stks2")
it_head = sub_must(it_head, "have hqs1 := hreg.q_src1; have hqs2 := hreg.q_src2",
                   "have hqs1 := hreg.q_src1", name="it-qs2")
# count folds: written value 1 → 0 FIRST, then read value 2 → 1
it_head = it_head.replace("(q.toNat + 8) (1#32)", "(q.toNat + 8) (0#32)")
it_head = sub_must(it_head, "site_8000e95c_sr σ3 i3 (c.steps + 1 + 1 + 1) _ vmi3 q (BitVec.ofNat 64 1)",
                   "site_8000e95c_sr σ3 i3 (c.steps + 1 + 1 + 1) _ vmi3 q (BitVec.ofNat 64 0)",
                   name="it-sw0")
it_head = sub_must(it_head, "some (BitVec.ofNat 64 1)", "some (BitVec.ofNat 64 0)", name="it-a12")
it_head = sub_must(it_head, "swData_one_sr", "swData_zero_sr", name="it-swdata")
it_head = it_head.replace("(2#32)", "(1#32)")
it_head = it_head.replace("(2#64)", "(1#64)")
it_head = sub_must(it_head, "lw_count2_sr", "lw_count1_sr", name="it-lw")
it_head = sub_must(it_head, "addiw_cnt2_sr", "addiw_cnt1_sr", name="it-addiw")
# resid: n1 + n2 → n1
it_head = sum_to_n1(it_head)
# the sub at e98c now yields 0
it_head = sub_must(it_head,
    "have ha14_16 : σ16.regs.get? Register.x14 = some (BitVec.ofNat 64 n2) := by",
    "have ha14_16 : σ16.regs.get? Register.x14 = some (BitVec.ofNat 64 0) := by",
    name="it-sub-val")
it_head = sub_must(it_head, "rwa [ofNat_sub_left n1 n2 (by omega)] at this",
                   "rwa [BitVec.sub_self] at this", name="it-sub-fold")
# downstream 0-values (e990 sd / hp18 pin / e994)
it_head = it_head.replace("(BitVec.ofNat 64 n2)", "(BitVec.ofNat 64 0)")
OUT_IT_TAIL = """  -- === e998: bnez a3 NOT taken (resid = 0) → fall through to 0x8000e99c ===
  obtain ⟨σ19, i19, hstp19, hi19, hG19, hmem19, hobs19⟩ :=
    site_8000e998_nottaken_sr σ18 i18 (c1.steps + 1 + 1 + 1 + 1 + 1 + 1) _ vmi18
      (BitVec.ofNat 64 0)
      hG18 hpc18 hmi18 ha13_18 hload18 rfl (by decide) hi18
  have hpc19 : σ19.regs.get? Register.PC = some (0x8000e99c#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs19
    rwa [show BitVec.addInt (0x8000e998#64) 4 = (0x8000e99c#64 : BitVec 64) from by decide] at this
  have hp21 := pins_bnottaken hobs19 (by rfl) hp20
  have hload19 : __ssprint_rLoaded σ19.mem := hmem19 ▸ hload18
  have hm19 : σ19.mem = writeMap8 c1.σ.mem (q.toNat + 16)
      (sdData_val (BitVec.ofNat 64 0)) := by
    rw [hmem19, hmem18, hm17]
  -- === St3 memory facts ===
  have hslot : ∀ (K : Nat) (v : BitVec 64), 8 ≤ K → K ≤ 56 →
      Pin8 (srStackMem m0 vsp r v8 v9 v18 v19 v20 v21) (vsp.toNat - K) v →
      Pin8 σ19.mem (vsp.toNat - K) v := by
    intro K v hK1 hK2 hpin
    rw [hm19]
    exact Pin8_frame (fun k hk1 hk2 => getElem_writeMap8_disjoint _ _ _ _ (by omega))
      (Pin8_frame (fun k hk1 hk2 =>
        hmframe1 k (by omega) (by omega) (by omega) (by omega))
        (Pin8_frame (fun k hk1 hk2 =>
          getElem_writeMap4_disjoint _ _ _ _ (by omega)) hpin))
  -- assemble St3
  refine ⟨⟨σ19, i19, c1.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, ?_, hG19, hload19, hpc19,
    hp21.2.2.2.1, hp21.2.2.1, hi19, hreg, ?_, ?_, ?_,
    hslot 8 r (by omega) (by omega) (srStackMem_ra m0 vsp r v8 v9 v18 v19 v20 v21 (by omega)),
    hslot 16 v8 (by omega) (by omega) (srStackMem_s0 m0 vsp r v8 v9 v18 v19 v20 v21 (by omega)),
    hslot 24 v9 (by omega) (by omega) (srStackMem_s1 m0 vsp r v8 v9 v18 v19 v20 v21 (by omega)),
    hslot 32 v18 (by omega) (by omega) (srStackMem_s2 m0 vsp r v8 v9 v18 v19 v20 v21),
    hslot 40 v19 (by omega) (by omega) (srStackMem_s3 m0 vsp r v8 v9 v18 v19 v20 v21 (by omega)),
    hslot 48 v20 (by omega) (by omega) (srStackMem_s4 m0 vsp r v8 v9 v18 v19 v20 v21 (by omega)),
    hslot 56 v21 (by omega) (by omega) (srStackMem_s5 m0 vsp r v8 v9 v18 v19 v20 v21 (by omega)),
    ?_, ?_⟩
  · -- Steps chain
    exact ((((((((((((((((((Steps.single hstp1).trans (Steps.single hstp2)).trans
      (Steps.single hstp3)).trans (Steps.single hstp4)).trans (Steps.single hstp5)).trans
      (Steps.single hstp6)).trans (Steps.single hstp7)).trans (Steps.single hstp8)).trans
      (Steps.single hstp9)).trans (Steps.single hstp10)).trans (Steps.single hstp11)).trans
      (Steps.single hstp12)).trans hsteps_call1).trans (Steps.single hstp13)).trans
      (Steps.single hstp14)).trans (Steps.single hstp15)).trans (Steps.single hstp16)).trans
      (Steps.single hstp17)).trans ((Steps.single hstp18).trans (Steps.single hstp19))
  · -- copied1
    intro k hk
    rw [hm19, getElem_writeMap8_disjoint _ _ _ _ (by omega)]
    exact hcopied1 k hk
  · -- cursorF
    rw [hm19]
    exact Pin8_frame (fun k hk1 hk2 => getElem_writeMap8_disjoint _ _ _ _ (by omega)) hcursor'
  · -- capF
    rw [hm19]
    exact Pin4_frame (fun k hk1 hk2 => getElem_writeMap8_disjoint _ _ _ _ (by omega))
      (swData_spNewCap cap32 n1 ▸ hcap')
  · -- mframe
    intro a h1 h2 h3 h4 h5 h6
    rw [hm19, getElem_writeMap8_disjoint _ _ _ _ (by omega)]
    refine (hmframe1 a (by omega) (by omega) (by omega) (by omega)).trans ?_
    rw [getElem_writeMap4_disjoint _ _ _ _ (by omega)]
    exact srStackMem_frame m0 vsp r v8 v9 v18 v19 v20 v21 (by omega) a (by omega)
  · -- register ghost frame
    intro R hR
    have hmv := hR.sp.mv
    have e1 : σ1.regs.get? R = c.σ.regs.get? R := frame_alu_mv hobs1 R hR.sp.x15 hmv
    have e2 : σ2.regs.get? R = σ1.regs.get? R := frame_alu_mv hobs2 R hR.sp.x13 hmv
    have e3 : σ3.regs.get? R = σ2.regs.get? R := frame_alu_mv hobs3 R hR.sp.x12 hmv
    have e4 : σ4.regs.get? R = σ3.regs.get? R := frame_store_mv hobs4 R hmv
    have e5 : σ5.regs.get? R = σ4.regs.get? R := frame_bnottaken_mv hobs5 R hmv
    have e6 : σ6.regs.get? R = σ5.regs.get? R := frame_alu_mv hobs6 R hR.x18 hmv
    have e7 : σ7.regs.get? R = σ6.regs.get? R := frame_bnottaken_mv hobs7 R hmv
    have e8 : σ8.regs.get? R = σ7.regs.get? R := frame_alu_mv hobs8 R hR.sp.x12 hmv
    have e9 : σ9.regs.get? R = σ8.regs.get? R := frame_alu_mv hobs9 R hR.sp.x13 hmv
    have e10 : σ10.regs.get? R = σ9.regs.get? R := frame_alu_mv hobs10 R hR.sp.x11 hmv
    have e11 : σ11.regs.get? R = σ10.regs.get? R := frame_alu_mv hobs11 R hR.sp.x10 hmv
    have e12 : σ12.regs.get? R = σ11.regs.get? R := frame_jal_sp hobs12 R hR.sp.x1 hmv
    have ec : c1.σ.regs.get? R = σ12.regs.get? R := hregframe1 R hR.sp
    have e13 : σ13.regs.get? R = c1.σ.regs.get? R := frame_bnottaken_mv hobs13 R hmv
    have e14 : σ14.regs.get? R = σ13.regs.get? R := frame_alu_mv hobs14 R hR.sp.x14 hmv
    have e15 : σ15.regs.get? R = σ14.regs.get? R := frame_alu_mv hobs15 R hR.sp.x8 hmv
    have e16 : σ16.regs.get? R = σ15.regs.get? R := frame_alu_mv hobs16 R hR.sp.x14 hmv
    have e17 : σ17.regs.get? R = σ16.regs.get? R := frame_store_mv hobs17 R hmv
    have e18 : σ18.regs.get? R = σ17.regs.get? R := frame_alu_mv hobs18 R hR.sp.x13 hmv
    have e19 : σ19.regs.get? R = σ18.regs.get? R := frame_bnottaken_mv hobs19 R hmv
    rw [e19, e18, e17, e16, e15, e14, e13, ec, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3,
      e2, e1]
    exact hgframe R hR

"""
OUT.append(rename(it_head) + OUT_IT_TAIL)

# ------------------------------------------------------------- post + tail
post = block("/-- Final postcondition at `PC = r`", "theorem tr_ssprint_tail ")
post = strip_params(post)
post = sum_to_n1(post)
post = drop_line(post, "c.σ.mem[(d.toNat + n1 + k)]? = some (bs2 k)", name="post-copied2")
post = sub_must(post, "cap32 - BitVec.ofNat 32 n1 - BitVec.ofNat 32 n2",
                "cap32 - BitVec.ofNat 32 n1", name="post-cap")
post = sub_must(post, "both iovecs flushed to\n`[d, d+n1)`",
                "the single iovec flushed to\n`[d, d+n1)`", name="post-doc") \
    if "both iovecs flushed to\n`[d, d+n1)`" in post else post
OUT.append(rename(post))

tail = block("theorem tr_ssprint_tail ", "/-! ## The composed")
tail = strip_params(tail)
tail = sum_to_n1(tail)
tail = sub_must(tail, "hreg, hcopied1, hcopied2, hcursorF, hcapF,",
                "hreg, hcopied1, hcursorF, hcapF,", name="tail-obtain")
tail = drop_line(tail, "have hn21 := hreg.n2_1", name="tail-n2binds")
# drop the copied2 bullet
COPIED2 = """  · -- copied2
    intro k hk
    rw [hmF, getElem_writeMap4_disjoint _ _ _ _ (by omega),
      getElem_writeMap8_disjoint _ _ _ _ (by omega)]
    exact hcopied2 k hk
"""
tail = sub_must(tail, COPIED2, "", name="tail-copied2")
tail = sub_must(tail, "?_, ?_, ?_, ?_, ?_, ?_, ?_, hi12, ?_⟩",
                "?_, ?_, ?_, ?_, ?_, ?_, hi12, ?_⟩", name="tail-refine")
OUT.append(rename(tail))

# ------------------------------------------------------------- capstone
OUT.append("""/-! ## The composed 1-iovec flush spec -/

/-- **`__ssprint_r` 1-iovec flush** (`0x8000e908 → ret`), composed once with
the verified `__ssputs_r` fast path: flushes the single (digit) iovec
`(s1, n1, bs1)` into the sink cursor buffer at `d`, advances the cursor to
`d + n1`, decrements the capacity word once, clears the `q` struct's
resid/count, returns `0` with all callee-saves and `sp` restored and a
pointwise frame outside the six written windows. -/
theorem ssprint_iov1_spec (g : (R : Register) → Option (RegisterType R))
    (r q viov p d s1 vsp v8 v9 v18 v19 v20 v21 va0 : BitVec 64)
    (n1 : Nat) (cap32 : BitVec 32) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs1 : Nat → BitVec 8) (halign : r.toNat % 4 = 0) :
    Triple (PreSr1 g r q viov p d s1 vsp v8 v9 v18 v19 v20 v21 va0 n1 cap32 m0 bs1)
      (ssprint_iov1_post g r q viov p d s1 vsp v8 v9 v18 v19 v20 v21 va0 n1 cap32 m0
        bs1) :=
  ((tr_ssprint_entry1 g r q viov p d s1 vsp v8 v9 v18 v19 v20 v21 va0 n1 cap32 m0
      bs1).seq
    (tr_ssprint_iter_1v g r q viov p d s1 vsp v8 v9 v18 v19 v20 v21 va0 n1 cap32 m0
      bs1)).seq
    (tr_ssprint_tail1 g r q viov p d s1 vsp v8 v9 v18 v19 v20 v21 va0 n1 cap32 m0
      bs1 halign)

end Vsa.Sim
""")

HDR = """import Vsa.Sim.SnprintfSpec20

/-!
# M3 Layer-3 — `SnprintfSpec50` : the `__ssprint_r` 1-iovec flush (`_sr1`)

`ssprint_iov1_spec` — the 1-iovec twin of `ssprint_iov2_spec`
(SnprintfSpec20) for the NONNEG `%lld` arm: no sign iovec, iov count `1`,
resid `n1` (the digit count), ONE loop iteration (count `1 → 0`, resid
`n1 → 0`, the `bnez` at `0x8000e998` NOT taken), then the shared tail.
The single iovec keeps the `(s1, n1, bs1)` ghost names.

Generated from SnprintfSpec20's source by
`scripts/pro_emitter/gen_spec50.py` (do not hand-edit; regenerate).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (MemmoveLoaded __ssprint_rLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

"""

out = HDR + "\n".join(OUT)
p = pathlib.Path("Vsa/Sim/SnprintfSpec50.lean")
p.write_text(out)
print(f"wrote {p} ({out.count(chr(10))} lines)")
