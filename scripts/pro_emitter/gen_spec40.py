#!/usr/bin/env python3
"""Emit Vsa/Sim/SnprintfSpec40.lean — the snprintf wrapper PRE-CALL segment
0x80005c44 (snprintf ABI entry) -> 0x80007654 (the jal _svfprintf_r completed).
House style: SnprintfSpec27 pattern over the SnprintfSitesWrap battery."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from emit_pro_seg import Seg

pins = [
    ("x2", "vsp + (864#64)"), ("x1", "wra0"), ("x3", "(0x8001b510#64)"),
    ("x10", "d"), ("x11", "sz"), ("x12", "vfmt"), ("x13", "v"),
    ("x14", "va4o"), ("x15", "va5o"), ("x16", "va6o"), ("x17", "va7o"),
    ("x8", "vS0o"), ("x9", "vS1o"),
    ("x18", "vS2o"), ("x19", "vS3o"), ("x20", "vS4o"), ("x21", "vS5o"),
    ("x22", "vS6o"), ("x23", "vS7o"), ("x24", "vS8o"), ("x25", "vS9o"),
    ("x26", "vS10o"), ("x27", "vS11o"),
]
S = Seg(pins)

SNP = "Vsa.Sim.Code.SnprintfLoaded"


def track_loaded(k, store_hoff=None, kind=None):
    P = k - 1
    prev = f"hsl{P}"
    if store_hoff is None:
        S.emit(f"  have hsl{k} : {SNP} σ{k}.mem := by rw [hmem{k}]; exact {prev}")
    else:
        fn = "snprintf_w8_wr" if kind == "w8" else "snprintf_w4_wr"
        S.emit(f"  have hsl{k} : {SNP} σ{k}.mem := by",
               f"    rw [hmem{k}, mem_afterNextPC]",
               f"    exact {fn} _ _ _ (by rw [{store_hoff}]; omega) {prev}")


def st(*a, **kw):
    hoff = kw.pop("track_hoff", None)
    kind = kw.pop("track_kind", None)
    S.step(*a, **kw)
    S.out.pop()
    track_loaded(S.k, hoff, kind)
    S.emit("")


SP = "(vsp + (592#64))"

# === 1: addi sp,sp,-272 ===
st(0x80005c44, "alu", "site_80005c44_wp", vals="(vsp + (864#64))",
   hyps="$p:x2 hsl0 rfl", nextpc=0x80005c48,
   rd="x2", rdval=SP, rdrw="sp_dec272_wr vsp", track=True,
   comment="addi sp,sp,-272")

# === 2: lui t1,0x80000 (hand site) ===
st(0x80005c48, "alu", "site_80005c48_wp",
   hyps="$L rfl", nextpc=0x80005c4c,
   rd="x6", rdval="(sign_extend (m := 64) ((0x80000#20) +++ 0x000#12))",
   track=True, comment="lui t1,0x80000")

# === 3..9: the 7 register spills (s1/ra/a3..a7) ===
spills = [
    (0x80005c4c, "site_80005c4c_wp", "x9", 792, "vS1o"),
    (0x80005c50, "site_80005c50_wp", "x1", 808, "wra0"),
    (0x80005c54, "site_80005c54_wp", "x13", 824, "v"),
    (0x80005c58, "site_80005c58_wp", "x14", 832, "va4o"),
    (0x80005c5c, "site_80005c5c_wp", "x15", 840, "va5o"),
    (0x80005c60, "site_80005c60_wp", "x16", 848, "va6o"),
    (0x80005c64, "site_80005c64_wp", "x17", 856, "va7o"),
]
for (addr, site, rs2, K, val) in spills:
    st(addr, "store", site, vals=f"{SP} _",
       hyps=f"$p:x2 $p:{rs2} $L rfl (by rw [hoff{K}]; omega) (by rw [hoff{K}]; omega)"
            f" (by rw [hoff{K}, htoh]; omega) (by rw [hoff{K}]; omega)",
       nextpc=addr + 4,
       memw=("w8", f"vsp.toNat + {K}", f"sdData_val {val}", [f"hoff{K}"]),
       track_hoff=f"hoff{K}", track_kind="w8",
       comment=f"sd -> sp+{K - 592} (= vsp+{K})")

# === 10: not t1,t1 (xori, hand site) — t1 := 0x7fffffff = INT_MAX ===
st(0x80005c68, "alu", "site_80005c68_wp",
   vals="(sign_extend (m := 64) ((0x80000#20) +++ 0x000#12))",
   hyps="$p:x6 $L rfl", nextpc=0x80005c6c,
   rd="x6", rdval="(0x7fffffff#64)", rdrw="t1_notmask_wr", track=True,
   comment="not t1,t1 — t1 := INT_MAX")

# === 11: ld s1,1120(gp) — the _impure_ptr static (0x8001b970 -> 0x8001b538) ===
S.emit("""  -- agreement below the frame after the seven spills (all keys ≥ vsp+592)
  have hag10 : ∀ a : Nat, a < vsp.toNat + 592 → σ10.mem[a]? = c.σ.mem[a]? := by
    intro a ha
    rw [hmE10,
      getElem?_writeMap8_out _ (vsp.toNat + 856) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 848) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 840) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 832) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 824) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 808) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 792) _ a (by omega)]
""")
st(0x80005c6c, "alu", "site_80005c6c_wp",
   vals="(0x8001b510#64) (0x38#8) (0xb5#8) (0x01#8) (0x80#8) (0x00#8) (0x00#8) (0x00#8) (0x00#8)",
   hyps="$p:x3 $L rfl (by rw [hoffimp]; omega) (by rw [hoffimp]; omega)"
        " (by rw [hoffimp, htoh]; omega) (by rw [hoffimp])"
        " (by rw [hoffimp]; exact (hag10 _ (by omega)).trans himp0)"
        " (by rw [hoffimp]; exact (hag10 _ (by omega)).trans himp1)"
        " (by rw [hoffimp]; exact (hag10 _ (by omega)).trans himp2)"
        " (by rw [hoffimp]; exact (hag10 _ (by omega)).trans himp3)"
        " (by rw [hoffimp]; exact (hag10 _ (by omega)).trans himp4)"
        " (by rw [hoffimp]; exact (hag10 _ (by omega)).trans himp5)"
        " (by rw [hoffimp]; exact (hag10 _ (by omega)).trans himp6)"
        " (by rw [hoffimp]; exact (hag10 _ (by omega)).trans himp7)",
   nextpc=0x80005c70,
   rd="x9", rdval="(0x8001b538#64)",
   rdrw="show (sign_extend (m := 64)"
        " ((((((((0x00#8).append (0x00#8)).append (0x00#8)).append (0x00#8)).append"
        " (0x80#8)).append (0x01#8)).append (0xb5#8)).append (0x38#8)"
        " : BitVec (8 * 8)) : BitVec 64) = (0x8001b538#64 : BitVec 64) from by"
        " apply BitVec.eq_of_toNat_eq; decide",
   track=True, comment="ld s1,1120(gp) — s1 := *_impure_ptr = 0x8001b538")

# === 12: bltu t1,a1 NOT taken (sz ≤ INT_MAX) ===
st(0x80005c70, "bnottaken", "site_80005c70_nottaken_wp",
   vals="(0x7fffffff#64) sz",
   hyps="$p:x6 $p:x11 $L rfl hgu12", nextpc=0x80005c74,
   pre=("have hgu12 : zopz0zI_u (0x7fffffff#64) sz = false :="
        " bltu_false_of_ge_wr _ _ (by"
        " rw [show ((0x7fffffff#64 : BitVec 64)).toNat = 0x7fffffff from rfl]; omega)",),
   comment="bltu t1,a1 — NOT taken (sz ≤ INT_MAX)")

# === 13: snez a4,a1 (sltu, hand site) — a4 := 1 ===
st(0x80005c74, "alu", "site_80005c74_wp", vals="sz",
   hyps="$p:x11 $L rfl", nextpc=0x80005c78,
   pre=("have hnz13 : zopz0zI_u (0#64) sz = true :="
        " bltu_of_lt_wr _ _ (by simp only [BitVec.toNat_ofNat]; omega)",),
   rd="x14", rdval="(1#64)",
   rdrw="show zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) sz)) = (1#64)"
        " from by rw [hnz13]; decide",
   track=True, comment="snez a4,a1 — a4 := 1 (sz ≠ 0)")

# === 14: lui a6,0xffff0 (hand site) ===
st(0x80005c78, "alu", "site_80005c78_wp",
   hyps="$L rfl", nextpc=0x80005c7c,
   rd="x16", rdval="(sign_extend (m := 64) ((0xffff0#20) +++ 0x000#12))",
   track=True, comment="lui a6,0xffff0")

# === 15: mv a5,a0 — a5 := d (the destination buffer) ===
st(0x80005c7c, "alu", "site_80005c7c_wp", vals="d",
   hyps="$p:x10 $L rfl", nextpc=0x80005c80,
   rd="x15", rdval="d", rdrw="sext0_add_pro d", track=True,
   comment="mv a5,a0 — a5 := d")

# === 16: subw a4,a1,a4 — a4 := sz - 1 (the capacity) ===
st(0x80005c80, "alu", "site_80005c80_wp", vals="sz (1#64)",
   hyps="$p:x11 $p:x14 $L rfl", nextpc=0x80005c84,
   rd="x14", rdval="(BitVec.ofNat 64 (sz.toNat - 1))",
   rdrw="subw_cap_wr sz (by omega) hszhi", track=True,
   comment="subw a4,a1,a4 — a4 := sz-1")

# === 17: sd s0,208(sp) — spill the caller's s0 ===
st(0x80005c84, "store", "site_80005c84_wp", vals=f"{SP} _",
   hyps="$p:x2 $p:x8 $L rfl (by rw [hoff800]; omega) (by rw [hoff800]; omega)"
        " (by rw [hoff800, htoh]; omega) (by rw [hoff800]; omega)",
   nextpc=0x80005c88,
   memw=("w8", "vsp.toNat + 800", "sdData_val vS0o", ["hoff800"]),
   track_hoff="hoff800", track_kind="w8",
   comment="sd s0,208(sp) (= vsp+800)")

# === 18: addi a3,sp,232 — a3 := the va area ===
st(0x80005c88, "alu", "site_80005c88_wp", vals=SP,
   hyps="$p:x2 $L rfl", nextpc=0x80005c8c,
   rd="x13", rdval="((vsp + (592#64)) + sign_extend (m := 64) (0x0e8#12))",
   track=True, comment="addi a3,sp,232 — the va_list pointer")

# === 19: addi a6,a6,520 — a6 := 0xffffffffffff0208 (_flags word) ===
st(0x80005c8c, "alu", "site_80005c8c_wp",
   vals="(sign_extend (m := 64) ((0xffff0#20) +++ 0x000#12))",
   hyps="$p:x16 $L rfl", nextpc=0x80005c90,
   rd="x16", rdval="(0xffffffffffff0208#64)", rdrw="a6_flags_wr", track=True,
   comment="addi a6,a6,520 — the __SWR|__SSTR flags image")

# === 20: mv s0,a1 — s0 := sz ===
st(0x80005c90, "alu", "site_80005c90_wp", vals="sz",
   hyps="$p:x11 $L rfl", nextpc=0x80005c94,
   rd="x8", rdval="sz", rdrw="sext0_add_pro sz", track=True,
   comment="mv s0,a1 — s0 := sz")

# === 21: mv a0,s1 — a0 := the reent ===
st(0x80005c94, "alu", "site_80005c94_wp", vals="(0x8001b538#64)",
   hyps="$p:x9 $L rfl", nextpc=0x80005c98,
   rd="x10", rdval="(0x8001b538#64)", rdrw="sext0_add_pro (0x8001b538#64)",
   track=True, comment="mv a0,s1 — a0 := the reent")

# === 22: addi a1,sp,8 — a1 := the FILE struct ===
st(0x80005c98, "alu", "site_80005c98_wp", vals=SP,
   hyps="$p:x2 $L rfl", nextpc=0x80005c9c,
   rd="x11", rdval="((vsp + (592#64)) + sign_extend (m := 64) (0x008#12))",
   track=True, comment="addi a1,sp,8 — the sink FILE pointer")

# === 23/24: sd a5,8(sp) / sd a5,32(sp) — cursor + _bf._base := d ===
for (addr, site, K, cm) in [(0x80005c9c, "site_80005c9c_wp", 600, "FILE cursor := d"),
                            (0x80005ca0, "site_80005ca0_wp", 624, "FILE _bf._base := d")]:
    st(addr, "store", site, vals=f"{SP} _",
       hyps=f"$p:x2 $p:x15 $L rfl (by rw [hoff{K}]; omega) (by rw [hoff{K}]; omega)"
            f" (by rw [hoff{K}, htoh]; omega) (by rw [hoff{K}]; omega)",
       nextpc=addr + 4,
       memw=("w8", f"vsp.toNat + {K}", "sdData_val d", [f"hoff{K}"]),
       track_hoff=f"hoff{K}", track_kind="w8",
       comment=f"sd a5 -> sp+{K - 592}: {cm}")

# === 25: sw zero,184(sp) ===
st(0x80005ca4, "store", "site_80005ca4_wp", vals=SP,
   hyps="$p:x2 $L rfl (by rw [hoff776]; omega) (by rw [hoff776]; omega)"
        " (by rw [hoff776, htoh]; omega) (by rw [hoff776]; omega)",
   nextpc=0x80005ca8,
   memw=("w4", "vsp.toNat + 776", "swData (0#64)", ["hoff776"]),
   track_hoff="hoff776", track_kind="w4",
   comment="sw zero,184(sp)")

# === 26/27: sw a4,20(sp) / sw a4,40(sp) — capacity (+_bf._size) := sz-1 ===
for (addr, site, K, cm) in [(0x80005ca8, "site_80005ca8_wp", 612, "FILE capacity := sz-1"),
                            (0x80005cac, "site_80005cac_wp", 632, "FILE _bf._size := sz-1")]:
    st(addr, "store", site, vals=f"{SP} _",
       hyps=f"$p:x2 $p:x14 $L rfl (by rw [hoff{K}]; omega) (by rw [hoff{K}]; omega)"
            f" (by rw [hoff{K}, htoh]; omega) (by rw [hoff{K}]; omega)",
       nextpc=addr + 4,
       memw=("w4", f"vsp.toNat + {K}", "swData (BitVec.ofNat 64 (sz.toNat - 1))",
             [f"hoff{K}"]),
       track_hoff=f"hoff{K}", track_kind="w4",
       comment=f"sw a4 -> sp+{K - 592}: {cm}")

# === 28: sw a6,24(sp) — the _flags word 0xffff0208 ===
st(0x80005cb0, "store", "site_80005cb0_wp", vals=f"{SP} _",
   hyps="$p:x2 $p:x16 $L rfl (by rw [hoff616]; omega) (by rw [hoff616]; omega)"
        " (by rw [hoff616, htoh]; omega) (by rw [hoff616]; omega)",
   nextpc=0x80005cb4,
   memw=("w4", "vsp.toNat + 616", "swData (0xffffffffffff0208#64)", ["hoff616"]),
   track_hoff="hoff616", track_kind="w4",
   comment="sw a6,24(sp) — _flags := 0x0208 (__SWR|__SSTR)")

# === 29: sd a3,0(sp) ===
st(0x80005cb4, "store", "site_80005cb4_wp", vals=f"{SP} _",
   hyps="$p:x2 $p:x13 $L rfl (by rw [hoff592]; omega) (by rw [hoff592]; omega)"
        " (by rw [hoff592, htoh]; omega) (by rw [hoff592]; omega)",
   nextpc=0x80005cb8,
   memw=("w8", "vsp.toNat + 592",
         "sdData_val ((vsp + (592#64)) + sign_extend (m := 64) (0x0e8#12))",
         ["hoff592"]),
   track_hoff="hoff592", track_kind="w8",
   comment="sd a3,0(sp) — va_list pointer copy")

# === 30: jal ra,_svfprintf_r ===
st(0x80005cb8, "jal", "site_80005cb8_wp", hyps="$L rfl", nextpc=0x80007654,
   pcrw="jal", jal_imm=0x00199c,
   rd="x1", rdval="(0x80005cbc#64)",
   rdrw="show BitVec.addInt (0x80005cb8#64) 4 = (0x80005cbc#64 : BitVec 64) from by"
        " apply BitVec.eq_of_toNat_eq; decide",
   track=True, comment="jal ra,_svfprintf_r — the call")

N = S.k
assert N == 30, N

# ---- post derivations ----
post = []

# survive helpers: writes in order (kind, key)
WRITES = [
    ("w8", 792), ("w8", 808), ("w8", 824), ("w8", 832), ("w8", 840),
    ("w8", 848), ("w8", 856), ("w8", 800), ("w8", 600), ("w8", 624),
    ("w4", 776), ("w4", 612), ("w4", 632), ("w4", 616), ("w8", 592),
]


def survive_chain(target_key, target_w, inner, pinfam):
    """later-write survival wrappers around `inner` for the writes after
    target_key's write (identified by first occurrence)."""
    idx = WRITES.index((target_w, target_key))
    later = WRITES[idx + 1:]
    lines = []
    for (kd, K) in reversed(later):
        fn = {"w8": f"{pinfam}_survives_writeMap8", "w4": f"{pinfam}_survives_writeMap4"}[kd]
        lines.append(f"    refine {fn} _ _ (by omega) ?_")
    return lines


# Pin8 cursor at vsp+600 (write 9), survives 624/776/612/632/616/592
post.append("\n".join(
    [f"  have hPcur : Pin8 σ{N}.mem (vsp.toNat + 600) d := by",
     f"    rw [hmE{N}]"]
    + survive_chain(600, "w8", None, "pinw8")
    + ["    exact Pin8_writeMap8 _ _ d"]))

# Pin4 capacity at vsp+612 = sz-1 (write 12), survives 632/616/592
post.append("\n".join(
    [f"  have hPcap : Pin4 σ{N}.mem (vsp.toNat + 612) (BitVec.ofNat 32 (sz.toNat - 1)) := by",
     f"    rw [hmE{N}, show swData (BitVec.ofNat 64 (sz.toNat - 1))"
     f" = ((BitVec.ofNat 32 (sz.toNat - 1)) : BitVec (8 * 4)) from extract32_ofNat64 _]"]
    + survive_chain(612, "w4", None, "pinw4")
    + ["    exact Pin4_writeMap4 _ _ _"]))

# the _flags bytes at vsp+616/617 (write 14), survive 592
post.append(f"""  have hfl0N : σ{N}.mem[vsp.toNat + 616]? = some (0x08#8) := by
    rw [hmE{N}, getElem?_writeMap8_out _ (vsp.toNat + 592) _ _ (by omega)]
    rw [show ((0x08#8 : BitVec 8)) = (swData (0xffffffffffff0208#64)).extractLsb' 0 8 from by decide]
    exact getElem_writeMap4_0 _ _ _
  have hfl1N : σ{N}.mem[vsp.toNat + 617]? = some (0x02#8) := by
    rw [hmE{N}, getElem?_writeMap8_out _ (vsp.toNat + 592) _ _ (by omega)]
    rw [show ((0x02#8 : BitVec 8)) = (swData (0xffffffffffff0208#64)).extractLsb' 8 8 from by decide]
    exact getElem_writeMap4_1 _ _ _""")

# Pin8 va value at vsp+824 (write 3)
post.append("\n".join(
    [f"  have hPva : Pin8 σ{N}.mem (vsp.toNat + 824) v := by",
     f"    rw [hmE{N}]"]
    + survive_chain(824, "w8", None, "pinw8")
    + ["    exact Pin8_writeMap8 _ _ v"]))

# SlotHolds for the epilogue reloads: s1@0x0c8(792), ra@0x0d8(808), s0@0x0d0(800)
for (nm, off, K, val) in [("hS0c8", 0x0c8, 792, "vS1o"), ("hS0d8", 0x0d8, 808, "wra0"),
                          ("hS0d0", 0x0d0, 800, "vS0o")]:
    lines = [f"  have {nm} : SlotHolds (vsp + (592#64)) 0x{off:03x} {val} σ{N}.mem := by",
             f"    rw [hmE{N}]"]
    idx = WRITES.index(("w8", K))
    for (kd, K2) in reversed(WRITES[idx + 1:]):
        fn = {"w8": "slot_survives_writeMap8", "w4": "slot_survives_writeMap4"}[kd]
        lines.append(f"    refine {fn} _ _ _ _ _ _ (by rw [hoff{K}]; omega) ?_")
    lines.append(f"    exact slot_save (vsp + (592#64)) 0x{off:03x} {val} _ _ _ hoff{K} rfl")
    post.append("\n".join(lines))

# single-window pointwise frame
frame_rws = []
for (kd, K) in reversed(WRITES):
    fn = {"w8": "getElem?_writeMap8_out", "w4": "getElem?_writeMap4_out_pro"}[kd]
    frame_rws.append(f"      {fn} _ (vsp.toNat + {K}) _ a (by omega)")
post.append(f"""  have hagN : ∀ a : Nat, ¬(vsp.toNat + 592 ≤ a ∧ a < vsp.toNat + 864) →
      σ{N}.mem[a]? = c.σ.mem[a]? := by
    intro a hw
    rw [hmE{N},
{",\n".join(frame_rws)}]""")

refine_items = [
    f"hG{N}", f"hpc{N}",
    "$p:x1", "$p:x2", "$p:x3", "$p:x8", "$p:x9", "$p:x10", "$p:x11", "$p:x12",
    "$p:x13", "$p:x18", "$p:x19", "$p:x20", "$p:x21", "$p:x22", "$p:x23",
    "$p:x24", "$p:x25", "$p:x26", "$p:x27",
    "hPcur", "hPcap", "hfl0N", "hfl1N", "hPva",
    "hS0c8", "hS0d0", "hS0d8",
    "hagN", f"hsl{N}",
    f"hi{N}", f"⟨vmi{N}, hmi{N}⟩",
]

core = "\n".join(S.out + post) + "\n"
tail_items = ",\n    ".join(S.subst(x, f"hp{N}", f"hmE{N}", N) for x in refine_items)
core += f"  refine ⟨⟨σ{N}, i{N}, c.steps + {N}⟩, ?_,\n    {tail_items}⟩\n"
chain = f"(Steps.single hstep{N})"
for j in range(N - 1, 0, -1):
    chain = f"((Steps.single hstep{j}).trans {chain})"
core += "  exact " + chain[1:-1] + "\n"

stmt = """/-- **The snprintf wrapper PRE-CALL segment**: `0x80005c44 → 0x80007654`.

From the `snprintf(d, sz, fmt, v)` ABI entry (`sp = vsp + 864`, `vsp` =
`_svfprintf_r`'s eventual frame base) through the 30-instruction wrapper body
to the completed `jal _svfprintf_r`: frame allocation, the seven va/save
spills, the `_impure_ptr` reent load, the `INT_MAX` size guard (not taken),
and the on-stack sink FILE struct construction — cursor := `d` (`Pin8`),
capacity := `sz − 1` (`Pin4`), `_flags` := `0x0208` (`__SWR|__SSTR`; bytes
`0x08`/`0x02` exported), the spilled `v` at the va area (`Pin8`), and the
three callee-save slots (`SlotHolds`) the return path reloads. -/
theorem snprintfPreCall_spec
    (vsp wra0 d sz vfmt v : BitVec 64)
    (va4o va5o va6o va7o : BitVec 64)
    (vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : Vsa.Sim.Code.SnprintfLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80005c44#64))
    (hx2 : c.σ.regs.get? Register.x2 = some (vsp + (864#64)))
    (hx1 : c.σ.regs.get? Register.x1 = some wra0)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx10 : c.σ.regs.get? Register.x10 = some d)
    (hx11 : c.σ.regs.get? Register.x11 = some sz)
    (hx12 : c.σ.regs.get? Register.x12 = some vfmt)
    (hx13 : c.σ.regs.get? Register.x13 = some v)
    (hx14 : c.σ.regs.get? Register.x14 = some va4o)
    (hx15 : c.σ.regs.get? Register.x15 = some va5o)
    (hx16 : c.σ.regs.get? Register.x16 = some va6o)
    (hx17 : c.σ.regs.get? Register.x17 = some va7o)
    (hx8 : c.σ.regs.get? Register.x8 = some vS0o)
    (hx9 : c.σ.regs.get? Register.x9 = some vS1o)
    (hx18 : c.σ.regs.get? Register.x18 = some vS2o)
    (hx19 : c.σ.regs.get? Register.x19 = some vS3o)
    (hx20 : c.σ.regs.get? Register.x20 = some vS4o)
    (hx21 : c.σ.regs.get? Register.x21 = some vS5o)
    (hx22 : c.σ.regs.get? Register.x22 = some vS6o)
    (hx23 : c.σ.regs.get? Register.x23 = some vS7o)
    (hx24 : c.σ.regs.get? Register.x24 = some vS8o)
    (hx25 : c.σ.regs.get? Register.x25 = some vS9o)
    (hx26 : c.σ.regs.get? Register.x26 = some vS10o)
    (hx27 : c.σ.regs.get? Register.x27 = some vS11o)
    (himp0 : c.σ.mem[(0x8001b970 : Nat)]? = some (0x38#8))
    (himp1 : c.σ.mem[(0x8001b970 : Nat) + 1]? = some (0xb5#8))
    (himp2 : c.σ.mem[(0x8001b970 : Nat) + 2]? = some (0x01#8))
    (himp3 : c.σ.mem[(0x8001b970 : Nat) + 3]? = some (0x80#8))
    (himp4 : c.σ.mem[(0x8001b970 : Nat) + 4]? = some (0x00#8))
    (himp5 : c.σ.mem[(0x8001b970 : Nat) + 5]? = some (0x00#8))
    (himp6 : c.σ.mem[(0x8001b970 : Nat) + 6]? = some (0x00#8))
    (himp7 : c.σ.mem[(0x8001b970 : Nat) + 7]? = some (0x00#8))
    (hsz23 : 23 ≤ sz.toNat)
    (hszhi : sz.toNat < 2 ^ 31)
    (hsplo : 0x8001c100 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 864 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x80007654#64) ∧
      c'.σ.regs.get? Register.x1 = some (0x80005cbc#64) ∧
      c'.σ.regs.get? Register.x2 = some (vsp + (592#64)) ∧
      c'.σ.regs.get? Register.x3 = some (0x8001b510#64) ∧
      c'.σ.regs.get? Register.x8 = some sz ∧
      c'.σ.regs.get? Register.x9 = some (0x8001b538#64) ∧
      c'.σ.regs.get? Register.x10 = some (0x8001b538#64) ∧
      c'.σ.regs.get? Register.x11 = some ((vsp + (592#64)) + sign_extend (m := 64) (0x008#12)) ∧
      c'.σ.regs.get? Register.x12 = some vfmt ∧
      c'.σ.regs.get? Register.x13 = some ((vsp + (592#64)) + sign_extend (m := 64) (0x0e8#12)) ∧
      c'.σ.regs.get? Register.x18 = some vS2o ∧
      c'.σ.regs.get? Register.x19 = some vS3o ∧
      c'.σ.regs.get? Register.x20 = some vS4o ∧
      c'.σ.regs.get? Register.x21 = some vS5o ∧
      c'.σ.regs.get? Register.x22 = some vS6o ∧
      c'.σ.regs.get? Register.x23 = some vS7o ∧
      c'.σ.regs.get? Register.x24 = some vS8o ∧
      c'.σ.regs.get? Register.x25 = some vS9o ∧
      c'.σ.regs.get? Register.x26 = some vS10o ∧
      c'.σ.regs.get? Register.x27 = some vS11o ∧
      Pin8 c'.σ.mem (vsp.toNat + 600) d ∧
      Pin4 c'.σ.mem (vsp.toNat + 612) (BitVec.ofNat 32 (sz.toNat - 1)) ∧
      c'.σ.mem[vsp.toNat + 616]? = some (0x08#8) ∧
      c'.σ.mem[vsp.toNat + 617]? = some (0x02#8) ∧
      Pin8 c'.σ.mem (vsp.toNat + 824) v ∧
      SlotHolds (vsp + (592#64)) 0x0c8 vS1o c'.σ.mem ∧
      SlotHolds (vsp + (592#64)) 0x0d0 vS0o c'.σ.mem ∧
      SlotHolds (vsp + (592#64)) 0x0d8 wra0 c'.σ.mem ∧
      (∀ a : Nat, ¬(vsp.toNat + 592 ≤ a ∧ a < vsp.toNat + 864) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      Vsa.Sim.Code.SnprintfLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have h592 : ((vsp + (592#64)) : BitVec 64).toNat = vsp.toNat + 592 := by
    rw [BitVec.toNat_add, show ((592#64 : BitVec 64)).toNat = 592 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
"""

hoffs = ""
for K, off in [(792, 0x0c8), (808, 0x0d8), (824, 0x0e8), (832, 0x0f0), (840, 0x0f8),
               (848, 0x100), (856, 0x108), (800, 0x0d0), (600, 0x008), (624, 0x020),
               (776, 0x0b8), (612, 0x014), (632, 0x028), (616, 0x018), (592, 0x000)]:
    hoffs += (f"  have hoff{K} : ((vsp + (592#64)) + sign_extend (m := 64)"
              f" (0x{off:03x}#12)).toNat = vsp.toNat + {K} := by\n"
              f"    rw [ptr_addoff (vsp + (592#64)) _ {K - 592} (by decide)"
              f" (by rw [h592]; omega), h592]\n")
hoffs += ("  have hoffimp : ((0x8001b510#64 : BitVec 64) + sign_extend (m := 64)"
          " (0x460#12)).toNat = (0x8001b970 : Nat) := by decide\n")

pins_list = ", ".join(f"⟨Register.{r}, {v}⟩" for r, v in pins)
pins_hyps = ", ".join(f"hx{r[1:]}" for r, _ in pins)
hp0 = (f"  have hp0 : PinsHold c.σ [{pins_list}] :=\n"
       f"    ⟨{pins_hyps}, trivial⟩\n")

hdr = """import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesWrap
import Vsa.Sim.SnprintfSpec20
import Vsa.Sim.SlotFrame
import Vsa.Sim.PinW
import Vsa.Sim.CodeRangeInsert
import Vsa.Sim.Code.LldFmt

/-!
# M3 Layer-3 — `SnprintfSpec40` : the snprintf wrapper PRE-CALL segment
## `0x80005c44` (snprintf ABI entry) → `0x80007654` (`jal _svfprintf_r` completed)

The WHILE interpreter's `stringify` int arm calls `snprintf(buf, 64, "%lld", v)`
(`0x800030d8`); newlib's `snprintf` (`0x80005c44`) builds the string-sink FILE
struct on its own 272-byte frame and calls `_svfprintf_r` directly (`jal` at
`0x80005cb8`).  This module verifies the 30-instruction pre-call body,
exporting exactly the wrapper-owned inputs of `svfprintf_lld_spec` (Spec38):
the FILE cursor/capacity/`_flags` pins, the spilled va-area value bytes, the
epilogue `SlotHolds`, and the single-window memory frame.

Also hosts the wrapper-shared value lemmas and the `of_agree` code-pin
transports Spec42 uses at the composition seams.

Emitted by `scripts/pro_emitter/gen_spec40.py` (SnprintfSpec27 house style).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Wrapper value lemmas -/

/-- `addi sp,sp,-272` from `vsp + 864` lands on `vsp + 592`. -/
theorem sp_dec272_wr (vsp : BitVec 64) :
    (vsp + (864#64)) + sign_extend (m := 64) (0xef0#12) = vsp + (592#64) := by
  rw [BitVec.add_assoc]
  congr 1

/-- `addi sp,sp,272` from `vsp + 592` restores `vsp + 864`. -/
theorem sp_inc272_wr (vsp : BitVec 64) :
    (vsp + (592#64)) + sign_extend (m := 64) (0x110#12) = vsp + (864#64) := by
  rw [BitVec.add_assoc]
  congr 1

/-- `lui t1,0x80000; not t1,t1` = `INT_MAX`. -/
theorem t1_notmask_wr :
    (sign_extend (m := 64) ((0x80000#20) +++ 0x000#12) : BitVec 64)
      ^^^ sign_extend (m := 64) (0xfff#12) = (0x7fffffff#64) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- `lui a6,0xffff0; addi a6,a6,520` = the `0xffff0208` flags image. -/
theorem a6_flags_wr :
    (sign_extend (m := 64) ((0xffff0#20) +++ 0x000#12) : BitVec 64)
      + sign_extend (m := 64) (0x208#12) = (0xffffffffffff0208#64) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- Introduction form of the `bltu` guard: `a < b` (as `toNat`) ⇒ taken. -/
theorem bltu_of_lt_wr (a b : BitVec 64) (h : a.toNat < b.toNat) :
    zopz0zI_u a b = true := by
  unfold zopz0zI_u; simp only [Sail.BitVec.toNatInt]
  exact decide_eq_true (Int.ofNat_lt.mpr h)

/-- Introduction form of the `bltu` NOT-taken guard: `b ≤ a` ⇒ not taken. -/
theorem bltu_false_of_ge_wr (a b : BitVec 64) (h : b.toNat ≤ a.toNat) :
    zopz0zI_u a b = false := by
  unfold zopz0zI_u; simp only [Sail.BitVec.toNatInt]
  exact decide_eq_false (fun hc => Nat.not_lt.mpr h (Int.ofNat_lt.mp hc))

/-- The `subw a4,a1,a4` capacity value: for `1 ≤ sz < 2^31` and `a4 = 1`,
the sign-extended 32-bit difference is `sz − 1`. -/
theorem subw_cap_wr (sz : BitVec 64) (h1 : 1 ≤ sz.toNat) (h2 : sz.toNat < 2 ^ 31) :
    (sign_extend (m := 64)
      ((Sail.BitVec.extractLsb sz 31 0) - (Sail.BitVec.extractLsb (1#64) 31 0)) : BitVec 64)
      = BitVec.ofNat 64 (sz.toNat - 1) := by
  have hesz : (Sail.BitVec.extractLsb sz 31 0).toNat = sz.toNat := by
    show (BitVec.ofNat (31 - 0 + 1) (sz.toNat >>> 0)).toNat = sz.toNat
    rw [Nat.shiftRight_zero, BitVec.toNat_ofNat]
    have := sz.isLt
    exact Nat.mod_eq_of_lt (by omega)
  rw [show (Sail.BitVec.extractLsb (1#64) 31 0) = (1#32) from by decide]
  have hz : ((Sail.BitVec.extractLsb sz 31 0) - (1#32)).toNat = sz.toNat - 1 := by
    rw [BitVec.toNat_sub, hesz, show ((1#32 : BitVec 32)).toNat = 1 from rfl]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [sext32_toNat_small _ (by omega), hz, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (by omega)).symm

/-! ## `SnprintfLoaded` write-survival (CodeRangeInsert pattern) -/

theorem snprintf_insert_wr (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (b : BitVec 8)
    (hk : 0x80018000 ≤ k) (h : Vsa.Sim.Code.SnprintfLoaded mem) :
    Vsa.Sim.Code.SnprintfLoaded (mem.insert k b) := by
  unfold Vsa.Sim.Code.SnprintfLoaded at h ⊢
  simp only [Vsa.Sim.Code.snprintfChunk0, Vsa.Sim.Code.snprintfChunk1,
    Vsa.Sim.Code.snprintfChunk2, Vsa.Sim.Code.snprintfChunk3] at h ⊢
  simp (disch := omega) only
    [getElem?_insert_outside 0x80005c44 0x80005d18 mem k b (Or.inr (by omega))]
  exact h

theorem snprintf_w8_wr (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (dw : BitVec (8 * 8))
    (ha : 0x80018000 ≤ a) (h : Vsa.Sim.Code.SnprintfLoaded mem) :
    Vsa.Sim.Code.SnprintfLoaded (writeMap8 mem a dw) :=
  snprintf_insert_wr _ _ _ (by omega) (snprintf_insert_wr _ _ _ (by omega)
    (snprintf_insert_wr _ _ _ (by omega) (snprintf_insert_wr _ _ _ (by omega)
    (snprintf_insert_wr _ _ _ (by omega) (snprintf_insert_wr _ _ _ (by omega)
    (snprintf_insert_wr _ _ _ (by omega) (snprintf_insert_wr _ _ _ (by omega) h)))))))

theorem snprintf_w4_wr (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (dw : BitVec (8 * 4))
    (ha : 0x80018000 ≤ a) (h : Vsa.Sim.Code.SnprintfLoaded mem) :
    Vsa.Sim.Code.SnprintfLoaded (writeMap4 mem a dw) :=
  snprintf_insert_wr _ _ _ (by omega) (snprintf_insert_wr _ _ _ (by omega)
    (snprintf_insert_wr _ _ _ (by omega) (snprintf_insert_wr _ _ _ (by omega) h)))

/-! ## `of_agree` code-pin transports for the composition seams (Spec42)

All from ONE pointwise agreement below `0x8001c000`: every code/static pin the
wrapper chain consumes sits below it, and every memory write in the chain
(snprintf frame ≥ `vsp+592`, svfprintf frame ≥ `vsp−88`, destination ≥ `d`)
sits at/above it under the capstone's layout hypotheses. -/

theorem snprintf_of_agree_wr {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, a < 0x8001c000 → mem[a]? = m0[a]?)
    (h : Vsa.Sim.Code.SnprintfLoaded m0) : Vsa.Sim.Code.SnprintfLoaded mem := by
  unfold Vsa.Sim.Code.SnprintfLoaded at h ⊢
  simp only [Vsa.Sim.Code.snprintfChunk0, Vsa.Sim.Code.snprintfChunk1,
    Vsa.Sim.Code.snprintfChunk2, Vsa.Sim.Code.snprintfChunk3] at h ⊢
  simp (disch := omega) only [hag]
  exact h

theorem lldfmt_of_agree_wr {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, a < 0x8001c000 → mem[a]? = m0[a]?)
    (h : Vsa.Sim.Code.LldFmtLoaded m0) : Vsa.Sim.Code.LldFmtLoaded mem := by
  unfold Vsa.Sim.Code.LldFmtLoaded Vsa.Sim.Code.lldFmtChunk0 at h ⊢
  simp (disch := omega) only [hag]
  exact h

theorem localeconv_of_agree_wr {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, a < 0x8001c000 → mem[a]? = m0[a]?)
    (h : Vsa.Sim.Code._localeconv_rLoaded m0) : Vsa.Sim.Code._localeconv_rLoaded mem := by
  unfold Vsa.Sim.Code._localeconv_rLoaded at h ⊢
  simp only [Vsa.Sim.Code._localeconv_rChunk0] at h ⊢
  simp (disch := omega) only [hag]
  exact h

theorem strlen_of_agree_wr {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, a < 0x8001c000 → mem[a]? = m0[a]?)
    (h : Vsa.Sim.Code.StrlenLoaded m0) : Vsa.Sim.Code.StrlenLoaded mem := by
  unfold Vsa.Sim.Code.StrlenLoaded at h ⊢
  simp only [Vsa.Sim.Code.strlenChunk0, Vsa.Sim.Code.strlenChunk1,
    Vsa.Sim.Code.strlenChunk2, Vsa.Sim.Code.strlenChunk3] at h ⊢
  simp (disch := omega) only [hag]
  exact h

theorem memset_of_agree_wr {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, a < 0x8001c000 → mem[a]? = m0[a]?)
    (h : Vsa.Sim.Code.MemsetLoaded m0) : Vsa.Sim.Code.MemsetLoaded mem := by
  unfold Vsa.Sim.Code.MemsetLoaded at h ⊢
  simp only [Vsa.Sim.Code.memsetChunk0, Vsa.Sim.Code.memsetChunk1,
    Vsa.Sim.Code.memsetChunk2, Vsa.Sim.Code.memsetChunk3] at h ⊢
  simp (disch := omega) only [hag]
  exact h

theorem ssprint_of_agree_wr {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, a < 0x8001c000 → mem[a]? = m0[a]?)
    (h : Vsa.Sim.Code.__ssprint_rLoaded m0) : Vsa.Sim.Code.__ssprint_rLoaded mem := by
  unfold Vsa.Sim.Code.__ssprint_rLoaded at h ⊢
  simp only [Vsa.Sim.Code.__ssprint_rChunk0, Vsa.Sim.Code.__ssprint_rChunk1,
    Vsa.Sim.Code.__ssprint_rChunk2, Vsa.Sim.Code.__ssprint_rChunk3] at h ⊢
  simp (disch := omega) only [hag]
  exact h

theorem ssputs_of_agree_wr {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, a < 0x8001c000 → mem[a]? = m0[a]?)
    (h : Vsa.Sim.Code.__ssputs_rLoaded m0) : Vsa.Sim.Code.__ssputs_rLoaded mem := by
  unfold Vsa.Sim.Code.__ssputs_rLoaded at h ⊢
  simp only [Vsa.Sim.Code.__ssputs_rChunk0, Vsa.Sim.Code.__ssputs_rChunk1,
    Vsa.Sim.Code.__ssputs_rChunk2, Vsa.Sim.Code.__ssputs_rChunk3,
    Vsa.Sim.Code.__ssputs_rChunk4, Vsa.Sim.Code.__ssputs_rChunk5,
    Vsa.Sim.Code.__ssputs_rChunk6] at h ⊢
  simp (disch := omega) only [hag]
  exact h

theorem memmove_of_agree_wr {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, a < 0x8001c000 → mem[a]? = m0[a]?)
    (h : Vsa.Sim.Code.MemmoveLoaded m0) : Vsa.Sim.Code.MemmoveLoaded mem := by
  unfold Vsa.Sim.Code.MemmoveLoaded at h ⊢
  simp only [Vsa.Sim.Code.memmoveChunk0, Vsa.Sim.Code.memmoveChunk1,
    Vsa.Sim.Code.memmoveChunk2, Vsa.Sim.Code.memmoveChunk3,
    Vsa.Sim.Code.memmoveChunk4] at h ⊢
  simp (disch := omega) only [hag]
  exact h

"""

out = hdr + stmt + hoffs + hp0 + core + "\nend Vsa.Sim\n"
open("Vsa/Sim/SnprintfSpec40.lean", "w").write(out)
print("wrote Vsa/Sim/SnprintfSpec40.lean", len(out.splitlines()), "lines")
