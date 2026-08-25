#!/usr/bin/env python3
import sys
sys.path.insert(0, "/tmp")
from emit_pro_seg import Seg

pins = [
    ("x2", "vsp + (592#64)"), ("x1", "vra0"), ("x3", "(0x8001b510#64)"),
    ("x10", "va0"), ("x11", "vfile"), ("x12", "vfmt"), ("x13", "vva"),
    ("x8", "vS0o"), ("x9", "vS1o"), ("x22", "vS6o"), ("x18", "vS2o"),
    ("x19", "vS3o"), ("x20", "vS4o"), ("x21", "vS5o"), ("x23", "vS7o"),
    ("x24", "vS8o"), ("x25", "vS9o"), ("x26", "vS10o"), ("x27", "vS11o"),
]
S = Seg(pins)

SVF = "Vsa.Sim.Code.SvfprintfSliceLoaded"
LC = "Vsa.Sim.Code._localeconv_rLoaded"


def track_loaded(k, store_hoff=None, kind=None):
    P = k - 1
    for nm, pred, w8fn, insfn in [("hsl", SVF, "svfprintfSlice_writeMap8_sn5",
                                   "svfprintfSlice_insert_sn4"),
                                  ("hlc", LC, "localeconv_w8_pro",
                                   "localeconv_insert_pro")]:
        prev = f"{nm}{P}" if P > 0 else f"{nm}0"
        if store_hoff is None:
            S.emit(f"  have {nm}{k} : {pred} σ{k}.mem := by rw [hmem{k}]; exact {prev}")
        else:
            fn = w8fn if kind == "w8" else insfn
            S.emit(f"  have {nm}{k} : {pred} σ{k}.mem := by",
                   f"    rw [hmem{k}, mem_afterNextPC]",
                   f"    exact {fn} _ _ _ (by rw [{store_hoff}]; omega) {prev}")


def st(*a, **kw):
    hoff = kw.pop("track_hoff", None)
    kind = kw.pop("track_kind", None)
    S.step(*a, **kw)
    S.out.pop()
    track_loaded(S.k, hoff, kind)
    S.emit("")


st(0x80007654, "alu", "site_80007654_pr", vals="(vsp + (592#64))",
   hyps="$p:x2 hsl0 rfl", nextpc=0x80007658,
   rd="x2", rdval="vsp", rdrw="sp_dec592_pro vsp", track=True,
   comment="addi sp,sp,-592")

spills = [
    (0x80007658, "site_80007658_pr", "x1", 584, "vra0"),
    (0x8000765c, "site_8000765c_pr", "x13", 24, "vva"),
    (0x80007660, "site_80007660_pr", "x11", 8, "vfile"),
    (0x80007664, "site_80007664_pr", "x8", 576, "vS0o"),
    (0x80007668, "site_80007668_pr", "x9", 568, "vS1o"),
    (0x8000766c, "site_8000766c_pr", "x22", 528, "vS6o"),
]
for (addr, site, rs2, K, val) in spills:
    st(addr, "store", site, vals="vsp _",
       hyps=f"$p:x2 $p:{rs2} $L rfl (by rw [hoff{K}]; omega) (by rw [hoff{K}]; omega)"
            f" (by rw [hoff{K}, htoh]; omega) (by rw [hoff{K}]; omega)",
       nextpc=addr + 4,
       memw=("w8", f"vsp.toNat + {K}", f"sdData_val {val}", [f"hoff{K}"]),
       track_hoff=f"hoff{K}", track_kind="w8",
       comment=f"sd -> sp+{K}")

st(0x80007670, "alu", "site_80007670_pr", vals="vfile", hyps="$p:x11 $L rfl",
   nextpc=0x80007674, rd="x9", rdval="vfile", rdrw="sext0_add_pro vfile", track=True,
   comment="mv s1,a1")
st(0x80007674, "alu", "site_80007674_pr", vals="vfmt", hyps="$p:x12 $L rfl",
   nextpc=0x80007678, rd="x22", rdval="vfmt", rdrw="sext0_add_pro vfmt", track=True,
   comment="mv s6,a2")
st(0x80007678, "alu", "site_80007678_pr", vals="va0", hyps="$p:x10 $L rfl",
   nextpc=0x8000767c, rd="x8", rdval="va0", rdrw="sext0_add_pro va0", track=True,
   comment="mv s0,a0")

st(0x8000767c, "jal", "site_8000767c_pr", hyps="$L rfl", nextpc=0x80010258, pcrw="jal",
   rd="x1", rdval="(0x80007680#64)",
   rdrw="show BitVec.addInt (0x8000767c#64) 4 = (0x80007680#64 : BitVec 64) from by"
        " apply BitVec.eq_of_toNat_eq; decide",
   track=True, comment="jal _localeconv_r")

st(0x80010258, "alu", "site_80010258_pl", vals="(0x8001b510#64)",
   hyps="$p:x3 $L:hlc rfl", nextpc=0x8001025c,
   rd="x10", rdval="(0x8001b898#64)",
   rdrw="show (0x8001b510#64 : BitVec 64) + sign_extend (m := 64) (0x388#12)"
        " = (0x8001b898#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide",
   track=True, comment="addi a0,gp,904 (lconv = 0x8001b898)")
st(0x8001025c, "jr", "site_8001025c_pl", vals="(0x80007680#64)",
   hyps="$p:x1 $L:hlc rfl (by rw [ret_tgt _ (by decide)]; decide)",
   nextpc=0x80007680, pcrw="ret", comment="ret (back to 0x80007680)")

S.emit("""  -- agreement below the frame after the six spills (all keys ≥ vsp)
  have hag13 : ∀ a : Nat, a < vsp.toNat → σ13.mem[a]? = c.σ.mem[a]? := by
    intro a ha
    rw [hmE13,
      getElem?_writeMap8_out _ (vsp.toNat + 528) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 568) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 576) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 8) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 24) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 584) _ a (by omega)]
""")
st(0x80007680, "alu", "site_80007680_pr", vals="(0x8001b898#64) _ _ _ _ _ _ _ _",
   hyps="$p:x10 $L rfl (by rw [hoffdp]; omega) (by rw [hoffdp]; omega)"
        " (by rw [hoffdp, htoh]; omega) (by rw [hoffdp])"
        " (by rw [hoffdp]; exact (hag13 _ (by omega)).trans hdp0)"
        " (by rw [hoffdp]; exact (hag13 _ (by omega)).trans hdp1)"
        " (by rw [hoffdp]; exact (hag13 _ (by omega)).trans hdp2)"
        " (by rw [hoffdp]; exact (hag13 _ (by omega)).trans hdp3)"
        " (by rw [hoffdp]; exact (hag13 _ (by omega)).trans hdp4)"
        " (by rw [hoffdp]; exact (hag13 _ (by omega)).trans hdp5)"
        " (by rw [hoffdp]; exact (hag13 _ (by omega)).trans hdp6)"
        " (by rw [hoffdp]; exact (hag13 _ (by omega)).trans hdp7)",
   nextpc=0x80007684,
   rd="x14", rdval="(0x80019770#64)",
   rdrw="show (sign_extend (m := 64)"
        " (((((((((0x00#8).append (0x00#8)).append (0x00#8)).append (0x00#8)).append"
        " (0x80#8)).append (0x01#8)).append (0x97#8)).append (0x70#8))"
        " : BitVec (8 * 8)) : BitVec 64) = (0x80019770#64 : BitVec 64) from by"
        " apply BitVec.eq_of_toNat_eq; decide",
   track=True, comment="ld a4,0(a0) — decimal_point = 0x80019770")

st(0x80007684, "alu", "site_80007684_pr", vals="(0x80019770#64)", hyps="$p:x14 $L rfl",
   nextpc=0x80007688, rd="x10", rdval="(0x80019770#64)",
   rdrw="sext0_add_pro (0x80019770#64)", track=True, comment="mv a0,a4")

st(0x80007688, "store", "site_80007688_pr", vals="vsp _",
   hyps="$p:x2 $p:x14 $L rfl (by rw [hoff80]; omega) (by rw [hoff80]; omega)"
        " (by rw [hoff80, htoh]; omega) (by rw [hoff80]; omega)",
   nextpc=0x8000768c,
   memw=("w8", "vsp.toNat + 80", "sdData_val (0x80019770#64)", ["hoff80"]),
   track_hoff="hoff80", track_kind="w8",
   comment="sd a4,80(sp) — lconv decimal_point spill")

N = S.k
assert N == 16, N

# ---- post derivations ----
post = []
post.append(f"""  -- exported Loaded predicates for the later segments
  have hstrlN : Vsa.Sim.Code.StrlenLoaded σ{N}.mem := by
    rw [hmE{N}]
    exact strlen_w8_pro _ _ _ (by omega) (strlen_w8_pro _ _ _ (by omega)
      (strlen_w8_pro _ _ _ (by omega) (strlen_w8_pro _ _ _ (by omega)
      (strlen_w8_pro _ _ _ (by omega) (strlen_w8_pro _ _ _ (by omega)
      (strlen_w8_pro _ _ _ (by omega) hstrl))))))
  have hmsN : Vsa.Sim.Code.MemsetLoaded σ{N}.mem := by
    rw [hmE{N}]
    exact memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) hms))))))
  have hlmN : Vsa.Sim.Code.__locale_mb_cur_maxLoaded σ{N}.mem := by
    rw [hmE{N}]
    exact localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) hlm))))))
  have hambN : Vsa.Sim.Code.__ascii_mbtowcLoaded σ{N}.mem := by
    rw [hmE{N}]
    exact amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) hamb))))))""")

# slot exports: (name, off-hex, hoff, value, #later-writes)
slots = [
    ("hS248", 0x248, "hoff584", "vra0", 6),
    ("hS018", 0x018, "hoff24", "vva", 5),
    ("hS008", 0x008, "hoff8", "vfile", 4),
    ("hS240", 0x240, "hoff576", "vS0o", 3),
    ("hS238", 0x238, "hoff568", "vS1o", 2),
    ("hS210", 0x210, "hoff528", "vS6o", 1),
    ("hS050", 0x050, "hoff80", "(0x80019770#64)", 0),
]
for (nm, off, hoff, val, later) in slots:
    ln = [f"  have {nm} : SlotHolds vsp 0x{off:03x} {val} σ{N}.mem := by",
          f"    rw [hmE{N}]"]
    for _ in range(later):
        ln.append(f"    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [{hoff}]; omega) ?_")
    ln.append(f"    exact slot_save vsp 0x{off:03x} {val} _ _ _ {hoff} rfl")
    post.append("\n".join(ln))

post.append(f"""  have hagN : ∀ a : Nat, ¬(vsp.toNat + 584 ≤ a ∧ a < vsp.toNat + 592) →
      ¬(vsp.toNat + 24 ≤ a ∧ a < vsp.toNat + 32) →
      ¬(vsp.toNat + 8 ≤ a ∧ a < vsp.toNat + 16) →
      ¬(vsp.toNat + 576 ≤ a ∧ a < vsp.toNat + 584) →
      ¬(vsp.toNat + 568 ≤ a ∧ a < vsp.toNat + 576) →
      ¬(vsp.toNat + 528 ≤ a ∧ a < vsp.toNat + 536) →
      ¬(vsp.toNat + 80 ≤ a ∧ a < vsp.toNat + 88) →
      σ{N}.mem[a]? = c.σ.mem[a]? := by
    intro a hw0 hw1 hw2 hw3 hw4 hw5 hw6
    rw [hmE{N},
      getElem?_writeMap8_out _ (vsp.toNat + 80) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 528) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 568) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 576) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 8) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 24) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 584) _ a (by omega)]""")

refine_items = [
    f"hG{N}", f"hpc{N}",
    "$p:x2", "$p:x1", "$p:x3", "$p:x8", "$p:x9", "$p:x22", "$p:x10", "$p:x14",
    "$p:x12", "$p:x13", "$p:x18", "$p:x19", "$p:x20", "$p:x21", "$p:x23",
    "$p:x24", "$p:x25", "$p:x26", "$p:x27",
    "hS248", "hS018", "hS008", "hS240", "hS238", "hS210", "hS050",
    "hagN", f"hsl{N}", f"hlc{N}", "hstrlN", "hmsN", "hlmN", "hambN",
    f"hi{N}", f"⟨vmi{N}, hmi{N}⟩",
]

core = "\n".join(S.out + post) + "\n"
tail_items = ",\n    ".join(S.subst(x, f"hp{N}", f"hmE{N}", N) for x in refine_items)
core += f"  refine ⟨⟨σ{N}, i{N}, c.steps + {N}⟩, ?_,\n    {tail_items}⟩\n"
chain = f"(Steps.single hstep{N})"
for j in range(N - 1, 0, -1):
    chain = f"((Steps.single hstep{j}).trans {chain})"
core += "  exact " + chain[1:-1] + "\n"

stmt = """/-- **Segment A of the svfprintf prologue**: `0x80007654 → 0x8000768c`.

Entry: the `_svfprintf_r` ABI entry (`a0` = reent, `a1` = FILE, `a2` = fmt,
`a3` = va_list, `sp = vsp + 592`).  Runs `addi sp,sp,-592`, the first six
spills (`ra/a3/a1/s0/s1/s6`), the register moves, the `_localeconv_r` call
(2 callee instructions, inlined), the `ld` of the static `decimal_point`
pointer, and its spill to `sp+80`; stops poised at the `jal strlen`. -/
theorem svfProA_spec
    (vsp vra0 va0 vfile vfmt vva : BitVec 64)
    (vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : Vsa.Sim.Code.SvfprintfSliceLoaded c.σ.mem)
    (hlc0 : Vsa.Sim.Code._localeconv_rLoaded c.σ.mem)
    (hstrl : Vsa.Sim.Code.StrlenLoaded c.σ.mem)
    (hms : Vsa.Sim.Code.MemsetLoaded c.σ.mem)
    (hlm : Vsa.Sim.Code.__locale_mb_cur_maxLoaded c.σ.mem)
    (hamb : Vsa.Sim.Code.__ascii_mbtowcLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80007654#64))
    (hx2 : c.σ.regs.get? Register.x2 = some (vsp + (592#64)))
    (hx1 : c.σ.regs.get? Register.x1 = some vra0)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx10 : c.σ.regs.get? Register.x10 = some va0)
    (hx11 : c.σ.regs.get? Register.x11 = some vfile)
    (hx12 : c.σ.regs.get? Register.x12 = some vfmt)
    (hx13 : c.σ.regs.get? Register.x13 = some vva)
    (hx8 : c.σ.regs.get? Register.x8 = some vS0o)
    (hx9 : c.σ.regs.get? Register.x9 = some vS1o)
    (hx22 : c.σ.regs.get? Register.x22 = some vS6o)
    (hx18 : c.σ.regs.get? Register.x18 = some vS2o)
    (hx19 : c.σ.regs.get? Register.x19 = some vS3o)
    (hx20 : c.σ.regs.get? Register.x20 = some vS4o)
    (hx21 : c.σ.regs.get? Register.x21 = some vS5o)
    (hx23 : c.σ.regs.get? Register.x23 = some vS7o)
    (hx24 : c.σ.regs.get? Register.x24 = some vS8o)
    (hx25 : c.σ.regs.get? Register.x25 = some vS9o)
    (hx26 : c.σ.regs.get? Register.x26 = some vS10o)
    (hx27 : c.σ.regs.get? Register.x27 = some vS11o)
    (hdp0 : c.σ.mem[(0x8001b898 : Nat)]? = some (0x70#8))
    (hdp1 : c.σ.mem[(0x8001b898 : Nat) + 1]? = some (0x97#8))
    (hdp2 : c.σ.mem[(0x8001b898 : Nat) + 2]? = some (0x01#8))
    (hdp3 : c.σ.mem[(0x8001b898 : Nat) + 3]? = some (0x80#8))
    (hdp4 : c.σ.mem[(0x8001b898 : Nat) + 4]? = some (0x00#8))
    (hdp5 : c.σ.mem[(0x8001b898 : Nat) + 5]? = some (0x00#8))
    (hdp6 : c.σ.mem[(0x8001b898 : Nat) + 6]? = some (0x00#8))
    (hdp7 : c.σ.mem[(0x8001b898 : Nat) + 7]? = some (0x00#8))
    (hsplo : 0x8001c000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x8000768c#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x1 = some (0x80007680#64) ∧
      c'.σ.regs.get? Register.x3 = some (0x8001b510#64) ∧
      c'.σ.regs.get? Register.x8 = some va0 ∧
      c'.σ.regs.get? Register.x9 = some vfile ∧
      c'.σ.regs.get? Register.x22 = some vfmt ∧
      c'.σ.regs.get? Register.x10 = some (0x80019770#64) ∧
      c'.σ.regs.get? Register.x14 = some (0x80019770#64) ∧
      c'.σ.regs.get? Register.x12 = some vfmt ∧
      c'.σ.regs.get? Register.x13 = some vva ∧
      c'.σ.regs.get? Register.x18 = some vS2o ∧
      c'.σ.regs.get? Register.x19 = some vS3o ∧
      c'.σ.regs.get? Register.x20 = some vS4o ∧
      c'.σ.regs.get? Register.x21 = some vS5o ∧
      c'.σ.regs.get? Register.x23 = some vS7o ∧
      c'.σ.regs.get? Register.x24 = some vS8o ∧
      c'.σ.regs.get? Register.x25 = some vS9o ∧
      c'.σ.regs.get? Register.x26 = some vS10o ∧
      c'.σ.regs.get? Register.x27 = some vS11o ∧
      SlotHolds vsp 0x248 vra0 c'.σ.mem ∧
      SlotHolds vsp 0x018 vva c'.σ.mem ∧
      SlotHolds vsp 0x008 vfile c'.σ.mem ∧
      SlotHolds vsp 0x240 vS0o c'.σ.mem ∧
      SlotHolds vsp 0x238 vS1o c'.σ.mem ∧
      SlotHolds vsp 0x210 vS6o c'.σ.mem ∧
      SlotHolds vsp 0x050 (0x80019770#64) c'.σ.mem ∧
      (∀ a : Nat, ¬(vsp.toNat + 584 ≤ a ∧ a < vsp.toNat + 592) →
      ¬(vsp.toNat + 24 ≤ a ∧ a < vsp.toNat + 32) →
      ¬(vsp.toNat + 8 ≤ a ∧ a < vsp.toNat + 16) →
      ¬(vsp.toNat + 576 ≤ a ∧ a < vsp.toNat + 584) →
      ¬(vsp.toNat + 568 ≤ a ∧ a < vsp.toNat + 576) →
      ¬(vsp.toNat + 528 ≤ a ∧ a < vsp.toNat + 536) →
      ¬(vsp.toNat + 80 ≤ a ∧ a < vsp.toNat + 88) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      Vsa.Sim.Code.SvfprintfSliceLoaded c'.σ.mem ∧
      Vsa.Sim.Code._localeconv_rLoaded c'.σ.mem ∧
      Vsa.Sim.Code.StrlenLoaded c'.σ.mem ∧
      Vsa.Sim.Code.MemsetLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__locale_mb_cur_maxLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__ascii_mbtowcLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
"""

hoffs = ""
for K, off in [(584, 0x248), (24, 0x018), (8, 0x008), (576, 0x240), (568, 0x238),
               (528, 0x210), (80, 0x050)]:
    hoffs += (f"  have hoff{K} : (vsp + sign_extend (m := 64) (0x{off:03x}#12)).toNat"
              f" = vsp.toNat + {K} := ptr_addoff vsp _ {K} (by decide) (by omega)\n")
hoffs += ("  have hoffdp : ((0x8001b898#64 : BitVec 64) + sign_extend (m := 64)"
          " (0x000#12)).toNat = (0x8001b898 : Nat) := by decide\n")

pins_list = ", ".join(f"⟨Register.{r}, {v}⟩" for r, v in pins)
pins_hyps = ", ".join(f"hx{r[1:]}" for r, _ in pins)
hp0 = (f"  have hp0 : PinsHold c.σ [{pins_list}] :=\n"
       f"    ⟨{pins_hyps}, trivial⟩\n")

hdr = """import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.SnprintfSitesPro2

/-!
# M3 Layer-3 — `SnprintfSpec27` : svfprintf prologue segment A
## `0x80007654` (entry) → `0x8000768c` (the `jal strlen`)

First segment of the svfprintf PROLOGUE + first-parse-pass chain (pctrace
`[0x80007654, 0x800077c0)`).  16 machine steps: `addi sp,sp,-592`, the six
early spills, the `mv` triple, `jal _localeconv_r` with the 2-instruction
callee body inlined (`addi a0,gp,904; ret` — gp is the concrete link-time
`0x8001b510`), the `ld` of the static `decimal_point` pointer
(`0x8001b898 → 0x80019770`), `mv a0,a4`, and the spill of the pointer to
`sp+80`.  Generated in the SnprintfSpec22 house style by /tmp/gen_spec27.py.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

"""

out = hdr + stmt + hoffs + hp0 + core + "\nend Vsa.Sim\n"
open("Vsa/Sim/SnprintfSpec27.lean", "w").write(out)
print("wrote Vsa/Sim/SnprintfSpec27.lean", len(out.splitlines()), "lines")
