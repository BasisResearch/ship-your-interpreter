#!/usr/bin/env python3
import sys
sys.path.insert(0, "/tmp")
from emit_pro_seg import Seg

pins = [
    ("x2", "vsp"), ("x3", "(0x8001b510#64)"), ("x8", "va0"), ("x9", "vfile"),
    ("x22", "vfmt"), ("x10", "vsp + sign_extend (m := 64) (0x0c8#12)"),
    ("x11", "(0#64)"), ("x12", "(8#64)"),
    ("x18", "vS2o"), ("x19", "vS3o"), ("x20", "vS4o"), ("x21", "vS5o"),
    ("x23", "vS7o"), ("x24", "vS8o"), ("x25", "vS9o"), ("x26", "vS10o"),
    ("x27", "vS11o"),
]
S = Seg(pins)


def st(*a, **kw):
    S.step(*a, **kw)


def dshow(lhs, rhs):
    return f"show {lhs} = ({rhs} : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide"


# 1: jal memset
st(0x800076a0, "jal", "site_800076a0_pr", hyps="hsl0 rfl", nextpc=0x80006aec, pcrw="jal",
   rd="x1", rdval="(0x800076a4#64)",
   rdrw="show BitVec.addInt (0x800076a0#64) 4 = (0x800076a4#64 : BitVec 64) from by"
        " apply BitVec.eq_of_toNat_eq; decide",
   track=True, comment="jal memset")

st(0x80006aec, "alu", "site_80006aec_pm", hyps="($mE ▸ hms0) rfl", nextpc=0x80006af0,
   rd="x6", rdval="(15#64)",
   rdrw=dshow("((0#64) : BitVec 64) + sign_extend (m := 64) (0x00f#12)", "15#64"),
   track=True, comment="li t1,15")
st(0x80006af0, "alu", "site_80006af0_pm", vals="(vsp + sign_extend (m := 64) (0x0c8#12))",
   hyps="$p:x10 ($mE ▸ hms0) rfl", nextpc=0x80006af4,
   rd="x14", rdval="vsp + sign_extend (m := 64) (0x0c8#12)",
   rdrw="sext0_add_pro (vsp + sign_extend (m := 64) (0x0c8#12))",
   track=True, comment="mv a4,a0")
st(0x80006af4, "btaken", "site_80006af4_taken_pm", vals="(15#64) (8#64)",
   hyps="$p:x6 $p:x12 ($mE ▸ hms0) rfl (by decide)", nextpc=0x80006b28,
   pcrw="tgt", comment="bgeu t1,a2 TAKEN (15 ≥ 8)")
st(0x80006b28, "alu", "site_80006b28_pm", vals="(15#64) (8#64)",
   hyps="$p:x6 $p:x12 ($mE ▸ hms0) rfl", nextpc=0x80006b2c,
   rd="x13", rdval="(7#64)",
   rdrw=dshow("(15#64 : BitVec 64) - (8#64)", "7#64"),
   track=True, comment="sub a3,t1,a2")
st(0x80006b2c, "alu", "site_80006b2c_pm4", vals="(7#64)",
   hyps="$p:x13 ($mE ▸ hms0) rfl", nextpc=0x80006b30,
   rd="x13", rdval="(28#64)",
   rdrw=dshow("shift_bits_left (7#64 : BitVec 64) (Sail.BitVec.extractLsb (0x02#6) 5 0)",
              "28#64"),
   track=True, comment="slli a3,a3,0x2")
st(0x80006b30, "alu", "site_80006b30_pm4", hyps="($mE ▸ hms0) rfl", nextpc=0x80006b34,
   rd="x5", rdval="(0x80006b30#64)",
   rdrw=dshow("(0x80006b30#64 : BitVec 64) + sign_extend (m := 64)"
              " ((0x00000#20) +++ 0x000#12)", "0x80006b30#64"),
   track=True, comment="auipc t0,0x0")
st(0x80006b34, "alu", "site_80006b34_pm", vals="(28#64) (0x80006b30#64)",
   hyps="$p:x13 $p:x5 ($mE ▸ hms0) rfl", nextpc=0x80006b38,
   rd="x13", rdval="(0x80006b4c#64)",
   rdrw=dshow("(28#64 : BitVec 64) + (0x80006b30#64)", "0x80006b4c#64"),
   track=True, comment="add a3,a3,t0")
st(0x80006b38, "jr", "site_80006b38_pm4", vals="(0x80006b4c#64)",
   hyps="$p:x13 ($mE ▸ hms0) rfl (by rw [hjr]; decide)",
   nextpc=0x80006b58, pcrw=("jrshow", "hjr"),
   pre=["have hjr : BitVec.update ((0x80006b4c#64 : BitVec 64)"
        " + sign_extend (m := 64) (0x00c#12)) 0 0#1 = (0x80006b58#64 : BitVec 64) := by"
        " apply BitVec.eq_of_toNat_eq; decide"],
   comment="jr 12(a3) → sb chain entry for n = 8")

# the eight sb's: sb a1,J(a4) for J = 7..0
sb_sites = [(0x80006b58, 7), (0x80006b5c, 6), (0x80006b60, 5), (0x80006b64, 4),
            (0x80006b68, 3), (0x80006b6c, 2), (0x80006b70, 1), (0x80006b74, 0)]
prev_ms = "($mE ▸ hms0)"
for i, (addr, J) in enumerate(sb_sites):
    k = S.k + 1
    st(addr, "store", f"site_{addr:08x}_pm", vals="(vsp + sign_extend (m := 64) (0x0c8#12)) _",
       hyps=f"$p:x14 $p:x11 {prev_ms} rfl (by rw [hoffsb{J}]; omega)"
            f" (by rw [hoffsb{J}]; omega) (by rw [hoffsb{J}, htoh]; omega)",
       nextpc=addr + 4,
       memw=("ins", f"vsp.toNat + {200 + J}", "stData 1 (0#64)", [f"hoffsb{J}"]))
    S.emit(f"  have hmsA{k} : Vsa.Sim.Code.MemsetLoaded σ{k}.mem := by",
           f"    rw [hmem{k}, mem_afterNextPC]",
           f"    exact memset_insert_pro _ _ _ (by rw [hoffsb{J}]; omega) " +
           (f"hmsA{k-1}" if i > 0 else f"(hmE{k-1} ▸ hms0)"),
           "")
    prev_ms = f"hmsA{k}"

st(0x80006b78, "jr", "site_80006b78_pm", vals="(0x800076a4#64)",
   hyps=f"$p:x1 {prev_ms} rfl (by rw [ret_tgt _ (by decide)]; decide)",
   nextpc=0x800076a4, pcrw="ret", comment="ret (memset done)")

# back in svfprintf: derive svf-loaded + above-frame agreement at σ17
S.emit("""  have hslA : Vsa.Sim.Code.SvfprintfSliceLoaded σ18.mem := by
    rw [hmE18]
    exact svfprintfSlice_insert_sn4 _ _ _ (by omega) (svfprintfSlice_insert_sn4 _ _ _
      (by omega) (svfprintfSlice_insert_sn4 _ _ _ (by omega)
      (svfprintfSlice_insert_sn4 _ _ _ (by omega) (svfprintfSlice_insert_sn4 _ _ _
      (by omega) (svfprintfSlice_insert_sn4 _ _ _ (by omega)
      (svfprintfSlice_insert_sn4 _ _ _ (by omega) (svfprintfSlice_insert_sn4 _ _ _
      (by omega) hsl0)))))))
  have hagA : ∀ a : Nat, vsp.toNat + 592 ≤ a → σ18.mem[a]? = c.σ.mem[a]? := by
    intro a ha
    rw [hmE18,
      getElem_insert_ne _ a (vsp.toNat + 200) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 201) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 202) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 203) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 204) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 205) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 206) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 207) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)]
""")

st(0x800076a4, "alu", "site_800076a4_pr4", vals="vfile _ _",
   hyps="$p:x9 hslA rfl (by rw [hoafl]; omega) (by rw [hoafl]; omega)"
        " (by rw [hoafl, htoh]; omega) (by rw [hoafl]; omega)"
        " (by rw [hoafl]; exact (hagA _ (by omega)).trans hfl0B)"
        " (by rw [hoafl]; exact (hagA _ (by omega)).trans hfl1B)",
   nextpc=0x800076a8,
   rd="x15", rdval="zero_extend (m := 64) ((fl1.append fl0) : BitVec (8 * 2))",
   track=True, comment="lhu a5,16(s1) — FILE _flags")
st(0x800076a8, "alu", "site_800076a8_pr4",
   vals="(zero_extend (m := 64) ((fl1.append fl0) : BitVec (8 * 2)))",
   hyps="$p:x15 (hmem19 ▸ hslA) rfl", nextpc=0x800076ac,
   rd="x15", rdval="(0#64)", rdrw="hflagB", track=True,
   comment="andi a5,a5,128 — __SCLE clear")
st(0x800076ac, "btaken", "site_800076ac_taken_pr", vals="(0#64)",
   hyps="$p:x15 ((hmem20.trans hmem19) ▸ hslA) rfl (by decide)", nextpc=0x800076bc,
   pcrw="tgt", comment="beqz a5 TAKEN → 0x800076bc")

N = S.k
assert N == 21, N

post = [f"""  have hslN : Vsa.Sim.Code.SvfprintfSliceLoaded σ{N}.mem :=
    (hmem21.trans (hmem20.trans hmem19)) ▸ hslA
  have hmsN : Vsa.Sim.Code.MemsetLoaded σ{N}.mem := by
    rw [hmem21, hmem20, hmem19, hmem18]; exact hmsA17
  have hlmN : Vsa.Sim.Code.__locale_mb_cur_maxLoaded σ{N}.mem := by
    rw [hmE{N}]
    exact localemb_insert_pro _ _ _ (by omega) (localemb_insert_pro _ _ _ (by omega)
      (localemb_insert_pro _ _ _ (by omega) (localemb_insert_pro _ _ _ (by omega)
      (localemb_insert_pro _ _ _ (by omega) (localemb_insert_pro _ _ _ (by omega)
      (localemb_insert_pro _ _ _ (by omega) (localemb_insert_pro _ _ _ (by omega)
        hlm0)))))))
  have hambN : Vsa.Sim.Code.__ascii_mbtowcLoaded σ{N}.mem := by
    rw [hmE{N}]
    exact amb_insert_pro _ _ _ (by omega) (amb_insert_pro _ _ _ (by omega)
      (amb_insert_pro _ _ _ (by omega) (amb_insert_pro _ _ _ (by omega)
      (amb_insert_pro _ _ _ (by omega) (amb_insert_pro _ _ _ (by omega)
      (amb_insert_pro _ _ _ (by omega) (amb_insert_pro _ _ _ (by omega)
        hamb0)))))))"""]

# the eight mbstate zero bytes at sp+200..207
zb = ["""  have hz200 : σ21.mem[vsp.toNat + 200]? = some (0x00#8) := by
    rw [hmE21, getElem_insert_self]
    rfl"""]
for J in range(1, 8):
    peels = "\n".join(
        f"      getElem_insert_ne _ (vsp.toNat + {200 + J}) (vsp.toNat + {200 + i}) _"
        f" (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)," for i in range(0, J))
    zb.append(f"""  have hz{200 + J} : σ21.mem[vsp.toNat + {200 + J}]? = some (0x00#8) := by
    rw [hmE21,
{peels}
      getElem_insert_self]
    rfl""")
post.extend(zb)

post.append(f"""  have hagN : ∀ a : Nat, ¬(vsp.toNat + 200 ≤ a ∧ a < vsp.toNat + 208) →
      σ{N}.mem[a]? = c.σ.mem[a]? := by
    intro a hw0
    rw [hmE{N},
      getElem_insert_ne _ a (vsp.toNat + 200) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 201) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 202) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 203) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 204) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 205) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 206) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 207) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)]""")

refine_items = [
    f"hG{N}", f"hpc{N}",
    "$p:x2", "$p:x1", "$p:x3", "$p:x8", "$p:x9", "$p:x22",
    "$p:x18", "$p:x19", "$p:x20", "$p:x21", "$p:x23",
    "$p:x24", "$p:x25", "$p:x26", "$p:x27",
    "hz200", "hz201", "hz202", "hz203", "hz204", "hz205", "hz206", "hz207",
    "hagN", "hslN", "hmsN", "hlmN", "hambN",
    f"hi{N}", f"⟨vmi{N}, hmi{N}⟩",
]

core = "\n".join(S.out + post) + "\n"
tail_items = ",\n    ".join(S.subst(x, f"hp{N}", f"hmE{N}", N) for x in refine_items)
core += f"  refine ⟨⟨σ{N}, i{N}, c.steps + {N}⟩, ?_,\n    {tail_items}⟩\n"
chain = f"(Steps.single hstep{N})"
for j in range(N - 1, 0, -1):
    chain = f"((Steps.single hstep{j}).trans {chain})"
core += "  exact " + chain[1:-1] + "\n"

stmt = """/-- **Segment C of the svfprintf prologue**: `0x800076a0 → 0x800076bc`.

The `jal memset` with the whole concrete `memset(sp+200, 0, 8)` execution
inlined (small-size dispatch `bgeu 15,8` taken, computed `jr` into the sb
chain, eight byte stores, `ret`), then the FILE `_flags` check: `lhu
a5,16(s1)`, `andi a5,a5,128` (the `__SCLE` bit is clear for the string-sink
FILE, caller fact `hflagB`), `beqz` taken to the second spill block. -/
theorem svfProC_spec
    (vsp va0 vfile vfmt : BitVec 64)
    (vS2o vS3o vS4o vS5o vS7o vS8o vS9o vS10o vS11o : BitVec 64)
    (fl0 fl1 : BitVec 8)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : Vsa.Sim.Code.SvfprintfSliceLoaded c.σ.mem)
    (hms0 : Vsa.Sim.Code.MemsetLoaded c.σ.mem)
    (hlm0 : Vsa.Sim.Code.__locale_mb_cur_maxLoaded c.σ.mem)
    (hamb0 : Vsa.Sim.Code.__ascii_mbtowcLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x800076a0#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx8 : c.σ.regs.get? Register.x8 = some va0)
    (hx9 : c.σ.regs.get? Register.x9 = some vfile)
    (hx22 : c.σ.regs.get? Register.x22 = some vfmt)
    (hx10 : c.σ.regs.get? Register.x10 = some (vsp + sign_extend (m := 64) (0x0c8#12)))
    (hx11 : c.σ.regs.get? Register.x11 = some (0#64))
    (hx12 : c.σ.regs.get? Register.x12 = some (8#64))
    (hx18 : c.σ.regs.get? Register.x18 = some vS2o)
    (hx19 : c.σ.regs.get? Register.x19 = some vS3o)
    (hx20 : c.σ.regs.get? Register.x20 = some vS4o)
    (hx21 : c.σ.regs.get? Register.x21 = some vS5o)
    (hx23 : c.σ.regs.get? Register.x23 = some vS7o)
    (hx24 : c.σ.regs.get? Register.x24 = some vS8o)
    (hx25 : c.σ.regs.get? Register.x25 = some vS9o)
    (hx26 : c.σ.regs.get? Register.x26 = some vS10o)
    (hx27 : c.σ.regs.get? Register.x27 = some vS11o)
    -- the FILE `_flags` halfword (bit 7, `__SCLE`, clear)
    (hfl0B : c.σ.mem[vfile.toNat + 16]? = some fl0)
    (hfl1B : c.σ.mem[vfile.toNat + 17]? = some fl1)
    (hflagB : (zero_extend (m := 64) ((fl1.append fl0) : BitVec (8 * 2)) : BitVec 64)
        &&& sign_extend (m := 64) (0x080#12) = 0#64)
    (hfilelo : vsp.toNat + 592 ≤ vfile.toNat)
    (hfilehi : vfile.toNat + 24 ≤ 0x100000000)
    (hfileal : vfile.toNat % 8 = 0)
    (hsplo : 0x8001c000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x800076bc#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x1 = some (0x800076a4#64) ∧
      c'.σ.regs.get? Register.x3 = some (0x8001b510#64) ∧
      c'.σ.regs.get? Register.x8 = some va0 ∧
      c'.σ.regs.get? Register.x9 = some vfile ∧
      c'.σ.regs.get? Register.x22 = some vfmt ∧
      c'.σ.regs.get? Register.x18 = some vS2o ∧
      c'.σ.regs.get? Register.x19 = some vS3o ∧
      c'.σ.regs.get? Register.x20 = some vS4o ∧
      c'.σ.regs.get? Register.x21 = some vS5o ∧
      c'.σ.regs.get? Register.x23 = some vS7o ∧
      c'.σ.regs.get? Register.x24 = some vS8o ∧
      c'.σ.regs.get? Register.x25 = some vS9o ∧
      c'.σ.regs.get? Register.x26 = some vS10o ∧
      c'.σ.regs.get? Register.x27 = some vS11o ∧
      c'.σ.mem[vsp.toNat + 200]? = some (0x00#8) ∧
      c'.σ.mem[vsp.toNat + 201]? = some (0x00#8) ∧
      c'.σ.mem[vsp.toNat + 202]? = some (0x00#8) ∧
      c'.σ.mem[vsp.toNat + 203]? = some (0x00#8) ∧
      c'.σ.mem[vsp.toNat + 204]? = some (0x00#8) ∧
      c'.σ.mem[vsp.toNat + 205]? = some (0x00#8) ∧
      c'.σ.mem[vsp.toNat + 206]? = some (0x00#8) ∧
      c'.σ.mem[vsp.toNat + 207]? = some (0x00#8) ∧
      (∀ a : Nat, ¬(vsp.toNat + 200 ≤ a ∧ a < vsp.toNat + 208) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      Vsa.Sim.Code.SvfprintfSliceLoaded c'.σ.mem ∧
      Vsa.Sim.Code.MemsetLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__locale_mb_cur_maxLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__ascii_mbtowcLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hoffc8 : (vsp + sign_extend (m := 64) (0x0c8#12)).toNat = vsp.toNat + 200 :=
    ptr_addoff vsp _ 200 (by decide) (by omega)
"""

for J in range(8):
    stmt += (f"  have hoffsb{J} : ((vsp + sign_extend (m := 64) (0x0c8#12))"
             f" + sign_extend (m := 64) (0x00{J}#12)).toNat = vsp.toNat + {200 + J} := by\n"
             f"    rw [ptr_addoff _ _ {J} (by decide) (by rw [hoffc8]; omega), hoffc8]\n")
stmt += ("  have hoafl : (vfile + sign_extend (m := 64) (0x010#12)).toNat"
         " = vfile.toNat + 16 := ptr_addoff vfile _ 16 (by decide) (by omega)\n")

pins_list = ", ".join(f"⟨Register.{r}, {v}⟩" for r, v in pins)
pins_hyps = ", ".join(f"hx{r[1:]}" for r, _ in pins)
hp0 = (f"  have hp0 : PinsHold c.σ [{pins_list}] :=\n"
       f"    ⟨{pins_hyps}, trivial⟩\n")

hdr = """import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.SnprintfSitesPro3
import Vsa.Sim.SnprintfSitesPro4

/-!
# M3 Layer-3 — `SnprintfSpec29` : svfprintf prologue segment C
## `0x800076a0` (the `jal memset`) → `0x800076bc` (second spill block)

`memset(sp+200, 0, 8)` (mbstate init) fully inlined — small-size `bgeu`
dispatch, computed `jr 12(a3)` into the byte-store chain, 8 × `sb`, `ret` —
then the FILE `_flags` `lhu`/`andi 128`/`beqz`-taken check (the `__SCLE`
bit is clear for the `_svsnprintf_r` string sink).
Generated in the SnprintfSpec22 house style by /tmp/gen_spec29.py.
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

out = hdr + stmt + hp0 + core + "\nend Vsa.Sim\n"
open("Vsa/Sim/SnprintfSpec29.lean", "w").write(out)
print("wrote Vsa/Sim/SnprintfSpec29.lean", len(out.splitlines()), "lines")
