#!/usr/bin/env python3
import sys
sys.path.insert(0, "/tmp")
from emit_pro_seg import Seg

pins = [
    ("x2", "vsp"), ("x3", "(0x8001b510#64)"), ("x8", "va0"),
    ("x9", "(0x8001b798#64)"), ("x22", "vfmt"), ("x20", "(0x80012268#64)"),
    ("x18", "(16#64)"), ("x19", "(37#64)"),
    ("x21", "vsp + sign_extend (m := 64) (0x160#12)"),
    ("x23", "vsp + sign_extend (m := 64) (0x160#12)"),
    ("x24", "vS8o"), ("x25", "vS9o"), ("x26", "vS10o"), ("x27", "vS11o"),
]
S = Seg(pins)


def st(*a, **kw):
    S.step(*a, **kw)


def dshow(lhs, rhs):
    return f"show {lhs} = ({rhs} : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide"


st(0x80007728, "jal", "site_80007728_rt", hyps="hsl0 rfl", nextpc=0x80010234, pcrw="jal",
   rd="x1", rdval="(0x8000772c#64)",
   rdrw="show BitVec.addInt (0x80007728#64) 4 = (0x8000772c#64 : BitVec 64) from by"
        " apply BitVec.eq_of_toNat_eq; decide",
   track=True, comment="jal __locale_mb_cur_max")
st(0x80010234, "alu", "site_80010234_rt3", vals="(0x8001b510#64) (0x01#8)",
   hyps="$p:x3 ($mE ▸ hlm0) rfl (by rw [hoffgp]; omega) (by rw [hoffgp]; omega)"
        " (Or.inr (by rw [hoffgp, htoh]; omega)) (by rw [hoffgp, $mE]; exact hmbB)",
   nextpc=0x80010238, rd="x10", rdval="(1#64)",
   rdrw=dshow("(zero_extend (m := 64) (0x01#8) : BitVec 64)", "1#64"),
   track=True, comment="lbu a0,1000(gp) — __mb_cur_max = 1")
st(0x80010238, "jr", "site_80010238_rt3", vals="(0x8000772c#64)",
   hyps="$p:x1 ($mE ▸ hlm0) rfl (by rw [ret_tgt _ (by decide)]; decide)",
   nextpc=0x8000772c, pcrw="ret", comment="ret")
st(0x8000772c, "alu", "site_8000772c_rt", vals="(1#64)", hyps="$p:x10 ($mE ▸ hsl0) rfl",
   nextpc=0x80007730, rd="x13", rdval="(1#64)", rdrw="sext0_add_pro (1#64)",
   track=True, comment="mv a3,a0 — n := 1")
st(0x80007730, "alu", "site_80007730_rt", vals="vsp", hyps="$p:x2 ($mE ▸ hsl0) rfl",
   nextpc=0x80007734, comment="addi a4,sp,200 (mbstate; value untracked)")
st(0x80007734, "alu", "site_80007734_rt", vals="vfmt", hyps="$p:x22 ($mE ▸ hsl0) rfl",
   nextpc=0x80007738, rd="x12", rdval="vfmt", rdrw="sext0_add_pro vfmt",
   track=True, comment="mv a2,s6 — the fmt cursor")
st(0x80007738, "alu", "site_80007738_rt", vals="vsp", hyps="$p:x2 ($mE ▸ hsl0) rfl",
   nextpc=0x8000773c, rd="x11", rdval="vsp + sign_extend (m := 64) (0x0b4#12)",
   track=True, comment="addi a1,sp,180 — pwc")
st(0x8000773c, "alu", "site_8000773c_rt", vals="va0", hyps="$p:x8 ($mE ▸ hsl0) rfl",
   nextpc=0x80007740, rd="x10", rdval="va0", rdrw="sext0_add_pro va0",
   track=True, comment="mv a0,s0 — reent")
st(0x80007740, "jalr", "site_80007740_rt5", vals="(0x80012268#64)",
   hyps="$p:x20 ($mE ▸ hsl0) rfl (by rw [ret_tgt _ (by decide)]; decide)",
   nextpc=0x80012268, pcrw=("jalrshow", "ret_tgt _ (by decide)"),
   rd="x1", rdval="(0x80007744#64)",
   rdrw="show BitVec.addInt (0x80007740#64) 4 = (0x80007744#64 : BitVec 64) from by"
        " apply BitVec.eq_of_toNat_eq; decide",
   track=True, comment="jalr s4 — indirect call to __ascii_mbtowc")
st(0x80012268, "bnottaken", "site_80012268_nottaken_rt4", vals="_",
   pre=["have hgv$K : ((vsp + sign_extend (m := 64) (0x0b4#12)) == (0#64 : BitVec 64))"
        " = false := beq64_false_pro _ _ (by"
        " rw [ptr_addoff vsp _ 180 (by decide) (by omega)];"
        " simp only [BitVec.toNat_ofNat]; omega)"],
   hyps="$p:x11 ($mE ▸ hamb0) rfl hgv$K", nextpc=0x8001226c,
   comment="beqz a1 NOT taken (pwc = sp+180)")
st(0x8001226c, "bnottaken", "site_8001226c_nottaken_rt4", vals="vfmt",
   pre=["have hgv$K : (vfmt == (0#64 : BitVec 64)) = false :="
        " beq64_false_pro _ _ (by simp only [BitVec.toNat_ofNat]; omega)"],
   hyps="$p:x12 ($mE ▸ hamb0) rfl hgv$K", nextpc=0x80012270,
   comment="beqz a2 NOT taken (fmt ≠ 0)")
st(0x80012270, "bnottaken", "site_80012270_nottaken_rt4", vals="(1#64)",
   hyps="$p:x13 ($mE ▸ hamb0) rfl (by decide)", nextpc=0x80012274,
   comment="beqz a3 NOT taken (n = 1)")
st(0x80012274, "alu", "site_80012274_rt4", vals="vfmt (0x25#8)",
   hyps="$p:x12 ($mE ▸ hamb0) rfl (by rw [hoffcur]; omega) (by rw [hoffcur]; omega)"
        " (by rw [hoffcur]; exact hfhtif) (by rw [hoffcur, $mE]; exact hpctB)",
   nextpc=0x80012278, rd="x15", rdval="(0x25#64)",
   rdrw=dshow("(zero_extend (m := 64) (0x25#8) : BitVec 64)", "0x25#64"),
   track=True, comment="lbu a5,0(a2) — the '%'")
st(0x80012278, "store", "site_80012278_rt4", vals="_ (0x25#64)",
   hyps="$p:x11 $p:x15 ($mE ▸ hamb0) rfl (by rw [hoff180]; omega)"
        " (by rw [hoff180]; omega) (by rw [hoff180, htoh]; omega)"
        " (by rw [hoff180]; omega)",
   nextpc=0x8001227c,
   memw=("w4", "vsp.toNat + 180", "swData (0x25#64)", ["hoff180"]),
   comment="sw a5,0(a1) — *pwc := '%'")
S.emit("""  have hambA : Vsa.Sim.Code.__ascii_mbtowcLoaded σ14.mem := by
    rw [hmem14, mem_afterNextPC]
    exact amb_w4_pro _ _ _ (by rw [hoff180]; omega) (hmE13 ▸ hamb0)
""")
st(0x8001227c, "alu", "site_8001227c_rt4", vals="vfmt (0x25#8)",
   hyps="$p:x12 hambA rfl (by rw [hoffcur]; omega) (by rw [hoffcur]; omega)"
        " (by rw [hoffcur]; exact hfhtif)"
        " (by rw [hoffcur, $mE];"
        " exact (getElem?_writeMap4_out_pro _ (vsp.toNat + 180) _ vfmt.toNat"
        " (by omega)).trans hpctB)",
   nextpc=0x80012280, rd="x10", rdval="(0x25#64)",
   rdrw=dshow("(zero_extend (m := 64) (0x25#8) : BitVec 64)", "0x25#64"),
   track=True, comment="lbu a0,0(a2) — '%' again")
st(0x80012280, "alu", "site_80012280_rt5", vals="(0x25#64)",
   pre=["have hsnez : (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64)"
        " (0x25#64))) : BitVec 64) = 1#64 := by"
        " rw [show zopz0zI_u (0#64) (0x25#64) = true from by"
        " simp only [zopz0zI_u, Sail.BitVec.toNatInt, BitVec.toNat_ofNat]; decide]"
        " ; apply BitVec.eq_of_toNat_eq; decide"],
   hyps="$p:x10 (hmem15 ▸ hambA) rfl", nextpc=0x80012284,
   rd="x10", rdval="(1#64)", rdrw="hsnez",
   track=True, comment="snez a0,a0 → 1 (one byte consumed)")
st(0x80012284, "jr", "site_80012284_rt4", vals="(0x80007744#64)",
   hyps="$p:x1 ((hmem16.trans hmem15) ▸ hambA) rfl"
        " (by rw [ret_tgt _ (by decide)]; decide)",
   nextpc=0x80007744, pcrw="ret", comment="ret (back to svfprintf)")
S.emit("""  have hslB : Vsa.Sim.Code.SvfprintfSliceLoaded σ17.mem := by
    rw [hmE17]
    exact svf_w4_pro _ _ _ (by omega) hsl0
""")
st(0x80007744, "bnottaken", "site_80007744_nottaken_pr", vals="(1#64)",
   hyps="$p:x10 hslB rfl (by decide)", nextpc=0x80007748,
   comment="beqz a0 NOT taken (a0 = 1)")
st(0x80007748, "bnottaken", "site_80007748_nottaken_pr", vals="(1#64)",
   hyps="$p:x10 (hmem18 ▸ hslB) rfl hsigned", nextpc=0x8000774c,
   comment="bltz a0 NOT taken")
st(0x8000774c, "alu", "site_8000774c_pr", vals="vsp _ _ _ _",
   pre=["have hpinw := Pin4_writeMap4 (c.σ.mem) (vsp.toNat + 180) (swData (0x25#64))"],
   hyps="$p:x2 ((hmem19.trans hmem18) ▸ hslB) rfl (by rw [hoffb4]; omega)"
        " (by rw [hoffb4]; omega) (by rw [hoffb4, htoh]; omega) (by rw [hoffb4]; omega)"
        " (by rw [hoffb4, $mE]; exact hpinw.1)"
        " (by rw [hoffb4, $mE]; exact hpinw.2.1)"
        " (by rw [hoffb4, $mE]; exact hpinw.2.2.1)"
        " (by rw [hoffb4, $mE]; exact hpinw.2.2.2)",
   nextpc=0x80007750, rd="x15", rdval="(0x25#64)",
   rdrw="show (sign_extend (m := 64) (((((swData (0x25#64)).extractLsb' 24 8).append"
        " ((swData (0x25#64)).extractLsb' 16 8)).append ((swData (0x25#64)).extractLsb'"
        " 8 8)).append ((swData (0x25#64)).extractLsb' 0 8) : BitVec (8 * 4))"
        " : BitVec 64) = (0x25#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide",
   track=True, comment="lw a5,180(sp) — the wide char = '%'")
st(0x80007750, "btaken", "site_80007750_taken_pr", vals="(0x25#64) (37#64)",
   hyps="$p:x15 $p:x19 ((hmem20.trans (hmem19.trans hmem18)) ▸ hslB) rfl (by decide)",
   nextpc=0x8000775c, pcrw="tgt", comment="beq a5,s3 TAKEN ('%' seen)")

N = S.k
assert N == 21, N

post = [f"""  have hslN : Vsa.Sim.Code.SvfprintfSliceLoaded σ{N}.mem :=
    (hmem21.trans (hmem20.trans (hmem19.trans hmem18))) ▸ hslB
  have hambN : Vsa.Sim.Code.__ascii_mbtowcLoaded σ{N}.mem := by
    rw [hmE{N}]
    exact amb_w4_pro _ _ _ (by omega) hamb0
  have hlmN : Vsa.Sim.Code.__locale_mb_cur_maxLoaded σ{N}.mem := by
    rw [hmE{N}]
    exact localemb_w4_pro _ _ _ (by omega) hlm0
  have hP180 : Pin4 σ{N}.mem (vsp.toNat + 180) (swData (0x25#64)) := by
    rw [hmE{N}]
    exact Pin4_writeMap4 _ _ _
  have hagN : ∀ a : Nat, ¬(vsp.toNat + 180 ≤ a ∧ a < vsp.toNat + 184) →
      σ{N}.mem[a]? = c.σ.mem[a]? := by
    intro a hw0
    rw [hmE{N}, getElem?_writeMap4_out_pro _ (vsp.toNat + 180) _ a (by omega)]"""]

refine_items = [
    f"hG{N}", f"hpc{N}",
    "$p:x2", "$p:x1", "$p:x3", "$p:x8", "$p:x9", "$p:x22", "$p:x20",
    "$p:x10", "$p:x11", "$p:x12", "$p:x13",
    "$p:x18", "$p:x19", "$p:x21", "$p:x23",
    "$p:x24", "$p:x25", "$p:x26", "$p:x27",
    "hP180", "hagN", "hslN", "hlmN", "hambN",
    f"hi{N}", f"⟨vmi{N}, hmi{N}⟩",
]

core = "\n".join(S.out + post) + "\n"
tail_items = ",\n    ".join(S.subst(x, f"hp{N}", f"hmE{N}", N) for x in refine_items)
core += f"  refine ⟨⟨σ{N}, i{N}, c.steps + {N}⟩, ?_,\n    {tail_items}⟩\n"
chain = f"(Steps.single hstep{N})"
for j in range(N - 1, 0, -1):
    chain = f"((Steps.single hstep{j}).trans {chain})"
core += "  exact " + chain[1:-1] + "\n"

stmt = """/-- **Segment F of the svfprintf prologue**: `0x80007728 → 0x8000775c`.

The parse loop's first pass over `"%lld"`: `jal __locale_mb_cur_max` (callee
inlined, `a0 := 1`), the mbtowc argument setup, the **indirect `jalr s4` →
`__ascii_mbtowc`** reading the concrete `'%'` (`0x25`) at `vfmt` and storing
it as a wide char at `sp+180`, return `a0 = 1`, then `beqz`/`bltz` not taken,
`lw a5,180(sp)` reading the `'%'` back, and `beq a5,s3` **taken** into the
`%`-directive block at `0x8000775c`. -/
theorem svfProF_spec
    (vsp va0 vfmt : BitVec 64)
    (vS8o vS9o vS10o vS11o : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : Vsa.Sim.Code.SvfprintfSliceLoaded c.σ.mem)
    (hlm0 : Vsa.Sim.Code.__locale_mb_cur_maxLoaded c.σ.mem)
    (hamb0 : Vsa.Sim.Code.__ascii_mbtowcLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80007728#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx8 : c.σ.regs.get? Register.x8 = some va0)
    (hx9 : c.σ.regs.get? Register.x9 = some (0x8001b798#64))
    (hx22 : c.σ.regs.get? Register.x22 = some vfmt)
    (hx20 : c.σ.regs.get? Register.x20 = some (0x80012268#64))
    (hx18 : c.σ.regs.get? Register.x18 = some (16#64))
    (hx19 : c.σ.regs.get? Register.x19 = some (37#64))
    (hx21 : c.σ.regs.get? Register.x21 = some (vsp + sign_extend (m := 64) (0x160#12)))
    (hx23 : c.σ.regs.get? Register.x23 = some (vsp + sign_extend (m := 64) (0x160#12)))
    (hx24 : c.σ.regs.get? Register.x24 = some vS8o)
    (hx25 : c.σ.regs.get? Register.x25 = some vS9o)
    (hx26 : c.σ.regs.get? Register.x26 = some vS10o)
    (hx27 : c.σ.regs.get? Register.x27 = some vS11o)
    -- static locale data: __mb_cur_max byte
    (hmbB : c.σ.mem[(0x8001b8f8 : Nat)]? = some (0x01#8))
    -- the format string's first byte: '%'
    (hpctB : c.σ.mem[vfmt.toNat]? = some (0x25#8))
    (hflo : 0x80000000 ≤ vfmt.toNat)
    (hfhi : vfmt.toNat + 8 ≤ 0x100000000)
    (hfhtif : vfmt.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vfmt.toNat)
    (hfstk : vfmt.toNat + 8 ≤ vsp.toNat ∨ vsp.toNat + 592 ≤ vfmt.toNat)
    (hsplo : 0x8001c000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x8000775c#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x1 = some (0x80007744#64) ∧
      c'.σ.regs.get? Register.x3 = some (0x8001b510#64) ∧
      c'.σ.regs.get? Register.x8 = some va0 ∧
      c'.σ.regs.get? Register.x9 = some (0x8001b798#64) ∧
      c'.σ.regs.get? Register.x22 = some vfmt ∧
      c'.σ.regs.get? Register.x20 = some (0x80012268#64) ∧
      c'.σ.regs.get? Register.x10 = some (1#64) ∧
      c'.σ.regs.get? Register.x11 = some (vsp + sign_extend (m := 64) (0x0b4#12)) ∧
      c'.σ.regs.get? Register.x12 = some vfmt ∧
      c'.σ.regs.get? Register.x13 = some (1#64) ∧
      c'.σ.regs.get? Register.x18 = some (16#64) ∧
      c'.σ.regs.get? Register.x19 = some (37#64) ∧
      c'.σ.regs.get? Register.x21 = some (vsp + sign_extend (m := 64) (0x160#12)) ∧
      c'.σ.regs.get? Register.x23 = some (vsp + sign_extend (m := 64) (0x160#12)) ∧
      c'.σ.regs.get? Register.x24 = some vS8o ∧
      c'.σ.regs.get? Register.x25 = some vS9o ∧
      c'.σ.regs.get? Register.x26 = some vS10o ∧
      c'.σ.regs.get? Register.x27 = some vS11o ∧
      Pin4 c'.σ.mem (vsp.toNat + 180) (swData (0x25#64)) ∧
      (∀ a : Nat, ¬(vsp.toNat + 180 ≤ a ∧ a < vsp.toNat + 184) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      Vsa.Sim.Code.SvfprintfSliceLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__locale_mb_cur_maxLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__ascii_mbtowcLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hoffgp : ((0x8001b510#64 : BitVec 64) + sign_extend (m := 64) (0x3e8#12)).toNat
      = (0x8001b8f8 : Nat) := by decide
  have hoffcur : (vfmt + sign_extend (m := 64) (0x000#12)).toNat = vfmt.toNat := by
    rw [sext0_add_pro]
  have hoffb4 : (vsp + sign_extend (m := 64) (0x0b4#12)).toNat = vsp.toNat + 180 :=
    ptr_addoff vsp _ 180 (by decide) (by omega)
  have hoff180 : ((vsp + sign_extend (m := 64) (0x0b4#12))
      + sign_extend (m := 64) (0x000#12)).toNat = vsp.toNat + 180 := by
    rw [sext0_add_pro, hoffb4]
  have hsigned : zopz0zI_s (1#64) (0#64) = false := by
    simp only [zopz0zI_s]; decide
"""

pins_list = ", ".join(f"⟨Register.{r}, {v}⟩" for r, v in pins)
pins_hyps = ", ".join(f"hx{r[1:]}" for r, _ in pins)
hp0 = (f"  have hp0 : PinsHold c.σ [{pins_list}] :=\n"
       f"    ⟨{pins_hyps}, trivial⟩\n")

hdr = """import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.SnprintfSitesRet
import Vsa.Sim.SnprintfSitesRet3
import Vsa.Sim.SnprintfSitesRet4
import Vsa.Sim.SnprintfSitesRet5

/-!
# M3 Layer-3 — `SnprintfSpec32` : svfprintf prologue segment F
## `0x80007728 → 0x8000775c` — parse pass 1, the `'%'` recognition

Reuses the `SnprintfSitesRet*` batteries (the same instructions run on the
NUL exit path verified in `SnprintfSpec22`); here the mbtowc reads the
concrete `'%'` (`0x25`) — the first byte of the static `"%lld"` template —
returns 1, and the `beq a5,s3` dispatches into the `%`-directive block.
Generated in the SnprintfSpec22 house style by /tmp/gen_spec32.py.
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
open("Vsa/Sim/SnprintfSpec32.lean", "w").write(out)
print("wrote Vsa/Sim/SnprintfSpec32.lean", len(out.splitlines()), "lines")
