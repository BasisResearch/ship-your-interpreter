#!/usr/bin/env python3
import sys
sys.path.insert(0, "/tmp")
from emit_pro_seg import Seg

pins = [
    ("x2", "vsp"), ("x3", "(0x8001b510#64)"), ("x8", "va0"),
    ("x9", "(0x8001b798#64)"), ("x22", "vfmt"), ("x10", "(1#64)"),
    ("x12", "vfmt"), ("x18", "(16#64)"), ("x19", "(37#64)"),
    ("x21", "vsp + sign_extend (m := 64) (0x160#12)"),
    ("x23", "vsp + sign_extend (m := 64) (0x160#12)"),
    ("x24", "vS8o"), ("x25", "vS9o"), ("x26", "vS10o"), ("x27", "vS11o"),
    ("x20", "(0x80012268#64)"),
]
S = Seg(pins)


def track_sl(k, hoff=None, kind="w8"):
    P = k - 1
    prev = f"hsl{P}" if P > 0 else "hsl0"
    if hoff is None:
        S.emit(f"  have hsl{k} : Vsa.Sim.Code.SvfprintfSliceLoaded σ{k}.mem := by"
               f" rw [hmem{k}]; exact {prev}")
    else:
        fn = ("svfprintfSlice_writeMap8_sn5" if kind == "w8"
              else "svfprintfSlice_insert_sn4")
        S.emit(f"  have hsl{k} : Vsa.Sim.Code.SvfprintfSliceLoaded σ{k}.mem := by",
               f"    rw [hmem{k}, mem_afterNextPC]",
               f"    exact {fn} _ _ _ (by rw [{hoff}]; omega) {prev}")


def st(*a, **kw):
    hoff = kw.pop("track_hoff", None)
    kind = kw.pop("track_kind", "w8")
    S.step(*a, **kw)
    S.out.pop()
    track_sl(S.k, hoff, kind)
    S.emit("")


def dshow(lhs, rhs):
    return f"show {lhs} = ({rhs} : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide"


st(0x8000775c, "alu", "site_8000775c_pr", vals="vsp _ _ _ _ _ _ _ _",
   pre=["obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ :="
        " slot_reload_bytes vsp 0x000 vfmt c.σ.mem hS000"],
   hyps="$p:x2 hsl0 rfl (by rw [hoff0]; omega) (by rw [hoff0]; omega)"
        " (Or.inr (by rw [hoff0, htoh]; omega)) (by rw [hoff0]; omega)"
        " hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7",
   nextpc=0x80007760, rd="x15", rdval="vfmt", rdrw="slot_reassemble vfmt",
   track=True, comment="ld a5,0(sp) — the fmt slot (still = vfmt)")
st(0x80007760, "alu", "site_80007760_pr", vals="(1#64)", hyps="$p:x10 $L rfl",
   nextpc=0x80007764, rd="x20", rdrw="raw", comment="mv s4,a0 (dead)")
st(0x80007764, "alu", "site_80007764_pr", vals="vfmt vfmt",
   hyps="$p:x22 $p:x15 $L rfl", nextpc=0x80007768,
   rd="x24", rdval="(0#64)", rdrw="subw_self_pro vfmt",
   track=True, comment="subw s8,s6,a5 = 0 (same value both sides)")
st(0x80007768, "bnottaken", "site_80007768_nottaken_pr", vals="(0#64)",
   hyps="$p:x24 $L rfl (by decide)", nextpc=0x8000776c,
   comment="bnez s8 NOT taken")
st(0x8000776c, "alu", "site_8000776c_pr", vals="vfmt", hyps="$p:x22 $L rfl",
   nextpc=0x80007770, rd="x15", rdval="vfmt + sign_extend (m := 64) (0x001#12)",
   track=True, comment="addi a5,s6,1 — cursor past the '%'")
st(0x80007770, "alu", "site_80007770_pr", vals="vfmt _",
   hyps="$p:x22 $L rfl (by rw [hofff1]; omega) (by rw [hofff1]; omega)"
        " (by rw [hofff1]; exact hfhtif1) (by rw [hofff1, $mE]; exact hlB)",
   nextpc=0x80007774, rd="x24", rdval="(0x6c#64)",
   rdrw=dshow("(zero_extend (m := 64) (0x6c#8) : BitVec 64)", "0x6c#64"),
   track=True, comment="lbu s8,1(s6) — format[1] = 'l'")
st(0x80007774, "store", "site_80007774_pr", vals="vsp",
   hyps="$p:x2 $L rfl (by rw [hoff167]; omega) (by rw [hoff167]; omega)"
        " (by rw [hoff167, htoh]; omega)",
   nextpc=0x80007778,
   memw=("ins", "vsp.toNat + 167", "stData 1 (0#64)", ["hoff167"]),
   track_hoff="hoff167", track_kind="ins",
   comment="sb zero,167(sp) — the sign-byte slot")
st(0x80007778, "store", "site_80007778_pr", vals="vsp _",
   hyps="$p:x2 $p:x15 $L rfl (by rw [hoff0]; omega) (by rw [hoff0]; omega)"
        " (by rw [hoff0, htoh]; omega) (by rw [hoff0]; omega)",
   nextpc=0x8000777c,
   memw=("w8", "vsp.toNat", "sdData_val (vfmt + sign_extend (m := 64) (0x001#12))",
         ["hoff0"]),
   track_hoff="hoff0",
   comment="sd a5,0(sp) — cursor slot := vfmt+1")
st(0x8000777c, "alu", "site_8000777c_pr", hyps="$L rfl", nextpc=0x80007780,
   rd="x20", rdval="(0xffffffffffffffff#64)",
   rdrw=dshow("((0#64) : BitVec 64) + sign_extend (m := 64) (0xfff#12)",
              "0xffffffffffffffff#64"),
   track=True, comment="li s4,-1 — default precision")
st(0x80007780, "alu", "site_80007780_pr", hyps="$L rfl", nextpc=0x80007784,
   rd="x6", rdval="(0#64)", rdrw="sext0_add_pro (0#64)",
   track=True, comment="li t1,0 — the flag word")
st(0x80007784, "alu", "site_80007784_pr", hyps="$L rfl", nextpc=0x80007788,
   rd="x26", rdval="(90#64)",
   rdrw=dshow("((0#64) : BitVec 64) + sign_extend (m := 64) (0x05a#12)", "90#64"),
   track=True, comment="li s10,90 — dispatch bound")
st(0x80007788, "alu", "site_80007788_pr4", hyps="$L rfl", nextpc=0x8000778c,
   rd="x22", rdval="(0x8001a788#64)",
   rdrw=dshow("(0x80007788#64 : BitVec 64) + sign_extend (m := 64)"
              " ((0x00013#20) +++ 0x000#12)", "0x8001a788#64"),
   track=True, comment="auipc s6,0x13")
st(0x8000778c, "alu", "site_8000778c_pr", vals="(0x8001a788#64)", hyps="$p:x22 $L rfl",
   nextpc=0x80007790, rd="x22", rdval="(0x8001a0fc#64)",
   rdrw=dshow("(0x8001a788#64 : BitVec 64) + sign_extend (m := 64) (0x974#12)",
              "0x8001a0fc#64"),
   track=True, comment="addi s6,s6,-1676 — parse jump-table base")
st(0x80007790, "alu", "site_80007790_pr", hyps="$L rfl", nextpc=0x80007794,
   rd="x27", rdval="(0#64)", rdrw="sext0_add_pro (0#64)",
   track=True, comment="li s11,0")
st(0x80007794, "alu", "site_80007794_pr", vals="(vfmt + sign_extend (m := 64) (0x001#12))",
   hyps="$p:x15 $L rfl", nextpc=0x80007798,
   rd="x25", rdval="vfmt + sign_extend (m := 64) (0x001#12)",
   rdrw="sext0_add_pro (vfmt + sign_extend (m := 64) (0x001#12))",
   track=True, comment="mv s9,a5")

N = S.k
assert N == 15, N

post = [f"""  have hz167 : σ{N}.mem[vsp.toNat + 167]? = some (0x00#8) := by
    rw [hmE{N}, getElem?_writeMap8_out _ (vsp.toNat) _ _ (by omega),
      getElem_insert_self]
    rfl
  have hS000N : SlotHolds vsp 0x000 (vfmt + sign_extend (m := 64) (0x001#12))
      σ{N}.mem := by
    rw [hmE{N}]
    exact slot_save vsp 0x000 (vfmt + sign_extend (m := 64) (0x001#12)) _ _ _ hoff0 rfl
  have hagN : ∀ a : Nat, ¬(vsp.toNat + 167 ≤ a ∧ a < vsp.toNat + 168) →
      ¬(vsp.toNat ≤ a ∧ a < vsp.toNat + 8) →
      σ{N}.mem[a]? = c.σ.mem[a]? := by
    intro a hw0 hw1
    rw [hmE{N},
      getElem?_writeMap8_out _ (vsp.toNat) _ a (by omega),
      getElem_insert_ne _ a (vsp.toNat + 167) _
        (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)]"""]

refine_items = [
    f"hG{N}", f"hpc{N}",
    "$p:x2", "$p:x3", "$p:x8", "$p:x9",
    "$p:x22", "$p:x24", "$p:x25", "$p:x26", "$p:x20", "$p:x6", "$p:x27",
    "$p:x10", "$p:x12", "$p:x18", "$p:x19", "$p:x21", "$p:x23",
    "hz167", "hS000N", "hagN", f"hsl{N}",
    f"hi{N}", f"⟨vmi{N}, hmi{N}⟩",
]

core = "\n".join(S.out + post) + "\n"
tail_items = ",\n    ".join(S.subst(x, f"hp{N}", f"hmE{N}", N) for x in refine_items)
core += f"  refine ⟨⟨σ{N}, i{N}, c.steps + {N}⟩, ?_,\n    {tail_items}⟩\n"
chain = f"(Steps.single hstep{N})"
for j in range(N - 1, 0, -1):
    chain = f"((Steps.single hstep{j}).trans {chain})"
core += "  exact " + chain[1:-1] + "\n"

stmt = """/-- **Segment G of the svfprintf prologue**: `0x8000775c → 0x80007798`.

The `%`-directive entry: cursor reload from the fmt slot, `subw s8,s6,a5 = 0`
(no literal text before the `%`), cursor bump + `lbu` of `format[1] = 'l'`,
the sign-byte slot zeroed at `sp+167`, the cursor slot updated to `vfmt+1`,
and the parse-loop register block: `s4 := -1` (default precision),
`t1 := 0` (flags), `s10 := 90`, `s6 := 0x8001a0fc` (parse jump-table base,
`auipc`/`addi`), `s11 := 0`, `s9 := vfmt+1`. -/
theorem svfProG_spec
    (vsp va0 vfmt : BitVec 64)
    (vS8o vS9o vS10o vS11o : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : Vsa.Sim.Code.SvfprintfSliceLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x8000775c#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx8 : c.σ.regs.get? Register.x8 = some va0)
    (hx9 : c.σ.regs.get? Register.x9 = some (0x8001b798#64))
    (hx22 : c.σ.regs.get? Register.x22 = some vfmt)
    (hx10 : c.σ.regs.get? Register.x10 = some (1#64))
    (hx12 : c.σ.regs.get? Register.x12 = some vfmt)
    (hx18 : c.σ.regs.get? Register.x18 = some (16#64))
    (hx19 : c.σ.regs.get? Register.x19 = some (37#64))
    (hx21 : c.σ.regs.get? Register.x21 = some (vsp + sign_extend (m := 64) (0x160#12)))
    (hx23 : c.σ.regs.get? Register.x23 = some (vsp + sign_extend (m := 64) (0x160#12)))
    (hx24 : c.σ.regs.get? Register.x24 = some vS8o)
    (hx25 : c.σ.regs.get? Register.x25 = some vS9o)
    (hx26 : c.σ.regs.get? Register.x26 = some vS10o)
    (hx27 : c.σ.regs.get? Register.x27 = some vS11o)
    (hx20 : c.σ.regs.get? Register.x20 = some (0x80012268#64))
    -- the fmt slot still holds vfmt, and format[1] = 'l'
    (hS000 : SlotHolds vsp 0x000 vfmt c.σ.mem)
    (hlB : c.σ.mem[vfmt.toNat + 1]? = some (0x6c#8))
    (hflo : 0x80000000 ≤ vfmt.toNat)
    (hfhi : vfmt.toNat + 8 ≤ 0x100000000)
    (hfhtif1 : vfmt.toNat + 2 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vfmt.toNat + 1)
    (hsplo : 0x8001c000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x80007798#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x3 = some (0x8001b510#64) ∧
      c'.σ.regs.get? Register.x8 = some va0 ∧
      c'.σ.regs.get? Register.x9 = some (0x8001b798#64) ∧
      c'.σ.regs.get? Register.x22 = some (0x8001a0fc#64) ∧
      c'.σ.regs.get? Register.x24 = some (0x6c#64) ∧
      c'.σ.regs.get? Register.x25 = some (vfmt + sign_extend (m := 64) (0x001#12)) ∧
      c'.σ.regs.get? Register.x26 = some (90#64) ∧
      c'.σ.regs.get? Register.x20 = some (0xffffffffffffffff#64) ∧
      c'.σ.regs.get? Register.x6 = some (0#64) ∧
      c'.σ.regs.get? Register.x27 = some (0#64) ∧
      c'.σ.regs.get? Register.x10 = some (1#64) ∧
      c'.σ.regs.get? Register.x12 = some vfmt ∧
      c'.σ.regs.get? Register.x18 = some (16#64) ∧
      c'.σ.regs.get? Register.x19 = some (37#64) ∧
      c'.σ.regs.get? Register.x21 = some (vsp + sign_extend (m := 64) (0x160#12)) ∧
      c'.σ.regs.get? Register.x23 = some (vsp + sign_extend (m := 64) (0x160#12)) ∧
      c'.σ.mem[vsp.toNat + 167]? = some (0x00#8) ∧
      SlotHolds vsp 0x000 (vfmt + sign_extend (m := 64) (0x001#12)) c'.σ.mem ∧
      (∀ a : Nat, ¬(vsp.toNat + 167 ≤ a ∧ a < vsp.toNat + 168) →
      ¬(vsp.toNat ≤ a ∧ a < vsp.toNat + 8) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      Vsa.Sim.Code.SvfprintfSliceLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hoff0 : (vsp + sign_extend (m := 64) (0x000#12)).toNat = vsp.toNat := by
    rw [sext0_add_pro]
  have hofff1 : (vfmt + sign_extend (m := 64) (0x001#12)).toNat = vfmt.toNat + 1 :=
    ptr_addoff vfmt _ 1 (by decide) (by omega)
  have hoff167 : (vsp + sign_extend (m := 64) (0x0a7#12)).toNat = vsp.toNat + 167 :=
    ptr_addoff vsp _ 167 (by decide) (by omega)
"""

pins_list = ", ".join(f"⟨Register.{r}, {v}⟩" for r, v in pins)
pins_hyps = ", ".join(f"hx{r[1:]}" for r, _ in pins)
hp0 = (f"  have hp0 : PinsHold c.σ [{pins_list}] :=\n"
       f"    ⟨{pins_hyps}, trivial⟩\n")

hdr = """import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.SnprintfSitesPro4

/-!
# M3 Layer-3 — `SnprintfSpec33` : svfprintf prologue segment G
## `0x8000775c → 0x80007798` — the `%`-directive entry + parse-state init

Establishes exactly the register block the `%lld` dispatch consumes: flags
`t1 = 0`, width `s4 = -1`, bound `s10 = 90`, table base `s6 = 0x8001a0fc`,
`s11 = 0`, cursor `s9 = vfmt+1` with `s8 = 'l'`; the sign-byte slot at
`sp+167` zeroed; the cursor slot at `sp+0` bumped to `vfmt+1`.
Generated in the SnprintfSpec22 house style by /tmp/gen_spec33.py.
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
open("Vsa/Sim/SnprintfSpec33.lean", "w").write(out)
print("wrote Vsa/Sim/SnprintfSpec33.lean", len(out.splitlines()), "lines")
