#!/usr/bin/env python3
import sys
sys.path.insert(0, "/tmp")
from emit_pro_seg import Seg

pins = [
    ("x2", "vsp"), ("x3", "(0x8001b510#64)"), ("x8", "va0"),
    ("x9", "(0x8001b798#64)"), ("x22", "(0x8001a0fc#64)"), ("x24", "(0x6c#64)"),
    ("x25", "vs9"), ("x26", "(90#64)"), ("x20", "(0xffffffffffffffff#64)"),
    ("x6", "(0#64)"), ("x27", "(0#64)"),
    ("x10", "(1#64)"), ("x12", "vfmt"), ("x18", "(16#64)"), ("x19", "(37#64)"),
    ("x21", "vsp + sign_extend (m := 64) (0x160#12)"),
    ("x23", "vsp + sign_extend (m := 64) (0x160#12)"),
]
S = Seg(pins)


def st(*a, **kw):
    S.step(*a, **kw)


def dshow(lhs, rhs):
    return f"show {lhs} = ({rhs} : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide"


st(0x80007798, "alu", "site_80007798_pr", vals="vs9", hyps="$p:x25 hsl0 rfl",
   nextpc=0x8000779c, rd="x25", rdval="vs9 + sign_extend (m := 64) (0x001#12)",
   track=True, comment="addi s9,s9,1 — cursor to format[2]")
st(0x8000779c, "alu", "site_8000779c_pr", vals="(0x6c#64)", hyps="$p:x24 ($mE ▸ hsl0) rfl",
   nextpc=0x800077a0, rd="x24", rdval="(0x6c#64)",
   rdrw=dshow("(sign_extend (m := 64) (Sail.BitVec.extractLsb ((0x6c#64 : BitVec 64)"
              " + sign_extend (m := 64) (0x000#12)) 31 0) : BitVec 64)", "0x6c#64"),
   track=True, comment="sext.w s8,s8 — still 'l'")
st(0x800077a0, "alu", "site_800077a0_pr", vals="(0x6c#64)", hyps="$p:x24 ($mE ▸ hsl0) rfl",
   nextpc=0x800077a4, rd="x15", rdval="(76#64)",
   rdrw=dshow("(sign_extend (m := 64) (Sail.BitVec.extractLsb ((0x6c#64 : BitVec 64)"
              " + sign_extend (m := 64) (0xfe0#12)) 31 0) : BitVec 64)", "76#64"),
   track=True, comment="addiw a5,s8,-32 — dispatch index 76")
st(0x800077a4, "bnottaken", "site_800077a4_nottaken_pr", vals="(90#64) (76#64)",
   pre=["have hbltu : zopz0zI_u (90#64) (76#64) = false := by"
        " simp only [zopz0zI_u, Sail.BitVec.toNatInt]; decide"],
   hyps="$p:x26 $p:x15 ($mE ▸ hsl0) rfl hbltu", nextpc=0x800077a8,
   comment="bltu s10,a5 NOT taken (76 ≤ 90)")
st(0x800077a8, "alu", "site_800077a8_pr4", vals="(76#64)", hyps="$p:x15 ($mE ▸ hsl0) rfl",
   nextpc=0x800077ac, rd="x14", rdval="(0x4c00000000#64)",
   rdrw=dshow("shift_bits_left (76#64 : BitVec 64) (Sail.BitVec.extractLsb (0x20#6) 5 0)",
              "0x4c00000000#64"),
   track=True, comment="slli a4,a5,0x20")
st(0x800077ac, "alu", "site_800077ac_pr4", vals="(0x4c00000000#64)",
   hyps="$p:x14 ($mE ▸ hsl0) rfl", nextpc=0x800077b0,
   rd="x15", rdval="(304#64)",
   rdrw=dshow("shift_bits_right (0x4c00000000#64 : BitVec 64)"
              " (Sail.BitVec.extractLsb (0x1e#6) 5 0)", "304#64"),
   track=True, comment="srli a5,a4,0x1e — 4*76")
st(0x800077b0, "alu", "site_800077b0_pr", vals="(304#64) (0x8001a0fc#64)",
   hyps="$p:x15 $p:x22 ($mE ▸ hsl0) rfl", nextpc=0x800077b4,
   rd="x15", rdval="(0x8001a22c#64)",
   rdrw=dshow("(304#64 : BitVec 64) + (0x8001a0fc#64)", "0x8001a22c#64"),
   track=True, comment="add a5,a5,s6 — the 'l' slot address")
st(0x800077b4, "alu", "site_800077b4_pr", vals="(0x8001a22c#64) _ _ _ _",
   hyps="$p:x15 ($mE ▸ hsl0) rfl (by rw [hofftb]; omega) (by rw [hofftb]; omega)"
        " (by rw [hofftb, htoh]; omega) (by rw [hofftb])"
        " (by rw [hofftb, $mE]; exact htb0) (by rw [hofftb, $mE]; exact htb1)"
        " (by rw [hofftb, $mE]; exact htb2) (by rw [hofftb, $mE]; exact htb3)",
   nextpc=0x800077b8, rd="x15", rdval="(0xfffffffffffee438#64)",
   rdrw="show (sign_extend (m := 64) (((((0xff#8).append (0xfe#8)).append"
        " (0xe4#8)).append (0x38#8)) : BitVec (8 * 4)) : BitVec 64)"
        " = (0xfffffffffffee438#64 : BitVec 64) from by"
        " apply BitVec.eq_of_toNat_eq; decide",
   track=True, comment="lw a5,0(a5) — table offset -0x11bc8")
st(0x800077b8, "alu", "site_800077b8_pr", vals="(0xfffffffffffee438#64) (0x8001a0fc#64)",
   hyps="$p:x15 $p:x22 ($mE ▸ hsl0) rfl", nextpc=0x800077bc,
   rd="x15", rdval="(0x80008534#64)",
   rdrw=dshow("(0xfffffffffffee438#64 : BitVec 64) + (0x8001a0fc#64)", "0x80008534#64"),
   track=True, comment="add a5,a5,s6 — the 'l' handler address")
st(0x800077bc, "jr", "site_800077bc_jr_sn4", vals="(0x80008534#64)",
   hyps="$p:x15 ($mE ▸ hsl0) rfl (by rw [ret_tgt _ (by decide)]; decide)",
   nextpc=0x80008534, pcrw="ret",
   comment="jr a5 → the 'l' length-modifier handler")

N = S.k
assert N == 10, N

post = [f"""  have hmemN : σ{N}.mem = c.σ.mem := hmE{N}
  have hslN : Vsa.Sim.Code.SvfprintfSliceLoaded σ{N}.mem := hmemN ▸ hsl0"""]

refine_items = [
    f"hG{N}", f"hpc{N}",
    "$p:x2", "$p:x3", "$p:x8", "$p:x9",
    "$p:x6", "$p:x20", "$p:x25", "$p:x26", "$p:x22", "$p:x27",
    "$p:x10", "$p:x12", "$p:x18", "$p:x19", "$p:x21", "$p:x23",
    "hmemN", "hslN",
    f"hi{N}", f"⟨vmi{N}, hmi{N}⟩",
]

core = "\n".join(S.out + post) + "\n"
tail_items = ",\n    ".join(S.subst(x, f"hp{N}", f"hmE{N}", N) for x in refine_items)
core += f"  refine ⟨⟨σ{N}, i{N}, c.steps + {N}⟩, ?_,\n    {tail_items}⟩\n"
chain = f"(Steps.single hstep{N})"
for j in range(N - 1, 0, -1):
    chain = f"((Steps.single hstep{j}).trans {chain})"
core += "  exact " + chain[1:-1] + "\n"

stmt = """/-- **Segment H of the svfprintf prologue chain**: `0x80007798 → 0x80008534`.

The `%lld` first dispatch, with a FULL post (unlike
`SnprintfSpec14.parseDispatch_l_full_spec`, which surfaces only
`x2/x6/x20/x25/x27`): cursor bump (`s9 := vs9+1`), `sext.w`/`addiw` index
arithmetic (`'l' − 32 = 76`), `bltu` bound check not taken, `slli`/`srli`/
`add` slot address `0x8001a22c`, the `.rodata` table `lw` (bytes
`38 e4 fe ff`, caller pins), `add` → `0x80008534`, and the indirect `jr a5`.
Memory is preserved verbatim (`c'.σ.mem = c.σ.mem`). -/
theorem svfProH_spec
    (vsp va0 vfmt vs9 : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : Vsa.Sim.Code.SvfprintfSliceLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80007798#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx8 : c.σ.regs.get? Register.x8 = some va0)
    (hx9 : c.σ.regs.get? Register.x9 = some (0x8001b798#64))
    (hx22 : c.σ.regs.get? Register.x22 = some (0x8001a0fc#64))
    (hx24 : c.σ.regs.get? Register.x24 = some (0x6c#64))
    (hx25 : c.σ.regs.get? Register.x25 = some vs9)
    (hx26 : c.σ.regs.get? Register.x26 = some (90#64))
    (hx20 : c.σ.regs.get? Register.x20 = some (0xffffffffffffffff#64))
    (hx6 : c.σ.regs.get? Register.x6 = some (0#64))
    (hx27 : c.σ.regs.get? Register.x27 = some (0#64))
    (hx10 : c.σ.regs.get? Register.x10 = some (1#64))
    (hx12 : c.σ.regs.get? Register.x12 = some vfmt)
    (hx18 : c.σ.regs.get? Register.x18 = some (16#64))
    (hx19 : c.σ.regs.get? Register.x19 = some (37#64))
    (hx21 : c.σ.regs.get? Register.x21 = some (vsp + sign_extend (m := 64) (0x160#12)))
    (hx23 : c.σ.regs.get? Register.x23 = some (vsp + sign_extend (m := 64) (0x160#12)))
    -- the .rodata parse-table 'l' slot bytes at 0x8001a22c (offset -0x11bc8)
    (htb0 : c.σ.mem[(0x8001a22c : Nat)]? = some (0x38#8))
    (htb1 : c.σ.mem[(0x8001a22c : Nat) + 1]? = some (0xe4#8))
    (htb2 : c.σ.mem[(0x8001a22c : Nat) + 2]? = some (0xfe#8))
    (htb3 : c.σ.mem[(0x8001a22c : Nat) + 3]? = some (0xff#8))
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x80008534#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x3 = some (0x8001b510#64) ∧
      c'.σ.regs.get? Register.x8 = some va0 ∧
      c'.σ.regs.get? Register.x9 = some (0x8001b798#64) ∧
      c'.σ.regs.get? Register.x6 = some (0#64) ∧
      c'.σ.regs.get? Register.x20 = some (0xffffffffffffffff#64) ∧
      c'.σ.regs.get? Register.x25 = some (vs9 + sign_extend (m := 64) (0x001#12)) ∧
      c'.σ.regs.get? Register.x26 = some (90#64) ∧
      c'.σ.regs.get? Register.x22 = some (0x8001a0fc#64) ∧
      c'.σ.regs.get? Register.x27 = some (0#64) ∧
      c'.σ.regs.get? Register.x10 = some (1#64) ∧
      c'.σ.regs.get? Register.x12 = some vfmt ∧
      c'.σ.regs.get? Register.x18 = some (16#64) ∧
      c'.σ.regs.get? Register.x19 = some (37#64) ∧
      c'.σ.regs.get? Register.x21 = some (vsp + sign_extend (m := 64) (0x160#12)) ∧
      c'.σ.regs.get? Register.x23 = some (vsp + sign_extend (m := 64) (0x160#12)) ∧
      c'.σ.mem = c.σ.mem ∧
      Vsa.Sim.Code.SvfprintfSliceLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hofftb : ((0x8001a22c#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)).toNat
      = (0x8001a22c : Nat) := by decide
"""

pins_list = ", ".join(f"⟨Register.{r}, {v}⟩" for r, v in pins)
pins_hyps = ", ".join(f"hx{r[1:]}" for r, _ in pins)
hp0 = (f"  have hp0 : PinsHold c.σ [{pins_list}] :=\n"
       f"    ⟨{pins_hyps}, trivial⟩\n")

hdr = """import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.SnprintfSitesPro4
import Vsa.Sim.SnprintfSites2

/-!
# M3 Layer-3 — `SnprintfSpec34` : svfprintf prologue segment H
## `0x80007798 → 0x80008534` — the first `%lld` dispatch, wide post

A self-contained twin of `SnprintfSpec14.parseDispatch_l_full_spec` whose
post carries **all** the registers `SnprintfSpec16.parseToPrintEntry_spec`
and `SnprintfSpec26`'s `hmidregs` need at the `'l'` handler entry
(`x2/x3/x6/x8/x9/x10/x12/x18/x19/x20/x21/x22/x23/x25/x26/x27`) plus
`c'.σ.mem = c.σ.mem`.  The table slot bytes are caller pins (`ParseSlotPinned
0x6c` unpacked; `parseSlot_l` in SnprintfSpec13 proves the same data).
Generated in the SnprintfSpec22 house style by /tmp/gen_spec34.py.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

"""

out = hdr + stmt + hp0 + core + "\nend Vsa.Sim\n"
open("Vsa/Sim/SnprintfSpec34.lean", "w").write(out)
print("wrote Vsa/Sim/SnprintfSpec34.lean", len(out.splitlines()), "lines")
