#!/usr/bin/env python3
import sys
sys.path.insert(0, "/tmp")
from emit_pro_seg import Seg

pins = [
    ("x2", "vsp"), ("x3", "(0x8001b510#64)"), ("x8", "va0"), ("x9", "vfile"),
    ("x22", "vfmt"),
    ("x18", "vS2o"), ("x19", "vS3o"), ("x20", "vS4o"), ("x21", "vS5o"),
    ("x23", "vS7o"), ("x24", "vS8o"), ("x25", "vS9o"), ("x26", "vS10o"),
    ("x27", "vS11o"),
]
S = Seg(pins)


def track_sl(k, hoff=None, kind="w8"):
    P = k - 1
    prev = f"hsl{P}" if P > 0 else "hsl0"
    if hoff is None:
        S.emit(f"  have hsl{k} : Vsa.Sim.Code.SvfprintfSliceLoaded σ{k}.mem := by"
               f" rw [hmem{k}]; exact {prev}")
    else:
        fn = "svfprintfSlice_writeMap8_sn5" if kind == "w8" else "svf_w4_pro"
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


spills = [
    (0x800076bc, "x18", 560, "vS2o"), (0x800076c0, "x19", 552, "vS3o"),
    (0x800076c4, "x20", 544, "vS4o"), (0x800076c8, "x21", 536, "vS5o"),
    (0x800076cc, "x23", 520, "vS7o"), (0x800076d0, "x24", 512, "vS8o"),
    (0x800076d4, "x25", 504, "vS9o"), (0x800076d8, "x26", 496, "vS10o"),
    (0x800076dc, "x27", 488, "vS11o"),
]
for (addr, rs2, K, val) in spills:
    st(addr, "store", f"site_{addr:08x}_pr", vals="vsp _",
       hyps=f"$p:x2 $p:{rs2} $L rfl (by rw [hoff{K}]; omega) (by rw [hoff{K}]; omega)"
            f" (by rw [hoff{K}, htoh]; omega) (by rw [hoff{K}]; omega)",
       nextpc=addr + 4,
       memw=("w8", f"vsp.toNat + {K}", f"sdData_val {val}", [f"hoff{K}"]),
       track_hoff=f"hoff{K}",
       comment=f"sd -> sp+{K}")

st(0x800076e0, "alu", "site_800076e0_pr", vals="vsp", hyps="$p:x2 $L rfl",
   nextpc=0x800076e4, rd="x21", rdval="vsp + sign_extend (m := 64) (0x160#12)",
   track=True, comment="addi s5,sp,352 — the iov array base")
st(0x800076e4, "store", "site_800076e4_pr", vals="vsp",
   hyps="$p:x2 $L rfl (by rw [hoff240]; omega) (by rw [hoff240]; omega)"
        " (by rw [hoff240, htoh]; omega) (by rw [hoff240]; omega)",
   nextpc=0x800076e8,
   memw=("w8", "vsp.toNat + 240", "sdData_val (0#64)", ["hoff240"]),
   track_hoff="hoff240", comment="sd zero,240(sp) — uio resid init")
st(0x800076e8, "store", "site_800076e8_pr", vals="vsp",
   hyps="$p:x2 $L rfl (by rw [hoff232]; omega) (by rw [hoff232]; omega)"
        " (by rw [hoff232, htoh]; omega) (by rw [hoff232]; omega)",
   nextpc=0x800076ec,
   memw=("w4", "vsp.toNat + 232", "swData (0#64)", ["hoff232"]),
   track_hoff="hoff232", track_kind="w4", comment="sw zero,232(sp) — iov count init")
st(0x800076ec, "store", "site_800076ec_pr", vals="vsp _",
   hyps="$p:x2 $p:x21 $L rfl (by rw [hoff224]; omega) (by rw [hoff224]; omega)"
        " (by rw [hoff224, htoh]; omega) (by rw [hoff224]; omega)",
   nextpc=0x800076f0,
   memw=("w8", "vsp.toNat + 224",
         "sdData_val (vsp + sign_extend (m := 64) (0x160#12))", ["hoff224"]),
   track_hoff="hoff224", comment="sd s5,224(sp) — iov base slot")
st(0x800076f0, "alu", "site_800076f0_pr", vals="(vsp + sign_extend (m := 64) (0x160#12))",
   hyps="$p:x21 $L rfl", nextpc=0x800076f4,
   rd="x23", rdval="vsp + sign_extend (m := 64) (0x160#12)",
   rdrw="sext0_add_pro (vsp + sign_extend (m := 64) (0x160#12))",
   track=True, comment="mv s7,s5")

N = S.k
assert N == 14, N

# write order (innermost -> outermost): 560,552,544,536,520,512,504,496,488,240,232(w4),224
writes = [(560, "w8"), (552, "w8"), (544, "w8"), (536, "w8"), (520, "w8"), (512, "w8"),
          (504, "w8"), (496, "w8"), (488, "w8"), (240, "w8"), (232, "w4"), (224, "w8")]

post = []
slots = [
    ("hS230", 0x230, "hoff560", "vS2o", 560), ("hS228", 0x228, "hoff552", "vS3o", 552),
    ("hS220", 0x220, "hoff544", "vS4o", 544), ("hS218", 0x218, "hoff536", "vS5o", 536),
    ("hS208", 0x208, "hoff520", "vS7o", 520), ("hS200", 0x200, "hoff512", "vS8o", 512),
    ("hS1f8", 0x1f8, "hoff504", "vS9o", 504), ("hS1f0", 0x1f0, "hoff496", "vS10o", 496),
    ("hS1e8", 0x1e8, "hoff488", "vS11o", 488),
    ("hS0f0", 0x0f0, "hoff240", "(0#64)", 240),
    ("hS0e0", 0x0e0, "hoff224",
     "(vsp + sign_extend (m := 64) (0x160#12))", 224),
]
for (nm, off, hoff, val, K) in slots:
    idx = [w for w, _ in writes].index(K)
    later = writes[idx + 1:]
    ln = [f"  have {nm} : SlotHolds vsp 0x{off:03x} {val} σ{N}.mem := by",
          f"    rw [hmE{N}]"]
    for (_, kind) in reversed(later):
        fn = "slot_survives_writeMap8" if kind == "w8" else "slot_survives_writeMap4"
        ln.append(f"    refine {fn} _ _ _ _ _ _ (by rw [{hoff}]; omega) ?_")
    ln.append(f"    exact slot_save vsp 0x{off:03x} {val} _ _ _ {hoff} rfl")
    post.append("\n".join(ln))

# the count word Pin4 at sp+232 (written by the sw; only the 224-write is later)
post.append(f"""  have hP232 : Pin4 σ{N}.mem (vsp.toNat + 232) (swData (0#64)) := by
    rw [hmE{N}]
    refine Pin4_frame (fun k hk1 hk2 =>
      getElem?_writeMap8_out _ (vsp.toNat + 224) _ k (by omega)) ?_
    exact Pin4_writeMap4 _ _ _""")

post.append(f"""  have hagN : ∀ a : Nat, ¬(vsp.toNat + 560 ≤ a ∧ a < vsp.toNat + 568) →
      ¬(vsp.toNat + 552 ≤ a ∧ a < vsp.toNat + 560) →
      ¬(vsp.toNat + 544 ≤ a ∧ a < vsp.toNat + 552) →
      ¬(vsp.toNat + 536 ≤ a ∧ a < vsp.toNat + 544) →
      ¬(vsp.toNat + 520 ≤ a ∧ a < vsp.toNat + 528) →
      ¬(vsp.toNat + 512 ≤ a ∧ a < vsp.toNat + 520) →
      ¬(vsp.toNat + 504 ≤ a ∧ a < vsp.toNat + 512) →
      ¬(vsp.toNat + 496 ≤ a ∧ a < vsp.toNat + 504) →
      ¬(vsp.toNat + 488 ≤ a ∧ a < vsp.toNat + 496) →
      ¬(vsp.toNat + 240 ≤ a ∧ a < vsp.toNat + 248) →
      ¬(vsp.toNat + 232 ≤ a ∧ a < vsp.toNat + 236) →
      ¬(vsp.toNat + 224 ≤ a ∧ a < vsp.toNat + 232) →
      σ{N}.mem[a]? = c.σ.mem[a]? := by
    intro a hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11
    rw [hmE{N},
      getElem?_writeMap8_out _ (vsp.toNat + 224) _ a (by omega),
      getElem?_writeMap4_out_pro _ (vsp.toNat + 232) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 240) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 488) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 496) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 504) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 512) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 520) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 536) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 544) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 552) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 560) _ a (by omega)]""")

refine_items = [
    f"hG{N}", f"hpc{N}",
    "$p:x2", "$p:x3", "$p:x8", "$p:x9", "$p:x22",
    "$p:x18", "$p:x19", "$p:x20", "$p:x21", "$p:x23",
    "$p:x24", "$p:x25", "$p:x26", "$p:x27",
    "hS230", "hS228", "hS220", "hS218", "hS208", "hS200", "hS1f8", "hS1f0", "hS1e8",
    "hS0f0", "hP232", "hS0e0",
    "hagN", f"hsl{N}", "hmsN", "hlmN", "hambN",
    f"hi{N}", f"⟨vmi{N}, hmi{N}⟩",
]

core = "\n".join(S.out + post) + "\n"
tail_items = ",\n    ".join(S.subst(x, f"hp{N}", f"hmE{N}", N) for x in refine_items)
core += f"  refine ⟨⟨σ{N}, i{N}, c.steps + {N}⟩, ?_,\n    {tail_items}⟩\n"
chain = f"(Steps.single hstep{N})"
for j in range(N - 1, 0, -1):
    chain = f"((Steps.single hstep{j}).trans {chain})"
core += "  exact " + chain[1:-1] + "\n"

stmt = """/-- **Segment D of the svfprintf prologue**: `0x800076bc → 0x800076f4`.

The nine remaining callee-save spills (`s2…s11` to `sp+0x1e8…0x230`), the iov
machinery init: `addi s5,sp,352` (iov array base), `sd zero,240(sp)` (uio
resid), `sw zero,232(sp)` (iov count), `sd s5,224(sp)` (iov base slot),
`mv s7,s5`. -/
theorem svfProD_spec
    (vsp va0 vfile vfmt : BitVec 64)
    (vS2o vS3o vS4o vS5o vS7o vS8o vS9o vS10o vS11o : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : Vsa.Sim.Code.SvfprintfSliceLoaded c.σ.mem)
    (hms0 : Vsa.Sim.Code.MemsetLoaded c.σ.mem)
    (hlm0 : Vsa.Sim.Code.__locale_mb_cur_maxLoaded c.σ.mem)
    (hamb0 : Vsa.Sim.Code.__ascii_mbtowcLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x800076bc#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx8 : c.σ.regs.get? Register.x8 = some va0)
    (hx9 : c.σ.regs.get? Register.x9 = some vfile)
    (hx22 : c.σ.regs.get? Register.x22 = some vfmt)
    (hx18 : c.σ.regs.get? Register.x18 = some vS2o)
    (hx19 : c.σ.regs.get? Register.x19 = some vS3o)
    (hx20 : c.σ.regs.get? Register.x20 = some vS4o)
    (hx21 : c.σ.regs.get? Register.x21 = some vS5o)
    (hx23 : c.σ.regs.get? Register.x23 = some vS7o)
    (hx24 : c.σ.regs.get? Register.x24 = some vS8o)
    (hx25 : c.σ.regs.get? Register.x25 = some vS9o)
    (hx26 : c.σ.regs.get? Register.x26 = some vS10o)
    (hx27 : c.σ.regs.get? Register.x27 = some vS11o)
    (hsplo : 0x8001c000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x800076f4#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x3 = some (0x8001b510#64) ∧
      c'.σ.regs.get? Register.x8 = some va0 ∧
      c'.σ.regs.get? Register.x9 = some vfile ∧
      c'.σ.regs.get? Register.x22 = some vfmt ∧
      c'.σ.regs.get? Register.x18 = some vS2o ∧
      c'.σ.regs.get? Register.x19 = some vS3o ∧
      c'.σ.regs.get? Register.x20 = some vS4o ∧
      c'.σ.regs.get? Register.x21 = some (vsp + sign_extend (m := 64) (0x160#12)) ∧
      c'.σ.regs.get? Register.x23 = some (vsp + sign_extend (m := 64) (0x160#12)) ∧
      c'.σ.regs.get? Register.x24 = some vS8o ∧
      c'.σ.regs.get? Register.x25 = some vS9o ∧
      c'.σ.regs.get? Register.x26 = some vS10o ∧
      c'.σ.regs.get? Register.x27 = some vS11o ∧
      SlotHolds vsp 0x230 vS2o c'.σ.mem ∧
      SlotHolds vsp 0x228 vS3o c'.σ.mem ∧
      SlotHolds vsp 0x220 vS4o c'.σ.mem ∧
      SlotHolds vsp 0x218 vS5o c'.σ.mem ∧
      SlotHolds vsp 0x208 vS7o c'.σ.mem ∧
      SlotHolds vsp 0x200 vS8o c'.σ.mem ∧
      SlotHolds vsp 0x1f8 vS9o c'.σ.mem ∧
      SlotHolds vsp 0x1f0 vS10o c'.σ.mem ∧
      SlotHolds vsp 0x1e8 vS11o c'.σ.mem ∧
      SlotHolds vsp 0x0f0 (0#64) c'.σ.mem ∧
      Pin4 c'.σ.mem (vsp.toNat + 232) (swData (0#64)) ∧
      SlotHolds vsp 0x0e0 (vsp + sign_extend (m := 64) (0x160#12)) c'.σ.mem ∧
      (∀ a : Nat, ¬(vsp.toNat + 560 ≤ a ∧ a < vsp.toNat + 568) →
      ¬(vsp.toNat + 552 ≤ a ∧ a < vsp.toNat + 560) →
      ¬(vsp.toNat + 544 ≤ a ∧ a < vsp.toNat + 552) →
      ¬(vsp.toNat + 536 ≤ a ∧ a < vsp.toNat + 544) →
      ¬(vsp.toNat + 520 ≤ a ∧ a < vsp.toNat + 528) →
      ¬(vsp.toNat + 512 ≤ a ∧ a < vsp.toNat + 520) →
      ¬(vsp.toNat + 504 ≤ a ∧ a < vsp.toNat + 512) →
      ¬(vsp.toNat + 496 ≤ a ∧ a < vsp.toNat + 504) →
      ¬(vsp.toNat + 488 ≤ a ∧ a < vsp.toNat + 496) →
      ¬(vsp.toNat + 240 ≤ a ∧ a < vsp.toNat + 248) →
      ¬(vsp.toNat + 232 ≤ a ∧ a < vsp.toNat + 236) →
      ¬(vsp.toNat + 224 ≤ a ∧ a < vsp.toNat + 232) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      Vsa.Sim.Code.SvfprintfSliceLoaded c'.σ.mem ∧
      Vsa.Sim.Code.MemsetLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__locale_mb_cur_maxLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__ascii_mbtowcLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
"""

for K, off in [(560, 0x230), (552, 0x228), (544, 0x220), (536, 0x218), (520, 0x208),
               (512, 0x200), (504, 0x1f8), (496, 0x1f0), (488, 0x1e8), (240, 0x0f0),
               (232, 0x0e8), (224, 0x0e0)]:
    stmt += (f"  have hoff{K} : (vsp + sign_extend (m := 64) (0x{off:03x}#12)).toNat"
             f" = vsp.toNat + {K} := ptr_addoff vsp _ {K} (by decide) (by omega)\n")

pins_list = ", ".join(f"⟨Register.{r}, {v}⟩" for r, v in pins)
pins_hyps = ", ".join(f"hx{r[1:]}" for r, _ in pins)
hp0 = (f"  have hp0 : PinsHold c.σ [{pins_list}] :=\n"
       f"    ⟨{pins_hyps}, trivial⟩\n")

hdr = """import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro

/-!
# M3 Layer-3 — `SnprintfSpec30` : svfprintf prologue segment D
## `0x800076bc` (second spill block) → `0x800076f4`

The nine `s2…s11` callee-save spills to `sp+0x1e8…0x230` (Spec26's
`hsv1e8…hsv230` residuals) and the uio/iov init (`resid := 0` at `sp+240`,
`count := 0` at `sp+232`, iov base `sp+352` at `sp+224`, `s5 = s7 := sp+352`).
Generated in the SnprintfSpec22 house style by /tmp/gen_spec30.py.
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

# exports of the other loadeds
post_loaded = f"""  have hmsN : Vsa.Sim.Code.MemsetLoaded σ{N}.mem := by
    rw [hmE{N}]
    exact memset_w8_pro _ _ _ (by omega) (memset_w4_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega) hms0)))))))))))
  have hlmN : Vsa.Sim.Code.__locale_mb_cur_maxLoaded σ{N}.mem := by
    rw [hmE{N}]
    exact localemb_w8_pro _ _ _ (by omega) (localemb_w4_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega) hlm0)))))))))))
  have hambN : Vsa.Sim.Code.__ascii_mbtowcLoaded σ{N}.mem := by
    rw [hmE{N}]
    exact amb_w8_pro _ _ _ (by omega) (amb_w4_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega) hamb0)))))))))))"""
post.insert(0, post_loaded)

core = "\n".join(S.out + post) + "\n"
tail_items = ",\n    ".join(S.subst(x, f"hp{N}", f"hmE{N}", N) for x in refine_items)
core += f"  refine ⟨⟨σ{N}, i{N}, c.steps + {N}⟩, ?_,\n    {tail_items}⟩\n"
chain = f"(Steps.single hstep{N})"
for j in range(N - 1, 0, -1):
    chain = f"((Steps.single hstep{j}).trans {chain})"
core += "  exact " + chain[1:-1] + "\n"

out = hdr + stmt + hp0 + core + "\nend Vsa.Sim\n"
open("Vsa/Sim/SnprintfSpec30.lean", "w").write(out)
print("wrote Vsa/Sim/SnprintfSpec30.lean", len(out.splitlines()), "lines")
