#!/usr/bin/env python3
"""Emit Vsa/Sim/SnprintfSpec41.lean — the snprintf wrapper POST-CALL segment
0x80005cbc (return from _svfprintf_r) -> snprintf's ret (PC = wra0).
House style: SnprintfSpec27/40 pattern over the SnprintfSitesWrap battery."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from emit_pro_seg import Seg

pins = [
    ("x2", "(vsp + (592#64))"), ("x10", "va0r"), ("x8", "sz"),
    ("x18", "vS2o"), ("x19", "vS3o"), ("x20", "vS4o"), ("x21", "vS5o"),
    ("x22", "vS6o"), ("x23", "vS7o"), ("x24", "vS8o"), ("x25", "vS9o"),
    ("x26", "vS10o"), ("x27", "vS11o"),
]
S = Seg(pins)

SNP = "Vsa.Sim.Code.SnprintfLoaded"


def track_loaded(k, insert=False):
    P = k - 1
    prev = f"hsl{P}"
    if not insert:
        S.emit(f"  have hsl{k} : {SNP} σ{k}.mem := by rw [hmem{k}]; exact {prev}")
    else:
        S.emit(f"  have hsl{k} : {SNP} σ{k}.mem := by",
               f"    rw [hmem{k}, mem_afterNextPC]",
               f"    exact snprintf_insert_wr _ _ _ (by rw [hoffcur]; omega) {prev}")


def st(*a, **kw):
    ins = kw.pop("track_insert", False)
    S.step(*a, **kw)
    S.out.pop()
    track_loaded(S.k, ins)
    S.emit("")


SP = "(vsp + (592#64))"
SD = "(sdData_val {v}).extractLsb'"

# === 1: li a5,-1 ===
st(0x80005cbc, "alu", "site_80005cbc_wp",
   hyps="$L rfl", nextpc=0x80005cc0,
   rd="x15", rdval="((0#64) + sign_extend (m := 64) (0xfff#12))",
   track=True, comment="li a5,-1")

# === 2: blt a0,a5 NOT taken (the svfprintf total ≥ 0 > -1) ===
st(0x80005cc0, "bnottaken", "site_80005cc0_nottaken_wp",
   vals="va0r _",
   hyps="$p:x10 $p:x15 $L rfl hgs2", nextpc=0x80005cc4,
   pre=("have hgs2 : zopz0zI_s va0r ((0#64) + sign_extend (m := 64) (0xfff#12)) = false :="
        " blt_m1_false_wr va0r hva0r",),
   comment="blt a0,a5 — NOT taken (a0 ≥ 0)")

# === 3: bnez s0 TAKEN (sz ≠ 0) -> 0x80005cdc ===
st(0x80005cc4, "btaken", "site_80005cc4_taken_wp",
   vals="sz",
   hyps="$p:x8 $L rfl hgn3", nextpc=0x80005cdc, pcrw=("btshow", 0x0018),
   pre=("have hgn3 : (sz != (0#64)) = true := by"
        " simp only [bne]"
        "; rw [beq64_false_pro sz (0#64) (by"
        " rw [show ((0#64 : BitVec 64)).toNat = 0 from rfl]; omega)]"
        "; rfl",),
   comment="bnez s0 — TAKEN (sz ≠ 0), to the NUL-terminate arm")

# === 4: ld a5,8(sp) — the updated FILE cursor = d + total ===
st(0x80005cdc, "alu", "site_80005cdc_wp",
   vals=f"{SP} _ _ _ _ _ _ _ _",
   hyps="$p:x2 $L rfl (by rw [hoff600]; omega) (by rw [hoff600]; omega)"
        " (by rw [hoff600, htoh]; omega) (by rw [hoff600]; omega)"
        " (by rw [hoff600, $mE]; exact hcur.1)"
        " (by rw [hoff600, $mE]; exact hcur.2.1)"
        " (by rw [hoff600, $mE]; exact hcur.2.2.1)"
        " (by rw [hoff600, $mE]; exact hcur.2.2.2.1)"
        " (by rw [hoff600, $mE]; exact hcur.2.2.2.2.1)"
        " (by rw [hoff600, $mE]; exact hcur.2.2.2.2.2.1)"
        " (by rw [hoff600, $mE]; exact hcur.2.2.2.2.2.2.1)"
        " (by rw [hoff600, $mE]; exact hcur.2.2.2.2.2.2.2)",
   nextpc=0x80005ce0,
   rd="x15", rdval="vcur", rdrw="slot_reassemble vcur", track=True,
   comment="ld a5,8(sp) — a5 := the updated cursor d+total")

# === 5: sb zero,0(a5) — the NUL terminator ===
st(0x80005ce0, "store", "site_80005ce0_wp", vals="vcur",
   hyps="$p:x15 $L rfl (by rw [hoffcur]; omega) (by rw [hoffcur]; omega)"
        " (by rw [hoffcur, htoh]; omega)",
   nextpc=0x80005ce4,
   memw=(None, "vcur.toNat", "stData 1 (0#64)", ["hoffcur"]),
   track_insert=True,
   comment="sb zero,0(a5) — NUL-terminate at d+total")

# transported slot facts across the NUL insert
S.emit("""  -- the three save slots survive the NUL byte (vcur is outside the frame)
  have hS0d0x : SlotHolds (vsp + (592#64)) 0x0d0 vS0o σ5.mem := by
    rw [hmE5]
    exact slot_survives_insert _ _ _ _ _ _ (by rw [hoff800]; omega) hS0d0
  have hS0d8x : SlotHolds (vsp + (592#64)) 0x0d8 wra0 σ5.mem := by
    rw [hmE5]
    exact slot_survives_insert _ _ _ _ _ _ (by rw [hoff808]; omega) hS0d8
  have hS0c8x : SlotHolds (vsp + (592#64)) 0x0c8 vS1o σ5.mem := by
    rw [hmE5]
    exact slot_survives_insert _ _ _ _ _ _ (by rw [hoff792]; omega) hS0c8
""")

# === 6/7/8: the three epilogue reloads ===
reloads = [
    (0x80005ce4, "site_80005ce4_wp", 0x0d0, 800, "x8", "vS0o", "hS0d0x",
     ("have hS0d8y : SlotHolds (vsp + (592#64)) 0x0d8 wra0 σ$K.mem := by"
      " rw [hmem$K]; exact hS0d8x",
      "have hS0c8y : SlotHolds (vsp + (592#64)) 0x0c8 vS1o σ$K.mem := by"
      " rw [hmem$K]; exact hS0c8x")),
    (0x80005ce8, "site_80005ce8_wp", 0x0d8, 808, "x1", "wra0", "hS0d8y",
     ("have hS0c8z : SlotHolds (vsp + (592#64)) 0x0c8 vS1o σ$K.mem := by"
      " rw [hmem$K]; exact hS0c8y",)),
    (0x80005cec, "site_80005cec_wp", 0x0c8, 792, "x9", "vS1o", "hS0c8z", ()),
]
for (addr, site, off, K, reg, val, hS, posts) in reloads:
    st(addr, "alu", site,
       vals=f"{SP} _ _ _ _ _ _ _ _",
       hyps=f"$p:x2 $L rfl (by rw [hoff{K}]; omega) (by rw [hoff{K}]; omega)"
            f" (by rw [hoff{K}, htoh]; omega) (by rw [hoff{K}]; omega)"
            f" {hS}.1"
            f" {hS}.2.1"
            f" {hS}.2.2.1"
            f" {hS}.2.2.2.1"
            f" {hS}.2.2.2.2.1"
            f" {hS}.2.2.2.2.2.1"
            f" {hS}.2.2.2.2.2.2.1"
            f" {hS}.2.2.2.2.2.2.2",
       nextpc=addr + 4,
       rd=reg, rdval=val, rdrw=f"slot_reassemble {val}", track=True,
       post=posts,
       comment=f"ld {reg},{off - 0x0c8 + 200}(sp) — reload {val}")

# === 9: addi sp,sp,272 ===
st(0x80005cf0, "alu", "site_80005cf0_wp", vals=SP,
   hyps="$p:x2 $L rfl", nextpc=0x80005cf4,
   rd="x2", rdval="(vsp + (864#64))", rdrw="sp_inc272_wr vsp", track=True,
   comment="addi sp,sp,272 — frame released")

# === 10: ret ===
st(0x80005cf4, "jr", "site_80005cf4_wp", vals="wra0",
   hyps="$p:x1 $L rfl (by rw [ret_tgt _ hwra]; exact hwra)",
   nextpc=0xDEADBEEF, pcrw=("jrshow", "ret_tgt _ hwra"),
   comment="ret — back to the snprintf caller")

N = S.k
assert N == 10, N

refine_items = [
    f"hG{N}", f"hpc{N}",
    "$p:x1", "$p:x2", "$p:x10", "$p:x8", "$p:x9",
    "$p:x18", "$p:x19", "$p:x20", "$p:x21", "$p:x22", "$p:x23",
    "$p:x24", "$p:x25", "$p:x26", "$p:x27",
    f"hmE{N}", f"hsl{N}",
    f"hi{N}", f"⟨vmi{N}, hmi{N}⟩",
]

core = "\n".join(S.out) + "\n"
tail_items = ",\n    ".join(S.subst(x, f"hp{N}", f"hmE{N}", N) for x in refine_items)
core += f"  refine ⟨⟨σ{N}, i{N}, c.steps + {N}⟩, ?_,\n    {tail_items}⟩\n"
chain = f"(Steps.single hstep{N})"
for j in range(N - 1, 0, -1):
    chain = f"((Steps.single hstep{j}).trans {chain})"
core += "  exact " + chain[1:-1] + "\n"

# the ret's symbolic target: patch the placeholder PC literal
core = core.replace("(0xdeadbeef#64)", "wra0")

stmt = """/-- **The snprintf wrapper POST-CALL segment**: `0x80005cbc → ret` (`PC = wra0`).

From `_svfprintf_r`'s return (`a0 = va0r` = the total, small and non-negative;
`s0 = sz ≠ 0`) through the error check (`blt` not taken), the `bnez` to the
NUL-terminate arm, the reload of the updated FILE cursor `vcur = d + total`
from `sp+8` (`Pin8`), the `sb zero,0(a5)` NUL terminator, the three
`SlotHolds` epilogue reloads, the frame release, and the `ret`.

Post: `PC = x1 = wra0`, `sp = vsp + 864`, `a0 = va0r` preserved, `s0/s1`
restored, and the memory is exactly the entry memory plus the single NUL byte
at `vcur`. -/
theorem snprintfPostCall_spec
    (vsp wra0 vcur sz va0r : BitVec 64)
    (vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : Vsa.Sim.Code.SnprintfLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80005cbc#64))
    (hx2 : c.σ.regs.get? Register.x2 = some (vsp + (592#64)))
    (hx10 : c.σ.regs.get? Register.x10 = some va0r)
    (hx8 : c.σ.regs.get? Register.x8 = some sz)
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
    (hcur : Pin8 c.σ.mem (vsp.toNat + 600) vcur)
    (hS0c8 : SlotHolds (vsp + (592#64)) 0x0c8 vS1o c.σ.mem)
    (hS0d0 : SlotHolds (vsp + (592#64)) 0x0d0 vS0o c.σ.mem)
    (hS0d8 : SlotHolds (vsp + (592#64)) 0x0d8 wra0 c.σ.mem)
    (hva0r : va0r.toNat < 2 ^ 63)
    (hsz : 1 ≤ sz.toNat)
    (hcurge : 0x8001c000 ≤ vcur.toNat)
    (hcurhi : vcur.toNat + 1 ≤ 0x100000000)
    (hcurdisj : vcur.toNat + 1 ≤ vsp.toNat + 592 ∨ vsp.toNat + 864 ≤ vcur.toNat)
    (hwra : wra0.toNat % 4 = 0)
    (hsplo : 0x8001c100 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 864 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some wra0 ∧
      c'.σ.regs.get? Register.x1 = some wra0 ∧
      c'.σ.regs.get? Register.x2 = some (vsp + (864#64)) ∧
      c'.σ.regs.get? Register.x10 = some va0r ∧
      c'.σ.regs.get? Register.x8 = some vS0o ∧
      c'.σ.regs.get? Register.x9 = some vS1o ∧
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
      c'.σ.mem = (c.σ.mem).insert (vcur.toNat) (stData 1 (0#64)) ∧
      Vsa.Sim.Code.SnprintfLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have h592 : ((vsp + (592#64)) : BitVec 64).toNat = vsp.toNat + 592 := by
    rw [BitVec.toNat_add, show ((592#64 : BitVec 64)).toNat = 592 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
"""

hoffs = ""
for K, off in [(600, 0x008), (792, 0x0c8), (800, 0x0d0), (808, 0x0d8)]:
    hoffs += (f"  have hoff{K} : ((vsp + (592#64)) + sign_extend (m := 64)"
              f" (0x{off:03x}#12)).toNat = vsp.toNat + {K} := by\n"
              f"    rw [ptr_addoff (vsp + (592#64)) _ {K - 592} (by decide)"
              f" (by rw [h592]; omega), h592]\n")
hoffs += ("  have hoffcur : ((vcur + sign_extend (m := 64) (0x000#12)) : BitVec 64).toNat"
          " = vcur.toNat := by rw [sext0_add_pro vcur]\n")

pins_list = ", ".join(f"⟨Register.{r}, {v}⟩" for r, v in pins)
pins_hyps = ", ".join(f"hx{r[1:]}" for r, _ in pins)
hp0 = (f"  have hp0 : PinsHold c.σ [{pins_list}] :=\n"
       f"    ⟨{pins_hyps}, trivial⟩\n")

hdr = """import Vsa.Sim.SnprintfSpec40

/-!
# M3 Layer-3 — `SnprintfSpec41` : the snprintf wrapper POST-CALL segment
## `0x80005cbc` (return from `_svfprintf_r`) → snprintf's `ret`

The 10-instruction return path of newlib's `snprintf`: error check (`a0 ≥ -1`,
not taken), `bnez s0` to the NUL-terminate arm (`sz ≠ 0`), reload of the
updated FILE cursor from `sp+8`, the `sb zero,0(a5)` **NUL terminator** at
`d + total`, the three callee-save reloads, the frame release, and the `ret`.
`snprintf` returns `_svfprintf_r`'s total in `a0` unchanged.

Emitted by `scripts/pro_emitter/gen_spec41.py` (SnprintfSpec27/40 house style).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- The `blt a0,a5` guard with `a5 = -1`: a small non-negative `a0` is not
signed-below `-1`. -/
theorem blt_m1_false_wr (x : BitVec 64) (hx : x.toNat < 2 ^ 63) :
    zopz0zI_s x ((0#64) + sign_extend (m := 64) (0xfff#12)) = false := by
  unfold zopz0zI_s
  rw [show (((0#64) + sign_extend (m := 64) (0xfff#12)) : BitVec 64).toInt = -1 from by decide,
    toInt_of_notop x hx]
  exact decide_eq_false (by omega)

"""

out = hdr + stmt + hoffs + hp0 + core + "\nend Vsa.Sim\n"
open("Vsa/Sim/SnprintfSpec41.lean", "w").write(out)
print("wrote Vsa/Sim/SnprintfSpec41.lean", len(out.splitlines()), "lines")
