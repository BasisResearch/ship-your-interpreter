#!/usr/bin/env python3
import sys
sys.path.insert(0, "/tmp")
from emit_pro_seg import Seg

pins = [
    ("x2", "vsp"), ("x3", "(0x8001b510#64)"), ("x8", "va0"), ("x9", "vfile"),
    ("x22", "vfmt"),
    ("x21", "vsp + sign_extend (m := 64) (0x160#12)"),
    ("x23", "vsp + sign_extend (m := 64) (0x160#12)"),
    ("x24", "vS8o"), ("x25", "vS9o"), ("x26", "vS10o"), ("x27", "vS11o"),
]
S = Seg(pins)


def track_sl(k, hoff=None):
    P = k - 1
    prev = f"hsl{P}" if P > 0 else "hsl0"
    if hoff is None:
        S.emit(f"  have hsl{k} : Vsa.Sim.Code.SvfprintfSliceLoaded σ{k}.mem := by"
               f" rw [hmem{k}]; exact {prev}")
    else:
        S.emit(f"  have hsl{k} : Vsa.Sim.Code.SvfprintfSliceLoaded σ{k}.mem := by",
               f"    rw [hmem{k}, mem_afterNextPC]",
               f"    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [{hoff}]; omega) {prev}")


def st(*a, **kw):
    hoff = kw.pop("track_hoff", None)
    S.step(*a, **kw)
    S.out.pop()
    track_sl(S.k, hoff)
    S.emit("")


def dshow(lhs, rhs):
    return f"show {lhs} = ({rhs} : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide"


zeros = [(0x800076f4, 40), (0x800076f8, 64), (0x800076fc, 88), (0x80007700, 104),
         (0x80007704, 128), (0x80007708, 96), (0x8000770c, 16)]
for (addr, K) in zeros:
    st(addr, "store", f"site_{addr:08x}_pr", vals="vsp",
       hyps=f"$p:x2 $L rfl (by rw [hoff{K}]; omega) (by rw [hoff{K}]; omega)"
            f" (by rw [hoff{K}, htoh]; omega) (by rw [hoff{K}]; omega)",
       nextpc=addr + 4,
       memw=("w8", f"vsp.toNat + {K}", "sdData_val (0#64)", [f"hoff{K}"]),
       track_hoff=f"hoff{K}",
       comment=f"sd zero,{K}(sp)")

st(0x80007710, "alu", "site_80007710_pr", vals="(0x8001b510#64)", hyps="$p:x3 $L rfl",
   nextpc=0x80007714, rd="x9", rdval="(0x8001b798#64)",
   rdrw=dshow("(0x8001b510#64 : BitVec 64) + sign_extend (m := 64) (0x288#12)",
              "0x8001b798#64"),
   track=True, comment="addi s1,gp,648 — s1 := &__global_locale")
st(0x80007714, "alu", "site_80007714_pr", hyps="$L rfl", nextpc=0x80007718,
   rd="x19", rdval="(37#64)",
   rdrw=dshow("((0#64) : BitVec 64) + sign_extend (m := 64) (0x025#12)", "37#64"),
   track=True, comment="li s3,37 — '%'")
st(0x80007718, "alu", "site_80007718_pr", hyps="$L rfl", nextpc=0x8000771c,
   rd="x18", rdval="(16#64)",
   rdrw=dshow("((0#64) : BitVec 64) + sign_extend (m := 64) (0x010#12)", "16#64"),
   track=True, comment="li s2,16")
st(0x8000771c, "store", "site_8000771c_pr", vals="vsp _",
   hyps="$p:x2 $p:x22 $L rfl (by rw [hoff0]; omega) (by rw [hoff0]; omega)"
        " (by rw [hoff0, htoh]; omega) (by rw [hoff0]; omega)",
   nextpc=0x80007720,
   memw=("w8", "vsp.toNat", "sdData_val vfmt", ["hoff0"]),
   track_hoff="hoff0", comment="sd s6,0(sp) — the fmt cursor slot")

# 12: ld s6,0(sp) — read back the just-stored fmt
st(0x80007720, "alu", "site_80007720_rt", vals="vsp _ _ _ _ _ _ _ _",
   pre=["have hrb0 : σ$K.mem[vsp.toNat]?"
        " = some ((sdData_val vfmt).extractLsb' 0 8) := by"
        " rw [$mE]; exact getElem_writeMap8_0 _ _ _",
        "have hrb1 : σ$K.mem[vsp.toNat + 1]?"
        " = some ((sdData_val vfmt).extractLsb' 8 8) := by"
        " rw [$mE]; exact getElem_writeMap8_1 _ _ _",
        "have hrb2 : σ$K.mem[vsp.toNat + 2]?"
        " = some ((sdData_val vfmt).extractLsb' 16 8) := by"
        " rw [$mE]; exact getElem_writeMap8_2 _ _ _",
        "have hrb3 : σ$K.mem[vsp.toNat + 3]?"
        " = some ((sdData_val vfmt).extractLsb' 24 8) := by"
        " rw [$mE]; exact getElem_writeMap8_3 _ _ _",
        "have hrb4 : σ$K.mem[vsp.toNat + 4]?"
        " = some ((sdData_val vfmt).extractLsb' 32 8) := by"
        " rw [$mE]; exact getElem_writeMap8_4 _ _ _",
        "have hrb5 : σ$K.mem[vsp.toNat + 5]?"
        " = some ((sdData_val vfmt).extractLsb' 40 8) := by"
        " rw [$mE]; exact getElem_writeMap8_5 _ _ _",
        "have hrb6 : σ$K.mem[vsp.toNat + 6]?"
        " = some ((sdData_val vfmt).extractLsb' 48 8) := by"
        " rw [$mE]; exact getElem_writeMap8_6 _ _ _",
        "have hrb7 : σ$K.mem[vsp.toNat + 7]?"
        " = some ((sdData_val vfmt).extractLsb' 56 8) := by"
        " rw [$mE]; exact getElem_writeMap8_7 _ _ _"],
   hyps="$p:x2 $L rfl (by rw [hoff0]; omega) (by rw [hoff0]; omega)"
        " (Or.inr (by rw [hoff0, htoh]; omega)) (by rw [hoff0]; omega)"
        " (by rw [hoff0]; exact hrb0) (by rw [hoff0]; exact hrb1)"
        " (by rw [hoff0]; exact hrb2) (by rw [hoff0]; exact hrb3)"
        " (by rw [hoff0]; exact hrb4) (by rw [hoff0]; exact hrb5)"
        " (by rw [hoff0]; exact hrb6) (by rw [hoff0]; exact hrb7)",
   nextpc=0x80007724, rd="x22", rdval="vfmt", rdrw="slot_reassemble vfmt",
   track=True, comment="ld s6,0(sp) — reload the fmt cursor")

# 13: ld s4,232(s1) — static locale mbtowc fn pointer
S.emit("""  -- below-frame agreement at σ12 (all eight writes are in-frame)
  have hagA : ∀ a : Nat, a < vsp.toNat → σ12.mem[a]? = c.σ.mem[a]? := by
    intro a ha
    rw [hmE12,
      getElem?_writeMap8_out _ (vsp.toNat) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 16) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 96) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 128) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 104) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 88) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 64) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 40) _ a (by omega)]
""")
st(0x80007724, "alu", "site_80007724_rt", vals="(0x8001b798#64) _ _ _ _ _ _ _ _",
   hyps="$p:x9 $L rfl (by rw [hoffloc]; omega) (by rw [hoffloc]; omega)"
        " (Or.inr (by rw [hoffloc, htoh]; omega)) (by rw [hoffloc])"
        " (by rw [hoffloc]; exact (hagA _ (by omega)).trans hfn0)"
        " (by rw [hoffloc]; exact (hagA _ (by omega)).trans hfn1)"
        " (by rw [hoffloc]; exact (hagA _ (by omega)).trans hfn2)"
        " (by rw [hoffloc]; exact (hagA _ (by omega)).trans hfn3)"
        " (by rw [hoffloc]; exact (hagA _ (by omega)).trans hfn4)"
        " (by rw [hoffloc]; exact (hagA _ (by omega)).trans hfn5)"
        " (by rw [hoffloc]; exact (hagA _ (by omega)).trans hfn6)"
        " (by rw [hoffloc]; exact (hagA _ (by omega)).trans hfn7)",
   nextpc=0x80007728, rd="x20", rdval="(0x80012268#64)",
   rdrw="show (sign_extend (m := 64)"
        " (((((((((0x00#8).append (0x00#8)).append (0x00#8)).append (0x00#8)).append"
        " (0x80#8)).append (0x01#8)).append (0x22#8)).append (0x68#8))"
        " : BitVec (8 * 8)) : BitVec 64) = (0x80012268#64 : BitVec 64) from by"
        " apply BitVec.eq_of_toNat_eq; decide",
   track=True, comment="ld s4,232(s1) — __global_locale.mbtowc = __ascii_mbtowc")

N = S.k
assert N == 13, N

writes = [40, 64, 88, 104, 128, 96, 16, 0]
post = []
slots = [("hS028", 0x028, "hoff40", 40), ("hS040", 0x040, "hoff64", 64),
         ("hS058", 0x058, "hoff88", 88), ("hS068", 0x068, "hoff104", 104),
         ("hS080", 0x080, "hoff128", 128), ("hS060", 0x060, "hoff96", 96),
         ("hS010", 0x010, "hoff16", 16)]
for (nm, off, hoff, K) in slots:
    later = writes[writes.index(K) + 1:]
    ln = [f"  have {nm} : SlotHolds vsp 0x{off:03x} (0#64) σ{N}.mem := by",
          f"    rw [hmE{N}]"]
    for _ in later:
        ln.append(f"    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [{hoff}]; omega) ?_")
    ln.append(f"    exact slot_save vsp 0x{off:03x} (0#64) _ _ _ {hoff} rfl")
    post.append("\n".join(ln))

post.append(f"""  have hS000 : SlotHolds vsp 0x000 vfmt σ{N}.mem := by
    rw [hmE{N}]
    exact slot_save vsp 0x000 vfmt _ _ _ hoff0 rfl
  have hagN : ∀ a : Nat, ¬(vsp.toNat + 40 ≤ a ∧ a < vsp.toNat + 48) →
      ¬(vsp.toNat + 64 ≤ a ∧ a < vsp.toNat + 72) →
      ¬(vsp.toNat + 88 ≤ a ∧ a < vsp.toNat + 96) →
      ¬(vsp.toNat + 104 ≤ a ∧ a < vsp.toNat + 112) →
      ¬(vsp.toNat + 128 ≤ a ∧ a < vsp.toNat + 136) →
      ¬(vsp.toNat + 96 ≤ a ∧ a < vsp.toNat + 104) →
      ¬(vsp.toNat + 16 ≤ a ∧ a < vsp.toNat + 24) →
      ¬(vsp.toNat ≤ a ∧ a < vsp.toNat + 8) →
      σ{N}.mem[a]? = c.σ.mem[a]? := by
    intro a hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7
    rw [hmE{N},
      getElem?_writeMap8_out _ (vsp.toNat) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 16) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 96) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 128) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 104) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 88) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 64) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 40) _ a (by omega)]
  have hmsN : Vsa.Sim.Code.MemsetLoaded σ{N}.mem := by
    rw [hmE{N}]
    exact memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega) hms0)))))))
  have hlmN : Vsa.Sim.Code.__locale_mb_cur_maxLoaded σ{N}.mem := by
    rw [hmE{N}]
    exact localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega) hlm0)))))))
  have hambN : Vsa.Sim.Code.__ascii_mbtowcLoaded σ{N}.mem := by
    rw [hmE{N}]
    exact amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega) hamb0)))))))""")

refine_items = [
    f"hG{N}", f"hpc{N}",
    "$p:x2", "$p:x3", "$p:x8", "$p:x9", "$p:x22", "$p:x20",
    "$p:x18", "$p:x19", "$p:x21", "$p:x23",
    "$p:x24", "$p:x25", "$p:x26", "$p:x27",
    "hS028", "hS040", "hS058", "hS068", "hS080", "hS060", "hS010", "hS000",
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

stmt = """/-- **Segment E of the svfprintf prologue**: `0x800076f4 → 0x80007728`.

The seven zero-initialized parse-state slots (`sp+{40,64,88,104,128,96,16}` —
the last is the TOTAL accumulator, Spec26's `htotS` with `vtot = 0`),
`s1 := &__global_locale` (`0x8001b798`), the `'%'` and `16` constants, the
fmt-cursor spill `sd s6,0(sp)` + reload, and the static
`__global_locale.mbtowc` function-pointer load (`s4 := __ascii_mbtowc =
0x80012268`, Spec26's `hfnslot` data). -/
theorem svfProE_spec
    (vsp va0 vfile vfmt : BitVec 64)
    (vS8o vS9o vS10o vS11o : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : Vsa.Sim.Code.SvfprintfSliceLoaded c.σ.mem)
    (hms0 : Vsa.Sim.Code.MemsetLoaded c.σ.mem)
    (hlm0 : Vsa.Sim.Code.__locale_mb_cur_maxLoaded c.σ.mem)
    (hamb0 : Vsa.Sim.Code.__ascii_mbtowcLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x800076f4#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx8 : c.σ.regs.get? Register.x8 = some va0)
    (hx9 : c.σ.regs.get? Register.x9 = some vfile)
    (hx22 : c.σ.regs.get? Register.x22 = some vfmt)
    (hx21 : c.σ.regs.get? Register.x21 = some (vsp + sign_extend (m := 64) (0x160#12)))
    (hx23 : c.σ.regs.get? Register.x23 = some (vsp + sign_extend (m := 64) (0x160#12)))
    (hx24 : c.σ.regs.get? Register.x24 = some vS8o)
    (hx25 : c.σ.regs.get? Register.x25 = some vS9o)
    (hx26 : c.σ.regs.get? Register.x26 = some vS10o)
    (hx27 : c.σ.regs.get? Register.x27 = some vS11o)
    -- static __global_locale.mbtowc slot bytes at 0x8001b880 (= 0x80012268)
    (hfn0 : c.σ.mem[(0x8001b880 : Nat)]? = some (0x68#8))
    (hfn1 : c.σ.mem[(0x8001b880 : Nat) + 1]? = some (0x22#8))
    (hfn2 : c.σ.mem[(0x8001b880 : Nat) + 2]? = some (0x01#8))
    (hfn3 : c.σ.mem[(0x8001b880 : Nat) + 3]? = some (0x80#8))
    (hfn4 : c.σ.mem[(0x8001b880 : Nat) + 4]? = some (0x00#8))
    (hfn5 : c.σ.mem[(0x8001b880 : Nat) + 5]? = some (0x00#8))
    (hfn6 : c.σ.mem[(0x8001b880 : Nat) + 6]? = some (0x00#8))
    (hfn7 : c.σ.mem[(0x8001b880 : Nat) + 7]? = some (0x00#8))
    (hsplo : 0x8001c000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x80007728#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x3 = some (0x8001b510#64) ∧
      c'.σ.regs.get? Register.x8 = some va0 ∧
      c'.σ.regs.get? Register.x9 = some (0x8001b798#64) ∧
      c'.σ.regs.get? Register.x22 = some vfmt ∧
      c'.σ.regs.get? Register.x20 = some (0x80012268#64) ∧
      c'.σ.regs.get? Register.x18 = some (16#64) ∧
      c'.σ.regs.get? Register.x19 = some (37#64) ∧
      c'.σ.regs.get? Register.x21 = some (vsp + sign_extend (m := 64) (0x160#12)) ∧
      c'.σ.regs.get? Register.x23 = some (vsp + sign_extend (m := 64) (0x160#12)) ∧
      c'.σ.regs.get? Register.x24 = some vS8o ∧
      c'.σ.regs.get? Register.x25 = some vS9o ∧
      c'.σ.regs.get? Register.x26 = some vS10o ∧
      c'.σ.regs.get? Register.x27 = some vS11o ∧
      SlotHolds vsp 0x028 (0#64) c'.σ.mem ∧
      SlotHolds vsp 0x040 (0#64) c'.σ.mem ∧
      SlotHolds vsp 0x058 (0#64) c'.σ.mem ∧
      SlotHolds vsp 0x068 (0#64) c'.σ.mem ∧
      SlotHolds vsp 0x080 (0#64) c'.σ.mem ∧
      SlotHolds vsp 0x060 (0#64) c'.σ.mem ∧
      SlotHolds vsp 0x010 (0#64) c'.σ.mem ∧
      SlotHolds vsp 0x000 vfmt c'.σ.mem ∧
      (∀ a : Nat, ¬(vsp.toNat + 40 ≤ a ∧ a < vsp.toNat + 48) →
      ¬(vsp.toNat + 64 ≤ a ∧ a < vsp.toNat + 72) →
      ¬(vsp.toNat + 88 ≤ a ∧ a < vsp.toNat + 96) →
      ¬(vsp.toNat + 104 ≤ a ∧ a < vsp.toNat + 112) →
      ¬(vsp.toNat + 128 ≤ a ∧ a < vsp.toNat + 136) →
      ¬(vsp.toNat + 96 ≤ a ∧ a < vsp.toNat + 104) →
      ¬(vsp.toNat + 16 ≤ a ∧ a < vsp.toNat + 24) →
      ¬(vsp.toNat ≤ a ∧ a < vsp.toNat + 8) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      Vsa.Sim.Code.SvfprintfSliceLoaded c'.σ.mem ∧
      Vsa.Sim.Code.MemsetLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__locale_mb_cur_maxLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__ascii_mbtowcLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hoff0 : (vsp + sign_extend (m := 64) (0x000#12)).toNat = vsp.toNat := by
    rw [sext0_add_pro]
  have hoffloc : ((0x8001b798#64 : BitVec 64) + sign_extend (m := 64) (0x0e8#12)).toNat
      = (0x8001b880 : Nat) := by decide
"""

for K, off in [(40, 0x028), (64, 0x040), (88, 0x058), (104, 0x068), (128, 0x080),
               (96, 0x060), (16, 0x010)]:
    stmt += (f"  have hoff{K} : (vsp + sign_extend (m := 64) (0x{off:03x}#12)).toNat"
             f" = vsp.toNat + {K} := ptr_addoff vsp _ {K} (by decide) (by omega)\n")

pins_list = ", ".join(f"⟨Register.{r}, {v}⟩" for r, v in pins)
pins_hyps = ", ".join(f"hx{r[1:]}" for r, _ in pins)
hp0 = (f"  have hp0 : PinsHold c.σ [{pins_list}] :=\n"
       f"    ⟨{pins_hyps}, trivial⟩\n")

hdr = """import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.SnprintfSitesRet

/-!
# M3 Layer-3 — `SnprintfSpec31` : svfprintf prologue segment E
## `0x800076f4 → 0x80007728` (the `jal __locale_mb_cur_max`)

Zero inits of the parse-state slots (incl. the TOTAL at `sp+16` — Spec26's
`htotS`), `s1 := &__global_locale`, the `'%'`/`16` constants, the fmt spill
`sd s6,0(sp)` and its immediate reload, and the static `mbtowc` function
pointer load `ld s4,232(s1)` (the parse loop's indirect callee).
Generated in the SnprintfSpec22 house style by /tmp/gen_spec31.py.
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
open("Vsa/Sim/SnprintfSpec31.lean", "w").write(out)
print("wrote Vsa/Sim/SnprintfSpec31.lean", len(out.splitlines()), "lines")
