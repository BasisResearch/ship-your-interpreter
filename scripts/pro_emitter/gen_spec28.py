#!/usr/bin/env python3
import sys
sys.path.insert(0, "/tmp")
from emit_pro_seg import Seg

pins = [
    ("x2", "vsp"), ("x3", "(0x8001b510#64)"), ("x8", "va0"), ("x9", "vfile"),
    ("x22", "vfmt"), ("x10", "(0x80019770#64)"),
    ("x18", "vS2o"), ("x19", "vS3o"), ("x20", "vS4o"), ("x21", "vS5o"),
    ("x23", "vS7o"), ("x24", "vS8o"), ("x25", "vS9o"), ("x26", "vS10o"),
    ("x27", "vS11o"),
]
S = Seg(pins)

# loaded tracking: (name, pred, w8-survival)
LOADEDS = [
    ("hsl", "Vsa.Sim.Code.SvfprintfSliceLoaded", "svfprintfSlice_writeMap8_sn5"),
    ("hstr", "Vsa.Sim.Code.StrlenLoaded", "strlen_w8_pro"),
    ("hms", "Vsa.Sim.Code.MemsetLoaded", "memset_w8_pro"),
    ("hlm", "Vsa.Sim.Code.__locale_mb_cur_maxLoaded", "localemb_w8_pro"),
    ("hamb", "Vsa.Sim.Code.__ascii_mbtowcLoaded", "amb_w8_pro"),
]


def st(*a, **kw):
    kw.pop("track_hoff", None)
    S.step(*a, **kw)


def dshow(lhs, rhs):
    return f"show {lhs} = ({rhs} : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide"


# 1: jal strlen
st(0x8000768c, "jal", "site_8000768c_pr", hyps="hsl0 rfl", nextpc=0x80006cf0, pcrw="jal",
   rd="x1", rdval="(0x80007690#64)",
   rdrw="show BitVec.addInt (0x8000768c#64) 4 = (0x80007690#64 : BitVec 64) from by"
        " apply BitVec.eq_of_toNat_eq; decide",
   track=True, comment="jal strlen")

# strlen body (concrete pointer 0x80019770, string \".\")
st(0x80006cf0, "alu", "site_80006cf0", vals="(0x80019770#64)", hyps="$p:x10 ($mE ▸ hstr0) rfl",
   nextpc=0x80006cf4, rd="x15", rdval="(0#64)",
   rdrw=dshow("(0x80019770#64 : BitVec 64) &&& sign_extend (m := 64) (0x007#12)", "0#64"),
   track=True, comment="andi a5,a0,7 (aligned)")
st(0x80006cf4, "alu", "site_80006cf4", vals="(0x80019770#64)", hyps="$p:x10 ($mE ▸ hstr0) rfl",
   nextpc=0x80006cf8, rd="x14", rdval="(0x80019770#64)",
   rdrw="sext0_add_pro (0x80019770#64)", track=True, comment="mv a4,a0")
st(0x80006cf8, "bnottaken", "site_80006cf8_nottaken", vals="(0#64)",
   hyps="$p:x15 ($mE ▸ hstr0) rfl (by decide)", nextpc=0x80006cfc,
   comment="bnez a5 NOT taken")
st(0x80006cfc, "alu", "site_80006cfc", hyps="($mE ▸ hstr0) rfl", nextpc=0x80006d00,
   rd="x15", rdval="(0x7f7f8000#64)",
   rdrw=dshow("(sign_extend (m := 64) ((0x7f7f8#20) +++ 0x000#12) : BitVec 64)",
              "0x7f7f8000#64"),
   track=True, comment="lui a5,0x7f7f8")
st(0x80006d00, "alu", "site_80006d00", vals="(0x7f7f8000#64)", hyps="$p:x15 ($mE ▸ hstr0) rfl",
   nextpc=0x80006d04, rd="x15", rdval="(0x7f7f7f7f#64)",
   rdrw=dshow("(0x7f7f8000#64 : BitVec 64) + sign_extend (m := 64) (0xf7f#12)",
              "0x7f7f7f7f#64"),
   track=True, comment="addi a5,a5,-129 (magic lo)")
st(0x80006d04, "alu", "site_80006d04", vals="(0x7f7f7f7f#64)", hyps="$p:x15 ($mE ▸ hstr0) rfl",
   nextpc=0x80006d08, rd="x13", rdval="(0x7f7f7f7f00000000#64)",
   rdrw=dshow("shift_bits_left (0x7f7f7f7f#64 : BitVec 64)"
              " (Sail.BitVec.extractLsb (0x20#6) 5 0)", "0x7f7f7f7f00000000#64"),
   track=True, comment="slli a3,a5,0x20")
st(0x80006d08, "alu", "site_80006d08", vals="(0x7f7f7f7f00000000#64) (0x7f7f7f7f#64)",
   hyps="$p:x13 $p:x15 ($mE ▸ hstr0) rfl", nextpc=0x80006d0c,
   rd="x13", rdval="(0x7f7f7f7f7f7f7f7f#64)",
   rdrw=dshow("(0x7f7f7f7f00000000#64 : BitVec 64) + (0x7f7f7f7f#64)",
              "0x7f7f7f7f7f7f7f7f#64"),
   track=True, comment="add a3,a3,a5 (magic)")
st(0x80006d0c, "alu", "site_80006d0c", hyps="($mE ▸ hstr0) rfl", nextpc=0x80006d10,
   rd="x11", rdval="(0xffffffffffffffff#64)",
   rdrw=dshow("((0#64) : BitVec 64) + sign_extend (m := 64) (0xfff#12)",
              "0xffffffffffffffff#64"),
   track=True, comment="li a1,-1")
st(0x80006d10, "alu", "site_80006d10", vals="(0x80019770#64)",
   hyps="$p:x14 ($mE ▸ hstr0) rfl (by rw [hoffdb]; omega) (by rw [hoffdb]; omega)"
        " (by rw [hoffdb, htoh]; omega) (by rw [hoffdb])",
   nextpc=0x80006d14,
   pre=["have hldval : (sign_extend (m := 64) (ldBytesT (afterNextPC (afterPrelude σ$K)"
        " (0x80006d10#64)) ((0x80019770#64) + sign_extend (m := 64) (0x000#12)))"
        " : BitVec 64) = (0x2e#64) := by",
        "  rw [ldBytesT_wordAt, mem_afterNextPC, hoffdb]",
        "  unfold strlenWordAt",
        "  rw [$mE, hdb0, hdb1, hdb2, hdb3, hdb4, hdb5, hdb6, hdb7]",
        "  simp only [Option.getD_some]",
        "  apply BitVec.eq_of_toNat_eq; decide"],
   rd="x12", rdval="(0x2e#64)", rdrw="hldval",
   track=True, comment="ld a2,0(a4) — total word load of \". \\0…\"")
st(0x80006d14, "alu", "site_80006d14", vals="(0x80019770#64)", hyps="$p:x14 ($mE ▸ hstr0) rfl",
   nextpc=0x80006d18, rd="x14", rdval="(0x80019778#64)",
   rdrw=dshow("(0x80019770#64 : BitVec 64) + sign_extend (m := 64) (0x008#12)",
              "0x80019778#64"),
   track=True, comment="addi a4,a4,8")
st(0x80006d18, "alu", "site_80006d18", vals="(0x2e#64) (0x7f7f7f7f7f7f7f7f#64)",
   hyps="$p:x12 $p:x13 ($mE ▸ hstr0) rfl", nextpc=0x80006d1c,
   rd="x15", rdval="(0x2e#64)",
   rdrw=dshow("(0x2e#64 : BitVec 64) &&& (0x7f7f7f7f7f7f7f7f#64)", "0x2e#64"),
   track=True, comment="and a5,a2,a3")
st(0x80006d1c, "alu", "site_80006d1c", vals="(0x2e#64) (0x7f7f7f7f7f7f7f7f#64)",
   hyps="$p:x15 $p:x13 ($mE ▸ hstr0) rfl", nextpc=0x80006d20,
   rd="x15", rdval="(0x7f7f7f7f7f7f7fad#64)",
   rdrw=dshow("(0x2e#64 : BitVec 64) + (0x7f7f7f7f7f7f7f7f#64)", "0x7f7f7f7f7f7f7fad#64"),
   track=True, comment="add a5,a5,a3")
st(0x80006d20, "alu", "site_80006d20", vals="(0x7f7f7f7f7f7f7fad#64) (0x2e#64)",
   hyps="$p:x15 $p:x12 ($mE ▸ hstr0) rfl", nextpc=0x80006d24,
   rd="x15", rdval="(0x7f7f7f7f7f7f7faf#64)",
   rdrw=dshow("(0x7f7f7f7f7f7f7fad#64 : BitVec 64) ||| (0x2e#64)", "0x7f7f7f7f7f7f7faf#64"),
   track=True, comment="or a5,a5,a2")
st(0x80006d24, "alu", "site_80006d24", vals="(0x7f7f7f7f7f7f7faf#64) (0x7f7f7f7f7f7f7f7f#64)",
   hyps="$p:x15 $p:x13 ($mE ▸ hstr0) rfl", nextpc=0x80006d28,
   rd="x15", rdval="(0x7f7f7f7f7f7f7fff#64)",
   rdrw=dshow("(0x7f7f7f7f7f7f7faf#64 : BitVec 64) ||| (0x7f7f7f7f7f7f7f7f#64)",
              "0x7f7f7f7f7f7f7fff#64"),
   track=True, comment="or a5,a5,a3")
st(0x80006d28, "bnottaken", "site_80006d28_nottaken",
   vals="(0x7f7f7f7f7f7f7fff#64) (0xffffffffffffffff#64)",
   hyps="$p:x15 $p:x11 ($mE ▸ hstr0) rfl (by decide)", nextpc=0x80006d2c,
   comment="beq a5,a1 NOT taken (NUL present)")
st(0x80006d2c, "alu", "site_80006d2c", vals="(0x80019778#64) _",
   hyps="$p:x14 ($mE ▸ hstr0) rfl (by rw [hoffm8]; omega) (by rw [hoffm8]; omega)"
        " (by rw [hoffm8, htoh]; omega) (by rw [hoffm8, $mE]; exact hdb0)",
   nextpc=0x80006d30, rd="x15", rdval="(0x2e#64)",
   rdrw=dshow("(zero_extend (m := 64) (0x2e#8) : BitVec 64)", "0x2e#64"),
   track=True, comment="lbu a5,-8(a4) — byte 0 = '.'")
st(0x80006d30, "alu", "site_80006d30", vals="(0x80019778#64) (0x80019770#64)",
   hyps="$p:x14 $p:x10 ($mE ▸ hstr0) rfl", nextpc=0x80006d34,
   rd="x13", rdval="(8#64)",
   rdrw=dshow("(0x80019778#64 : BitVec 64) - (0x80019770#64)", "8#64"),
   track=True, comment="sub a3,a4,a0")
st(0x80006d34, "bnottaken", "site_80006d34_nottaken", vals="(0x2e#64)",
   hyps="$p:x15 ($mE ▸ hstr0) rfl (by decide)", nextpc=0x80006d38,
   comment="beqz a5 NOT taken ('.' ≠ 0)")
st(0x80006d38, "alu", "site_80006d38", vals="(0x80019778#64) _",
   hyps="$p:x14 ($mE ▸ hstr0) rfl (by rw [hoffm7]; omega) (by rw [hoffm7]; omega)"
        " (by rw [hoffm7, htoh]; omega) (by rw [hoffm7, $mE]; exact hdb1)",
   nextpc=0x80006d3c, rd="x15", rdval="(0#64)",
   rdrw=dshow("(zero_extend (m := 64) (0x00#8) : BitVec 64)", "0#64"),
   track=True, comment="lbu a5,-7(a4) — the NUL")
st(0x80006d3c, "btaken", "site_80006d3c_taken", vals="(0#64)",
   hyps="$p:x15 ($mE ▸ hstr0) rfl (by decide)", nextpc=0x80006d94,
   pcrw=("btshow", 0x0058), comment="beqz a5 TAKEN → byte-1 exit")
st(0x80006d94, "alu", "site_80006d94", vals="(8#64)", hyps="$p:x13 ($mE ▸ hstr0) rfl",
   nextpc=0x80006d98, rd="x10", rdval="(1#64)",
   rdrw=dshow("(8#64 : BitVec 64) + sign_extend (m := 64) (0xff9#12)", "1#64"),
   track=True, comment="addi a0,a3,-7 — strlen(\".\") = 1")
st(0x80006d98, "jr", "site_80006d98", vals="(0x80007690#64)",
   hyps="$p:x1 ($mE ▸ hstr0) rfl (by rw [ret_tgt _ (by decide)]; decide)",
   nextpc=0x80007690, pcrw="ret", comment="ret (back to 0x80007690)")

# back in svfprintf
st(0x80007690, "store", "site_80007690_pr", vals="vsp _",
   hyps="$p:x2 $p:x10 ($mE ▸ hsl0) rfl (by rw [hoff72]; omega) (by rw [hoff72]; omega)"
        " (by rw [hoff72, htoh]; omega) (by rw [hoff72]; omega)",
   nextpc=0x80007694,
   memw=("w8", "vsp.toNat + 72", "sdData_val (1#64)", ["hoff72"]),
   track_hoff="hoff72",
   comment="sd a0,72(sp) — strlen result spill")
S.emit("""  have hslA : Vsa.Sim.Code.SvfprintfSliceLoaded σ24.mem := by
    rw [hmem24, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff72]; omega) (hmE23 ▸ hsl0)
""")
st(0x80007694, "alu", "site_80007694_pr", hyps="hslA rfl", nextpc=0x80007698,
   rd="x12", rdval="(8#64)",
   rdrw=dshow("((0#64) : BitVec 64) + sign_extend (m := 64) (0x008#12)", "8#64"),
   track=True, comment="li a2,8")
S.emit("  have hslB : Vsa.Sim.Code.SvfprintfSliceLoaded σ25.mem := hmem25 ▸ hslA")
st(0x80007698, "alu", "site_80007698_pr", vals="vsp", hyps="$p:x2 hslB rfl",
   nextpc=0x8000769c, rd="x10", rdval="vsp + sign_extend (m := 64) (0x0c8#12)",
   track=True, comment="addi a0,sp,200")
S.emit("  have hslC : Vsa.Sim.Code.SvfprintfSliceLoaded σ26.mem := hmem26 ▸ hslB")
st(0x8000769c, "alu", "site_8000769c_pr", hyps="hslC rfl", nextpc=0x800076a0,
   rd="x11", rdval="(0#64)",
   rdrw="sext0_add_pro (0#64)", track=True, comment="li a1,0")

N = S.k
assert N == 27, N

post = []
post.append(f"""  have hslN : Vsa.Sim.Code.SvfprintfSliceLoaded σ{N}.mem := hmem27 ▸ hslC
  have hmsN : Vsa.Sim.Code.MemsetLoaded σ{N}.mem := by
    rw [hmE{N}]
    exact memset_w8_pro _ _ _ (by omega) hms0
  have hlmN : Vsa.Sim.Code.__locale_mb_cur_maxLoaded σ{N}.mem := by
    rw [hmE{N}]
    exact localemb_w8_pro _ _ _ (by omega) hlm0
  have hambN : Vsa.Sim.Code.__ascii_mbtowcLoaded σ{N}.mem := by
    rw [hmE{N}]
    exact amb_w8_pro _ _ _ (by omega) hamb0
  have hS048 : SlotHolds vsp 0x048 (1#64) σ{N}.mem := by
    rw [hmE{N}]
    exact slot_save vsp 0x048 (1#64) _ _ _ hoff72 rfl
  have hagN : ∀ a : Nat, ¬(vsp.toNat + 72 ≤ a ∧ a < vsp.toNat + 80) →
      σ{N}.mem[a]? = c.σ.mem[a]? := by
    intro a hw0
    rw [hmE{N}, getElem?_writeMap8_out _ (vsp.toNat + 72) _ a (by omega)]""")

refine_items = [
    f"hG{N}", f"hpc{N}",
    "$p:x2", "$p:x1", "$p:x3", "$p:x8", "$p:x9", "$p:x22",
    "$p:x10", "$p:x11", "$p:x12",
    "$p:x18", "$p:x19", "$p:x20", "$p:x21", "$p:x23",
    "$p:x24", "$p:x25", "$p:x26", "$p:x27",
    "hS048", "hagN", "hslN", "hmsN", "hlmN", "hambN",
    f"hi{N}", f"⟨vmi{N}, hmi{N}⟩",
]

core = "\n".join(S.out + post) + "\n"
tail_items = ",\n    ".join(S.subst(x, f"hp{N}", f"hmE{N}", N) for x in refine_items)
core += f"  refine ⟨⟨σ{N}, i{N}, c.steps + {N}⟩, ?_,\n    {tail_items}⟩\n"
chain = f"(Steps.single hstep{N})"
for j in range(N - 1, 0, -1):
    chain = f"((Steps.single hstep{j}).trans {chain})"
core += "  exact " + chain[1:-1] + "\n"

stmt = """/-- **Segment B of the svfprintf prologue**: `0x8000768c → 0x800076a0`.

The `jal strlen` with the whole concrete `strlen(".")` execution inlined
(aligned word probe of the static decimal-point string at `0x80019770`,
magic-constant NUL detection, byte-tail exit at `0x80006d94`, result `1`),
the spill of the result to `sp+72`, and the `memset` argument setup
(`a2 := 8`, `a0 := sp+200`, `a1 := 0`); stops poised at the `jal memset`. -/
theorem svfProB_spec
    (vsp va0 vfile vfmt : BitVec 64)
    (vS2o vS3o vS4o vS5o vS7o vS8o vS9o vS10o vS11o : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : Vsa.Sim.Code.SvfprintfSliceLoaded c.σ.mem)
    (hstr0 : Vsa.Sim.Code.StrlenLoaded c.σ.mem)
    (hms0 : Vsa.Sim.Code.MemsetLoaded c.σ.mem)
    (hlm0 : Vsa.Sim.Code.__locale_mb_cur_maxLoaded c.σ.mem)
    (hamb0 : Vsa.Sim.Code.__ascii_mbtowcLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x8000768c#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx8 : c.σ.regs.get? Register.x8 = some va0)
    (hx9 : c.σ.regs.get? Register.x9 = some vfile)
    (hx22 : c.σ.regs.get? Register.x22 = some vfmt)
    (hx10 : c.σ.regs.get? Register.x10 = some (0x80019770#64))
    (hx18 : c.σ.regs.get? Register.x18 = some vS2o)
    (hx19 : c.σ.regs.get? Register.x19 = some vS3o)
    (hx20 : c.σ.regs.get? Register.x20 = some vS4o)
    (hx21 : c.σ.regs.get? Register.x21 = some vS5o)
    (hx23 : c.σ.regs.get? Register.x23 = some vS7o)
    (hx24 : c.σ.regs.get? Register.x24 = some vS8o)
    (hx25 : c.σ.regs.get? Register.x25 = some vS9o)
    (hx26 : c.σ.regs.get? Register.x26 = some vS10o)
    (hx27 : c.σ.regs.get? Register.x27 = some vS11o)
    -- the static "." decimal-point string bytes at 0x80019770
    (hdb0 : c.σ.mem[(0x80019770 : Nat)]? = some (0x2e#8))
    (hdb1 : c.σ.mem[(0x80019770 : Nat) + 1]? = some (0x00#8))
    (hdb2 : c.σ.mem[(0x80019770 : Nat) + 2]? = some (0x00#8))
    (hdb3 : c.σ.mem[(0x80019770 : Nat) + 3]? = some (0x00#8))
    (hdb4 : c.σ.mem[(0x80019770 : Nat) + 4]? = some (0x00#8))
    (hdb5 : c.σ.mem[(0x80019770 : Nat) + 5]? = some (0x00#8))
    (hdb6 : c.σ.mem[(0x80019770 : Nat) + 6]? = some (0x00#8))
    (hdb7 : c.σ.mem[(0x80019770 : Nat) + 7]? = some (0x00#8))
    (hsplo : 0x8001c000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x800076a0#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x1 = some (0x80007690#64) ∧
      c'.σ.regs.get? Register.x3 = some (0x8001b510#64) ∧
      c'.σ.regs.get? Register.x8 = some va0 ∧
      c'.σ.regs.get? Register.x9 = some vfile ∧
      c'.σ.regs.get? Register.x22 = some vfmt ∧
      c'.σ.regs.get? Register.x10 = some (vsp + sign_extend (m := 64) (0x0c8#12)) ∧
      c'.σ.regs.get? Register.x11 = some (0#64) ∧
      c'.σ.regs.get? Register.x12 = some (8#64) ∧
      c'.σ.regs.get? Register.x18 = some vS2o ∧
      c'.σ.regs.get? Register.x19 = some vS3o ∧
      c'.σ.regs.get? Register.x20 = some vS4o ∧
      c'.σ.regs.get? Register.x21 = some vS5o ∧
      c'.σ.regs.get? Register.x23 = some vS7o ∧
      c'.σ.regs.get? Register.x24 = some vS8o ∧
      c'.σ.regs.get? Register.x25 = some vS9o ∧
      c'.σ.regs.get? Register.x26 = some vS10o ∧
      c'.σ.regs.get? Register.x27 = some vS11o ∧
      SlotHolds vsp 0x048 (1#64) c'.σ.mem ∧
      (∀ a : Nat, ¬(vsp.toNat + 72 ≤ a ∧ a < vsp.toNat + 80) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      Vsa.Sim.Code.SvfprintfSliceLoaded c'.σ.mem ∧
      Vsa.Sim.Code.MemsetLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__locale_mb_cur_maxLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__ascii_mbtowcLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hoff72 : (vsp + sign_extend (m := 64) (0x048#12)).toNat = vsp.toNat + 72 :=
    ptr_addoff vsp _ 72 (by decide) (by omega)
  have hoffdb : ((0x80019770#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)).toNat
      = (0x80019770 : Nat) := by decide
  have hoffm8 : ((0x80019778#64 : BitVec 64) + sign_extend (m := 64) (0xff8#12)).toNat
      = (0x80019770 : Nat) := by decide
  have hoffm7 : ((0x80019778#64 : BitVec 64) + sign_extend (m := 64) (0xff9#12)).toNat
      = (0x80019770 : Nat) + 1 := by decide
"""

pins_list = ", ".join(f"⟨Register.{r}, {v}⟩" for r, v in pins)
pins_hyps = ", ".join(f"hx{r[1:]}" for r, _ in pins)
hp0 = (f"  have hp0 : PinsHold c.σ [{pins_list}] :=\n"
       f"    ⟨{pins_hyps}, trivial⟩\n")

hdr = """import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.StrlenSites
import Vsa.Sim.StrlenSpec

/-!
# M3 Layer-3 — `SnprintfSpec28` : svfprintf prologue segment B
## `0x8000768c` (the `jal strlen`) → `0x800076a0` (the `jal memset`)

`strlen(decimal_point)` for the concrete static string `"."` at `0x80019770`
(from `_localeconv_r`), fully inlined (22 `StrlenSites` steps: aligned entry,
one magic word probe, byte tail, exit `a0 = 1`), the result spill to `sp+72`,
and the `memset(sp+200, 0, 8)` argument setup.
Generated in the SnprintfSpec22 house style by /tmp/gen_spec28.py.
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
open("Vsa/Sim/SnprintfSpec28.lean", "w").write(out)
print("wrote Vsa/Sim/SnprintfSpec28.lean", len(out.splitlines()), "lines")
