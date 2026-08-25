#!/usr/bin/env python3
"""Emit Vsa/Sim/SnprintfSpec46.lean — `exitToPrintNN_spec`: the NONNEG twin of
SnprintfSpec7's `exitToPrint_spec` (0x80008358 → 0x8000782c).

Derivation: Spec7's statement + proof steps 1-16 VERBATIM (the exit-restore
block through `j 0x8000812c`), then the seam with `beqz t5` **TAKEN** (the sign
slot holds 0x00 — no sign byte), skipping the `addiw a6,a6,1` bump: `a6 = len`.
Steps 17-22: 812c beqz-taken → 8088 bnez-nt → 808c j → a830 sd → a834 sd →
a838 j → 0x8000782c.
"""
import re, pathlib

SRC = pathlib.Path("Vsa/Sim/SnprintfSpec7.lean").read_text()

# ---- head: statement + steps 1-16 ----
CUT = "  -- === 812c: beq t5,zero NOT taken ==="
try:
    start = SRC.index("theorem exitToPrint_spec")
except ValueError:
    raise SystemExit("theorem not found")
# include the docstring? start from the theorem keyword; write our own docstring.
head = SRC[SRC.index("theorem exitToPrint_spec"):SRC.index(CUT)]

# statement edits
head = head.replace("theorem exitToPrint_spec", "theorem exitToPrintNN_spec", 1)
old_sbne = ("    (hsbne : ((zero_extend (m := 64) sb : BitVec 64) == (0#64)) = false)\n")
new_sbz = ("    (hsbz : ((zero_extend (m := 64) sb : BitVec 64) == (0#64)) = true)\n")
assert old_sbne in head
head = head.replace(old_sbne, new_sbz)
old_x16 = """      c'.σ.regs.get? Register.x16 = some (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((sign_extend (m := 64)
          ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0)))
          + sign_extend (m := 64) (0x001#12)) 31 0)) ∧"""
new_x16 = """      c'.σ.regs.get? Register.x16 = some (sign_extend (m := 64)
        ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) ∧"""
assert old_x16 in head
head = head.replace(old_x16, new_x16)

LEN = ("(sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - "
       "(Sail.BitVec.extractLsb vcur 31 0)))")
SB64 = "(zero_extend (m := 64) sb)"

# ---- generated tail: steps 17-22 ----
L = []
def emit(*lines): L.extend(lines)

track = {"2": "vsp", "20": "vwidth", "6": "vflags", "16": LEN, "22": LEN,
         "28": "vt3v", "23": "vs7v", "8": "vs0v", "30": SB64, "31": "(0#64)"}

def steps_expr(k): return "c.steps" + "+1" * k

OBS_OTHER = {"bt": "obs_btaken_other", "bnt": "obs_bnottaken_other",
             "j": "obs_jr_other"}

def thread_regs(k, cls):
    for r, val in track.items():
        prev = f"hx{r}_{k-1}"
        if cls == "store":
            emit(f"  have hx{r}_{k} : σ{k}.regs.get? Register.x{r} = some {val} :=",
                 f"    obs_store_other_sn4 Register.x{r} hobs{k} (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) {prev}")
        else:
            dec = " ".join(["(by decide)"] * 7)
            emit(f"  have hx{r}_{k} : σ{k}.regs.get? Register.x{r} = some {val} :=",
                 f"    {OBS_OTHER[cls]} hobs{k} Register.x{r} {dec} {prev}")

def minstret(k, cls):
    if cls == "bt":
        emit(f"  obtain ⟨vmi{k}, hmi{k}⟩ := obs_btaken_minstret hobs{k}")
    elif cls == "bnt":
        emit(f"  obtain ⟨vmi{k}, hmi{k}⟩ := obs_bnottaken_minstret hobs{k}")
    elif cls == "store":
        emit(f"  obtain ⟨vmi{k}, hmi{k}⟩ := obs_store_minstret_sn4 hobs{k}")
    elif cls == "j":
        emit(f"  obtain ⟨vmi{k}, hmi{k}⟩ := hG{k}.minstret")

def hdr(k, addr, comment, site, args, hyps):
    emit(f"  -- === 0x{addr:x}: {comment} ===")
    emit(f"  obtain ⟨σ{k}, i{k}, hs{k}, hi{k}, hG{k}, hmem{k}, hobs{k}⟩ :=",
         f"    {site} σ{k-1} i{k-1} ({steps_expr(k-1)}) (0x{addr:08x}#64) vmi{k-1} {args}".rstrip(),
         f"      {hyps}")
    emit(f"  have hstep{k} : Step ⟨σ{k-1},i{k-1},{steps_expr(k-1)}⟩ ⟨σ{k},i{k},{steps_expr(k)}⟩ := hs{k}")

def mem_id(k):
    emit(f"  have hload{k} : SvfprintfSliceLoaded σ{k}.mem := hmem{k} ▸ hload{k-1}")
    emit(f"  have hfp{k} : FlushPinsLoaded σ{k}.mem := hmem{k} ▸ hfp{k-1}")

def mem_w8(k, addr, hoff):
    emit(f"  have hNP{k-1}b : (afterNextPC (afterPrelude σ{k-1}) (0x{addr:08x}#64)).mem = σ{k-1}.mem := rfl")
    emit(f"  have hload{k} : SvfprintfSliceLoaded σ{k}.mem := by",
         f"    rw [hmem{k}, hNP{k-1}b]; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [{hoff}]; omega) hload{k-1}")
    emit(f"  have hfp{k} : FlushPinsLoaded σ{k}.mem := by",
         f"    rw [hmem{k}, hNP{k-1}b]; exact flushPins_writeMap8_fl _ _ _ (by rw [{hoff}]; omega) hfp{k-1}")

# aliases so thread_regs's hx{r}_16 names exist
emit("  -- name aliases for the seam threading",
     "  have hx20_16 := hx20w_16",
     "  have hx6_16 := hx6w_16",
     "  have hx28_16 := hx28w_16",
     "  have hx23_16 := hx23w_16",
     "  have hx8_16 := hx8w_16",
     "")

# step 17: 812c beqz t5 TAKEN
hdr(17, 0x8000812c, "beq t5,zero TAKEN (no sign byte)",
    "site_8000812c_taken_fs", SB64,
    "hG16 hpc16 hmi16 hx30_16 hload16 rfl hsbz hi16")
emit("  have hpc17 : σ17.regs.get? Register.PC = some (0x80008088#64) := by",
     "    have := obs_btaken_pc hobs17",
     "    rwa [site_8000812c_taken_fs_tgt] at this")
minstret(17, "bt")
thread_regs(17, "bt")
mem_id(17)
emit("")

# step 18: 8088 bnez t6 NOT taken
hdr(18, 0x80008088, "bne t6,zero NOT taken", "site_80008088_nottaken_fl", "(0#64)",
    "hG17 hpc17 hmi17 hx31_17 hload17 rfl (by decide) hi17")
emit("  have hpc18 : σ18.regs.get? Register.PC = some (0x8000808c#64) := by",
     "    have := obs_bnottaken_pc hobs18",
     "    rwa [show BitVec.addInt (0x80008088#64 : BitVec 64) 4 = (0x8000808c#64 : BitVec 64) from by",
     "      apply BitVec.eq_of_toNat_eq; decide] at this")
minstret(18, "bnt")
thread_regs(18, "bnt")
mem_id(18)
emit("")

# step 19: 808c j a830
hdr(19, 0x8000808c, "j 0x8000a830", "site_8000808c_fl", "",
    "hG18 hpc18 hmi18 hload18 rfl (by decide) hi18")
emit("  have hpc19 : σ19.regs.get? Register.PC = some (0x8000a830#64) := by",
     "    have := obs_jx0_pc_sn5 hobs19",
     "    rwa [show (0x8000808c#64 : BitVec 64) + sign_extend (m := 64) (0x0027a4#21)",
     "      = (0x8000a830#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this")
minstret(19, "j")
thread_regs(19, "j")
mem_id(19)
emit("")

# step 20: a830 sd zero,56(sp)
hdr(20, 0x8000a830, "sd zero,56(sp)", "site_8000a830_fl", "vsp",
    "hG19 hpc19 hmi19 hx2_19 hfp19 rfl (by rw [hoff56]; omega) (by rw [hoff56]; omega) (by rw [hoff56]; omega) (by rw [hoff56]; omega) hi19")
emit("  have hpc20 : σ20.regs.get? Register.PC = some (0x8000a834#64) := by",
     "    have := obs_store_pc_sn4 hobs20",
     "    rwa [show BitVec.addInt (0x8000a830#64 : BitVec 64) 4 = (0x8000a834#64 : BitVec 64) from by",
     "      apply BitVec.eq_of_toNat_eq; decide] at this")
minstret(20, "store")
thread_regs(20, "store")
mem_w8(20, 0x8000a830, "hoff56")
emit("")

# step 21: a834 sd zero,48(sp)
hdr(21, 0x8000a834, "sd zero,48(sp)", "site_8000a834_fl", "vsp",
    "hG20 hpc20 hmi20 hx2_20 hfp20 rfl (by rw [hoff48]; omega) (by rw [hoff48]; omega) (by rw [hoff48]; omega) (by rw [hoff48]; omega) hi20")
emit("  have hpc21 : σ21.regs.get? Register.PC = some (0x8000a838#64) := by",
     "    have := obs_store_pc_sn4 hobs21",
     "    rwa [show BitVec.addInt (0x8000a834#64 : BitVec 64) 4 = (0x8000a838#64 : BitVec 64) from by",
     "      apply BitVec.eq_of_toNat_eq; decide] at this")
minstret(21, "store")
thread_regs(21, "store")
mem_w8(21, 0x8000a834, "hoff48")
emit("")

# step 22: a838 j 782c
hdr(22, 0x8000a838, "j 0x8000782c — the PRINT entry", "site_8000a838_fl", "",
    "hG21 hpc21 hmi21 hfp21 rfl (by decide) hi21")
emit("  have hpc22 : σ22.regs.get? Register.PC = some (0x8000782c#64) := by",
     "    have := obs_jx0_pc_sn5 hobs22",
     "    rwa [show (0x8000a838#64 : BitVec 64) + sign_extend (m := 64) (0x1fcff4#21)",
     "      = (0x8000782c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this")
minstret(22, "j")
thread_regs(22, "j")
mem_id(22)
emit("")

# post
emit("""  -- slot sp+0x20 := 0 (σ15's `sd zero,32(sp)`), transported to σ22
  have hs32z_22 : SlotHolds vsp 0x020 (0#64) σ22.mem := by
    have h15 : SlotHolds vsp 0x020 (0#64) σ15.mem := by
      rw [hmem15, hNP14]
      exact slotHolds_self vsp 0x020 _ (0#64) σ14.mem rfl
    have h19 : SlotHolds vsp 0x020 (0#64) σ19.mem := by
      rw [hmem19, hmem18, hmem17, hmem16]; exact h15
    have h20 : SlotHolds vsp 0x020 (0#64) σ20.mem := by
      rw [hmem20, hNP19b]
      exact slotHolds_writeMap8 vsp 0x020 (0#64) σ19.mem _ _ (by rw [hoff32, hoff56]; omega) h19
    have h21 : SlotHolds vsp 0x020 (0#64) σ21.mem := by
      rw [hmem21, hNP20b]
      exact slotHolds_writeMap8 vsp 0x020 (0#64) σ20.mem _ _ (by rw [hoff32, hoff48]; omega) h20
    rw [hmem22]; exact h21
  -- mid-register (+ x26) preservation across all 22 steps
  have hkeep22 : KeepRegs (Register.x26 :: midRegs5) c.σ σ22 := by
    have h0 := keep_rfl (Register.x26 :: midRegs5) c.σ
    have h1 := keep_alu hobs1 (by decide) h0
    have h2 := keep_store hobs2 (by decide) h1
    have h3 := keep_alu hobs3 (by decide) h2
    have h4 := keep_alu hobs4 (by decide) h3
    have h5 := keep_alu hobs5 (by decide) h4
    have h6 := keep_store hobs6 (by decide) h5
    have h7 := keep_alu hobs7 (by decide) h6
    have h8 := keep_alu hobs8 (by decide) h7
    have h9 := keep_alu hobs9 (by decide) h8
    have h10 := keep_alu hobs10 (by decide) h9
    have h11 := keep_bnottaken hobs11 (by decide) h10
    have h12 := keep_alu hobs12 (by decide) h11
    have h13 := keep_alu hobs13 (by decide) h12
    have h14 := keep_alu hobs14 (by decide) h13
    have h15 := keep_store hobs15 (by decide) h14
    have h16 := keep_jr hobs16 (by decide) h15
    have h17 := keep_btaken hobs17 (by decide) h16
    have h18 := keep_bnottaken hobs18 (by decide) h17
    have h19 := keep_jr hobs19 (by decide) h18
    have h20 := keep_store hobs20 (by decide) h19
    have h21 := keep_store hobs21 (by decide) h20
    exact keep_jr hobs22 (by decide) h21
  -- the pointwise frame outside [sp+32,sp+64) ∪ [sp+104,sp+112)
  have hmframe : ∀ a : Nat, ¬(vsp.toNat + 32 ≤ a ∧ a < vsp.toNat + 64) →
      ¬(vsp.toNat + 104 ≤ a ∧ a < vsp.toNat + 112) →
      σ22.mem[a]? = c.σ.mem[a]? := by
    intro a hA hB
    rw [hmem22, hmem21, hNP20b, getElem?_writeMap8_out _ _ _ _ (by rw [hoff48]; omega),
      hmem20, hNP19b, getElem?_writeMap8_out _ _ _ _ (by rw [hoff56]; omega),
      hmem19, hmem18, hmem17, hmem16,
      hmem15, hNP14, getElem?_writeMap8_out _ _ _ _ (by rw [hoff32]; omega),
      hmem14, hmem13, hmem12, hmem11, hmem10, hmem9, hmem8, hmem7,
      hmem6, hNP5, getElem?_writeMap8_out _ _ _ _ (by rw [hoff40]; omega),
      hmem5, hmem4, hmem3,
      hmem2, hNP1, getElem?_writeMap8_out _ _ _ _ (by rw [hoff104]; omega),
      hmem1]
  have hload22' : SvfprintfSliceLoaded σ22.mem := hload22
  have hfp22' : FlushPinsLoaded σ22.mem := hfp22
  refine ⟨⟨σ22, i22, """ + steps_expr(22) + """⟩, ?_, hG22, hpc22, hx22_22, hx16_22, hx30_22, hx31_22,
    hx20_22, hx6_22, hx28_22, hx23_22, hx8_22, hx2_22, hi22, hG22.minstret,
    hs32z_22, hkeep22, hmframe, hload22', hfp22'⟩""")
chain = "(Steps.single hstep22)"
for j in range(21, 0, -1):
    chain = f"((Steps.single hstep{j}).trans {chain})"
emit("  exact " + chain[1:-1])
emit("", "end Vsa.Sim", "")

DOC = '''import Vsa.Sim.SnprintfSpec7
import Vsa.Sim.SnprintfSitesFast

/-!
# M3 Layer-3 — `SnprintfSpec46` : exit-restore + hops, NONNEG twin (`beqz` taken)

`exitToPrintNN_spec` — `exitToPrint_spec`'s (SnprintfSpec7) twin for the
NON-NEGATIVE arm: same 16-step exit-restore block `0x80008358 → j 0x8000812c`,
but the sign slot holds `0x00`, so the seam `beqz t5` at `0x8000812c` is
**TAKEN** — `a6` stays `len` (no `+1` bump) and the path hops
`0x8088 → 0x8000a830 → 0x8000782c` directly (22 steps total; the neg version's
`addiw a6,a6,1`/`j` pair is not executed).  Statement/steps 1-16 are Spec7's
verbatim (generated from its source by `scripts/pro_emitter/gen_spec46.py`);
the post differs only in `x16 = len` (not len+1).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded SvfprintfSliceLoaded FlushPinsLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- **The exit-restore + hops for the NONNEG arm** (`0x80008358 → 0x8000782c`,
`beqz t5` taken, `a6 = len`). -/
'''

out = DOC + head + "\n".join(L)
pathlib.Path("Vsa/Sim/SnprintfSpec46.lean").write_text(out)
print(f"wrote Vsa/Sim/SnprintfSpec46.lean ({out.count(chr(10))} lines)")
