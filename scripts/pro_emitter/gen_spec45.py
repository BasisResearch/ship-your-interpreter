#!/usr/bin/env python3
"""Emit Vsa/Sim/SnprintfSpec45.lean — `entryToPrintNN_fast_spec`:
the single-digit fast path 0x80008100 → 0x8000782c for the NEGATIVE arm
(sign byte present at sp+167, `beqz t5` at 0x8000812c NOT taken).

21 machine steps:
  8100 li a5,9 ; 8104 bltu nottaken (m ≤ 9) ; 8108 addiw a4,a4,48 ;
  810c sb a4,347(sp) ; 8110 sext.w a6,s4 ; 8114 blez s4 TAKEN → 8ea4 ;
  8ea4 lbu t5,167(sp) ; 8ea8 li a6,1 ; 8eac li t6,0 ; 8eb0 li s6,1 ;
  8eb4 addi s10,sp,347 ; 8eb8 j 8128 ; 8128 sd zero,32(sp) ;
  812c beqz t5 nottaken ; 8130 addiw a6,a6,1 ; 8134 j 8088 ;
  8088 bnez t6 nottaken ; 808c j a830 ; a830 sd zero,56(sp) ;
  a834 sd zero,48(sp) ; a838 j 782c.

House pattern: SnprintfSpec7 (exitToPrint_spec) — the seam steps 14-21 are
that file's steps 17-24 verbatim (renumbered).
"""

L = []
def emit(*lines):
    L.extend(lines)

A4 = ("(sign_extend (m := 64) (Sail.BitVec.extractLsb (w + sign_extend"
      " (m := 64) (0x030#12)) 31 0))")
SB64 = "(zero_extend (m := 64) sb)"
X16A = "((0#64) + sign_extend (m := 64) (0x001#12))"

# tracked registers: name -> (Register field, value expr).  Ordered.
track = {}

def sig(k):
    return "c.σ" if k == 0 else f"σ{k}"

def tick(k):
    return "c.tick" if k == 0 else f"i{k}"

def steps_expr(k):
    return "c.steps" if k == 0 else "c.steps" + "+1" * k

OBS_OTHER = {
    "alu": ("obs_alu_other", 8),
    "bnt": ("obs_bnottaken_other", 7),
    "bt": ("obs_btaken_other", 7),
    "j": ("obs_jr_other", 7),
    "store": None,  # special: obs_store_other_sn4 Register first
}

def thread_regs(k, cls, skip=()):
    for r, (val, _) in track.items():
        if r in skip:
            continue
        prev = f"hx{r}_{k-1}" if k > 1 else f"hx{r}_0"
        if cls == "store":
            emit(f"  have hx{r}_{k} : σ{k}.regs.get? Register.x{r} = some {val} :=",
                 f"    obs_store_other_sn4 Register.x{r} hobs{k} (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) {prev}")
        else:
            name, n = OBS_OTHER[cls]
            dec = " ".join(["(by decide)"] * n)
            emit(f"  have hx{r}_{k} : σ{k}.regs.get? Register.x{r} = some {val} :=",
                 f"    {name} hobs{k} Register.x{r} {dec} {prev}")

def minstret(k, cls):
    if cls == "alu":
        emit(f"  obtain ⟨vmi{k}, hmi{k}⟩ := obs_alu_minstret hobs{k}")
    elif cls == "bnt":
        emit(f"  obtain ⟨vmi{k}, hmi{k}⟩ := obs_bnottaken_minstret hobs{k}")
    elif cls == "bt":
        emit(f"  obtain ⟨vmi{k}, hmi{k}⟩ := obs_btaken_minstret hobs{k}")
    elif cls == "store":
        emit(f"  obtain ⟨vmi{k}, hmi{k}⟩ := obs_store_minstret_sn4 hobs{k}")
    elif cls == "j":
        emit(f"  obtain ⟨vmi{k}, hmi{k}⟩ := hG{k}.minstret")

def pc_add4(k, addr, nxt):
    obs = {"alu": "obs_alu_pc", "bnt": "obs_bnottaken_pc", "store": "obs_store_pc_sn4"}
    emit(f"  have hpc{k} : σ{k}.regs.get? Register.PC = some (0x{nxt:08x}#64) := by",
         f"    have := {obs[CLS]}" + f" hobs{k}",
         f"    rwa [show BitVec.addInt (0x{addr:08x}#64 : BitVec 64) 4 = (0x{nxt:08x}#64 : BitVec 64) from by",
         f"      apply BitVec.eq_of_toNat_eq; decide] at this")

def step_header(k, addr, comment, site, args, hyps):
    emit(f"  -- === 0x{addr:x}: {comment} ===")
    emit(f"  obtain ⟨σ{k}, i{k}, hs{k}, hi{k}, hG{k}, hmem{k}, hobs{k}⟩ :=",
         f"    {site} {sig(k-1)} {tick(k-1)} ({steps_expr(k-1)}) (0x{addr:08x}#64) vmi{k-1} {args}".rstrip(),
         f"      {hyps}")
    if k == 1:
        emit(f"  have hstep1 : Step c ⟨σ1, i1, c.steps+1⟩ := by cases c; exact hs1")
    else:
        emit(f"  have hstep{k} : Step ⟨σ{k-1},i{k-1},{steps_expr(k-1)}⟩ ⟨σ{k},i{k},{steps_expr(k)}⟩ := hs{k}")

# memory-fact threading.  memfacts: name -> (statement-RHS producer per kind)
# We keep: hload (svfSlice), hfp (flushPins), hap (armPins), hsb (sp+167 byte),
# hdig (digit byte, from step 4), hs32z (slot 0x20 = 0, from step 13).
have_dig = False
have_s32z = False

def thread_mem_id(k):
    """mem unchanged: hmemK : σK.mem = σ{K-1}.mem"""
    emit(f"  have hload{k} : SvfprintfSliceLoaded σ{k}.mem := hmem{k} ▸ hload{k-1}")
    emit(f"  have hfp{k} : FlushPinsLoaded σ{k}.mem := hmem{k} ▸ hfp{k-1}")
    emit(f"  have hap{k} : ArmPinsLoaded σ{k}.mem := hmem{k} ▸ hap{k-1}")
    emit(f"  have hsb{k} : σ{k}.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some sb := hmem{k} ▸ hsb{k-1}")
    if have_dig:
        emit(f"  have hdig{k} : σ{k}.mem[vsp.toNat + 347]? = some (BitVec.ofNat 8 (48 + w.toNat)) := hmem{k} ▸ hdig{k-1}")
    if have_s32z:
        emit(f"  have hs32z{k} : SlotHolds vsp 0x020 (0#64) σ{k}.mem := hmem{k} ▸ hs32z{k-1}")

def thread_mem_w8(k, hoff, off_hex):
    """mem = writeMap8 (afterNextPC σ{k-1}).mem (vsp+sext off).toNat (sdData_val 0)"""
    emit(f"  have hNP{k-1}b : (afterNextPC (afterPrelude σ{k-1}) (0x{ADDR:08x}#64)).mem = σ{k-1}.mem := rfl")
    emit(f"  have hload{k} : SvfprintfSliceLoaded σ{k}.mem := by",
         f"    rw [hmem{k}, hNP{k-1}b]; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [{hoff}]; omega) hload{k-1}")
    emit(f"  have hfp{k} : FlushPinsLoaded σ{k}.mem := by",
         f"    rw [hmem{k}, hNP{k-1}b]; exact flushPins_writeMap8_fl _ _ _ (by rw [{hoff}]; omega) hfp{k-1}")
    emit(f"  have hap{k} : ArmPinsLoaded σ{k}.mem := by",
         f"    rw [hmem{k}, hNP{k-1}b]; exact armPins_writeMap8_43 _ _ _ (by rw [{hoff}]; omega) hap{k-1}")
    emit(f"  have hsb{k} : σ{k}.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some sb := by",
         f"    rw [hmem{k}, hNP{k-1}b, getElem?_writeMap8_out _ _ _ _ (by rw [{hoff}, hoff167]; omega)]",
         f"    exact hsb{k-1}")
    if have_dig:
        emit(f"  have hdig{k} : σ{k}.mem[vsp.toNat + 347]? = some (BitVec.ofNat 8 (48 + w.toNat)) := by",
             f"    rw [hmem{k}, hNP{k-1}b, getElem?_writeMap8_out _ _ _ _ (by rw [{hoff}]; omega)]",
             f"    exact hdig{k-1}")
    if have_s32z:
        emit(f"  have hs32z{k} : SlotHolds vsp 0x020 (0#64) σ{k}.mem := by",
             f"    rw [hmem{k}, hNP{k-1}b]",
             f"    exact slotHolds_writeMap8 vsp 0x020 (0#64) σ{k-1}.mem _ _ (by rw [hoff32, {hoff}]; omega) hs32z{k-1}")

CLS = None
ADDR = None

def std_step(k, addr, nxt, cls, comment, site, args, hyps,
             rd=None, rdval=None, rdfold=None, pc_lines=None, memkind="id",
             hoff=None, drop=None):
    """One machine step with full threading."""
    global CLS, ADDR, have_dig, have_s32z
    CLS, ADDR = cls, addr
    step_header(k, addr, comment, site, args, hyps)
    if pc_lines:
        emit(*pc_lines)
    else:
        pc_add4(k, addr, nxt)
    if cls != "j":
        minstret(k, cls)
    else:
        minstret(k, "j")
    if rd is not None:
        emit(f"  have hx{rd}_{k} : σ{k}.regs.get? Register.x{rd} = some {rdval} :=",
             f"    obs_alu_rd hobs{k} (by decide) (by decide) (by decide) (by decide) (by decide)")
        if rdfold:
            emit(*rdfold)
    if drop:
        for r in drop:
            track.pop(r, None)
    thread_regs(k, cls, skip=(rd,) if rd is not None else ())
    if rd is not None:
        track[rd] = (rdval, None)
    if memkind == "id":
        thread_mem_id(k)
    elif memkind == "w8":
        thread_mem_w8(k, hoff, None)
    emit("")


A4v = ("(sign_extend (m := 64) (Sail.BitVec.extractLsb (v + sign_extend"
       " (m := 64) (0x030#12)) 31 0))")

emit("import Vsa.Sim.SnprintfSitesFast",
     "import Vsa.Sim.SnprintfSitesFast2",
     "import Vsa.Sim.SnprintfSpec43",
     "",
     "/-!",
     "# M3 Layer-3 — `SnprintfSpec45` : the NONNEG single-digit arm (`_f45`)",
     "",
     "From the value-arm entry `0x800080e4` with the loaded argument `v` NON-NEGATIVE",
     "and `v.toNat ≤ 9`: `mv a4,a3` → `bgez a3` TAKEN → `0x80008050 bltz s4` TAKEN",
     "(default precision `-1`) → the `0x80008100` split → the single-digit fast path",
     "(digit `sb` at `sp+347`) → the `0x80008ea4` tail block (sign read-back reads the",
     "prologue-cleared `0x00`) → seam `0x8000812c` `beqz t5` **TAKEN** (no sign byte;",
     "`a6` stays `1 = len`) → `0x8088`/`0xa830` hops → the PRINT entry `0x8000782c`.",
     "",
     "NO sign byte is written on this path — `sp+167` still holds `0x00` at exit and",
     "the downstream PRINT segment will emit a SINGLE iovec (count 1).",
     "-/",
     "",
     "open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa",
     "open Register",
     "open Sail.ConcurrencyInterfaceV1.PreSail",
     "open Vsa.Machine (MState Config Step Steps)",
     "open Vsa.Logic",
     "open Vsa.Sim.Code (SvfprintfSliceLoaded FlushPinsLoaded ArmPinsLoaded)",
     "",
     "set_option maxHeartbeats 8000000",
     "set_option maxRecDepth 1000000",
     "",
     "namespace Vsa.Sim",
     "",
     "/-- **The nonneg single-digit arm**: `0x800080e4 → 0x8000782c`. -/",
     "theorem entryToPrintNN_fast_spec",
     "    (v vsp vt1 v8 v20 v23 v28 : BitVec 64)",
     "    (c : Config)",
     "    (hG : GoodState c.σ)",
     "    (hload : SvfprintfSliceLoaded c.σ.mem)",
     "    (hfp : FlushPinsLoaded c.σ.mem)",
     "    (hap : ArmPinsLoaded c.σ.mem)",
     "    (hpc : c.σ.regs.get? Register.PC = some (0x800080e4#64))",
     "    (hx13 : c.σ.regs.get? Register.x13 = some v)",
     "    (hx2 : c.σ.regs.get? Register.x2 = some vsp)",
     "    (hx6 : c.σ.regs.get? Register.x6 = some vt1)",
     "    (hx8 : c.σ.regs.get? Register.x8 = some v8)",
     "    (hx20 : c.σ.regs.get? Register.x20 = some v20)",
     "    (hx23 : c.σ.regs.get? Register.x23 = some v23)",
     "    (hx28 : c.σ.regs.get? Register.x28 = some v28)",
     "    (hnn : zopz0zKzJ_s v (0#64) = true)",
     "    (hmag9 : v.toNat ≤ 9)",
     "    (hwneg : v20.toInt < 0)",
     "    (hz167 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8))",
     "    (htlo : tohostAddr + 16 + 64 ≤ vsp.toNat)",
     "    (hhi : vsp.toNat + 356 ≤ 0x100000000)",
     "    (halign : vsp.toNat % 8 = 0)",
     "    (htick : c.tick < 2) :",
     "    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧",
     "      c'.σ.regs.get? Register.PC = some (0x8000782c#64) ∧",
     "      c'.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 1) ∧",
     "      c'.σ.regs.get? Register.x16 = some (BitVec.ofNat 64 1) ∧",
     "      c'.σ.regs.get? Register.x30 = some (0#64) ∧",
     "      c'.σ.regs.get? Register.x31 = some (0#64) ∧",
     "      c'.σ.regs.get? Register.x20 = some v20 ∧",
     "      c'.σ.regs.get? Register.x6 = some vt1 ∧",
     "      c'.σ.regs.get? Register.x28 = some v28 ∧",
     "      c'.σ.regs.get? Register.x23 = some v23 ∧",
     "      c'.σ.regs.get? Register.x8 = some v8 ∧",
     "      c'.σ.regs.get? Register.x2 = some vsp ∧",
     "      c'.σ.regs.get? Register.x26 = some (BitVec.ofNat 64 ((entryTop vsp).toNat - 1)) ∧",
     "      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) ∧",
     "      SlotHolds vsp 0x020 (0#64) c'.σ.mem ∧",
     "      BufInv (entryTop vsp) v.toNat 1 c'.σ.mem ∧",
     "      KeepRegs midRegs5 c.σ c'.σ ∧",
     "      (∀ a : Nat, a ≠ vsp.toNat + 347 →",
     "        ¬(vsp.toNat + 32 ≤ a ∧ a < vsp.toNat + 40) →",
     "        ¬(vsp.toNat + 48 ≤ a ∧ a < vsp.toNat + 64) →",
     "        c'.σ.mem[a]? = c.σ.mem[a]?) ∧",
     "      c'.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) ∧",
     "      SvfprintfSliceLoaded c'.σ.mem ∧ FlushPinsLoaded c'.σ.mem ∧",
     "      ArmPinsLoaded c'.σ.mem := by",
     "  have htohv : tohostAddr = 0x8001ad00 := rfl",
     "  have hnw : vsp.toNat + 348 < 2 ^ 64 := by omega",
     "  obtain ⟨vmi0, hmi0⟩ := hG.minstret",
     "  have hoff347 : (vsp + sign_extend (m := 64) (0x15b#12)).toNat = vsp.toNat + 347 :=",
     "    addoff_toNat_sn5 vsp (0x15b#12) 347 (by omega) (by decide) hnw",
     "  have hoff167 : (vsp + sign_extend (m := 64) (0x0a7#12)).toNat = vsp.toNat + 167 :=",
     "    addoff_toNat_sn5 vsp (0x0a7#12) 167 (by omega) (by decide) hnw",
     "  have hoff32 : (vsp + sign_extend (m := 64) (0x020#12)).toNat = vsp.toNat + 32 :=",
     "    addoff_toNat_sn5 vsp (0x020#12) 32 (by omega) (by decide) hnw",
     "  have hoff56 : (vsp + sign_extend (m := 64) (0x038#12)).toNat = vsp.toNat + 56 :=",
     "    addoff_toNat_sn5 vsp (0x038#12) 56 (by omega) (by decide) hnw",
     "  have hoff48 : (vsp + sign_extend (m := 64) (0x030#12)).toNat = vsp.toNat + 48 :=",
     "    addoff_toNat_sn5 vsp (0x030#12) 48 (by omega) (by decide) hnw",
     "  have htop_toNat : (entryTop vsp).toNat = vsp.toNat + 348 :=",
     "    addoff_toNat_sn5 vsp (0x15c#12) 348 (by omega) (by decide) hnw",
     "  have hg9 : zopz0zI_u ((0#64) + sign_extend (m := 64) (0x009#12)) v = false := by",
     "    unfold zopz0zI_u",
     "    simp only [Sail.BitVec.toNatInt,",
     "      show ((0#64) + sign_extend (m := 64) (0x009#12) : BitVec 64).toNat = 9 from by decide]",
     "    apply decide_eq_false",
     "    intro hc",
     "    exact absurd (Int.ofNat_lt.mp hc) (by omega)",
     "  have hgbltz : zopz0zI_s v20 (0#64) = true := by",
     "    unfold zopz0zI_s",
     "    apply decide_eq_true",
     "    simp only [BitVec.toInt_zero]",
     "    omega",
     "  have hgblez : zopz0zKzJ_s (0#64) v20 = true := by",
     "    unfold zopz0zKzJ_s",
     "    apply decide_eq_true",
     "    simp only [BitVec.toInt_zero, ge_iff_le]",
     "    omega",
     "  -- step-0 aliases",
     "  have hx2_0 := hx2",
     "  have hx6_0 := hx6",
     "  have hx20_0 := hx20",
     "  have hx23_0 := hx23",
     "  have hx8_0 := hx8",
     "  have hx28_0 := hx28",
     "  have hx13_0 := hx13",
     "  have hload0 : SvfprintfSliceLoaded c.σ.mem := hload",
     "  have hfp0 : FlushPinsLoaded c.σ.mem := hfp",
     "  have hap0 : ArmPinsLoaded c.σ.mem := hap",
     "  have hsb0 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := hz167")

track.clear()
track.update({"2": ("vsp", None), "6": ("vt1", None), "20": ("v20", None),
              "23": ("v23", None), "8": ("v8", None), "28": ("v28", None),
              "13": ("v", None)})

# patch thread functions' sb type: replace 'some sb' with 'some (0x00#8)' via wrapper
import re as _re
_emit = emit
def emit(*lines):
    _emit(*[l.replace("some sb", "some (0x00#8)") for l in lines])
# rebind in helper closures: helpers reference global emit — they see module-level name.

# === step 1: 80e4 mv a4,a3 ===
std_step(1, 0x800080e4, 0x800080e8, "alu", "mv a4,a3 — the (nonneg) magnitude",
         "site_800080e4_sn4", "v",
         "hG hpc hmi0 hx13_0 hload0 rfl htick",
         rd="14", rdval="(v + sign_extend (m := 64) (0x000#12))",
         rdfold=[
             "  rw [show (v + sign_extend (m := 64) (0x000#12) : BitVec 64) = v from by",
             "    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = (0#64) from by decide]",
             "    exact BitVec.add_zero v] at hx14_1"])
track["14"] = ("v", None)

# === step 2: 80e8 bgez a3 TAKEN → 8050 ===
std_step(2, 0x800080e8, 0x80008050, "bt", "bgez a3 TAKEN (v nonneg)",
         "site_800080e8_taken_fs", "v",
         "hG1 hpc1 hmi1 hx13_1 hload1 rfl hnn hi1",
         pc_lines=[
             "  have hpc2 : σ2.regs.get? Register.PC = some (0x80008050#64) := by",
             "    have := obs_btaken_pc hobs2",
             "    rwa [site_800080e8_taken_fs_tgt] at this"])

# === step 3: 8050 bltz s4 TAKEN → 8100 ===
std_step(3, 0x80008050, 0x80008100, "bt", "bltz s4 TAKEN (default precision -1)",
         "site_80008050_taken_fs", "v20",
         "hG2 hpc2 hmi2 hx20_2 hload2 rfl hgbltz hi2",
         pc_lines=[
             "  have hpc3 : σ3.regs.get? Register.PC = some (0x80008100#64) := by",
             "    have := obs_btaken_pc hobs3",
             "    rwa [site_80008050_taken_fs_tgt] at this"],
         drop=("13",))

# === step 4: 8100 li a5,9 ===
std_step(4, 0x80008100, 0x80008104, "alu", "li a5,9",
         "site_80008100_sn5", "",
         "hG3 hpc3 hmi3 hload3 rfl hi3",
         rd="15", rdval="((0#64) + sign_extend (m := 64) (0x009#12))")

# === step 5: 8104 bltu NOT taken ===
std_step(5, 0x80008104, 0x80008108, "bnt", "bltu a5,a4 NOT taken (v ≤ 9)",
         "site_80008104_nottaken_fs",
         "((0#64) + sign_extend (m := 64) (0x009#12)) v",
         "hG4 hpc4 hmi4 hx15_4 hx14_4 hload4 rfl hg9 hi4",
         drop=("15",))

# === step 6: 8108 addiw a4,a4,48 ===
std_step(6, 0x80008108, 0x8000810c, "alu", "addiw a4,a4,48 — the digit char",
         "site_80008108_fs", "v",
         "hG5 hpc5 hmi5 hx14_5 hload5 rfl hi5",
         rd="14", rdval=A4v)

# === step 7: 810c sb a4,347(sp) ===
CLS, ADDR = "store", 0x8000810c
step_header(7, 0x8000810c, "sb a4,347(sp) — the single digit byte",
            "site_8000810c_fs", f"vsp {A4v}",
            "hG6 hpc6 hmi6 hx2_6 hx14_6 hload6 rfl (by rw [hoff347]; omega) (by rw [hoff347]; omega) (by rw [hoff347]; omega) hi6")
pc_add4(7, 0x8000810c, 0x80008110)
minstret(7, "store")
thread_regs(7, "store")
track.pop("14", None)
emit("  have hNP6b : (afterNextPC (afterPrelude σ6) (0x8000810c#64)).mem = σ6.mem := rfl",
     "  have hload7 : SvfprintfSliceLoaded σ7.mem := by",
     "    rw [hmem7, hNP6b]; exact svfprintfSlice_insert_sn4 _ _ _ (by rw [hoff347]; omega) hload6",
     "  have hfp7 : FlushPinsLoaded σ7.mem := by",
     "    rw [hmem7, hNP6b]; exact flushPins_insert_fl _ _ _ (by rw [hoff347]; omega) hfp6",
     "  have hap7 : ArmPinsLoaded σ7.mem := by",
     "    rw [hmem7, hNP6b]; exact armPins_insert_43 _ _ _ (by rw [hoff347]; omega) hap6",
     "  have hsb7 : σ7.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := by",
     "    rw [hmem7, hNP6b, getElem_insert_ne _ ((vsp + sign_extend (m := 64) (0x0a7#12)).toNat) ((vsp + sign_extend (m := 64) (0x15b#12)).toNat) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; rw [hoff347, hoff167]; omega)]",
     "    exact hsb6",
     "  have hdig7 : σ7.mem[vsp.toNat + 347]? = some (BitVec.ofNat 8 (48 + v.toNat)) := by",
     "    rw [hmem7, hNP6b, hoff347, ← fast_digit_byte_43 v hmag9]",
     "    exact getElem_insert_self _ _ _",
     "")
have_dig = True
# NB: helper thread functions mention 'w.toNat' in hdig — patch via emit wrapper below
def emit(*lines):
    _emit(*[l.replace("some sb", "some (0x00#8)").replace("48 + w.toNat", "48 + v.toNat")
            for l in lines])

# === step 8: 8110 sext.w a6,s4 ===
std_step(8, 0x80008110, 0x80008114, "alu", "sext.w a6,s4 (value dead)",
         "site_80008110_fs", "v20",
         "hG7 hpc7 hmi7 hx20_7 hload7 rfl hi7",
         rd="16",
         rdval="(sign_extend (m := 64) (Sail.BitVec.extractLsb (v20 + sign_extend (m := 64) (0x000#12)) 31 0))")

# === step 9: 8114 blez s4 TAKEN ===
std_step(9, 0x80008114, 0x80008ea4, "bt", "blez s4 TAKEN",
         "site_80008114_taken_fs", "v20",
         "hG8 hpc8 hmi8 hx20_8 hload8 rfl hgblez hi8",
         pc_lines=[
             "  have hpc9 : σ9.regs.get? Register.PC = some (0x80008ea4#64) := by",
             "    have := obs_btaken_pc hobs9",
             "    rwa [site_80008114_taken_fs_tgt] at this"],
         drop=("16",))

# === step 10: 8ea4 lbu t5,167(sp) — reads the CLEARED sign slot ===
std_step(10, 0x80008ea4, 0x80008ea8, "alu", "lbu t5,167(sp) — reads 0x00 (no sign)",
         "site_80008ea4_fs2", "vsp (0x00#8)",
         "hG9 hpc9 hmi9 hx2_9 hap9 rfl (by rw [hoff167]; omega) (by rw [hoff167]; omega) (Or.inr (by rw [hoff167]; omega)) hsb9 hi9",
         rd="30", rdval="(zero_extend (m := 64) (0x00#8))",
         rdfold=[
             "  rw [show (zero_extend (m := 64) (0x00#8) : BitVec 64) = (0#64) from by decide] at hx30_10"])
track["30"] = ("(0#64)", None)

# === step 11: 8ea8 li a6,1 ===
std_step(11, 0x80008ea8, 0x80008eac, "alu", "li a6,1",
         "site_80008ea8_fs2", "",
         "hG10 hpc10 hmi10 hap10 rfl hi10",
         rd="16", rdval=X16A)

# === step 12: 8eac li t6,0 ===
std_step(12, 0x80008eac, 0x80008eb0, "alu", "li t6,0",
         "site_80008eac_fs2", "",
         "hG11 hpc11 hmi11 hap11 rfl hi11",
         rd="31", rdval="((0#64) + sign_extend (m := 64) (0x000#12))",
         rdfold=[
             "  rw [show ((0#64) + sign_extend (m := 64) (0x000#12) : BitVec 64) = (0#64) from by decide] at hx31_12"])
track["31"] = ("(0#64)", None)

# === step 13: 8eb0 li s6,1 ===
std_step(13, 0x80008eb0, 0x80008eb4, "alu", "li s6,1 — the length",
         "site_80008eb0_fs2", "",
         "hG12 hpc12 hmi12 hap12 rfl hi12",
         rd="22", rdval=X16A)

# === step 14: 8eb4 addi s10,sp,347 ===
std_step(14, 0x80008eb4, 0x80008eb8, "alu", "addi s10,sp,347 — the digit base",
         "site_80008eb4_fs2", "vsp",
         "hG13 hpc13 hmi13 hx2_13 hap13 rfl hi13",
         rd="26", rdval="(vsp + sign_extend (m := 64) (0x15b#12))")

# === step 15: 8eb8 j 8128 ===
std_step(15, 0x80008eb8, 0x80008128, "j", "j 0x80008128",
         "site_80008eb8_fs2", "",
         "hG14 hpc14 hmi14 hap14 rfl (by decide) hi14",
         pc_lines=[
             "  have hpc15 : σ15.regs.get? Register.PC = some (0x80008128#64) := by",
             "    have := obs_jx0_pc_sn5 hobs15",
             "    rwa [show (0x80008eb8#64 : BitVec 64) + sign_extend (m := 64) (0x1ff270#21)",
             "      = (0x80008128#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this"])

# === step 16: 8128 sd zero,32(sp) ===
CLS, ADDR = "store", 0x80008128
step_header(16, 0x80008128, "sd zero,32(sp)",
            "site_80008128_fs", "vsp",
            "hG15 hpc15 hmi15 hx2_15 hload15 rfl (by rw [hoff32]; omega) (by rw [hoff32]; omega) (by rw [hoff32]; omega) (by rw [hoff32]; omega) hi15")
pc_add4(16, 0x80008128, 0x8000812c)
minstret(16, "store")
thread_regs(16, "store")
thread_mem_w8(16, "hoff32", None)
emit("  have hs32z16 : SlotHolds vsp 0x020 (0#64) σ16.mem := by",
     "    rw [hmem16, hNP15b]",
     "    exact slotHolds_self vsp 0x020 _ (0#64) σ15.mem rfl",
     "")
have_s32z = True

# === step 17: 812c beqz t5 TAKEN (no sign byte) → 8088 ===
std_step(17, 0x8000812c, 0x80008088, "bt", "beqz t5 TAKEN (no sign byte)",
         "site_8000812c_taken_fs", "(0#64)",
         "hG16 hpc16 hmi16 hx30_16 hload16 rfl (by decide) hi16",
         pc_lines=[
             "  have hpc17 : σ17.regs.get? Register.PC = some (0x80008088#64) := by",
             "    have := obs_btaken_pc hobs17",
             "    rwa [site_8000812c_taken_fs_tgt] at this"])

# === step 18: 8088 bnez t6 NOT taken ===
std_step(18, 0x80008088, 0x8000808c, "bnt", "bnez t6 NOT taken",
         "site_80008088_nottaken_fl", "(0#64)",
         "hG17 hpc17 hmi17 hx31_17 hload17 rfl (by decide) hi17")

# === step 19: 808c j a830 ===
std_step(19, 0x8000808c, 0x8000a830, "j", "j 0x8000a830",
         "site_8000808c_fl", "",
         "hG18 hpc18 hmi18 hload18 rfl (by decide) hi18",
         pc_lines=[
             "  have hpc19 : σ19.regs.get? Register.PC = some (0x8000a830#64) := by",
             "    have := obs_jx0_pc_sn5 hobs19",
             "    rwa [show (0x8000808c#64 : BitVec 64) + sign_extend (m := 64) (0x0027a4#21)",
             "      = (0x8000a830#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this"])

# === step 20: a830 sd zero,56(sp) ===
CLS, ADDR = "store", 0x8000a830
step_header(20, 0x8000a830, "sd zero,56(sp)",
            "site_8000a830_fl", "vsp",
            "hG19 hpc19 hmi19 hx2_19 hfp19 rfl (by rw [hoff56]; omega) (by rw [hoff56]; omega) (by rw [hoff56]; omega) (by rw [hoff56]; omega) hi19")
pc_add4(20, 0x8000a830, 0x8000a834)
minstret(20, "store")
thread_regs(20, "store")
thread_mem_w8(20, "hoff56", None)
emit("")

# === step 21: a834 sd zero,48(sp) ===
CLS, ADDR = "store", 0x8000a834
step_header(21, 0x8000a834, "sd zero,48(sp)",
            "site_8000a834_fl", "vsp",
            "hG20 hpc20 hmi20 hx2_20 hfp20 rfl (by rw [hoff48]; omega) (by rw [hoff48]; omega) (by rw [hoff48]; omega) (by rw [hoff48]; omega) hi20")
pc_add4(21, 0x8000a834, 0x8000a838)
minstret(21, "store")
thread_regs(21, "store")
thread_mem_w8(21, "hoff48", None)
emit("")

# === step 22: a838 j 782c ===
std_step(22, 0x8000a838, 0x8000782c, "j", "j 0x8000782c — the PRINT entry",
         "site_8000a838_fl", "",
         "hG21 hpc21 hmi21 hfp21 rfl (by decide) hi21",
         pc_lines=[
             "  have hpc22 : σ22.regs.get? Register.PC = some (0x8000782c#64) := by",
             "    have := obs_jx0_pc_sn5 hobs22",
             "    rwa [show (0x8000a838#64 : BitVec 64) + sign_extend (m := 64) (0x1fcff4#21)",
             "      = (0x8000782c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this"])

# === post assembly ===
emit("  -- x22 = 1 and x16 = 1 (fold the li forms)",
     "  rw [show ((0#64) + sign_extend (m := 64) (0x001#12) : BitVec 64) = BitVec.ofNat 64 1 from by",
     "    apply BitVec.eq_of_toNat_eq; decide] at hx22_22 hx16_22",
     "  -- x26 = ofNat (top−1)",
     "  rw [show (vsp + sign_extend (m := 64) (0x15b#12) : BitVec 64)",
     "      = BitVec.ofNat 64 ((entryTop vsp).toNat - 1) from by",
     "    apply BitVec.eq_of_toNat_eq",
     "    rw [hoff347, htop_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]",
     "    omega] at hx26_22",
     "  -- the one-digit buffer",
     "  have hbuf : BufInv (entryTop vsp) v.toNat 1 σ22.mem := by",
     "    intro j hj",
     "    have hj0 : j = 0 := by omega",
     "    subst hj0",
     "    have hkey : (entryTop vsp).toNat - 1 - 0 = vsp.toNat + 347 := by",
     "      rw [htop_toNat]; omega",
     "    have hval : 48 + (v.toNat / 10 ^ 0) % 10 = 48 + v.toNat := by",
     "      simp only [Nat.pow_zero, Nat.div_one]",
     "      rw [Nat.mod_eq_of_lt (by omega)]",
     "    rw [hkey, hval]",
     "    exact hdig22",
     "  -- mid-register preservation across all 22 steps",
     "  have hkeep : KeepRegs midRegs5 c.σ σ22 := by",
     "    have h0 := keep_rfl midRegs5 c.σ",
     "    have h1 := keep_alu hobs1 (by decide) h0",
     "    have h2 := keep_btaken hobs2 (by decide) h1",
     "    have h3 := keep_btaken hobs3 (by decide) h2",
     "    have h4 := keep_alu hobs4 (by decide) h3",
     "    have h5 := keep_bnottaken hobs5 (by decide) h4",
     "    have h6 := keep_alu hobs6 (by decide) h5",
     "    have h7 := keep_store hobs7 (by decide) h6",
     "    have h8 := keep_alu hobs8 (by decide) h7",
     "    have h9 := keep_btaken hobs9 (by decide) h8",
     "    have h10 := keep_alu hobs10 (by decide) h9",
     "    have h11 := keep_alu hobs11 (by decide) h10",
     "    have h12 := keep_alu hobs12 (by decide) h11",
     "    have h13 := keep_alu hobs13 (by decide) h12",
     "    have h14 := keep_alu hobs14 (by decide) h13",
     "    have h15 := keep_jr hobs15 (by decide) h14",
     "    have h16 := keep_store hobs16 (by decide) h15",
     "    have h17 := keep_btaken hobs17 (by decide) h16",
     "    have h18 := keep_bnottaken hobs18 (by decide) h17",
     "    have h19 := keep_jr hobs19 (by decide) h18",
     "    have h20 := keep_store hobs20 (by decide) h19",
     "    have h21 := keep_store hobs21 (by decide) h20",
     "    exact keep_jr hobs22 (by decide) h21",
     "  -- pointwise frame",
     "  have hmframe : ∀ a : Nat, a ≠ vsp.toNat + 347 →",
     "      ¬(vsp.toNat + 32 ≤ a ∧ a < vsp.toNat + 40) →",
     "      ¬(vsp.toNat + 48 ≤ a ∧ a < vsp.toNat + 64) →",
     "      σ22.mem[a]? = c.σ.mem[a]? := by",
     "    intro a hd hA hB",
     "    rw [hmem22, hmem21, hNP20b, getElem?_writeMap8_out _ _ _ _ (by rw [hoff48]; omega),",
     "      hmem20, hNP19b, getElem?_writeMap8_out _ _ _ _ (by rw [hoff56]; omega),",
     "      hmem19, hmem18, hmem17,",
     "      hmem16, hNP15b, getElem?_writeMap8_out _ _ _ _ (by rw [hoff32]; omega),",
     "      hmem15, hmem14, hmem13, hmem12, hmem11, hmem10, hmem9, hmem8,",
     "      hmem7, hNP6b, getElem_insert_ne _ a ((vsp + sign_extend (m := 64) (0x15b#12)).toNat) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; rw [hoff347]; omega),",
     "      hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]",
     "  refine ⟨⟨σ22, i22, " + steps_expr(22) + "⟩, ?_, hG22, hpc22, hx22_22, hx16_22,",
     "    hx30_22, hx31_22, hx20_22, hx6_22, hx28_22, hx23_22, hx8_22, hx2_22, hx26_22,",
     "    hi22, hG22.minstret, hs32z22, hbuf, hkeep, hmframe, hsb22, hload22, hfp22, hap22⟩")
chain = f"(Steps.single hstep22)"
for j in range(21, 0, -1):
    chain = f"((Steps.single hstep{j}).trans {chain})"
emit("  exact " + chain[1:-1])
emit("", "end Vsa.Sim", "")

import pathlib
out = pathlib.Path("Vsa/Sim/SnprintfSpec45.lean")
out.write_text("\n".join(L))
print(f"wrote {out} ({len(L)} lines)")
