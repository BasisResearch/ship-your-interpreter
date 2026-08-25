#!/usr/bin/env python3
"""Emit Vsa/Sim/SnprintfSpec49.lean — `printToSsprintNN_spec`: the 1-iovec
PRINT segment for the NONNEG arm, `0x8000782c → 0x8000e908`.

35 machine steps total: 27 emitted here (782c ld cursor / 7830 andi t0 /
7834 mv / 7838 beqz-taken → 7cd4 subw pad / 7cd8 bgtz-nt / 7cdc lbu sign=0 /
7ce0 bnez-NOT-taken (no sign iovec!) / 7ce4 subw s4,s4,s6 / 7ce8 blez-taken →
78bc iovec fill (count vcnt→vcnt+1, s7 = iov base itself) ... 7904 mv a5,a6),
then `iov2Tail_spec` (SnprintfSpec17) covers 7908 → the completed
`jal __ssprint_r` (vsel := vlen, the `bge t3,a6` NOT-taken arm).

House pattern: scripts/pro_emitter/gen_spec45.py (SnprintfSpec45).
"""

L = []
def emit(*lines):
    L.extend(lines)

SUBW_PAD = ("(sign_extend (m := 64) ((Sail.BitVec.extractLsb vt3 31 0)"
            " - (Sail.BitVec.extractLsb vlen 31 0)))")
SUBW_PREC = ("(sign_extend (m := 64) ((Sail.BitVec.extractLsb v20 31 0)"
             " - (Sail.BitVec.extractLsb vs6 31 0)))")
ADDIW_CNT = ("(sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) vcnt"
             " : BitVec 64) + sign_extend (m := 64) (0x001#12)) 31 0))")
SEXT_CNT = "(sign_extend (m := 64) vcnt : BitVec 64)"

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
    "store": None,
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
    fn = {"alu": "obs_alu_minstret", "bnt": "obs_bnottaken_minstret",
          "bt": "obs_btaken_minstret", "store": "obs_store_minstret_sn4"}[cls]
    emit(f"  obtain ⟨vmi{k}, hmi{k}⟩ := {fn} hobs{k}")

def pc_add4(k, addr, nxt, cls):
    obs = {"alu": "obs_alu_pc", "bnt": "obs_bnottaken_pc", "store": "obs_store_pc_sn4"}
    emit(f"  have hpc{k} : σ{k}.regs.get? Register.PC = some (0x{nxt:08x}#64) := by",
         f"    have := {obs[cls]} hobs{k}",
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

# running memory expression (over c.σ.mem)
MEM = ["c.σ.mem"]
LOADPRED = {"load": "SvfprintfSliceLoaded", "fp": "FlushPinsLoaded", "ap": "ArmPinsLoaded"}

def thread_mem_id(k):
    emit(f"  have hmE{k} : σ{k}.mem = {MEM[0]} := " +
         (f"hmem{k}" if k == 1 else f"hmem{k}.trans hmE{k-1}"))
    for nm in LOADPRED:
        emit(f"  have h{nm}{k} : {LOADPRED[nm]} σ{k}.mem := hmem{k} ▸ h{nm}{k-1}")

def thread_mem_write(k, addr, kind, key, data, keyoff):
    wrap = {"w8": "writeMap8", "w4": "writeMap4"}[kind]
    new = f"{wrap} ({MEM[0]}) (({key}).toNat) ({data})"
    emit(f"  have hNP{k-1}b : (afterNextPC (afterPrelude σ{k-1}) (0x{addr:08x}#64)).mem = σ{k-1}.mem := rfl")
    emit(f"  have hmE{k} : σ{k}.mem = {new} := by",
         f"    rw [hmem{k}, hNP{k-1}b, hmE{k-1}]")
    MEM[0] = new
    pres = {("load", "w8"): "svfprintfSlice_writeMap8_sn5",
            ("load", "w4"): "svfprintfSlice_writeMap4_pe",
            ("fp", "w8"): "flushPins_writeMap8_fl",
            ("fp", "w4"): "flushPins_writeMap4_pe",
            ("ap", "w8"): "armPins_writeMap8_43"}
    for nm in LOADPRED:
        if (nm, kind) in pres:
            emit(f"  have h{nm}{k} : {LOADPRED[nm]} σ{k}.mem := by",
                 f"    rw [hmem{k}, hNP{k-1}b]; exact {pres[(nm, kind)]} _ _ _ (by rw [{keyoff}]; omega) h{nm}{k-1}")
        else:  # ap under w4: four inserts
            emit(f"  have h{nm}{k} : {LOADPRED[nm]} σ{k}.mem := by",
                 f"    rw [hmem{k}, hNP{k-1}b]",
                 f"    exact armPins_insert_43 _ _ _ (by rw [{keyoff}]; omega) (armPins_insert_43 _ _ _ (by rw [{keyoff}]; omega)",
                 f"      (armPins_insert_43 _ _ _ (by rw [{keyoff}]; omega) (armPins_insert_43 _ _ _ (by rw [{keyoff}]; omega) h{nm}{k-1})))")

def std_step(k, addr, nxt, cls, comment, site, args, hyps,
             rd=None, rdraw=None, rdfold=None, rdtrack=None,
             pc_lines=None, drop=None,
             memw=None):
    """memw = (kind, key, data, keyoff) for store steps."""
    step_header(k, addr, comment, site, args, hyps)
    if pc_lines:
        emit(*pc_lines)
    else:
        pc_add4(k, addr, nxt, cls)
    minstret(k, cls)
    if rd is not None:
        emit(f"  have hx{rd}_{k} : σ{k}.regs.get? Register.x{rd} = some {rdraw} :=",
             f"    obs_alu_rd hobs{k} (by decide) (by decide) (by decide) (by decide) (by decide)")
        if rdfold:
            emit(*rdfold)
    if drop:
        for r in drop:
            track.pop(r, None)
    thread_regs(k, cls, skip=(rd,) if rd is not None else ())
    if rd is not None:
        track[rd] = (rdtrack if rdtrack is not None else rdraw, None)
    if memw is None:
        thread_mem_id(k)
    else:
        thread_mem_write(k, addr, *memw)
    emit("")

# ---------------------------------------------------------------- preamble
HDR = """import Vsa.Sim.SnprintfSpec17
import Vsa.Sim.SnprintfSpec43
import Vsa.Sim.SnprintfSitesPrint
import Vsa.Sim.SnprintfSitesPrint2
import Vsa.Sim.SnprintfSitesFast2

/-!
# M3 Layer-3 — `SnprintfSpec49` : the 1-iovec PRINT segment (nonneg arm)

`printToSsprintNN_spec`: from the PRINT-macro entry `0x8000782c` (where
`entryToPrintNN_any_spec`, Spec48, lands with the sign slot `0x00`) to the
completed `jal __ssprint_r` (`PC = 0x8000e908`, `ra = 0x80008688`).  The
`bnez` at `0x80007ce0` reads the CLEARED sign byte and is NOT taken — no
sign iovec is built; the single (digit) iovec entry is written at the iov
cursor `s7 = viov` (count `vcnt → vcnt+1`, cursor `vcur → vcur+len`).
The shared call tail from `0x80007908` is `iov2Tail_spec` (Spec17),
consumed with `vsel := vlen` (the `bge t3,a6` NOT-taken arm).

Emitted by `scripts/pro_emitter/gen_spec49.py`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded FlushPinsLoaded ArmPinsLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- **PRINT entry → `__ssprint_r` call, 1-iovec (nonneg) arm**
(`0x8000782c → 0x8000e908`, 35 steps incl. the Spec17 tail). -/
"""

emit(HDR.rstrip(),
     "theorem printToSsprintNN_spec",
     "    (vsp vt1 vt3 vlen vs6 v20 v8 viov vbase vcur vtot vstr : BitVec 64)",
     "    (vcnt : BitVec 32)",
     "    (c : Config)",
     "    (hG : GoodState c.σ)",
     "    (hload : SvfprintfSliceLoaded c.σ.mem)",
     "    (hfp : FlushPinsLoaded c.σ.mem)",
     "    (hap : ArmPinsLoaded c.σ.mem)",
     "    (hpc : c.σ.regs.get? Register.PC = some (0x8000782c#64))",
     "    (hx2 : c.σ.regs.get? Register.x2 = some vsp)",
     "    (hx6 : c.σ.regs.get? Register.x6 = some vt1)",
     "    (hx8 : c.σ.regs.get? Register.x8 = some v8)",
     "    (hx16 : c.σ.regs.get? Register.x16 = some vlen)",
     "    (hx20 : c.σ.regs.get? Register.x20 = some v20)",
     "    (hx22 : c.σ.regs.get? Register.x22 = some vs6)",
     "    (hx23 : c.σ.regs.get? Register.x23 = some viov)",
     "    (hx26 : c.σ.regs.get? Register.x26 = some vbase)",
     "    (hx28 : c.σ.regs.get? Register.x28 = some vt3)",
     "    -- FILE fields + the cleared sign byte",
     "    (hcur : SlotHolds vsp 0x0f0 vcur c.σ.mem)",
     "    (hcnt0 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat]? = some (vcnt.extractLsb' 0 8))",
     "    (hcnt1 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 1]? = some (vcnt.extractLsb' 8 8))",
     "    (hcnt2 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 2]? = some (vcnt.extractLsb' 16 8))",
     "    (hcnt3 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 3]? = some (vcnt.extractLsb' 24 8))",
     "    (hz167 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8))",
     "    (htot : SlotHolds vsp 0x010 vtot c.σ.mem)",
     "    (hstr : SlotHolds vsp 0x008 vstr c.σ.mem)",
     "    -- branch guards (nonneg-%lld path, upstream provenance)",
     "    (hflag84 : vt1 &&& sign_extend (m := 64) (0x084#12) = 0#64)",
     "    (hflag256 : vt1 &&& sign_extend (m := 64) (0x100#12) = 0#64)",
     "    (hflag4z : vt1 &&& sign_extend (m := 64) (0x004#12) = 0#64)",
     "    (hpad : zopz0zI_s (0#64) " + SUBW_PAD + " = false)",
     "    (hprec : zopz0zKzJ_s (0#64) " + SUBW_PREC + " = true)",
     "    (hcntlt : zopz0zI_s (0x7#64) " + ADDIW_CNT + " = false)",
     "    (hwlen : zopz0zKzJ_s vt3 vlen = false)",
     "    (hvc2 : ((vcur + vs6) != (0#64)) = true)",
     "    -- layout",
     "    (hspwin : tohostAddr + 16 + 64 ≤ vsp.toNat)",
     "    (hsphi : vsp.toNat + 356 ≤ 0x100000000)",
     "    (hspalign : vsp.toNat % 8 = 0)",
     "    (hiovwin : tohostAddr + 16 ≤ viov.toNat)",
     "    (hiovhi : viov.toNat + 16 ≤ 0x100000000)",
     "    (hiovalign : viov.toNat % 8 = 0)",
     "    (hiovsep : vsp.toNat + 24 ≤ viov.toNat)",
     "    (htick : c.tick < 2) :",
     "    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧",
     "      c'.σ.regs.get? Register.PC = some (0x8000e908#64) ∧",
     "      c'.σ.regs.get? Register.x1 = some (0x80008688#64) ∧",
     "      c'.σ.regs.get? Register.x10 = some v8 ∧",
     "      c'.σ.regs.get? Register.x11 = some vstr ∧",
     "      c'.σ.regs.get? Register.x12 = some (vsp + sign_extend (m := 64) (0x0e0#12)) ∧",
     "      c'.σ.regs.get? Register.x2 = some vsp ∧",
     "      c'.σ.regs.get? Register.x5 = some (0#64) ∧",
     "      c'.σ.regs.get? Register.x6 = some (0#64) ∧",
     "      c'.σ.regs.get? Register.x8 = some v8 ∧",
     "      c'.σ.regs.get? Register.x16 = some vlen ∧",
     "      c'.σ.regs.get? Register.x20 = some " + SUBW_PREC + " ∧",
     "      c'.σ.regs.get? Register.x22 = some vs6 ∧",
     "      c'.σ.regs.get? Register.x23 = some (viov + sign_extend (m := 64) (0x010#12)) ∧",
     "      c'.σ.regs.get? Register.x26 = some vbase ∧",
     "      c'.σ.regs.get? Register.x28 = some vt3 ∧",
     "      c'.σ.mem = writeMap8",
     "        (writeMap4",
     "          (writeMap8",
     "            (writeMap8",
     "              (writeMap8 c.σ.mem",
     "                ((vsp + sign_extend (m := 64) (0x0f0#12)).toNat) (sdData_val (vcur + vs6)))",
     "              ((viov + sign_extend (m := 64) (0x000#12)).toNat) (sdData_val vbase))",
     "            ((viov + sign_extend (m := 64) (0x008#12)).toNat) (sdData_val vs6))",
     "          ((vsp + sign_extend (m := 64) (0x0e8#12)).toNat)",
     "            (swData " + ADDIW_CNT + "))",
     "        ((vsp + sign_extend (m := 64) (0x010#12)).toNat)",
     "          (sdData_val (sign_extend (m := 64)",
     "            (Sail.BitVec.extractLsb vlen 31 0 + Sail.BitVec.extractLsb vtot 31 0))) ∧",
     "      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) ∧",
     "      KeepRegs midRegs5 c.σ c'.σ := by",
     "  have htohv : tohostAddr = 0x8001ad00 := rfl",
     "  have hnw : vsp.toNat + 348 < 2 ^ 64 := by omega",
     "  obtain ⟨vmi0, hmi0⟩ := hG.minstret",
     "  have hoff240 : (vsp + sign_extend (m := 64) (0x0f0#12)).toNat = vsp.toNat + 240 :=",
     "    addoff_toNat_sn5 vsp (0x0f0#12) 240 (by omega) (by decide) hnw",
     "  have hoff232 : (vsp + sign_extend (m := 64) (0x0e8#12)).toNat = vsp.toNat + 232 :=",
     "    addoff_toNat_sn5 vsp (0x0e8#12) 232 (by omega) (by decide) hnw",
     "  have hoff167 : (vsp + sign_extend (m := 64) (0x0a7#12)).toNat = vsp.toNat + 167 :=",
     "    addoff_toNat_sn5 vsp (0x0a7#12) 167 (by omega) (by decide) hnw",
     "  have hoff16 : (vsp + sign_extend (m := 64) (0x010#12)).toNat = vsp.toNat + 16 :=",
     "    addoff_toNat_sn5 vsp (0x010#12) 16 (by omega) (by decide) hnw",
     "  have hoff8 : (vsp + sign_extend (m := 64) (0x008#12)).toNat = vsp.toNat + 8 :=",
     "    addoff_toNat_sn5 vsp (0x008#12) 8 (by omega) (by decide) hnw",
     "  have hoffiov0 : (viov + sign_extend (m := 64) (0x000#12)).toNat = viov.toNat :=",
     "    addoff_toNat_sn5 viov (0x000#12) 0 (by omega) (by decide) (by omega)",
     "  have hoffiov8 : (viov + sign_extend (m := 64) (0x008#12)).toNat = viov.toNat + 8 :=",
     "    addoff_toNat_sn5 viov (0x008#12) 8 (by omega) (by decide) (by omega)",
     "  -- step-0 aliases",
     "  have hx2_0 := hx2",
     "  have hx6_0 := hx6",
     "  have hx8_0 := hx8",
     "  have hx16_0 := hx16",
     "  have hx20_0 := hx20",
     "  have hx22_0 := hx22",
     "  have hx23_0 := hx23",
     "  have hx26_0 := hx26",
     "  have hx28_0 := hx28",
     "  have hload0 : SvfprintfSliceLoaded c.σ.mem := hload",
     "  have hfp0 : FlushPinsLoaded c.σ.mem := hfp",
     "  have hap0 : ArmPinsLoaded c.σ.mem := hap",
     "  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩ := hcur",
     "")

track.clear()
track.update({"2": ("vsp", None), "6": ("vt1", None), "8": ("v8", None),
              "16": ("vlen", None), "20": ("v20", None), "22": ("vs6", None),
              "23": ("viov", None), "26": ("vbase", None), "28": ("vt3", None)})

CUR8 = " ".join(f"((sdData_val vcur).extractLsb' {8*j} 8)" for j in range(8))
LDRAW = ("(sign_extend (m := 64) (((((((((sdData_val vcur).extractLsb' 56 8).append"
         " ((sdData_val vcur).extractLsb' 48 8)).append ((sdData_val vcur).extractLsb' 40 8)).append"
         " ((sdData_val vcur).extractLsb' 32 8)).append ((sdData_val vcur).extractLsb' 24 8)).append"
         " ((sdData_val vcur).extractLsb' 16 8)).append ((sdData_val vcur).extractLsb' 8 8)).append"
         " ((sdData_val vcur).extractLsb' 0 8) : BitVec (8 * 8)))")

# === step 1: 782c ld a2,240(sp) ===
std_step(1, 0x8000782c, 0x80007830, "alu", "ld a2,240(sp) — the running cursor",
         "site_8000782c_pv", "vsp " + CUR8,
         "hG hpc hmi0 hx2_0 hload0 rfl (by rw [hoff240]; omega) (by rw [hoff240]; omega)"
         " (Or.inr (by rw [hoff240]; omega)) (by rw [hoff240]; omega)"
         " hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 htick",
         rd="12", rdraw=LDRAW,
         rdfold=["  rw [ve_sext_reassemble vcur] at hx12_1"],
         rdtrack="vcur")

# === step 2: 7830 andi t0,t1,132 ===
std_step(2, 0x80007830, 0x80007834, "alu", "andi t0,t1,132 — flags & 0x84 = 0",
         "site_80007830_pv", "vt1",
         "hG1 hpc1 hmi1 hx6_1 hload1 rfl hi1",
         rd="5", rdraw="(vt1 &&& sign_extend (m := 64) (0x084#12))",
         rdfold=["  rw [hflag84] at hx5_2"],
         rdtrack="(0#64)")

# === step 3: 7834 mv a0,a2 ===
std_step(3, 0x80007834, 0x80007838, "alu", "mv a0,a2",
         "site_80007834_pv", "vcur",
         "hG2 hpc2 hmi2 hx12_2 hload2 rfl hi2",
         rd="10", rdraw="(vcur + sign_extend (m := 64) (0x000#12))")

# === step 4: 7838 beqz t0 TAKEN → 7cd4 ===
std_step(4, 0x80007838, 0x80007cd4, "bt", "beqz t0 TAKEN (no adjust flags)",
         "site_80007838_taken_pv", "(0#64)",
         "hG3 hpc3 hmi3 hx5_3 hload3 rfl (by decide) hi3",
         pc_lines=[
             "  have hpc4 : σ4.regs.get? Register.PC = some (0x80007cd4#64) := by",
             "    have := obs_btaken_pc hobs4",
             "    rwa [site_80007838_taken_pv_tgt] at this"],
         drop=("10",))

# === step 5: 7cd4 subw a4,t3,a6 — pad count ===
std_step(5, 0x80007cd4, 0x80007cd8, "alu", "subw a4,t3,a6 — pad count (≤ 0)",
         "site_80007cd4_pv2", "vt3 vlen",
         "hG4 hpc4 hmi4 hx28_4 hx16_4 hfp4 rfl hi4",
         rd="14", rdraw=SUBW_PAD)

# === step 6: 7cd8 bgtz a4 NOT taken ===
std_step(6, 0x80007cd8, 0x80007cdc, "bnt", "bgtz a4 NOT taken (no left pad)",
         "site_80007cd8_nottaken_pv2", SUBW_PAD,
         "hG5 hpc5 hmi5 hx14_5 hfp5 rfl hpad hi5")

# === step 7: 7cdc lbu a4,167(sp) — the CLEARED sign byte ===
emit("  have hz167_6 : σ6.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := by",
     "    rw [hmE6]; exact hz167")
std_step(7, 0x80007cdc, 0x80007ce0, "alu", "lbu a4,167(sp) — reads 0x00 (no sign)",
         "site_80007cdc_pv2", "vsp (0x00#8)",
         "hG6 hpc6 hmi6 hx2_6 hfp6 rfl (by rw [hoff167]; omega) (by rw [hoff167]; omega)"
         " (Or.inr (by rw [hoff167]; omega)) hz167_6 hi6",
         rd="14", rdraw="(zero_extend (m := 64) (0x00#8))",
         rdfold=["  rw [show (zero_extend (m := 64) (0x00#8) : BitVec 64) = (0#64) from by decide] at hx14_7"],
         rdtrack="(0#64)")

# === step 8: 7ce0 bnez a4 NOT taken — the nonneg fork ===
std_step(8, 0x80007ce0, 0x80007ce4, "bnt", "bnez a4 NOT taken — NO sign iovec",
         "site_80007ce0_nottaken_pv2", "(0#64)",
         "hG7 hpc7 hmi7 hx14_7 hfp7 rfl (by decide) hi7")

# === step 9: 7ce4 subw s4,s4,s6 ===
std_step(9, 0x80007ce4, 0x80007ce8, "alu", "subw s4,s4,s6 — precision − len",
         "site_80007ce4_fs2", "v20 vs6",
         "hG8 hpc8 hmi8 hx20_8 hx22_8 hap8 rfl hi8",
         rd="20", rdraw=SUBW_PREC)

# === step 10: 7ce8 blez s4 TAKEN → 78bc ===
std_step(10, 0x80007ce8, 0x800078bc, "bt", "blez s4 TAKEN → the iovec fill",
         "site_80007ce8_taken_fs2", SUBW_PREC,
         "hG9 hpc9 hmi9 hx20_9 hap9 rfl hprec hi9",
         pc_lines=[
             "  have hpc10 : σ10.regs.get? Register.PC = some (0x800078bc#64) := by",
             "    have := obs_btaken_pc hobs10",
             "    rwa [site_80007ce8_taken_fs2_tgt] at this"])

# === step 11: 78bc andi a4,t1,256 ===
std_step(11, 0x800078bc, 0x800078c0, "alu", "andi a4,t1,256 — flags & 0x100 = 0",
         "site_800078bc_pv", "vt1",
         "hG10 hpc10 hmi10 hx6_10 hload10 rfl hi10",
         rd="14", rdraw="(vt1 &&& sign_extend (m := 64) (0x100#12))",
         rdfold=["  rw [hflag256] at hx14_11"],
         rdtrack="(0#64)")

# === step 12: 78c0 bnez a4 NOT taken ===
std_step(12, 0x800078c0, 0x800078c4, "bnt", "bnez a4 NOT taken",
         "site_800078c0_nottaken_pv", "(0#64)",
         "hG11 hpc11 hmi11 hx14_11 hload11 rfl (by decide) hi11")

# === step 13: 78c4 lw a5,232(sp) — the iov count ===
emit("  have hcnt0_12 : σ12.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat]? = some (vcnt.extractLsb' 0 8) := by",
     "    rw [hmE12]; exact hcnt0",
     "  have hcnt1_12 : σ12.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 1]? = some (vcnt.extractLsb' 8 8) := by",
     "    rw [hmE12]; exact hcnt1",
     "  have hcnt2_12 : σ12.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 2]? = some (vcnt.extractLsb' 16 8) := by",
     "    rw [hmE12]; exact hcnt2",
     "  have hcnt3_12 : σ12.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 3]? = some (vcnt.extractLsb' 24 8) := by",
     "    rw [hmE12]; exact hcnt3",
     "  have hlwval : (sign_extend (m := 64)",
     "      ((((vcnt.extractLsb' 24 8).append (vcnt.extractLsb' 16 8)).append",
     "        (vcnt.extractLsb' 8 8)).append (vcnt.extractLsb' 0 8) : BitVec (8 * 4)))",
     "      = (sign_extend (m := 64) vcnt : BitVec 64) := by",
     "    have hreassemble : ((((vcnt.extractLsb' 24 8).append (vcnt.extractLsb' 16 8)).append",
     "        (vcnt.extractLsb' 8 8)).append (vcnt.extractLsb' 0 8) : BitVec (8 * 4)) = vcnt := by",
     "      apply BitVec.eq_of_toNat_eq",
     "      rw [word_toNat_recon]",
     "      simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]",
     "      have := vcnt.isLt",
     "      omega",
     "    rw [hreassemble]")
std_step(13, 0x800078c4, 0x800078c8, "alu", "lw a5,232(sp) — the iov count",
         "site_800078c4_pv",
         "vsp (vcnt.extractLsb' 0 8) (vcnt.extractLsb' 8 8) (vcnt.extractLsb' 16 8) (vcnt.extractLsb' 24 8)",
         "hG12 hpc12 hmi12 hx2_12 hload12 rfl (by rw [hoff232]; omega) (by rw [hoff232]; omega)"
         " (Or.inr (by rw [hoff232]; omega)) (by rw [hoff232]; omega)"
         " hcnt0_12 hcnt1_12 hcnt2_12 hcnt3_12 hi12",
         rd="15",
         rdraw="(sign_extend (m := 64) ((((vcnt.extractLsb' 24 8).append (vcnt.extractLsb' 16 8)).append (vcnt.extractLsb' 8 8)).append (vcnt.extractLsb' 0 8) : BitVec (8 * 4)))",
         rdfold=["  rw [hlwval] at hx15_13"],
         rdtrack=SEXT_CNT)

# === step 14: 78c8 add a2,a2,s6 ===
std_step(14, 0x800078c8, 0x800078cc, "alu", "add a2,a2,s6 — cursor + len",
         "site_800078c8_pv", "vcur vs6",
         "hG13 hpc13 hmi13 hx12_13 hx22_13 hload13 rfl hi13",
         rd="12", rdraw="(vcur + vs6)")

# === step 15: 78cc sd a2,240(sp) — store the bumped cursor ===
std_step(15, 0x800078cc, 0x800078d0, "store", "sd a2,240(sp) — the bumped cursor",
         "site_800078cc_pv", "vsp (vcur + vs6)",
         "hG14 hpc14 hmi14 hx2_14 hx12_14 hload14 rfl (by rw [hoff240]; omega)"
         " (by rw [hoff240]; omega) (by rw [hoff240]; omega) (by rw [hoff240]; omega) hi14",
         memw=("w8", "vsp + sign_extend (m := 64) (0x0f0#12)", "sdData_val (vcur + vs6)", "hoff240"))

# === step 16: 78d0 addiw a5,a5,1 ===
std_step(16, 0x800078d0, 0x800078d4, "alu", "addiw a5,a5,1 — count + 1",
         "site_800078d0_pv", SEXT_CNT,
         "hG15 hpc15 hmi15 hx15_15 hload15 rfl hi15",
         rd="15", rdraw=ADDIW_CNT)

# === step 17: 78d4 sd s10,0(s7) — iov base ===
std_step(17, 0x800078d4, 0x800078d8, "store", "sd s10,0(s7) — iov[0].iov_base := digit base",
         "site_800078d4_pv", "viov vbase",
         "hG16 hpc16 hmi16 hx23_16 hx26_16 hload16 rfl (by rw [hoffiov0]; omega)"
         " (by rw [hoffiov0]; omega) (by rw [hoffiov0]; omega) (by rw [hoffiov0]; omega) hi16",
         memw=("w8", "viov + sign_extend (m := 64) (0x000#12)", "sdData_val vbase", "hoffiov0"))

# === step 18: 78d8 sd s6,8(s7) — iov len ===
std_step(18, 0x800078d8, 0x800078dc, "store", "sd s6,8(s7) — iov[0].iov_len := len",
         "site_800078d8_pv", "viov vs6",
         "hG17 hpc17 hmi17 hx23_17 hx22_17 hload17 rfl (by rw [hoffiov8]; omega)"
         " (by rw [hoffiov8]; omega) (by rw [hoffiov8]; omega) (by rw [hoffiov8]; omega) hi17",
         memw=("w8", "viov + sign_extend (m := 64) (0x008#12)", "sdData_val vs6", "hoffiov8"))

# === step 19: 78dc li a4,7 ===
std_step(19, 0x800078dc, 0x800078e0, "alu", "li a4,7",
         "site_800078dc_pv", "",
         "hG18 hpc18 hmi18 hload18 rfl hi18",
         rd="14", rdraw="((0#64) + sign_extend (m := 64) (0x007#12))",
         rdfold=["  rw [show ((0#64) + sign_extend (m := 64) (0x007#12) : BitVec 64) = (0x7#64) from by decide] at hx14_19"],
         rdtrack="(0x7#64)")

# === step 20: 78e0 sw a5,232(sp) — store count + 1 ===
std_step(20, 0x800078e0, 0x800078e4, "store", "sw a5,232(sp) — the bumped count",
         "site_800078e0_pv", "vsp " + ADDIW_CNT,
         "hG19 hpc19 hmi19 hx2_19 hx15_19 hload19 rfl (by rw [hoff232]; omega)"
         " (by rw [hoff232]; omega) (by rw [hoff232]; omega) (by rw [hoff232]; omega) hi19",
         memw=("w4", "vsp + sign_extend (m := 64) (0x0e8#12)", "swData " + ADDIW_CNT, "hoff232"))

# === step 21: 78e4 blt a4,a5 NOT taken (count+1 ≤ 7, no flush) ===
std_step(21, 0x800078e4, 0x800078e8, "bnt", "blt a4,a5 NOT taken (no early flush)",
         "site_800078e4_nottaken_pv", "(0x7#64) " + ADDIW_CNT,
         "hG20 hpc20 hmi20 hx14_20 hx15_20 hload20 rfl hcntlt hi20")

# === step 22: 78e8 addi s7,s7,16 ===
std_step(22, 0x800078e8, 0x800078ec, "alu", "addi s7,s7,16 — iov cursor += 16",
         "site_800078e8_pv", "viov",
         "hG21 hpc21 hmi21 hx23_21 hload21 rfl hi21",
         rd="23", rdraw="(viov + sign_extend (m := 64) (0x010#12))")

# === step 23: 78ec andi t1,t1,4 ===
std_step(23, 0x800078ec, 0x800078f0, "alu", "andi t1,t1,4 — t1 := 0",
         "site_800078ec_pv", "vt1",
         "hG22 hpc22 hmi22 hx6_22 hload22 rfl hi22",
         rd="6", rdraw="(vt1 &&& sign_extend (m := 64) (0x004#12))",
         rdfold=["  rw [hflag4z] at hx6_23"],
         rdtrack="(0#64)")

# === step 24: 78f0 beqz t1 TAKEN → 78fc ===
std_step(24, 0x800078f0, 0x800078fc, "bt", "beqz t1 TAKEN",
         "site_800078f0_taken_pv", "(0#64)",
         "hG23 hpc23 hmi23 hx6_23 hload23 rfl (by decide) hi23",
         pc_lines=[
             "  have hpc24 : σ24.regs.get? Register.PC = some (0x800078fc#64) := by",
             "    have := obs_btaken_pc hobs24",
             "    rwa [site_800078f0_taken_pv_tgt] at this"])

# === step 25: 78fc mv a5,t3 ===
std_step(25, 0x800078fc, 0x80007900, "alu", "mv a5,t3",
         "site_800078fc_pv", "vt3",
         "hG24 hpc24 hmi24 hx28_24 hload24 rfl hi24",
         rd="15", rdraw="(vt3 + sign_extend (m := 64) (0x000#12))")

# === step 26: 7900 bge t3,a6 NOT taken (width < len) ===
std_step(26, 0x80007900, 0x80007904, "bnt", "bge t3,a6 NOT taken",
         "site_80007900_nottaken_pv", "vt3 vlen",
         "hG25 hpc25 hmi25 hx28_25 hx16_25 hload25 rfl hwlen hi25")

# === step 27: 7904 mv a5,a6 — vsel := len ===
std_step(27, 0x80007904, 0x80007908, "alu", "mv a5,a6 — the selected length",
         "site_80007904_pv", "vlen",
         "hG26 hpc26 hmi26 hx16_26 hload26 rfl hi26",
         rd="15", rdraw="(vlen + sign_extend (m := 64) (0x000#12))",
         rdfold=["  rw [show (vlen + sign_extend (m := 64) (0x000#12) : BitVec 64) = vlen from by",
                 "    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = (0#64) from by decide]",
                 "    exact BitVec.add_zero vlen] at hx15_27"],
         rdtrack="vlen")

# ---------------------------------------------------------------- tail glue
CHAIN = "(Steps.single hstep27)"
for _j in range(26, 0, -1):
    CHAIN = f"((Steps.single hstep{_j}).trans {CHAIN})"

emit("  -- === the shared call tail 0x7908 → jal __ssprint_r (Spec17) ===",
     "  -- SlotHolds sp+16 / sp+8 transported across the four writes (outermost first)",
     "  have htot27 : SlotHolds vsp 0x010 vtot σ27.mem := by",
     "    rw [hmE27]",
     "    exact slotHolds_writeMap4_i2 vsp 0x010 vtot _ _ _ (by rw [hoff16, hoff232]; omega)",
     "      (slotHolds_writeMap8 vsp 0x010 vtot _ _ _ (Or.inl (by rw [hoff16, hoffiov8]; omega))",
     "        (slotHolds_writeMap8 vsp 0x010 vtot _ _ _ (Or.inl (by rw [hoff16, hoffiov0]; omega))",
     "          (slotHolds_writeMap8 vsp 0x010 vtot _ _ _ (Or.inl (by rw [hoff16, hoff240]; omega)) htot)))",
     "  have hstr27 : SlotHolds vsp 0x008 vstr σ27.mem := by",
     "    rw [hmE27]",
     "    exact slotHolds_writeMap4_i2 vsp 0x008 vstr _ _ _ (by rw [hoff8, hoff232]; omega)",
     "      (slotHolds_writeMap8 vsp 0x008 vstr _ _ _ (Or.inl (by rw [hoff8, hoffiov8]; omega))",
     "        (slotHolds_writeMap8 vsp 0x008 vstr _ _ _ (Or.inl (by rw [hoff8, hoffiov0]; omega))",
     "          (slotHolds_writeMap8 vsp 0x008 vstr _ _ _ (Or.inl (by rw [hoff8, hoff240]; omega)) hstr)))",
     "  obtain ⟨c', hs', hG', hpc', hx1', hx10', hx11', hx12', hx2', hx5', hx6', hx8',",
     "    hx16', hx20', hx22', hx23', hx26', hx28', hmem', htick', hmi', hkeep'⟩ :=",
     "    iov2Tail_spec vsp (0#64) (0#64) v8 (vcur + vs6) vlen",
     "      " + SUBW_PREC + " vs6",
     "      (viov + sign_extend (m := 64) (0x010#12)) vbase vt3 vlen vstr vtot",
     "      ⟨σ27, i27, " + steps_expr(27) + "⟩ hG27 hpc27 hx2_27 hx5_27 hx6_27 hx8_27",
     "      hx12_27 hx15_27 hx16_27 hx20_27 hx22_27 hx23_27 hx26_27 hx28_27",
     "      hload27 hfp27 htot27 hstr27 hvc2 hspwin hsphi hspalign hi27",
     "  -- final memory shape",
     "  have hmemF : c'.σ.mem = writeMap8",
     "      (writeMap4",
     "        (writeMap8",
     "          (writeMap8",
     "            (writeMap8 c.σ.mem",
     "              ((vsp + sign_extend (m := 64) (0x0f0#12)).toNat) (sdData_val (vcur + vs6)))",
     "            ((viov + sign_extend (m := 64) (0x000#12)).toNat) (sdData_val vbase))",
     "          ((viov + sign_extend (m := 64) (0x008#12)).toNat) (sdData_val vs6))",
     "        ((vsp + sign_extend (m := 64) (0x0e8#12)).toNat)",
     "          (swData " + ADDIW_CNT + "))",
     "      ((vsp + sign_extend (m := 64) (0x010#12)).toNat)",
     "        (sdData_val (sign_extend (m := 64)",
     "          (Sail.BitVec.extractLsb vlen 31 0 + Sail.BitVec.extractLsb vtot 31 0))) := by",
     "    rw [hmem']",
     "    show writeMap8 σ27.mem _ _ = _",
     "    rw [hmE27]",
     "  -- KeepRegs over the 27 emitted steps, then the tail's",
     "  have hkeep27 : KeepRegs midRegs5 c.σ σ27 := by",
     "    have h0 := keep_rfl midRegs5 c.σ",
     "    have h1 := keep_alu hobs1 (by decide) h0",
     "    have h2 := keep_alu hobs2 (by decide) h1",
     "    have h3 := keep_alu hobs3 (by decide) h2",
     "    have h4 := keep_btaken hobs4 (by decide) h3",
     "    have h5 := keep_alu hobs5 (by decide) h4",
     "    have h6 := keep_bnottaken hobs6 (by decide) h5",
     "    have h7 := keep_alu hobs7 (by decide) h6",
     "    have h8 := keep_bnottaken hobs8 (by decide) h7",
     "    have h9 := keep_alu hobs9 (by decide) h8",
     "    have h10 := keep_btaken hobs10 (by decide) h9",
     "    have h11 := keep_alu hobs11 (by decide) h10",
     "    have h12 := keep_bnottaken hobs12 (by decide) h11",
     "    have h13 := keep_alu hobs13 (by decide) h12",
     "    have h14 := keep_alu hobs14 (by decide) h13",
     "    have h15 := keep_store hobs15 (by decide) h14",
     "    have h16 := keep_alu hobs16 (by decide) h15",
     "    have h17 := keep_store hobs17 (by decide) h16",
     "    have h18 := keep_store hobs18 (by decide) h17",
     "    have h19 := keep_alu hobs19 (by decide) h18",
     "    have h20 := keep_store hobs20 (by decide) h19",
     "    have h21 := keep_bnottaken hobs21 (by decide) h20",
     "    have h22 := keep_alu hobs22 (by decide) h21",
     "    have h23 := keep_alu hobs23 (by decide) h22",
     "    have h24 := keep_btaken hobs24 (by decide) h23",
     "    have h25 := keep_alu hobs25 (by decide) h24",
     "    have h26 := keep_bnottaken hobs26 (by decide) h25",
     "    exact keep_alu hobs27 (by decide) h26",
     "  have hkeepF : KeepRegs midRegs5 c.σ c'.σ := keep_trans hkeep27 hkeep'",
     "  -- assemble the Steps chain: c → σ27 → c'",
     "  have hchain : Steps c ⟨σ27, i27, " + steps_expr(27) + "⟩ :=",
     "    " + CHAIN[1:-1],
     "  exact ⟨c', hchain.trans hs', hG', hpc', hx1', hx10', hx11', hx12', hx2', hx5',",
     "    hx6', hx8', hx16', hx20', hx22', hx23', hx26', hx28', hmemF, htick', hmi', hkeepF⟩",
     "",
     "end Vsa.Sim",
     "")

import pathlib
out = pathlib.Path("Vsa/Sim/SnprintfSpec49.lean")
out.write_text("\n".join(L))
print(f"wrote {out} ({len(L)} lines)")
