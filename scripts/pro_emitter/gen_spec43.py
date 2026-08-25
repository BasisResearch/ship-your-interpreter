#!/usr/bin/env python3
"""Emit Vsa/Sim/SnprintfSpec43.lean — `fastToPrint_neg_spec`:
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

emit("import Vsa.Sim.SnprintfSitesFast",
     "import Vsa.Sim.SnprintfSitesFast2",
     "import Vsa.Sim.SnprintfSpec7",
     "",
     "/-!",
     "# M3 Layer-3 — `SnprintfSpec43` : the single-digit fast path, negative arm (`_f43`)",
     "",
     "From the fast/multi split `0x80008100` with magnitude `w` in `a4`, `w.toNat ≤ 9`:",
     "the machine skips the decimal loop entirely — `bltu` at `0x80008104` falls",
     "through, `addiw a4,a4,48` forms the single digit character, `sb a4,347(sp)`",
     "stores it at the buffer top-1, the `blez s4` precision test (default `s4 < 1`)",
     "jumps to the `0x80008ea4` tail block (sign read-back `lbu t5,167(sp)`, `a6:=1`,",
     "`t6:=0`, `s6:=1` = len, `s10:=sp+347` = digit base, `j 0x8128`), the parse slot",
     "`sp+0x20` is re-zeroed, and the seam `0x8000812c` (`beqz t5` NOT taken — the",
     "sign byte is `'-'`) bumps `a6` to `2 = len+1` and hops via `0x8088`/`0xa830`",
     "to the PRINT entry `0x8000782c` — the SAME landing state shape as",
     "`exitToPrint_spec` (SnprintfSpec7) with `p = 0`.",
     "",
     "Sites: `_fs`/`_fs2` (generated, `SnprintfSitesFast{,2}`) + the `_fl` seam",
     "sites (SnprintfSitesFlush) + `site_80008100_sn5` (SnprintfSites3).",
     "Arm-tail code pins: `Code/ArmPins.lean` (`ArmPinsLoaded`).",
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
     "/-- `ArmPinsLoaded` survives a byte store at a key above `0x80009000` (the",
     "arm-pin ranges end at `0x80008ebc`). -/",
     "theorem armPins_insert_43 (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)",
     "    (hk : 0x80009000 ≤ k) (h : ArmPinsLoaded mem) : ArmPinsLoaded (mem.insert k v) := by",
     "  unfold ArmPinsLoaded Vsa.Sim.Code.armPinsChunk0 at h ⊢",
     "  simp (disch := omega) only [getElem?_insert_above_sn4 mem k v hk]",
     "  exact h",
     "",
     "theorem armPins_writeMap8_43 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat)",
     "    (d : BitVec (8 * 8)) (ha : 0x80009000 ≤ a) (h : ArmPinsLoaded mem) :",
     "    ArmPinsLoaded (writeMap8 mem a d) :=",
     "  armPins_insert_43 _ _ _ (by omega) (armPins_insert_43 _ _ _ (by omega)",
     "    (armPins_insert_43 _ _ _ (by omega) (armPins_insert_43 _ _ _ (by omega)",
     "    (armPins_insert_43 _ _ _ (by omega) (armPins_insert_43 _ _ _ (by omega)",
     "    (armPins_insert_43 _ _ _ (by omega) (armPins_insert_43 _ _ _ (by omega) h)))))))",
     "",
     "/-- The single-digit emit byte: for `w.toNat ≤ 9`, the `addiw a4,a4,48` output",
     "truncated to the stored byte is `ofNat 8 (48 + w.toNat)` (`emit_byte` at the",
     "abstract register value). -/",
     "theorem fast_digit_byte_43 (w : BitVec 64) (hw : w.toNat ≤ 9) :",
     f"    stData 1 {A4}",
     "      = BitVec.ofNat 8 (48 + w.toNat) := by",
     "  have h := emit_byte w.toNat (by omega)",
     "  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h",
     "",
     "/-- **The single-digit fast path, negative arm**: `0x80008100 → 0x8000782c`.",
     "",
     "Entry: magnitude `w` in `a4` with `w.toNat ≤ 9`, the parsed width/precision",
     "`v20` in `s4` with `v20.toInt < 1` (the `%lld` default is `-1`), the sign byte",
     "`sb ≠ 0` at `sp+167`.  Exit at the PRINT entry with the one-digit buffer",
     "(`BufInv (entryTop vsp) w.toNat 1`, digit at `sp+347`), `s6 = x22 = 1` (len),",
     "`a6 = x16 = 2` (len+1, sign included), `s10 = x26 = sp+347` (digit base),",
     "`t5 = x30` = the sign byte, `t6 = x31 = 0`, slot `sp+0x20` zeroed, the",
     "carried registers intact, and a pointwise frame outside the digit byte and",
     "the two zeroed spill windows. -/",
     "theorem fastToPrint_neg_spec",
     "    (w vsp vt1 v8 v20 v23 v28 : BitVec 64) (sb : BitVec 8)",
     "    (c : Config)",
     "    (hG : GoodState c.σ)",
     "    (hload : SvfprintfSliceLoaded c.σ.mem)",
     "    (hfp : FlushPinsLoaded c.σ.mem)",
     "    (hap : ArmPinsLoaded c.σ.mem)",
     "    (hpc : c.σ.regs.get? Register.PC = some (0x80008100#64))",
     "    (hx14 : c.σ.regs.get? Register.x14 = some w)",
     "    (hx2 : c.σ.regs.get? Register.x2 = some vsp)",
     "    (hx6 : c.σ.regs.get? Register.x6 = some vt1)",
     "    (hx8 : c.σ.regs.get? Register.x8 = some v8)",
     "    (hx20 : c.σ.regs.get? Register.x20 = some v20)",
     "    (hx23 : c.σ.regs.get? Register.x23 = some v23)",
     "    (hx28 : c.σ.regs.get? Register.x28 = some v28)",
     "    (hmag9 : w.toNat ≤ 9)",
     "    (hwneg : v20.toInt < 1)",
     "    (hsb : c.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some sb)",
     "    (hsbne : ((zero_extend (m := 64) sb : BitVec 64) == (0#64)) = false)",
     "    (htlo : tohostAddr + 16 + 64 ≤ vsp.toNat)",
     "    (hhi : vsp.toNat + 356 ≤ 0x100000000)",
     "    (halign : vsp.toNat % 8 = 0)",
     "    (htick : c.tick < 2) :",
     "    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧",
     "      c'.σ.regs.get? Register.PC = some (0x8000782c#64) ∧",
     "      c'.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 1) ∧",
     "      c'.σ.regs.get? Register.x16 = some (BitVec.ofNat 64 2) ∧",
     "      c'.σ.regs.get? Register.x30 = some (zero_extend (m := 64) sb) ∧",
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
     "      BufInv (entryTop vsp) w.toNat 1 c'.σ.mem ∧",
     "      KeepRegs midRegs5 c.σ c'.σ ∧",
     "      (∀ a : Nat, a ≠ vsp.toNat + 347 →",
     "        ¬(vsp.toNat + 32 ≤ a ∧ a < vsp.toNat + 40) →",
     "        ¬(vsp.toNat + 48 ≤ a ∧ a < vsp.toNat + 64) →",
     "        c'.σ.mem[a]? = c.σ.mem[a]?) ∧",
     "      c'.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some sb ∧",
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
     "  -- the bltu guard: 9 < w is FALSE (m ≤ 9)",
     "  have hg9 : zopz0zI_u ((0#64) + sign_extend (m := 64) (0x009#12)) w = false := by",
     "    unfold zopz0zI_u",
     "    simp only [Sail.BitVec.toNatInt,",
     "      show ((0#64) + sign_extend (m := 64) (0x009#12) : BitVec 64).toNat = 9 from by decide]",
     "    apply decide_eq_false",
     "    intro hc",
     "    exact absurd (Int.ofNat_lt.mp hc) (by omega)",
     "  -- the blez guard: s4 ≤ 0 is TRUE (default precision -1)",
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
     "  have hx14_0 := hx14",
     "  have hload0 : SvfprintfSliceLoaded c.σ.mem := hload",
     "  have hfp0 : FlushPinsLoaded c.σ.mem := hfp",
     "  have hap0 : ArmPinsLoaded c.σ.mem := hap",
     "  have hsb0 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some sb := hsb")

track = {"2": ("vsp", None), "6": ("vt1", None), "20": ("v20", None),
         "23": ("v23", None), "8": ("v8", None), "28": ("v28", None),
         "14": ("w", None)}

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

# === step 1: 8100 li a5,9 (SvfSlice, _sn5 battery) ===
std_step(1, 0x80008100, 0x80008104, "alu", "li a5,9",
         "site_80008100_sn5", "",
         "hG hpc hmi0 hload0 rfl htick",
         rd="15", rdval="((0#64) + sign_extend (m := 64) (0x009#12))")

# === step 2: 8104 bltu a5,a4 NOT taken ===
std_step(2, 0x80008104, 0x80008108, "bnt", "bltu a5,a4 NOT taken (w ≤ 9)",
         "site_80008104_nottaken_fs",
         "((0#64) + sign_extend (m := 64) (0x009#12)) w",
         "hG1 hpc1 hmi1 hx15_1 hx14_1 hload1 rfl hg9 hi1",
         drop=("15",))

# === step 3: 8108 addiw a4,a4,48 ===
std_step(3, 0x80008108, 0x8000810c, "alu", "addiw a4,a4,48 — the digit char",
         "site_80008108_fs", "w",
         "hG2 hpc2 hmi2 hx14_2 hload2 rfl hi2",
         rd="14", rdval=A4)

# === step 4: 810c sb a4,347(sp) ===
CLS, ADDR = "store", 0x8000810c
step_header(4, 0x8000810c, "sb a4,347(sp) — the single digit byte",
            "site_8000810c_fs", f"vsp {A4}",
            "hG3 hpc3 hmi3 hx2_3 hx14_3 hload3 rfl (by rw [hoff347]; omega) (by rw [hoff347]; omega) (by rw [hoff347]; omega) hi3")
pc_add4(4, 0x8000810c, 0x80008110)
minstret(4, "store")
thread_regs(4, "store")
track.pop("14", None)
emit("  have hNP3b : (afterNextPC (afterPrelude σ3) (0x8000810c#64)).mem = σ3.mem := rfl",
     "  have hload4 : SvfprintfSliceLoaded σ4.mem := by",
     "    rw [hmem4, hNP3b]; exact svfprintfSlice_insert_sn4 _ _ _ (by rw [hoff347]; omega) hload3",
     "  have hfp4 : FlushPinsLoaded σ4.mem := by",
     "    rw [hmem4, hNP3b]; exact flushPins_insert_fl _ _ _ (by rw [hoff347]; omega) hfp3",
     "  have hap4 : ArmPinsLoaded σ4.mem := by",
     "    rw [hmem4, hNP3b]; exact armPins_insert_43 _ _ _ (by rw [hoff347]; omega) hap3",
     "  have hsb4 : σ4.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some sb := by",
     "    rw [hmem4, hNP3b, getElem_insert_ne _ ((vsp + sign_extend (m := 64) (0x0a7#12)).toNat) ((vsp + sign_extend (m := 64) (0x15b#12)).toNat) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; rw [hoff347, hoff167]; omega)]",
     "    exact hsb3",
     "  have hdig4 : σ4.mem[vsp.toNat + 347]? = some (BitVec.ofNat 8 (48 + w.toNat)) := by",
     "    rw [hmem4, hNP3b, hoff347, ← fast_digit_byte_43 w hmag9]",
     "    exact getElem_insert_self _ _ _",
     "")
have_dig = True

# === step 5: 8110 sext.w a6,s4 (dead value) ===
std_step(5, 0x80008110, 0x80008114, "alu", "sext.w a6,s4 (value dead)",
         "site_80008110_fs", "v20",
         "hG4 hpc4 hmi4 hx20_4 hload4 rfl hi4",
         rd="16",
         rdval="(sign_extend (m := 64) (Sail.BitVec.extractLsb (v20 + sign_extend (m := 64) (0x000#12)) 31 0))")

# === step 6: 8114 blez s4 TAKEN → 8ea4 ===
std_step(6, 0x80008114, 0x80008ea4, "bt", "blez s4 TAKEN (default precision < 1)",
         "site_80008114_taken_fs", "v20",
         "hG5 hpc5 hmi5 hx20_5 hload5 rfl hgblez hi5",
         pc_lines=[
             "  have hpc6 : σ6.regs.get? Register.PC = some (0x80008ea4#64) := by",
             "    have := obs_btaken_pc hobs6",
             "    rwa [site_80008114_taken_fs_tgt] at this"],
         drop=("16",))

# === step 7: 8ea4 lbu t5,167(sp) — sign read-back ===
std_step(7, 0x80008ea4, 0x80008ea8, "alu", "lbu t5,167(sp) — sign read-back",
         "site_80008ea4_fs2", "vsp sb",
         "hG6 hpc6 hmi6 hx2_6 hap6 rfl (by rw [hoff167]; omega) (by rw [hoff167]; omega) (Or.inr (by rw [hoff167]; omega)) hsb6 hi6",
         rd="30", rdval=SB64)

# === step 8: 8ea8 li a6,1 ===
std_step(8, 0x80008ea8, 0x80008eac, "alu", "li a6,1",
         "site_80008ea8_fs2", "",
         "hG7 hpc7 hmi7 hap7 rfl hi7",
         rd="16", rdval=X16A)

# === step 9: 8eac li t6,0 ===
std_step(9, 0x80008eac, 0x80008eb0, "alu", "li t6,0",
         "site_80008eac_fs2", "",
         "hG8 hpc8 hmi8 hap8 rfl hi8",
         rd="31", rdval="((0#64) + sign_extend (m := 64) (0x000#12))",
         rdfold=[
             "  rw [show ((0#64) + sign_extend (m := 64) (0x000#12) : BitVec 64) = (0#64) from by decide] at hx31_9"])
track["31"] = ("(0#64)", None)

# === step 10: 8eb0 li s6,1 ===
std_step(10, 0x80008eb0, 0x80008eb4, "alu", "li s6,1 — the length",
         "site_80008eb0_fs2", "",
         "hG9 hpc9 hmi9 hap9 rfl hi9",
         rd="22", rdval=X16A)

# === step 11: 8eb4 addi s10,sp,347 — digit base ===
std_step(11, 0x80008eb4, 0x80008eb8, "alu", "addi s10,sp,347 — the digit base",
         "site_80008eb4_fs2", "vsp",
         "hG10 hpc10 hmi10 hx2_10 hap10 rfl hi10",
         rd="26", rdval="(vsp + sign_extend (m := 64) (0x15b#12))")

# === step 12: 8eb8 j 8128 ===
std_step(12, 0x80008eb8, 0x80008128, "j", "j 0x80008128",
         "site_80008eb8_fs2", "",
         "hG11 hpc11 hmi11 hap11 rfl (by decide) hi11",
         pc_lines=[
             "  have hpc12 : σ12.regs.get? Register.PC = some (0x80008128#64) := by",
             "    have := obs_jx0_pc_sn5 hobs12",
             "    rwa [show (0x80008eb8#64 : BitVec 64) + sign_extend (m := 64) (0x1ff270#21)",
             "      = (0x80008128#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this"])

# === step 13: 8128 sd zero,32(sp) ===
CLS, ADDR = "store", 0x80008128
step_header(13, 0x80008128, "sd zero,32(sp) — the parse slot re-zeroed",
            "site_80008128_fs", "vsp",
            "hG12 hpc12 hmi12 hx2_12 hload12 rfl (by rw [hoff32]; omega) (by rw [hoff32]; omega) (by rw [hoff32]; omega) (by rw [hoff32]; omega) hi12")
pc_add4(13, 0x80008128, 0x8000812c)
minstret(13, "store")
thread_regs(13, "store")
thread_mem_w8(13, "hoff32", None)
emit("  have hs32z13 : SlotHolds vsp 0x020 (0#64) σ13.mem := by",
     "    rw [hmem13, hNP12b]",
     "    exact slotHolds_self vsp 0x020 _ (0#64) σ12.mem rfl",
     "")
have_s32z = True

# === step 14: 812c beqz t5 NOT taken (sign byte ≠ 0) ===
std_step(14, 0x8000812c, 0x80008130, "bnt", "beqz t5 NOT taken (sign byte ≠ 0)",
         "site_8000812c_nottaken_fl", SB64,
         "hG13 hpc13 hmi13 hx30_13 hload13 rfl hsbne hi13")

# === step 15: 8130 addiw a6,a6,1 → a6 = 2 ===
std_step(15, 0x80008130, 0x80008134, "alu", "addiw a6,a6,1 ⇒ a6 := 2 = len+1",
         "site_80008130_fl", X16A,
         "hG14 hpc14 hmi14 hx16_14 hload14 rfl hi14",
         rd="16",
         rdval="(sign_extend (m := 64) (Sail.BitVec.extractLsb ("
               + X16A + " + sign_extend (m := 64) (0x001#12)) 31 0))",
         rdfold=[
             "  rw [show (sign_extend (m := 64) (Sail.BitVec.extractLsb (((0#64) + sign_extend (m := 64) (0x001#12)) + sign_extend (m := 64) (0x001#12)) 31 0) : BitVec 64) = BitVec.ofNat 64 2 from by apply BitVec.eq_of_toNat_eq; decide] at hx16_15"])
track["16"] = ("(BitVec.ofNat 64 2)", None)

# === step 16: 8134 j 8088 ===
std_step(16, 0x80008134, 0x80008088, "j", "j 0x80008088",
         "site_80008134_fl", "",
         "hG15 hpc15 hmi15 hload15 rfl (by decide) hi15",
         pc_lines=[
             "  have hpc16 : σ16.regs.get? Register.PC = some (0x80008088#64) := by",
             "    have := obs_jx0_pc_sn5 hobs16",
             "    rwa [show (0x80008134#64 : BitVec 64) + sign_extend (m := 64) (0x1fff54#21)",
             "      = (0x80008088#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this"])

# === step 17: 8088 bnez t6 NOT taken ===
std_step(17, 0x80008088, 0x8000808c, "bnt", "bnez t6 NOT taken (t6 = 0)",
         "site_80008088_nottaken_fl", "(0#64)",
         "hG16 hpc16 hmi16 hx31_16 hload16 rfl (by decide) hi16")

# === step 18: 808c j a830 ===
std_step(18, 0x8000808c, 0x8000a830, "j", "j 0x8000a830",
         "site_8000808c_fl", "",
         "hG17 hpc17 hmi17 hload17 rfl (by decide) hi17",
         pc_lines=[
             "  have hpc18 : σ18.regs.get? Register.PC = some (0x8000a830#64) := by",
             "    have := obs_jx0_pc_sn5 hobs18",
             "    rwa [show (0x8000808c#64 : BitVec 64) + sign_extend (m := 64) (0x0027a4#21)",
             "      = (0x8000a830#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this"])

# === step 19: a830 sd zero,56(sp) ===
CLS, ADDR = "store", 0x8000a830
step_header(19, 0x8000a830, "sd zero,56(sp)",
            "site_8000a830_fl", "vsp",
            "hG18 hpc18 hmi18 hx2_18 hfp18 rfl (by rw [hoff56]; omega) (by rw [hoff56]; omega) (by rw [hoff56]; omega) (by rw [hoff56]; omega) hi18")
pc_add4(19, 0x8000a830, 0x8000a834)
minstret(19, "store")
thread_regs(19, "store")
thread_mem_w8(19, "hoff56", None)
emit("")

# === step 20: a834 sd zero,48(sp) ===
CLS, ADDR = "store", 0x8000a834
step_header(20, 0x8000a834, "sd zero,48(sp)",
            "site_8000a834_fl", "vsp",
            "hG19 hpc19 hmi19 hx2_19 hfp19 rfl (by rw [hoff48]; omega) (by rw [hoff48]; omega) (by rw [hoff48]; omega) (by rw [hoff48]; omega) hi19")
pc_add4(20, 0x8000a834, 0x8000a838)
minstret(20, "store")
thread_regs(20, "store")
thread_mem_w8(20, "hoff48", None)
emit("")

# === step 21: a838 j 782c ===
std_step(21, 0x8000a838, 0x8000782c, "j", "j 0x8000782c — the PRINT entry",
         "site_8000a838_fl", "",
         "hG20 hpc20 hmi20 hfp20 rfl (by decide) hi20",
         pc_lines=[
             "  have hpc21 : σ21.regs.get? Register.PC = some (0x8000782c#64) := by",
             "    have := obs_jx0_pc_sn5 hobs21",
             "    rwa [show (0x8000a838#64 : BitVec 64) + sign_extend (m := 64) (0x1fcff4#21)",
             "      = (0x8000782c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this"])

# === post assembly ===
emit("  -- x22 = 1 (fold the li form)",
     "  rw [show ((0#64) + sign_extend (m := 64) (0x001#12) : BitVec 64) = BitVec.ofNat 64 1 from by",
     "    apply BitVec.eq_of_toNat_eq; decide] at hx22_21",
     "  -- x26 = ofNat (top−1)",
     "  rw [show (vsp + sign_extend (m := 64) (0x15b#12) : BitVec 64)",
     "      = BitVec.ofNat 64 ((entryTop vsp).toNat - 1) from by",
     "    apply BitVec.eq_of_toNat_eq",
     "    rw [hoff347, htop_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]] at hx26_21",
     "  -- the one-digit buffer",
     "  have hbuf : BufInv (entryTop vsp) w.toNat 1 σ21.mem := by",
     "    intro j hj",
     "    have hj0 : j = 0 := by omega",
     "    subst hj0",
     "    have hkey : (entryTop vsp).toNat - 1 - 0 = vsp.toNat + 347 := by",
     "      rw [htop_toNat]; omega",
     "    have hval : 48 + (w.toNat / 10 ^ 0) % 10 = 48 + w.toNat := by",
     "      simp only [Nat.pow_zero, Nat.div_one]",
     "      rw [Nat.mod_eq_of_lt (by omega)]",
     "    rw [hkey, hval]",
     "    exact hdig21",
     "  -- mid-register preservation across all 21 steps",
     "  have hkeep : KeepRegs midRegs5 c.σ σ21 := by",
     "    have h0 := keep_rfl midRegs5 c.σ",
     "    have h1 := keep_alu hobs1 (by decide) h0",
     "    have h2 := keep_bnottaken hobs2 (by decide) h1",
     "    have h3 := keep_alu hobs3 (by decide) h2",
     "    have h4 := keep_store hobs4 (by decide) h3",
     "    have h5 := keep_alu hobs5 (by decide) h4",
     "    have h6 := keep_btaken hobs6 (by decide) h5",
     "    have h7 := keep_alu hobs7 (by decide) h6",
     "    have h8 := keep_alu hobs8 (by decide) h7",
     "    have h9 := keep_alu hobs9 (by decide) h8",
     "    have h10 := keep_alu hobs10 (by decide) h9",
     "    have h11 := keep_alu hobs11 (by decide) h10",
     "    have h12 := keep_jr hobs12 (by decide) h11",
     "    have h13 := keep_store hobs13 (by decide) h12",
     "    have h14 := keep_bnottaken hobs14 (by decide) h13",
     "    have h15 := keep_alu hobs15 (by decide) h14",
     "    have h16 := keep_jr hobs16 (by decide) h15",
     "    have h17 := keep_bnottaken hobs17 (by decide) h16",
     "    have h18 := keep_jr hobs18 (by decide) h17",
     "    have h19 := keep_store hobs19 (by decide) h18",
     "    have h20 := keep_store hobs20 (by decide) h19",
     "    exact keep_jr hobs21 (by decide) h20",
     "  -- pointwise frame outside the digit byte + the two zeroed spill windows",
     "  have hmframe : ∀ a : Nat, a ≠ vsp.toNat + 347 →",
     "      ¬(vsp.toNat + 32 ≤ a ∧ a < vsp.toNat + 40) →",
     "      ¬(vsp.toNat + 48 ≤ a ∧ a < vsp.toNat + 64) →",
     "      σ21.mem[a]? = c.σ.mem[a]? := by",
     "    intro a hd hA hB",
     "    rw [hmem21, hmem20, hNP19b, getElem?_writeMap8_out _ _ _ _ (by rw [hoff48]; omega),",
     "      hmem19, hNP18b, getElem?_writeMap8_out _ _ _ _ (by rw [hoff56]; omega),",
     "      hmem18, hmem17, hmem16, hmem15, hmem14,",
     "      hmem13, hNP12b, getElem?_writeMap8_out _ _ _ _ (by rw [hoff32]; omega),",
     "      hmem12, hmem11, hmem10, hmem9, hmem8, hmem7, hmem6, hmem5,",
     "      hmem4, hNP3b, getElem_insert_ne _ a ((vsp + sign_extend (m := 64) (0x15b#12)).toNat) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; rw [hoff347]; omega),",
     "      hmem3, hmem2, hmem1]",
     "  refine ⟨⟨σ21, i21, " + steps_expr(21) + "⟩, ?_, hG21, hpc21, hx22_21, hx16_21,",
     "    hx30_21, hx31_21, hx20_21, hx6_21, hx28_21, hx23_21, hx8_21, hx2_21, hx26_21,",
     "    hi21, hG21.minstret, hs32z21, hbuf, hkeep, hmframe, hsb21, hload21, hfp21, hap21⟩")
chain = f"(Steps.single hstep21)"
for j in range(20, 0, -1):
    chain = f"((Steps.single hstep{j}).trans {chain})"
emit("  exact " + chain[1:-1])
emit("", "end Vsa.Sim", "")

import pathlib
out = pathlib.Path("Vsa/Sim/SnprintfSpec43.lean")
out.write_text("\n".join(L))
print(f"wrote {out} ({len(L)} lines)")
