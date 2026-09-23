import VsaIris.Vsa.Tools
import VsaIris.Vsa.MallocConsumer
import Vsa.Sim.EnvNewSuccessSuffix

namespace VsaIris.Inst.EnvNew

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config Step MState)
open Vsa.Sim Vsa.MemRepr

/-! ## Code -/

def envNewCode : List (BitVec 8) :=
  [0x13#8, 0x01#8, 0x01#8, 0xff#8, 0x23#8, 0x30#8, 0x81#8, 0x00#8, 0x13#8, 0x04#8, 0x05#8, 0x00#8,
   0x13#8, 0x05#8, 0x00#8, 0x02#8, 0x23#8, 0x34#8, 0x11#8, 0x00#8, 0xef#8, 0x10#8, 0x10#8, 0x58#8,
   0x63#8, 0x02#8, 0x05#8, 0x02#8, 0x83#8, 0x30#8, 0x81#8, 0x00#8, 0x23#8, 0x3c#8, 0x85#8, 0x00#8,
   0x03#8, 0x34#8, 0x01#8, 0x00#8, 0x23#8, 0x30#8, 0x05#8, 0x00#8, 0x23#8, 0x34#8, 0x05#8, 0x00#8,
   0x23#8, 0x38#8, 0x05#8, 0x00#8, 0x13#8, 0x01#8, 0x01#8, 0x01#8, 0x67#8, 0x80#8, 0x00#8, 0x00#8,
   0x83#8, 0xb7#8, 0x01#8, 0x46#8, 0x13#8, 0x06#8, 0xe0#8, 0x00#8, 0x93#8, 0x05#8, 0x10#8, 0x00#8,
   0x83#8, 0xb6#8, 0x87#8, 0x01#8, 0x17#8, 0x65#8, 0x01#8, 0x00#8, 0x13#8, 0x05#8, 0x85#8, 0x5f#8,
   0xef#8, 0x20#8, 0x10#8, 0x01#8, 0x13#8, 0x05#8, 0x10#8, 0x00#8, 0xef#8, 0x10#8, 0xd0#8, 0x50#8]

abbrev codeBase : Nat := 0x800029fc

theorem loaded_of_code {m : Std.ExtHashMap Nat (BitVec 8)}
    (h : ∀ p ∈ codeFoot codeBase envNewCode, m[p.1]? = some p.2.2) : Code.Env_newLoaded m := by
  have h' : ∀ a b, (a, b) ∈ envNewCode.zipIdx.map (fun p => (codeBase + p.2, p.1)) →
      m[a]? = some b := by
    intro a b hab
    obtain ⟨q, hq, e⟩ := List.mem_map.mp hab
    cases e
    exact h _ (List.mem_map_of_mem (f := fun p => (codeBase + p.2, DFrac.discard, p.1)) hq)
  unfold Code.Env_newLoaded Code.env_newChunk0 Code.env_newChunk1
  repeat' apply And.intro
  all_goals (apply h'; decide)

/-- An 8-byte store at `base + off` inside a `size`-byte window satisfies
its `MemFacts` (the geometry `EnvNewCallerGeom`/`EnvNewFreshGeom` records). -/
theorem storeFact {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs} {a : MInstr}
    {bs : List (BitVec 8)} (base : BitVec 64) (off size : Nat)
    (hlo : 0x80000000 ≤ base.toNat) (hhi : base.toNat + size ≤ 0x100000000)
    (hwin : tohostAddr + 16 ≤ base.toNat) (halign : base.toNat % 8 = 0)
    (hk : a.kind = .sd) (hsrc : srcVal a.rs1 L = base)
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hoff : off + 8 ≤ size) (hoff8 : off % 8 = 0) : MemFacts m L bs a := by
  have hea : (eaddrM a L).toNat = base.toNat + off := by
    unfold eaddrM
    rw [hsrc, BitVec.toNat_add, himm, Nat.mod_eq_of_lt (by omega)]
  unfold MemFacts
  rw [hk]
  exact ⟨by rw [hea]; omega, by rw [hea]; omega, by rw [hea]; omega, by rw [hea]; omega⟩

/-! ## The prefix: `addi sp,-16; sd s0,0(sp); mv s0,a0; li a0,32; sd ra,8(sp)` -/

#derive_case envNewPrefixSeg chain
  [(0x800029fc#64, 0xff010113#32),
   (0x80002a00#64, 0x00813023#32),
   (0x80002a04#64, 0x00050413#32),
   (0x80002a08#64, 0x02000513#32),
   (0x80002a0c#64, 0x00113423#32)]

abbrev prefixL (esp s0v par r : BitVec 64) : GRegs := [(2, esp), (8, s0v), (10, par), (1, r)]

theorem prefix_facts {m : Std.ExtHashMap Nat (BitVec 8)} {esp s0v par r : BitVec 64}
    (hcode : Code.Env_newLoaded m) (hg : EnvNewCallerGeom (esp - 16#64) r) :
    ChainFacts m m (prefixL esp s0v par r) [] envNewPrefixSeg := by
  unfold envNewPrefixSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.env_new_at_"
  · exact storeFact (esp - 16#64) 0 16 hg.lo hg.hi hg.win hg.align (by decide)
      (by rw [← sp_sub16]; rfl) (by decide) (by decide) (by decide)
  · exact storeFact (esp - 16#64) 8 16 hg.lo hg.hi hg.win hg.align (by decide)
      (by rw [← sp_sub16]; rfl) (by decide) (by decide) (by decide)

theorem prefix_log_raw (esp s0v par r : BitVec 64) :
    (segOut envNewPrefixSeg (prefixL esp s0v par r) []).log =
      [((esp + sign_extend (m := 64) (0xff0#12) + sign_extend (m := 64) (0x000#12)).toNat, 8, s0v),
       ((esp + sign_extend (m := 64) (0xff0#12) + sign_extend (m := 64) (0x008#12)).toNat, 8, r)] :=
  rfl

theorem prefix_fin (esp s0v par r : BitVec 64) :
    finReg envNewPrefixSeg (prefixL esp s0v par r) [] 2 = esp + sign_extend (m := 64) (0xff0#12) ∧
    finReg envNewPrefixSeg (prefixL esp s0v par r) [] 8 = par + sign_extend (m := 64) (0x000#12) ∧
    finReg envNewPrefixSeg (prefixL esp s0v par r) [] 10 = 0#64 + sign_extend (m := 64) (0x020#12) ∧
    finReg envNewPrefixSeg (prefixL esp s0v par r) [] 1 = r :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem prefix_fin' (esp s0v par r : BitVec 64) :
    finReg envNewPrefixSeg [(2, esp), (8, s0v), (10, par), (1, r)] [] 2 = esp - 16#64 ∧
    finReg envNewPrefixSeg [(2, esp), (8, s0v), (10, par), (1, r)] [] 8 = par ∧
    finReg envNewPrefixSeg [(2, esp), (8, s0v), (10, par), (1, r)] [] 10 = 32#64 ∧
    finReg envNewPrefixSeg [(2, esp), (8, s0v), (10, par), (1, r)] [] 1 = r := by
  obtain ⟨h2, h8, h10, h1⟩ := prefix_fin esp s0v par r
  exact ⟨h2.trans (sp_sub16 esp), h8.trans (addi0_env par), h10.trans (by decide), h1⟩

theorem prefix_pc (esp s0v par r : BitVec 64) :
    evalBlocksPC 0x800029fc#64 (SegEvalState.init (prefixL esp s0v par r) []) envNewPrefixSeg =
      0x80002a10#64 := rfl

/-! ## The success suffix (`envNewSuccessSeg`, reflected in VSA) -/

abbrev link : BitVec 64 := 0x80002a14#64

def succL (b p par : BitVec 64) : GRegs := [(2, b), (10, p), (8, par), (1, link)]

/-- The loads of the suffix read the two saved words from the prefix's image. -/
def succLds (mS : Std.ExtHashMap Nat (BitVec 8)) (b : BitVec 64) : List (List (BitVec 8)) :=
  [execRetEpilogueWord mS (b.toNat + 8), execRetEpilogueWord mS b.toNat]

theorem loadFact {m mS : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs} {a : MInstr}
    (base : BitVec 64) (off : Nat)
    (hlo : 0x80000000 ≤ base.toNat) (hhi : base.toNat + 16 ≤ 0x100000000)
    (hwin : tohostAddr + 16 ≤ base.toNat)
    (hk : a.kind = .ld) (hsrc : srcVal a.rs1 L = base)
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off) (hoff : off + 8 ≤ 16)
    (hpin : ∀ k, k < 8 → (m[base.toNat + off + k]?).getD 0 = (mS[base.toNat + off + k]?).getD 0) :
    MemFacts m L (execRetEpilogueWord mS (base.toNat + off)) a := by
  have hea : (eaddrM a L).toNat = base.toNat + off := by
    unfold eaddrM
    rw [hsrc, BitVec.toNat_add, himm, Nat.mod_eq_of_lt (by omega)]
  unfold MemFacts
  rw [hk]
  refine ⟨⟨by rw [hea]; omega, by rw [hea]; omega, by rw [hea]; right; omega⟩, ?_⟩
  rw [hea]
  have h := hpin
  simp only [LPins8, execRetEpilogueWord, List.getD_cons_zero, List.getD_cons_succ]
  exact ⟨by simpa using h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega),
    h 4 (by omega), h 5 (by omega), h 6 (by omega), h 7 (by omega)⟩

theorem succ_facts {m mS : Std.ExtHashMap Nat (BitVec 8)} {b p par r : BitVec 64}
    (hcode : Code.Env_newLoaded m) (hg : EnvNewCallerGeom b r) (hf : EnvNewFreshGeom b p)
    (hra : read64 mS (b.toNat + 8) = some r.toNat)
    (hpin : ∀ k, k < 16 → (m[b.toNat + k]?).getD 0 = (mS[b.toNat + k]?).getD 0) :
    ChainFacts m m (succL b p par) (succLds mS b) envNewSuccessSeg := by
  have hret : BitVec.update r 0 0#1 = r := by
    simpa only [show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 by decide,
      BitVec.add_zero] using ret_tgt r hg.ret_align
  have hra' := execRetEpilogueWord_value _ _ _ hra
  have hp24 : (p + sign_extend (m := 64) (24#12)).toNat = p.toNat + 24 :=
    off24_addr p (by have := hf.hi; omega)
  unfold envNewSuccessSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.env_new_at_"
  · simpa +ground [guardB, succL, srcVal, lookupG, runGM] using
      (beq_eq_false_iff_ne.mpr hf.nonzero)
  · exact loadFact b 8 hg.lo hg.hi hg.win (by decide) rfl (by decide) (by decide)
      (fun k hk => by rw [Nat.add_assoc]; exact hpin (8 + k) (by omega))
  · exact storeFact p 24 32 hf.lo hf.hi hf.win hf.align (by decide) rfl (by decide) (by decide)
      (by decide)
  · change MemFacts
      (applyW m ((p + sign_extend (m := 64) (24#12)).toNat, 8, par))
      _ (execRetEpilogueWord mS (b.toNat + 0)) _
    rw [hp24]
    refine loadFact b 0 hg.lo hg.hi hg.win (by decide) rfl (by decide) (by decide) fun k hk => ?_
    rw [applyW_out m (p.toNat + 24) 8 par _ (by have := hf.stack_disjoint; omega)]
    exact hpin k (by omega)
  · exact storeFact p 0 32 hf.lo hf.hi hf.win hf.align (by decide) rfl (by decide) (by decide)
      (by decide)
  · exact storeFact p 8 32 hf.lo hf.hi hf.win hf.align (by decide) rfl (by decide) (by decide)
      (by decide)
  · exact storeFact p 16 32 hf.lo hf.hi hf.win hf.align (by decide) rfl (by decide) (by decide)
      (by decide)
  · simpa [TermFactsO, TermFactsT, succL, succLds,
      runGM, stepGM, stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM,
      hra', hret,
      show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 by decide] using hg.ret_align

theorem succ_log (mS : Std.ExtHashMap Nat (BitVec 8)) {b p par : BitVec 64}
    (hhi : p.toNat + 32 ≤ 0x100000000) :
    (segOut envNewSuccessSeg (succL b p par) (succLds mS b)).log = envNewSuccessLog p par := by
  have hp8 := off8_addr p (by omega)
  have hp16 := off16_addr p (by omega)
  have hp24 := off24_addr p (by omega)
  simp [segOut, envNewSuccessSeg, evalBlocks, evalBlock, SegEvalState.init,
    succL, succLds, envNewSuccessLog, wlogM, wentryM, widthOfM,
    runGM, stepGM, stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG,
    mkLine, decodeM, eaddrM, hp8, hp16, hp24]

theorem succ_fin (mS : Std.ExtHashMap Nat (BitVec 8)) (b p par : BitVec 64) :
    finReg envNewSuccessSeg (succL b p par) (succLds mS b) 2 = b + sign_extend (m := 64) (0x010#12) ∧
    finReg envNewSuccessSeg (succL b p par) (succLds mS b) 10 = p ∧
    finReg envNewSuccessSeg (succL b p par) (succLds mS b) 8 =
      bytesVal .ld (execRetEpilogueWord mS b.toNat) ∧
    finReg envNewSuccessSeg (succL b p par) (succLds mS b) 1 =
      bytesVal .ld (execRetEpilogueWord mS (b.toNat + 8)) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem succ_pc (mS : Std.ExtHashMap Nat (BitVec 8)) (b p par : BitVec 64) :
    evalBlocksPC 0x80002a14#64 (SegEvalState.init (succL b p par) (succLds mS b)) envNewSuccessSeg =
      BitVec.update (bytesVal .ld (execRetEpilogueWord mS (b.toNat + 8)) +
        sign_extend (m := 64) (0#12)) 0 0#1 := rfl

theorem succ_fin' (mS : Std.ExtHashMap Nat (BitVec 8)) (b p par r s0v : BitVec 64)
    (hra : read64 mS (b.toNat + 8) = some r.toNat) (hs0 : read64 mS b.toNat = some s0v.toNat) :
    finReg envNewSuccessSeg [(2, b), (10, p), (8, par), (1, link)] (succLds mS b) 2 =
      b + sign_extend (m := 64) (0x010#12) ∧
    finReg envNewSuccessSeg [(2, b), (10, p), (8, par), (1, link)] (succLds mS b) 10 = p ∧
    finReg envNewSuccessSeg [(2, b), (10, p), (8, par), (1, link)] (succLds mS b) 8 = s0v ∧
    finReg envNewSuccessSeg [(2, b), (10, p), (8, par), (1, link)] (succLds mS b) 1 = r := by
  obtain ⟨h2, h10, h8, h1⟩ := succ_fin mS b p par
  exact ⟨h2, h10, h8.trans (execRetEpilogueWord_value _ _ _ hs0),
    h1.trans (execRetEpilogueWord_value _ _ _ hra)⟩

theorem succ_pc' (mS : Std.ExtHashMap Nat (BitVec 8)) (b p par r : BitVec 64)
    (hra : read64 mS (b.toNat + 8) = some r.toNat) (halign : r.toNat % 4 = 0) :
    evalBlocksPC 0x80002a14#64 (SegEvalState.init (succL b p par) (succLds mS b))
      envNewSuccessSeg = r := by
  rw [succ_pc, execRetEpilogueWord_value _ _ _ hra]
  simpa only [show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 by decide,
    BitVec.add_zero] using ret_tgt r halign

/-! ## The call site `0x80002a10: jal malloc` -/

abbrev mallocEntry : BitVec 64 := 0x80004790#64
def jalCode : List (BitVec 8) := [0xef#8, 0x10#8, 0x10#8, 0x58#8]

theorem jal_exec (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x80002a10 jalCode, live p.1) :
    JalExec (vsaModel live) 0x80002a10 jalCode mallocEntry := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x80002a10, .discard, 0xef#8) (by simp [codeFoot, jalCode])
  have hb1 := hb (0x80002a11, .discard, 0x10#8) (by simp [codeFoot, jalCode])
  have hb2 := hb (0x80002a12, .discard, 0x10#8) (by simp [codeFoot, jalCode])
  have hb3 := hb (0x80002a13, .discard, 0x58#8) (by simp [codeFoot, jalCode])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x80002a10#64) vm (0x581010ef#32) (0x001d80#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80002a10#64) 4)
      (0xef#8) (0x10#8) (0x10#8) (0x58#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      nr_581010ef_env w_581010ef_env
      (Vsa.Sim.DecodeTable.decode_581010ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x80002a10#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := mallocEntry) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  rwa [show BitVec.addInt (0x80002a10#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x80002a10 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

/-! ## Pure facts the spec consumes -/

/-- The prefix's stack image: the two saved words. -/
abbrev stackImg (Wstk : List (Nat × BitVec 8)) (esp s0v par r : BitVec 64) :
    Std.ExtHashMap Nat (BitVec 8) :=
  writeLog (wbase Wstk) (segOut envNewPrefixSeg (prefixL esp s0v par r) []).log

theorem stackImg_reads (Wstk : List (Nat × BitVec 8)) {esp s0v par r : BitVec 64}
    (hg : EnvNewCallerGeom (esp - 16#64) r) :
    read64 (stackImg Wstk esp s0v par r) ((esp - 16#64).toNat + 8) = some r.toNat ∧
    read64 (stackImg Wstk esp s0v par r) (esp - 16#64).toNat = some s0v.toNat := by
  have h8 := off8_addr (esp - 16#64) (by have := hg.hi; omega)
  unfold stackImg
  rw [prefix_log_raw, sp_sub16, off0_addr, h8]
  change read64 (writeMap8 (writeMap8 (wbase Wstk) (esp - 16#64).toNat (sdData_val s0v))
      ((esp - 16#64).toNat + 8) (sdData_val r)) _ = _ ∧
    read64 (writeMap8 (writeMap8 (wbase Wstk) (esp - 16#64).toNat (sdData_val s0v))
      ((esp - 16#64).toNat + 8) (sdData_val r)) _ = _
  rw [read64_writeMap8, sdData_toNat, read64_writeMap8_disjoint _ _ _ _ (by omega),
    read64_writeMap8, sdData_toNat]
  exact ⟨rfl, rfl⟩

/-- The initialized `Env`: `names = vals = NULL`, `count = cap = 0`,
`parent = par` (`c/src/env.c`). -/
def EnvImage (m : Std.ExtHashMap Nat (BitVec 8)) (p par : BitVec 64) : Prop :=
  read64 m p.toNat = some 0 ∧ read64 m (p.toNat + 8) = some 0 ∧
  read64 m (p.toNat + 16) = some 0 ∧ read64 m (p.toNat + 24) = some par.toNat

theorem envImage_of_log (m : Std.ExtHashMap Nat (BitVec 8)) (p par : BitVec 64) :
    EnvImage (writeLog m (envNewSuccessLog p par)) p par := by
  change EnvImage (writeMap8 (writeMap8 (writeMap8 (writeMap8 m (p.toNat + 24) (sdData_val par))
    p.toNat (sdData_val 0#64)) (p.toNat + 8) (sdData_val 0#64)) (p.toNat + 16) (sdData_val 0#64))
    p par
  have z := sdData_toNat 0#64
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [read64_writeMap8_disjoint _ _ _ _ (by omega), read64_writeMap8_disjoint _ _ _ _ (by omega),
      read64_writeMap8, z]; rfl
  · rw [read64_writeMap8_disjoint _ _ _ _ (by omega), read64_writeMap8, z]; rfl
  · rw [read64_writeMap8, z]; rfl
  · rw [read64_writeMap8_disjoint _ _ _ _ (by omega), read64_writeMap8_disjoint _ _ _ _ (by omega),
      read64_writeMap8_disjoint _ _ _ _ (by omega), read64_writeMap8, sdData_toNat]

/-- The arena lies in RAM above the HTIF window. -/
structure ArenaGeom (HL : DlLayout) : Prop where
  lo : 0x80000000 ≤ HL.lo
  hi : HL.hi ≤ 0x100000000
  win : tohostAddr + 16 ≤ HL.lo

theorem fresh_geom {HL : DlLayout} {H : List (Nat × Nat)} {b p : BitVec 64} (ha : ArenaGeom HL)
    (hf : FreshBlock HL H p.toNat 32) (halign : p.toNat % 16 = 0)
    (hdisj : p.toNat + 32 ≤ b.toNat ∨ b.toNat + 16 ≤ p.toNat) : EnvNewFreshGeom b p := by
  obtain ⟨h0, hlo, hhi, _⟩ := hf
  refine ⟨fun h => h0 (by rw [h]; rfl), by have := ha.lo; omega, by have := ha.hi; omega,
    by have := ha.win; omega, by omega, hdisj⟩

theorem esp_ge16 {esp r : BitVec 64} (hg : EnvNewCallerGeom (esp - 16#64) r) : 16 ≤ esp.toNat := by
  have h1 := hg.lo
  have h2 := hg.hi
  rw [BitVec.toNat_sub] at h1 h2
  have := esp.isLt
  simp at h1 h2
  omega

/-! ## The Iris specification -/

section Spec

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The fresh `Env` block, owned, holding the initialized image. -/
def envBlock (p par : BitVec 64) : IProp GF :=
  iprop(∃ m, ⌜EnvImage m p par⌝ ∗ sepL (List.range' p.toNat 32) (fun a => a ↦ₘ (m[a]?).getD 0))

theorem code_jal : instrAt (GF := GF) codeBase envNewCode ⊢ instrAt 0x80002a10 jalCode := by
  rw [show envNewCode = envNewCode.take 20 ++ (jalCode ++ envNewCode.drop 24) from rfl,
    show (0x80002a10 : Nat) = codeBase + (envNewCode.take 20).length from rfl]
  iintro H
  ihave ⟨-, H⟩ := (instrAt_append _ _ _).1 $$ H
  ihave ⟨H, -⟩ := (instrAt_append _ _ _).1 $$ H
  iexact H

theorem codeFoot_live {live : Nat → Prop}
    (hlive : ∀ a, codeBase ≤ a → a < codeBase + 96 → live a) :
    ∀ p ∈ codeFoot codeBase envNewCode, live p.1 := fun p hp => by
  have := codeFoot_bounds hp
  exact hlive _ this.1 (by simpa [envNewCode] using this.2)

/-- **`env_new(par)` in continuation style.** Entered at `0x800029fc` with the
return address `r`, the parent `par`, the stack pointer `esp`, 16 bytes of
stack below `esp`, malloc's scratch below those, and the allocator's heap:
the success continuation receives a fresh 32-byte block `p` holding the
initialized `Env`, the heap with `p` live, and every register and byte the
caller handed over back at its entry value (the stack bytes at some value).
`malloc`'s NULL return is handed to the caller's `Knull` at the `beqz`
(VSA's proof assumes arena non-exhaustion there instead). Whatever else the
caller owns is framed by the continuation. -/
theorem envNew_spec {Φ : Nat × String → IProp GF} (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live))
    (hlive : ∀ a, codeBase ≤ a → a < codeBase + 96 → live a)
    {HL : DlLayout} {SpOK : BitVec 64 → Prop} {freeEntry gpv : BitVec 64} {clob savedRegs : List Nat}
    {headroom : Nat} {text : List (Nat × BitVec 8)}
    (impl : DlMallocImpl (vsaModel live) HL SpOK mallocEntry freeEntry gpv clob savedRegs headroom text)
    (harena : ArenaGeom HL) (H : List (Nat × Nat)) (esp r par s0v : BitVec 64)
    (rest : List (Nat × BitVec 64)) (hsaved : 8 :: rest.map Prod.fst = savedRegs)
    (hg : EnvNewCallerGeom (esp - 16#64) r) (hsp : SpOK (esp - 16#64)) :
    instrAt codeBase envNewCode ∗ textOwn text ∗ PC ↦ᵣ 0x800029fc#64 ∗ (1 : Nat) ↦ᵣ r ∗
      (10 : Nat) ↦ᵣ par ∗ (2 : Nat) ↦ᵣ esp ∗ (8 : Nat) ↦ᵣ s0v ∗ savedOwn rest ∗ gp ↦ᵣ□ gpv ∗
      clobbered clob ∗ sepL (List.range' (esp - 16#64).toNat 16) byteAny ∗
      stackScratch (esp - 16#64) headroom ∗ isHeap HL H ∗
      (∀ p : BitVec 64, ⌜FreshBlock HL H p.toNat 32 ∧ p.toNat % 16 = 0⌝ -∗ PC ↦ᵣ r -∗
        (1 : Nat) ↦ᵣ r -∗ (10 : Nat) ↦ᵣ p -∗ (2 : Nat) ↦ᵣ esp -∗ (8 : Nat) ↦ᵣ s0v -∗
        savedOwn rest -∗ clobbered clob -∗ sepL (List.range' (esp - 16#64).toNat 16) byteAny -∗
        stackScratch (esp - 16#64) headroom -∗ isHeap HL ((p.toNat, 32) :: H) -∗
        envBlock p par -∗ Wp.W Φ) ∗
      (PC ↦ᵣ link -∗ (1 : Nat) ↦ᵣ link -∗ (10 : Nat) ↦ᵣ 0#64 -∗ (2 : Nat) ↦ᵣ (esp - 16#64) -∗
        (8 : Nat) ↦ᵣ par -∗ savedOwn rest -∗ clobbered clob -∗
        sepL (List.range' (esp - 16#64).toNat 16) byteAny -∗
        stackScratch (esp - 16#64) headroom -∗ isHeap HL H -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  have h16 := esp_ge16 hg
  have hb := sp_sub16_toNat esp h16
  have hcodeLive := codeFoot_live hlive
  iintro ⟨#Hcode, #Htext, Hpc, Hra, Ha0, Hsp, Hs0, Hsv, #Hgp, Hclob, Hstk, Hscr, Hheap, Kok,
    Knull⟩
  ihave ⟨%Wstk, %hWstk, Hstk⟩ := sepL_byteAny_exists _ $$ Hstk
  have hWmem : ∀ a, (∃ q ∈ Wstk, q.1 = a) ↔ a ∈ List.range' (esp - 16#64).toNat 16 := by
    intro a; rw [← hWstk]; simp
  -- the prefix segment
  iapply wp_segW live Wp envNewPrefixSeg (prefixL esp s0v par r) [] 0x800029fc#64
    (codeFoot codeBase envNewCode) Wstk 4 (by decide)
    (by change ChainOK _ [2, 8, 10, 1] _; decide) (by change KeysOK [2, 8, 10, 1]; decide)
    (by change ∀ k ∈ wrChain envNewPrefixSeg, k ∈ [2, 8, 10, 1]; decide)
    (fun a ha => by
      rw [prefix_log_raw, sp_sub16, off0_addr, off8_addr _ (by have := hg.hi; omega)]
      have : ¬ a ∈ List.range' (esp - 16#64).toNat 16 := fun h => by
        obtain ⟨q, hq, e⟩ := (hWmem a).2 h
        exact ha q hq e
      rw [List.mem_range'] at this
      simp only [OutL]
      refine ⟨?_, ?_, trivial⟩ <;>
      · apply Classical.byContradiction; intro hc
        exact this ⟨a - (esp - 16#64).toNat, by omega, by omega⟩)
    (fun c hok ⟨_, hMR, _, _⟩ =>
      prefix_facts (loaded_of_code (code_present hok _ hMR hcodeLive)) hg)
  have hpc := prefix_pc esp s0v par r
  obtain ⟨f2, f8, f10, f1⟩ := prefix_fin' esp s0v par r
  simp only [prefixL] at hpc
  simp only [prefixL, sepL_cons, sepL_nil, hpc, f2, f8, f10, f1]
  rw [← instrAt_eq]
  iframe Hpc Hsp Hs0 Ha0 Hra Hstk Hcode
  iintro Hpc ⟨Hsp, Hs0, Ha0, Hra, -⟩ Hstk -
  -- the call: the stack frame is the owned set `wp_call_malloc_owns` keeps
  have hjal := jal_exec live fun q hq => by
    have := codeFoot_bounds hq
    exact hlive _ (by simp [codeBase] at *; omega) (by simp [jalCode, codeBase] at *; omega)
  ihave #Hjal := code_jal $$ Hcode
  have hnd : (Wstk.map Prod.fst).Nodup := by rw [hWstk]; exact List.nodup_range' _ (by omega)
  let stkB : Nat → BitVec 8 := fun a => ((stackImg Wstk esp s0v par r)[a]?).getD 0
  ihave HC := sepL_to_ownSet _ hnd (fun a => a ↦ₘ stkB a) $$ [Hstk]
  · rw [sepL_map]; iexact Hstk
  iapply wp_call_malloc_owns Wp impl hjal H r (32#64) (esp - 16#64) ((8, par) :: rest)
    (by simp [hsaved]) hsp (by decide) (fun a => a ∈ Wstk.map Prod.fst) stkB
  unfold VsaIris.ra VsaIris.a0 VsaIris.sp savedOwn
  simp only [sepL_cons]
  iframe Hjal Htext Hpc Hra Hsp Hgp Hclob Hs0 Hsv Hscr Hheap HC
  isplitl [Ha0]
  · iexact Ha0
  iintro %p Hpc Hra Ha0 Hsp Hclob ⟨Hs0, Hsv⟩ Hscr Hpost HC %hoff
  ihave Hstk := ownSet_to_sepL _ hnd _ $$ HC
  unfold mallocPost
  icases Hpost with (⟨%hp0, Hheap⟩ | ⟨%⟨hfresh, halign⟩, Hheap, Hblk⟩)
  · -- malloc returned NULL: the caller's continuation at the `beqz`
    subst hp0
    iapply Knull $$ Hpc Hra Ha0 Hsp Hs0 Hsv Hclob [Hstk] Hscr Hheap
    rw [← hWstk]
    iapply sepL_mono _ _ _ (fun a => by iintro H; iexists stkB a; iexact H) $$ Hstk
  -- malloc returned a fresh block
  have hfresh : FreshBlock HL H p.toNat 32 := hfresh
  have hdisj : p.toNat + 32 ≤ (esp - 16#64).toNat ∨ (esp - 16#64).toNat + 16 ≤ p.toNat := by
    apply Classical.byContradiction; intro hc
    have hp : p ≠ 0 := fun h => hfresh.nonzero (by rw [h]; rfl)
    let a := max (esp - 16#64).toNat p.toNat
    have ha : a ∈ Wstk.map Prod.fst := by
      rw [hWstk, List.mem_range']
      exact ⟨a - (esp - 16#64).toNat, by simp only [a, Nat.max_def]; split <;> omega, by omega⟩
    exact (hoff hp a ha).1 (by unfold InExt; simp only [a, Nat.max_def]; split <;> simp <;> omega)
  have hf := fresh_geom harena hfresh halign hdisj
  obtain ⟨hra, hs0⟩ := stackImg_reads Wstk (s0v := s0v) (par := par) hg
  ihave Hblk := blockOwn_range _ _ $$ Hblk
  ihave ⟨%Wblk, %hWblk, Hblk⟩ := sepL_byteAny_exists _ $$ Hblk
  have hWblk : Wblk.map Prod.fst = List.range' p.toNat 32 := hWblk
  -- the success suffix
  iapply wp_segW live Wp envNewSuccessSeg (succL (esp - 16#64) p par)
    (succLds (stackImg Wstk esp s0v par r) (esp - 16#64)) link
    (codeFoot codeBase envNewCode ++ (Wstk.map Prod.fst).map fun a => (a, DFrac.own 1, stkB a))
    Wblk 8 (by decide)
    (by change ChainOK _ [2, 10, 8, 1] _; decide) (by change KeysOK [2, 10, 8, 1]; decide)
    (by change ∀ k ∈ wrChain envNewSuccessSeg, k ∈ [2, 10, 8, 1]; decide)
    (fun a ha => by
      rw [succ_log _ hf.hi]
      have : ¬ a ∈ List.range' p.toNat 32 := fun h => by
        rw [← hWblk] at h
        obtain ⟨q, hq, e⟩ := List.mem_map.mp h
        exact ha q hq e
      rw [List.mem_range'] at this
      simp only [envNewSuccessLog, OutL]
      refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;>
      · apply Classical.byContradiction; intro hc
        exact this ⟨a - p.toNat, by omega, by omega⟩)
    (fun c hok ⟨_, hMR, _, _⟩ => by
      refine succ_facts (loaded_of_code (code_present hok _
        (fun q hq => hMR q (List.mem_append_left _ hq)) hcodeLive)) hg hf hra fun k hk => ?_
      have hk' : (esp - 16#64).toNat + k ∈ Wstk.map Prod.fst := by
        rw [hWstk, List.mem_range']; exact ⟨k, hk, by omega⟩
      exact hMR _ (List.mem_append_right _ (List.mem_map_of_mem
        (f := fun a => (a, DFrac.own 1, stkB a)) hk')))
  simp only [newByte]
  rw [succ_log _ hf.hi, succ_pc' _ _ _ _ _ hra hg.ret_align]
  obtain ⟨g2, g10, g8, g1⟩ := succ_fin' _ _ p par r s0v hra hs0
  simp only [succL, sepL_cons, sepL_nil, g2, g10, g8, g1, sp_restore]
  iframe Hpc Hsp Ha0 Hs0 Hra
  isplitl [Hblk]
  · iexact Hblk
  isplitl [Hstk]
  · iapply (sepL_append _ _ _).2
    isplitr
    · rw [← instrAt_eq]; iexact Hcode
    rw [sepL_map (fun a => (a, DFrac.own 1, stkB a))]; iexact Hstk
  iintro Hpc ⟨Hsp, Ha0, Hs0, Hra, -⟩ Hblk HMR
  ihave ⟨-, Hstk⟩ := (sepL_append _ _ _).1 $$ HMR
  ihave Hstk := sepL_map_forget' _ stkB $$ Hstk
  iapply Kok $$ %p %⟨hfresh, halign⟩ Hpc Hra Ha0 Hsp Hs0 Hsv Hclob [Hstk] Hscr [Hheap] [Hblk]
  · rw [← hWstk]; iexact Hstk
  · rw [show ((p.toNat, 32) :: H) = ((p.toNat, (32#64).toNat) :: H) from rfl]
    iexact Hheap
  unfold envBlock
  iexists writeLog (wbase Wblk) (envNewSuccessLog p par)
  isplitr
  · ipureintro; exact envImage_of_log _ p par
  rw [← hWblk, sepL_map]
  iexact Hblk

/-- The fixed binary's arena lies in RAM above the HTIF window. -/
theorem arenaGeom_vsa : ArenaGeom VsaHeap.vsaLayout :=
  ⟨by decide, by decide, by decide⟩

/-- **`env_new` against the binary's own allocator.** `envNew_spec` at
`vsaLayout` with `vsaDlMallocImpl`: the only allocator assumptions left are
the sibling's named instruction-level runs of `_malloc_r`/`_free_r`
(`MallocLocalRun`, `FreeLocalRun`). The callee-saved registers `malloc`
spills (`vsaSaved = s0 s1 s2 s3`) are handed over with `s0` at its spilled
value and `s1-s3` from the caller. -/
theorem envNew_spec_vsa {Φ : Nat × String → IProp GF} (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live))
    (hlive : ∀ a, codeBase ≤ a → a < codeBase + 96 → live a)
    {SpOK : BitVec 64 → Prop} {gpv : BitVec 64} {headroom : Nat} {text : List (Nat × BitVec 8)}
    (hm : MallocLocalRun (vsaModel live) VsaHeap.vsaLayout SpOK VsaHeap.mallocEntryBV gpv
      VsaHeap.vsaClob VsaHeap.vsaSaved headroom text)
    (hf : FreeLocalRun (vsaModel live) VsaHeap.vsaLayout SpOK VsaHeap.freeEntryBV gpv
      VsaHeap.vsaClob VsaHeap.vsaSaved headroom text)
    (H : List (Nat × Nat)) (esp r par s0v s1 s2 s3 : BitVec 64)
    (hg : EnvNewCallerGeom (esp - 16#64) r) (hsp : SpOK (esp - 16#64)) :
    instrAt codeBase envNewCode ∗ textOwn text ∗ PC ↦ᵣ 0x800029fc#64 ∗ (1 : Nat) ↦ᵣ r ∗
      (10 : Nat) ↦ᵣ par ∗ (2 : Nat) ↦ᵣ esp ∗ (8 : Nat) ↦ᵣ s0v ∗
      savedOwn [(9, s1), (18, s2), (19, s3)] ∗ gp ↦ᵣ□ gpv ∗
      clobbered VsaHeap.vsaClob ∗ sepL (List.range' (esp - 16#64).toNat 16) byteAny ∗
      stackScratch (esp - 16#64) headroom ∗ isHeap VsaHeap.vsaLayout H ∗
      (∀ p : BitVec 64, ⌜FreshBlock VsaHeap.vsaLayout H p.toNat 32 ∧ p.toNat % 16 = 0⌝ -∗
        PC ↦ᵣ r -∗ (1 : Nat) ↦ᵣ r -∗ (10 : Nat) ↦ᵣ p -∗ (2 : Nat) ↦ᵣ esp -∗
        (8 : Nat) ↦ᵣ s0v -∗ savedOwn [(9, s1), (18, s2), (19, s3)] -∗
        clobbered VsaHeap.vsaClob -∗ sepL (List.range' (esp - 16#64).toNat 16) byteAny -∗
        stackScratch (esp - 16#64) headroom -∗ isHeap VsaHeap.vsaLayout ((p.toNat, 32) :: H) -∗
        envBlock p par -∗ Wp.W Φ) ∗
      (PC ↦ᵣ link -∗ (1 : Nat) ↦ᵣ link -∗ (10 : Nat) ↦ᵣ 0#64 -∗ (2 : Nat) ↦ᵣ (esp - 16#64) -∗
        (8 : Nat) ↦ᵣ par -∗ savedOwn [(9, s1), (18, s2), (19, s3)] -∗
        clobbered VsaHeap.vsaClob -∗ sepL (List.range' (esp - 16#64).toNat 16) byteAny -∗
        stackScratch (esp - 16#64) headroom -∗ isHeap VsaHeap.vsaLayout H -∗
        Wp.W Φ)
    ⊢ Wp.W Φ :=
  envNew_spec live Wp hlive (VsaHeap.vsaDlMallocImpl live gpv headroom text hm hf) arenaGeom_vsa
    H esp r par s0v [(9, s1), (18, s2), (19, s3)] rfl hg hsp

end Spec

end VsaIris.Inst.EnvNew
