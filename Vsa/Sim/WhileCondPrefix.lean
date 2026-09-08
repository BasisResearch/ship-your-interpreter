import Vsa.Sim.WhileBodyDispatch

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (Config Steps)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

#derive_case execWhileCondPrefixSeg chain
  [(0x8000403c#64, 0x00843603#32),  -- discipline: allow(R10-exec-evalchild-arm) reused as `whileCondArm.seg` (rows/EvalChildArmWhile)
   (0x80004040#64, 0x00098693#32),
   (0x80004044#64, 0x05010513#32),
   (0x80004048#64, 0x00048593#32)]

def execWhileCondPrefixL (esp aStmt aInterp aRet aEnv : BitVec 64) : GRegs :=
  [(2, esp), (8, aStmt), (9, aInterp), (18, aRet), (19, aEnv)]

def execWhileCondPrefixLds (m : Mem) (aStmt : BitVec 64) : List (List (BitVec 8)) :=
  [execWhileWordLds m (aStmt.toNat + 8)]

theorem execWhileCondPrefix_facts
    {m : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet aStmt : BitVec 64} {cnd : Expr} {body : Stmt}
    (hg : ExecGround m SL A sp aRet aStmt.toNat (.whileStmt cnd body))
    (hcode : Code.Exec_stmtLoaded m) (esp aInterp aEnv : BitVec 64) :
    ChainFacts m m (execWhileCondPrefixL esp aStmt aInterp aRet aEnv)
      (execWhileCondPrefixLds m aStmt) execWhileCondPrefixSeg := by
  obtain ⟨lo, hi, hr⟩ := hg.ast.region
  have hn := stmtIn_node hr.nodes
  have haddr : (aStmt + sign_extend (m := 64) (0x008#12)).toNat =
      aStmt.toNat + 8 := by
    have hs : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by decide
    rw [hs, BitVec.toNat_add]
    have h8 : (8#64 : BitVec 64).toNat = 8 := by decide
    rw [h8, Nat.mod_eq_of_lt]
    have := hn.hi_ge
    have := hr.hi_ram
    omega
  unfold execWhileCondPrefixSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  change ((0x80000000 ≤ (aStmt + sign_extend (m := 64) (0x008#12)).toNat ∧
    (aStmt + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000 ∧
    ((aStmt + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr ∨
      tohostAddr + 8 ≤ (aStmt + sign_extend (m := 64) (0x008#12)).toNat)) ∧
    LPins8 m (aStmt + sign_extend (m := 64) (0x008#12)).toNat
      (execWhileWordLds m (aStmt.toNat + 8)))
  rw [haddr]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · have := hr.lo_ram; have := hn.lo_le; omega
  · have := hr.hi_ram; have := hn.hi_ge; omega
  · right; have := hr.win; have := hn.lo_le; omega
  · simp only [execWhileWordLds, LPins8, List.getD_cons_zero, List.getD_cons_succ]
    trivial

/-- Exact state after the condition prefix and its call instruction. -/
structure ExecWhileCondCallState
    (g : (R : Register) → Option (RegisterType R))
    (esp aInterp aCond aEnv : BitVec 64) (m : Mem) (out : Array String)
    (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some 0x80003164#64
  ra : cfg.σ.regs.get? Register.x1 = some 0x80004050#64
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  spReg : cfg.σ.regs.get? Register.x2 = some esp
  a0 : cfg.σ.regs.get? Register.x10 = some (esp + 80#64)
  a1 : cfg.σ.regs.get? Register.x11 = some aInterp
  a2 : cfg.σ.regs.get? Register.x12 = some aCond
  a3 : cfg.σ.regs.get? Register.x13 = some aEnv
  mem : cfg.σ.mem = m
  out : cfg.σ.sailOutput = out
  frame : ∀ R, AbiPreserved R = true → cfg.σ.regs.get? R = g R

theorem execWhileCondPrefix_run
    {m : Mem} {SL : StackLayout} {A : Arena}
    {sp aRet aStmt aInterp aEnv aCond esp : BitVec 64}
    {cnd : Expr} {body : Stmt} {cfg : Config}
    (hg : ExecGround m SL A sp aRet aStmt.toNat (.whileStmt cnd body))
    (hcode : Code.Exec_stmtLoaded m)
    (hread : read64 m (aStmt.toNat + 8) = some aCond.toNat)
    (hgood : GoodState cfg.σ) (htick : cfg.tick < 2)
    (hpc : cfg.σ.regs.get? Register.PC = some 0x8000403c#64)
    (hmi : ∃ w, cfg.σ.regs.get? Register.minstret = some w)
    (hmem : cfg.σ.mem = m)
    (hregs : GHolds cfg.σ (execWhileCondPrefixL esp aStmt aInterp aRet aEnv)) :
    ∃ cfg', Steps cfg cfg' ∧
      ExecWhileCondCallState (fun R => cfg.σ.regs.get? R)
        esp aInterp aCond aEnv m cfg.σ.sailOutput cfg' := by
  let regs := execWhileCondPrefixL esp aStmt aInterp aRet aEnv
  let lds := execWhileCondPrefixLds m aStmt
  obtain ⟨vm, hvm⟩ := hmi
  have hfacts := execWhileCondPrefix_facts hg hcode esp aInterp aEnv
  obtain ⟨σ', i', hs, hi, hG, hPC, hRA, hMI, hRegs, hMem, hOut, hFrame⟩ :=
    bridgeOfSegOut execWhileCondPrefixSeg regs lds cfg.σ cfg.tick cfg.steps
      0x8000403c#64 0x80003164#64 0x80004050#64 vm m
      hgood hpc hvm hmem hregs (by change KeysOK [2, 8, 9, 18, 19]; decide)
      (hmem.symm ▸ hfacts) htick
      (by change ChainOK 0x8000403c#64 [2, 8, 9, 18, 19] execWhileCondPrefixSeg; decide)
      (by change WrChainAvoidAbi execWhileCondPrefixSeg; decide)
      (by change KeysOK [11, 10, 13, 12, 2, 8, 9, 18, 19]; decide)
      (by change ∀ n ∈ [11, 10, 13, 12, 2, 8, 9, 18, 19], n ≠ 1; decide)
      (by
        intro σ i u hG hi hpc hmi hm _
        obtain ⟨vm, hvm⟩ := hmi
        have hp : σ.regs.get? Register.PC = some 0x8000404c#64 := by
          simpa only [execWhileCondPrefixSeg] using hpc
        have hc : Code.Exec_stmtLoaded σ.mem := by
          simpa only [execWhileCondPrefixSeg, writeLog] using hm ▸ hcode
        obtain ⟨σ2, i2, hs2, hi2, hG2, hm2, ho2⟩ :=
          site_8000404c_es σ i u 0x8000404c#64 vm hG hp hvm hc rfl hi
        exact jalStepO_of_obs hs2 hi2 hG2 hm2 ho2 (by decide))
  have hload : bytesVal MKind.ld (execWhileWordLds m (aStmt.toNat + 8)) = aCond := by
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7,
      hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hrec⟩ :=
      read64_bytes m (aStmt.toNat + 8) aCond.toNat hread
    simp only [execWhileWordLds, bytesVal, List.getD_cons_zero,
      List.getD_cons_succ, hb0, hb1, hb2, hb3, hb4, hb5,
      hb6, hb7, Option.getD_some]
    rw [sext_full]
    apply BitVec.eq_of_toNat_eq
    rw [word8_toNat_recon]
    exact hrec
  change GHolds σ'
    [(11, aInterp + sign_extend (m := 64) (0#12)),
     (10, esp + sign_extend (m := 64) (0x050#12)),
     (13, aEnv + sign_extend (m := 64) (0#12)),
     (12, bytesVal MKind.ld (execWhileWordLds m (aStmt.toNat + 8))),
     (2, esp), (8, aStmt), (9, aInterp), (18, aRet), (19, aEnv)] at hRegs
  have hzero : (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 := by decide
  have h80 : (sign_extend (m := 64) (0x050#12) : BitVec 64) = 80#64 := by decide
  simp only [hzero, h80, BitVec.add_zero, hload] at hRegs
  refine ⟨⟨σ', i', cfg.steps + evalBlocksFuel execWhileCondPrefixSeg + 1⟩, hs, ?_⟩
  exact
    { good := hG
      tick := hi
      pc := hPC
      ra := hRA
      minstret := hMI
      spReg := gholds_lookup (n := 2) _ hRegs (by rfl)
      a0 := gholds_lookup (n := 10) _ hRegs (by rfl)
      a1 := gholds_lookup (n := 11) _ hRegs (by rfl)
      a2 := gholds_lookup (n := 12) _ hRegs (by rfl)
      a3 := gholds_lookup (n := 13) _ hRegs (by rfl)
      mem := by simpa only [execWhileCondPrefixSeg, writeLog] using hMem
      out := hOut
      frame := hFrame }

#print axioms execWhileCondPrefix_run

end Vsa.Sim
