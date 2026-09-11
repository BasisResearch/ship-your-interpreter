import Vsa.Sim.ClosureReturnNull

namespace Vsa.Sim.ClosureReturn

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Caller geometry and saved reads at the actual body exit. -/
structure Pre (sp sret interp saved5 saved3 saved7 : BitVec 64) (depth : Nat)
    (returns : Bool) (before : Config) : Prop where
  depthEntry : ClosureReturnDepth.Pre interp sret depth returns before
  spReg : before.σ.regs.get? Register.x2 = some sp
  reads : ClosureCallPrefix.BodyReturnReads before.σ.mem sp interp saved5 saved3 saved7 depth
  joinGeometry : ClosureReturnJoin.Geometry sp sret
  interpAbove : sp.toNat + 1056 ≤ interp.toNat
  retOffSpills : sret.toNat + 24 ≤ sp.toNat + 1016 ∨ sp.toNat + 1056 ≤ sret.toNat
  nullRegion : NullRegion sret
  nullCode : Code.Value_nullLoaded before.σ.mem

/-- Both actual return routes reach the epilogue with restored caller registers. -/
structure Post (N : NativeAddrs) (phiC : Addr → Nat)
    (sp sret interp saved5 saved3 saved7 : BitVec 64) (depth : Nat) (returns : Bool)
    (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some 0x800033ec#64
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  regs : GHolds after.σ [(2, sp), (9, sret), (19, saved3), (21, saved5), (23, saved7)]
  copied : returns = true → ∀ j, j < 24 →
    after.σ.mem[sret.toNat + j]? = some ((before.σ.mem[sp.toNat + 144 + j]?).getD 0)
  normalValue : returns = false → ValueRepr after.σ.mem N phiC sret.toNat .null
  restored : ∀ k, ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
    after.σ.mem[k]? = (writeLog before.σ.mem [(interp.toNat + 8, 4, BitVec.ofNat 64 depth)])[k]?
  outside : ∀ k, ¬ (interp.toNat + 8 ≤ k ∧ k < interp.toNat + 12) →
    ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) → before.σ.mem[k]? = after.σ.mem[k]?
  presence : MemExtends before.σ.mem after.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, ClosureReturnJoin.keep R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Compose the checked depth route, optional null helper, and caller restoration. -/
theorem run {sp sret interp saved5 saved3 saved7 : BitVec 64} {depth : Nat} {returns : Bool}
    {before : Config} (h : Pre sp sret interp saved5 saved3 saved7 depth returns before)
    (N : NativeAddrs) (phiC : Addr → Nat) :
    ∃ after, Steps before after ∧ Post N phiC sp sret interp saved5 saved3 saved7 depth returns before after := by
  obtain ⟨middle, depthSteps, depthPost⟩ := ClosureReturnDepth.run h.depthEntry
  have kept (R : Register) (keep : ClosureReturnJoin.keep R = true) : AbiPreserved R = true := by
    simp only [ClosureReturnJoin.keep, Bool.and_eq_true] at keep
    exact keep.1.1.1
  have depthPresence : MemExtends before.σ.mem middle.σ.mem := by
    rw [depthPost.memory]; exact memExtends_writeLog _ _
  have code : Code.Eval_exprLoaded middle.σ.mem := by
    apply loaded_eval_expr_agreeP before.σ.mem middle.σ.mem _ h.depthEntry.code
    intro k hk
    apply depthPost.outside k
    have := h.depthEntry.geometry.htif
    have : 0x80003fe0 ≤ tohostAddr := by decide
    omega
  have savedRead (off : Nat) (lo : 1016 ≤ off) (hi : off + 8 ≤ 1056) :
      read64 before.σ.mem (sp.toNat + off) = read64 middle.σ.mem (sp.toNat + off) := by
    apply read64_agreeP (P := fun k => ¬ (interp.toNat + 8 ≤ k ∧ k < interp.toNat + 12)) depthPost.outside
    intro k hk
    have := h.interpAbove; omega
  have spReg := (depthPost.frame .x2 (by decide)).trans h.spReg
  have sretReg : middle.σ.regs.get? Register.x9 = some sret :=
    gholds_lookup _ depthPost.regs (show lookupG 9 _ = some sret from rfl)
  cases returns
  · have loaded : Code.Value_nullLoaded middle.σ.mem := by
      apply loaded_null_agreeP before.σ.mem middle.σ.mem _ h.nullCode
      intro k hk
      apply depthPost.outside k
      have := h.depthEntry.geometry.htif
      have : 0x800027fc ≤ tohostAddr := by decide
      omega
    obtain ⟨initialized, nullSteps, nullPost⟩ := closureReturnNull_run middle sret N phiC
      depthPost.good depthPost.tick depthPost.pc
      (gholds_lookup _ depthPost.regs (show lookupG 10 _ = some sret from rfl))
      depthPost.minstret code loaded h.nullRegion
    have nullFrame (R : Register) (abi : AbiPreserved R = true) :
        initialized.σ.regs.get? R = middle.σ.regs.get? R :=
      nullPost.frame R (notWrittenV_of_abiPreserved R abi) (by simp [wrChain])
        (abiPreserved_ne abi (by decide))
    have code' : Code.Eval_exprLoaded initialized.σ.mem := by
      apply loaded_eval_expr_agreeP middle.σ.mem initialized.σ.mem _ code
      intro k hk
      apply nullPost.outside k
      have := h.joinGeometry.retHtif
      have : 0x80003fe0 ≤ tohostAddr := by decide
      omega
    have nullRead (off : Nat) (lo : 1016 ≤ off) (hi : off + 8 ≤ 1056) :
        read64 middle.σ.mem (sp.toNat + off) = read64 initialized.σ.mem (sp.toNat + off) := by
      apply read64_agreeP (P := fun k => ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24)) nullPost.outside
      intro k hk
      have := h.retOffSpills; omega
    have input : ClosureReturnJoin.Pre sp sret saved5 saved3 saved7 false initialized :=
      { good := nullPost.good, tick := nullPost.tick, pc := nullPost.pc, minstret := nullPost.minstret
        regs := ⟨(nullFrame .x2 (by decide)).trans spReg, (nullFrame .x9 (by decide)).trans sretReg, trivial⟩
        geometry := h.joinGeometry, code := code'
        saved5Read := ((savedRead 1032 (by decide) (by decide)).trans (nullRead 1032 (by decide) (by decide))).symm.trans h.reads.saved5Read
        saved3Read := ((savedRead 1048 (by decide) (by decide)).trans (nullRead 1048 (by decide) (by decide))).symm.trans h.reads.saved3Read
        saved7Read := ((savedRead 1016 (by decide) (by decide)).trans (nullRead 1016 (by decide) (by decide))).symm.trans h.reads.saved7Read }
    obtain ⟨after, joinSteps, joined⟩ := ClosureReturnJoin.run input
    have memory : after.σ.mem = initialized.σ.mem := joined.memory
    exact ⟨after, depthSteps.trans (nullSteps.trans joinSteps),
      { good := joined.good, tick := joined.tick, pc := joined.pc, minstret := joined.minstret
        regs := joined.regs, copied := fun impossible => by cases impossible
        normalValue := fun _ => memory ▸ nullPost.value
        restored := fun k hr => (joined.outside k hr).symm.trans
          ((nullPost.outside k hr).symm.trans (congrArg (fun m => m[k]?) depthPost.memory))
        outside := fun k hd hr => (depthPost.outside k hd).trans
          ((nullPost.outside k hr).trans (joined.outside k hr))
        presence := memory.symm ▸ depthPresence.trans nullPost.presence
        output := joined.output.trans (nullPost.output.trans depthPost.output)
        frame := fun R hr => (joined.frame R hr).trans
          ((nullFrame R (kept R hr)).trans (depthPost.frame R (kept R hr))) }⟩
  · have input : ClosureReturnJoin.Pre sp sret saved5 saved3 saved7 true middle :=
      { good := depthPost.good, tick := depthPost.tick, pc := depthPost.pc, minstret := depthPost.minstret
        regs := ⟨spReg, sretReg, trivial⟩, geometry := h.joinGeometry, code := code
        saved5Read := (savedRead 1032 (by decide) (by decide)).symm.trans h.reads.saved5Read
        saved3Read := (savedRead 1048 (by decide) (by decide)).symm.trans h.reads.saved3Read
        saved7Read := (savedRead 1016 (by decide) (by decide)).symm.trans h.reads.saved7Read }
    obtain ⟨after, joinSteps, joined⟩ := ClosureReturnJoin.run input
    refine ⟨after, depthSteps.trans joinSteps,
      { good := joined.good, tick := joined.tick, pc := joined.pc, minstret := joined.minstret
        regs := joined.regs, copied := ?_, normalValue := fun impossible => by cases impossible
        restored := fun k hr => (joined.outside k hr).symm.trans (congrArg (fun m => m[k]?) depthPost.memory)
        outside := fun k hd hr => (depthPost.outside k hd).trans (joined.outside k hr)
        presence := depthPresence.trans (by rw [joined.memory]; exact memExtends_writeLog _ _)
        output := joined.output.trans depthPost.output
        frame := fun R hr => (joined.frame R hr).trans (depthPost.frame R (kept R hr)) }⟩
    intro _ j hj
    rw [joined.copied rfl j hj, ← depthPost.outside (sp.toNat + 144 + j) (by
      have := h.interpAbove; omega)]

end Vsa.Sim.ClosureReturn
