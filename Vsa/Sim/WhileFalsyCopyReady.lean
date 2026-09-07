import Vsa.Sim.WhileFalsyBranch
import Vsa.Sim.WhileGeomSuppliers

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (Config)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

structure ExecWhileFalsyExitHead
    (gCond : (R : Register) → Option (RegisterType R))
    (mHead : Mem) (out : Array String) (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some 0x80004090#64
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  mem : cfg.σ.mem = mHead
  out : cfg.σ.sailOutput = out
  frame : ∀ R, Vsa.Alloc.AbiPreserved R = true →
    cfg.σ.regs.get? R = gCond R

theorem execWhileFalsyBranch_writeLog_eq (m : Mem)
    (sp s0 s1 s2 s3 : BitVec 64) :
    writeLog m (evalBlocks execWhileFalsyBranchSeg
      (SegEvalState.init
        (execWhileRouteL 0#64 sp 0x80004070#64 s0 s1 s2 s3) [])).log = m := by
  rfl

theorem execWhileFalsy_of_copyReady
    (gCond : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Addr → Nat) (v : Value)
    (esp aStmt aInterp aRet aEnv : BitVec 64)
    (mCopy : Mem) (out : Array String) (cfgCopy : Config)
    (hReady : ExecWhileCondCopyReady gCond N φc v esp aStmt aInterp
      aRet aEnv mCopy out cfgCopy)
    (hfalsy : v.truthy = false) :
    ∃ cfgHead : Config,
      Vsa.Machine.Steps cfgCopy cfgHead ∧
      ExecWhileFalsyExitHead gCond mCopy out cfgHead := by
  have hPre : ExecWhileFalsyHeaderPre
      (fun R => cfgCopy.σ.regs.get? R) N φc v
      (esp + sign_extend (m := 64) (0x010#12)) esp aStmt aInterp aRet aEnv
      mCopy out cfgCopy := by
    refine ⟨?_, hReady.code, hfalsy, hReady.sp, hReady.s0, hReady.s1,
      hReady.s2, hReady.s3⟩
    refine ⟨hReady.good, ?_, hReady.mem, hReady.pc, hReady.a0, hReady.ra,
      hReady.minstret, hReady.tick, hReady.header, hReady.region, ?_,
      hReady.out, ?_⟩
    · exact hReady.mem.symm ▸ hReady.truthy_loaded
    · decide
    · intro R _hR
      rfl
  obtain ⟨cfgHead, hsHead, hroute, hframeHead, htickHead, hmiHead⟩ :=
    execWhileFalsyHeaderToExitHead_framed
      (fun R => cfgCopy.σ.regs.get? R) N φc v
      (esp + sign_extend (m := 64) (0x010#12)) esp aStmt aInterp aRet aEnv
      mCopy out cfgCopy hPre
  rcases hroute with ⟨hgoodHead, hmemHead, houtHead, hpcHead, _hregsHead⟩
  have hmemHead' : cfgHead.σ.mem = mCopy := by
    simpa only [execWhileFalsyBranch_writeLog_eq] using hmemHead
  refine ⟨cfgHead, hsHead, ?_⟩
  exact
    { good := hgoodHead
      tick := htickHead
      pc := hpcHead
      minstret := hmiHead
      mem := hmemHead'
      out := houtHead
      frame := fun R hR => (hframeHead R hR).trans (hReady.frame R hR) }


#print axioms execWhileFalsy_of_copyReady

end Vsa.Sim
