import Vsa.Sim.rows.ExecWhileRouteRows

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.Alloc Vsa.Sim.Code

namespace Vsa.Sim

#derive_case execWhileFalsyBranchSeg chain
  []
    terminator ⟨0x80004070#64, 0x02050063#32, 0x63#8, 0x00#8, 0x05#8, 0x02#8,
      .br bop.BEQ true, 10, 0, 0x0020#13, 0#21, 0#12⟩

theorem execWhileFalsyBranch_facts (m : Mem)
    (sp s0 s1 s2 s3 : BitVec 64) (hcode : Exec_stmtLoaded m) :
    ChainFacts m m
      (execWhileRouteL 0#64 sp 0x80004070#64 s0 s1 s2 s3) []
      execWhileFalsyBranchSeg := by
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · show guardB bop.BEQ
      (srcVal 10 (execWhileRouteL 0#64 sp 0x80004070#64 s0 s1 s2 s3))
      (srcVal 0 (execWhileRouteL 0#64 sp 0x80004070#64 s0 s1 s2 s3)) = true
    simp [execWhileRouteL, srcVal, lookupG, guardB]

def ExecWhileFalsyHeaderPre
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (v : Vsa.While.Value)
    (buf sp s0 s1 s2 s3 : BitVec 64) (m0 : Mem) (out0 : Array String)
    (c : Config) : Prop :=
  truthy_header_pre g buf 0x80004070#64 N φc v m0 out0 c ∧
  Exec_stmtLoaded m0 ∧ v.truthy = false ∧
  g Register.x2 = some sp ∧ g Register.x8 = some s0 ∧
  g Register.x9 = some s1 ∧ g Register.x18 = some s2 ∧
  g Register.x19 = some s3

private theorem notWrittenT_of_abiPreserved (R : Register)
    (hR : Vsa.Alloc.AbiPreserved R = true) : NotWrittenT R := by
  cases R <;> simp_all [Vsa.Alloc.AbiPreserved, NotWrittenT]

/-- Framed form of the falsy helper and branch.  This retains the
callee-preserved registers needed by the enclosing while frame. -/
theorem execWhileFalsyHeaderToExitHead_framed
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (v : Vsa.While.Value)
    (buf sp s0 s1 s2 s3 : BitVec 64) (m0 : Mem) (out0 : Array String) :
    Triple
      (ExecWhileFalsyHeaderPre g N φc v buf sp s0 s1 s2 s3 m0 out0)
      (fun c => ExecWhileRoutePost execWhileFalsyBranchSeg 0x80004090#64
          0#64 sp 0x80004070#64 s0 s1 s2 s3 [] m0 out0 c ∧
        (∀ R, Vsa.Alloc.AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        c.tick < 2 ∧
        ∃ w, c.σ.regs.get? Register.minstret = some w) := by
  intro c hpre
  obtain ⟨htruthy, hcode, hv, hgsp, hgs0, hgs1, hgs2, hgs3⟩ := hpre
  obtain ⟨cT, hsT, hG, hpc, ha0, hra, hmi, htick, hmem, hout, hframe⟩ :=
    value_truthy_header_spec g buf 0x80004070#64 N φc v m0 out0 c htruthy
  have hpc' : cT.σ.regs.get? Register.PC = some 0x80004070#64 := by
    rw [hpc]
    apply congrArg some
    apply BitVec.eq_of_toNat_eq
    decide
  have ha0' : cT.σ.regs.get? Register.x10 = some 0#64 := by
    simpa [hv] using ha0
  have hsp' : cT.σ.regs.get? Register.x2 = some sp := by
    rw [hframe Register.x2 (notWrittenT_of_abiPreserved _ (by decide)), hgsp]
  have hs0' : cT.σ.regs.get? Register.x8 = some s0 := by
    rw [hframe Register.x8 (notWrittenT_of_abiPreserved _ (by decide)), hgs0]
  have hs1' : cT.σ.regs.get? Register.x9 = some s1 := by
    rw [hframe Register.x9 (notWrittenT_of_abiPreserved _ (by decide)), hgs1]
  have hs2' : cT.σ.regs.get? Register.x18 = some s2 := by
    rw [hframe Register.x18 (notWrittenT_of_abiPreserved _ (by decide)), hgs2]
  have hs3' : cT.σ.regs.get? Register.x19 = some s3 := by
    rw [hframe Register.x19 (notWrittenT_of_abiPreserved _ (by decide)), hgs3]
  have hL : GHolds cT.σ
      (execWhileRouteL 0#64 sp 0x80004070#64 s0 s1 s2 s3) := by
    simp only [execWhileRouteL, GHolds, gprGet]
    exact ⟨ha0', hsp', hra, hs0', hs1', hs2', hs3', True.intro⟩
  have hfacts := execWhileFalsyBranch_facts m0 sp s0 s1 s2 s3 hcode
  have hfactsT : ChainFacts cT.σ.mem cT.σ.mem
      (execWhileRouteL 0#64 sp 0x80004070#64 s0 s1 s2 s3) []
      execWhileFalsyBranchSeg := by
    simpa only [hmem] using hfacts
  obtain ⟨σB, iB, hsB, hiB, hGB, hmemB, houtB, hpcB, hmiB,
      hregsB, hframeB⟩ :=
    segEval_sound execWhileFalsyBranchSeg cT.σ cT.tick cT.steps
      0x80004070#64 (Classical.choose hmi)
      (execWhileRouteL 0#64 sp 0x80004070#64 s0 s1 s2 s3) []
      hG hpc' (Classical.choose_spec hmi) hL
      (by
        have hk : keysG
            (execWhileRouteL 0#64 sp 0x80004070#64 s0 s1 s2 s3) =
            [10, 2, 1, 8, 9, 18, 19] := rfl
        rw [hk]
        decide)
      hfactsT
      (by
        have hk : keysG
            (execWhileRouteL 0#64 sp 0x80004070#64 s0 s1 s2 s3) =
            [10, 2, 1, 8, 9, 18, 19] := rfl
        rw [hk]
        show ChainOK 0x80004070#64 [10, 2, 1, 8, 9, 18, 19]
          execWhileFalsyBranchSeg
        decide)
      htick
  have hmemB' : σB.mem = writeLog m0
      (evalBlocks execWhileFalsyBranchSeg
        (SegEvalState.init
          (execWhileRouteL 0#64 sp 0x80004070#64 s0 s1 s2 s3) [])).log := by
    rw [hmem] at hmemB
    exact hmemB
  have houtB' : σB.sailOutput = out0 := by rw [houtB, hout]
  refine ⟨⟨σB, iB, cT.steps + evalBlocksFuel execWhileFalsyBranchSeg⟩,
    hsT.trans hsB, ?_, ?_, hiB, hmiB⟩
  · exact ⟨hGB, hmemB', houtB', by rw [hpcB]; rfl, hregsB⟩
  · intro R hR
    exact (abiFrame_of_wrChain (by
      show WrChainAvoidAbi execWhileFalsyBranchSeg
      decide) hframeB R hR).trans
        (hframe R (notWrittenT_of_abiPreserved R hR))


#print axioms execWhileFalsyHeaderToExitHead_framed

end Vsa.Sim
