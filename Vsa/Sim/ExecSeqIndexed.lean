import Vsa.Sim.ExecSimCommon
import Vsa.Sim.ExecBlock
import Vsa.While.Cost

namespace Vsa.Sim

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (Config)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

local notation "SpecSt" => Vsa.While.St

/-- Static geometry proving that an `exec_stmt` child cannot touch the closure
caller's high spill window. -/
structure ClosureBodyFrameGeom
    (A : Arena) (SL : StackLayout) (sp aRet : BitVec 64) : Prop where
  stackLo : SL.lo ≤ sp.toNat
  arenaBelow : A.hi ≤ SL.lo
  retBelow : aRet.toNat + 24 ≤ sp.toNat + 168

/-- The recursive statement contract already frames every closure-caller byte
at or above `sp+168`.  Thus the sequence resume need only prove preservation
for its own finite instruction segment. -/
theorem closureBodyStackFrame_of_execExitD
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {nf nc : Nat} {st' : SpecSt} {status : Status}
    {sp r aRet : BitVec 64} {m0 : Mem} {c : Config}
    (G : ClosureBodyFrameGeom A SL sp aRet)
    (h : ExecExitD g N A SL φf φc nf nc st' status sp r aRet m0 c) :
    ExecSeqStackFrame .closureBody SL sp m0 c.σ.mem := by
  intro a hlo hhi
  have hArenaBelow := G.arenaBelow
  have hStackLo := G.stackLo
  have hRetBelow := G.retBelow
  rcases h.1.memFrame a (by omega) (by
      intro ha
      omega) with hret | heq
  · exfalso
    omega
  · exact heq

#print axioms closureBodyStackFrame_of_execExitD

theorem execSeqCopy_supports_normal (copy : ExecSeqCopy) :
    copy.Supports .normal := by
  cases copy <;> simp [ExecSeqCopy.Supports]

/-- The status-indexed landing of one physical sequence-loop iteration. -/
def ExecSeqStepPostI
    (copy : ExecSeqCopy)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (phiF phiC : Addr → Nat)
    (st st' stFin : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt)
    (sp aRet : BitVec 64) (m0 : Mem) (status : Status)
    (cfg : Config) : Prop :=
  (status = .normal ∧
    ∃ phiF' phiC',
      PhiExtends phiF phiF' stFin.store.frames.size ∧
      PhiExtends phiC phiC' stFin.store.closures.size ∧
      ExecSeqEntryI copy g N A SL phiF' phiC' st' d env ss sp aRet cfg.σ.mem cfg ∧
      (∀ a, ¬ (SL.lo ≤ a ∧ a < SL.hi) →
        ¬ (A.lo ≤ a ∧ a < A.hi) → cfg.σ.mem[a]? = m0[a]?) ∧
      ExecSeqStackFrame copy SL sp m0 cfg.σ.mem) ∨
  (status ≠ .normal ∧
    ExecSeqExitI copy g N A SL phiF phiC st.store.frames.size
      st.store.closures.size st' status sp aRet m0 cfg)

/-- One physical sequence-loop iteration.  This is the finite machine seam
needed by the two `ExecSeq.cons` constructors. -/
def ExecSeqStepI
    (copy : ExecSeqCopy)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
    (sp aRet : BitVec 64) (m0 : Mem)
    (st' stFin : SpecSt) (status : Status) (headIH : Prop) : Prop :=
  ExecS st d env s st' status →
  headIH →
  copy.Supports status →
    Triple
      (ExecSeqEntryI copy g N A SL φf φc st d env (s :: ss) sp aRet m0)
    (ExecSeqStepPostI copy g N A SL φf φc st st' stFin d env ss
      sp aRet m0 status)

/-- The genuinely machine-specific part of one sequence iteration. The
recursive `exec_stmt` call is not an oracle here: `dispatch` lands at its exact
entry, and `resume` starts at its exact typed exit. -/
structure ExecSeqStepGeomI
    (copy : ExecSeqCopy)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
    (sp aRet : BitVec 64) (m0 : Mem)
    (st' stFin : SpecSt) (status : Status) : Prop where
  childFrame : match copy with
    | .closureBody => ClosureBodyFrameGeom A SL sp aRet
    | _ => True
  dispatch : Triple
    (ExecSeqEntryI copy g N A SL φf φc st d env (s :: ss) sp aRet m0)
    (fun cfg => ∃ (gExec : (R : Register) → Option (RegisterType R))
        (aInterp aStmt aEnv : BitVec 64) (mCall : Mem),
      ExecEntry gExec N A SL φf φc st d env s sp
        (BitVec.ofNat 64 (execSeqChildRetPC copy))
        aInterp aStmt aEnv aRet mCall cfg)
  resume : ∀ (gExec : (R : Register) → Option (RegisterType R))
      (aInterp aStmt aEnv : BitVec 64) (mCall : Mem),
    copy.Supports status →
    Triple
      (fun c =>
        ExecExitD gExec N A SL φf φc st.store.frames.size
          st.store.closures.size st' status sp
          (BitVec.ofNat 64 (execSeqChildRetPC copy)) aRet mCall c ∧
        ExecSeqStackFrame copy SL sp mCall c.σ.mem)
      (ExecSeqStepPostI copy g N A SL φf φc st st' stFin d env ss
        sp aRet m0 status)

/-- Compose a physical dispatch/resume seam with the recursive statement IH. -/
theorem execSeqStepI_of_geom
    (copy : ExecSeqCopy)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
    (sp aRet : BitVec 64) (m0 : Mem) (st' stFin : SpecSt) (status : Status)
    (G : ExecSeqStepGeomI copy g N A SL φf φc st d env s ss sp aRet m0
      st' stFin status) :
    ExecSeqStepI copy g N A SL φf φc st d env s ss sp aRet m0
      st' stFin status (ExecIH st d env s st' status) := by
  intro _hS hIH hsupport cfg hentry
  obtain ⟨cfgE, hsE, gExec, aInterp, aStmt, aEnv, mCall, hExecEntry⟩ :=
    G.dispatch cfg hentry
  obtain ⟨cfgX, hsX, hExecExit⟩ :=
    hIH gExec N A SL φf φc sp
      (BitVec.ofNat 64 (execSeqChildRetPC copy))
      aInterp aStmt aEnv aRet mCall cfgE hExecEntry
  have hChildFrame : ExecSeqStackFrame copy SL sp mCall cfgX.σ.mem := by
    cases copy with
    | interpRun => trivial
    | blockBody => trivial
    | closureBody =>
        exact closureBodyStackFrame_of_execExitD G.childFrame hExecExit
  obtain ⟨cfgR, hsR, hpost⟩ :=
    G.resume gExec aInterp aStmt aEnv mCall hsupport cfgX
      ⟨hExecExit, hChildFrame⟩
  exact ⟨cfgR, (hsE.trans hsX).trans hsR, hpost⟩

#print axioms execSeqStepI_of_geom

/-- Interp-run copy: the recursive statement call is discharged, leaving only
its concrete dispatch/resume machine geometry. -/
theorem execSeqInterpRunStepI
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
    (sp aRet : BitVec 64) (m0 : Mem) (st' stFin : SpecSt) (status : Status)
    (G : ExecSeqStepGeomI .interpRun g N A SL φf φc st d env s ss
      sp aRet m0 st' stFin status) :
    ExecSeqStepI .interpRun g N A SL φf φc st d env s ss sp aRet m0
      st' stFin status (ExecIH st d env s st' status) :=
  execSeqStepI_of_geom .interpRun g N A SL φf φc st d env s ss
    sp aRet m0 st' stFin status G

/-- Closure-body copy: the recursive statement call is discharged, leaving
only its concrete dispatch/resume machine geometry. -/
theorem execSeqClosureBodyStepI
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
    (sp aRet : BitVec 64) (m0 : Mem) (st' stFin : SpecSt) (status : Status)
    (G : ExecSeqStepGeomI .closureBody g N A SL φf φc st d env s ss
      sp aRet m0 st' stFin status) :
    ExecSeqStepI .closureBody g N A SL φf φc st d env s ss sp aRet m0
      st' stFin status (ExecIH st d env s st' status) :=
  execSeqStepI_of_geom .closureBody g N A SL φf φc st d env s ss
    sp aRet m0 st' stFin status G

/-- Block-body copy: the recursive statement call is discharged, leaving only
its concrete dispatch/resume machine geometry. -/
theorem execSeqBlockBodyStepI
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
    (sp aRet : BitVec 64) (m0 : Mem) (st' stFin : SpecSt) (status : Status)
    (G : ExecSeqStepGeomI .blockBody g N A SL φf φc st d env s ss
      sp aRet m0 st' stFin status) :
    ExecSeqStepI .blockBody g N A SL φf φc st d env s ss sp aRet m0
      st' stFin status (ExecIH st d env s st' status) :=
  execSeqStepI_of_geom .blockBody g N A SL φf φc st d env s ss
    sp aRet m0 st' stFin status G

#print axioms execSeqInterpRunStepI
#print axioms execSeqClosureBodyStepI
#print axioms execSeqBlockBodyStepI

/-- One abrupt constructor, once the physical copy's one-step seam is known. -/
theorem execSeqConsAbruptI
    (copy : ExecSeqCopy)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
    (status : Status) (sp aRet : BitVec 64) (m0 : Mem) (headIH : Prop)
    (hS : ExecS st d env s st' status) (hHead : headIH)
    (hne : status ≠ .normal) (hsupport : copy.Supports status)
    (hstep : ExecSeqStepI copy g N A SL φf φc st d env s ss sp aRet m0
      st' st' status headIH) :
    Triple
      (ExecSeqEntryI copy g N A SL φf φc st d env (s :: ss) sp aRet m0)
      (ExecSeqExitI copy g N A SL φf φc st.store.frames.size
        st.store.closures.size st' status sp aRet m0) := by
  intro cfg hentry
  obtain ⟨cfg', hs, hpost⟩ := hstep hS hHead hsupport cfg hentry
  rcases hpost with ⟨heq, _⟩ | ⟨_, hexit⟩
  · exact absurd heq hne
  · exact ⟨cfg', hs, hexit⟩

#print axioms execSeqConsAbruptI

/-- Rebase an indexed exit across one normal loop iteration. -/
theorem execSeqExitI_extend
    (copy : ExecSeqCopy)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc φf' φc' : Addr → Nat)
    (nf nc nf' nc' : Nat)
    (st' : SpecSt) (status : Status) (sp aRet : BitVec 64)
    (m0 mNow : Mem) (cfg : Config)
    (hmf : nf ≤ nf') (hmc : nc ≤ nc')
    (hpf : PhiExtends φf φf' nf') (hpc : PhiExtends φc φc' nc')
    (hmem : ∀ a, ¬ (SL.lo ≤ a ∧ a < SL.hi) →
      ¬ (A.lo ≤ a ∧ a < A.hi) → mNow[a]? = m0[a]?)
    (hstack : ExecSeqStackFrame copy SL sp m0 mNow)
    (hexit : ExecSeqExitI copy g N A SL φf' φc' nf' nc'
      st' status sp aRet mNow cfg) :
    ExecSeqExitI copy g N A SL φf φc nf nc st' status sp aRet m0 cfg := by
  obtain ⟨φf'', φc'', hpf'', hpc'', hstore⟩ := hexit.store
  exact
    { supported := hexit.supported
      good := hexit.good
      tick := hexit.tick
      pc := hexit.pc
      status_abi := hexit.status_abi
      store := ⟨φf'', φc'', PhiExtends.mono hmf (hpf.trans hpf''),
        PhiExtends.mono hmc (hpc.trans hpc''), hstore⟩
      out := hexit.out
      retval := fun v hv => by
        obtain ⟨φc'', hp'', hrepr⟩ := hexit.retval v hv
        exact ⟨φc'', PhiExtends.mono hmc (hpc.trans hp''), hrepr⟩
      mem_frame := fun a hs ha => by
        rw [hexit.mem_frame a hs ha]
        exact hmem a hs ha
      stack_frame := hstack.trans hexit.stack_frame
      frame := hexit.frame
      minstret := hexit.minstret }

/-- One normal constructor followed by the already-indexed tail IH. -/
theorem execSeqConsNormalI
    (copy : ExecSeqCopy)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st stMid stFin : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
    (status : Status) (sp aRet : BitVec 64) (m0 : Mem) (headIH : Prop)
    (hS : ExecS st d env s stMid .normal) (hHead : headIH)
    (hTailStore : stMid.store.frames.size ≤ stFin.store.frames.size ∧
      stMid.store.closures.size ≤ stFin.store.closures.size)
    (hstep : ExecSeqStepI copy g N A SL φf φc st d env s ss sp aRet m0
      stMid stFin .normal headIH)
    (hTail : ∀ (φf' φc' : Addr → Nat) (mNow : Mem),
      Triple
        (ExecSeqEntryI copy g N A SL φf' φc' stMid d env ss sp aRet mNow)
        (ExecSeqExitI copy g N A SL φf' φc'
          stMid.store.frames.size stMid.store.closures.size
          stFin status sp aRet mNow)) :
    Triple
      (ExecSeqEntryI copy g N A SL φf φc st d env (s :: ss) sp aRet m0)
      (ExecSeqExitI copy g N A SL φf φc st.store.frames.size
        st.store.closures.size stFin status sp aRet m0) := by
  intro cfg hentry
  obtain ⟨cfg1, hs1, hpost⟩ :=
    hstep hS hHead (execSeqCopy_supports_normal copy) cfg hentry
  rcases hpost with ⟨_, φf', φc', hpf, hpc, hentry', hmem, hstack⟩ | ⟨hne, _⟩
  · obtain ⟨cfg2, hs2, hexit⟩ := hTail φf' φc' cfg1.σ.mem cfg1 hentry'
    have hSle := execS_store_mono hS
    refine ⟨cfg2, hs1.trans hs2, ?_⟩
    exact execSeqExitI_extend copy g N A SL φf φc φf' φc'
      st.store.frames.size st.store.closures.size
      stMid.store.frames.size stMid.store.closures.size
      stFin status sp aRet m0 cfg1.σ.mem cfg2
      hSle.1 hSle.2 (PhiExtends.mono hTailStore.1 hpf)
      (PhiExtends.mono hTailStore.2 hpc) hmem hstack hexit
  · exact absurd rfl hne

#print axioms execSeqConsNormalI

/-- Fold the copy-indexed one-step seam over an `ExecSeq` derivation. -/
theorem execSeqLoopI
    (copy : ExecSeqCopy)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (d : Nat) (env : Addr) (sp aRet : BitVec 64)
    (HeadIH : SpecSt → Stmt → SpecSt → Status → Prop)
    (hHead : ∀ (st st' : SpecSt) (s : Stmt) (status : Status),
      ExecS st d env s st' status → HeadIH st s st' status)
    (hstep : ∀ (φf φc : Addr → Nat) (st : SpecSt) (s : Stmt) (ss : List Stmt)
      (st' stFin : SpecSt) (status : Status) (m0 : Mem),
      ExecSeqStepI copy g N A SL φf φc st d env s ss sp aRet m0 st' stFin status
        (HeadIH st s st' status)) :
    ∀ (ss : List Stmt) (φf φc : Addr → Nat) (st st' : SpecSt)
      (status : Status) (m0 : Mem),
      copy.Supports status →
      ExecSeq st d env ss st' status →
      Triple
        (ExecSeqEntryI copy g N A SL φf φc st d env ss sp aRet m0)
        (ExecSeqExitI copy g N A SL φf φc st.store.frames.size
          st.store.closures.size st' status sp aRet m0) := by
  intro ss
  induction ss with
  | nil =>
      intro φf φc st st' status m0 hsupport hseq
      cases hseq
      exact execSeqNilI copy g N A SL φf φc st d env sp aRet m0 hsupport
  | cons s ss ih =>
      intro φf φc st st' status m0 hsupport hseq
      cases hseq with
      | consNormal _ _ _ _ _ stMid _ _ hS hTail =>
          intro cfg hentry
          obtain ⟨cfg1, hs1, hpost⟩ :=
            hstep φf φc st s ss stMid st' .normal m0 hS (hHead st stMid s .normal hS)
              (execSeqCopy_supports_normal copy) cfg hentry
          rcases hpost with ⟨_, φf', φc', hpf, hpc, hentry', hmem, hstack⟩ | ⟨hne, _⟩
          · obtain ⟨cfg2, hs2, hexit⟩ :=
              ih φf' φc' stMid st' status cfg1.σ.mem hsupport hTail cfg1 hentry'
            have hSle := execS_store_mono hS
            have hTle := execSeq_store_mono hTail
            refine ⟨cfg2, hs1.trans hs2, ?_⟩
            exact execSeqExitI_extend copy g N A SL φf φc φf' φc'
              st.store.frames.size st.store.closures.size
              stMid.store.frames.size stMid.store.closures.size
              st' status sp aRet m0 cfg1.σ.mem cfg2
              hSle.1 hSle.2 (PhiExtends.mono hTle.1 hpf)
              (PhiExtends.mono hTle.2 hpc) hmem hstack hexit
          · exact absurd rfl hne
      | consAbrupt _ _ _ _ _ _ _ hS hne =>
          intro cfg hentry
          obtain ⟨cfg1, hs1, hpost⟩ :=
            hstep φf φc st s ss st' st' status m0 hS
              (hHead st st' s status hS) hsupport cfg hentry
          rcases hpost with ⟨heq, _⟩ | ⟨_, hexit⟩
          · exact absurd heq hne
          · exact ⟨cfg1, hs1, hexit⟩

#print axioms execSeqLoopI

end Vsa.Sim
