import Vsa.Sim.ExecSimCommon
import Vsa.Sim.ExecBlock
import Vsa.While.Cost
import Vsa.Sim.RecursiveStepGeom

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
    ExecSeqStackFrame .closureBody A SL sp aRet m0 c.σ.mem := by
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

/-- The recursive statement contract frames every byte at or above the
child's `sp` outside the arena except the forwarded return slot; the block
copy's window starts at `sp+136`, so no geometry is needed. -/
theorem blockBodyStackFrame_of_execExitD
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {nf nc : Nat} {st' : SpecSt} {status : Status}
    {sp r aRet : BitVec 64} {m0 : Mem} {c : Config}
    (h : ExecExitD g N A SL φf φc nf nc st' status sp r aRet m0 c) :
    ExecSeqStackFrame .blockBody A SL sp aRet m0 c.σ.mem := by
  intro a hlo hhi hr hA
  rcases h.1.memFrame a (by intro ha; omega) hA with hret | heq
  · exact absurd hret hr
  · exact heq

#print axioms blockBodyStackFrame_of_execExitD

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
  RecursiveStepPost (status = .normal)
    (fun cfg => ∃ phiF' phiC',
      PhiExtends phiF phiF' st.store.frames.size ∧
      PhiExtends phiC phiC' st.store.closures.size ∧
      ExecSeqEntryI copy g N A SL phiF' phiC' st' d env ss sp aRet cfg.σ.mem cfg ∧
      (∀ a, ¬ (SL.lo ≤ a ∧ a < SL.hi) →
        ¬ (A.lo ≤ a ∧ a < A.hi) → cfg.σ.mem[a]? = m0[a]?) ∧
      ExecSeqStackFrame copy A SL sp aRet m0 cfg.σ.mem ∧
      MemExtends m0 cfg.σ.mem)
    (ExecSeqExitI copy g N A SL phiF phiC st.store.frames.size
      st.store.closures.size st' status sp aRet m0) cfg

/-- A final normal route supplies the empty recursive entry with its chosen maps. -/
theorem execSeqNormalStepPostI_nil_of_exit
    {copy : ExecSeqCopy}
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' stFin : SpecSt} {d : Nat} {env : Addr}
    {sp aRet : BitVec 64} {m0 : Mem} {cfg : Config}
    (h : ExecSeqExitI copy g N A SL φf φc st.store.frames.size
      st.store.closures.size st' .normal sp aRet m0 cfg) :
    ExecSeqStepPostI copy g N A SL φf φc st st' stFin d env []
      sp aRet m0 .normal cfg := by
  obtain ⟨φf', φc', hpf, hpc, hsurv⟩ := h.store_survives
  refine Or.inl ⟨rfl, φf', φc', hpf, hpc, ?_, h.mem_frame, h.stack_frame, h.mem_extends⟩
  exact
    { good := h.good
      tick := h.tick
      pc := by cases copy <;> exact h.pc
      store := hsurv _ (fun _ _ => rfl)
      store_survives := hsurv
      out := h.out
      mem := rfl
      ready := fun hne => (hne rfl).elim
      empty_status := fun _ => h.status_abi
      frame := h.frame
      minstret := h.minstret }

#print axioms execSeqNormalStepPostI_nil_of_exit

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

/-- Actual machine arguments selected by sequence dispatch. -/
structure ExecSeqChildIndex where
  gExec : (R : Register) → Option (RegisterType R)
  aInterp : BitVec 64
  aStmt : BitVec 64
  aEnv : BitVec 64
  mCall : Mem

/-- Dispatch establishes a carrier retained across the actual child IH. -/
def ExecSeqStepGeomI
    (copy : ExecSeqCopy)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
    (sp aRet : BitVec 64) (m0 : Mem)
    (st' stFin : SpecSt) (status : Status) : Prop :=
  ∃ Carrier : ExecSeqChildIndex → Prop,
    ExecS st d env s st' status → copy.Supports status →
    ChildBoundary ExecSeqChildIndex Carrier
      (fun index cfg =>
        (match copy with
          | .closureBody => ClosureBodyFrameGeom A SL sp aRet
          | _ => True) ∧
        ExecEntry index.gExec N A SL φf φc st d env s sp
          (BitVec.ofNat 64 (execSeqChildRetPC copy))
          index.aInterp index.aStmt index.aEnv aRet index.mCall cfg)
      (fun index c =>
        ExecExitD index.gExec N A SL φf φc st.store.frames.size
          st.store.closures.size st' status sp
          (BitVec.ofNat 64 (execSeqChildRetPC copy)) aRet index.mCall c ∧
        ExecSeqStackFrame copy A SL sp aRet index.mCall c.σ.mem)
      (ExecSeqEntryI copy g N A SL φf φc st d env (s :: ss) sp aRet m0)
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
  intro hS hIH hsupport
  obtain ⟨Carrier, hboundary⟩ := G
  apply (hboundary hS hsupport).run
  intro index cfgE hentry
  obtain ⟨cfgX, hsX, hExecExit⟩ :=
    hIH index.gExec N A SL φf φc sp
      (BitVec.ofNat 64 (execSeqChildRetPC copy))
      index.aInterp index.aStmt index.aEnv aRet index.mCall cfgE hentry.2
  have hChildFrame : ExecSeqStackFrame copy A SL sp aRet index.mCall cfgX.σ.mem := by
    cases copy with
    | interpRun => trivial
    | blockBody =>
        exact blockBodyStackFrame_of_execExitD hExecExit
    | closureBody =>
        exact closureBodyStackFrame_of_execExitD hentry.1 hExecExit
  exact ⟨cfgX, hsX, hExecExit, hChildFrame⟩

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
  exact RecursiveStepGeom.terminal ⟨hstep hS hHead hsupport⟩ hne

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
    (hpf : PhiExtends φf φf' nf) (hpc : PhiExtends φc φc' nc)
    (hmem : ∀ a, ¬ (SL.lo ≤ a ∧ a < SL.hi) →
      ¬ (A.lo ≤ a ∧ a < A.hi) → mNow[a]? = m0[a]?)
    (hstack : ExecSeqStackFrame copy A SL sp aRet m0 mNow)
    (hext : MemExtends m0 mNow)
    (hexit : ExecSeqExitI copy g N A SL φf' φc' nf' nc'
      st' status sp aRet mNow cfg) :
    ExecSeqExitI copy g N A SL φf φc nf nc st' status sp aRet m0 cfg := by
  obtain ⟨φf'', φc'', hpf'', hpc'', hstore⟩ := hexit.store
  obtain ⟨φfS, φcS, hpfS, hpcS, hsurv⟩ := hexit.store_survives
  exact
    { supported := hexit.supported
      good := hexit.good
      tick := hexit.tick
      pc := hexit.pc
      status_abi := hexit.status_abi
      store := ⟨φf'', φc'', hpf.trans (PhiExtends.mono hmf hpf''),
        hpc.trans (PhiExtends.mono hmc hpc''), hstore⟩
      out := hexit.out
      retval := fun v hv => by
        obtain ⟨φc'', hp'', hrepr⟩ := hexit.retval v hv
        exact ⟨φc'', hpc.trans (PhiExtends.mono hmc hp''), hrepr⟩
      mem_frame := fun a hs ha => by
        rw [hexit.mem_frame a hs ha]
        exact hmem a hs ha
      stack_frame := hstack.trans hexit.stack_frame
      mem_extends := hext.trans hexit.mem_extends
      store_survives := ⟨φfS, φcS, hpf.trans (PhiExtends.mono hmf hpfS),
        hpc.trans (PhiExtends.mono hmc hpcS), hsurv⟩
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
  obtain ⟨cfg1, hs1, φf', φc', hpf, hpc, hentry', hmem, hstack, hext⟩ :=
    RecursiveStepGeom.continuing
      ⟨hstep hS hHead (execSeqCopy_supports_normal copy)⟩ rfl cfg hentry
  obtain ⟨cfg2, hs2, hexit⟩ := hTail φf' φc' cfg1.σ.mem cfg1 hentry'
  have hSle := execS_store_mono hS
  refine ⟨cfg2, hs1.trans hs2, ?_⟩
  exact execSeqExitI_extend copy g N A SL φf φc φf' φc'
    st.store.frames.size st.store.closures.size
    stMid.store.frames.size stMid.store.closures.size
    stFin status sp aRet m0 cfg1.σ.mem cfg2
    hSle.1 hSle.2 hpf hpc hmem hstack hext hexit

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
          exact execSeqConsNormalI copy g N A SL φf φc st stMid st' d env s ss
            status sp aRet m0 (HeadIH st s stMid .normal) hS
            (hHead st stMid s .normal hS) (execSeq_store_mono hTail)
            (hstep φf φc st s ss stMid st' .normal m0)
            (fun φf' φc' mNow => ih φf' φc' stMid st' status mNow hsupport hTail)
      | consAbrupt _ _ _ _ _ _ _ hS hne =>
          exact execSeqConsAbruptI copy g N A SL φf φc st st' d env s ss status
            sp aRet m0 (HeadIH st s st' status) hS (hHead st st' s status hS)
            hne hsupport (hstep φf φc st s ss st' st' status m0)

#print axioms execSeqLoopI

end Vsa.Sim
