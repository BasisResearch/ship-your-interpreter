import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasTraceCheck

/-! Reached trace carriers retain absence of the machine exception CSR.
The initial data log includes the access snapshot's prefix writes. Memory is
still represented by the existing `writeLog snapshotMem d.log` interface.

The segment adapter uses `segEval_sound`'s full register frame. Both linking
call adapters use the actual instruction post and frame. No claim about
arbitrary `Steps` or exception-state preservation is assumed.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa Vsa.Machine Vsa.MemRepr

namespace Vsa.Sim.AstAccessAudit

open Vsa.Sim.OutputAliasLoaded

/-- The exact reached trace state, retaining an absent exception-cause CSR. -/
structure AccessHolds (d : TraceData) (c : Config) : Prop extends TraceHolds d c where
  mcause_absent : c.σ.regs.get? Register.mcause = none

/-- GPR writes never target the machine exception-cause CSR. -/
private theorem gprReg_mcause (n : Nat) : (gprReg n == Register.mcause) = false := by
  unfold gprReg
  split <;> rfl

/-- Data normalization preserves the exception fact at the same endpoint. -/
theorem AccessHolds.rebase {source target : TraceData} {c : Config}
    (h : AccessHolds source c) (fit : TraceFits source target) : AccessHolds target c where
  toTraceHolds := h.toTraceHolds.rebase fit
  mcause_absent := h.mcause_absent

/-- Segment certificates preserve the full reached trace state, including HTIF. -/
theorem AccessHolds.segment {d : TraceData} {c : Config}
    (h : AccessHolds d c) (bs : List BBlock) (lds : List (List (BitVec 8)))
    (hkeys : KeysOK (keysG d.regs))
    (hfacts : ChainFacts (writeLog snapshotMem d.log) (writeLog snapshotMem d.log)
      d.regs lds bs)
    (hwf : ChainOK d.pc (keysG d.regs) bs)
    (hpayload : ∀ n ∈ wrChain bs, (gprReg n == Register.htif_payload_writes) = false) :
    ∃ c', Steps c c' ∧ AccessHolds (d.afterSegment bs lds) c' := by
  obtain ⟨vm, hvm⟩ := h.minstret
  have hcf : ChainFacts c.σ.mem c.σ.mem d.regs lds bs := by
    rw [h.mem]
    exact hfacts
  obtain ⟨σ', i', hs, hi', hG', hm', ho', hp', hmi', hr', hf'⟩ :=
    segEval_sound bs c.σ c.tick c.steps d.pc vm d.regs lds
      h.good h.pc hvm h.regs hkeys hcf hwf h.tick
  refine ⟨⟨σ', i', c.steps + evalBlocksFuel bs⟩, hs, ?_⟩
  exact {
    good := hG'
    tick := hi'
    pc := hp'
    minstret := hmi'
    regs := hr'
    mem := by
      change σ'.mem = writeLog snapshotMem
        (d.log ++ (evalBlocks bs (SegEvalState.init d.regs lds)).log)
      rw [writeLog_append, ← h.mem]
      exact hm'
    out := ho'.trans h.out
    payload := (hf' Register.htif_payload_writes (by decide) hpayload).trans h.payload
    mcause_absent := (hf' Register.mcause (by decide)
      (fun n _ => gprReg_mcause n)).trans h.mcause_absent }


private theorem gpr_avoids_noise : ∀ n, n < 32 → 1 ≤ n →
    ∀ R ∈ noiseRegs, (R == gprReg n) = false := by decide

/-- The existing register-frame theorem handles all GPR indices. -/
private theorem gholds_call {σ' σ : MState} {link : BitVec 64}
    (hra : gprGet σ' 1 = some link)
    (hf : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ n ∈ ([1] : List Nat), (gprReg n == R) = false) →
      σ'.regs.get? R = σ.regs.get? R)
    (L : GRegs) (hk : KeysOK (keysG L)) (h : GHolds σ L) :
    GHolds σ' ((1, link) :: eraseG 1 L) := by
  refine ⟨hra, ?_⟩
  induction L with
  | nil => exact True.intro
  | cons p L ih =>
    obtain ⟨n, v⟩ := p
    have ht : KeysOK (keysG L) := fun k hmem =>
      hk k (List.mem_cons_of_mem n hmem)
    obtain ⟨hn1, hn31⟩ := hk n (List.mem_cons_self ..)
    by_cases heq : n = 1
    · simp only [eraseG, heq, ↓reduceIte]
      exact ih ht h.2
    · simp only [eraseG, heq, ↓reduceIte, GHolds]
      refine ⟨?_, ih ht h.2⟩
      apply Eq.trans (gprGet_of_frame n hn1 hn31
        (gpr_avoids_noise n (by omega) hn1) ?_ hf) h.1
      intro m hm
      have hm1 : m = 1 := List.mem_singleton.mp hm
      subst m
      exact gprReg_beq_false 1 (by decide) n (by omega)
        (by decide) hn1 (Ne.symm heq)

private theorem access_decode_at {d : TraceData} {w : BitVec 32}
    {ins : instruction} {b0 b1 b2 b3 : BitVec 8}
    (f : TraceCallFacts d w ins b0 b1 b2 b3) {c : Config}
    (h : TraceHolds d c) :
    (ext_decode w).run (afterPrelude c.σ) = .ok ins (afterPrelude c.σ) := by
  apply f.decode
  · rw [get?_afterPrelude c.σ _ (by decide)]
    exact h.good.misa
  · rw [get?_afterPrelude c.σ _ (by decide)]
    exact h.good.cur_privilege
  · rw [get?_afterPrelude c.σ _ (by decide)]
    exact h.good.mseccfg

/-- One direct linking call, including the exact memory log and HTIF payload. -/
theorem AccessHolds.jal {d : TraceData} {c : Config}
    (h : AccessHolds d c) (w : BitVec 32) (imm : BitVec 21)
    (b0 b1 b2 b3 : BitVec 8)
    (f : TraceCallFacts d w (instruction.JAL (imm, gprIdx 1)) b0 b1 b2 b3)
    (hk : KeysOK (keysG d.regs))
    (htgt : (d.pc + sign_extend (m := 64) imm).toNat % 4 = 0) :
    ∃ c', Steps c c' ∧ AccessHolds
      (d.afterCall (d.pc + sign_extend (m := 64) imm)) c' := by
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨σ', i', hs, hi, hg, hm, ho⟩ :=
    stepObs_jal c.σ c.tick c.steps d.pc vm w imm (gprIdx 1) Register.x1
      (BitVec.addInt d.pc 4) b0 b1 b2 b3 h.good h.pc hvm
      (by rw [h.mem]; exact f.byte0) (by rw [h.mem]; exact f.byte1)
      (by rw [h.mem]; exact f.byte2) (by rw [h.mem]; exact f.byte3)
      f.lower f.upper f.aligned f.uncompressed f.word (access_decode_at f h.toTraceHolds) htgt
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt d.pc 4)) h.tick
  have hf : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ n ∈ ([1] : List Nat), (gprReg n == R) = false) →
      σ'.regs.get? R = c.σ.regs.get? R := by
    intro R hn hw
    exact (ho.1 R (hn _ (by decide)) (hn _ (by decide))
      (hn _ (by decide))).trans
      (get?_sigmaPost_jal c.σ d.pc vm imm Register.x1 _ R
        (hn _ (by decide)) (hn _ (by decide)) (hw 1 (by simp))
        (hn _ (by decide)) (hn _ (by decide)))
  refine ⟨⟨σ', i', c.steps + 1⟩, Steps.single hs, ?_⟩
  exact {
    good := hg
    tick := hi
    pc := obs_jal_pc_env ho
    minstret := obs_jal_minstret_env ho
    regs := gholds_call (obs_jal_rd_env ho (by decide) (by decide)
      (by decide) (by decide) (by decide)) hf d.regs hk h.regs
    mem := hm.trans h.mem
    out := ho.out.trans h.out
    payload := (hf Register.htif_payload_writes (by decide) (by decide)).trans h.payload
    mcause_absent := (hf Register.mcause (by decide) (by decide)).trans h.mcause_absent }

/-- One indirect linking call. The source is read from the reached GPR list,
before x1 is overwritten, so rs1=x1 is supported. -/
theorem AccessHolds.jalr {d : TraceData} {c : Config}
    (h : AccessHolds d c) (w : BitVec 32) (imm : BitVec 12)
    (rs1 : Nat) (vrs1 : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (f : TraceCallFacts d w (instruction.JALR (imm, gprIdx rs1, gprIdx 1))
      b0 b1 b2 b3)
    (hk : KeysOK (keysG d.regs)) (hr1 : 1 ≤ rs1) (hr31 : rs1 ≤ 31)
    (hr : lookupG rs1 d.regs = some vrs1)
    (htgt : (Sail.BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0) :
    ∃ c', Steps c c' ∧ AccessHolds
      (d.afterCall (Sail.BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)) c' := by
  obtain ⟨vm, hvm⟩ := h.minstret
  have hp : srcPin c.σ rs1 vrs1 := by
    cases rs1 with
    | zero => omega
    | succ n => exact gholds_lookup d.regs h.regs hr
  obtain ⟨σ', i', hs, hi, hg, hm, ho⟩ :=
    stepObs_jalr c.σ c.tick c.steps d.pc vm vrs1 w imm (gprIdx rs1) (gprIdx 1)
      Register.x1 (BitVec.addInt d.pc 4) b0 b1 b2 b3 h.good h.pc hvm
      (by rw [h.mem]; exact f.byte0) (by rw [h.mem]; exact f.byte1)
      (by rw [h.mem]; exact f.byte2) (by rw [h.mem]; exact f.byte3)
      f.lower f.upper f.aligned f.uncompressed f.word (access_decode_at f h.toTraceHolds)
      (rX_src c.σ d.pc rs1 hr31 vrs1 hp) htgt
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt d.pc 4)) h.tick
  have hf : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ n ∈ ([1] : List Nat), (gprReg n == R) = false) →
      σ'.regs.get? R = c.σ.regs.get? R := by
    intro R hn hw
    exact (ho.1 R (hn _ (by decide)) (hn _ (by decide))
      (hn _ (by decide))).trans
      (post_jalr_other c.σ d.pc vm _ Register.x1 _ R
        (hn _ (by decide)) (hn _ (by decide)) (hw 1 (by simp))
        (hn _ (by decide)) (hn _ (by decide)))
  refine ⟨⟨σ', i', c.steps + 1⟩, Steps.single hs, ?_⟩
  exact {
    good := hg
    tick := hi
    pc := obs_jalr_pc ho
    minstret := obs_jalr_minstret ho
    regs := gholds_call (obs_jalr_rd ho (by decide) (by decide)
      (by decide) (by decide) (by decide)) hf d.regs hk h.regs
    mem := hm.trans h.mem
    out := ho.out.trans h.out
    payload := (hf Register.htif_payload_writes (by decide) (by decide)).trans h.payload
    mcause_absent := (hf Register.mcause (by decide) (by decide)).trans h.mcause_absent }

#print axioms AccessHolds.rebase
#print axioms AccessHolds.segment
#print axioms AccessHolds.jal
#print axioms AccessHolds.jalr

end Vsa.Sim.AstAccessAudit
