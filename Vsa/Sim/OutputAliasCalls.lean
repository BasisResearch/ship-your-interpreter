import Vsa.Sim.OutputAliasTrace
import Vsa.Sim.SegToTripleFramed
import Vsa.Sim.SnprintfSitesRet5
import Vsa.Sim.BridgeSegOut

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa Vsa.Machine

namespace Vsa.Sim.OutputAliasLoaded

/-- Fetch and decode facts only; no machine transition is assumed. -/
structure TraceCallFacts (d : TraceData) (w : BitVec 32)
    (ins : instruction) (b0 b1 b2 b3 : BitVec 8) : Prop where
  byte0 : (writeLog snapshotMem d.log)[d.pc.toNat]? = some b0
  byte1 : (writeLog snapshotMem d.log)[d.pc.toNat + 1]? = some b1
  byte2 : (writeLog snapshotMem d.log)[d.pc.toNat + 2]? = some b2
  byte3 : (writeLog snapshotMem d.log)[d.pc.toNat + 3]? = some b3
  lower : 0x80000000 ≤ d.pc.toNat
  upper : d.pc.toNat + 4 ≤ tohostAddr
  aligned : d.pc.toNat % 4 = 0
  uncompressed : Sail.BitVec.extractLsb
    (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2)
  word : (((b3.append b2).append b1).append b0) = w
  decode : ∀ σ : MState,
    σ.regs.get? Register.misa = some initMisa →
    σ.regs.get? Register.cur_privilege = some Privilege.Machine →
    σ.regs.get? Register.mseccfg = some (0#64) →
    (ext_decode w).run σ = .ok ins σ

def TraceData.afterCall (d : TraceData) (target : BitVec 64) : TraceData :=
  { d with pc := target, regs := (1, BitVec.addInt d.pc 4) :: eraseG 1 d.regs }

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

private theorem TraceCallFacts.decode_at {d : TraceData} {w : BitVec 32}
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
theorem TraceHolds.jal {d : TraceData} {c : Config}
    (h : TraceHolds d c) (w : BitVec 32) (imm : BitVec 21)
    (b0 b1 b2 b3 : BitVec 8)
    (f : TraceCallFacts d w (instruction.JAL (imm, gprIdx 1)) b0 b1 b2 b3)
    (hk : KeysOK (keysG d.regs))
    (htgt : (d.pc + sign_extend (m := 64) imm).toNat % 4 = 0) :
    ∃ c', Steps c c' ∧ TraceHolds
      (d.afterCall (d.pc + sign_extend (m := 64) imm)) c' := by
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨σ', i', hs, hi, hg, hm, ho⟩ :=
    stepObs_jal c.σ c.tick c.steps d.pc vm w imm (gprIdx 1) Register.x1
      (BitVec.addInt d.pc 4) b0 b1 b2 b3 h.good h.pc hvm
      (by rw [h.mem]; exact f.byte0) (by rw [h.mem]; exact f.byte1)
      (by rw [h.mem]; exact f.byte2) (by rw [h.mem]; exact f.byte3)
      f.lower f.upper f.aligned f.uncompressed f.word (f.decode_at h) htgt
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
    payload := (hf Register.htif_payload_writes (by decide) (by decide)).trans h.payload }

/-- One indirect linking call. The source is read from the reached GPR list,
before x1 is overwritten, so rs1=x1 is supported. -/
theorem TraceHolds.jalr {d : TraceData} {c : Config}
    (h : TraceHolds d c) (w : BitVec 32) (imm : BitVec 12)
    (rs1 : Nat) (vrs1 : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (f : TraceCallFacts d w (instruction.JALR (imm, gprIdx rs1, gprIdx 1))
      b0 b1 b2 b3)
    (hk : KeysOK (keysG d.regs)) (hr1 : 1 ≤ rs1) (hr31 : rs1 ≤ 31)
    (hr : lookupG rs1 d.regs = some vrs1)
    (htgt : (Sail.BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0) :
    ∃ c', Steps c c' ∧ TraceHolds
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
      f.lower f.upper f.aligned f.uncompressed f.word (f.decode_at h)
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
    payload := (hf Register.htif_payload_writes (by decide) (by decide)).trans h.payload }

#print axioms TraceHolds.jal
#print axioms TraceHolds.jalr

end Vsa.Sim.OutputAliasLoaded
