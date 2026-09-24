import VsaIris.Vsa.Strlen
import VsaIris.Vsa.AllocRun
import Vsa.Sim.DecodeTable.Batch04Part25

/-!
# The allocator's `sltu` (`0x800052d0`)

`_realloc_r`'s request check `sltu a4,a5,a4` is outside `MKind`, so
`gen_alloc_steps.py` emits no step lemma for it. As for `strlen`'s `snez`
(`Strlen.lean`), the instruction is VSA's observational ALU step
(`stepObs_alu` with the decode-table entry `decode_00e7b733`), turned into a
one-step run by `Inst.runFact_of_aluStep`; `swp_aluRR` makes any such step one
`SWP` step, and `st_800052d0` is the lemma the generator would emit.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast
open Vsa.Machine (Config MState)
open Iris
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

section SWP

variable {live : Nat → Prop} {text : List (Nat × BitVec 8)} {rs : List Nat} {S : Nat → Prop}
  {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- **One observational ALU step**: `rd` takes the value and the run
continues at the next instruction. -/
theorem swp_aluRR {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (i : Nat) (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8))
    (rd : Nat) (val : BitVec 64) (hexec : AluStep live i RR MR rd val)
    (hMR : ∀ p ∈ MR, (p.1, p.2.2) ∈ text)
    (hRR : ∀ p ∈ RR, p.1 ∈ rs ∧ p.1 ≠ VsaIris.PC ∧ R p.1 = p.2.2)
    (hPC : VsaIris.PC ∈ rs) (hrd : rd ∈ rs) (hpc : pc = BitVec.ofNat 64 i)
    (hk : SWP live text rs S Q (BitVec.ofNat 64 (i + 4)) (upd R rd val) Mt) :
    SWP live text rs S Q pc R Mt := by
  subst hpc
  obtain ⟨n, hn⟩ := hk
  refine ⟨n + 1, fun rv mv hm => .inr ⟨0, segFrom_of_runFact (MW := [])
    (runFact_of_aluStep (old := rv rd) hexec) (fun p hp => ?_) (fun p hp => .inl (hMR p hp)) ?_
    (fun p hp => by cases hp) ?_⟩⟩
  · obtain ⟨h1, h2, h3⟩ := hRR p hp
    exact .inr ⟨h1, by rw [hm.regs _ h1 h2, h3]⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact .inl ⟨hPC, hm.pc⟩
    · exact .inl ⟨hrd, rfl⟩
  · intro rv' mv' h1 h2 _ h4
    refine hn rv' mv' ⟨h1 _ List.mem_cons_self, fun r hr hne => ?_, fun a ha => ?_⟩
    · by_cases hr1 : r = rd
      · subst hr1
        rw [upd_same]
        exact h1 (r, rv r, val) (by simp)
      · rw [upd_other _ _ hr1]
        refine (h2 r hr fun p hp => ?_).trans (hm.regs r hr hne)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact fun e => hne e.symm
        · exact fun e => hr1 e.symm
    · rw [h4 a ha (fun p hp => by cases hp), hm.img a ha]

end SWP

/-- `sltu a4,a5,a4` executes. -/
theorem exec_sltu_a4_a5_a4 (σ : MState) (pc : BitVec 64) (v14 v15 : BitVec 64)
    (hx14 : σ.regs.get? Register.x14 = some v14) (hx15 : σ.regs.get? Register.x15 = some v15) :
    (execute (instruction.RTYPE (regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0e#5,
        rop.SLTU))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_alu σ pc Register.x14 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v15 v14)))) := by
  have h14 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx14
  have h15 : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx15
  exact execute_rtype_sltu_char (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5)
    v15 v14 (afterNextPC (afterPrelude σ) pc)
    (sigma3_alu σ pc Register.x14 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v15 v14))))
    (rX_bits_x15 _ v15 h15) (rX_bits_x14 _ v14 h14)
    (wX_bits_x14 _ (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v15 v14))))

/-- The code bytes of the `sltu` are allocator text. -/
theorem alloc_code_800052d0 :
    ∀ p ∈ codeFoot 0x800052d0 [0x33#8, 0xb7#8, 0xe7#8, 0x00#8], (p.1, p.2.2) ∈ allocText := by
  intro p hp
  simp only [codeFoot, List.zipIdx, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact List.mem_append_left allocNode180_360 (List.mem_append_right allocNode0_90 (List.mem_append_right allocNode90_135 (List.mem_append_left allocNode157_180 (List.mem_append_right allocNode135_146 (List.mem_append_right allocNode146_151 (List.mem_append_right allocNode151_154 (List.mem_append_left allocNode155_157 ((by decide : ((0x800052d0 : Nat), (0x33#8 : BitVec 8)) ∈ allocChunk154)))))))))
  · exact List.mem_append_left allocNode180_360 (List.mem_append_right allocNode0_90 (List.mem_append_right allocNode90_135 (List.mem_append_left allocNode157_180 (List.mem_append_right allocNode135_146 (List.mem_append_right allocNode146_151 (List.mem_append_right allocNode151_154 (List.mem_append_left allocNode155_157 ((by decide : ((0x800052d1 : Nat), (0xb7#8 : BitVec 8)) ∈ allocChunk154)))))))))
  · exact List.mem_append_left allocNode180_360 (List.mem_append_right allocNode0_90 (List.mem_append_right allocNode90_135 (List.mem_append_left allocNode157_180 (List.mem_append_right allocNode135_146 (List.mem_append_right allocNode146_151 (List.mem_append_right allocNode151_154 (List.mem_append_left allocNode155_157 ((by decide : ((0x800052d2 : Nat), (0xe7#8 : BitVec 8)) ∈ allocChunk154)))))))))
  · exact List.mem_append_left allocNode180_360 (List.mem_append_right allocNode0_90 (List.mem_append_right allocNode90_135 (List.mem_append_left allocNode157_180 (List.mem_append_right allocNode135_146 (List.mem_append_right allocNode146_151 (List.mem_append_right allocNode151_154 (List.mem_append_left allocNode155_157 ((by decide : ((0x800052d3 : Nat), (0x00#8 : BitVec 8)) ∈ allocChunk154)))))))))

theorem sltu_word :
    (((0x00#8).append (0xe7#8)).append (0xb7#8)).append (0x33#8) = (0x00e7b733#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

theorem sltu_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xe7#8)).append (0xb7#8)).append (0x33#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- The `sltu` as one observational ALU step. -/
theorem sltuAluStep {live : Nat → Prop} (hlive : ∀ p ∈ allocText, live p.1) (v14 v15 : BitVec 64) :
    AluStep live 0x800052d0 [(14, DFrac.own 1, v14), (15, DFrac.own 1, v15)]
      (codeFoot 0x800052d0 [0x33#8, 0xb7#8, 0xe7#8, 0x00#8]) 14
      (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v15 v14))) := by
  intro c hok hpc hRR hMR
  have hread := readBytes_present hok _ hMR (fun p hp => hlive _ (alloc_code_800052d0 p hp))
  have hb : ∀ k (b : BitVec 8), ((0x800052d0 + k : Nat), DFrac.discard, b) ∈
      codeFoot 0x800052d0 [0x33#8, 0xb7#8, 0xe7#8, 0x00#8] → c.σ.mem[0x800052d0 + k]? = some b :=
    fun k b h => hread _ h
  have hb0 := hb 0 0x33#8 (by simp [codeFoot])
  have hb1 := hb 1 0xb7#8 (by simp [codeFoot])
  have hb2 := hb 2 0xe7#8 (by simp [codeFoot])
  have hb3 := hb 3 0x00#8 (by simp [codeFoot])
  have hpcσ : c.σ.regs.get? Register.PC = some (0x800052d0#64 : BitVec 64) := by
    obtain ⟨w, hw⟩ := hok.good.PC
    have h : pcVal c.σ = BitVec.ofNat 64 0x800052d0 := hpc
    unfold pcVal at h
    rw [hw] at h ⊢
    exact congrArg some h
  have ha4 : gprGet c.σ 14 = some v14 :=
    gprGet_eq_of_vsaReg hok (by omega) (by omega) (hRR _ List.mem_cons_self)
  have ha5 : gprGet c.σ 15 = some v15 :=
    gprGet_eq_of_vsaReg hok (by omega) (by omega) (hRR _ (.tail _ List.mem_cons_self))
  obtain ⟨vm, hvm⟩ := hok.good.minstret
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    stepObs_alu c.σ c.tick c.steps (0x800052d0#64) vm (0x00e7b733#32)
      (instruction.RTYPE (regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, regidx.Regidx 0x0e#5, rop.SLTU))
      Register.x14 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v15 v14)))
      (0x33#8) (0xb7#8) (0xe7#8) (0x00#8)
      hok.good hpcσ hvm sltu_word sltu_notrvc
      (Vsa.Sim.DecodeTable.decode_00e7b733 (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hok.good.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hok.good.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hok.good.mseccfg))
      (exec_sltu_a4_a5_a4 c.σ (0x800052d0#64) v14 v15 ha4 ha5)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hok.tick
  have hframe := StepFrameOut.of_alu hobs
  have hnoise : ∀ n, n < 32 → 1 ≤ n → ∀ R ∈ noiseRegs, (R == gprReg n) = false := by decide
  have hgprFrame : ∀ n, 1 ≤ n → n ≤ 31 → n ≠ 14 → gprGet σ' n = gprGet c.σ n := by
    intro n h1 h31 hn
    refine gprGet_of_frame (wrs := [14]) n h1 h31 (hnoise n (by omega) h1)
      (fun mm hmm => ?_) (fun R hR hw => hframe.frame R fun rr hrr => ?_)
    · rcases List.mem_cons.mp hmm with rfl | hmm
      · exact gprReg_beq_false 14 (by omega) n (by omega) (by omega) h1 (fun e => hn e.symm)
      · cases hmm
    · rcases List.mem_cons.mp hrr with rfl | hrr
      · exact hw 14 List.mem_cons_self
      · exact hR rr hrr
  have ha4' : σ'.regs.get? Register.x14
      = some (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v15 v14))) :=
    obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨⟨σ', i', c.steps + 1⟩, hstep, ⟨hG', hi', fun n h1 h31 => ?_, fun a ha => ?_, ?_⟩,
    ?_, ?_, ?_, fun a => ?_, ?_⟩
  · show (gprGet σ' n).isSome = true
    by_cases hn : n = 14
    · subst hn
      rw [show gprGet σ' 14 = σ'.regs.get? Register.x14 from rfl, ha4']
      rfl
    · rw [hgprFrame n h1 h31 hn]; exact hok.gpr n h1 h31
  · change (σ'.mem[a]?).isSome
    rw [hmem']; exact hok.live a ha
  · rw [hframe.frame Register.htif_payload_writes (by decide)]; exact hok.htifIdle
  · change pcVal σ' = _
    unfold pcVal
    rw [obs_alu_pc hobs]
    rfl
  · change vsaReg ⟨σ', i', c.steps + 1⟩ 14 = _
    rw [vsaReg_gpr (by decide)]
    change (gprGet σ' 14).getD 0 = _
    rw [show gprGet σ' 14 = σ'.regs.get? Register.x14 from rfl, ha4']
    rfl
  · intro k hkpc hk14
    change vsaReg ⟨σ', i', c.steps + 1⟩ k = vsaReg c k
    rw [vsaReg_gpr hkpc, vsaReg_gpr (c := c) hkpc]
    by_cases hr : 1 ≤ k ∧ k ≤ 31
    · rw [hgprFrame k hr.1 hr.2 hk14]
    · rw [gprGet_none (by unfold VsaIris.PC at hkpc; omega),
        gprGet_none (by unfold VsaIris.PC at hkpc; omega)]
  · change (σ'.mem[a]?).getD 0 = ((c.σ.mem)[a]?).getD 0
    rw [hmem']
  · show Vsa.Machine.output σ' = Vsa.Machine.output c.σ
    unfold Vsa.Machine.output
    rw [hframe.out]

/-- **`sltu a4,a5,a4`** (`0x800052d0`): `a4 := (a5 <u a4)`. -/
theorem st_800052d0 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x800052d4#64
      (upd R 14 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (R 15) (R 14))))) Mt) :
    AW live S Q 0x800052d0#64 R Mt :=
  swp_aluRR 0x800052d0 _ _ 14 _ (sltuAluStep hlive (R 14) (R 15)) alloc_code_800052d0
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact ⟨by dsimp only; decide, by dsimp only; decide, rfl⟩)
    (by decide) (by decide) rfl hk

end VsaIris.Sym
