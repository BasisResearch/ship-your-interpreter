import Vsa.Sim.Skeleton
import Vsa.Sim.Frame

/-!
# Retirement: one commit rule for every instruction kind

An instruction that retires moves the machine from `σ` to `retirePost σ3 npc vm`, where `σ3` is
whatever `execute` returned from the prelude state `afterNextPC (afterPrelude σ) pc`. The front of
`try_step` (interrupt dispatch, fetch, decode, landing pad) and the back (`PC := nextPC`,
`minstret += 1`, the clock tick of `stepOnce`) do not depend on the kind. The theorems here are
stated over an abstract `σ3`; a kind supplies only its `execute` fact and the four `RetireReads`
of its post-execute state.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

namespace Vsa.Sim

/-- Decision procedure for reads through a chain of register `insert`s (law L-frame): each key
comparison is decided by `decide`; the listed facts close the reads that reach the base state. -/
macro "reg_reads" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp (config := {decide := true}) only
    [Std.ExtDHashMap.get?_insert, dite_true, dite_false, cast_eq, $hs,*] <;> rfl))

/-- The state after `try_step` retires with post-execute state `σ3`. -/
abbrev retirePost (σ3 : MState) (npc vm : BitVec 64) : MState :=
  {(({σ3 with regs := σ3.regs.insert Register.PC npc}) : MState) with
    regs := (({σ3 with regs := σ3.regs.insert Register.PC npc}) : MState).regs.insert
      Register.minstret (BitVec.addInt vm 1)}

/-- The state after the clock tick of `stepOnce`. -/
noncomputable abbrev tickPost (s : MState) (vmip vmtime vmtimecmp vmcycle : BitVec 64) : MState :=
  {s with regs := (((s.regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert
    Register.mtime (BitVec.addInt vmtime 1)).insert Register.mip
      (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp (BitVec.addInt vmtime 1)))))}

/-- The four reads `try_step` performs on the post-execute state. -/
structure RetireReads (σ3 : MState) (npc vm : BitVec 64) : Prop where
  hart : σ3.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ())
  nextPC : σ3.regs.get? Register.nextPC = some npc
  inc : σ3.regs.get? Register.minstret_increment = some true
  minstret : σ3.regs.get? Register.minstret = some vm

/-- The fetched instruction at `pc`: pins, program counter, the four bytes and their decode. -/
structure Fetched (σ : MState) (pc : BitVec 64) (ast : instruction) : Prop where
  good : GoodState σ
  pcReg : σ.regs.get? Register.PC = some pc
  lo : 0x80000000 ≤ pc.toNat
  hi : pc.toNat + 4 ≤ tohostAddr
  align : pc.toNat % 4 = 0
  word : ∃ b0 b1 b2 b3 : BitVec 8,
    σ.mem[pc.toNat]? = some b0 ∧ σ.mem[pc.toNat + 1]? = some b1 ∧
    σ.mem[pc.toNat + 2]? = some b2 ∧ σ.mem[pc.toNat + 3]? = some b3 ∧
    Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2) ∧
    (ext_decode (((b3.append b2).append b1).append b0)).run (afterPrelude σ)
      = .ok ast (afterPrelude σ)

theorem Fetched.of_bytes {σ : MState} {pc : BitVec 64} {ast : instruction} {w : BitVec 32}
    {b0 b1 b2 b3 : BitVec 8} (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ) = .ok ast (afterPrelude σ)) :
    Fetched σ pc ast :=
  ⟨hG, hpc, hlo, hhi, halign, b0, b1, b2, b3, hb0, hb1, hb2, hb3, hnotrvc, hword ▸ hdec⟩

/-- **Commit (front).** Every retiring instruction: `try_step` returns the retire post-state. -/
theorem try_step_retire {σ σ3 : MState} {u : Nat} {pc npc vm : BitVec 64} {ast : instruction}
    (F : Fetched σ pc ast)
    (hexec : (execute ast).run (afterNextPC (afterPrelude σ) pc) = .ok RETIRE_SUCCESS σ3)
    (R : RetireReads σ3 npc vm) :
    (try_step u true).run σ = .ok false (retirePost σ3 npc vm) := by
  obtain ⟨hG, hpc, hlo, hhi, halign, b0, b1, b2, b3, hb0, hb1, hb2, hb3, hnotrvc, hdec⟩ := F
  have P : ∀ (A : Register) {v : RegisterType A}, (Register.minstret_increment == A) = false →
      σ.regs.get? A = some v → (afterPrelude σ).regs.get? A = some v :=
    fun A _ h hv => (get?_afterPrelude σ A h).trans hv
  obtain ⟨vmip, hmip⟩ := hG.mip
  obtain ⟨vmeip, hmeip⟩ := hG.sig_meip
  obtain ⟨vseip, hseip⟩ := hG.sig_seip
  exact try_step_execute_char σ u pc npc _ ast σ3 vm
    hG.cur_privilege hG.hart_state hG.mcountinhibit hG.minstretcfg hpc
    (dispatch_none _ vmip vmeip vseip _ _ (P _ (by decide) hG.misa) (P _ (by decide) hG.mie)
      (P _ (by decide) hmip) (P _ (by decide) hmeip) (P _ (by decide) hseip)
      (P _ (by decide) hG.mideleg) (P _ (by decide) hG.mstatus))
    (fetch_F_Base _ pc b0 b1 b2 b3 _ _ _ (P _ (by decide) hpc) (P _ (by decide) hG.cur_privilege)
      (P _ (by decide) hG.mstatus) (P _ (by decide) hG.misa) (P _ (by decide) hG.pma_regions)
      (P _ (by decide) hG.pmpcfg_n) (P _ (by decide) hG.pmpaddr_n)
      (P _ (by decide) hG.htif_tohost_base) hlo hhi halign
      (by rw [mem_afterPrelude]; exact hb0) (by rw [mem_afterPrelude]; exact hb1)
      (by rw [mem_afterPrelude]; exact hb2) (by rw [mem_afterPrelude]; exact hb3) hnotrvc)
    hdec (is_landing_pad_expected_false _ (P _ (by decide) hG.elp))
    hexec R.hart R.nextPC R.inc R.minstret

/-- **Commit (back, no tick).** -/
theorem stepOnce_retire_notick {σ s : MState} {i u : Nat}
    (hts : (try_step u true).run σ = .ok false s) (hG : GoodState σ) (hGs : GoodState s)
    (htick : i + 1 ≠ 2) :
    (stepOnce i u).run σ = .ok (.inr (i + 1, u + 1)) s := by
  simp only [EStateM.run] at hts
  have hhtif := hG.htif_done
  have hhtif' := hGs.htif_done
  unfold stepOnce
  simp only [bind, Bind.bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get, hhtif,
    Bool.false_eq_true, ite_false]
  rw [hts]
  simp only [Bool.false_eq_true, ite_false, EStateM.pure, EStateM.bind, EStateM.get, hhtif']
  have htick' : (i + 1 == Int.toNat plat_insns_per_tick) = false := by
    simp only [plat_insns_per_tick, show Int.toNat 2 = 2 from rfl, beq_eq_false_iff_ne]
    exact htick
  simp only [htick', Bool.false_eq_true, ite_false, EStateM.pure]

/-- **Commit (back, tick).** The clock touches only `mcycle`, `mtime`, `mip`. -/
theorem stepOnce_retire_tick {σ s : MState} {i u : Nat} {vmip vmtime vmtimecmp vmcycle : BitVec 64}
    (hts : (try_step u true).run σ = .ok false s) (hG : GoodState σ) (hGs : GoodState s)
    (hmip : s.regs.get? Register.mip = some vmip)
    (hmtime : s.regs.get? Register.mtime = some vmtime)
    (hmtimecmp : s.regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : s.regs.get? Register.mcycle = some vmcycle)
    (htick : i + 1 = 2) :
    (stepOnce i u).run σ = .ok (.inr (0, u + 1)) (tickPost s vmip vmtime vmtimecmp vmcycle) := by
  simp only [EStateM.run] at hts
  have hhtif := hG.htif_done
  have hhtif' := hGs.htif_done
  have htc := tick_clock_char s vmip vmtime vmtimecmp vmcycle
    hGs.cur_privilege hGs.mcountinhibit hGs.mcyclecfg hGs.menvcfg hGs.misa
    hmip hmtime hmtimecmp hmcycle hGs.sig_meip hGs.sig_seip
  simp only [EStateM.run] at htc
  unfold stepOnce
  simp only [bind, Bind.bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get, hhtif,
    Bool.false_eq_true, ite_false]
  rw [hts]
  simp only [Bool.false_eq_true, ite_false, EStateM.pure, EStateM.bind, EStateM.get, hhtif']
  have htick' : (i + 1 == Int.toNat plat_insns_per_tick) = true := by
    simp only [plat_insns_per_tick, show Int.toNat 2 = 2 from rfl, beq_iff_eq]
    exact htick
  simp only [htick', ite_true, EStateM.bind]
  rw [htc]
  rfl

theorem GoodState.tickPost {s : MState} (hGs : GoodState s) (vmip vmtime vmtimecmp vmcycle : BitVec 64) :
    GoodState (tickPost s vmip vmtime vmtimecmp vmcycle) :=
  ((hGs.insert_nonpinned (r := Register.mcycle) (by decide) _).insert_nonpinned
    (r := Register.mtime) (by decide) _).insert_nonpinned (r := Register.mip) (by decide) _

theorem GoodState.retirePost {σ3 : MState} (hG : GoodState σ3) (npc vm : BitVec 64) :
    GoodState (retirePost σ3 npc vm) :=
  (hG.insert_nonpinned (r := Register.PC) (by decide) _).insert_nonpinned
    (r := Register.minstret) (by decide) _

/-- **Commit (machine step, no tick).** -/
theorem step_retire_notick {σ s : MState} {i u : Nat}
    (hts : (try_step u true).run σ = .ok false s) (hG : GoodState σ) (hGs : GoodState s)
    (htick : i + 1 ≠ 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩ ⟨s, i + 1, u + 1⟩ ∧ GoodState s :=
  ⟨Vsa.Machine.Step.mk (stepOnce_retire_notick hts hG hGs htick), hGs⟩

/-- **Commit (machine step, tick).** -/
theorem step_retire_tick {σ s : MState} {i u : Nat} {vmip vmtime vmtimecmp vmcycle : BitVec 64}
    (hts : (try_step u true).run σ = .ok false s) (hG : GoodState σ) (hGs : GoodState s)
    (hmip : s.regs.get? Register.mip = some vmip)
    (hmtime : s.regs.get? Register.mtime = some vmtime)
    (hmtimecmp : s.regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : s.regs.get? Register.mcycle = some vmcycle)
    (htick : i + 1 = 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩ ⟨tickPost s vmip vmtime vmtimecmp vmcycle, 0, u + 1⟩
    ∧ GoodState (tickPost s vmip vmtime vmtimecmp vmcycle) :=
  ⟨Vsa.Machine.Step.mk (stepOnce_retire_tick hts hG hGs hmip hmtime hmtimecmp hmcycle htick),
   hGs.tickPost _ _ _ _⟩

end Vsa.Sim
