import Vsa.Sim.GoodState
import Vsa.Sim.StateNF
import Vsa.Sim.StepAddi
import Vsa.Sim.StepBeq

open LeanRV64DExecutable Sail ConcurrencyInterfaceV1
open Vsa.Machine (MState)

namespace Vsa.Sim

def isNonPinned (r : Register) : Bool :=
  match r with
  | .cur_privilege | .misa | .mstatus | .mie | .mseccfg | .satp | .mtvec
  | .mideleg | .medeleg | .hart_state | .htif_done | .htif_tohost
  | .htif_tohost_base | .elp | .pmpcfg_n | .pmpaddr_n | .pma_regions
  | .menvcfg | .mcountinhibit | .mcyclecfg | .minstretcfg => false
  | _ => true

abbrev NonPinned (r : Register) : Prop := isNonPinned r = true

theorem pin_of_isNonPinned {r A : Register}
    (hr : isNonPinned r = true) (hA : isNonPinned A = false) : (r == A) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro h; subst h; rw [hr] at hA; exact absurd hA (by decide)

theorem get?_insert_pinned (regs : Std.ExtDHashMap Register RegisterType)
    (r : Register) (v : RegisterType r) (A : Register)
    (hne : (r == A) = false) :
    (regs.insert r v).get? A = regs.get? A := by
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hne, dif_neg, Bool.false_eq_true, not_false_eq_true]

theorem exists_get?_insert (regs : Std.ExtDHashMap Register RegisterType)
    (r : Register) (v : RegisterType r) (A : Register)
    (h : ∃ w, regs.get? A = some w) : ∃ w, (regs.insert r v).get? A = some w := by
  rw [Std.ExtDHashMap.get?_insert]
  by_cases hc : (r == A) = true
  · simp only [hc, dif_pos]; exact ⟨_, rfl⟩
  · simp only [hc, dif_neg, Bool.not_eq_true]; exact h

theorem GoodState.insert_nonpinned {σ : MState} (hG : GoodState σ)
    {r : Register} (hr : NonPinned r) (v : RegisterType r) :
    GoodState {σ with regs := σ.regs.insert r v} := by
  have P : ∀ (A : Register), isNonPinned A = false →
      ({σ with regs := σ.regs.insert r v}).regs.get? A = σ.regs.get? A :=
    fun A hA => get?_insert_pinned σ.regs r v A (pin_of_isNonPinned hr hA)
  have E : ∀ (A : Register), (∃ w, σ.regs.get? A = some w) →
      ∃ w, ({σ with regs := σ.regs.insert r v}).regs.get? A = some w :=
    fun A h => exists_get?_insert σ.regs r v A h
  constructor
  case cur_privilege => rw [P _ (by decide)]; exact hG.cur_privilege
  case misa => rw [P _ (by decide)]; exact hG.misa
  case mstatus => rw [P _ (by decide)]; exact hG.mstatus
  case mie => rw [P _ (by decide)]; exact hG.mie
  case mseccfg => rw [P _ (by decide)]; exact hG.mseccfg
  case satp => rw [P _ (by decide)]; exact hG.satp
  case mtvec => rw [P _ (by decide)]; exact hG.mtvec
  case mideleg => rw [P _ (by decide)]; exact hG.mideleg
  case medeleg => rw [P _ (by decide)]; exact hG.medeleg
  case hart_state => rw [P _ (by decide)]; exact hG.hart_state
  case htif_done => rw [P _ (by decide)]; exact hG.htif_done
  case htif_tohost => rw [P _ (by decide)]; exact hG.htif_tohost
  case htif_tohost_base => rw [P _ (by decide)]; exact hG.htif_tohost_base
  case elp => rw [P _ (by decide)]; exact hG.elp
  case pmpcfg_n => rw [P _ (by decide)]; exact hG.pmpcfg_n
  case pmpaddr_n => rw [P _ (by decide)]; exact hG.pmpaddr_n
  case pma_regions => rw [P _ (by decide)]; exact hG.pma_regions
  case menvcfg => rw [P _ (by decide)]; exact hG.menvcfg
  case mcountinhibit => rw [P _ (by decide)]; exact hG.mcountinhibit
  case mcyclecfg => rw [P _ (by decide)]; exact hG.mcyclecfg
  case minstretcfg => rw [P _ (by decide)]; exact hG.minstretcfg
  case mip => exact E _ hG.mip
  case sig_meip => exact E _ hG.sig_meip
  case sig_seip => exact E _ hG.sig_seip
  case mtime => exact E _ hG.mtime
  case mtimecmp => exact E _ hG.mtimecmp
  case minstret => exact E _ hG.minstret
  case minstret_increment => exact E _ hG.minstret_increment
  case mcycle => exact E _ hG.mcycle
  case nextPC => exact E _ hG.nextPC
  case PC => exact E _ hG.PC

theorem GoodState.of_regs_eq {σ σ' : MState} (h : σ'.regs = σ.regs)
    (hG : GoodState σ) : GoodState σ' := by
  constructor
  case cur_privilege => rw [h]; exact hG.cur_privilege
  case misa => rw [h]; exact hG.misa
  case mstatus => rw [h]; exact hG.mstatus
  case mie => rw [h]; exact hG.mie
  case mseccfg => rw [h]; exact hG.mseccfg
  case satp => rw [h]; exact hG.satp
  case mtvec => rw [h]; exact hG.mtvec
  case mideleg => rw [h]; exact hG.mideleg
  case medeleg => rw [h]; exact hG.medeleg
  case hart_state => rw [h]; exact hG.hart_state
  case htif_done => rw [h]; exact hG.htif_done
  case htif_tohost => rw [h]; exact hG.htif_tohost
  case htif_tohost_base => rw [h]; exact hG.htif_tohost_base
  case elp => rw [h]; exact hG.elp
  case pmpcfg_n => rw [h]; exact hG.pmpcfg_n
  case pmpaddr_n => rw [h]; exact hG.pmpaddr_n
  case pma_regions => rw [h]; exact hG.pma_regions
  case menvcfg => rw [h]; exact hG.menvcfg
  case mcountinhibit => rw [h]; exact hG.mcountinhibit
  case mcyclecfg => rw [h]; exact hG.mcyclecfg
  case minstretcfg => rw [h]; exact hG.minstretcfg
  case mip => rw [h]; exact hG.mip
  case sig_meip => rw [h]; exact hG.sig_meip
  case sig_seip => rw [h]; exact hG.sig_seip
  case mtime => rw [h]; exact hG.mtime
  case mtimecmp => rw [h]; exact hG.mtimecmp
  case minstret => rw [h]; exact hG.minstret
  case minstret_increment => rw [h]; exact hG.minstret_increment
  case mcycle => rw [h]; exact hG.mcycle
  case nextPC => rw [h]; exact hG.nextPC
  case PC => rw [h]; exact hG.PC

syntax (name := goodstateFrame) "goodstate_frame " term : tactic

macro_rules
  | `(tactic| goodstate_frame $h:term) =>
    `(tactic|
      (repeat' first
        | exact $h
        | (apply GoodState.insert_nonpinned (hr := by decide))))

end Vsa.Sim
