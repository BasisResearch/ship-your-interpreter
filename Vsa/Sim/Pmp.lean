import Vsa.Elf
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem getElem!_replicate {α : Type} [Inhabited α] (m : Nat) (a : α) (n : Nat)
    (hd : (default : α) = a) : (Vector.replicate m a)[n]! = a := by
  by_cases h : n < m
  · rw [getElem!_pos (Vector.replicate m a) n h, Vector.getElem_replicate]
  · rw [getElem!_neg (Vector.replicate m a) n h]; exact hd

theorem getElem!_replicate_int {α : Type} [Inhabited α] (m : Nat) (a : α) (j : Int)
    (hd : (default : α) = a) : (Vector.replicate m a)[j]! = a := by
  show (Vector.replicate m a)[j.toNat]! = a
  exact getElem!_replicate m a j.toNat hd

theorem forIn'_loop_const {ε σ' τ : Type} {β : Type}
    (range : IntRange)
    (f : (i : Int) → i ∈ range → β → ExceptT τ (EStateM ε σ') (ForInStep β))
    (b : β) (i : Int) (hs : (i - range.start) % range.step = 0)
    (σ : σ')
    (hbody : ∀ (j : Int) (hj : j ∈ range) (c : β),
      f j hj c σ = .ok (.ok (.yield c)) σ) :
    IntRange.forIn'.loop range f b i hs σ = .ok (.ok b) σ := by
  induction b, i, hs using IntRange.forIn'.loop.induct range with
  | case1 b i hs hmem ih =>
    rw [IntRange.forIn'.loop.eq_1]
    simp only [hmem, dif_pos, bind, ExceptT.bind, ExceptT.mk, EStateM.bind]
    rw [show (f i hmem b) σ = EStateM.Result.ok (Except.ok (ForInStep.yield b)) σ
          from hbody i hmem b]
    exact ih b
  | case2 b i hs hmem =>
    rw [IntRange.forIn'.loop.eq_1]
    simp only [hmem, dif_neg, not_false_iff]
    rfl

theorem forIn'_const {ε σ' τ : Type} {β : Type}
    (range : IntRange) (b : β)
    (f : (i : Int) → i ∈ range → β → ExceptT τ (EStateM ε σ') (ForInStep β))
    (σ : σ')
    (hbody : ∀ (j : Int) (hj : j ∈ range) (c : β),
      f j hj c σ = .ok (.ok (.yield c)) σ) :
    IntRange.forIn' range b f σ = .ok (.ok b) σ :=
  forIn'_loop_const range f b range.start (by simp) σ hbody

theorem pmpMatchAddr_off (addr : physaddr) (width : BitVec 64)
    (pmpaddr prev : BitVec 64)
    (σ : SequentialState RegisterType trivialChoiceSource) :
    (pmpMatchAddr addr width 0#8 pmpaddr prev) σ = .ok pmpAddrMatch.PMP_NoMatch σ := by
  cases addr with
  | Physaddr a =>
  simp only [pmpMatchAddr]
  simp_all [simp_sail, pure, EStateM.pure,
    _get_Pmpcfg_ent_A, pmpAddrMatchType_encdec_backwards]

theorem pmpReadAddrReg_reset (σ : SequentialState RegisterType trivialChoiceSource) (n : Nat)
    (v : RegisterType Register.pmpaddr_n)
    (hcfg : σ.regs.get? Register.pmpcfg_n =
      some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some v) :
    (pmpReadAddrReg n) σ = .ok (v[n]!) σ := by
  simp only [pmpReadAddrReg, sys_pmp_grain]
  simp_all only [simp_sail, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, _get_Pmpcfg_ent_A,
    getElem!_replicate 64 (0#8) n rfl]
  split <;> rfl

theorem pmp_allows (σ : SequentialState RegisterType trivialChoiceSource)
    (addr : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload)
    (v : RegisterType Register.pmpaddr_n)
    (hcfg : σ.regs.get? Register.pmpcfg_n =
      some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some v) :
    (pmpCheck addr width access Privilege.Machine).run σ = .ok none σ := by
  unfold pmpCheck

  simp only [sys_pmp_count, LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    PreSailME.run, ExceptT.run, PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, forIn, ForIn.forIn, ForIn'.forIn']
  rw [if_neg (by decide)]
  simp only [EStateM.run, EStateM.bind]

  rw [forIn'_const _ () _ σ ?hbody]
  ·
    rfl
  case hbody =>
    intro j hj c

    cases c

    split <;>
    · simp only [ExceptT.mk, ExceptT.bindCont, ExceptT.pure, Functor.map,
        EStateM.map, EStateM.bind, EStateM.pure, bind, pure, Bind.bind, Pure.pure,
        simp_sail, get, getThe, MonadStateOf.get, EStateM.get, hcfg,
        pmpReadAddrReg_reset σ _ v hcfg haddr,
        getElem!_replicate_int 64 (0#8) j rfl, pmpMatchAddr_off]

end Vsa.Sim
