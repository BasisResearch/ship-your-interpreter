import Vsa.Elf
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail

/-!
# PMP always allows in Machine mode under the reset configuration

PLAN-InterpSim.md §Layer 0, item 1.

The Sail RV64D model checks physical-memory-protection (PMP) permissions on
every fetch and data access via `pmpCheck`.  With the reset PMP configuration
— all `pmpcfg` entries zero, hence every entry `OFF` (`A = 0b00`) — no entry
matches any address, so in Machine mode `pmpCheck` returns `none` (no
exception) and leaves the machine state untouched.

This file proves that for arbitrary address / width / access, taming the
16-entry PMP walk (`sys_pmp_count = 16`) with a single generic loop lemma
(`forIn'_loop_const`) rather than a 16-fold unfold: the walk is a
state-preserving `IntRange.forIn'.loop` whose body always yields, so the whole
loop collapses to `.ok () σ`.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- `getElem!` on a `Vector.replicate` is the replicated element at *any* index
(out-of-bounds returns the default, which for the reset config is also `0#8`). -/
theorem getElem!_replicate {α : Type} [Inhabited α] (m : Nat) (a : α) (n : Nat)
    (hd : (default : α) = a) : (Vector.replicate m a)[n]! = a := by
  by_cases h : n < m
  · rw [getElem!_pos (Vector.replicate m a) n h, Vector.getElem_replicate]
  · rw [getElem!_neg (Vector.replicate m a) n h]; exact hd

/-- Same, for the Sail `Int`-indexed `GetElem?` instance (`c[i]! = c[i.toNat]!`). -/
theorem getElem!_replicate_int {α : Type} [Inhabited α] (m : Nat) (a : α) (j : Int)
    (hd : (default : α) = a) : (Vector.replicate m a)[j]! = a := by
  show (Vector.replicate m a)[j.toNat]! = a
  exact getElem!_replicate m a j.toNat hd

/-- If the loop body always yields the same accumulator with the state fixed at
`σ` unchanged, the whole `IntRange.forIn'.loop` returns that accumulator with
unchanged state.  This kills the 16-entry PMP walk in one shot. -/
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

/-- Same, phrased for `IntRange.forIn'` (which is `loop` started at `range.start`). -/
theorem forIn'_const {ε σ' τ : Type} {β : Type}
    (range : IntRange) (b : β)
    (f : (i : Int) → i ∈ range → β → ExceptT τ (EStateM ε σ') (ForInStep β))
    (σ : σ')
    (hbody : ∀ (j : Int) (hj : j ∈ range) (c : β),
      f j hj c σ = .ok (.ok (.yield c)) σ) :
    IntRange.forIn' range b f σ = .ok (.ok b) σ :=
  forIn'_loop_const range f b range.start (by simp) σ hbody

/-- `pmpMatchAddr` on an `OFF` (all-zero) config entry is always `PMP_NoMatch`,
in any state, without touching the state. -/
theorem pmpMatchAddr_off (addr : physaddr) (width : BitVec 64)
    (pmpaddr prev : BitVec 64)
    (σ : SequentialState RegisterType trivialChoiceSource) :
    (pmpMatchAddr addr width 0#8 pmpaddr prev) σ = .ok pmpAddrMatch.PMP_NoMatch σ := by
  cases addr with
  | Physaddr a =>
  simp only [pmpMatchAddr]
  simp_all [simp_sail, pure, EStateM.pure,
    _get_Pmpcfg_ent_A, pmpAddrMatchType_encdec_backwards]

/-- `pmpReadAddrReg` under the reset config (grain 0, all-zero `pmpcfg`) just
reads the corresponding `pmpaddr_n` entry and leaves the state untouched. -/
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

/--
**PLAN-InterpSim.md §Layer 0, item 1.**

In Machine mode, under the reset PMP configuration (all `pmpcfg` entries zero),
`pmpCheck` allows every access: it returns `.ok none` and leaves the machine
state unchanged.  `addr`, `width` and `access` are arbitrary.

Register footprint: `pmpcfg_n` (all zero) and `pmpaddr_n` (any value).  The
privilege is supplied as the explicit `Privilege.Machine` argument, so no
`cur_privilege` read is on this path, and `mseccfg` is never consulted here
(the `pmpLocked`/`MML` logic is only reached on a *match*, which never happens).
-/
theorem pmp_allows (σ : SequentialState RegisterType trivialChoiceSource)
    (addr : physaddr) (width : Nat)
    (access : MemoryAccessType mem_payload)
    (v : RegisterType Register.pmpaddr_n)
    (hcfg : σ.regs.get? Register.pmpcfg_n =
      some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some v) :
    (pmpCheck addr width access Privilege.Machine).run σ = .ok none σ := by
  unfold pmpCheck
  -- Peel the SailME.run / ExceptT plumbing, exposing the walk as an
  -- `IntRange.forIn'` in the underlying `EStateM (Error ⊕ Unit) σ`.
  simp only [sys_pmp_count, LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    PreSailME.run, ExceptT.run, PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, forIn, ForIn.forIn, ForIn'.forIn']
  rw [if_neg (by decide)]
  simp only [EStateM.run, EStateM.bind]
  -- The 16-entry walk collapses to `.ok (.ok ()) σ`: every entry is OFF, so the
  -- body yields with unchanged state and no throw.
  rw [forIn'_const _ () _ σ ?hbody]
  · -- Loop done; `priv == Machine`, so `pure none`, state untouched.
    rfl
  case hbody =>
    intro j hj c
    -- The body reads `pmpcfg_n[j]! = 0#8` (OFF) ⇒ `pmpMatchAddr = PMP_NoMatch` ⇒ yield.
    cases c
    -- push the application through the `if`, unfold ExceptT/EStateM plumbing,
    -- and apply the reset facts at σ.  Both branches only differ in `prev_pmpaddr`,
    -- which is irrelevant because the entry is OFF.
    split <;>
    · simp only [ExceptT.mk, ExceptT.bindCont, ExceptT.pure, Functor.map,
        EStateM.map, EStateM.bind, EStateM.pure, bind, pure, Bind.bind, Pure.pure,
        simp_sail, get, getThe, MonadStateOf.get, EStateM.get, hcfg,
        pmpReadAddrReg_reset σ _ v hcfg haddr,
        getElem!_replicate_int 64 (0#8) j rfl, pmpMatchAddr_off]

end Vsa.Sim
