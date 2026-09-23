import VsaIris.Adequacy

/-!
# Smoke test: the whole chain on a toy machine

A machine whose only state is register `a0`, counting down: a nonzero `a0`
decrements, zero exits with code 0 and output "done". The loop's total WP is
proved by ordinary Lean induction on the count (how a terminating loop or a
recursion over a derivation is handled without Löb), through the footprint
step rule, and adequacy turns it into `Halts`. This checks that the adequacy
hypothesis is satisfiable and that nothing in the stack is vacuous.
-/

namespace VsaIris.Example

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

abbrev countdown : MachineModel where
  State := BitVec 64
  step σ := if σ = 0#64 then .halt 0 "done" else .next (σ - 1#64)
  reg σ k := if k = a0 then σ else 0#64
  mem _ _ := 0

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem countdown_twp (n : Nat) (hn : n < 2 ^ 64) :
    ⊢@{IProp GF} (a0 ↦ᵣ BitVec.ofNat 64 n) -∗
      mTWP countdown (fun v => iprop(⌜v = (0, "done")⌝)) := by
  induction n with
  | zero =>
    iintro Ha
    iapply wp_exec_halt
    unfold mstateInterp
    iintro %σ ⟨Hr, Hm⟩
    ihave %hσ := reg_valid $$ Hr Ha
    have h0 : σ = 0#64 := by simpa [countdown] using hσ
    imodintro
    isplitr
    · ipureintro; exact ⟨0, "done", by simp [countdown, h0]⟩
    iintro %e %out %h
    simp [countdown, h0] at h
    obtain ⟨rfl, rfl⟩ := h
    imodintro
    iframe Hr Hm
    ipureintro; rfl
  | succ n ih =>
    iintro Ha
    iapply wp_local_step [] [] [(a0, BitVec.ofNat 64 (n + 1), BitVec.ofNat 64 n)] []
    · intro σ ⟨_, _, hrw, _⟩
      have hσ : σ = BitVec.ofNat 64 (n + 1) := by
        simpa [countdown] using hrw _ List.mem_cons_self
      have hne : σ ≠ 0#64 := by
        rw [hσ]; intro h
        have := congrArg BitVec.toNat h
        simp [Nat.mod_eq_of_lt hn] at this
      refine ⟨σ - 1#64, by simp [countdown, hne], ?_, ?_, ?_, ?_⟩
      · intro p hp
        simp at hp; subst hp
        simp [countdown, hσ]
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_sub, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (Nat.lt_of_succ_lt hn)]
        omega
      · intro k hk
        simp at hk
        simp [Ne.symm hk]
      · intro p hp; cases hp
      · intro k _; rfl
    unfold footPre footPost
    simp only [sepL_cons, sepL_nil]
    isplitl [Ha]
    · iframe Ha
    iintro ⟨-, -, ⟨Ha, -⟩, -⟩
    iapply ih (Nat.lt_of_succ_lt hn) $$ Ha

end

/-- Adequacy on the toy machine: from any count, it halts with exit 0. -/
theorem countdown_halts (n : Nat) (hn : n < 2 ^ 64) :
    Halts countdown (BitVec.ofNat 64 n) 0 "done" := by
  have hr : RegAgree countdown
      (PartialMap.insert (∅ : NatMap (BitVec 64)) a0 (BitVec.ofNat 64 n))
      (BitVec.ofNat 64 n) := by
    intro k v hk
    by_cases h : a0 = k
    · subst h
      rw [LawfulPartialMap.get?_insert_eq rfl] at hk
      cases hk; simp
    · rw [LawfulPartialMap.get?_insert_ne h, LawfulPartialMap.get?_empty] at hk
      cases hk
  have hm : MemAgree countdown (∅ : NatMap (BitVec 8)) (BitVec.ofNat 64 n) := by
    intro k v hk
    rw [LawfulPartialMap.get?_empty] at hk
    cases hk
  obtain ⟨e, out, hh, hφ⟩ := mach_adequacy (GF := MachGF) (M := countdown)
    (BitVec.ofNat 64 n) _ _ hr hm (fun v => v = (0, "done")) (by
      intro _
      iintro Hr -
      ihave Ha := (BigSepM.bigSepM_insert (LawfulPartialMap.get?_empty _)).1 $$ Hr
      icases Ha with ⟨Ha, -⟩
      iapply countdown_twp n hn $$ Ha)
  cases hφ
  exact hh

end VsaIris.Example
