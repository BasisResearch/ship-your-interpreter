import VsaIris.Vsa.Stdout.Win
import VsaIris.Vsa.SnpCtx

/-!
# The snprintf stack window

`snpS s dst n` owns the `snpNeed` bytes below the `Nat` stack pointer `s`. `snp_win s n` puts
`Win (snpS s dst k) s n 0` in the context; the addresses `s - K + k` of the snprintf runs are
then keyed by `Win.posK`/`.posKT` (`Stdout/Win.lean`).
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Stdio VsaIris.VsaHeap

/-- The `n` bytes below `s` inside `snpS s dst k`, all premises in one conjunction for `omega`. -/
theorem Win.of_snpS {s dst k n : Nat}
    (h : n ≤ 1024 ∧ 0x8001c168 + n ≤ s ∧ s ≤ 0x88000000 ∧ s % 8 = 0) : Win (snpS s dst k) s n 0 :=
  ⟨⟨⟨fun j hj => .inr (.inl (by unfold snpNeed; omega))⟩, by omega, by omega⟩, by omega,
    .inr (by omega)⟩

/-- A static access inside the stdio footprint (off the impure word) is inside `snpS`. -/
theorem snpS_static {s dst k a w : Nat}
    (h : (decide (0x8001b520 ≤ a ∧ a + w ≤ 0x8001b538) || decide (0x8001b53c ≤ a ∧ a + w ≤ 0x8001b960) ||
      decide (0x8001b978 ≤ a ∧ a + w ≤ 0x8001b990) || decide (0x8001b9b0 ≤ a ∧ a + w ≤ 0x8001ba08) ||
      decide (0x8001ba0c ≤ a ∧ a + w ≤ 0x8001ba18) || decide (0x8001ba68 ≤ a ∧ a + w ≤ 0x8001c168)) = true) :
    ∀ b, b ∈ accAddrs a w → snpS s dst k b := by
  intro b hb
  have hb := mem_accAddrs_iff.mp hb
  have := stdioFoot_rng a w h (b - a) (by omega)
  rw [show a + (b - a) = b by omega] at this
  exact .inl this

macro_rules
  | `(tactic| win_static_own) => `(tactic| (win_foot snpS; exact snpS_static (by decide)))

open Lean Elab Tactic Meta in
/-- `snp_win s n`: put the window of the `n` bytes below the `Nat` stack pointer `s` in the
context as `hw_<s>`, from the run's stack hypotheses (`omega`). -/
elab "snp_win " s:term:max n:term:max : tactic => do
  let S ← goalFoot
  let tag := if s.raw.isIdent then s!"{s.raw.getId}" else "0"
  let others ← ctxWins
  let hw := mkIdent (Name.mkSimple s!"hw_{tag}")
  evalTactic (← `(tactic| have $hw : Win $S $s $n 0 := Win.of_snpS (by omega)))
  winSeps tag s n (← `(0)) others

section Checks

variable (s dst k : Nat) (hw : Win (snpS s dst k) s 1024 0)
include hw

example : StOK (BitVec.ofNat 64 (s - 864 + 584)).toNat 8 := by win_side
example : LdOK (BitVec.ofNat 64 (s - 864)).toNat 8 := by win_side
example : ∀ b ∈ accAddrs (BitVec.ofNat 64 (s - 864 + 584)).toNat 8, snpS s dst k b := by win_side
example : ∀ b ∈ accAddrs 0x8001b898 8, snpS s dst k b := by win_side
example : s - 864 + 584 < 2 ^ 64 := by win_key
example : s - 864 + 584 + widthOfM .ld ≤ s - 864 + 576 ∨ s - 864 + 576 + 8 ≤ s - 864 + 584 := by
  win_key
example : 0x8001b898 + 8 ≤ (BitVec.ofNat 64 (s - 264 + 16)).toNat ∨
    (BitVec.ofNat 64 (s - 264 + 16)).toNat + 2 ≤ 0x8001b898 := by win_key

end Checks

end VsaIris.Sym
