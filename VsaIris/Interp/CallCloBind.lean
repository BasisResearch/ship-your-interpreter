import VsaIris.Interp.CallCloRuns

/-!
# The closure call's parameter binding (lane E4)

From `env_new`'s return (`0x800032c0`) to `jal value_null(sp+144)`
(`0x80003328`): `argc` tested, then one `env_define(frame, params[j], &arg_j)`
per argument, the argument copied to `sp+64` first (`CloB_run0`,
`CloB_runL`, `CloB_runR`).

`cloBind` is Wp-generic and abstracts the `env_define` call
(`CloDefineStep`): the total case instantiates it with `ms_callEnvDefine`
(credits `defineCost`), the partial one with `ms_callEnvDefineP` (out of
memory through `wp_oomBlock`). The store advances as the semantics' fold
(`Call.closure`: `(params.zip vs).foldl (·.define frame ·.1 ·.2)`).

* `CloSpills`: the eval prologue's spills and the call arm's (`s3`, `s5`,
  `s7`), which every run of the path keeps.
* `CloPL`: the loop head's state; `CloPD`: the state at `jal value_null`.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Newlib
open Vsa.MemRepr Vsa.Sim Vsa.While

/-- The spilled words the closure path keeps (`[sp+1016, sp+1088)` but
`s4`/`s6`'s slots): the prologue's `ra`, `s0`-`s2` and the arm's `s3`, `s5`,
`s7`. -/
structure CloSpills (Mt : Mem) (s ret : BitVec 64) (rv : Nat → BitVec 64) : Prop where
  saved : CallSaved Mt s ret (rv 8) (rv 9) (rv 18)
  s3 : ldv .ld Mt (s.toNat - 1088 + 1048) = rv 19
  s5 : ldv .ld Mt (s.toNat - 1088 + 1032) = rv 21
  s7 : ldv .ld Mt (s.toNat - 1088 + 1016) = rv 23

/-- The spills survive a memory agreeing on `[sp+1016, sp+1088)`. -/
theorem CloSpills.agree {Mt Mt' : Mem} {s ret : BitVec 64} {rv : Nat → BitVec 64}
    (h : CloSpills Mt s ret rv)
    (hag : ∀ k, s.toNat - 1088 + 1016 ≤ k → k < s.toNat - 1088 + 1088 → imgM Mt' k = imgM Mt k) :
    CloSpills Mt' s ret rv :=
  ⟨⟨(ldv_agree fun j hj => hag _ (by omega) (by omega)).trans h.saved.ra,
    (ldv_agree fun j hj => hag _ (by omega) (by omega)).trans h.saved.s0,
    (ldv_agree fun j hj => hag _ (by omega) (by omega)).trans h.saved.s1,
    (ldv_agree fun j hj => hag _ (by omega) (by omega)).trans h.saved.s2⟩,
   (ldv_agree fun j hj => hag _ (by omega) (by omega)).trans h.s3,
   (ldv_agree fun j hj => hag _ (by omega) (by omega)).trans h.s5,
   (ldv_agree fun j hj => hag _ (by omega) (by omega)).trans h.s7⟩

/-- An element of a represented parameter array. -/
theorem paramsRepr_get {m : Mem} {P : Nat → Prop} :
    ∀ {a n : Nat} {ps : List String}, ParamsReprWithin m P a n ps →
      ∀ j (h : j < ps.length), ∃ p, read64 m (a + 8 * j) = some p ∧ CStringWithin m P p ps[j]
  | _, _, _, .nil, j, h => absurd h (by simp)
  | _, _, _, .cons hp _ hs _, 0, _ => ⟨_, by simpa using hp, hs⟩
  | a, _, _, .cons _ _ _ hrest, j + 1, h => by
    obtain ⟨p, hp, hs⟩ := paramsRepr_get hrest j (by simpa using h)
    exact ⟨p, by rw [show a + 8 * (j + 1) = a + 8 + 8 * j by omega]; exact hp, hs⟩

/-- Every byte of a represented parameter array's pointers is in the view
and present. -/
theorem paramsRepr_covers {m : Mem} {P : Nat → Prop} :
    ∀ {a n : Nat} {ps : List String}, ParamsReprWithin m P a n ps →
      ∀ k, k < 8 * n → P (a + k) ∧ (m[a + k]?).isSome
  | _, _, _, .nil, k, h => absurd h (by omega)
  | a, _, _, .cons hp cp _ hrest, k, h => by
    by_cases hk : k < 8
    · exact ⟨cp k hk, isSome_of_readLE hp hk⟩
    · obtain ⟨h1, h2⟩ := paramsRepr_covers hrest (k - 8) (by omega)
      rw [show a + 8 + (k - 8) = a + k by omega] at h1 h2
      exact ⟨h1, h2⟩

end VsaIris.Interp
