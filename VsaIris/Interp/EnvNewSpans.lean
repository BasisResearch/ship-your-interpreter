import VsaIris.Interp.EnvScanCore

/-!
# `env_new`'s spans, first-order

`env_new` (`0x800029fc`, `env.c:12`) is a prologue, `jal malloc`, and a tail
that either initializes the fresh `Env` and returns or takes the
out-of-memory arm (`0x80002a38`):

* `new_pro` `0x800029fc` → `0x80002a10` (`jal malloc`): spill `s0`/`ra`,
  `s0 := par`, `a0 := 32`;
* `new_ok` `0x80002a14` → return, on a non-NULL block: the `Env` initialized
  (`count = cap = 0`, `names = vals = NULL`, `parent = par`), `s0`/`ra`
  restored;
* `new_null` `0x80002a14` → `0x80002a38` on NULL.
-/

namespace VsaIris.Interp

open VsaIris.Sym VsaIris.MallocFast Vsa.MemRepr Vsa.Sim

/-- `env_new`'s stack frame after its prologue (entry `sp = s`). -/
structure NewStack (s : Nat) (r s0 : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  sp : (R 2).toNat = s - 16
  ra : ldv .ld Mt (s - 8) = r
  s0 : ldv .ld Mt (s - 16) = s0

theorem new_pro {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {s : Nat}
    {R : Nat → BitVec 64} {Mt : Mem}
    (hlo : htifLo + 16 + 16 ≤ s) (hhi : s ≤ 0x100000000) (hal : s % 16 = 0)
    (h2 : (R 2).toNat = s) :
    Span live (fun a => s - 16 ≤ a ∧ a < s) 0x800029fc#64 R Mt
      (fun pc' R' Mt' => pc' = 0x80002a10#64 ∧ NewStack s (R 1) (R 8) R' Mt' ∧
        R' 8 = R 10 ∧ R' 10 = 32#64 ∧ ∀ k, k ≠ 2 → k ≠ 8 → k ≠ 10 → R' k = R k) := by
  intro Q hk
  sx_run hl at 0x80002a10
  refine hk _ _ _ ⟨rfl, ⟨?_, ?_, ?_⟩, ?_, ?_, fun k h2' h8 h10 => ?_⟩
  all_goals (try sx_norm)
  all_goals (try sx_mem)
  · rw [BitVec.toNat_add, h2]; simp only [BitVec.reduceToNat]; omega
  · simp [upd_apply, h2', h8, h10]

/-- The success tail: initialize the `Env` at `p`, restore, return. -/
theorem new_ok {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {s pn : Nat}
    {r s0 : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (hlo : htifLo + 16 + 16 ≤ s) (hhi : s ≤ 0x100000000) (hra : r.toNat % 4 = 0)
    (hstk : NewStack s r s0 R Mt) (hp0 : R 10 ≠ 0#64) (hp : (R 10).toNat = pn)
    (hpw : 0x80000000 ≤ pn ∧ pn + 32 ≤ 0x100000000 ∧ htifLo + 16 ≤ pn ∧ pn % 16 = 0)
    (hsep : pn + 32 ≤ s - 16 ∨ s ≤ pn) :
    Span live (fun a => (s - 16 ≤ a ∧ a < s) ∨ (pn ≤ a ∧ a < pn + 32)) 0x80002a14#64 R Mt
      (fun pc' R' Mt' => pc' = r ∧ R' 10 = R 10 ∧ R' 1 = r ∧ R' 8 = s0 ∧
        R' 2 = BitVec.ofNat 64 s ∧ (∀ k, k ≠ 1 → k ≠ 2 → k ≠ 8 → R' k = R k) ∧
        ldv .ld Mt' pn = 0#64 ∧ ldv .ld Mt' (pn + 8) = 0#64 ∧ ldv .ld Mt' (pn + 16) = 0#64 ∧
        ldv .ld Mt' (pn + 24) = R 8) := by
  intro Q hk
  have hsp := hstk.sp
  have hra' : ldv .ld Mt (R 2 + 8#64).toNat = r := by
    rw [show (R 2 + 8#64).toNat = s - 8 by rw [BitVec.toNat_add, hsp]; simp; omega]
    exact hstk.ra
  have hs0' : ldv .ld Mt (R 2).toNat = s0 := by rw [hsp]; exact hstk.s0
  sx_run hl
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [hra']; exact hra
  have e0 : (R 10).toNat = pn := hp
  have e8 : (R 10 + 8#64).toNat = pn + 8 := by rw [BitVec.toNat_add, hp]; simp; omega
  have e16 : (R 10 + 16#64).toNat = pn + 16 := by rw [BitVec.toNat_add, hp]; simp; omega
  have e24 : (R 10 + 24#64).toNat = pn + 24 := by rw [BitVec.toNat_add, hp]; simp; omega
  refine hk _ _ _ ⟨hra', by simp [upd_apply], ?_, ?_, ?_,
    fun k h1 h2' h8 => by simp [upd_apply, h1, h2', h8], ?_, ?_, ?_, ?_⟩
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hra'
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hs0'
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hsp, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  all_goals rw [e0, e8, e16, e24]
  · rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_hit_eq _ _ rfl]
  · rw [ldv_ld_miss _ _ (by omega), ldv_ld_hit_eq _ _ rfl]
  · rw [ldv_ld_hit_eq _ _ rfl]
  · rw [ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega), ldv_ld_miss _ _ (by omega),
      ldv_ld_hit_eq _ _ rfl]

/-- The NULL branch: on to the out-of-memory arm. -/
theorem new_null {live : Nat → Prop} (hl : ∀ p ∈ envText, live p.1) {S : Nat → Prop}
    {R : Nat → BitVec 64} {Mt : Mem} (hp0 : R 10 = 0#64) :
    Span live S 0x80002a14#64 R Mt (fun pc' R' Mt' => pc' = 0x80002a38#64 ∧ R' = R ∧ Mt' = Mt) := by
  intro Q hk
  sx_run hl at 0x80002a38
  · intro _; exact hk _ _ _ ⟨rfl, rfl, rfl⟩
  · intro h; exact absurd hp0 h

end VsaIris.Interp
