import VsaIris.Interp.HelperRun
import VsaIris.Vsa.Stdout.Attr

/-!
# Store forwarding at every width (lane N1)

newlib's stdio code stores `FILE` fields with `sw`/`sh`/`sb` and reloads
them with `lw`/`lh`/`lhu`/`lbu` (`_putc_r` decrements `_w`, `__swbuf_r` reads
it back; `__swrite` rewrites `_flags`, `_fflush_r` reloads it). `ix_mem`
(`Arm.lean`) forwards doublewords and words through doubleword stores; this
module adds every load kind through a store of any width: the misses
(`ldv_*_miss`: disjoint bytes) and the hits (`ldv_*_hit`: the same address
and width, value the stored value's low bytes, `ofNat` of a `%`, which the
normalizer reduces for literal stores). `nx_mem` is `ix_mem` with them.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-! ## Load values through the little-endian image -/

theorem toNat_append2 (f : Nat → BitVec 8) (a : Nat) :
    (((f (a + 1)).append (f a)) : BitVec (8 * 2)).toNat = imgLE f a 2 := by
  simp only [BitVec.append_eq, BitVec.toNat_append, imgLE]
  have h0 := (f a).isLt; have h1 := (f (a + 1)).isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  omega

theorem bytesAt2 (f : Nat → BitVec 8) (a : Nat) : bytesAt f a 2 = [f a, f (a + 1)] := rfl
theorem bytesAt1 (f : Nat → BitVec 8) (a : Nat) : bytesAt f a 1 = [f a] := by simp [bytesAt]

theorem ldv_lw_img (M : Mem) (a : Nat) :
    ldv .lw M a = sign_extend (m := 64) (BitVec.ofNat 32 (imgLE (imgM M) a 4)) := by
  have hw := toNat_append4 (imgM M) a
  simp only [ldv, bytesAt4, bytesVal, widthOfM, List.getD_cons_zero, List.getD_cons_succ]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := imgLE_lt (imgM M) a 4; omega)]

theorem ldv_lh_img (M : Mem) (a : Nat) :
    ldv .lh M a = sign_extend (m := 64) (BitVec.ofNat 16 (imgLE (imgM M) a 2)) := by
  have hw := toNat_append2 (imgM M) a
  simp only [ldv, bytesAt2, bytesVal, widthOfM, List.getD_cons_zero, List.getD_cons_succ]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := imgLE_lt (imgM M) a 2; omega)]

theorem ldv_lhu_img (M : Mem) (a : Nat) :
    ldv .lhu M a = BitVec.ofNat 64 (imgLE (imgM M) a 2) := by
  have hw := toNat_append2 (imgM M) a
  have hk := imgLE_lt (imgM M) a 2
  simp only [ldv, bytesAt2, bytesVal, widthOfM, List.getD_cons_zero, List.getD_cons_succ]
  apply BitVec.eq_of_toNat_eq
  simp only [LeanRV64DExecutable.zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth]
  rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem ldv_lbu_img (M : Mem) (a : Nat) :
    ldv .lbu M a = BitVec.ofNat 64 (imgLE (imgM M) a 1) := by
  have hk := (imgM M a).isLt
  simp only [ldv, bytesAt1, bytesVal, widthOfM, List.getD_cons_zero, imgLE]
  apply BitVec.eq_of_toNat_eq
  simp only [LeanRV64DExecutable.zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mul_zero, Nat.add_zero,
    Nat.mod_eq_of_lt (by omega)]

/-! ## Stores read back -/

theorem imgLE_store2_hit (Mt : Mem) (a : Nat) (v : BitVec 64) :
    imgLE (imgM (writeLog Mt [(a, 2, v)])) a 2 = v.toNat % 2 ^ 16 := by
  simp only [imgLE, imgM, writeLog, List.foldl_cons, List.foldl_nil, applyW]
  rw [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert,
    Std.ExtHashMap.getElem?_insert_self]
  simp only [beq_iff_eq, show ¬ (a + 1 = a) by omega, ite_false, ite_true, Option.getD_some,
    Nat.mul_zero, Nat.add_zero]
  simp only [shData, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.reduceMul, Nat.reducePow]
  have hv := v.isLt
  rw [Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow]
  omega

theorem imgLE_store1_hit (Mt : Mem) (a : Nat) (v : BitVec 64) :
    imgLE (imgM (writeLog Mt [(a, 1, v)])) a 1 = v.toNat % 2 ^ 8 := by
  simp only [imgLE, imgM, writeLog, List.foldl_cons, List.foldl_nil, applyW,
    Std.ExtHashMap.getElem?_insert_self, Option.getD_some, Nat.mul_zero, Nat.add_zero]
  show (BitVec.ofNat 8 v.toNat).toNat = _
  simp [BitVec.toNat_ofNat]

theorem ldv_lw_hit (Mt : Mem) {a b : Nat} (v : BitVec 64) (h : a = b) :
    ldv .lw (writeLog Mt [(b, 4, v)]) a = sign_extend (m := 64) (BitVec.ofNat 32 (v.toNat % 2 ^ 32)) := by
  subst h; rw [ldv_lw_img, imgLE_store4_hit]

theorem ldv_lh_hit (Mt : Mem) {a b : Nat} (v : BitVec 64) (h : a = b) :
    ldv .lh (writeLog Mt [(b, 2, v)]) a = sign_extend (m := 64) (BitVec.ofNat 16 (v.toNat % 2 ^ 16)) := by
  subst h; rw [ldv_lh_img, imgLE_store2_hit]

theorem ldv_lhu_hit (Mt : Mem) {a b : Nat} (v : BitVec 64) (h : a = b) :
    ldv .lhu (writeLog Mt [(b, 2, v)]) a = BitVec.ofNat 64 (v.toNat % 2 ^ 16) := by
  subst h; rw [ldv_lhu_img, imgLE_store2_hit]

theorem ldv_lbu_hit (Mt : Mem) {a b : Nat} (v : BitVec 64) (h : a = b) :
    ldv .lbu (writeLog Mt [(b, 1, v)]) a = BitVec.ofNat 64 (v.toNat % 2 ^ 8) := by
  subst h; rw [ldv_lbu_img, imgLE_store1_hit]

/-! ## Disjoint stores -/

theorem ldv_lh_miss (Mt : Mem) {a b w : Nat} (v : BitVec 64) (h : a + 2 ≤ b ∨ b + w ≤ a) :
    ldv .lh (writeLog Mt [(b, w, v)]) a = ldv .lh Mt a := ldv_store_miss .lh Mt v h
theorem ldv_lhu_miss (Mt : Mem) {a b w : Nat} (v : BitVec 64) (h : a + 2 ≤ b ∨ b + w ≤ a) :
    ldv .lhu (writeLog Mt [(b, w, v)]) a = ldv .lhu Mt a := ldv_store_miss .lhu Mt v h
theorem ldv_lbu_miss (Mt : Mem) {a b w : Nat} (v : BitVec 64) (h : a + 1 ≤ b ∨ b + w ≤ a) :
    ldv .lbu (writeLog Mt [(b, w, v)]) a = ldv .lbu Mt a := ldv_store_miss .lbu Mt v h
theorem ldv_lwu_miss (Mt : Mem) {a b w : Nat} (v : BitVec 64) (h : a + 4 ≤ b ∨ b + w ≤ a) :
    ldv .lwu (writeLog Mt [(b, w, v)]) a = ldv .lwu Mt a := ldv_store_miss .lwu Mt v h

/-! ### Goal-only address arithmetic

`sx_addr` normalizes every hypothesis (`simp … at *`), which dominates a
long run's cost: the context holds the run's facts and summaries. `nx_addr`
rewrites only the goal: `(x + k#64).toNat` becomes `x.toNat + k` or
`x.toNat - (2^64 - k)` (a negative offset), side conditions by `omega` from
the context's bounds; then `omega`. -/

theorem toNat_add_lit {x : BitVec 64} {k : Nat} (h : x.toNat + k < 2 ^ 64) :
    (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : k < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt h]

theorem toNat_add_neg {x : BitVec 64} {k : Nat} (hk : k < 2 ^ 64) (h : 2 ^ 64 ≤ x.toNat + k) :
    (x + BitVec.ofNat 64 k).toNat = x.toNat - (2 ^ 64 - k) := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  have := x.isLt
  omega

syntax "nx_addr" : tactic
macro_rules
  | `(tactic| nx_addr) => `(tactic| ((try simp (disch := omega) only [mem_accAddrs_iff, LdOK, StOK, StOKb, Vsa.Sim.tohostAddr, toNat_add_lit, toNat_add_neg, BitVec.toNat_ofNat,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, and_true, true_and]); first | done | omega))

/-! ## Abstract memory posts

A callee's summary hands its caller a fresh memory `M'` with a frame fact
`MemKeep M M' P`: every byte in `P` is unchanged. Loads whose bytes are all
in `P` forward to the entry memory (`ldv_keep*`), so the caller never sees
the callee's write log. -/

/-- `M'` agrees with `M` on the bytes `P`. -/
structure MemKeep (M M' : Mem) (P : Nat → Prop) : Prop where
  keep : ∀ a, P a → imgM M' a = imgM M a

theorem MemKeep.trans {M M' M'' : Mem} {P Q : Nat → Prop} (h1 : MemKeep M M' P)
    (h2 : MemKeep M' M'' Q) : MemKeep M M'' (fun a => P a ∧ Q a) :=
  ⟨fun a ha => (h2.keep a ha.2).trans (h1.keep a ha.1)⟩

theorem ldv_keep_gen {M M' : Mem} {P : Nat → Prop} (k : MKind) (h : MemKeep M M' P) {a : Nat}
    (hP : ∀ i, i < widthOfM k → P (a + i)) : ldv k M' a = ldv k M a := by
  unfold ldv bytesAt
  congr 1
  refine List.map_congr_left fun j hj => h.keep _ (hP j (List.mem_range.mp hj))

theorem ldv_keep8 {M M' : Mem} {P : Nat → Prop} (h : MemKeep M M' P) {a : Nat}
    (hP : ∀ i, i < 8 → P (a + i)) : ldv .ld M' a = ldv .ld M a := ldv_keep_gen .ld h hP
theorem ldv_keep4 {M M' : Mem} {P : Nat → Prop} (h : MemKeep M M' P) {a : Nat}
    (hP : ∀ i, i < 4 → P (a + i)) : ldv .lw M' a = ldv .lw M a := ldv_keep_gen .lw h hP
theorem ldv_keep4u {M M' : Mem} {P : Nat → Prop} (h : MemKeep M M' P) {a : Nat}
    (hP : ∀ i, i < 4 → P (a + i)) : ldv .lwu M' a = ldv .lwu M a := ldv_keep_gen .lwu h hP
theorem ldv_keep2 {M M' : Mem} {P : Nat → Prop} (h : MemKeep M M' P) {a : Nat}
    (hP : ∀ i, i < 2 → P (a + i)) : ldv .lh M' a = ldv .lh M a := ldv_keep_gen .lh h hP
theorem ldv_keep2u {M M' : Mem} {P : Nat → Prop} (h : MemKeep M M' P) {a : Nat}
    (hP : ∀ i, i < 2 → P (a + i)) : ldv .lhu M' a = ldv .lhu M a := ldv_keep_gen .lhu h hP
theorem ldv_keep1u {M M' : Mem} {P : Nat → Prop} (h : MemKeep M M' P) {a : Nat}
    (hP : ∀ i, i < 1 → P (a + i)) : ldv .lbu M' a = ldv .lbu M a := ldv_keep_gen .lbu h hP

/-- A store that rewrites a field's own bytes leaves them unchanged. -/
theorem imgM_store_restore (M : Mem) {b w : Nat} (v : BitVec 64) (hw : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8)
    (hv : imgLE (imgM M) b w = v.toNat % 2 ^ (8 * w)) {a : Nat} (ha : b ≤ a ∧ a < b + w) :
    imgM (writeLog M [(b, w, v)]) a = imgM M a := by
  have hst : imgLE (imgM (writeLog M [(b, w, v)])) b w = v.toNat % 2 ^ (8 * w) := by
    rcases hw with rfl | rfl | rfl | rfl
    · exact imgLE_store1_hit M b v
    · exact imgLE_store2_hit M b v
    · exact imgLE_store4_hit M b v
    · rw [imgLE_imgM_store]; exact (Nat.mod_eq_of_lt v.isLt).symm
  have e := imgLE_inj (hst.trans hv.symm) (a - b) (by omega)
  rwa [show b + (a - b) = a by omega] at e

/-- Store forwarding through write logs. -/
syntax "nx_mem_log" : tactic
macro_rules
  | `(tactic| nx_mem_log) => `(tactic| simp (disch := nx_addr) only [ldv_store_hit, ldv_ld_hit_eq,
      ldv_ld_miss, ldv_lw_miss, ldv_lw_store8, ldv_lw_hit, ldv_lh_hit, ldv_lhu_hit, ldv_lbu_hit,
      ldv_lh_miss, ldv_lhu_miss, ldv_lbu_miss, ldv_lwu_miss])

/-- Load forwarding through a callee's frame: every `MemKeep` hypothesis of
the context instantiates the `ldv_keep*` rewrites (the frame is not found by
`simp`'s discharger, which does not assign it). -/
syntax "nx_mem_keep" : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| nx_mem_keep) => withMainContext do
    let mut hs : Array Expr := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if (← instantiateMVars d.type).isAppOf ``MemKeep then hs := hs.push d.toExpr
    let mut progress := false
    for h in hs do
      let hx ← Term.exprToSyntax h
      let saved ← saveState
      try
        evalTactic (← `(tactic| simp (disch := (intro i hi; (try simp only [nx_mt] at ⊢); (try dsimp only); nx_addr)) only
          [ldv_keep8 $hx, ldv_keep4 $hx, ldv_keep4u $hx, ldv_keep2 $hx, ldv_keep2u $hx, ldv_keep1u $hx]))
        progress := true
      catch _ => saved.restore
    unless progress do throwError "nx_mem_keep: no progress"

/-- Store forwarding at every width, for stdio runs. -/
syntax "nx_mem" : tactic
macro_rules
  | `(tactic| nx_mem) => `(tactic| first
      | (nx_mem_log; (try nx_mem_keep); (try nx_mem_log))
      | (nx_mem_keep; (try nx_mem_log)))

end VsaIris.Sym
