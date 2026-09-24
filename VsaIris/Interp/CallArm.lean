import VsaIris.Interp.SpecLoop
import VsaIris.Interp.CallJalr

/-!
# `eval_expr`'s call arm: the shared layer (lane E4)

`interp.c:248-256` (`EX_CALL`, `call_value` inlined), `eval_expr`
`0x800031b0`..`0x80003404`:

```
800031b0  ld a2,8(a2); addi a0,sp,96; sd a3,0(sp)
800031bc  jal eval_expr                     -- the callee, into sp+96
800031c0  lw a5,24(s0); li a4,32
800031c8  blt a4,a5,80003fb0                -- too many arguments (runtime_error)
800031cc  sd s7,1016(sp); ld a3,0(sp); li a6,0
800031d8  blez a5,80003254                  -- no arguments
800031dc  … the argument loop (E6: evalArgsT_body) … 80003250
80003254  copy the callee to sp+120; lw a1,4(s0) (line); kind dispatch:
          5 (native) → 800039e0, 4 (closure) → 80003288, else → 80003da4
800039e0  marshal a0..a4; 800039f4 jalr a6 (the native); ld s7; j epilogue
```

This file: the node's facts (`CallNode`, from the representation), the
symbolic runs every call row shares, and the stack arithmetic.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While

/-- The bytes of a call node its runs read: the tag, the callee and argument
pointers and the count (not the line field at `+4`). -/
abbrev callView (a : Nat) : List Nat := accAddrs a 4 ++ accAddrs (a + 8) 20

/-- What a call node gives the runs: its word reads at the node's register
value, its view and its placement. -/
structure CallNode (m : Mem) (P : Nat → Prop) (aX aF : BitVec 64) (argc : Nat) : Prop where
  kind : ldv .lw m aX.toNat = 9#64
  kindu : ldv .lwu m aX.toNat = 9#64
  callee : ldv .ld m (aX + 8#64).toNat = aF
  cnt : ldv .lw m (aX + 24#64).toNat = BitVec.ofNat 64 argc
  small : argc < 2 ^ 31
  lo : 0x80000000 ≤ aX.toNat
  hi : aX.toNat + 28 ≤ 0x100000000
  off : aX.toNat + 28 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat
  view : ∀ a ∈ callView aX.toNat, P a ∧ (m[a]?).isSome

theorem exprArray_length {m : Mem} {P : Nat → Prop} :
    ∀ {a n : Nat} {es : List Expr}, ExprArrayReprWithin m P a n es → es.length = n
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ _ _ hrest => by simp [exprArray_length hrest]

/-- A call node's facts, from its representation over a geometric view. -/
theorem callNode_of_repr {m : Mem} {P : Nat → Prop} {aX : BitVec 64} {f : Expr} {args : List Expr}
    (h : ExprReprWithin m P aX.toNat (.call f args)) (hg : ∀ k, P k → ReadOK k) :
    ∃ aF : Nat, CallNode m P aX (BitVec.ofNat 64 aF) args.length ∧
      ExprReprWithin m P aF f ∧ aF < 2 ^ 64 := by
  cases h with
  | call hk ck hf cf hrf harr carr hargc cargc hsmall hes =>
    rename_i aF arr argc
    have hlen : args.length = argc := by
      exact exprArray_length hes
    subst hlen
    have g0 := hg _ (ck 0 (by omega)); have g3 := hg _ (ck 3 (by omega))
    have g8 := hg _ (cf 0 (by omega)); have g27 := hg _ (cargc 3 (by omega))
    have e8 : (aX + 8#64).toNat = aX.toNat + 8 := by
      have := g27.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have e24 : (aX + 24#64).toNat = aX.toNat + 24 := by
      have := g27.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    refine ⟨aF, ⟨?_, ?_, ?_, ?_, hsmall, g0.lo, ?_, ?_, ?_⟩, hrf, readLE_lt hf⟩
    · exact ldv_lw_read32 hk (by decide)
    · exact ldv_lwu_read32 hk
    · rw [e8]; exact ldv_ld_read64 hf
    · rw [e24]; exact ldv_lw_read32 hargc hsmall
    · have := g27.hi; omega
    · have h0 := g0.off; have h3 := g3.off; have h8' := g8.off; have h27 := g27.off
      have h15 := (hg _ (cf 7 (by omega))).off; have h16 := (hg _ (carr 0 (by omega))).off
      have h23 := (hg _ (carr 7 (by omega))).off; have h24 := (hg _ (cargc 0 (by omega))).off
      simp only [Nat.add_zero] at h0 h8' h16 h24; omega
    · intro a ha
      simp only [List.mem_append, mem_accAddrs_iff] at ha
      rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨j, rfl⟩ : ∃ j, a = aX.toNat + j := ⟨a - aX.toNat, by omega⟩
        exact ⟨ck j (by omega), isSome_of_readLE hk (by omega)⟩
      · by_cases hj : a < aX.toNat + 16
        · obtain ⟨j, rfl⟩ : ∃ j, a = aX.toNat + 8 + j := ⟨a - (aX.toNat + 8), by omega⟩
          exact ⟨cf j (by omega), isSome_of_readLE hf (by omega)⟩
        · by_cases hj' : a < aX.toNat + 24
          · obtain ⟨j, rfl⟩ : ∃ j, a = aX.toNat + 16 + j := ⟨a - (aX.toNat + 16), by omega⟩
            exact ⟨carr j (by omega), isSome_of_readLE harr (by omega)⟩
          · obtain ⟨j, rfl⟩ : ∃ j, a = aX.toNat + 24 + j := ⟨a - (aX.toNat + 24), by omega⟩
            exact ⟨cargc j (by omega), isSome_of_readLE hargc (by omega)⟩

/-! ## The shared runs -/

-- Run 1: prologue, kind dispatch, stage the callee (`a2 = e->callee`,
-- `a0 = sp+96`, `a3` spilled at `sp+0`).
#ix_seg Call_run1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s aE inp sret aF : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 28 ≤ 0x100000000)
    (hx3 : aX.toNat + 28 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h10 : R 10 = sret) (h11 : R 11 = inp) (h12 : R 12 = aX) (h13 : R 13 = aE) (h2 : R 2 = s)
    (hk9 : ldv .lw m aX.toNat = 9#64) (hk9u : ldv .lwu m aX.toNat = 9#64)
    (hcallee : ldv .ld m (aX + 8#64).toNat = aF) :
    IW live m (callView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x80003164#64 R Mt
  by ix_run hlive using [h10, h11, h12, h13, h2, hk9, hk9u, hcallee, hsf] at 0x800031bc

-- Run 2: the argument count test (`argc > 32` leaves for the error at
-- `0x80003fb0`), spill `s7`, reload `a3 = env`, `a6 = 0`; `blez` to the
-- dispatch (no arguments) or the loop head.
#ix_seg Call_run2 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s aE : BitVec 64} {argc : Nat}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 28 ≤ 0x100000000)
    (hx3 : aX.toNat + 28 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h8 : R 8 = aX) (h2 : R 2 = s + 18446744073709550528#64)
    (hcnt : ldv .lw m (aX + 24#64).toNat = BitVec.ofNat 64 argc)
    (hA : ldv .ld Mt (s.toNat - 1088) = aE) :
    IW live m (callView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x800031c0#64 R Mt
  by ix_run hlive using [h8, h2, hcnt, hA, hsf] at 0x800031dc 0x80003254 0x80003fb0

end VsaIris.Interp
