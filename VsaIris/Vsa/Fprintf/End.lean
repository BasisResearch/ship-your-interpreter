import VsaIris.Vsa.Fprintf.SConv

/-!
# `_vfprintf_r`'s end (lane N5, shared with N3)

At the format's NUL (`0x8000aca8`) `_vfprintf_r` flushes the pending iovs
through `__sprint_r` if any (`0x8000cf9c`), clears the iov count, releases
the `FILE`'s lock (`__retarget_lock_release_recursive`, a stub, taken when
`_flags2 & 1 = 0` and `flags & __SNPT = 0`), checks `__SERR`, and returns
the count (`vfp_tail`, from `0x8000acbc`). The `FILE`'s flags are a
parameter: `0x2008` for `__sbprintf`'s stack `FILE`, `0x201a` for `stderr`.
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

local macro_rules | `(tactic| sx_side) => `(tactic| closed_decide)

/-- The `FILE` fields the end reads: flags `fl` (no `__SNPT`, no
`__SERR`), `_flags2` clear. -/
structure EndFile (M : Mem) (f fl : BitVec 64) : Prop where
  flags : ldv .lh M (f + 16#64).toNat = fl
  flags2 : ldv .lw M (f + 176#64).toNat = 0#64
  snpt : fl &&& 512#64 = 0#64
  serr : fl &&& 64#64 = 0#64

/-- The callee-saved registers `_vfprintf_r` restores. -/
abbrev vfpSaved : List Nat := [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

#ix_piece vfpTail_1 {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem} {R C : Nat → BitVec 64}
    {s sp f fl : BitVec 64} {need cnt : Nat}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hf1 : 0x8001ad10 ≤ f.toNat) (hf2 : f.toNat + 184 ≤ 0x88000000) (hfa : f.toNat % 8 = 0)
    (hfC : Cover (outS s need) f.toNat (f.toNat + 184))
    (h2 : R 2 = sp) (h20 : R 20 = f) (hE : EndFile Mt f fl)
    (hc : ldv .ld Mt (sp + 16#64).toNat = BitVec.ofNat 64 cnt) (hS : VfpSpills Mt sp C)
    (hra : (C 1).toNat % 4 = 0)
    (hk : ∀ R' : Nat → BitVec 64, R' 10 = BitVec.ofNat 64 cnt → R' 2 = sp + 592#64 → R' 1 = C 1 →
      (∀ x ∈ vfpSaved, R' x = C x) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t (C 1) R'
        (writeLog Mt [((sp + 232#64).toNat, 4, 0#64)])) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000acbc#64 R Mt by
  have eo : ∀ k : Nat, k ≤ 600 → (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := fun k hk => sp_lit (by omega)
  have h1 : ldv .ld Mt (sp + 584#64).toNat = C 1 := by rw [eo 584 (by omega)]; exact hS.ra
  have h8 : ldv .ld Mt (sp + 576#64).toNat = C 8 := by rw [eo 576 (by omega)]; exact hS.s0
  have h20' : ldv .ld Mt (sp + 544#64).toNat = C 20 := by rw [eo 544 (by omega)]; exact hS.s4
  have h22 : ldv .ld Mt (sp + 528#64).toNat = C 22 := by rw [eo 528 (by omega)]; exact hS.s6
  have h9 := hS.s1; have h18 := hS.s2; have h19 := hS.s3
  have h21 := hS.s5; have h23 := hS.s7; have h24 := hS.s8; have h25 := hS.s9; have h26 := hS.s10
  have h27 := hS.s11
  have hfl := hE.flags; have hfl2 := hE.flags2; have h512 := hE.snpt; have h64 := hE.serr
  nf_go 1 [14] hlive using [h2, h20, hfl, hfl2, hc, h1, h8, h9, h18, h19, h20', h21, h22, h23, h24, h25, h26, h27,
    h512, h64, BitVec.add_assoc] at 2147483648

#ix_piece vfpTail_2 from vfpTail_1 by
  nf_go 2 [14] hlive using [h2, h20, hfl, hfl2, hc, h1, h8, h9, h18, h19, h20', h21, h22, h23, h24, h25, h26, h27,
    h512, h64, BitVec.add_assoc] at 2147483648
  all_goals refine hk _ (by rsimp) (by rsimp; first | rfl | (rw [f2]; exact h2 ▸ rfl) | skip) (by rsimp) ?_
  all_goals (intro x hx
             simp only [vfpSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
             rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rsimp <;>
               first | rfl | assumption)

/-! **`vfp_tail`**: `_vfprintf_r`'s end after the flush, `0x8000acbc` → the caller, returning the count. -/
#ix_chain vfp_tail := [vfpTail_1, vfpTail_2]

end VsaIris.Sym.Fp
