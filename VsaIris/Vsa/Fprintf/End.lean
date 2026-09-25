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
    (hfC : Cover (outS s need) f.toNat (f.toNat + 184)) (hfsp : f.toNat + 184 ≤ sp.toNat ∨ sp.toNat + 592 ≤ f.toNat)
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
  all_goals refine hk _ (by rsimp <;> first | rfl | assumption) (by rsimp <;> first | rfl | assumption) (by rsimp <;> first | rfl | assumption) ?_
  all_goals (intro x hx
             simp only [vfpSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
             rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rsimp <;>
               first | rfl | assumption)

/-! **`vfp_tail`**: `_vfprintf_r`'s end after the flush, `0x8000acbc` → the caller, returning the count. -/
#ix_chain vfp_tail := [vfpTail_1, vfpTail_2]

/-- What the end reads back after the final `__sprint_r`: the count, the
`FILE`'s flags, the spill slots. -/
structure EndRet (Mt M' : Mem) (sp f : BitVec 64) : Prop where
  count : ldv .ld M' (sp + 16#64).toNat = ldv .ld Mt (sp + 16#64).toNat
  flags : ldv .lh M' (f + 16#64).toNat = ldv .lh Mt (f + 16#64).toNat
  flags2 : ldv .lw M' (f + 176#64).toNat = ldv .lw Mt (f + 176#64).toNat
  spills : ∀ k, 488 ≤ k → k + 8 ≤ 592 → ldv .ld M' (sp.toNat + k) = ldv .ld Mt (sp.toNat + k)

theorem VfpSpills.ofEnd {Mt M' : Mem} {sp f : BitVec 64} {C : Nat → BitVec 64} (h : VfpSpills Mt sp C)
    (hE : EndRet Mt M' sp f) (hsp : sp.toNat + 600 < 2 ^ 64) : VfpSpills M' sp C := by
  have eo : ∀ k : Nat, k ≤ 600 → (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := fun k hk => sp_lit (by omega)
  have sp' : ∀ k, 488 ≤ k → k + 8 ≤ 592 → ldv .ld M' (sp + BitVec.ofNat 64 k).toNat =
      ldv .ld Mt (sp + BitVec.ofNat 64 k).toNat := fun k h1 h2 => by
    rw [eo k (by omega)]; exact hE.spills k h1 h2
  exact ⟨(hE.spills 584 (by omega) (by omega)).trans h.ra, (hE.spills 576 (by omega) (by omega)).trans h.s0,
    (sp' 568 (by omega) (by omega)).trans h.s1, (sp' 560 (by omega) (by omega)).trans h.s2,
    (sp' 552 (by omega) (by omega)).trans h.s3, (hE.spills 544 (by omega) (by omega)).trans h.s4,
    (sp' 536 (by omega) (by omega)).trans h.s5, (hE.spills 528 (by omega) (by omega)).trans h.s6,
    (sp' 520 (by omega) (by omega)).trans h.s7, (sp' 512 (by omega) (by omega)).trans h.s8,
    (sp' 504 (by omega) (by omega)).trans h.s9, (sp' 496 (by omega) (by omega)).trans h.s10,
    (sp' 488 (by omega) (by omega)).trans h.s11⟩

/-- **`_vfprintf_r`'s end with nothing pending**: no flush. -/
theorem vfp_end0 {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem}
    {R C : Nat → BitVec 64} {s sp reent f fl : BitVec 64} {need cnt : Nat} {iovs : List (Nat × List (BitVec 8))}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hf1 : 0x8001ad10 ≤ f.toNat) (hf2 : f.toNat + 184 ≤ 0x88000000) (hfa : f.toNat % 8 = 0)
    (hfC : Cover (outS s need) f.toNat (f.toNat + 184)) (hfsp : f.toNat + 184 ≤ sp.toNat ∨ sp.toNat + 592 ≤ f.toNat)
    (hP : VfpPend R Mt sp reent f cnt iovs) (hE : EndFile Mt f fl) (hS : VfpSpills Mt sp C)
    (hra : (C 1).toNat % 4 = 0)
    (h0 : piecesLen iovs = 0)
    (hk0 : ∀ R' : Nat → BitVec 64, R' 10 = BitVec.ofNat 64 cnt → R' 2 = sp + 592#64 →
      R' 1 = C 1 → (∀ x ∈ vfpSaved, R' x = C x) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t (C 1) R'
        (writeLog Mt [((sp + 232#64).toNat, 4, 0#64)])) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000aca8#64 R Mt := by
  have h2 := hP.spR; have hre := hP.reent; have hfi := hP.file; have hres := hP.resid
  rw [h0] at hres
  nx_run hlive using [h2, hre, hfi, hres] at 2147527868
  refine vfp_tail hlive hs1 hs2 hs3 hs4 hal hf1 hf2 hfa hfC hfsp ?_ ?_ hE hP.count hS hra hk0
  · rsimp; exact h2
  · rsimp

/-! **`vfp_end1`**: `_vfprintf_r`'s end with pieces pending: the final flush (the hook `hSh`,
returning to `0x8000cfac`), then `vfp_tail`. -/
#ix_piece vfp_end1 {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) {Post : List (BitVec 8) → Mem → Prop} {t : String} {Mt : Mem}
    {R C : Nat → BitVec 64} {s sp reent f fl : BitVec 64} {need cnt : Nat} {iovs : List (Nat × List (BitVec 8))}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hf1 : 0x8001ad10 ≤ f.toNat) (hf2 : f.toNat + 184 ≤ 0x88000000) (hfa : f.toNat % 8 = 0)
    (hfC : Cover (outS s need) f.toNat (f.toNat + 184)) (hfsp : f.toNat + 184 ≤ sp.toNat ∨ sp.toNat + 592 ≤ f.toNat)
    (hP : VfpPend R Mt sp reent f cnt iovs) (hE : EndFile Mt f fl) (hS : VfpSpills Mt sp C)
    (hra : (C 1).toNat % 4 = 0)
    (hpl : piecesLen iovs < 2 ^ 31) (h0 : piecesLen iovs ≠ 0)
    (hSh : ∀ R0 : Nat → BitVec 64, R0 2 = sp → R0 10 = reent → R0 11 = f → R0 12 = sp + 224#64 →
      R0 1 = 0x8000cfac#64 → (∀ R' M' out, RetOK R0 R' 0#64 → Post out M' →
        SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs out) 0x8000cfac#64 R' M') →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000e8cc#64 R0 Mt)
    (hPR : ∀ out M', Post out M' → EndRet Mt M' sp f)
    (hk1 : ∀ out M', Post out M' → ∀ R' : Nat → BitVec 64, R' 10 = BitVec.ofNat 64 cnt → R' 2 = sp + 592#64 →
      R' 1 = C 1 → (∀ x ∈ vfpSaved, R' x = C x) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs out) (C 1) R'
        (writeLog M' [((sp + 232#64).toNat, 4, 0#64)])) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000aca8#64 R Mt by
  have h2 := hP.spR; have hre := hP.reent; have hfi := hP.file; have hres := hP.resid
  have hz1 : (BitVec.ofNat 64 (piecesLen iovs) = 0#64) = False := eq_false fun h => by
    have := congrArg BitVec.toNat h; simp at this; omega
  have hz2 : (BitVec.ofNat 64 (piecesLen iovs) ≠ 0#64) = True := eq_true fun h => by
    have := congrArg BitVec.toNat h; simp at this; omega
  nx_run hlive using [h2, hre, hfi, hres, hz1, hz2] at 2147543244
  refine hSh _ (by rsimp; exact h2) (by rsimp) (by rsimp) (by rsimp) (by rsimp) fun R' M' out hret hpost => ?_
  have H := hPR out M' hpost
  nx_ret hret
  have k2 : R' 2 = sp := by rw [rk2]; rsimp <;> exact h2
  have k20 : R' 20 = f := by rw [rk20]; try rsimp
  rsimp
  nx_run hlive using [k2, k20, rk10] at 2147527868
  have hE' : EndFile M' f fl := ⟨H.flags.trans hE.flags, H.flags2.trans hE.flags2, hE.snpt, hE.serr⟩
  refine vfp_tail hlive hs1 hs2 hs3 hs4 hal hf1 hf2 hfa hfC hfsp ?_ ?_ hE' (H.count.trans hP.count)
    (hS.ofEnd H (by omega)) hra (hk1 out M' hpost)
  · rsimp; exact k2
  · rsimp; exact k20

/-- **`_vfprintf_r`'s end** from the format's NUL (`0x8000aca8`) to the caller. -/
theorem vfp_end {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) {Post : List (BitVec 8) → Mem → Prop} {t : String} {Mt : Mem}
    {R C : Nat → BitVec 64} {s sp reent f fl : BitVec 64} {need cnt : Nat} {iovs : List (Nat × List (BitVec 8))}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hf1 : 0x8001ad10 ≤ f.toNat) (hf2 : f.toNat + 184 ≤ 0x88000000) (hfa : f.toNat % 8 = 0)
    (hfC : Cover (outS s need) f.toNat (f.toNat + 184)) (hfsp : f.toNat + 184 ≤ sp.toNat ∨ sp.toNat + 592 ≤ f.toNat)
    (hP : VfpPend R Mt sp reent f cnt iovs) (hE : EndFile Mt f fl) (hS : VfpSpills Mt sp C)
    (hra : (C 1).toNat % 4 = 0)
    (hpl : piecesLen iovs < 2 ^ 31)
    (hSh : ∀ R0 : Nat → BitVec 64, R0 2 = sp → R0 10 = reent → R0 11 = f → R0 12 = sp + 224#64 →
      R0 1 = 0x8000cfac#64 → (∀ R' M' out, RetOK R0 R' 0#64 → Post out M' →
        SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs out) 0x8000cfac#64 R' M') →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000e8cc#64 R0 Mt)
    (hPR : ∀ out M', Post out M' → EndRet Mt M' sp f)
    (hk0 : piecesLen iovs = 0 → ∀ R' : Nat → BitVec 64, R' 10 = BitVec.ofNat 64 cnt → R' 2 = sp + 592#64 →
      R' 1 = C 1 → (∀ x ∈ vfpSaved, R' x = C x) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t (C 1) R'
        (writeLog Mt [((sp + 232#64).toNat, 4, 0#64)]))
    (hk1 : ∀ out M', Post out M' → ∀ R' : Nat → BitVec 64, R' 10 = BitVec.ofNat 64 cnt → R' 2 = sp + 592#64 →
      R' 1 = C 1 → (∀ x ∈ vfpSaved, R' x = C x) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs out) (C 1) R'
        (writeLog M' [((sp + 232#64).toNat, 4, 0#64)])) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000aca8#64 R Mt := by
  by_cases h0 : piecesLen iovs = 0
  · exact vfp_end0 hlive hs1 hs2 hs3 hs4 hal hf1 hf2 hfa hfC hfsp hP hE hS hra h0 (hk0 h0)
  · exact vfp_end1 hlive hs1 hs2 hs3 hs4 hal hf1 hf2 hfa hfC hfsp hP hE hS hra hpl h0 hSh hPR hk1

theorem SbOut.endRet {Mt M' : Mem} {sp f : BitVec 64} {pend0 pend' : List (BitVec 8)}
    {iovs : List (Nat × List (BitVec 8))} {out : List (BitVec 8)} (h : SbOut Mt M' sp f pend0 pend' iovs out)
    (hF : SbFile Mt f pend0) (hsp : 0x80100000 ≤ sp.toNat) (hsp2 : sp.toNat + 600 < 2 ^ 64)
    (hf : sp.toNat + 592 ≤ f.toNat) : EndRet Mt M' sp f := by
  have eo : ∀ k : Nat, k ≤ 600 → (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := fun k hk =>
    sp_lit (by omega)
  refine ⟨?_, h.file.flags.trans hF.flags.symm, h.file.flags2.trans hF.flags2.symm, fun k h1 h2 =>
    h.frame.ldv .ld fun j hj => SbOut.notReg hsp2 _ (by omega) (by simp [widthOfM] at hj; omega)
      (by simp [widthOfM] at hj; omega) (by omega)⟩
  rw [eo 16 (by omega)]
  exact h.frame.ldv .ld fun j hj => SbOut.notReg hsp2 _ (by omega) (by simp [widthOfM] at hj; omega)
    (by simp [widthOfM] at hj; omega) (by omega)

end VsaIris.Sym.Fp
