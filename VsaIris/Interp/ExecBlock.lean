import VsaIris.Interp.ExecEnv
import VsaIris.Interp.SeqLoop

/-!
# `exec_stmt`'s block arm: runs and node facts (lane E5)

`0x8000418c`: `mv a0,s3; jal env_new` (`0x80004190`), then `lw a5,16(s0)` (the
count), `mv s3,a0` (the new frame), `li a6,0`, `blez a5` to the shared exit
(`0x80004090`: `li a0,0`) or on to the statement loop's head `0x800041a4`
(lane G's `blockSeqT_body`/`blockSeqP_body`).
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

#ix_seg BlockArm_run1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s : BitVec 64}
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 20 ≤ 0x100000000)
    (hx3 : aS.toNat + 20 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (h16 : R 16 = 8#64) (h14 : R 14 = 0x80019fb8#64)
    (hk : ldv .lw m aS.toNat = 2#64) (hku : ldv .lwu m aS.toNat = 2#64) :
    IW live m (stmtView aS.toNat 20) (InExt (s.toNat - 176, 176)) Q 0x80004014#64 R Mt
  by rw [← upd_eq_self h16]
     ix_run hlive using [h8, h14, hk, hku] at 0x80004190

#ix_seg BlockArm_runE {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s : BitVec 64}
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 20 ≤ 0x100000000)
    (hx3 : aS.toNat + 20 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (hc : ldv .lw m (aS + 16#64).toNat = 0#64) :
    IW live m (stmtView aS.toNat 20) (InExt (s.toNat - 176, 176)) Q 0x80004194#64 R Mt
  by ix_run hlive using [h8, hc] at 0x8000409c

#ix_seg BlockArm_runL {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s : BitVec 64} {count : Nat}
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 20 ≤ 0x100000000)
    (hx3 : aS.toNat + 20 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (hc : ldv .lw m (aS + 16#64).toNat = BitVec.ofNat 64 count) :
    IW live m (stmtView aS.toNat 20) (InExt (s.toNat - 176, 176)) Q 0x80004194#64 R Mt
  by ix_run hlive using [h8, hc] at 0x800041a4 0x80004090

/-- Every byte of a represented statement array is read-covered and present. -/
theorem stmtArray_cover {m : Mem} {P : Nat → Prop} :
    ∀ {a n : Nat} {ss : List Vsa.While.Stmt}, StmtArrayReprWithin m P a n ss →
      ∀ j, j < 8 * n → P (a + j) ∧ (m[a + j]?).isSome
  | _, _, _, .nil, j, h => absurd h (by omega)
  | a, _, _, .cons hp cp _ hrest, j, h => by
    by_cases hj : j < 8
    · exact ⟨cp j hj, isSome_of_readLE hp hj⟩
    · have := stmtArray_cover hrest (j - 8) (by omega)
      rwa [show a + 8 + (j - 8) = a + j by omega] at this

/-- A nonempty block node over a geometric view: G's `BlockNode` (the loop's
node facts) and the count. -/
theorem blockNode_of {m : Mem} {P : Nat → Prop} {aS : BitVec 64} {ss : List Vsa.While.Stmt}
    (h : StmtReprWithin m P aS.toNat (.block ss)) (hg : ∀ k, P k → Interp.ReadOK k) :
    ∃ arr count, StmtNode m P aS 2 20 ∧
      ldv .lw m (aS + 16#64).toNat = BitVec.ofNat 64 count ∧ ss.length = count ∧
      (0 < count → BlockNode m P aS (BitVec.ofNat 64 arr) count ss) := by
  cases h with
  | block h0 c0 ha ca hc cc hss =>
    rename_i arr count
    have hn := stmtNode_of (w := 20) hg h0 c0 (by decide) (Or.inr (by decide)) (fun j h1 h2 => by
      by_cases j1 : j < 16
      · exact field_mid ha ca h1 (by omega)
      · exact field_mid hc cc (by omega) (by omega))
    have g19 := (hg _ (cc 3 (by decide))).win
    have hlen := stmtArray_length hss
    have hal := readLE_lt ha
    have hat : (BitVec.ofNat 64 arr).toNat = arr := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hal]
    have hcl := readLE_lt hc
    have e16 : (aS + 16#64).toNat = aS.toNat + 16 := by
      have := hn.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hsmall : count < 2 ^ 31 := by
      rcases Nat.eq_zero_or_pos count with h | h
      · omega
      · have gl := hg _ (stmtArray_cover hss (8 * count - 1) (by omega)).1
        have g0 := hg _ (stmtArray_cover hss 0 (by omega)).1
        have := gl.hi; have := g0.lo; omega
    refine ⟨arr, count, hn, by rw [e16]; exact ldv_lw_read32 hc hsmall, hlen, fun hpos => ?_⟩
    have gl := hg _ (stmtArray_cover hss (8 * count - 1) (by omega)).1
    have g0 := hg _ (stmtArray_cover hss 0 (by omega)).1
    have e8 : (aS + 8#64).toNat = aS.toNat + 8 := by
      have := hn.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    refine ⟨by rw [e8]; exact ldv_ld_read64 ha, by rw [e16]; exact ldv_lw_read32 hc hsmall,
      hn.lo, by have := g19.1; omega, ?_, by rw [hat]; simpa using g0.lo,
      by rw [hat]; have := gl.hi; omega, ?_, hsmall, by rw [hat]; exact hss, hg, ?_⟩
    · have h1 := g19.2; have h0 := hn.off
      unfold Vsa.Sim.tohostAddr at *
      omega
    · rw [hat]
      have h0 := g0.off; have h1 := gl.off
      simp only [Nat.add_zero] at h0
      unfold Vsa.Sim.tohostAddr at *
      rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
      · left; omega
      · exfalso
        have := (hg _ (stmtArray_cover hss (2147593472 + 15 - arr) (by omega)).1).off
        unfold Vsa.Sim.tohostAddr at this; omega
      · omega
      · right; omega
    · intro a ha'
      simp only [List.mem_append, mem_accAddrs_iff] at ha'
      rcases ha' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨j, rfl⟩ : ∃ j, a = aS.toNat + j := ⟨a - aS.toNat, by omega⟩
        by_cases j1 : j < 16
        · exact field_mid ha ca (by omega) (by omega)
        · exact field_mid hc cc (by omega) (by omega)
      · rw [hat] at h1 h2
        obtain ⟨j, rfl⟩ : ∃ j, a = arr + j := ⟨a - arr, by omega⟩
        exact stmtArray_cover hss j (by omega)

end VsaIris.Interp
