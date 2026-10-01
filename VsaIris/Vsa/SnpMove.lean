import VsaIris.Vsa.SnpCtx
import VsaIris.Interp.Arm
import VsaIris.Vsa.ReallocMove
import VsaIris.Vsa.BvLits
import VsaIris.Vsa.MoveRun

namespace VsaIris.Sym

open Vsa.MemRepr Vsa.Sim VsaIris.MallocFast

macro "snp_ld " h:term : tactic =>
  `(tactic| (rintro ⟨f, hfD, hfS, hv⟩; subst hv; rw [ldvf_readWin (ReadWin.transport $h (fun a h1 h2 => by
      first | rfl | (simp (disch := sx_addr) only [imgM_store_miss]))) hfD hfS _ (by sx_addr) (by simp only [widthOfM]; sx_addr)]; clear hfD hfS f))

structure MoveGeom (s dst n d src len : Nat) : Prop where
  d_lo : 0x8001ad10 ≤ d
  d_in : dst ≤ d ∧ d + len ≤ dst + n
  dst_hi : dst + n ≤ 0x100000000
  s_lo : 0x80000000 ≤ src
  s_hi : src + len ≤ 0x100000000
  s_htif : src + len ≤ 0x8001ad00 ∨ 0x8001ad10 ≤ src
  disj : src + len ≤ d ∨ d + len ≤ src

theorem nw_gen {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {pc : BitVec 64} {R : Nat → BitVec 64}
    {M : Mem} (P : Mem → Prop) (hP : P M) (h : ∀ M', P M' → SnpW live Dt DA S Q pc R M') :
    SnpW live Dt DA S Q pc R M := h M hP

theorem move_snp : ∀ p ∈ moveText, p ∈ snpText :=
  piecesText_sub (rs' := snpCodeRanges) fun a h => by
    simp [inRangesB, moveRanges, snpCodeRanges] at h ⊢; omega

theorem memmove_nw {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1) {Dt : Mem}
    {DA : List Nat} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {s dst n : Nat}
    (d src len : Nat) (g : Nat → BitVec 8) (R : Nat → BitVec 64) (Mt : Mem)
    (G : MoveGeom s dst n d src len)
    (h10 : R 10 = BitVec.ofNat 64 d) (h11 : R 11 = BitVec.ofNat 64 src)
    (h12 : R 12 = BitVec.ofNat 64 len) (hal : (R 1).toNat % 4 = 0)
    (hw : ReadWin Dt DA (snpS s dst n) Mt src (src + len) g)
    (hk : ∀ R' Mt', MMFrame R' R → Copied Mt' Mt d src len g →
      SnpW live Dt DA (snpS s dst n) Q (R 1) R' Mt') :
    SnpW live Dt DA (snpS s dst n) Q 0x800069c4#64 R Mt := by
  obtain ⟨hd1, ⟨hdd1, hdd2⟩, hdn, hs1, hs2, hs3, hdisj⟩ := G
  exact swp_host_out (fun p hp => List.mem_append_left _ (move_snp p hp))
    (memmoveH (fun p hp => hlive _ (move_snp p hp)) d src len g R Mt
      ⟨hd1, by omega, fun b h1 h2 => Or.inr (Or.inr ⟨by omega, by omega⟩), hs1, hs2, hs3, hdisj⟩
      h10 h11 h12 hal hw fun R' Mt' hF hc => swp_host_in (hk R' Mt' hF hc))

end VsaIris.Sym
