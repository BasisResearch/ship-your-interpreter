import VsaIris.CallAbort
import VsaIris.DlHeap

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem blockOwn_cast {p n p' n' : Nat} (hp : p = p') (hn : n = n') :
    blockOwn (GF := GF) p n ⊢ blockOwn p' n' := by
  subst hp; subst hn; exact .rfl

theorem blockOwn_split (p n m q k : Nat) (hm : m ≤ n) (hq : q = p + m) (hk : k = n - m) :
    blockOwn (GF := GF) p n ⊢ blockOwn p m ∗ blockOwn q k := by
  subst hq; subst hk
  unfold blockOwn
  iintro Hb
  ihave ⟨H1, H2⟩ := ownSet_split (InExt (p, n)) (InExt (p, m)) byteAny $$ Hb
  isplitl [H1]
  · iapply ownSet_iff byteAny _ $$ H1
    intro a; unfold InExt; simp only []; omega
  · iapply ownSet_iff byteAny _ $$ H2
    intro a; unfold InExt; simp only []; omega

theorem blockOwn_join (p n q m r : Nat) (hq : q = p + n) (hr : r = n + m) :
    blockOwn (GF := GF) p n ∗ blockOwn q m ⊢ blockOwn p r := by
  subst hq; subst hr
  unfold blockOwn
  iintro H
  ihave H := ownSet_join (InExt (p, n)) (InExt (p + n, m)) byteAny
    (fun a ha => by unfold InExt at *; omega) $$ H
  iapply ownSet_iff byteAny _ $$ H
  intro a; unfold InExt; simp only []; omega

theorem toNat_sub_frame {s f : BitVec 64} (hf : f.toNat ≤ s.toNat) :
    (s - f).toNat = s.toNat - f.toNat := by
  rw [BitVec.toNat_sub]
  have := s.isLt; have := f.isLt
  omega

theorem stackScratch_narrow {s : BitVec 64} {n m : Nat} (hn : n ≤ s.toNat) (hm : m ≤ n) :
    stackScratch (GF := GF) s n ⊢ blockOwn (s.toNat - n) (n - m) ∗ stackScratch s m := by
  unfold stackScratch
  iapply blockOwn_split (s.toNat - n) n (n - m) (s.toNat - m) m (by omega) (by omega) (by omega)

theorem stackScratch_widen {s : BitVec 64} {n m : Nat} (hn : n ≤ s.toNat) (hm : m ≤ n) :
    blockOwn (GF := GF) (s.toNat - n) (n - m) ∗ stackScratch s m ⊢ stackScratch s n := by
  unfold stackScratch
  iapply blockOwn_join (s.toNat - n) (n - m) (s.toNat - m) m n (by omega) (by omega)

theorem stackScratch_frame {s f : BitVec 64} {n : Nat} (hn : n ≤ s.toNat) (hf : f.toNat ≤ n) :
    stackScratch (GF := GF) s n ⊢
      stackScratch (s - f) (n - f.toNat) ∗ blockOwn (s - f).toNat f.toNat := by
  have hsf : (s - f).toNat = s.toNat - f.toNat := toNat_sub_frame (by omega)
  unfold stackScratch
  rw [hsf]
  iintro Hb
  ihave ⟨H1, H2⟩ := blockOwn_split (s.toNat - n) n (n - f.toNat) (s.toNat - f.toNat) f.toNat
    (by omega) (by omega) (by omega) $$ Hb
  isplitl [H1]
  · iapply blockOwn_cast (by omega) rfl $$ H1
  · iexact H2

theorem stackScratch_unframe {s f : BitVec 64} {n : Nat} (hn : n ≤ s.toNat) (hf : f.toNat ≤ n) :
    stackScratch (GF := GF) (s - f) (n - f.toNat) ∗ blockOwn (s - f).toNat f.toNat ⊢
      stackScratch s n := by
  have hsf : (s - f).toNat = s.toNat - f.toNat := toNat_sub_frame (by omega)
  unfold stackScratch
  rw [hsf]
  iintro ⟨H1, H2⟩
  ihave H1 := blockOwn_cast (p' := s.toNat - n) (n' := n - f.toNat) (by omega) rfl $$ H1
  iapply blockOwn_join (s.toNat - n) (n - f.toNat) (s.toNat - f.toNat) f.toNat n
    (by omega) (by omega)
  iframe H1 H2

def abortAt (Core : IProp GF) (s : BitVec 64) (need : Nat) : IProp GF :=
  iprop(Core ∗ stackScratch s need)

theorem abortAt_elim (Core : IProp GF) (s : BitVec 64) (need : Nat) :
    abortAt Core s need ⊢ iprop(Core ∗ stackScratch s need) := .rfl

theorem abortAt_intro (Core : IProp GF) (s : BitVec 64) (need : Nat) :
    iprop(Core ∗ stackScratch s need) ⊢ abortAt Core s need := .rfl

end

end VsaIris
