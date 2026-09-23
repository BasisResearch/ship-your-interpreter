import VsaIris.CallAbort
import VsaIris.DlHeap

/-!
# The stack: carve, join, and re-basing an abort continuation (work package F3)

INTERP_DESIGN.md §2 F3 ("`stackScratch s n` split and join (`blockOwn`
arithmetic)") and §4.2/§10.2.

A callee's scratch region is carved out of the caller's owned stack region and
returned at the call's end. VSA states this as the side condition `StackOK SL
sp headroom` plus a "stack window below the entry sp" exception in every
frame; in the Iris route the window is an owned resource, so the carve is a
separation-logic step and the return is its inverse. The arithmetic is
`blockOwn`'s: an interval of bytes splits at any cut point and adjacent
intervals join.

The abort resource of INTERP_DESIGN.md §4.2 is `abortAt Core s need`: a
`Core` that does not mention the site's stack pointer (the landing registers
and SOME world), and the WHOLE owned stack below `s`. `abort_rebase` turns a
caller's abort continuation into its callee's by joining the caller's frame
bytes `[s_c, s_p)` and the slack `[s_p - n_p, s_c - n_c)` back in. Because
`fnSpecAbort`'s two branches are an additive pair, those same bytes also serve
the return branch (INTERP_DESIGN.md §10.1-§10.2).
-/

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-! ## `blockOwn` interval arithmetic -/

/-- The empty interval owns nothing. -/
theorem blockOwn_emp (p : Nat) : emp ⊢@{IProp GF} blockOwn p 0 := by
  have hno : ∀ a : Nat, a ∈ ([] : List Nat) ↔ InExt (p, 0) a := by
    intro a
    constructor
    · intro h; cases h
    · intro h; unfold InExt at h; simp only [] at h; omega
  unfold blockOwn ownSet
  iintro _
  iexists ([] : List Nat)
  isplitr
  · ipureintro
    exact ⟨List.nodup_nil, hno⟩
  simp only [sepL_nil]
  iempintro

/-- **Split** an owned interval at a cut point: `[p, p+n)` is `[p, p+m)` and
`[p+m, p+n)`. The successor address and length are given as equations so call
sites never rewrite under `blockOwn`. -/
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

/-- **Join** two adjacent owned intervals. -/
theorem blockOwn_join (p n q m r : Nat) (hq : q = p + n) (hr : r = n + m) :
    blockOwn (GF := GF) p n ∗ blockOwn q m ⊢ blockOwn p r := by
  subst hq; subst hr
  unfold blockOwn
  iintro H
  ihave H := ownSet_join (InExt (p, n)) (InExt (p + n, m)) byteAny
    (fun a ha => by unfold InExt at *; omega) $$ H
  iapply ownSet_iff byteAny _ $$ H
  intro a; unfold InExt; simp only []; omega

/-! ## The caller's stack region and the callee's scratch

`stackScratch s n` is `blockOwn (s.toNat - n) n`, the `n` bytes below `s`
(VSA's `StackOK SL s n` as ownership). -/

/-- `sp - f` in `Nat`, for a frame that fits. -/
theorem toNat_sub_frame {s f : BitVec 64} (hf : f.toNat ≤ s.toNat) :
    (s - f).toNat = s.toNat - f.toNat := by
  rw [BitVec.toNat_sub]
  have := s.isLt; have := f.isLt
  omega

/-- **Narrowing** the owned stack: a caller with `n` bytes below `s` keeps the
slack `[s - n, s - m)` and offers `m`. -/
theorem stackScratch_narrow {s : BitVec 64} {n m : Nat} (hn : n ≤ s.toNat) (hm : m ≤ n) :
    stackScratch (GF := GF) s n ⊢ blockOwn (s.toNat - n) (n - m) ∗ stackScratch s m := by
  unfold stackScratch
  iapply blockOwn_split (s.toNat - n) n (n - m) (s.toNat - m) m (by omega) (by omega) (by omega)

/-- **Widening** it back. -/
theorem stackScratch_widen {s : BitVec 64} {n m : Nat} (hn : n ≤ s.toNat) (hm : m ≤ n) :
    blockOwn (GF := GF) (s.toNat - n) (n - m) ∗ stackScratch s m ⊢ stackScratch s n := by
  unfold stackScratch
  iapply blockOwn_join (s.toNat - n) (n - m) (s.toNat - m) m n (by omega) (by omega)

/-- **Carve a callee's scratch out of the caller's stack.** The caller owns
`n` bytes below `s`, spills an `f`-byte frame (`addi sp,sp,-f`) and calls with
`sp = s - f`; the callee needs `nc` bytes below that. The caller keeps its own
frame `[s - f, s)` and the slack below the callee's region.

The side condition `nc + f.toNat ≤ n` is exactly `StackOK.child`'s
(`Vsa/While/StackNeed.lean`), which for every structural node is definitional:
a node's need is its frame plus the deepest child's. -/
theorem stackScratch_carve {s f : BitVec 64} {n nc : Nat}
    (hn : n ≤ s.toNat) (hf : f.toNat ≤ s.toNat) (hle : nc + f.toNat ≤ n) :
    stackScratch (GF := GF) s n ⊢
      blockOwn (s.toNat - n) (n - (nc + f.toNat)) ∗ stackScratch (s - f) nc ∗
        blockOwn (s - f).toNat f.toNat := by
  unfold stackScratch
  rw [toNat_sub_frame hf]
  iintro Hb
  ihave ⟨H0, Hb⟩ := blockOwn_split (s.toNat - n) n (n - (nc + f.toNat))
    (s.toNat - f.toNat - nc) (nc + f.toNat) (by omega) (by omega) (by omega) $$ Hb
  ihave ⟨H1, H2⟩ := blockOwn_split (s.toNat - f.toNat - nc) (nc + f.toNat) nc
    (s.toNat - f.toNat) f.toNat (by omega) (by omega) (by omega) $$ Hb
  iframe H0 H1 H2

/-- **Return the callee's scratch and the caller's frame.** The inverse of
`stackScratch_carve`: what the caller re-assembles at the call's return, and
what an abort must hand back (`abort_rebase`). -/
theorem stackScratch_join {s f : BitVec 64} {n nc : Nat}
    (hn : n ≤ s.toNat) (hf : f.toNat ≤ s.toNat) (hle : nc + f.toNat ≤ n) :
    blockOwn (GF := GF) (s.toNat - n) (n - (nc + f.toNat)) ∗ stackScratch (s - f) nc ∗
        blockOwn (s - f).toNat f.toNat ⊢ stackScratch s n := by
  unfold stackScratch
  rw [toNat_sub_frame hf]
  iintro ⟨H0, H1, H2⟩
  ihave Hb := blockOwn_join (s.toNat - f.toNat - nc) nc (s.toNat - f.toNat) f.toNat
    (nc + f.toNat) (by omega) (by omega) $$ [H1 H2]
  · iframe H1 H2
  iapply blockOwn_join (s.toNat - n) (n - (nc + f.toNat)) (s.toNat - f.toNat - nc)
    (nc + f.toNat) n (by omega) (by omega)
  iframe H0 Hb

/-! ## The abort resource and its re-basing -/

/-- **What an abort hands the top** (INTERP_DESIGN.md §4.2, `abortRes`).
`Core` is the part that does not mention the site's stack pointer: the landing
registers (H5 pins them from the `jmp_buf`, or the `exit(1)` entry for an
out-of-memory), and SOME world. The rest is the WHOLE owned stack below `s`,
because the landing runs `fprintf` on it. -/
def abortAt (Core : IProp GF) (s : BitVec 64) (need : Nat) : IProp GF :=
  iprop(Core ∗ stackScratch s need)

/-- **Re-basing an abort continuation** (INTERP_DESIGN.md §10.2, F3). A
caller holding "if the run aborts below MY `sp`, the rest of the run is
proved" turns it into the same for its callee's region, by joining in the
bytes the callee does not own: its own frame `[s_c, s_p)` and the slack
`[s_p - n_p, s_c - n_c)`.

Because `fnSpecAbort`'s branches are an additive pair, the caller may hand
the SAME bytes to the return branch (`stackScratch_join`) — they are proved
from one context, not split between them. -/
theorem abort_rebase {M : MachineModel} {Wp : MachWP (GF := GF) M}
    {Φ : Nat × String → IProp GF} (Core : IProp GF) (sp_ sc : BitVec 64) (np nc : Nat)
    (hnp : np ≤ sp_.toNat) (hnc : nc ≤ sc.toNat) (hsc : sc.toNat ≤ sp_.toNat)
    (hle : sp_.toNat - np ≤ sc.toNat - nc) :
    (abortAt Core sp_ np -∗ Wp.W Φ) ∗
      blockOwn sc.toNat (sp_.toNat - sc.toNat) ∗
      blockOwn (sp_.toNat - np) ((sc.toNat - nc) - (sp_.toNat - np))
    ⊢ (abortAt Core sc nc -∗ Wp.W Φ) := by
  unfold abortAt stackScratch
  iintro ⟨Hk, Htop, Hlow⟩ ⟨HC, Hc⟩
  ihave Hlow := blockOwn_join (sp_.toNat - np) ((sc.toNat - nc) - (sp_.toNat - np))
    (sc.toNat - nc) nc (sc.toNat - (sp_.toNat - np)) (by omega) (by omega) $$ [Hlow Hc]
  · iframe Hlow Hc
  ihave Hlow := blockOwn_join (sp_.toNat - np) (sc.toNat - (sp_.toNat - np)) sc.toNat
    (sp_.toNat - sc.toNat) np (by omega) (by omega) $$ [Hlow Htop]
  · iframe Hlow Htop
  iapply Hk $$ [HC Hlow]
  iframe HC Hlow

end

end VsaIris
