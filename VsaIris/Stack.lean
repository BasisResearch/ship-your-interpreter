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

/-- Re-index an owned interval by equal endpoints (the `Nat` arithmetic a
call site would otherwise `rw` under `blockOwn`). -/
theorem blockOwn_cast {p n p' n' : Nat} (hp : p = p') (hn : n = n') :
    blockOwn (GF := GF) p n ⊢ blockOwn p' n' := by
  subst hp; subst hn; exact .rfl

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

/-- **The prologue**: `addi sp,sp,-f` takes the callee's own frame out of the
top of its owned region, leaving the rest below the lowered `sp`. -/
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

/-- **The epilogue**: `addi sp,sp,f` puts the frame back. -/
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

/-! ## The abort resource and its re-basing -/

/-- **What an abort hands the top** (INTERP_DESIGN.md §4.2, `abortRes`).
`Core` is the part that does not mention the site's stack pointer: the landing
registers (H5 pins them from the `jmp_buf`, or the `exit(1)` entry for an
out-of-memory), and SOME world. The rest is the WHOLE owned stack below `s`,
because the landing runs `fprintf` on it. -/
def abortAt (Core : IProp GF) (s : BitVec 64) (need : Nat) : IProp GF :=
  iprop(Core ∗ stackScratch s need)

/-- The named destructurer / constructor of `abortAt` (CLAUDE.md: a landed
∃/∧ tower is consumed through ONE named lemma, never positionally). -/
theorem abortAt_elim (Core : IProp GF) (s : BitVec 64) (need : Nat) :
    abortAt Core s need ⊢ iprop(Core ∗ stackScratch s need) := .rfl

theorem abortAt_intro (Core : IProp GF) (s : BitVec 64) (need : Nat) :
    iprop(Core ∗ stackScratch s need) ⊢ abortAt Core s need := .rfl

/-! ## The call step of an arm

At a call the caller lends the callee a NARROWER part of its own stack region
and keeps the slack. In partial mode it must also re-base the abort
continuation it inherited, and — because `fnSpecAbort`'s branches are an
additive pair — the very same bytes serve the return branch
(INTERP_DESIGN.md §10.2). These two rules are that step, once. -/

end

end VsaIris
