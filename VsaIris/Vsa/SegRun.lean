import VsaIris.Vsa.Tools
import VsaIris.LocalRun

/-!
# Reflected segments as local-run steps

`VsaIris/LocalRun.lean` gives the fuel-bounded owned-footprint run rule
`wp_localRunW` (the loop rule, for either WP; xv6iris `ProofMemset.v:1-9`
"bounded loop, not iLöb") and `segFrom_of_runFact`, which turns ONE VSA
`RunFact` into ONE `SegFrom` step of such a run.

This file closes the gap for the shape every H3 helper has: a leaf function
(`strlen`, `strcmp`, the `memcpy` loops) is a chain of reflected segments that
WRITE NO MEMORY, over a fixed set of owned registers. `segFrom_of_seg`
instantiates `segFrom_of_runFact` at `Inst.seg_runFact` with an empty written
set, so a caller supplies only

* the segment's own four `decide`s (`hlen`, `hwf`, `hkeys`, `hwr`);
* silence (`hsilent`: the reflected write log is empty, one `decide`);
* the segment's `ChainFacts` (exactly what `segToTriple`/`chain_facts` needs);
* where each read byte lives (`hMR`: persistent text, or an owned byte);
* the register pins, read off the run's register valuation.

`readBytes_present` is the companion: the read footprint of such a step is
present with its values, which is what VSA's fetch facts (`Code.*Loaded`) and
its string predicates (`CStr`) consume.

Discipline (CLAUDE.md): this is the abstraction the per-site batteries would
otherwise duplicate. A helper proof instantiates it; it never re-runs
`seg_runFact` by hand.
-/

namespace VsaIris.Inst

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable
open Vsa.Machine (Config)
open Vsa.Sim

section SegRun

variable {live : Nat → Prop}

/-- **A read-only reflected segment as one local-run step.** The segment `bs`
from `pc0` writes no memory (`hsilent`), pins the registers `L` (each owned,
at its current value in the run's valuation `rv`), and reads the bytes `MR`
(each either a persistent text byte or an owned byte at its current value).
The successor's valuation has the reflected end PC, the reflected final value
of every pin, and every other owned register and byte unchanged. -/
theorem segFrom_of_seg {ro : List (Nat × BitVec 64)} {text : List (Nat × BitVec 8)}
    {rs : List Nat} {S : Nat → Prop} (bs : List BBlock) (L : GRegs)
    (lds : List (List (BitVec 8))) (pc0 : BitVec 64) (MR : List (Nat × DFrac × BitVec 8))
    (n : Nat) {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    {P : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlen : evalBlocksFuel bs = n + 1)
    (hwf : ChainOK pc0 (keysG L) bs) (hkeys : KeysOK (keysG L))
    (hwr : ∀ k ∈ wrChain bs, k ∈ keysG L)
    (hsilent : (segOut bs L lds).log = [])
    (hfacts : ∀ c : Config, VsaOk live c →
      FootHolds (M := vsaModel live) c [] MR (segRW bs L lds pc0) [] →
      ChainFacts c.σ.mem c.σ.mem L lds bs)
    (hMR : ∀ q ∈ MR, (q.1, q.2.2) ∈ text ∨ (S q.1 ∧ mv q.1 = q.2.2))
    (hPC : VsaIris.PC ∈ rs) (hpc : rv VsaIris.PC = pc0)
    (hL : ∀ q ∈ L, q.1 ∈ rs ∧ q.2 = rv q.1)
    (hP : ∀ (rv' : Nat → BitVec 64) (mv' : Nat → BitVec 8),
      rv' VsaIris.PC = evalBlocksPC pc0 (SegEvalState.init L lds) bs →
      (∀ q ∈ L, rv' q.1 = finReg bs L lds q.1) →
      (∀ k ∈ rs, k ≠ VsaIris.PC → (∀ q ∈ L, q.1 ≠ k) → rv' k = rv k) →
      (∀ a, S a → mv' a = mv a) → P rv' mv') :
    SegFrom (vsaModel live) ro text rs S n rv mv P := by
  have hMWnil : segMW bs L lds [] = [] := rfl
  refine segFrom_of_runFact
    (hMW := fun p hp => nomatch (hMWnil ▸ hp))
    (seg_runFact live bs L lds pc0 MR [] n hlen hwf hkeys hwr
      (fun a _ => by rw [hsilent]; trivial) hfacts)
    (fun p hp => nomatch hp) hMR ?_ ?_
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨hPC, hpc⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact ⟨(hL q hq).1, (hL q hq).2.symm⟩
  · intro rv' mv' hnew hframe _ hmem
    refine hP rv' mv' (hnew _ List.mem_cons_self) (fun q hq => hnew _ (.tail _
      (List.mem_map_of_mem (f := fun p : Nat × BitVec 64 => (p.1, p.2, finReg bs L lds p.1)) hq)))
      (fun k hk hkpc hkL => hframe k hk fun p hp => ?_) (fun a ha => hmem a ha (fun p hp => nomatch (hMWnil ▸ hp)))
    rcases List.mem_cons.mp hp with rfl | hp
    · exact fun e => hkpc e.symm
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hkL q hq

/-- Fuel is a bound: a run that finishes in `n` segments finishes in `n+1`. -/
theorem localRun_succ {ro : List (Nat × BitVec 64)} {text : List (Nat × BitVec 8)}
    {rs : List Nat} {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} :
    ∀ (n : Nat) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8),
      LocalRun (vsaModel live) ro text rs S Q n rv mv →
      LocalRun (vsaModel live) ro text rs S Q (n + 1) rv mv
  | 0, _, _, h => .inl h
  | n + 1, rv, mv, h => by
    rcases h with h | ⟨k, h⟩
    · exact .inl h
    · exact .inr ⟨k, h.mono fun rv' mv' hr => localRun_succ n rv' mv' hr⟩

theorem localRun_le {ro : List (Nat × BitVec 64)} {text : List (Nat × BitVec 8)}
    {rs : List Nat} {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {n n' : Nat} (hn : n ≤ n') {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : LocalRun (vsaModel live) ro text rs S Q n rv mv) :
    LocalRun (vsaModel live) ro text rs S Q n' rv mv := by
  induction n' with
  | zero => rwa [Nat.le_zero.mp hn] at h
  | succ m ih =>
    rcases Nat.lt_or_ge m n with hm | hm
    · rwa [show m + 1 = n from by omega]
    · exact localRun_succ m rv mv (ih hm)

/-- **The read footprint is present with its values.** A step's read bytes
are either persistent text or owned; either way, in any `VsaOk` state that
holds the footprint and keeps them `live`, they are present in memory with
the footprint's values. This is what VSA's `Code.*Loaded` fetch predicates
and its string predicates (`CStr`) consume. -/
theorem readBytes_present {c : Config} (hok : VsaOk live c)
    (MR : List (Nat × DFrac × BitVec 8))
    (hmr : ∀ p ∈ MR, (vsaModel live).mem c p.1 = p.2.2)
    (hlive : ∀ p ∈ MR, live p.1) : ∀ p ∈ MR, c.σ.mem[p.1]? = some p.2.2 :=
  code_present hok MR hmr hlive

end SegRun

end VsaIris.Inst
