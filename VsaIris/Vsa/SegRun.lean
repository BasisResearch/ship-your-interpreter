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

/-- **A reflected segment as one local-run step.** The segment `bs` from
`pc0` pins the registers `L` (each owned, at its current value in the run's
valuation `rv`), reads the bytes `MR` (each either a persistent text byte or
an owned byte at its current value) and writes the owned bytes `W` (at their
current values). The successor's valuation has the reflected end PC, the
reflected final value of every pin, every written byte at its value after the
reflected write log, and every other owned register and byte unchanged. -/
theorem segFrom_of_segW {ro : List (Nat × BitVec 64)} {text : List (Nat × BitVec 8)}
    {rs : List Nat} {S : Nat → Prop} (bs : List BBlock) (L : GRegs)
    (lds : List (List (BitVec 8))) (pc0 : BitVec 64) (MR : List (Nat × DFrac × BitVec 8))
    (W : List (Nat × BitVec 8)) (n : Nat) {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    {P : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlen : evalBlocksFuel bs = n + 1)
    (hwf : ChainOK pc0 (keysG L) bs) (hkeys : KeysOK (keysG L))
    (hwr : ∀ k ∈ wrChain bs, k ∈ keysG L)
    (hcover : ∀ a, (∀ q ∈ W, q.1 ≠ a) → OutL (segOut bs L lds).log a)
    (hfacts : ∀ c : Config, VsaOk live c →
      FootHolds (M := vsaModel live) c [] MR (segRW bs L lds pc0) (segMW bs L lds W) →
      ChainFacts c.σ.mem c.σ.mem L lds bs)
    (hMR : ∀ q ∈ MR, (q.1, q.2.2) ∈ text ∨ (S q.1 ∧ mv q.1 = q.2.2))
    (hW : ∀ q ∈ W, S q.1 ∧ mv q.1 = q.2)
    (hPC : VsaIris.PC ∈ rs) (hpc : rv VsaIris.PC = pc0)
    (hL : ∀ q ∈ L, q.1 ∈ rs ∧ q.2 = rv q.1)
    (hP : ∀ (rv' : Nat → BitVec 64) (mv' : Nat → BitVec 8),
      rv' VsaIris.PC = evalBlocksPC pc0 (SegEvalState.init L lds) bs →
      (∀ q ∈ L, rv' q.1 = finReg bs L lds q.1) →
      (∀ k ∈ rs, k ≠ VsaIris.PC → (∀ q ∈ L, q.1 ≠ k) → rv' k = rv k) →
      (∀ q ∈ W, mv' q.1 = newByte bs L lds W q.1) →
      (∀ a, S a → (∀ q ∈ W, q.1 ≠ a) → mv' a = mv a) → P rv' mv') :
    SegFrom (vsaModel live) ro text rs S n rv mv P := by
  refine segFrom_of_runFact
    (seg_runFact live bs L lds pc0 MR W n hlen hwf hkeys hwr hcover hfacts)
    (fun p hp => nomatch hp) hMR ?_ ?_ ?_
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inl ⟨hPC, hpc⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact Or.inl ⟨(hL q hq).1, (hL q hq).2.symm⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hW q hq
  · intro rv' mv' hnew hframe hmemNew hmem
    refine hP rv' mv' (hnew _ List.mem_cons_self) (fun q hq => hnew _ (.tail _
      (List.mem_map_of_mem (f := fun p : Nat × BitVec 64 => (p.1, p.2, finReg bs L lds p.1)) hq)))
      (fun k hk hkpc hkL => hframe k hk fun p hp => ?_)
      (fun q hq => hmemNew _ (List.mem_map_of_mem
        (f := fun p : Nat × BitVec 8 =>
          (p.1, p.2, ((writeLog (wbase W) (segOut bs L lds).log)[p.1]?).getD 0)) hq))
      (fun a ha hne => hmem a ha fun p hp => ?_)
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact fun e => hkpc e.symm
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact hkL q hq
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hne q hq

/-- **A read-only reflected segment as one local-run step**: `segFrom_of_segW`
with an empty written set (`hsilent`: the reflected write log is empty). -/
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
    SegFrom (vsaModel live) ro text rs S n rv mv P :=
  segFrom_of_segW bs L lds pc0 MR [] n hlen hwf hkeys hwr
    (fun a _ => by rw [hsilent]; trivial) hfacts hMR (fun q hq => nomatch hq) hPC hpc hL
    (fun rv' mv' h1 h2 h3 _ h5 => hP rv' mv' h1 h2 h3 (fun a ha => h5 a ha (fun q hq => nomatch hq)))

/-! ## Leaf functions

A leaf function (`strlen`, `strcmp`, `memcpy`, the `snprintf` digit loop)
touches a FIXED set of GPRs, reads a fixed footprint and writes a fixed owned
byte set, so the whole function — loops, branches, tails and all — is ONE
`LocalRun` over ONE pin list. `leafL`/`leafStep` package that: a segment of
such a run contributes its `ChainFacts` and nothing else, and `hwf`, `hkeys`
and `hwr` are one `decide` each on the literal register list. -/

/-- The pin list of a leaf function: the registers it touches, at the run's
current values. -/
def leafL (regs : List Nat) (rv : Nat → BitVec 64) : GRegs := regs.map (fun k => (k, rv k))

theorem keysG_leafL : ∀ (regs : List Nat) (rv : Nat → BitVec 64), keysG (leafL regs rv) = regs
  | [], _ => rfl
  | k :: ks, rv => by
    show k :: keysG (leafL ks rv) = k :: ks
    rw [keysG_leafL ks rv]

/-- **One reflected segment of a leaf function's run.** -/
theorem leafStep {ro : List (Nat × BitVec 64)} {text : List (Nat × BitVec 8)}
    {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {rv : Nat → BitVec 64} {mv : Nat → BitVec 8} (regs : List Nat) (m : Nat)
    (bs : List BBlock) (lds : List (List (BitVec 8))) (pc0 : BitVec 64)
    (MR : List (Nat × DFrac × BitVec 8)) (W : List (Nat × BitVec 8)) (n : Nat)
    (hlen : evalBlocksFuel bs = n + 1)
    (hkeys : KeysOK regs) (hwf : ChainOK pc0 regs bs)
    (hwr : ∀ k ∈ wrChain bs, k ∈ regs)
    (hcover : ∀ a, (∀ q ∈ W, q.1 ≠ a) → OutL (segOut bs (leafL regs rv) lds).log a)
    (hfacts : ∀ c : Config, VsaOk live c →
      FootHolds (M := vsaModel live) c [] MR (segRW bs (leafL regs rv) lds pc0)
        (segMW bs (leafL regs rv) lds W) →
      ChainFacts c.σ.mem c.σ.mem (leafL regs rv) lds bs)
    (hMR : ∀ q ∈ MR, (q.1, q.2.2) ∈ text ∨ (S q.1 ∧ mv q.1 = q.2.2))
    (hW : ∀ q ∈ W, S q.1 ∧ mv q.1 = q.2)
    (hpc : rv VsaIris.PC = pc0)
    (hnext : ∀ (rv' : Nat → BitVec 64) (mv' : Nat → BitVec 8),
      rv' VsaIris.PC = evalBlocksPC pc0 (SegEvalState.init (leafL regs rv) lds) bs →
      (∀ k ∈ regs, rv' k = finReg bs (leafL regs rv) lds k) →
      (∀ q ∈ W, mv' q.1 = newByte bs (leafL regs rv) lds W q.1) →
      (∀ a, S a → (∀ q ∈ W, q.1 ≠ a) → mv' a = mv a) →
      LocalRun (vsaModel live) ro text (VsaIris.PC :: regs) S Q m rv' mv') :
    LocalRun (vsaModel live) ro text (VsaIris.PC :: regs) S Q (m + 1) rv mv := by
  refine Or.inr ⟨n, segFrom_of_segW bs (leafL regs rv) lds pc0 MR W n hlen
    (by rw [keysG_leafL]; exact hwf) (by rw [keysG_leafL]; exact hkeys)
    (by rw [keysG_leafL]; exact hwr) hcover hfacts hMR hW List.mem_cons_self hpc
    (fun q hq => ?_) (fun rv' mv' h1 h2 h3 h4 h5 => hnext rv' mv' h1 (fun k hk => ?_) h4 h5)⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
    exact ⟨.tail _ hk, rfl⟩
  · exact h2 (k, rv k) (List.mem_map_of_mem (f := fun k => (k, rv k)) hk)

/-! ## Instructions outside the reflected block model

`MKind` (`Vsa/Sim/BlockMem.lean:549`) does not cover every RISC-V instruction
gcc emitted: `sltu` (`snez`) is the one `strlen` needs. Such an instruction
still has a generated VSA site lemma (`stepObs_alu`): ONE step that advances
the PC by four, writes ONE GPR, and leaves memory, the output and every other
register alone. `AluStep` is that fact in the Iris machine's own vocabulary
and `runFact_of_aluStep` turns it into one local-run step, exactly as
`jalExec_of_site` does for a `jal`. -/

/-- **One observational ALU step.** From a well-formed state parked at `i`
with the read registers `RR` and read bytes `MR` at their values: one step to
a well-formed state with the PC at `i + 4`, `rd` holding `val`, and every
other register, every byte and the output unchanged. -/
def AluStep (live : Nat → Prop) (i : Nat) (RR : List (Nat × DFrac × BitVec 64))
    (MR : List (Nat × DFrac × BitVec 8)) (rd : Nat) (val : BitVec 64) : Prop :=
  ∀ c : Config, VsaOk live c → vsaReg c VsaIris.PC = BitVec.ofNat 64 i →
    (∀ q ∈ RR, vsaReg c q.1 = q.2.2) → (∀ q ∈ MR, (vsaModel live).mem c q.1 = q.2.2) →
    ∃ c' : Config, Vsa.Machine.Step c c' ∧ VsaOk live c' ∧
      vsaReg c' VsaIris.PC = BitVec.ofNat 64 (i + 4) ∧ vsaReg c' rd = val ∧
      (∀ k, k ≠ VsaIris.PC → k ≠ rd → vsaReg c' k = vsaReg c k) ∧
      (∀ a, (vsaModel live).mem c' a = (vsaModel live).mem c a) ∧
      (vsaModel live).out c' = (vsaModel live).out c

/-- **An observational ALU step as a one-step `RunFact`.** -/
theorem runFact_of_aluStep {live : Nat → Prop} {i : Nat}
    {RR : List (Nat × DFrac × BitVec 64)} {MR : List (Nat × DFrac × BitVec 8)}
    {rd : Nat} {old val : BitVec 64} (h : AluStep live i RR MR rd val) :
    RunFact (vsaModel live) 0 RR MR
      [(VsaIris.PC, BitVec.ofNat 64 i, BitVec.ofNat 64 (i + 4)), (rd, old, val)] [] := by
  intro c hok hfoot
  obtain ⟨hRR, hMR, hRW, _⟩ := hfoot
  have hpc : vsaReg c VsaIris.PC = BitVec.ofNat 64 i := hRW _ List.mem_cons_self
  obtain ⟨c', hstep, hok', hpc', hrd', hframe, hmem, hout⟩ := h c hok hpc hRR hMR
  refine ⟨c', ReachesN.succ (M := vsaModel live) (vsaStep_of_step hstep) (ReachesN.zero (M := vsaModel live) c'), hok', ⟨?_, ?_, ?_, ?_⟩,
    hout⟩
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hpc'
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact hrd'
      · cases hq
  · intro k hk
    exact hframe k (fun e => hk _ List.mem_cons_self e.symm)
      (fun e => hk _ (.tail _ List.mem_cons_self) e.symm)
  · intro q hq; cases hq
  · intro a _; exact hmem a

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
