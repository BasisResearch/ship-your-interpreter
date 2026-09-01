import Vsa.Sim.DeriveCaseRow

/-!
# `SegToTripleFramed` — the FRAMED seg→`Triple` marshalling (gen_fn layer)

`segToTriple` (DeriveCaseRow.lean) discards three clauses of `segEval_sound`
that a whole-function fold cannot live without: the register FRAME clause (all
non-noise, non-written registers preserved), sailOutput preservation, and the
computed register outcome (`GHolds … out.regs`).  A function fold threads an
ABI keep-set (ra/sp/gp/s0…), the console output, and the HTIF mailbox registers
(`htif_payload_writes`/`htif_tohost` — `noiseRegs` excludes them, so the frame
clause transports them across any body seg) through EVERY block; this file
lands that marshalling ONCE:

* `segToTripleFramed` — `segToTriple` keeping ALL of `segEval_sound`'s
  conclusion (probe-proven 2026-09-01, lifted verbatim).
* `FrameOK keep bs` — decidable admissibility of a keep-set against a seg:
  every kept pin a genuine GPR, not noise, not written by the chain; the chain
  writes no HTIF mailbox register.  ONE `decide` per row instantiation.
* `FramedSegPre`/`FramedSegPost` — the named-field pre/post every gen_fn block
  row uses: `SegPre` + keep-set + output + HTIF mailbox pins; the computed
  outcome + all of them transported.
* `segRowFramed` — the generic framed block row: `Triple FramedSegPre
  FramedSegPost` from two `decide`s.  gen_fn's per-block emission is an
  INSTANTIATION of this (seg + L literals + the decides), nothing more.

`gprGet`/`gprReg` note: `σ.regs.get? (gprReg n)` is DEPENDENTLY typed
(`Option (RegisterType (gprReg n))`), so the frame transport cases on the
concrete index 1..31 — each branch a defeq `exact` — exactly the type-level
trick `BlockPilot.lean` documents for `gprGet` itself.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)

namespace Vsa.Sim

/-- `segToTriple` keeping segEval_sound's frame clause AND sailOutput
preservation AND the computed register outcome (all discarded by plain
`segToTriple`). -/
theorem segToTripleFramed (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (Q : Config → Prop)
    (hwf : ChainOK pc0 (keysG L) bs)
    (hpost : ∀ (c : Config) (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.mem = writeLog m0 (evalBlocks bs (SegEvalState.init L lds)).log →
      σ'.sailOutput = c.σ.sailOutput →
      σ'.regs.get? Register.PC
        = some (evalBlocksPC pc0 (SegEvalState.init L lds) bs) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      GHolds σ' (evalBlocks bs (SegEvalState.init L lds)).regs →
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ n ∈ wrChain bs, (gprReg n == R) = false) →
        σ'.regs.get? R = c.σ.regs.get? R) →
      Q ⟨σ', i', u'⟩) :
    Triple (SegPre bs L lds pc0 m0) Q := by
  intro c hpre
  obtain ⟨hG, hmem, hpc, ⟨vm, hmi⟩, hL, hkeys, hfacts, htick⟩ := hpre
  obtain ⟨σ', i', hs, hi', hG', hmem', hout, hpc', hmi', hregs, hframe⟩ :=
    segEval_sound bs c.σ c.tick c.steps pc0 vm L lds hG hpc hmi hL hkeys hfacts hwf htick
  rw [hmem] at hmem'
  exact ⟨⟨σ', i', c.steps + evalBlocksFuel bs⟩, hs,
    hpost c σ' i' (c.steps + evalBlocksFuel bs) hG' hi' hmem' hout hpc' hmi' hregs hframe⟩

#print axioms segToTripleFramed

/-- Keep-set admissibility against a seg, in exactly the `Bool`-equation form
the frame clause consumes: every kept key a genuine GPR index whose register is
neither noise nor written by the chain; and the chain writes no HTIF mailbox
register.  Concrete at every instantiation — ONE kernel `decide` per row. -/
def FrameOK (ks : List Nat) (bs : List BBlock) : Prop :=
  (∀ n ∈ ks, (1 ≤ n ∧ n ≤ 31) ∧
    (∀ rr ∈ noiseRegs, (rr == gprReg n) = false) ∧
    (∀ m ∈ wrChain bs, (gprReg m == gprReg n) = false)) ∧
  (∀ m ∈ wrChain bs, (gprReg m == Register.htif_payload_writes) = false ∧
    (gprReg m == Register.htif_tohost) = false)

instance instDecFrameOK (ks : List Nat) (bs : List BBlock) :
    Decidable (FrameOK ks bs) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- One kept pin transported across a frame clause: full case analysis on the
concrete GPR index (each branch defeq — the `RegisterType` dependent-typing
trick). -/
theorem gprGet_of_frame {σ' σ : MState} {wrs : List Nat} (n : Nat)
    (h1 : 1 ≤ n) (h31 : n ≤ 31)
    (hnoise : ∀ rr ∈ noiseRegs, (rr == gprReg n) = false)
    (hwr : ∀ m ∈ wrs, (gprReg m == gprReg n) = false)
    (hframe : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ m ∈ wrs, (gprReg m == R) = false) →
      σ'.regs.get? R = σ.regs.get? R) :
    gprGet σ' n = gprGet σ n := by
  match n, h1, h31, hnoise, hwr with
  | 1, _, _, hn, hw => exact hframe (gprReg 1) hn hw
  | 2, _, _, hn, hw => exact hframe (gprReg 2) hn hw
  | 3, _, _, hn, hw => exact hframe (gprReg 3) hn hw
  | 4, _, _, hn, hw => exact hframe (gprReg 4) hn hw
  | 5, _, _, hn, hw => exact hframe (gprReg 5) hn hw
  | 6, _, _, hn, hw => exact hframe (gprReg 6) hn hw
  | 7, _, _, hn, hw => exact hframe (gprReg 7) hn hw
  | 8, _, _, hn, hw => exact hframe (gprReg 8) hn hw
  | 9, _, _, hn, hw => exact hframe (gprReg 9) hn hw
  | 10, _, _, hn, hw => exact hframe (gprReg 10) hn hw
  | 11, _, _, hn, hw => exact hframe (gprReg 11) hn hw
  | 12, _, _, hn, hw => exact hframe (gprReg 12) hn hw
  | 13, _, _, hn, hw => exact hframe (gprReg 13) hn hw
  | 14, _, _, hn, hw => exact hframe (gprReg 14) hn hw
  | 15, _, _, hn, hw => exact hframe (gprReg 15) hn hw
  | 16, _, _, hn, hw => exact hframe (gprReg 16) hn hw
  | 17, _, _, hn, hw => exact hframe (gprReg 17) hn hw
  | 18, _, _, hn, hw => exact hframe (gprReg 18) hn hw
  | 19, _, _, hn, hw => exact hframe (gprReg 19) hn hw
  | 20, _, _, hn, hw => exact hframe (gprReg 20) hn hw
  | 21, _, _, hn, hw => exact hframe (gprReg 21) hn hw
  | 22, _, _, hn, hw => exact hframe (gprReg 22) hn hw
  | 23, _, _, hn, hw => exact hframe (gprReg 23) hn hw
  | 24, _, _, hn, hw => exact hframe (gprReg 24) hn hw
  | 25, _, _, hn, hw => exact hframe (gprReg 25) hn hw
  | 26, _, _, hn, hw => exact hframe (gprReg 26) hn hw
  | 27, _, _, hn, hw => exact hframe (gprReg 27) hn hw
  | 28, _, _, hn, hw => exact hframe (gprReg 28) hn hw
  | 29, _, _, hn, hw => exact hframe (gprReg 29) hn hw
  | 30, _, _, hn, hw => exact hframe (gprReg 30) hn hw
  | 31, _, _, hn, hw => exact hframe (gprReg 31) hn hw
  | n + 32, _, h31, _, _ => exact absurd h31 (by omega)

/-- Transport a kept pin list across a frame clause. -/
theorem gholds_keep_of_frame {σ' σ : MState} {wrs : List Nat}
    (keep : GRegs)
    (hok : ∀ n ∈ keysG keep, (1 ≤ n ∧ n ≤ 31) ∧
      (∀ rr ∈ noiseRegs, (rr == gprReg n) = false) ∧
      (∀ m ∈ wrs, (gprReg m == gprReg n) = false))
    (hframe : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ m ∈ wrs, (gprReg m == R) = false) →
      σ'.regs.get? R = σ.regs.get? R)
    (hkeep : GHolds σ keep) : GHolds σ' keep := by
  induction keep with
  | nil => trivial
  | cons p L ih =>
    obtain ⟨n, v⟩ := p
    obtain ⟨hv, hL⟩ := hkeep
    obtain ⟨⟨h1, h31⟩, hnoise, hwr⟩ := hok n (List.mem_cons_self ..)
    exact ⟨(gprGet_of_frame n h1 h31 hnoise hwr hframe).trans hv,
      ih (fun m hm => hok m (List.mem_cons_of_mem _ hm)) hL⟩

/-- **The framed block-row precondition**: `SegPre` + the ABI keep-set + the
console output + the HTIF mailbox pins.  What a function fold knows arriving at
any block. -/
structure FramedSegPre (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (keep : GRegs) (outp : Array String) (pwv : BitVec 4)
    (c : Config) : Prop where
  seg : SegPre bs L lds pc0 m0 c
  keep : GHolds c.σ keep
  out : c.σ.sailOutput = outp
  pw : c.σ.regs.get? Register.htif_payload_writes = some pwv
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-- **The framed block-row post**: the computed seg outcome (end PC, write-log
memory, computed registers) with the keep-set, output, and HTIF mailbox pins
TRANSPORTED, plus the tick budget for the next block. -/
structure FramedSegPost (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (keep : GRegs) (outp : Array String) (pwv : BitVec 4)
    (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = writeLog m0 (evalBlocks bs (SegEvalState.init L lds)).log
  pc : c.σ.regs.get? Register.PC
    = some (evalBlocksPC pc0 (SegEvalState.init L lds) bs)
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  regs : GHolds c.σ (evalBlocks bs (SegEvalState.init L lds)).regs
  keep : GHolds c.σ keep
  out : c.σ.sailOutput = outp
  pw : c.σ.regs.get? Register.htif_payload_writes = some pwv
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-- **The generic framed block row.**  From the row's two kernel `decide`s
(`ChainOK`, `FrameOK`), the whole block runs `FramedSegPre → FramedSegPost`.
Every gen_fn block row is an instantiation of this at its seg/L literals. -/
theorem segRowFramed (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (keep : GRegs) (outp : Array String) (pwv : BitVec 4)
    (hwf : ChainOK pc0 (keysG L) bs)
    (hfr : FrameOK (keysG keep) bs) :
    Triple (FramedSegPre bs L lds pc0 m0 keep outp pwv)
      (FramedSegPost bs L lds pc0 m0 keep outp pwv) := by
  intro c hpre
  obtain ⟨hG, hmem, hpc, ⟨vm, hmi⟩, hL, hkeys, hfacts, htick⟩ := hpre.seg
  obtain ⟨σ', i', hs, hi', hG', hmem', hout, hpc', hmi', hregs, hframe⟩ :=
    segEval_sound bs c.σ c.tick c.steps pc0 vm L lds hG hpc hmi hL hkeys hfacts hwf htick
  rw [hmem] at hmem'
  refine ⟨⟨σ', i', c.steps + evalBlocksFuel bs⟩, hs, ?_⟩
  exact
    { good := hG'
      tick := hi'
      mem := hmem'
      pc := hpc'
      minstret := hmi'
      regs := hregs
      keep := gholds_keep_of_frame keep hfr.1 hframe hpre.keep
      out := hout.trans hpre.out
      pw := (hframe Register.htif_payload_writes (by decide)
        (fun m hm => (hfr.2 m hm).1)).trans hpre.pw
      th := by
        obtain ⟨v, hv⟩ := hpre.th
        exact ⟨v, (hframe Register.htif_tohost (by decide)
          (fun m hm => (hfr.2 m hm).2)).trans hv⟩ }

#print axioms segRowFramed

end Vsa.Sim
