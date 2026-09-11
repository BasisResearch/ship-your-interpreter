import Vsa.Sim.EnvGetReflected.EnvGetLookupData
import Vsa.Sim.EnvGetRecursive

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config Steps)
open Vsa.Logic (Triple)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim.EnvGetReflected
open RuntimeOwnership

section Invariant

variable (N : NativeAddrs) (phiF phiC : Vsa.While.Addr → Nat)
    (s : Vsa.While.Store) (query : String) (v : Vsa.While.Value)
    (name out sp : BitVec 64) (m0 : Mem)

/-- Successful lookup is at a parent-count head or the selected binding's copy head. -/
inductive LookupPosition (c : Config) : Prop where
  | head {fa gas : Nat} {ra : BitVec 64}
      (hchain : LookupChain s query gas fa v)
      (registers : FrameRegisters (BitVec.ofNat 64 (phiF fa)) name out ra sp c)
      (pc : c.σ.regs.get? Register.PC = some 0x80002c40#64)
      (mem : c.σ.mem = m0)
  | hit {fa : Nat} {f : Vsa.While.Frame} {pn : BitVec 64} {i : Nat}
      {g : (R : Register) → Option (RegisterType R)}
      (frame : s.frames[fa]? = some f)
      (index : i < f.vars.length)
      (binding : f.vars[i] = (query, v))
      (point : ScanLoopPoint (BitVec.ofNat 64 (phiF fa)) name out
        (BitVec.ofNat 64 f.vars.length) pn sp f query N phiF phiC m0
        g 0x80002c70#64 0x80002c6c#64 i c)

/-- The parent loop retains the caller's register frame and output. -/
structure LookupInv (before c : Config) : Prop where
  position : LookupPosition N phiF phiC s query v name out sp m0 c
  kept_frame : ∀ R, kept R = true → c.σ.regs.get? R = before.σ.regs.get? R
  output : c.σ.sailOutput = before.σ.sailOutput

structure LookupExit (before c : Config) : Prop extends
    LookupInv N phiF phiC s query v name out sp m0 before c where
  exited : c.σ.regs.get? Register.PC ≠ some 0x80002c40#64

end Invariant

section Loop

variable {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {s : Vsa.While.Store}
    {query : String} {name : BitVec 64} {m0 : Mem}

/-- One frame scan either selects the source binding or descends to an older frame. -/
theorem lookup_loop_body
    (D : LookupData N A SL phiF phiC alloc exts shared s query name m0)
    (out sp : BitVec 64) (v : Vsa.While.Value) (before : Config) (n : Nat) :
    Triple
      (fun c => LookupInv N phiF phiC s query v name out sp m0 before c ∧
        c.σ.regs.get? Register.PC = some 0x80002c40#64 ∧ lookupMeasure s phiF c = n)
      (fun c => LookupInv N phiF phiC s query v name out sp m0 before c ∧
        lookupMeasure s phiF c < n) := by
  intro c hc
  obtain ⟨hInv, hguard, hn⟩ := hc
  cases hInv.position with
  | hit hframe hi hbinding hp =>
      exact False.elim ((by decide : (0x80002c70#64) ≠ (0x80002c40#64))
        (Option.some.inj (hp.pc.symm.trans hguard)))
  | @head fa gas ra hchain hregs hpc hmem =>
      obtain ⟨f, hframe⟩ := hchain.headFrame
      obtain ⟨hfa, helem⟩ := Array.getElem?_eq_some_iff.mp hframe
      have hmeasure : fa + 1 = n := (D.measure_head hfa hpc hregs.env4).symm.trans hn
      obtain ⟨pn, hstate⟩ := D.frame_state hframe hregs hmem
      obtain ⟨scanned, hs⟩ := frame_scan (BitVec.ofNat 64 (phiF fa)) name out pn ra sp
        f query N phiF phiC c hstate hpc
      cases hs.outcome with
      | @hit g i hp hi hfound =>
          have hbinding : f.vars[i] = (query, v) := by
            cases hchain with
            | @hit gas fa frame value hf hfirst =>
                have heq : frame = f := Option.some.inj (hf.symm.trans hframe)
                subst frame
                exact Option.some.inj (hfound.symm.trans hfirst.find?_eq_some)
            | @parent gas fa frame parent value hf hmiss hparent htail =>
                have heq : frame = f := Option.some.inj (hf.symm.trans hframe)
                subst frame
                rw [hmiss.find?_eq_none] at hfound
                contradiction
          have hz : lookupMeasure s phiF scanned = 0 := lookupMeasure_exit hp.pc (by decide)
          refine ⟨scanned, hs.steps,
            { position := .hit hframe hi hbinding (hmem ▸ hp)
              kept_frame := fun R hR => (hs.kept_frame R hR).trans (hInv.kept_frame R hR)
              output := hs.output.trans hInv.output }, ?_⟩
          omega
      | miss hmissState hmissPC hmissMem hnone =>
          cases hchain with
          | @hit gas fa frame value hf hfirst =>
              have heq : frame = f := Option.some.inj (hf.symm.trans hframe)
              subst frame
              rw [hfirst.find?_eq_some] at hnone
              contradiction
          | @parent gas fa frame parent value hf hmiss hparent htail =>
              have heq : frame = f := Option.some.inj (hf.symm.trans hframe)
              subst frame
              obtain ⟨next, hp⟩ := frame_parent hmissState hmissPC hparent
              have hlt : parent < fa := D.parents fa hfa parent (by
                simpa only [helem] using hparent)
              have hparentBound : parent < s.frames.size := Nat.lt_trans hlt hfa
              have hnextMeasure : lookupMeasure s phiF next = parent + 1 :=
                D.measure_head hparentBound hp.pc hp.env
              refine ⟨next, hs.steps.trans hp.steps,
                { position := .head htail hp.registers hp.pc
                    (hp.mem.trans (hmissMem.trans hmem))
                  kept_frame := fun R hR => (hp.kept_frame R hR).trans
                    ((hs.kept_frame R hR).trans (hInv.kept_frame R hR))
                  output := hp.output.trans (hs.output.trans hInv.output) }, ?_⟩
              change lookupMeasure s phiF next < n
              rw [hnextMeasure, ← hmeasure]
              exact Nat.succ_lt_succ hlt

/-- Fold the generated parent loop and retain the successful source lookup. -/
theorem lookup_loop
    (D : LookupData N A SL phiF phiC alloc exts shared s query name m0)
    (out sp : BitVec 64) (v : Vsa.While.Value)
    {fa gas : Nat} {ra : BitVec 64} (c : Config)
    (hchain : LookupChain s query gas fa v)
    (hregs : FrameRegisters (BitVec.ofNat 64 (phiF fa)) name out ra sp c)
    (hpc : c.σ.regs.get? Register.PC = some 0x80002c40#64)
    (hmem : c.σ.mem = m0) :
    ∃ after, Steps c after ∧ LookupExit N phiF phiC s query v name out sp m0 c after := by
  have hstart : LookupInv N phiF phiC s query v name out sp m0 c c :=
    { position := .head hchain hregs hpc hmem
      kept_frame := fun _ _ => rfl
      output := rfl }
  obtain ⟨after, hs, hInv, hExit⟩ :=
    loopFromBody (lookupMeasure s phiF) (lookup_loop_body D out sp v c) c hstart
  exact ⟨after, hs, { hInv with exited := hExit }⟩

/-- A successful lookup exits at the actual value-copy head. -/
theorem LookupExit.pc
    {out sp : BitVec 64} {v : Vsa.While.Value} {before after : Config}
    (h : LookupExit N phiF phiC s query v name out sp m0 before after) :
    after.σ.regs.get? Register.PC = some 0x80002c70#64 := by
  cases h.position with
  | head _ _ hpc _ => exact False.elim (h.exited hpc)
  | hit _ _ _ hp => exact hp.pc

theorem LookupExit.mem
    {out sp : BitVec 64} {v : Vsa.While.Value} {before after : Config}
    (h : LookupExit N phiF phiC s query v name out sp m0 before after) :
    after.σ.mem = m0 := by
  cases h.position with
  | head _ _ hpc _ => exact False.elim (h.exited hpc)
  | hit _ _ _ hp => exact hp.mem

end Loop

#print axioms lookup_loop_body
#print axioms lookup_loop
#print axioms LookupExit.pc
#print axioms LookupExit.mem

end Vsa.Sim.EnvGetReflected
