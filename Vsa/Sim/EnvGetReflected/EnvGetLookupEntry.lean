import Vsa.Sim.EnvGetReflected.EnvGetPrologueFramed
import Vsa.Sim.EnvGetReflected.EnvGetLookupLoop

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim.EnvGetReflected
open RuntimeOwnership

/-- The selected binding and its ownership at the actual copy-head memory.
Saved words and caller observations come from the same entry-to-hit execution. -/
structure EntryLookupResult
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (phiF phiC : Vsa.While.Addr → Nat) (alloc : Allocations)
    (exts : List Extent) (shared : Nat → Prop) (s : Vsa.While.Store)
    (query : String) (v : Vsa.While.Value)
    (name out sp0 r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (before after : Config) : Prop extends
    LookupExit N phiF phiC s query v name out (sp0 - 64#64) after.σ.mem before after where
  steps : Steps before after
  extendsMemory : MemExtends before.σ.mem after.σ.mem
  data : LookupData N A SL phiF phiC alloc exts shared s query name after.σ.mem
  saved : PrologueSaved after.σ.mem (sp0 - 64#64) r0 r8 r9 r18 r19 r20 r21
  outside : ∀ k, OutsideSpill sp0 k → after.σ.mem[k]? = before.σ.mem[k]?

/-- Compose the generated prologue, owned-data transport, and both lookup loops. -/
theorem lookup_entry
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {s : Vsa.While.Store}
    {query : String} {v : Vsa.While.Value} {fa gas len pn : Nat}
    {name out sp0 r0 r8 r9 r18 r19 r20 r21 : BitVec 64} {c : Config}
    (D : LookupData N A SL phiF phiC alloc exts shared s query name c.σ.mem)
    (hw : LookupSpillWindow A SL sp0)
    (hchain : LookupChain s query gas fa v)
    (hSt : PrologueHeadSt (BitVec.ofNat 64 (phiF fa)) name out sp0 r0
      r8 r9 r18 r19 r20 r21 len pn c.σ.mem c)
    (hstrcmp : Code.StrcmpLoaded c.σ.mem) :
    ∃ after, EntryLookupResult N A SL phiF phiC alloc exts shared s query v
      name out sp0 r0 r8 r9 r18 r19 r20 r21 c after := by
  obtain ⟨head, hp⟩ := prologue_framed (BitVec.ofNat 64 (phiF fa)) name out sp0 r0
    r8 r9 r18 r19 r20 r21 len pn c.σ.mem c hSt hstrcmp
  have dh : LookupData N A SL phiF phiC alloc exts shared s query name head.σ.mem :=
    D.after_spill hw hp.outside
  obtain ⟨after, hs, hl⟩ := lookup_loop dh out (sp0 - 64#64) v head
    hchain hp.registers hp.pc rfl
  exact ⟨after,
    { position := hl.mem.symm ▸ hl.position
      kept_frame := fun R hR => (hl.kept_frame R hR).trans (hp.kept_frame R hR)
      output := hl.output.trans hp.output
      exited := hl.exited
      steps := hp.steps.trans hs
      extendsMemory := hl.mem.symm ▸ hp.extendsMemory
      data := hl.mem.symm ▸ dh
      saved := hl.mem.symm ▸ hp.saved
      outside := fun k hk => (congrArg (fun m : Mem => m[k]?) hl.mem).trans
        (hp.outside k hk) }⟩

#print axioms lookup_entry

end Vsa.Sim.EnvGetReflected
