import Vsa.Sim.EnvGetReflected.EnvGetOutputTransport
import Vsa.Sim.EnvGetReflected.EnvGetFootprint
import Vsa.Sim.EnvGetSpec10

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim.EnvGetReflected
open RuntimeOwnership

/-- The complete lookup execution retains its value, owned store, caller
registers, memory footprint, and output at one return state. -/
structure LookupReturnResult
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (phiF phiC : Vsa.While.Addr → Nat) (alloc : Allocations)
    (exts : List Extent) (shared : Nat → Prop) (s : Vsa.While.Store)
    (query : String) (v : Vsa.While.Value)
    (name out sp0 r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (before after : Config) : Prop where
  steps : Steps before after
  good : GoodState after.σ
  tick : after.tick < 2
  loaded : Code.Env_getLoaded after.σ.mem
  pc : after.σ.regs.get? Register.PC = some r0
  regs : GHolds after.σ (restoreRegs (sp0 - 64#64) 1#64 r0 r8 r9 r18 r19 r20 r21)
  value : ValueWordRepr after.σ.mem N phiC out.toNat v
  owned : ValueOwned after.σ.mem shared out.toNat v
  data : LookupData N A SL phiF phiC alloc exts shared s query name after.σ.mem
  entryPost : ∃ m9, EnvGetEntryPost N phiC out sp0 r0 r8 r9 r18 r19 r20 r21
    before.σ.sailOutput v before.σ.mem m9 after
  extendsMemory : MemExtends before.σ.mem after.σ.mem
  outside : ∀ k, EnvGetFootprint out sp0 k → after.σ.mem[k]? = before.σ.mem[k]?
  output : after.σ.sailOutput = before.σ.sailOutput
  kept_frame : ∀ R, kept R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Compose the actual prologue, parent/frame scans, selected copy, and restore.
The entry data and static caller windows remain explicit caller obligations. -/
theorem lookup_return
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {s : Vsa.While.Store}
    {query : String} {v : Vsa.While.Value} {fa gas len pn : Nat}
    {name out sp0 r0 r8 r9 r18 r19 r20 r21 : BitVec 64} {c : Config}
    (D : LookupData N A SL phiF phiC alloc exts shared s query name c.σ.mem)
    (hw : LookupSpillWindow A SL sp0)
    (hwindow : CallerTailWindow A SL out (sp0 - 64#64))
    (hchain : LookupChain s query gas fa v)
    (hSt : PrologueHeadSt (BitVec.ofNat 64 (phiF fa)) name out sp0 r0
      r8 r9 r18 r19 r20 r21 len pn c.σ.mem c)
    (hstrcmp : Code.StrcmpLoaded c.σ.mem) (halign : r0.toNat % 4 = 0) :
    ∃ after, LookupReturnResult N A SL phiF phiC alloc exts shared s query v
      name out sp0 r0 r8 r9 r18 r19 r20 r21 c after := by
  obtain ⟨hit, hp⟩ := lookup_entry D hw hchain hSt hstrcmp
  obtain ⟨fa', f, i, pv, hh⟩ := LookupExit.owned_hit hp.data hp.toLookupExit
  have hg := hp.data.hit_geometry hh hwindow
  obtain ⟨after, ht⟩ := hit_tail hh hg r0 r8 r9 r18 r19 r20 r21 halign hp.saved
  exact ⟨after,
    { steps := hp.steps.trans ht.steps
      good := ht.good, tick := ht.tick, loaded := ht.loaded, pc := ht.pc, regs := ht.regs
      value := ht.value, owned := ht.owned
      data := hp.data.after_output hwindow ht.outside
      entryPost := ⟨hit.σ.mem,
        { toEnvGetValuePost := ht.toValuePost.output_trans hp.output, spill := hp.outside }⟩
      extendsMemory := hp.extendsMemory.trans ht.extendsMemory
      outside := fun k hk => (ht.outside k hk.1).trans (hp.outside k hk.2)
      output := ht.output.trans hp.output
      kept_frame := fun R hR => (ht.kept_frame R hR).trans (hp.kept_frame R hR) }⟩

#print axioms lookup_return

end Vsa.Sim.EnvGetReflected
