import Vsa.Sim.TermSimAssembly

/-!
# Fixed-map obstruction at the indexed initializer exit

The former fixed-map initializer exit could alias a fresh semantic frame with
an old frame. `ExecInitExitD` now selects extended maps. Its selected frame map
must distinguish the fresh frame from every old frame, by `StoreRepr`
injectivity. The final lemma checks this property of the repaired interface.
-/

namespace Vsa.Sim

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.RuntimeRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.TermSimAssembly

/-- A map representing an allocated store cannot map its fresh frame index to
the address of any frame from the old prefix. -/
theorem storeRepr_allocFrame_fresh_ne
    {m : Vsa.MemRepr.Mem} {N : NativeAddrs} {A : Arena}
    {phiF phiC : Addr -> Nat}
    {store : Store} {parent : Option Addr}
    (hstore : StoreRepr m N A phiF phiC (store.allocFrame parent).1)
    {old : Addr} (hold : old < store.frames.size) :
    phiF old ≠ phiF (store.allocFrame parent).2 := by
  intro halias
  have hold' : old < (store.allocFrame parent).1.frames.size := by
    simpa [Store.allocFrame] using Nat.lt_succ_of_lt hold
  have hfresh : (store.allocFrame parent).2 <
      (store.allocFrame parent).1.frames.size := by
    simp [Store.allocFrame]
  have heq := hstore.φf_inj old (store.allocFrame parent).2 hold' hfresh halias
  have : old = store.frames.size := by
    simpa [Store.allocFrame] using heq
  exact (Nat.ne_of_lt hold) this

/-- Consequently, a `ForLoopReady` post over the unchanged map is impossible
whenever that map aliases the initializer's fresh frame with an old frame.
This is the fixed-map obligation that an `ExecIH` with existentially extended
maps cannot discharge. -/
theorem forLoopReady_allocFrame_alias_false
    {g : (R : Register) -> Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Addr -> Nat} {store : Store} {parent : Option Addr}
    {out : String} {d : Nat} {outer : Addr} {init : Option Stmt}
    {cnd step : Option Expr}
    {body : Stmt} {sp r aInterp aStmt aOuter aRet : BitVec 64}
    {m0 ment : Vsa.MemRepr.Mem} {cfg : Config} {liveRA : BitVec 64}
    (hready : ForLoopReady g N A SL phiF phiC
      { store := (store.allocFrame parent).1, out := out }
      d outer init cnd step body sp r aInterp aStmt aOuter aRet
      m0 ment cfg (liveRA := liveRA))
    {old : Addr} (hold : old < store.frames.size)
    (halias : phiF old = phiF (store.allocFrame parent).2) : False :=
  storeRepr_allocFrame_fresh_ne hready.store hold halias

/-- The repaired exit selects a map that distinguishes the allocated frame. -/
theorem execInitExitD_allocFrame_fresh
    {store : Store} {parent : Option Addr} {out : String} {d outer : Nat}
    {init : Option Stmt}
    (cnd step : Option Expr) (body : Stmt)
    (g : (R : Register) -> Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (phiF phiC : Addr -> Nat)
    (sp r aInterp aStmt aOuter aRet : BitVec 64)
    (m0 : Vsa.MemRepr.Mem) (cfg : Config)
    (hdone : ExecInitExitD g N A SL phiF phiC store.frames.size store.closures.size
      { store := (store.allocFrame parent).1, out := out } d outer init cnd step body
      sp r aInterp aStmt aOuter aRet m0 cfg)
    {old : Addr} (hold : old < store.frames.size)
    : ∃ phiF' phiC' liveRA,
      ExecInitExit g N A SL phiF phiC store.frames.size store.closures.size
        { store := (store.allocFrame parent).1, out := out } d outer init cnd step body
        sp r aInterp aStmt aOuter aRet m0 cfg phiF' phiC' liveRA ∧
      phiF' old ≠ phiF' (store.allocFrame parent).2 := by
  obtain ⟨phiF', phiC', liveRA, hpost⟩ := hdone.result
  exact ⟨phiF', phiC', liveRA, hpost,
    storeRepr_allocFrame_fresh_ne hpost.ready.store hold⟩

end Vsa.Sim

#print axioms Vsa.Sim.storeRepr_allocFrame_fresh_ne
#print axioms Vsa.Sim.forLoopReady_allocFrame_alias_false
#print axioms Vsa.Sim.execInitExitD_allocFrame_fresh
