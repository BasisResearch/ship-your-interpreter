import EnvGetLookupEntry

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

namespace Vsa.Sim.EnvGetReflected
open RuntimeOwnership

/-- Owned copy data for the binding selected by the reached machine index. -/
structure OwnedLookupHit
    (N : NativeAddrs) (A : Arena) (phiF phiC : Vsa.While.Addr → Nat)
    (shared : Nat → Prop) (s : Vsa.While.Store) (query : String) (v : Vsa.While.Value)
    (out sp : BitVec 64) (fa : Nat) (f : Vsa.While.Frame) (i pv : Nat) (c : Config) : Prop where
  source : EnvGetOwnedSource c.σ.mem N phiF phiC shared s query v fa f i pv
  access : EnvGetSourceAccess c.σ.mem A pv i
  envPointer : (BitVec.ofNat 64 (phiF fa)).toNat = phiF fa
  good : GoodState c.σ
  loaded : Code.Env_getLoaded c.σ.mem
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some 0x80002c70#64
  regs : GHolds c.σ (env_getX2c70L (BitVec.ofNat 64 (phiF fa)) (BitVec.ofNat 64 i) out)
  stack : c.σ.regs.get? Register.x2 = some sp

/-- Recover ownership at the actual successful scan endpoint. The frame,
binding, and first-match index are those retained by the machine loop. -/
theorem LookupExit.owned_hit
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {phiF phiC : Vsa.While.Addr → Nat} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {s : Vsa.While.Store}
    {query : String} {v : Vsa.While.Value} {name out sp : BitVec 64}
    {m0 : Mem} {before after : Config}
    (D : LookupData N A SL phiF phiC alloc exts shared s query name m0)
    (h : LookupExit N phiF phiC s query v name out sp m0 before after) :
    ∃ fa f i pv, OwnedLookupHit N A phiF phiC shared s query v out sp fa f i pv after := by
  cases h.position with
  | head _ _ hpc _ => exact False.elim (h.exited hpc)
  | @hit fa f pn i g hframe hi hbinding hp =>
      obtain ⟨hfa, helem⟩ := Array.getElem?_eq_some_iff.mp hframe
      have hfr : FrameRepr m0 N phiF phiC (phiF fa) f := by
        simpa only [helem] using D.repr.frames fa hfa
      have hfo : FrameOwned m0 phiF alloc shared fa f := by
        simpa only [helem] using D.owned.frames fa hfa
      obtain ⟨pv, hpv, hvalue⟩ := frame_slot_valueRepr m0 N phiF phiC (phiF fa) f i hfr hi
      have hsource : EnvGetOwnedSource m0 N phiF phiC shared s query v fa f i pv :=
        { frame := hframe
          index := hi
          binding := hbinding
          first := fun j hj => hp.earlier j (Nat.lt_trans hj hi) hj
          values := hpv
          repr := by simpa only [hbinding] using hvalue
          owned := by simpa only [hbinding] using hfo.values pv hpv i hi }
      have haccess := hsource.access D.owned D.ledger D.arrays D.arenaHi
      exact ⟨fa, f, i, pv,
        { source := hp.mem.symm ▸ hsource
          access := hp.mem.symm ▸ haccess
          envPointer := D.framePointer hfa
          good := hp.good
          loaded := hp.loadedG
          tick := hp.tick
          pc := hp.pc
          regs := ⟨by simpa [gprGet] using hp.env4,
            by simpa [gprGet] using hp.idx0,
            by simpa [gprGet] using hp.out5, trivial⟩
          stack := hp.sp2 }⟩

#print axioms LookupExit.owned_hit

end Vsa.Sim.EnvGetReflected
