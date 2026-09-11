import Vsa.Sim.HelperCallEnvNew
import Vsa.Sim.EnvNewSuccessSuffix
import Vsa.Sim.AllocRuns
import Vsa.Sim.rows.CallClosureEnvNewMarshal

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Allocation and initialization facts retained from the actual env_new run. -/
structure EnvNewAllocationPost
    (N : NativeAddrs) {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (exts : List Extent) (st : Vsa.While.St) (env : Addr)
    (esp aEnv r p savedS0 : BitVec 64) (m : Mem) (credits : Nat) (allocated after : Config) : Prop where
  block : MallocBlock A exts 32 p.toNat
  budget : ResourceBudget A maxReq ((p.toNat, 32) :: exts) credits
  reserve : AllocationReserve A after.σ.mem ((p.toNat, 32) :: exts) maxReq credits
  initialized : EnvNewSuccessPost (esp - 16#64) p aEnv r savedS0 allocated after
  invariant : AInvAt M gpv after.σ.mem ((p.toNat, 32) :: exts)
  fresh : EnvNewFresh N A SL phiF phiC st env p
    (pushFrameMap phiF st.store.frames.size p.toNat) after.σ.mem
  agreement : AgreeP (AllocOff SL M.privFoot [(p.toNat, 32)]) m after.σ.mem

/-- Bind the retained allocation witnesses to one reached return state. -/
inductive EnvNewAllocationPost.At
    (N : NativeAddrs) {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (exts : List Extent) (st : Vsa.While.St) (env : Addr)
    (esp aEnv r : BitVec 64) (m : Mem) (credits : Nat) (after : Config) : Prop where
  | intro (p savedS0 : BitVec 64) (allocated : Config)
      (facts : EnvNewAllocationPost N M phiF phiC exts st env esp aEnv r p savedS0 m credits allocated after) :
      EnvNewAllocationPost.At N M phiF phiC exts st env esp aEnv r m credits after

/-- The ordinary return and retained allocation describe the same execution. -/
structure EnvNewRetainedReturn
    (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (exts : List Extent) (st : Vsa.While.St) (env : Addr)
    (esp aEnv r : BitVec 64) (m : Mem) (out : Array String) (credits : Nat) (after : Config) : Prop where
  exit : EnvNewReturnState g N A SL phiF phiC st env esp r m out after
  allocation : EnvNewAllocationPost.At N M phiF phiC exts st env esp aEnv r m credits after

end Vsa.Sim
