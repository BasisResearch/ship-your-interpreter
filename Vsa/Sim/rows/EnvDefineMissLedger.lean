import Vsa.Sim.rows.EnvDefineContractUpdate
import Vsa.Sim.rows.EnvNewContractSupply
import Vsa.Sim.AllocRuns
import Vsa.Sim.Code.FixedImage_Strlen
import Vsa.Sim.Code.FixedImage_Memcpy

/-!
# `EnvDefineMissLedger` — the external facts of the `env_define` miss lanes

A miss (`x` bound nowhere in the frame at `env`) copies the name and appends
it, growing the frame's arrays through `realloc` when full or on the empty
frame.  The callee contracts the landed specs state (`strlen_spec_framed`,
`MallocContract.spec`, `memcpy_spec_framed_{byte,word}`, `ReallocOps`) carry
neither the console output nor byte presence, which `EnvDefineReturnState`
demands; the four runs below restate each contract with exactly those clauses
(the supplier of each is the landed spec plus the observation that the callee
executes no HTIF store and only inserts bytes).  `EnvDefineMissLedger` collects
the runs with the allocator-footprint discipline and the request bounds, each
field naming its supplier.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

/-! ## 2. The miss ledger -/

/-- **The external ledger of the miss lanes** (append, grow, empty frame): the
facts neither `EnvDefineMem` nor `EnvDefineUpdateLedger` carry.  Each field
names its supplier. -/
structure EnvDefineMissLedger (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent) : Prop where
  /-- The run-global allocator ledger: the `malloc`/`free`/`realloc`/`strlen`/
  `memcpy` runs, the private footprint's arena residence, the arena/stack/HTIF
  geometry, the footprint discipline and the request ceilings
  (`Vsa/Sim/AllocRuns.lean`).  ONE field per entry, not a restatement. -/
  alloc : AllocLedger A SL gpv headroom maxReq M
  /-- The queried name's bytes are RAM off the HTIF window and the `strlen`
  text (`StrRegions`; the parser's script region). -/
  name_regions : StrRegions aName x.length
  /-- The queried name is 8-aligned (`strlen`'s aligned fast path; the parser's
  aligned identifier copies). -/
  name_align : aName.toNat % 8 = 0
  /-- The queried name's bytes, with the terminator, lie in the arena (the
  parser's `strdup` of every identifier; the interpreter's AST ownership). -/
  name_arena : A.contains aName.toNat (x.length + 1)
  /-- The names array is 8-aligned (allocator alignment recorded by the frame's
  creation contract). -/
  names_aligned : ∀ names, read64 m (φf env + 8) = some names → names % 8 = 0
  /-- The copied name takes one of `memcpy`'s two landed routes: at most 71
  bytes with the terminator (the source identifier length bound; the large
  aligned word loop is outside every landed `memcpy` spec). -/
  copy_fit : 8 * ((x.length + 1) / 8) ≤ 64
  /-- Request bounds (concrete at M6): the copied name, the grown arrays
  (`2*cap` slots of 8 and 24 bytes), and the empty frame's first arrays
  (8 slots: 64 and 192 bytes). -/
  copy_req : x.length + 1 ≤ maxReq
  grow_req : ∀ cap, read32 m (φf env + 4) = some cap → 48 * cap ≤ maxReq

end Vsa.Sim
