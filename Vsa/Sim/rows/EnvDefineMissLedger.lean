import Vsa.Sim.rows.EnvDefineContractUpdate
import Vsa.Sim.rows.EnvNewContractSupply
import Vsa.Sim.ReallocSpec
import Vsa.Sim.StrlenSpec
import Vsa.Sim.MemcpySpecFramedWord
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

/-! ## 1. The callee runs with the clauses their contracts omit -/

/-- `ReallocOps.grow`/`.null` with the console output retained and no byte
removed.  Supplier: the verified-allocator proof behind `ReallocOps`; `realloc`
writes no HTIF output and the machine's stores only insert bytes. -/
def ReallocRun {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {AInv : MState → List Extent → Prop} {privFoot : Nat → Prop}
    (_RO : ReallocOps A SL gpv headroom maxReq AInv privFoot) : Prop :=
  (∀ (g : (R : Register) → Option (RegisterType R)) (exts : List Extent)
      (pOld nOld nNew : Nat) (sp r : BitVec 64) (m0 : Mem) (out : Array String),
    nNew ≤ maxReq → nOld < nNew → pOld ≠ 0 → (pOld, nOld) ∈ exts →
    Triple
      (fun c => ReallocPre SL gpv headroom AInv exts pOld nNew sp r m0 g c ∧
        c.σ.sailOutput = out)
      (fun c => ReallocPost gpv sp r g c ∧
        ReallocGrowResult A SL privFoot AInv exts pOld nOld nNew sp m0 c.σ ∧
        c.σ.sailOutput = out ∧ MemExtends m0 c.σ.mem)) ∧
  (∀ (g : (R : Register) → Option (RegisterType R)) (exts : List Extent)
      (n : Nat) (sp r : BitVec 64) (m0 : Mem) (out : Array String),
    0 < n → n ≤ maxReq →
    Triple
      (fun c => ReallocPre SL gpv headroom AInv exts 0 n sp r m0 g c ∧
        c.σ.sailOutput = out)
      (fun c => ReallocPost gpv sp r g c ∧
        ReallocNullResult A SL privFoot AInv exts n sp m0 c.σ ∧
        c.σ.sailOutput = out ∧ MemExtends m0 c.σ.mem))

/-- A `realloc` operation instance with its run. -/
inductive ReallocInstance (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (AInv : MState → List Extent → Prop)
    (privFoot : Nat → Prop) : Prop where
  | intro (ops : ReallocOps A SL gpv headroom maxReq AInv privFoot) (run : ReallocRun ops)

/-- `strlen_spec_framed` with the console output retained (its post keeps the
memory, so presence is immediate).  Supplier: `strlen_spec_framed` plus the
observation that `strlen` executes no HTIF store. -/
def StrlenRun : Prop :=
  ∀ (p r : BitVec 64) (s : String) (m0 : Mem)
    (g : (R : Register) → Option (RegisterType R)) (out : Array String),
    Triple
      (fun c => strlen_pre p r s m0 c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧ c.σ.sailOutput = out)
      (fun c => strlen_post r s m0 c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧ c.tick < 2 ∧
        c.σ.sailOutput = out)

/-- `memcpy_spec_framed_byte`/`_word` (the two landed routes, under the
disjunction of exactly their route hypotheses) with the console output
retained.  Supplier: the two framed specs plus the observation that `memcpy`
executes no HTIF store.  The large aligned route (`8 * (n / 8) > 64`) is
outside every landed `memcpy` spec; the copied name's length is bounded by
`copy_fit` below. -/
def MemcpyRun : Prop :=
  ∀ (gm : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat)
    (m0 : Mem) (bs : Nat → BitVec 8) (out : Array String),
    r.toNat % 4 = 0 →
    (((src.toNat ^^^ dst.toNat) % 8 ≠ 0 ∨ n < 8) ∨
      ((src.toNat ^^^ dst.toNat) % 8 = 0 ∧ 8 ≤ n ∧ dst.toNat % 8 = 0 ∧ 8 * (n / 8) ≤ 64)) →
    Triple
      (fun c => PreDispatch gm r dst src n m0 bs c ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R) ∧ c.σ.sailOutput = out)
      (fun c => (∃ g', memcpy_bytepath_post g' r dst n m0 bs c) ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R) ∧ c.σ.sailOutput = out)

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
  /-- The allocator run with silence and presence (`MallocRun`:
  `MallocContract.spec` plus the two clauses it omits). -/
  malloc : MallocRun M
  /-- A `realloc` operation instance over the same allocator state and private
  footprint, with silence and presence (`ReallocRun`). -/
  realloc : ReallocInstance A SL gpv headroom maxReq M.AInv M.privFoot
  /-- `strlen` with the console output retained (`StrlenRun`). -/
  strlen : StrlenRun
  /-- `memcpy` on both landed routes with the console output retained
  (`MemcpyRun`). -/
  memcpy : MemcpyRun
  /-- The allocator-private footprint lies inside the arena (the allocator's
  metadata and reent state are arena-resident; linker script, M6). -/
  priv_arena : ∀ a, M.privFoot a → A.lo ≤ a ∧ a < A.hi
  /-- The arena and the stack region are disjoint (linker script, M6). -/
  arena_stack : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo
  /-- The allocator invariant reads only `gp` and the allocator-private bytes,
  at every ledger (the `MallocContract` footprint discipline: `privFoot` is the
  allocator's whole state; live extents are caller data). -/
  ainv_private : ∀ (exts' : List Extent) (σa σb : MState),
    σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
    (∀ a, M.privFoot a → σa.mem[a]? = σb.mem[a]?) →
    M.AInv σa exts' → M.AInv σb exts'
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
  init_req : 192 ≤ maxReq

end Vsa.Sim
