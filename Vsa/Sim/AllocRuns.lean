import Vsa.Sim.ReallocSpec
import Vsa.Sim.StrlenSpec
import Vsa.Sim.MemcpySpecFramedWord
import Vsa.Sim.Code.FixedImage_Strlen
import Vsa.Sim.Code.FixedImage_Memcpy
import Vsa.Sim.AllocOff

/-!
# `AllocRuns` — the allocator's callee runs and the run-global ledger

The runs each allocating site needs, and the one record that bundles them, must
sit BELOW every per-entry ledger that carries them.  They did not: `MallocRun`
was declared in `rows/EnvNewContractSupply.lean` and the `realloc`/`strlen`/
`memcpy` runs in `rows/EnvDefineMissLedger.lean`, while `AllocLedger` bundles all
four and imports the latter — so no per-entry ledger could take an `AllocLedger`
field without an import cycle, and each went on restating the allocator fields
itself.

This module is that preparatory move.  It holds the runs (`MallocRun`, `FreeRun`,
`ReallocRun`/`ReallocInstance`, `StrlenRun`, `MemcpyRun`), each being the landed
callee contract plus the clauses it omits — no console output and no byte
removal — and the run-global `AllocLedger` with `AInvAt` and its transport
lemmas.  The call adapters stay in `Vsa/Sim/AllocLedger.lean`, above the
per-entry ledgers they serve.

Nothing here is new: every declaration moved verbatim from one of those three
files.  What changes is only that a per-entry ledger may now hold ONE `alloc`
field instead of restating the allocator.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.RuntimeOwnership

/-! ## 1. The `malloc` run -/

/-- `MallocContract.spec`'s precondition, named. -/
structure MallocEntry (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (n : Nat)
    (spv r : BitVec 64) (m0 : Mem) (out : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 mallocEntry)
  a0 : c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 n)
  ra : c.σ.regs.get? Register.x1 = some r
  ra_align : r.toNat % 4 = 0
  sp : c.σ.regs.get? Register.x2 = some spv
  stack : StackOK SL spv headroom
  gp : c.σ.regs.get? Register.x3 = some gpv
  frame : ∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R
  ainv : M.AInv c.σ exts
  mem : c.σ.mem = m0
  out : c.σ.sailOutput = out

/-- `MallocContract.spec`'s postcondition, named, plus the two clauses the
abstract contract omits: the console output is unchanged and no byte is
removed. -/
structure MallocExit (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (n : Nat)
    (spv r : BitVec 64) (m0 : Mem) (out : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some r
  sp : c.σ.regs.get? Register.x2 = some spv
  gp : c.σ.regs.get? Register.x3 = some gpv
  frame : ∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R
  result : (c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧ M.AInv c.σ exts) ∨
    (∃ p, c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
      p ≠ 0 ∧ p % 16 = 0 ∧ A.contains p n ∧
      (∀ e ∈ exts, ExtDisjoint (p, n) e) ∧
      M.AInv c.σ ((p, n) :: exts))
  mem_frame : ∀ a, ¬ M.privFoot a → ¬ (SL.lo ≤ a ∧ a < spv.toNat) → c.σ.mem[a]? = m0[a]?
  out : c.σ.sailOutput = out
  mem_extends : MemExtends m0 c.σ.mem

/-- **The allocator run.**  `MallocContract.spec` (the same pre and post, named)
with the two clauses it omits.  Supplier: the verified-allocator proof behind
`MallocContract.spec`; `malloc` writes no HTIF output and the machine's stores
only insert bytes (`memExtends_applyW`). -/
def MallocRun {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (n : Nat)
    (sp r : BitVec 64) (m0 : Mem) (out : Array String),
    n ≤ maxReq →
    Triple (MallocEntry A SL gpv headroom maxReq M g exts n sp r m0 out)
      (MallocExit A SL gpv headroom maxReq M g exts n sp r m0 out)

/-! ## 2. The `realloc`, `strlen` and `memcpy` runs -/

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


/-! ## 3. The `free` run -/

/-- `MallocContract.freeSpec`'s precondition, named: the block `q` of size `n`
is live and at the head of the abstract list. -/
structure FreeEntry (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (q n : Nat)
    (spv r : BitVec 64) (m0 : Mem) (out : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 freeEntry)
  a0 : c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 q)
  ra : c.σ.regs.get? Register.x1 = some r
  ra_align : r.toNat % 4 = 0
  sp : c.σ.regs.get? Register.x2 = some spv
  stack : StackOK SL spv headroom
  gp : c.σ.regs.get? Register.x3 = some gpv
  frame : ∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R
  ainv : M.AInv c.σ ((q, n) :: exts)
  mem : c.σ.mem = m0
  out : c.σ.sailOutput = out

/-- `MallocContract.freeSpec`'s postcondition, named, plus the console output
and byte presence clauses the abstract contract omits. -/
structure FreeExit (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (q n : Nat)
    (spv r : BitVec 64) (m0 : Mem) (out : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some r
  sp : c.σ.regs.get? Register.x2 = some spv
  gp : c.σ.regs.get? Register.x3 = some gpv
  frame : ∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R
  ainv : M.AInv c.σ exts
  mem_frame : ∀ a, ¬ M.privFoot a → ¬ (q ≤ a ∧ a < q + n) →
    ¬ (SL.lo ≤ a ∧ a < spv.toNat) → c.σ.mem[a]? = m0[a]?
  out : c.σ.sailOutput = out
  mem_extends : MemExtends m0 c.σ.mem

/-- **The `free` run.**  `MallocContract.freeSpec` (named) with the two clauses it
omits.  Supplier: the verified-allocator proof behind `MallocContract.freeSpec`;
`free` writes no HTIF output and the machine's stores only insert bytes. -/
def FreeRun {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (q n : Nat)
    (sp r : BitVec 64) (m0 : Mem) (out : Array String),
    Triple (FreeEntry A SL gpv headroom maxReq M g exts q n sp r m0 out)
      (FreeExit A SL gpv headroom maxReq M g exts q n sp r m0 out)

/-! ## 4. The run-global ledger -/

/-- **The run-global allocator ledger.**  One record per run: the callee runs
and the footprint discipline every allocating call site consumes.  Each field
names its supplier; none depends on an entry. -/
structure AllocLedger (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (M : MallocContract A SL gpv headroom maxReq) : Prop where
  /-- `MallocContract.spec` with silence and presence (`MallocRun`). -/
  malloc : MallocRun M
  /-- `MallocContract.freeSpec` with silence and presence (`FreeRun`). -/
  free : FreeRun M
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
  -- discipline: allow(R14-alloc-ledger-field) the canonical run-global home
  priv_arena : ∀ a, M.privFoot a → A.lo ≤ a ∧ a < A.hi
  /-- The arena is RAM above the HTIF window (linker script, M6). -/
  -- discipline: allow(R14-alloc-ledger-field) the canonical run-global home
  arena_htif : tohostAddr + 16 ≤ A.lo
  arena_hi : A.hi ≤ 0x100000000
  /-- The arena and the stack region are disjoint (linker script, M6). -/
  arena_stack : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo
  /-- The allocator invariant reads only `gp` and the allocator-private bytes
  (the `MallocContract` footprint discipline: `privFoot` is the allocator's
  whole state; live extents are caller data). -/
  -- discipline: allow(R14-alloc-ledger-field) the canonical run-global home
  ainv_private : ∀ (exts : List Extent) (σa σb : MState),
    σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
    (∀ a, M.privFoot a → σa.mem[a]? = σb.mem[a]?) →
    M.AInv σa exts → M.AInv σb exts
  /-- The abstract live list is a set: the invariant is stable under
  reordering (dlmalloc keeps no order on the caller's live blocks; the list is
  the specification's own bookkeeping). -/
  ainv_perm : ∀ (σ : MState) (exts exts' : List Extent),
    exts.Perm exts' → M.AInv σ exts → M.AInv σ exts'
  /-- The allocator's stack headroom fits under the largest interpreter helper
  frame that calls it (`env_define`'s 64 bytes under the 1088-byte budget;
  concrete at M6). -/
  headroom_le : headroom + 64 ≤ 1088
  /-- The largest fixed request (the empty frame's first value array, 192 bytes)
  is within the interpreter's static ceiling (concrete at M6). -/
  init_req : 192 ≤ maxReq

namespace AllocLedger

variable {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
  {M : MallocContract A SL gpv headroom maxReq}

/-- `env_new`'s fixed 32-byte request is under the ceiling. -/
theorem req32 (L : AllocLedger A SL gpv headroom maxReq M) : 32 ≤ maxReq := by
  have := L.init_req; omega

theorem arena_ram (L : AllocLedger A SL gpv headroom maxReq M) :
    0x80000000 ≤ A.lo ∧ A.hi ≤ 0x100000000 := by
  have h := L.arena_htif
  have ht : tohostAddr = 0x8001ad00 := rfl
  exact ⟨by omega, L.arena_hi⟩

/-- Private bytes are off any stack window below `hi ≤ SL.hi`. -/
theorem priv_off_stack (L : AllocLedger A SL gpv headroom maxReq M)
    {hi : Nat} (hhi : hi ≤ SL.hi) {a : Nat} (hp : M.privFoot a) :
    ¬ (SL.lo ≤ a ∧ a < hi) := by
  have hA := L.priv_arena a hp
  rcases L.arena_stack with h | h <;> omega

end AllocLedger

/-! ## 5. The allocator invariant at a memory -/

/-- The allocator invariant at memory `m` with the pinned `gp`: exactly the
`ainv_entry` field shape of the per-entry ledgers. -/
def AInvAt {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (gpv : BitVec 64) (m : Mem)
    (exts : List Extent) : Prop :=
  ∀ σ : MState, σ.regs.get? Register.x3 = some gpv → σ.mem = m → M.AInv σ exts

namespace AllocLedger

variable {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
  {M : MallocContract A SL gpv headroom maxReq}

/-- The invariant at a state is the invariant at its memory. -/
theorem ainvAt_of_state (L : AllocLedger A SL gpv headroom maxReq M)
    {σ : MState} {exts : List Extent}
    (hgp : σ.regs.get? Register.x3 = some gpv) (h : M.AInv σ exts) :
    AInvAt M gpv σ.mem exts :=
  fun σ' hgp' hm => L.ainv_private exts σ σ' (hgp.trans hgp'.symm) (fun _ _ => by rw [hm]) h

theorem ainvAt_at_state {σ : MState} {exts : List Extent} {m : Mem}
    (h : AInvAt M gpv m exts) (hgp : σ.regs.get? Register.x3 = some gpv)
    (hm : σ.mem = m) : M.AInv σ exts :=
  h σ hgp hm

/-- The invariant survives any memory change off the private bytes. -/
theorem ainvAt_transport (L : AllocLedger A SL gpv headroom maxReq M)
    {m m' : Mem} {exts : List Extent} (h : AInvAt M gpv m exts)
    (hag : ∀ a, M.privFoot a → m[a]? = m'[a]?) : AInvAt M gpv m' exts := by
  intro σ' hgp' hm'
  have hσ : M.AInv { σ' with mem := m } exts := h _ hgp' rfl
  refine L.ainv_private exts { σ' with mem := m } σ' rfl ?_ hσ
  intro a hp
  show m[a]? = σ'.mem[a]?
  rw [hm']
  exact hag a hp

/-- The invariant survives any memory change inside a stack window. -/
theorem ainvAt_transport_offStack (L : AllocLedger A SL gpv headroom maxReq M)
    {m m' : Mem} {exts : List Extent} {hi : Nat} (hhi : hi ≤ SL.hi)
    (h : AInvAt M gpv m exts)
    (hag : ∀ a, ¬ (SL.lo ≤ a ∧ a < hi) → m[a]? = m'[a]?) : AInvAt M gpv m' exts :=
  L.ainvAt_transport h (fun a hp => hag a (L.priv_off_stack hhi hp))

/-- The per-entry `ainv_stable` field, as ONE theorem of the ledger. -/
theorem ainv_stable (L : AllocLedger A SL gpv headroom maxReq M)
    (esp : BitVec 64) (hesp : esp.toNat ≤ SL.hi) (exts : List Extent) :
    ∀ σa σb : MState,
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a, ¬ (SL.lo ≤ a ∧ a < esp.toNat) → σa.mem[a]? = σb.mem[a]?) →
      M.AInv σa exts → M.AInv σb exts :=
  fun σa σb hgp hag h =>
    L.ainv_private exts σa σb hgp (fun a hp => hag a (L.priv_off_stack hesp hp)) h

/-- Live extents are off the private bytes, at any memory carrying the invariant. -/
theorem privDisjoint_of_ainvAt {m : Mem} {exts : List Extent}
    (h : AInvAt M gpv m exts) (σ : MState) (hgp : σ.regs.get? Register.x3 = some gpv) :
    ∀ e ∈ exts, ∀ k < e.2, ¬ M.privFoot (e.1 + k) :=
  M.privFoot_disjoint { σ with mem := m } exts (h _ hgp rfl)

end AllocLedger


end Vsa.Sim
