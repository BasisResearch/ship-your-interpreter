import Vsa.Sim.AllocMallocAdapters
import Vsa.Sim.AllocOff
import Vsa.Sim.rows.EnvDefineCallRuns
import Vsa.Sim.rows.EnvDefineAppendClosed
import Vsa.Sim.rows.EnvDefineTailFramed
import Vsa.Sim.RuntimeOwnershipArrays

/-!
# `EnvDefineAppendLane` — the append head to the `env_define` return

The append head (`0x80002b1c`, `EnvDefineAppendHead`) is reached three ways:
from the cap dispatch of a non-empty frame, from the empty frame's `cap ≠ 0`
route, and from the grow rejoin.  From it the helper runs `strlen` (the
name), `malloc` (the copy), `memcpy`, the five-store append block and the
shared epilogue.  `envDefineAppendLane` composes those over the ledger's runs
(`StrlenRun`, `MallocRun`, `MemcpyRun`; the memory transported through each
callee's public frame by runtime ownership) to `EnvDefineReturnState`:
`Store.define` appends, and the store side is `frameRepr_append`
(`appendStoreReadback`) plus `storeDefineAdvance_of_append`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.MemRepr Vsa.RuntimeRepr
open Vsa.Alloc (AbiPreserved StackLayout StackOK MallocContract ExtDisjoint)
open Vsa.Sim.Code (Env_defineLoaded StrlenLoaded MemcpyLoaded FixedTextLoaded)
open Vsa.While (Addr Value)
open Vsa.Sim.RuntimeOwnership (HeapOwned ValueOwned SharedCString Allocated ExtentByte
  Allocations)

open Vsa.Sim.TruthyCopy (abiButS0 abiButS0_noise)

namespace Vsa.Sim

/-! ## 1. Ownership transports off the live extents -/

/-- Ownership at a memory agreeing on every live extent, every shared byte
and the staged value slot, from the ownership witness at hand. -/
theorem envDefineOwned_of_agree {A : Arena} {SL : StackLayout} {exts : List Extent}
    {m m' : Mem} {φf φc : Addr → Nat} {st : Vsa.While.St} {x : String}
    {aName pv : BitVec 64} {v : Value} {P : Nat → Prop}
    {alloc : Allocations} {shared readable writes : Nat → Prop}
    (hheap : HeapOwned A exts m φf φc alloc shared readable writes st.store)
    (hstack : ∀ k, SL.lo ≤ k → k < SL.hi → writes k)
    (hval : ValueOwned m shared pv.toNat v)
    (hname : SharedCString m shared aName.toNat x)
    (hag : AgreeP P m m')
    (hExt : ∀ e ∈ exts, ∀ k, ExtentByte e k → P k)
    (hs : ∀ k, shared k → P k)
    (hSlot : ∀ k, valHeader pv.toNat k → P k) :
    EnvDefineOwned A SL exts m' φf φc st x aName pv v :=
  ⟨alloc, shared, readable, writes,
    hheap.transport hag (fun role p n hpn k hk => hExt _ (hheap.ledger.live _ _ _ hpn) k hk) hs,
    hstack, hval.transport hag hSlot hs, hname.transport (fun k hk => hag k (hs k hk))⟩

/-- Two equal-length windows whose second is byte-wise off the first are
disjoint. -/
theorem windows_disjoint_of_off {p s n : Nat} (hn : 0 < n)
    (h : ∀ k, k < n → ¬ ExtentByte (p, n) (s + k)) : p + n ≤ s ∨ s + n ≤ p := by
  rcases Nat.lt_or_ge s (p + n) with h1 | h1
  · rcases Nat.lt_or_ge p (s + n) with h2 | h2
    · exfalso
      rcases Nat.lt_or_ge s p with h3 | h3
      · exact h (p - s) (by omega) ⟨by omega, by omega⟩
      · exact h 0 hn ⟨by omega, by omega⟩
    · exact Or.inr h2
  · exact Or.inl h1

/-! ## 2. The append head -/

/-- **The memory-side facts of a miss lane** at a memory `mA` over the live
extents `extsA`: the entry geometry, the represented store, ownership, the
staged value, the target frame's capacity word and array alignment, the miss,
and the relation to the entry memory `m`. -/
structure EnvDefineMissFacts (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (extsA : List Extent) (mA : Mem)
    (cap : Nat) : Prop where
  ra_align : r.toNat % 4 = 0
  /-- The caller's ghost holds its stack pointer (`EnvDefineEntryState.frame`). -/
  g_sp : g Register.x2 = some esp
  env_lt : env < st.store.frames.size
  env_addr : aEnv.toNat = φf env
  text : FixedTextLoaded mA
  store : StoreRepr mA N A φf φc st.store
  owned : EnvDefineOwned A SL extsA mA φf φc st x aName pv v
  word : ValueWordRepr mA N φc pv.toNat v
  cap_read : read32 mA (φf env + 4) = some cap
  names_align : ∀ pn, read64 mA (φf env + 8) = some pn → pn % 8 = 0
  vals_align : ∀ pv', read64 mA (φf env + 16) = some pv' → pv' % 8 = 0
  miss : ∀ j (hj : j < (st.store.frames[env]'env_lt).vars.length),
    ((st.store.frames[env]'env_lt).vars[j]'hj).1 ≠ x
  mem_agree : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → ¬ (SL.lo ≤ k ∧ k < esp.toNat) → mA[k]? = m[k]?
  mem_extends : MemExtends m mA

/-- **The machine side of a miss lane point**: the five argument/frame
registers, the caller's untouched registers, the saved spill image, the
stack budget and the allocator invariant at the config `c`. -/
structure EnvDefineMissRegs (g : (R : Register) → Option (RegisterType R))
    (A : Arena) (SL : StackLayout) (st : Vsa.While.St) (env : Addr)
    (esp aEnv aName pv r : BitVec 64) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (extsA : List Extent) (mA : Mem)
    (env_lt : env < st.store.frames.size) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = mA
  out : c.σ.sailOutput = out
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  sp : c.σ.regs.get? Register.x2 = some (esp - 64#64)
  gp : c.σ.regs.get? Register.x3 = some gpv
  s2 : c.σ.regs.get? Register.x18 = some aName
  s3 : c.σ.regs.get? Register.x19 =
    some (BitVec.ofNat 64 (st.store.frames[env]'env_lt).vars.length)
  s4 : c.σ.regs.get? Register.x20 = some aEnv
  s5 : c.σ.regs.get? Register.x21 = some pv
  /-- The registers the epilogue does not restore still hold the caller's. -/
  rest : ∀ R, AbiPreserved R = true → EnvDefineRestored R = false → R ≠ Register.x2 →
    c.σ.regs.get? R = g R
  saved : EnvDefineSavedSpillFrame (esp - 64#64) (envDefineSaved g r) c
  stack : StackOK SL (esp - 64#64) headroom
  ainv : M.AInv c.σ extsA

/-- **The append head** at `0x80002b1c`: the machine state the cap dispatch,
the empty frame's `cap ≠ 0` route and the grow rejoin all park at, with the
memory-side facts at its memory `mA` over the live extents `extsA` and room
for the new binding. -/
structure EnvDefineAppendHead (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (extsA : List Extent) (mA : Mem)
    (cap : Nat) (c : Config) : Prop where
  facts : EnvDefineMissFacts g N A SL φf φc st env x v esp aEnv aName pv r m extsA mA cap
  regs : EnvDefineMissRegs g A SL st env esp aEnv aName pv r out M extsA mA facts.env_lt c
  pc : c.σ.regs.get? Register.PC = some 0x80002b1c#64
  room : (st.store.frames[env]'facts.env_lt).vars.length < cap

/-! ## 3. The append footprint from ownership -/

/-- The target frame's own bytes off the three append windows, from runtime
ownership: the record, the old name slots, the old name strings, the old
value headers and payloads, the copied name (fresh) and the staged value. -/
theorem appendFootprint_of_owned {A : Arena} {exts : List Extent} {m : Mem}
    {φf φc : Addr → Nat} {alloc : Allocations} {shared readable writes : Nat → Prop}
    {s : Vsa.While.Store} {env : Addr} {cap names vals p n src : Nat}
    {x : String} {v : Value}
    (h : HeapOwned A exts m φf φc alloc shared readable writes s)
    (henv : env < s.frames.size)
    (hcap : read32 m (φf env + 4) = some cap)
    (hnames : read64 m (φf env + 8) = some names)
    (hvals : read64 m (φf env + 16) = some vals)
    (hroom : s.frames[env].vars.length < cap)
    (hfresh : ∀ e ∈ exts, ExtDisjoint (p, n) e) (hn : x.length + 1 ≤ n)
    (hsrc : ValueOwned m shared src v) :
    EnvDefineAppendFootprint m (φf env) names vals s.frames[env].vars.length p src
      s.frames[env].vars x v := by
  have hfo := h.store.frames env henv
  obtain ⟨a, harr⟩ := hfo.arrays
  have ec : a.cap = cap := Option.some.inj (harr.capRead.symm.trans hcap)
  have en : a.names = names := Option.some.inj (harr.namesRead.symm.trans hnames)
  have ev : a.values = vals := Option.some.inj (harr.valuesRead.symm.trans hvals)
  have hposCap : 0 < a.cap := by omega
  have hnA : Allocated alloc (.names env) names (8 * cap) := by
    have := harr.names.nonempty hposCap
    rwa [en, ec] at this
  have hvA : Allocated alloc (.values env) vals (24 * cap) := by
    have := harr.values.nonempty hposCap
    rwa [ev, ec] at this
  have hrA : Allocated alloc (.frame env) (φf env) 32 := hfo.record
  have nsub : ∀ k, names + 8 * s.frames[env].vars.length ≤ k ∧ k < names + 8 * s.frames[env].vars.length + 8 →
      ExtentByte (names, 8 * cap) k := by
    intro k hk
    change names ≤ k ∧ k < names + 8 * cap
    omega
  have vsub : ∀ k, vals + 24 * s.frames[env].vars.length ≤ k ∧ k < vals + 24 * s.frames[env].vars.length + 24 →
      ExtentByte (vals, 24 * cap) k := by
    intro k hk
    change vals ≤ k ∧ k < vals + 24 * cap
    omega
  have rsub : ∀ k, φf env ≤ k ∧ k < φf env + 4 → ExtentByte (φf env, 32) k := by
    intro k hk
    change φf env ≤ k ∧ k < φf env + 32
    omega
  have hsharedOut : ∀ k, shared k → AppendUntouched (φf env) names vals s.frames[env].vars.length k := by
    intro k hk
    exact ⟨h.immutable.outsideWindow (by trivial) hnA nsub k hk,
      h.immutable.outsideWindow (by trivial) hvA vsub k hk,
      h.immutable.outsideWindow (by trivial) hrA rsub k hk⟩
  have hrecOut : ∀ k, ExtentByte (φf env, 32) k → k < φf env ∨ φf env + 4 ≤ k →
      AppendUntouched (φf env) names vals s.frames[env].vars.length k := by
    intro k hk hk4
    exact ⟨h.ledger.outsideWindow hrA hnA nofun nsub k hk,
      h.ledger.outsideWindow hrA hvA nofun vsub k hk, hk4⟩
  have hnamesOut : ∀ k, ExtentByte (names, 8 * cap) k →
      (k < names + 8 * s.frames[env].vars.length ∨ names + 8 * s.frames[env].vars.length + 8 ≤ k) →
      AppendUntouched (φf env) names vals s.frames[env].vars.length k := by
    intro k hk hkw
    exact ⟨hkw, h.ledger.outsideWindow hnA hvA nofun vsub k hk,
      h.ledger.outsideWindow hnA hrA nofun rsub k hk⟩
  have hvalsOut : ∀ k, ExtentByte (vals, 24 * cap) k →
      (k < vals + 24 * s.frames[env].vars.length ∨ vals + 24 * s.frames[env].vars.length + 24 ≤ k) →
      AppendUntouched (φf env) names vals s.frames[env].vars.length k := by
    intro k hk hkw
    exact ⟨h.ledger.outsideWindow hvA hnA nofun nsub k hk, hkw,
      h.ledger.outsideWindow hvA hrA nofun rsub k hk⟩
  have hnamesMem := h.ledger.live _ _ _ hnA
  have hvalsMem := h.ledger.live _ _ _ hvA
  have hrecMem := h.ledger.live _ _ _ hrA
  have hfreshN := hfresh _ hnamesMem
  have hfreshV := hfresh _ hvalsMem
  have hfreshR := hfresh _ hrecMem
  change p + n ≤ names ∨ names + 8 * cap ≤ p at hfreshN
  change p + n ≤ vals ∨ vals + 24 * cap ≤ p at hfreshV
  change p + n ≤ φf env ∨ φf env + 32 ≤ p at hfreshR
  have hsep := h.ledger.separated _ _ _ _ _ _ hnA hvA nofun
  have hsepR := h.ledger.separated _ _ _ _ _ _ hnA hrA nofun
  have hsepVR := h.ledger.separated _ _ _ _ _ _ hvA hrA nofun
  change names + 8 * cap ≤ vals ∨ vals + 24 * cap ≤ names at hsep
  change names + 8 * cap ≤ φf env ∨ φf env + 32 ≤ names at hsepR
  change vals + 24 * cap ≤ φf env ∨ φf env + 32 ≤ vals at hsepVR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk1 hk2
    exact hrecOut k ⟨by omega, by omega⟩ (Or.inr hk1)
  · intro i hi k hk
    exact hnamesOut _ ⟨by omega, by omega⟩ (Or.inl (by omega))
  · intro i hi q hq k hk
    obtain ⟨q', hq', key⟩ := harr.keys i hi
    rw [en] at hq'
    have := Option.some.inj (hq'.symm.trans hq)
    subst this
    exact hsharedOut _ (key.immutable.bytes k hk)
  · intro i hi k hk
    unfold valHeader at hk
    exact hvalsOut k ⟨by omega, by omega⟩ (Or.inl (by omega))
  · intro i hi
    exact (hfo.values vals hvals i hi).covered hsharedOut
  · intro k hk
    exact ⟨by omega, by omega, by omega⟩
  · exact hsrc.covered hsharedOut
  · omega
  · omega
  · omega

/-- The store block's address geometry from the arena and the stack slot. -/
theorem appendStoreFactsGeom_at {A : Arena} {exts : List Extent}
    {m : Mem} {φf φc : Addr → Nat} {alloc : Allocations}
    {shared readable writes : Nat → Prop} {s : Vsa.While.Store} {env : Addr}
    {cap names vals : Nat} {aEnv pv : BitVec 64}
    (h : HeapOwned A exts m φf φc alloc shared readable writes s)
    (henv : env < s.frames.size) (henvAddr : aEnv.toNat = φf env)
    (hcap : read32 m (φf env + 4) = some cap)
    (hnames : read64 m (φf env + 8) = some names)
    (hvals : read64 m (φf env + 16) = some vals)
    (hroom : s.frames[env].vars.length < cap) (hcapS : cap < 2^31)
    (hnamesAl : names % 8 = 0) (hvalsAl : vals % 8 = 0)
    (henvAl : φf env % 8 = 0)
    (harenaRam : 0x80000000 ≤ A.lo ∧ A.hi ≤ 0x100000000)
    (harenaHtif : tohostAddr + 16 ≤ A.lo)
    (sourceLo : 0x80000000 ≤ pv.toNat) (sourceHi : pv.toNat + 24 ≤ 0x100000000)
    (sourceHtif : tohostAddr + 16 ≤ pv.toNat) (sourceAlign : pv.toNat % 8 = 0) :
    AppendStoreFactsGeom aEnv pv s.frames[env].vars.length names vals ∧
      A.contains (names + 8 * s.frames[env].vars.length) 8 ∧
      A.contains (vals + 24 * s.frames[env].vars.length) 24 ∧
      A.contains aEnv.toNat 4 := by
  have hfo := h.store.frames env henv
  obtain ⟨a, harr⟩ := hfo.arrays
  have ec : a.cap = cap := Option.some.inj (harr.capRead.symm.trans hcap)
  have en : a.names = names := Option.some.inj (harr.namesRead.symm.trans hnames)
  have ev : a.values = vals := Option.some.inj (harr.valuesRead.symm.trans hvals)
  have hposCap : 0 < a.cap := by omega
  obtain ⟨_, hnLo, hnHi⟩ := h.ledger.arena.1 _ (h.ledger.live _ _ _ (harr.names.nonempty hposCap))
  obtain ⟨_, hvLo, hvHi⟩ := h.ledger.arena.1 _ (h.ledger.live _ _ _ (harr.values.nonempty hposCap))
  obtain ⟨_, hrLo, hrHi⟩ := h.ledger.arena.1 _ (h.ledger.live _ _ _ hfo.record)
  simp only at hnLo hnHi hvLo hvHi hrLo hrHi
  rw [en] at hnLo
  rw [en, ec] at hnHi
  rw [ev] at hvLo
  rw [ev, ec] at hvHi
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩,
    ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- The original caller slot supplies the same append-store geometry. -/
theorem appendStoreFactsGeom_of {A : Arena} {SL : StackLayout} {exts : List Extent}
    {m : Mem} {φf φc : Addr → Nat} {alloc : Allocations}
    {shared readable writes : Nat → Prop} {s : Vsa.While.Store} {env : Addr}
    {cap names vals : Nat} {aEnv pv esp : BitVec 64}
    (h : HeapOwned A exts m φf φc alloc shared readable writes s)
    (henv : env < s.frames.size) (henvAddr : aEnv.toNat = φf env)
    (hcap : read32 m (φf env + 4) = some cap)
    (hnames : read64 m (φf env + 8) = some names)
    (hvals : read64 m (φf env + 16) = some vals)
    (hroom : s.frames[env].vars.length < cap) (hcapS : cap < 2^31)
    (hnamesAl : names % 8 = 0) (hvalsAl : vals % 8 = 0)
    (henvAl : φf env % 8 = 0)
    (harenaRam : 0x80000000 ≤ A.lo ∧ A.hi ≤ 0x100000000)
    (harenaHtif : tohostAddr + 16 ≤ A.lo)
    (hpv : pv.toNat = esp.toNat + 16)
    (hstack : StackOK SL esp 1088) (hslot : esp.toNat + 40 ≤ SL.hi)
    (hramLo : 0x80000000 ≤ SL.lo) (hramHi : SL.hi ≤ 0x100000000)
    (hwin : tohostAddr + 16 ≤ SL.lo) :
    AppendStoreFactsGeom aEnv pv s.frames[env].vars.length names vals ∧
      A.contains (names + 8 * s.frames[env].vars.length) 8 ∧
      A.contains (vals + 24 * s.frames[env].vars.length) 24 ∧
      A.contains aEnv.toNat 4 := by
  have hsp1 := hstack.1
  have hsp2 := hstack.2.1
  have hsp3 := hstack.2.2
  exact appendStoreFactsGeom_at h henv henvAddr hcap hnames hvals hroom hcapS
    hnamesAl hvalsAl henvAl harenaRam harenaHtif
    (by omega) (by omega) (by omega) (by omega)

/-! ## 4. The lane -/

/-- The name is absent: `Store.define` takes its append branch. -/
theorem any_false_of_miss (vars : List (String × Value)) (x : String)
    (hmiss : ∀ j (hj : j < vars.length), (vars[j]'hj).1 ≠ x) :
    vars.any (·.1 == x) = false := by
  rw [List.any_eq_false]
  intro y hy
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
  simp only [beq_iff_eq]
  exact hmiss j hj

/-- **The append lane.**  From the append head, under both ledgers and the
entry facts, the helper runs to the contract's return state. -/
theorem envDefineAppendLane
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts extsA : List Extent) (mA : Mem)
    (cap : Nat)
    (hE : EnvDefineMem N A SL φf φc st env x v aEnv aName pv esp m)
    (L : EnvDefineUpdateLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (LM : EnvDefineMissLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (budget : ResourceBudget A maxReq extsA 1)
    (reserve : AllocationReserve A mA extsA maxReq 1) :
    Triple (EnvDefineAppendHead g N A SL φf φc st env x v esp aEnv aName pv r m out M extsA mA cap)
      (EnvDefineReturnState g N A SL φf φc st env x v esp r m out) := by
  intro c0 H
  -- ── geometry
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hsp1 := hE.stack.1
  have hsp2 := hE.stack.2.1
  have hsp3 := hE.stack.2.2
  have hramLo := hE.stack_ram.1
  have hramHi := hE.stack_ram.2
  have hwin := hE.stack_win
  have h64 : 64 ≤ esp.toNat := by omega
  have hsp64 : (esp - 64#64).toNat = esp.toNat - 64 := sp_sub64_toNat esp h64
  have hAlo := L.alloc.arena_ram.1
  have hAhi := L.alloc.arena_ram.2
  have hAhtif := L.alloc.arena_htif
  have hAstack := LM.alloc.arena_stack
  have hAimg := hE.arena_image
  have hpvNat := hE.pv_frame
  have hslot := hE.slot_in_stack
  have henvLt := H.facts.env_lt
  have hroom : (st.store.frames[env]).vars.length < cap := H.room
  obtain ⟨alloc, shared, readable, writes, hheap, hstackW, hvalO, hnameO⟩ := H.facts.owned
  have hfo := hheap.store.frames env henvLt
  obtain ⟨arr, harr⟩ := hfo.arrays
  obtain ⟨hcountR, ⟨cap0, hcap0, hcaple⟩, ⟨pn, pvals, hpn, hpvals, hslots⟩, hpar⟩ :=
    H.facts.store.frames env henvLt
  have hcapEq : cap0 = cap := Option.some.inj (hcap0.symm.trans H.facts.cap_read)
  subst cap0
  have hcapS : cap < 2^31 := hfo.capSigned hheap.ledger H.facts.cap_read (by omega)
  have ecap : arr.cap = cap := Option.some.inj (harr.capRead.symm.trans H.facts.cap_read)
  have enames : arr.names = pn := Option.some.inj (harr.namesRead.symm.trans hpn)
  have evals : arr.values = pvals := Option.some.inj (harr.valuesRead.symm.trans hpvals)
  have hposCap : 0 < arr.cap := by have := H.room; omega
  have hnA : Allocated alloc (.names env) pn (8 * cap) := by
    have := harr.names.nonempty hposCap; rwa [enames, ecap] at this
  have hvA : Allocated alloc (.values env) pvals (24 * cap) := by
    have := harr.values.nonempty hposCap; rwa [evals, ecap] at this
  have hrA : Allocated alloc (.frame env) (φf env) 32 := hfo.record
  obtain ⟨_, hnLo, hnHi⟩ := hheap.ledger.arena.1 _ (hheap.ledger.live _ _ _ hnA)
  obtain ⟨_, hvLo, hvHi⟩ := hheap.ledger.arena.1 _ (hheap.ledger.live _ _ _ hvA)
  obtain ⟨_, hrLo, hrHi⟩ := hheap.ledger.arena.1 _ (hheap.ledger.live _ _ _ hrA)
  try simp only at hnLo hnHi hvLo hvHi hrLo hrHi
  have henvGeom : EnvRecordGeom aEnv :=
    { lo := by rw [H.facts.env_addr]; omega
      hi := by rw [H.facts.env_addr]; omega
      htif := by rw [H.facts.env_addr]; omega
      align := by rw [H.facts.env_addr]; exact (H.facts.store.frames_arena env henvLt).2
      code := by rw [H.facts.env_addr]; rcases hAimg with h | h <;> omega }
  -- the four entry-side allocator separation facts, from ONE lemma (`AllocOff.lean`)
  have hprivLive : ∀ e ∈ extsA, ∀ i < e.2, ¬ M.privFoot (e.1 + i) :=
    M.privFoot_disjoint c0.σ extsA H.regs.ainv
  have EO : EntryOff A SL extsA M.privFoot alloc shared :=
    hheap.entryOff hstackW hprivLive LM.alloc.priv_arena
  have hsharedPriv := EO.shared_priv
  have hsharedStack := EO.shared_stack
  have hextArena := EO.ext_arena
  have hextPriv := EO.ext_priv
  -- the text image at any memory agreeing off the arena and the stack window
  have htextOf : ∀ m', (∀ a, ¬ (A.lo ≤ a ∧ a < A.hi) → ¬ (SL.lo ≤ a ∧ a < esp.toNat - 64) →
      m'[a]? = mA[a]?) → FixedTextLoaded m' := by
    intro m' hag
    apply H.facts.text.transport
    intro a ha0 ha1
    apply hag
    · rcases hAimg with h | h <;> omega
    · omega
  -- ── strlen
  have hcode0 : Env_defineLoaded c0.σ.mem := by
    rw [H.regs.mem]; exact H.facts.text.Env_defineLoaded
  obtain ⟨c1, S1⟩ := envDefineStrlenParked_of aName c0 H.regs.good H.pc H.regs.s2 hcode0 H.regs.tick
  have hpre1 : strlen_pre aName 0x80002b24#64 x mA c1 :=
    ⟨S1.good, by rw [S1.mem, H.regs.mem]; exact H.facts.text.StrlenLoaded, S1.mem.trans H.regs.mem, S1.pc, S1.a0,
      S1.ra, S1.minstret, S1.tick, LM.name_regions, LM.name_align, hnameO.repr, by decide⟩
  obtain ⟨c2, hs2, hpost2, habi2, htick2, hout2⟩ :=
    LM.alloc.strlen aName 0x80002b24#64 x mA (fun R => c1.σ.regs.get? R) out c1
      ⟨hpre1, fun _ _ => rfl, S1.out.trans H.regs.out⟩
  obtain ⟨hG2, hpc2, ha02, hra2, hmem2⟩ := hpost2
  -- ── malloc
  have hcopyLt : x.length + 1 < 72 := by have := LM.copy_fit; omega
  have hcode2 : Env_defineLoaded c2.σ.mem := by rw [hmem2]; exact H.facts.text.Env_defineLoaded
  obtain ⟨c3, S3⟩ := envDefineMallocParked_of x.length c2 (by omega) hG2 hpc2 ha02 hcode2 htick2
  have hx2_3 : c3.σ.regs.get? Register.x2 = some (esp - 64#64) := by
    rw [S3.abi _ (by decide), habi2 _ (by decide), S1.abi _ (by decide)]; exact H.regs.sp
  have hx3_3 : c3.σ.regs.get? Register.x3 = some gpv := by
    rw [S3.abi _ (by decide), habi2 _ (by decide), S1.abi _ (by decide)]; exact H.regs.gp
  have hainv3 : M.AInv c3.σ extsA := by
    apply LM.alloc.ainv_private extsA c0.σ c3.σ (H.regs.gp.trans hx3_3.symm) _ H.regs.ainv
    intro a _
    rw [S3.mem, hmem2, H.regs.mem]
  let g3 : (R : Register) → Option (RegisterType R) := fun R => c3.σ.regs.get? R
  have hentry3 : MallocEntry A SL gpv headroom maxReq M g3 extsA (x.length + 1) (esp - 64#64)
      0x80002b30#64 mA out c3 :=
    { good := S3.good
      tick := S3.tick
      pc := S3.pc
      a0 := S3.a0
      ra := S3.ra
      ra_align := by decide
      sp := hx2_3
      stack := H.regs.stack
      gp := hx3_3
      frame := fun _ _ => rfl
      ainv := hainv3
      mem := S3.mem.trans hmem2
      out := S3.out.trans hout2 }
  obtain ⟨c4, hs4, success4⟩ := LM.alloc.mallocSuccess g3 extsA (x.length + 1) 0
    (esp - 64#64) 0x80002b30#64 mA out c3
    (MallocSuccessEntry.of_entry hentry3 (by rw [hentry3.mem]; exact H.facts.text)
      { bounded := LM.copy_req, budget := budget
        reserve := by rw [hentry3.mem]; exact reserve })
  obtain ⟨p, result4⟩ := success4.allocated
  have X4 := success4.returned.toMallocExit (M := M) result4
  have ha04 := result4.pointer.register
  have hp0 := result4.pointer.nonzero
  have hp16 := result4.pointer.aligned
  have hpA := result4.pointer.arena
  have hpFresh := result4.disjoint
  have hainv4 := result4.ainv
  change A.lo ≤ p ∧ p + (x.length + 1) ≤ A.hi at hpA
  have hpLt : p + (x.length + 1) < 2^64 := by omega
  -- memory after malloc: agrees with `mA` off the private bytes and the window
  have hag4 : ∀ a, ¬ M.privFoot a → ¬ (SL.lo ≤ a ∧ a < esp.toNat - 64) → c4.σ.mem[a]? = mA[a]? := by
    intro a h1 h2
    apply X4.mem_frame a h1
    rw [hsp64]; exact h2
  have hag4' : ∀ a, ¬ (A.lo ≤ a ∧ a < A.hi) → ¬ (SL.lo ≤ a ∧ a < esp.toNat - 64) →
      c4.σ.mem[a]? = mA[a]? :=
    fun a h1 h2 => hag4 a (fun hp => h1 (LM.alloc.priv_arena a hp)) h2
  have htext4 : FixedTextLoaded c4.σ.mem := htextOf _ hag4'
  -- ── memcpy
  have hx8_4 : c4.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 (x.length + 1)) := by
    rw [X4.frame _ (by decide)]; exact S3.s0
  have hx18_4 : c4.σ.regs.get? Register.x18 = some aName := by
    rw [X4.frame _ (by decide)]
    show c3.σ.regs.get? Register.x18 = some aName
    rw [S3.abi _ (by decide), habi2 _ (by decide), S1.abi _ (by decide)]; exact H.regs.s2
  have hpBV : BitVec.ofNat 64 p ≠ 0#64 := by
    intro hz
    have := congrArg BitVec.toNat hz
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    exact hp0 this
  have hpNat : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨c5, S5⟩ := envDefineMemcpyParked_of (BitVec.ofNat 64 p) (BitVec.ofNat 64 (x.length + 1)) aName c4
    hpBV X4.good X4.pc ha04 hx8_4 hx18_4 htext4.Env_defineLoaded X4.tick
  -- the name bytes at the memcpy entry
  have hsharedAg5 : AgreeP shared mA c5.σ.mem := by
    intro k hk
    rw [S5.mem]
    exact (hag4 k (hsharedPriv k hk) (fun hin => hsharedStack k hk ⟨hin.1, by omega⟩)).symm
  have hname5 : SharedCString c5.σ.mem shared aName.toNat x := hnameO.transport hsharedAg5
  obtain ⟨len', bs, hlen', hstr5⟩ := cstring_bytes c5.σ.mem aName x hname5.repr
  subst hlen'
  have hnameArena := LM.name_arena
  change A.lo ≤ aName.toNat ∧ aName.toNat + (x.length + 1) ≤ A.hi at hnameArena
  have hnameOff : ∀ k, k < (x.length + 1) → ¬ ExtentByte (p, (x.length + 1)) (aName.toNat + k) := by
    intro k hk
    exact hheap.reserved.outsideFresh hpA hpFresh _ (hnameO.bytes k (by omega))
  have hdisj := windows_disjoint_of_off (by omega) hnameOff
  have hregions : Regions (BitVec.ofNat 64 p) aName (x.length + 1) :=
    { dst_nowrap := by rw [hpNat]; exact hpLt
      src_nowrap := by have := LM.name_regions.nowrap; omega
      disjoint := by rw [hpNat]; exact hdisj
      code_disjoint := by rw [hpNat]; rcases hAimg with h | h <;> omega
      dst_lo := by rw [hpNat]; omega
      dst_hi := by rw [hpNat]; omega
      src_lo := by omega
      src_hi := by omega
      dst_win := by rw [hpNat]; omega
      src_win := by omega }
  let g5 : (R : Register) → Option (RegisterType R) := fun R => c5.σ.regs.get? R
  have hpre5 : PreDispatch g5 0x80002b44#64 (BitVec.ofNat 64 p) aName (x.length + 1) c5.σ.mem bs c5 :=
    { good := S5.good
      loaded := by
        rw [S5.mem]; exact htext4.MemcpyLoaded
      pc := S5.pc
      a0 := S5.a0
      a1 := S5.a1
      a2 := S5.a2
      ra := S5.ra
      minstret := S5.minstret
      tick := S5.tick
      regions := hregions
      npos := by omega
      meminv :=
        { copied := fun k hk => absurd hk (by omega)
          outside := fun _ _ => rfl
          src_intact := by
            intro k _ hk
            by_cases hkl : k < x.length
            · exact (hstr5.chars k hkl).1
            · have hke : k = x.length := by omega
              subst hke
              exact hstr5.nul }
      hframe := fun _ _ => rfl }
  have hroute : ((aName.toNat ^^^ (BitVec.ofNat 64 p).toNat) % 8 ≠ 0 ∨ (x.length + 1) < 8) ∨
      ((aName.toNat ^^^ (BitVec.ofNat 64 p).toNat) % 8 = 0 ∧ 8 ≤ (x.length + 1) ∧
        (BitVec.ofNat 64 p).toNat % 8 = 0 ∧ 8 * ((x.length + 1) / 8) ≤ 64) := by
    rw [hpNat]
    rcases Nat.lt_or_ge (x.length + 1) 8 with hlt | hge
    · exact Or.inl (Or.inr hlt)
    · right
      have hx : (aName.toNat ^^^ p) % 8 = 0 := by
        have h := @Nat.xor_mod_two_pow aName.toNat p 3
        have h8 : (2:Nat)^3 = 8 := by decide
        rw [h8] at h
        rw [h, LM.name_align, show p % 8 = 0 by omega]
        decide
      exact ⟨hx, hge, by omega, LM.copy_fit⟩
  obtain ⟨c6, hs6, ⟨g', hbyte⟩, habi6, hout6⟩ :=
    LM.alloc.memcpy g5 0x80002b44#64 (BitVec.ofNat 64 p) aName (x.length + 1) c5.σ.mem bs out (by decide) hroute c5
      ⟨hpre5, fun _ _ => rfl, S5.out.trans (X4.out)⟩
  have hbyteK := hbyte
  obtain ⟨hG6, hpc6, ha06, hra6, hcopiedB, hout6m, htick6, _⟩ := hbyte
  -- memory after memcpy: agrees with `mA` off the private bytes, the window and the copy
  have hag6 : ∀ a, ¬ M.privFoot a → ¬ (SL.lo ≤ a ∧ a < esp.toNat - 64) →
      (a < p ∨ p + (x.length + 1) ≤ a) → c6.σ.mem[a]? = mA[a]? := by
    intro a h1 h2 h3
    rw [hout6m a (by rw [hpNat]; exact h3), S5.mem]
    exact hag4 a h1 h2
  have hag6' : ∀ a, ¬ (A.lo ≤ a ∧ a < A.hi) → ¬ (SL.lo ≤ a ∧ a < esp.toNat - 64) →
      c6.σ.mem[a]? = mA[a]? :=
    fun a h1 h2 => hag6 a (fun hp => h1 (LM.alloc.priv_arena a hp)) h2 (by omega)
  -- the footprint the store block reads: live extents, shared bytes, the value slot
  let P6 : Nat → Prop := fun k => (∃ e ∈ extsA, ExtentByte e k) ∨ shared k ∨ valHeader pv.toNat k
  have hagP6 : AgreeP P6 mA c6.σ.mem := by
    intro k hk
    apply Eq.symm
    rcases hk with ⟨e, he, hek⟩ | hk | hk
    · have hkA := hextArena e he k hek
      have hfr := hpFresh e he
      change p + (x.length + 1) ≤ e.1 ∨ e.1 + e.2 ≤ p at hfr
      change e.1 ≤ k ∧ k < e.1 + e.2 at hek
      refine hag6 k (hextPriv e he k hek) (fun hin => ?_) (by omega)
      rcases hAstack with h | h <;> omega
    · have hoff := hheap.reserved.outsideFresh hpA hpFresh k hk
      change ¬ (p ≤ k ∧ k < p + (x.length + 1)) at hoff
      exact hag6 k (hsharedPriv k hk) (fun hin => hsharedStack k hk ⟨hin.1, by omega⟩) (by omega)
    · unfold valHeader at hk
      refine hag6 k (fun hp => ?_) (by omega) (by rcases hAstack with h | h <;> omega)
      have := LM.alloc.priv_arena k hp
      rcases hAstack with h | h <;> omega
  have hExt6 : ∀ e ∈ extsA, ∀ k, ExtentByte e k → P6 k := fun e he k hk => Or.inl ⟨e, he, hk⟩
  have hsP6 : ∀ k, shared k → P6 k := fun k hk => Or.inr (Or.inl hk)
  have hSlot6 : ∀ k, valHeader pv.toNat k → P6 k := fun k hk => Or.inr (Or.inr hk)
  have hallocP6 : ∀ role q nn, Allocated alloc role q nn → ∀ k, ExtentByte (q, nn) k → P6 k :=
    fun role q nn hq k hk => hExt6 _ (hheap.ledger.live _ _ _ hq) k hk
  have hheap6 : HeapOwned A extsA c6.σ.mem φf φc alloc shared readable writes st.store :=
    hheap.transport hagP6 hallocP6 hsP6
  have hstore6 : StoreRepr c6.σ.mem N A φf φc st.store :=
    hheap.store.repr_transport H.facts.store hagP6 hallocP6 hsP6
  have hvalO6 : ValueOwned c6.σ.mem shared pv.toNat v := hvalO.transport hagP6 hSlot6 hsP6
  have hword6 : ValueWordRepr c6.σ.mem N φc pv.toNat v :=
    ⟨valueRepr_agreeP hagP6 hSlot6 (hvalO.covered hsP6) H.facts.word.repr,
      RuntimeOwnership.valueWordsTotal_transport H.facts.word.total hagP6 hSlot6⟩
  have hrecCov : ∀ k, ExtentByte (φf env, 32) k → P6 k :=
    fun k hk => hExt6 _ (hheap.ledger.live _ _ _ hrA) k hk
  have hcount6 : read32 c6.σ.mem (φf env) = some (st.store.frames[env]).vars.length := by
    rw [← read32_agreeP hagP6 (fun k hk => hrecCov _ ⟨by omega, by omega⟩)]; exact hcountR
  have hcap6 : read32 c6.σ.mem (φf env + 4) = some cap := by
    rw [← read32_agreeP hagP6 (fun k hk => hrecCov _ ⟨by omega, by omega⟩)]; exact H.facts.cap_read
  have hpn6 : read64 c6.σ.mem (φf env + 8) = some pn := by
    rw [← read64_agreeP hagP6 (fun k hk => hrecCov _ ⟨by omega, by omega⟩)]; exact hpn
  have hpv6 : read64 c6.σ.mem (φf env + 16) = some pvals := by
    rw [← read64_agreeP hagP6 (fun k hk => hrecCov _ ⟨by omega, by omega⟩)]; exact hpvals
  have hcode6 : Env_defineLoaded c6.σ.mem := (htextOf _ hag6').Env_defineLoaded
  have hcopied6 : CString c6.σ.mem p x := by
    have := envDefineMemcpyPostCString g' p (x.length + 1) x.length aName x c5.σ.mem bs c6 rfl rfl
      hname5.repr hstr5 hbyteK
    rwa [hpNat] at this
  -- ── the store block
  obtain ⟨hgeomS, hnameA, hvalsA, henvA⟩ := appendStoreFactsGeom_of hheap henvLt H.facts.env_addr
    H.facts.cap_read hpn hpvals H.room hcapS (H.facts.names_align pn hpn) (H.facts.vals_align pvals hpvals)
    (H.facts.store.frames_arena env henvLt).2 L.alloc.arena_ram L.alloc.arena_htif hpvNat hE.stack
    hE.slot_in_stack hramLo hramHi hwin
  have hfp6 : EnvDefineAppendFootprint c6.σ.mem aEnv.toNat pn pvals (st.store.frames[env]).vars.length
      (BitVec.ofNat 64 p).toNat pv.toNat (st.store.frames[env]).vars x v := by
    rw [H.facts.env_addr, hpNat]
    exact appendFootprint_of_owned hheap6 henvLt hcap6 hpn6 hpv6 H.room hpFresh (by omega) hvalO6
  obtain ⟨lds, hfacts, hcountW, hnamesW, hvalsW, hp0, hp1, hp2⟩ :=
    appendStoreFacts aEnv pv (BitVec.ofNat 64 p) (st.store.frames[env]).vars.length pn pvals c6.σ.mem N φc v hcode6
      (by rw [H.facts.env_addr]; exact hcount6) (by rw [H.facts.env_addr]; exact hpn6)
      (by rw [H.facts.env_addr]; exact hpv6) hword6 hgeomS
  -- registers at the memcpy return
  have regChain : ∀ R, AbiPreserved R = true → R ≠ Register.x8 → R ≠ Register.x9 →
      c6.σ.regs.get? R = c0.σ.regs.get? R := by
    intro R hR h8 h9
    have h1 : AbiExceptS1 R = true := by
      simp only [AbiExceptS1, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
      exact ⟨hR, h9⟩
    have h0 : abiButS0 R = true := by
      simp only [abiButS0, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
      exact ⟨hR, Ne.symm h8⟩
    rw [habi6 R hR]
    show c5.σ.regs.get? R = _
    rw [S5.abi R h1, X4.frame R hR]
    show c3.σ.regs.get? R = _
    rw [S3.abi R h0, habi2 R hR]
    show c1.σ.regs.get? R = _
    rw [S1.abi R hR]
  have hx20_6 : c6.σ.regs.get? Register.x20 = some aEnv := by
    rw [regChain _ (by decide) (by decide) (by decide)]; exact H.regs.s4
  have hx21_6 : c6.σ.regs.get? Register.x21 = some pv := by
    rw [regChain _ (by decide) (by decide) (by decide)]; exact H.regs.s5
  have hx9_6 : c6.σ.regs.get? Register.x9 = some (BitVec.ofNat 64 p) := by
    rw [habi6 _ (by decide)]; exact S5.s1
  have hx2_6 : c6.σ.regs.get? Register.x2 = some (esp - 64#64) := by
    rw [regChain _ (by decide) (by decide) (by decide)]; exact H.regs.sp
  have hGH6 : GHolds c6.σ (appendStoreL aEnv pv (BitVec.ofNat 64 p)) :=
    ⟨by simpa [gprGet] using hx20_6, by simpa [gprGet] using hx21_6,
      by simpa [gprGet] using hx9_6, trivial⟩
  have hpre7 : SegPre appendStoreSeg (appendStoreL aEnv pv (BitVec.ofNat 64 p)) lds 0x80002b44#64
      c6.σ.mem c6 :=
    ⟨hG6, rfl, hpc6, hG6.minstret, hGH6, (by show KeysOK [20, 21, 9]; decide), hfacts, htick6⟩
  let g6 : (R : Register) → Option (RegisterType R) := fun R => c6.σ.regs.get? R
  obtain ⟨c7, hs7, ⟨hG7, hmem7, hpc7, htick7, hmi7, hregs7⟩, hk7⟩ :=
    segRowKeepGhost appendStoreSeg (appendStoreL aEnv pv (BitVec.ofNat 64 p)) lds 0x80002b44#64
      c6.σ.mem AbiPreserved g6 out
      (fun c => GoodState c.σ ∧ c.σ.mem = writeLog c6.σ.mem (evalBlocks appendStoreSeg
          (SegEvalState.init (appendStoreL aEnv pv (BitVec.ofNat 64 p)) lds)).log ∧
        c.σ.regs.get? Register.PC = some 0x80002aec#64 ∧ c.tick < 2 ∧
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
        GHolds c.σ (evalBlocks appendStoreSeg
          (SegEvalState.init (appendStoreL aEnv pv (BitVec.ofNat 64 p)) lds)).regs)
      (by show ChainOK 0x80002b44#64 [20, 21, 9] appendStoreSeg; decide)
      abiPreserved_noise (by show WrChainAvoids AbiPreserved appendStoreSeg; decide)
      (fun σ' i' u' hG hi hmem hpc hmi hregs => ⟨hG, hmem, by rw [hpc]; rfl, hi, hmi, hregs⟩)
      c6 ⟨hpre7, fun _ _ => rfl, hout6⟩
  have hcount32 : (st.store.frames[env]).vars.length + 1 < 2^31 := by omega
  have hnamesHi : pn + 8 * (st.store.frames[env]).vars.length + 8 ≤ 2^64 := by have := H.room; omega
  have hvalsHi : pvals + 24 * (st.store.frames[env]).vars.length + 24 ≤ 2^64 := by have := H.room; omega
  have henvHi : aEnv.toNat + 4 ≤ 2^64 := by rw [H.facts.env_addr]; omega
  have hmem7' : c7.σ.mem = AppendStoreTower c6.σ.mem aEnv.toNat pn pvals (st.store.frames[env]).vars.length (BitVec.ofNat 64 p)
      (bytesVal .ld (lds.getD 3 [])) (bytesVal .ld (lds.getD 4 [])) (bytesVal .ld (lds.getD 5 [])) := by
    rw [hmem7, appendStoreLogExact aEnv pv (BitVec.ofNat 64 p) lds (st.store.frames[env]).vars.length pn pvals hcountW hnamesW
      hvalsW hcount32 hnamesHi hvalsHi henvHi]
    rfl
  have hag7 : AgreeP (AppendUntouched aEnv.toNat pn pvals (st.store.frames[env]).vars.length) c6.σ.mem c7.σ.mem := by
    rw [hmem7']
    exact appendStoreTowerAgree _ _ _ _ _ _ _ _ _
  have hframe6 : FrameRepr c6.σ.mem N φf φc aEnv.toNat ⟨(st.store.frames[env]).parent, (st.store.frames[env]).vars⟩ := by
    rw [H.facts.env_addr]; exact hstore6.frames env henvLt
  have hread := appendStoreReadback aEnv pv (BitVec.ofNat 64 p) lds c6.σ.mem N φf φc (st.store.frames[env]).parent
    (st.store.frames[env]).vars x v cap pn pvals hframe6 (by rw [H.facts.env_addr]; exact hcap6) H.room
    (by rw [H.facts.env_addr]; exact hpn6) (by rw [H.facts.env_addr]; exact hpv6) hcountW hnamesW hvalsW
    hp0 hp1 hp2 hword6 (by rw [hpNat]; exact hcopied6) hfp6 hcount32 hnamesHi hvalsHi henvHi
  have hnew : FrameRepr c7.σ.mem N φf φc (φf env) ⟨(st.store.frames[env]).parent, (st.store.frames[env]).vars ++ [(x, v)]⟩ := by
    rw [hmem7, ← H.facts.env_addr]
    exact hread.frame
  have hget : st.store.frames[env]? = some st.store.frames[env] :=
    Array.getElem?_eq_some_iff.mpr ⟨henvLt, rfl⟩
  have hag7' : AgreeP (AppendUntouched (φf env) pn pvals (st.store.frames[env]).vars.length) c6.σ.mem c7.σ.mem := by
    rw [← H.facts.env_addr]; exact hag7
  have hfoot := StoreAppendFootprint.of_runtime_owned (N := N) henvLt hheap6 hcap6 hpn6 hpv6
    H.room hag7'
  have hadv : StoreDefineAdvance N A φf φc st.store env x v c7.σ.mem :=
    storeDefineAdvance_of_append hstore6 hget (any_false_of_miss (st.store.frames[env]).vars x H.facts.miss) hnew hag7' hfoot
  -- the spill window and the text survive every step
  have harenaStack' : A.hi ≤ (esp - 64#64).toNat ∨ (esp - 64#64).toNat + 64 ≤ A.lo := by
    rw [hsp64]; rcases hAstack with h | h <;> omega
  have harenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo := by
    rcases hAimg with h | h <;> omega
  have hsaved3 : EnvDefineSavedSpillFrame (esp - 64#64) (envDefineSaved g r) c3 :=
    ((H.regs.saved.of_mem_eq S1.mem).of_mem_eq (hmem2.trans (S1.mem.trans H.regs.mem).symm)).of_mem_eq S3.mem
  have hsaved4 : EnvDefineSavedSpillFrame (esp - 64#64) (envDefineSaved g r) c4 := by
    apply hsaved3.of_interval_agree
    · intro a ha0 ha1
      rw [S3.mem, hmem2]
      exact hag4' a (by rcases hAimg with h | h <;> omega) (by omega)
    · intro a ha0 ha1
      rw [S3.mem, hmem2]
      rw [hsp64] at ha0 ha1
      exact hag4' a (by rcases hAstack with h | h <;> omega) (by omega)
  have hsaved6 : EnvDefineSavedSpillFrame (esp - 64#64) (envDefineSaved g r) c6 := by
    apply (hsaved4.of_mem_eq S5.mem).of_interval_agree
    · intro a ha0 ha1
      exact hout6m a (by rw [hpNat]; rcases hAimg with h | h <;> omega)
    · intro a ha0 ha1
      rw [hsp64] at ha0 ha1
      exact hout6m a (by rw [hpNat]; rcases hAstack with h | h <;> omega)
  have hwrites := appendStoreWritesInArena A aEnv pv (BitVec.ofNat 64 p) lds (st.store.frames[env]).vars.length pn pvals
    hcountW hnamesW hvalsW hcount32 hnamesHi hvalsHi henvHi hnameA hvalsA henvA
  have hpublic7 := appendStorePublicFrame_of_arena A (esp - 64#64) aEnv pv (BitVec.ofNat 64 p) lds
    c6.σ.mem hwrites harenaStack' harenaCode
  have hsaved7 : EnvDefineSavedSpillFrame (esp - 64#64) (envDefineSaved g r) c7 := by
    apply hsaved6.of_interval_agree
    · intro a ha0 ha1
      rw [hmem7]
      exact hpublic7.code a ha0 ha1
    · intro a ha0 ha1
      rw [hmem7]
      exact hpublic7.spills a ha0 ha1
  -- ── the epilogue
  obtain ⟨epiLds, hepiFacts, hepiValues⟩ := hsaved7.chainFacts
  have hx2_7 : c7.σ.regs.get? Register.x2 = some (esp - 64#64) := by
    rw [hk7.keep _ (by decide)]; exact hx2_6
  have hepiPre : SegPre envDefineEpilogueSeg (envDefineEpilogueL (esp - 64#64)) epiLds
      0x80002aec#64 c7.σ.mem c7 :=
    ⟨hG7, rfl, hpc7, hG7.minstret, ⟨hx2_7, trivial⟩, (by show KeysOK [2]; decide), hepiFacts,
      htick7⟩
  let g7 : (R : Register) → Option (RegisterType R) := fun R => c7.σ.regs.get? R
  obtain ⟨c8, hs8, hepiPost, hk8⟩ := envDefineEpilogueRowKeep (esp - 64#64) epiLds c7.σ.mem g7
    out c7 ⟨hepiPre, fun _ _ => rfl, hk7.out⟩
  have hepi := envDefineEpilogueExact_of_post (esp - 64#64) (envDefineSaved g r) epiLds c7.σ.mem
    c8 hepiValues hepiPost
  -- ── the return state
  obtain ⟨v8, hg8⟩ := Option.isSome_iff_exists.mp L.present.s0
  obtain ⟨v9, hg9⟩ := Option.isSome_iff_exists.mp L.present.s1
  obtain ⟨v18, hg18⟩ := Option.isSome_iff_exists.mp L.present.s2
  obtain ⟨v19, hg19⟩ := Option.isSome_iff_exists.mp L.present.s3
  obtain ⟨v20, hg20⟩ := Option.isSome_iff_exists.mp L.present.s4
  obtain ⟨v21, hg21⟩ := Option.isSome_iff_exists.mp L.present.s5
  obtain ⟨v22, hg22⟩ := Option.isSome_iff_exists.mp L.present.s6
  have hmf : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → ¬ (SL.lo ≤ k ∧ k < esp.toNat) →
      c8.σ.mem[k]? = m[k]? := by
    intro k hkA hkS
    rw [hepi.mem, hmem7']
    have hk1 : k < A.lo ∨ A.hi ≤ k := by omega
    have hn1 : k < pn + 8 * (st.store.frames[env]).vars.length ∨
        pn + 8 * (st.store.frames[env]).vars.length + 8 ≤ k := by
      rcases hk1 with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have hv1 : k < pvals + 24 * (st.store.frames[env]).vars.length ∨
        pvals + 24 * (st.store.frames[env]).vars.length + 24 ≤ k := by
      rcases hk1 with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have he1 : k < aEnv.toNat ∨ aEnv.toNat + 4 ≤ k := by
      rw [H.facts.env_addr]
      rcases hk1 with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    rw [appendStoreTowerOutside _ _ _ _ _ _ _ _ _ _ ⟨hn1, hv1, he1⟩]
    rw [hag6' k hkA (by omega)]
    exact H.facts.mem_agree k hkA hkS
  have hext6 : MemExtends c5.σ.mem c6.σ.mem := by
    intro a b hb
    by_cases hin : p ≤ a ∧ a < p + (x.length + 1)
    · refine ⟨bs (a - p), ?_⟩
      have := hcopiedB (a - p) (by omega)
      rw [hpNat, show p + (a - p) = a by omega] at this
      exact this
    · exact ⟨b, by rw [hout6m a (by rw [hpNat]; omega)]; exact hb⟩
  have hext8 : MemExtends m c8.σ.mem := by
    rw [hepi.mem, hmem7]
    have hext46 : MemExtends c4.σ.mem c6.σ.mem := by
      rw [← S5.mem]; exact hext6
    exact ((H.facts.mem_extends.trans X4.mem_extends).trans hext46).trans (memExtends_writeLog _ _)
  have hstore8 : StoreRepr c8.σ.mem N A φf φc (st.store.define env x v) := by
    rw [hepi.mem]; exact hadv.toStoreRepr
  refine ⟨c8, S1.steps.trans (hs2.trans (S3.steps.trans (hs4.trans (S5.steps.trans
    (hs6.trans (hs7.trans hs8)))))), ?_⟩
  exact
    { good := hepi.good
      tick := hepi.tick
      pc := by rw [hepi.pc, envDefineSaved_x1, Option.getD_some, bitvec_update_self r H.facts.ra_align]
      ra := by rw [hepi.ra, envDefineSaved_x1]; rfl
      sp := by rw [hepi.spReg, BitVec.sub_add_cancel]
      minstret := hepi.good.minstret
      a0_defined := by
        refine ⟨bytesVal .ld (lds.getD 4 []), ?_⟩
        rw [hk8.keep _ (by decide)]
        show c7.σ.regs.get? Register.x10 = _
        have h10 : lookupG 10 (evalBlocks appendStoreSeg
            (SegEvalState.init (appendStoreL aEnv pv (BitVec.ofNat 64 p)) lds)).regs =
            some (bytesVal .ld (lds.getD 4 [])) := by
          simp [appendStoreSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,
            stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG, appendStoreL, mkLine, decodeM,
            List.getD_eq_getElem?_getD]
        simpa [gprGet] using gholds_lookup _ hregs7 h10
      out := hk8.out
      frame := by
        intro R hR
        by_cases h2 : R = Register.x2
        · subst h2
          rw [hepi.spReg, BitVec.sub_add_cancel, H.facts.g_sp]
        · cases hres : EnvDefineRestored R with
          | true =>
            simp only [EnvDefineRestored, Bool.or_eq_true, beq_iff_eq] at hres
            rcases hres with ((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
            · rw [hepi.s0, envDefineSaved_ne g r (by decide), hg8]; rfl
            · rw [hepi.s1, envDefineSaved_ne g r (by decide), hg9]; rfl
            · rw [hepi.s2, envDefineSaved_ne g r (by decide), hg18]; rfl
            · rw [hepi.s3, envDefineSaved_ne g r (by decide), hg19]; rfl
            · rw [hepi.s4, envDefineSaved_ne g r (by decide), hg20]; rfl
            · rw [hepi.s5, envDefineSaved_ne g r (by decide), hg21]; rfl
            · rw [hepi.s6, envDefineSaved_ne g r (by decide), hg22]; rfl
          | false =>
            obtain ⟨hkeep, _, h8, h9, _⟩ := envDefineRest_facts R hR hres h2
            rw [hk8.keep R hkeep]
            show c7.σ.regs.get? R = g R
            rw [hk7.keep R hR]
            show c6.σ.regs.get? R = g R
            rw [regChain R hR h8 h9]
            exact H.regs.rest R hR hres h2
      store := hstore8
      store_survives := fun m' hm' => L.define_survives c8.σ.mem hmf hstore8 m' hm'
      mem_frame := hmf
      mem_extends := hext8 }

#print axioms envDefineOwned_of_agree
#print axioms windows_disjoint_of_off
#print axioms appendFootprint_of_owned
#print axioms appendStoreFactsGeom_of
#print axioms any_false_of_miss
#print axioms envDefineAppendLane

end Vsa.Sim
