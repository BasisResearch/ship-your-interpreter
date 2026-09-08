import Vsa.Sim.AllocOff
import Vsa.Sim.rows.EnvDefineAppendLane
import Vsa.Sim.rows.EnvDefineReallocArray

/-!
# `EnvDefineGrowLane` — the grow arm (and the empty frame) to the append head

From the grow arm (`0x80002b90`, `count = cap`) or the empty frame's `cap = 0`
route (`0x80002b98`, `cap := 8`) the helper stores the new capacity, calls
`realloc` on the names array, stores its result, calls `realloc` on the values
array, stores its result and rejoins the append head.  `envDefineGrowLane`
composes the reflected prefixes (`EnvDefineCallRuns`) with the ledger's
`ReallocRun` (`reallocArray_run`, grow or `NULL`) and re-establishes the
represented store and its runtime ownership with the replaced arrays
(`RuntimeOwnershipArrays`), landing `EnvDefineAppendHead` over the
post-`realloc` ledger.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.MemRepr Vsa.RuntimeRepr
open Vsa.Alloc (AbiPreserved StackLayout StackOK MallocContract ExtDisjoint)
open Vsa.Sim.Code (Env_defineLoaded FixedTextLoaded)
open Vsa.While (Addr Value)
open Vsa.Sim.RuntimeOwnership (HeapOwned ValueOwned SharedCString Allocated ExtentByte
  Allocations ArrayOwned Role ArrayState)

open Vsa.Sim.TruthyCopy (abiButS0 abiButS0_noise)

namespace Vsa.Sim

-- `omega` after discarding the lane's standing interval disjunctions (each
-- consumer case-splits the one it needs first): keeps every arithmetic leaf a
-- small problem.
set_option hygiene false in
macro "omg" : tactic => `(tactic| (
  try clear hsepNV
  try clear hsepNR
  try clear hsepVR
  try clear hrecOffNew
  try clear hrecOffNewV
  try clear hnewNewDisj
  try clear hAimg
  try clear hAstack
  try clear hnamesO
  try clear hvalsO
  try clear hvalsO1
  try clear hnamesO'
  try clear hvalsO'
  try clear hpre1
  try clear hpre3
  try clear hslots
  try clear hpar
  try clear harr
  try clear hheap
  omega))

/-- How the grow lane is entered: the grow arm with the current capacity in
`a5`, or the empty frame's route with `cap := 8` (`a5 = 8`, `a1 = 64`). -/
inductive EnvDefineGrowKind (cap : Nat) (c : Config) : Prop where
  | grow (hpos : 0 < cap) (hpc : c.σ.regs.get? Register.PC = some 0x80002b90#64)
      (ha5 : c.σ.regs.get? Register.x15 = some (BitVec.ofNat 64 cap))
  | init (hcap : cap = 0) (hpc : c.σ.regs.get? Register.PC = some 0x80002b98#64)
      (ha5 : c.σ.regs.get? Register.x15 = some 8#64)
      (ha1 : c.σ.regs.get? Register.x11 = some 64#64)

private theorem privOff {privFoot : Nat → Prop} {X : List Extent}
    (h : ∀ e ∈ X, ∀ i < e.2, ¬ privFoot (e.1 + i)) {e : Extent} (he : e ∈ X) {k : Nat}
    (hk : ExtentByte e k) : ¬ privFoot k := by
  intro hp
  change e.1 ≤ k ∧ k < e.1 + e.2 at hk
  have := h e he (k - e.1) (by omega)
  rw [show e.1 + (k - e.1) = k by omega] at this
  exact this hp

/-- **The grow lane's calls, done** — the data: the reflected prefixes, the
two `realloc` runs and the rejoin, with the per-step memory relations, the
fresh arrays, the two ledgers and the allocator invariant they carry. -/
structure GrowCallsData (A : Arena) (SL : StackLayout) {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (mA : Mem) (aEnv esp : BitVec 64)
    (extsA : List Extent) (pn pvals cap : Nat) (c0 c1 c2 c3 c4 c5 : Config)
    (cap' pNamesNew pValsNew : Nat) (exts1 exts2 : List Extent) : Prop where
  steps : Steps c0 c5
  good5 : GoodState c5.σ
  tick5 : c5.tick < 2
  pc5 : c5.σ.regs.get? Register.PC = some 0x80002b1c#64
  minstret5 : ∃ w, c5.σ.regs.get? Register.minstret = some w
  out5 : c5.σ.sailOutput = c0.σ.sailOutput
  abi5 : ∀ R, AbiPreserved R = true → c5.σ.regs.get? R = c0.σ.regs.get? R
  capLt : cap < cap'
  capPos : 0 < cap'
  capS : cap' < 2^31
  privA : ∀ e ∈ extsA, ∀ i < e.2, ¬ M.privFoot (e.1 + i)
  mem1 : c1.σ.mem = writeMap4 mA (aEnv.toNat + 4) (swData (BitVec.ofNat 64 cap'))
  A2 : ∀ k, ¬ M.privFoot k → ¬ (SL.lo ≤ k ∧ k < esp.toNat - 64) →
    (k < pn ∨ pn + 8 * cap ≤ k) → (k < pNamesNew ∨ pNamesNew + 8 * cap' ≤ k) →
    c2.σ.mem[k]? = c1.σ.mem[k]?
  C1 : ∀ j, j < 8 * cap → c2.σ.mem[pNamesNew + j]? = c1.σ.mem[pn + j]?
  mem3 : c3.σ.mem = writeMap8 c2.σ.mem (aEnv.toNat + 8) (sdData_val (BitVec.ofNat 64 pNamesNew))
  A4 : ∀ k, ¬ M.privFoot k → ¬ (SL.lo ≤ k ∧ k < esp.toNat - 64) →
    (k < pvals ∨ pvals + 24 * cap ≤ k) → (k < pValsNew ∨ pValsNew + 24 * cap' ≤ k) →
    c4.σ.mem[k]? = c3.σ.mem[k]?
  C2 : ∀ j, j < 24 * cap → c4.σ.mem[pValsNew + j]? = c3.σ.mem[pvals + j]?
  mem5 : c5.σ.mem = writeMap8 c4.σ.mem (aEnv.toNat + 16) (sdData_val (BitVec.ofNat 64 pValsNew))
  ext2 : MemExtends c1.σ.mem c2.σ.mem
  ext4 : MemExtends c3.σ.mem c4.σ.mem
  nz2 : pNamesNew ≠ 0
  al2 : pNamesNew % 16 = 0
  hA2 : A.contains pNamesNew (8 * cap')
  nz4 : pValsNew ≠ 0
  al4 : pValsNew % 16 = 0
  hA4 : A.contains pValsNew (24 * cap')
  fresh2 : ∀ e ∈ extsA, e ≠ (pn, 8 * cap) → ExtDisjoint (pNamesNew, 8 * cap') e
  fresh4 : ∀ e ∈ exts1, e ≠ (pvals, 24 * cap) → ExtDisjoint (pValsNew, 24 * cap') e
  exts1_def : exts1 = (pNamesNew, 8 * cap') :: extsA.erase (pn, 8 * cap)
  exts2_def : exts2 = (pValsNew, 24 * cap') :: exts1.erase (pvals, 24 * cap)
  ainv2 : M.AInv c2.σ exts1
  ainv4 : M.AInv c4.σ exts2
  x3_54 : c5.σ.regs.get? Register.x3 = c4.σ.regs.get? Register.x3
  text4 : FixedTextLoaded c4.σ.mem

/-- The calls, with their configs and results selected. -/
inductive GrowCalls (A : Arena) (SL : StackLayout) {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (mA : Mem) (aEnv esp : BitVec 64)
    (extsA : List Extent) (pn pvals cap : Nat) (c0 : Config) : Prop where
  | intro (c1 c2 c3 c4 c5 : Config) (cap' pNamesNew pValsNew : Nat) (exts1 exts2 : List Extent)
      (data : GrowCallsData A SL M mA aEnv esp extsA pn pvals cap c0 c1 c2 c3 c4 c5
        cap' pNamesNew pValsNew exts1 exts2)

/-- **The grow lane's memory core** at the rejoined memory `m5`: the master
agreement with the arm memory, the record's words, the copied slots,
presence and the text image. -/
structure GrowMemCore (A : Arena) (SL : StackLayout) {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (mA m5 : Mem) (φf : Addr → Nat)
    (env : Addr) (aEnv esp : BitVec 64) (pn pvals cap pNamesNew pValsNew cap' : Nat) : Prop where
  agOff : ∀ k, ¬ M.privFoot k → ¬ (SL.lo ≤ k ∧ k < esp.toNat - 64) →
    (k < pn ∨ pn + 8 * cap ≤ k) → (k < pNamesNew ∨ pNamesNew + 8 * cap' ≤ k) →
    (k < pvals ∨ pvals + 24 * cap ≤ k) → (k < pValsNew ∨ pValsNew + 24 * cap' ≤ k) →
    (k < aEnv.toNat + 4 ∨ aEnv.toNat + 24 ≤ k) → m5[k]? = mA[k]?
  count : read32 m5 (φf env) = read32 mA (φf env)
  parent : read64 m5 (φf env + 24) = read64 mA (φf env + 24)
  capRead : read32 m5 (φf env + 4) = some cap'
  namesRead : read64 m5 (φf env + 8) = some pNamesNew
  valsRead : read64 m5 (φf env + 16) = some pValsNew
  keys : ∀ i, i < cap → ∀ k, k < 8 → m5[pNamesNew + 8 * i + k]? = mA[pn + 8 * i + k]?
  values : ∀ i, i < cap → ∀ k, k < 24 → m5[pValsNew + 24 * i + k]? = mA[pvals + 24 * i + k]?
  ext : MemExtends mA m5
  text : FixedTextLoaded m5

/-- **The grow lane's memory facts**: the core plus the bytes the lane leaves
untouched — every other allocation, every shared byte, every byte off the
arena and the callee's window, and the staged value slot. -/
structure GrowMemFacts (A : Arena) (SL : StackLayout) (mA m5 : Mem) (φf : Addr → Nat)
    (env : Addr) (esp pv : BitVec 64) (alloc : Allocations) (shared : Nat → Prop)
    (pn pvals cap pNamesNew pValsNew cap' : Nat) : Prop where
  other : ∀ role q nn, role ≠ .frame env → role ≠ .names env → role ≠ .values env →
    Allocated alloc role q nn → ∀ k, ExtentByte (q, nn) k → m5[k]? = mA[k]?
  sharedOff : ∀ k, shared k → m5[k]? = mA[k]?
  offArena : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → ¬ (SL.lo ≤ k ∧ k < esp.toNat - 64) →
    m5[k]? = mA[k]?
  slot : ∀ k, valHeader pv.toNat k → m5[k]? = mA[k]?
/-- **The grow lane's calls**: from either entry, the prefixes, both `realloc`
runs and the rejoin. -/
theorem envDefineGrowCalls
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts extsA : List Extent) (mA : Mem)
    (cap pn pvals : Nat) (c0 : Config)
    (hE : EnvDefineMem N A SL φf φc st env x v aEnv aName pv esp m)
    (L : EnvDefineUpdateLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (LM : EnvDefineMissLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (F : EnvDefineMissFacts g N A SL φf φc st env x v esp aEnv aName pv r m extsA mA cap)
    (R : EnvDefineMissRegs g A SL st env esp aEnv aName pv r out M extsA mA F.env_lt c0)
    (hfull : (st.store.frames[env]'F.env_lt).vars.length = cap)
    (hpn : read64 mA (φf env + 8) = some pn)
    (hpvals : read64 mA (φf env + 16) = some pvals)
    (hgrowReq : 48 * cap ≤ maxReq)
    (K : EnvDefineGrowKind cap c0)
    (hs6 : c0.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 pn)) :
    GrowCalls A SL M mA aEnv esp extsA pn pvals cap c0 := by
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
  have henvLt := F.env_lt
  have hfull' : (st.store.frames[env]).vars.length = cap := hfull
  obtain ⟨alloc, shared, readable, writes, hheap, hstackW, hvalO, hnameO⟩ := F.owned
  have hfo := hheap.store.frames env henvLt
  obtain ⟨arr, harr⟩ := hfo.arrays
  obtain ⟨hcountR, ⟨cap0, hcap0, hcaple⟩, ⟨pn0, pvals0, hpn0, hpvals0, hslots⟩, hpar⟩ :=
    F.store.frames env henvLt
  have hcapEq : cap0 = cap := Option.some.inj (hcap0.symm.trans F.cap_read)
  subst cap0
  have hpnEq : pn0 = pn := Option.some.inj (hpn0.symm.trans hpn)
  subst pn0
  have hpvEq : pvals0 = pvals := Option.some.inj (hpvals0.symm.trans hpvals)
  subst pvals0
  have ecap : arr.cap = cap := Option.some.inj (harr.capRead.symm.trans F.cap_read)
  have enames : arr.names = pn := Option.some.inj (harr.namesRead.symm.trans hpn)
  have evals : arr.values = pvals := Option.some.inj (harr.valuesRead.symm.trans hpvals)
  have hnamesO : ArrayOwned alloc (.names env) pn 8 cap := by
    have := harr.names; rwa [enames, ecap] at this
  have hvalsO : ArrayOwned alloc (.values env) pvals 24 cap := by
    have := harr.values; rwa [evals, ecap] at this
  have hrA : Allocated alloc (.frame env) (φf env) 32 := hfo.record
  have hrecMem : (φf env, 32) ∈ extsA := hheap.ledger.live _ _ _ hrA
  obtain ⟨_, hrLo, hrHi⟩ := hheap.ledger.arena.1 _ hrecMem
  have hcapS : cap < 2^31 := hfo.capSigned hheap.ledger F.cap_read (by omega)
  have henvGeom : EnvRecordGeom aEnv :=
    { lo := by rw [F.env_addr]; omega
      hi := by rw [F.env_addr]; omega
      htif := by rw [F.env_addr]; omega
      align := by rw [F.env_addr]; exact (F.store.frames_arena env henvLt).2
      code := by rw [F.env_addr]; rcases hAimg with h | h <;> omega }
  -- old arrays: allocated when the capacity is positive, `NULL` otherwise
  have hnamesMem : 0 < cap → (pn, 8 * cap) ∈ extsA :=
    fun hc => hheap.ledger.live _ _ _ (hnamesO.nonempty hc)
  have hvalsMem : 0 < cap → (pvals, 24 * cap) ∈ extsA :=
    fun hc => hheap.ledger.live _ _ _ (hvalsO.nonempty hc)
  have hzero : cap = 0 → pn = 0 ∧ pvals = 0 := by
    intro hc
    rcases hnamesO with ⟨_, h1⟩ | ⟨h1, _⟩
    · rcases hvalsO with ⟨_, h2⟩ | ⟨h2, _⟩
      · exact ⟨h1, h2⟩
      · omega
    · omega
  have hsepNV : ExtDisjoint (pn, 8 * cap) (pvals, 24 * cap) := by
    rcases Nat.eq_zero_or_pos cap with hc | hc
    · obtain ⟨h1, h2⟩ := hzero hc
      subst h1; subst h2
      exact Or.inl (by omega)
    · exact hheap.ledger.separated _ _ _ _ _ _ (hnamesO.nonempty hc) (hvalsO.nonempty hc) nofun
  have hsepNR : ExtDisjoint (pn, 8 * cap) (φf env, 32) := by
    rcases Nat.eq_zero_or_pos cap with hc | hc
    · obtain ⟨h1, _⟩ := hzero hc
      subst h1
      exact Or.inl (by omega)
    · exact hheap.ledger.separated _ _ _ _ _ _ (hnamesO.nonempty hc) hrA nofun
  have hsepVR : ExtDisjoint (pvals, 24 * cap) (φf env, 32) := by
    rcases Nat.eq_zero_or_pos cap with hc | hc
    · obtain ⟨_, h2⟩ := hzero hc
      subst h2
      exact Or.inl (by omega)
    · exact hheap.ledger.separated _ _ _ _ _ _ (hvalsO.nonempty hc) hrA nofun
  change pn + 8 * cap ≤ pvals ∨ pvals + 24 * cap ≤ pn at hsepNV
  change pn + 8 * cap ≤ φf env ∨ φf env + 32 ≤ pn at hsepNR
  change pvals + 24 * cap ≤ φf env ∨ φf env + 32 ≤ pvals at hsepVR
  have hnamesArena : 0 < cap → A.lo ≤ pn ∧ pn + 8 * cap ≤ A.hi := by
    intro hc
    obtain ⟨_, h1, h2⟩ := hheap.ledger.arena.1 _ (hnamesMem hc)
    exact ⟨h1, h2⟩
  have hvalsArena : 0 < cap → A.lo ≤ pvals ∧ pvals + 24 * cap ≤ A.hi := by
    intro hc
    obtain ⟨_, h1, h2⟩ := hheap.ledger.arena.1 _ (hvalsMem hc)
    exact ⟨h1, h2⟩
  have hcap30 : cap < 2^30 := by
    rcases Nat.eq_zero_or_pos cap with hc | hc
    · omega
    · have := hvalsArena hc; omega
  have hprivA : ∀ e ∈ extsA, ∀ i < e.2, ¬ M.privFoot (e.1 + i) :=
    M.privFoot_disjoint c0.σ extsA R.ainv
  -- the entry-side allocator separation facts, from ONE lemma (`AllocOff.lean`)
  have EO : EntryOff A SL extsA M.privFoot alloc shared :=
    hheap.entryOff hstackW hprivA LM.alloc.priv_arena
  have hsharedPriv := EO.shared_priv
  have hsharedStack := EO.shared_stack
  have hextArena := EO.ext_arena
  -- ── the first prefix (either entry), parked at `realloc(names)`
  have hcode0 : Env_defineLoaded c0.σ.mem := by rw [R.mem]; exact F.text.Env_defineLoaded
  obtain ⟨cap', hcapLt, hcapPos, hreq8, hreq24, hcapS', c1, P1⟩ :
      ∃ cap', cap < cap' ∧ 0 < cap' ∧ 8 * cap' ≤ maxReq ∧ 24 * cap' ≤ maxReq ∧ cap' < 2^31 ∧
        ∃ c1, EnvDefineReallocNamesParked aEnv (BitVec.ofNat 64 pn) cap' c0 c1 := by
    rcases K with ⟨hpos, hpc, ha5⟩ | ⟨hc, hpc, ha5, ha1⟩
    · obtain ⟨c1, P1⟩ := envDefineReallocNamesParked_grow aEnv (BitVec.ofNat 64 pn) cap c0 hcap30
        henvGeom R.good hpc ha5 R.s4 hs6 hcode0 R.tick
      exact ⟨2 * cap, by omega, by omega, by omega, by omega, by omega, c1, P1⟩
    · subst hc
      obtain ⟨c1, P1⟩ := envDefineReallocNamesParked_init aEnv (BitVec.ofNat 64 pn) c0 henvGeom
        R.good hpc ha5 ha1 R.s4 hs6 hcode0 R.tick
      exact ⟨8, by omega, by omega, by have := LM.alloc.init_req; omega,
        by have := LM.alloc.init_req; omega, by omega, c1, P1⟩
  have henvNat : aEnv.toNat = φf env := F.env_addr
  have hmem1 : c1.σ.mem = writeMap4 mA (aEnv.toNat + 4) (swData (BitVec.ofNat 64 cap')) := by
    rw [P1.mem, R.mem]
  have A1 : ∀ k, (k < aEnv.toNat + 4 ∨ aEnv.toNat + 8 ≤ k) → c1.σ.mem[k]? = mA[k]? := by
    intro k hk
    rw [hmem1]
    exact getElem_writeMap4_disjoint _ _ _ _ hk
  have hrecNotPriv : ∀ a, φf env ≤ a → a < φf env + 32 → ¬ M.privFoot a :=
    fun a h1 h2 => privOff hprivA hrecMem ⟨h1, h2⟩
  have hrecNotStack : ∀ a, φf env ≤ a → a < φf env + 32 → ¬ (SL.lo ≤ a ∧ a < esp.toNat - 64) := by
    intro a h1 h2 hin
    rcases hAstack with h | h <;> omega
  have hrecNe : (φf env, 32) ≠ (pn, 8 * cap) := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    omega
  have hvalsNeNames : 0 < cap → (pvals, 24 * cap) ≠ (pn, 8 * cap) := by
    intro hc h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    omega
  -- ── realloc(names)
  have hx3_1 : c1.σ.regs.get? Register.x3 = some gpv := by rw [P1.abi _ (by decide)]; exact R.gp
  have hx2_1 : c1.σ.regs.get? Register.x2 = some (esp - 64#64) := by
    rw [P1.abi _ (by decide)]; exact R.sp
  have hainv1 : M.AInv c1.σ extsA := by
    apply LM.alloc.ainv_private extsA c0.σ c1.σ (R.gp.trans hx3_1.symm) _ R.ainv
    intro a hpa
    rw [R.mem, ← (A1 a ?_)]
    by_cases hin : aEnv.toNat + 4 ≤ a ∧ a < aEnv.toNat + 8
    · exact absurd hpa (hrecNotPriv a (by omega) (by omega))
    · omega
  let g1 : (R : Register) → Option (RegisterType R) := fun R => c1.σ.regs.get? R
  have hpre1 : ReallocPre SL gpv headroom M.AInv extsA pn (8 * cap') (esp - 64#64) 0x80002ba4#64
      c1.σ.mem g1 c1 :=
    ⟨P1.good, P1.tick, P1.pc, P1.a0, P1.a1, P1.ra, by decide, hx2_1, R.stack, hx3_1,
      fun _ _ => rfl, hainv1, rfl⟩
  obtain ⟨c2, hs2, post2, res2, out2, ext2⟩ :=
    reallocArray_run LM.alloc.realloc hheap.ledger.arena hnamesO hnamesMem
      (fun hc => by have := hnamesArena hc; omega) (by omega) hreq8 (by omega) g1
      (esp - 64#64) 0x80002ba4#64 c1.σ.mem out c1 ⟨hpre1, P1.out.trans R.out⟩
  obtain ⟨hG2, htick2, hpc2, hsp2, hgp2, habi2⟩ := post2
  obtain ⟨pNamesNew, hx10_2, hnz2, hal2, hA2, hfresh2, hcopies2, hainv2, hframe2⟩ := res2
  have hA2' : A.lo ≤ pNamesNew ∧ pNamesNew + 8 * cap' ≤ A.hi := hA2
  have A2 : ∀ k, ¬ M.privFoot k → ¬ (SL.lo ≤ k ∧ k < esp.toNat - 64) →
      (k < pn ∨ pn + 8 * cap ≤ k) → (k < pNamesNew ∨ pNamesNew + 8 * cap' ≤ k) →
      c2.σ.mem[k]? = c1.σ.mem[k]? := by
    intro k h1 h2 h3 h4
    apply hframe2 k h1 (by rw [hsp64]; exact h2)
    intro e he
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact h3
    · exact h4
  have C1 : ∀ j, j < 8 * cap → c2.σ.mem[pNamesNew + j]? = c1.σ.mem[pn + j]? := hcopies2
  generalize hexts1 : (pNamesNew, 8 * cap') :: extsA.erase (pn, 8 * cap) = exts1 at hainv2
  have hpriv1 : ∀ e ∈ exts1, ∀ i < e.2, ¬ M.privFoot (e.1 + i) :=
    M.privFoot_disjoint c2.σ exts1 hainv2
  have hrec1 : (φf env, 32) ∈ exts1 := by
    rw [← hexts1]
    exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne hrecNe).mpr hrecMem)
  have hnew1 : (pNamesNew, 8 * cap') ∈ exts1 := by rw [← hexts1]; exact List.mem_cons_self
  have hrecOffNew : ExtDisjoint (pNamesNew, 8 * cap') (φf env, 32) := hfresh2 _ hrecMem hrecNe
  change pNamesNew + 8 * cap' ≤ φf env ∨ φf env + 32 ≤ pNamesNew at hrecOffNew
  -- the record's words at the first `realloc` return
  have hrecAg12 : ∀ a, φf env ≤ a → a < φf env + 32 → c2.σ.mem[a]? = c1.σ.mem[a]? := by
    intro a h1 h2
    exact A2 a (hrecNotPriv a h1 h2) (hrecNotStack a h1 h2) (by omega) (by omega)
  have hcap2 : read32 c2.σ.mem (aEnv.toNat + 4) = some cap' := by
    rw [← read32_agreeP (P := fun a => φf env ≤ a ∧ a < φf env + 32)
      (fun a ha => (hrecAg12 a ha.1 ha.2).symm) (fun k hk => by rw [henvNat] at *; omega)]
    rw [hmem1, read32_writeMap4, swData_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hpv2 : read64 c2.σ.mem (aEnv.toNat + 16) = some pvals := by
    rw [← read64_agreeP (P := fun a => φf env ≤ a ∧ a < φf env + 32)
      (fun a ha => (hrecAg12 a ha.1 ha.2).symm) (fun k hk => by rw [henvNat] at *; omega)]
    rw [← read64_agreeP (P := fun a => aEnv.toNat + 16 ≤ a ∧ a < aEnv.toNat + 24)
      (fun a ha => (A1 a (by omega)).symm) (fun k hk => by omega)]
    rw [henvNat]; exact hpvals
  have hOffText : ∀ a, 0x80000000 ≤ a → a < 0x80018be0 → ¬ (A.lo ≤ a ∧ a < A.hi) := by
    intro a h1 h2 hin
    rcases hAimg with h | h <;> omega
  have hOffTextStack : ∀ a, 0x80000000 ≤ a → a < 0x80018be0 →
      ¬ (SL.lo ≤ a ∧ a < esp.toNat - 64) := by
    intro a h1 h2 hin
    omega
  have hnamesInArena : ∀ k, pn ≤ k → k < pn + 8 * cap → A.lo ≤ k ∧ k < A.hi := by
    intro k h1 h2
    have hc : 0 < cap := by omega
    have := hnamesArena hc
    omega
  have hvalsInArena : ∀ k, pvals ≤ k → k < pvals + 24 * cap → A.lo ≤ k ∧ k < A.hi := by
    intro k h1 h2
    have hc : 0 < cap := by omega
    have := hvalsArena hc
    omega
  have htext2 : FixedTextLoaded c2.σ.mem := by
    apply F.text.transport
    intro a h1 h2
    have hna := hOffText a h1 h2
    have hoffN : a < pn ∨ pn + 8 * cap ≤ a := by
      rcases Nat.lt_or_ge a pn with h | h
      · exact Or.inl h
      · rcases Nat.lt_or_ge a (pn + 8 * cap) with h' | h'
        · exact absurd (hnamesInArena a h h') hna
        · exact Or.inr h'
    have hoffNN : a < pNamesNew ∨ pNamesNew + 8 * cap' ≤ a := by
      rcases Nat.lt_or_ge a pNamesNew with h | h
      · exact Or.inl h
      · right; omega
    have hoffR : a < aEnv.toNat + 4 ∨ aEnv.toNat + 8 ≤ a := by
      rw [henvNat]
      rcases Nat.lt_or_ge a (φf env + 4) with h | h
      · exact Or.inl h
      · right; omega
    rw [A2 a (fun hp => hna (LM.alloc.priv_arena a hp)) (hOffTextStack a h1 h2) hoffN hoffNN]
    exact A1 a hoffR
  -- ── the second prefix, parked at `realloc(vals)`
  have hs4_2 : c2.σ.regs.get? Register.x20 = some aEnv := by
    rw [habi2 _ (by decide)]
    show c1.σ.regs.get? Register.x20 = _
    rw [P1.abi _ (by decide)]; exact R.s4
  obtain ⟨c3, P3⟩ := envDefineReallocValsParked_of aEnv (BitVec.ofNat 64 pNamesNew) cap' pvals c2
    henvGeom hcapS' hcap2 hpv2 hG2 hpc2 hx10_2 hs4_2 htext2.Env_defineLoaded htick2
  have A3 : ∀ k, (k < aEnv.toNat + 8 ∨ aEnv.toNat + 16 ≤ k) → c3.σ.mem[k]? = c2.σ.mem[k]? := by
    intro k hk
    rw [P3.mem]
    exact getElem_writeMap8_disjoint _ _ _ _ hk
  -- ── realloc(vals)
  have hx3_3 : c3.σ.regs.get? Register.x3 = some gpv := by rw [P3.abi _ (by decide)]; exact hgp2
  have hx2_3 : c3.σ.regs.get? Register.x2 = some (esp - 64#64) := by
    rw [P3.abi _ (by decide)]; exact hsp2
  have hainv3 : M.AInv c3.σ exts1 := by
    apply LM.alloc.ainv_private exts1 c2.σ c3.σ (hgp2.trans hx3_3.symm) _ hainv2
    intro a hpa
    rw [← (A3 a ?_)]
    by_cases hin : aEnv.toNat + 8 ≤ a ∧ a < aEnv.toNat + 16
    · exact absurd hpa (privOff hpriv1 hrec1 ⟨by omega, by omega⟩)
    · omega
  let alloc1 : Allocations := alloc.insert (.names env) pNamesNew (8 * cap')
  have hvalsO1 : ArrayOwned alloc1 (.values env) pvals 24 cap :=
    hvalsO.congr (Vsa.Sim.RuntimeOwnership.Allocations.insert_other nofun)
  have ledger1 : Vsa.Sim.RuntimeOwnership.Ledger A exts1 alloc1 := by
    rw [← hexts1]
    exact hheap.ledger.replaceArray hnamesO (by omega) hA2 hfresh2
  let g3 : (R : Register) → Option (RegisterType R) := fun R => c3.σ.regs.get? R
  have hpre3 : ReallocPre SL gpv headroom M.AInv exts1 pvals (24 * cap') (esp - 64#64)
      0x80002bc0#64 c3.σ.mem g3 c3 :=
    ⟨P3.good, P3.tick, P3.pc, P3.a0, P3.a1, P3.ra, by decide, hx2_3, R.stack, hx3_3,
      fun _ _ => rfl, hainv3, rfl⟩
  obtain ⟨c4, hs4, post4, res4, out4, ext4⟩ :=
    reallocArray_run LM.alloc.realloc ledger1.arena hvalsO1
      (fun hc => ledger1.live _ _ _ (hvalsO1.nonempty hc))
      (fun hc => by have := hvalsArena hc; omega) (by omega) hreq24 (by omega) g3
      (esp - 64#64) 0x80002bc0#64 c3.σ.mem out c3 ⟨hpre3, P3.out.trans out2⟩
  obtain ⟨hG4, htick4, hpc4, hsp4, hgp4, habi4⟩ := post4
  obtain ⟨pValsNew, hx10_4, hnz4, hal4, hA4, hfresh4, hcopies4, hainv4, hframe4⟩ := res4
  have hA4' : A.lo ≤ pValsNew ∧ pValsNew + 24 * cap' ≤ A.hi := hA4
  have A4 : ∀ k, ¬ M.privFoot k → ¬ (SL.lo ≤ k ∧ k < esp.toNat - 64) →
      (k < pvals ∨ pvals + 24 * cap ≤ k) → (k < pValsNew ∨ pValsNew + 24 * cap' ≤ k) →
      c4.σ.mem[k]? = c3.σ.mem[k]? := by
    intro k h1 h2 h3 h4
    apply hframe4 k h1 (by rw [hsp64]; exact h2)
    intro e he
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact h3
    · exact h4
  have C2 : ∀ j, j < 24 * cap → c4.σ.mem[pValsNew + j]? = c3.σ.mem[pvals + j]? := hcopies4
  generalize hexts2 : (pValsNew, 24 * cap') :: exts1.erase (pvals, 24 * cap) = exts2 at hainv4
  have hpriv2 : ∀ e ∈ exts2, ∀ i < e.2, ¬ M.privFoot (e.1 + i) :=
    M.privFoot_disjoint c4.σ exts2 hainv4
  have hrecNeV : (φf env, 32) ≠ (pvals, 24 * cap) := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    omega
  have hrec2 : (φf env, 32) ∈ exts2 := by
    rw [← hexts2]
    exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne hrecNeV).mpr hrec1)
  have hrecOffNewV : ExtDisjoint (pValsNew, 24 * cap') (φf env, 32) := hfresh4 _ hrec1 hrecNeV
  change pValsNew + 24 * cap' ≤ φf env ∨ φf env + 32 ≤ pValsNew at hrecOffNewV
  have hnewNe : (pNamesNew, 8 * cap') ≠ (pvals, 24 * cap) := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    rcases Nat.eq_zero_or_pos cap with hc | hc
    · omega
    · have := hfresh2 _ (hvalsMem hc) (hvalsNeNames hc)
      change pNamesNew + 8 * cap' ≤ pvals ∨ pvals + 24 * cap ≤ pNamesNew at this
      omega
  have hnewNewDisj : ExtDisjoint (pValsNew, 24 * cap') (pNamesNew, 8 * cap') :=
    hfresh4 _ hnew1 hnewNe
  change pValsNew + 24 * cap' ≤ pNamesNew ∨ pNamesNew + 8 * cap' ≤ pValsNew at hnewNewDisj
  have hnewOldV : 0 < cap → ExtDisjoint (pNamesNew, 8 * cap') (pvals, 24 * cap) :=
    fun hc => hfresh2 _ (hvalsMem hc) (hvalsNeNames hc)
  have hnew2 : (pNamesNew, 8 * cap') ∈ exts2 := by
    rw [← hexts2]
    exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne hnewNe).mpr hnew1)
  -- the record's words at the second `realloc` return
  have hrecAg34 : ∀ a, φf env ≤ a → a < φf env + 32 → c4.σ.mem[a]? = c3.σ.mem[a]? := by
    intro a h1 h2
    exact A4 a (hrecNotPriv a h1 h2) (hrecNotStack a h1 h2) (by omega) (by omega)
  have hpNamesLt : pNamesNew < 2^64 := by omega
  have hpValsLt : pValsNew < 2^64 := by omega
  have hnames4 : read64 c4.σ.mem (aEnv.toNat + 8) = some pNamesNew := by
    rw [← read64_agreeP (P := fun a => φf env ≤ a ∧ a < φf env + 32)
      (fun a ha => (hrecAg34 a ha.1 ha.2).symm) (fun k hk => by rw [henvNat] at *; omega)]
    rw [P3.mem, read64_writeMap8, sdData_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpNamesLt]
  -- ── the rejoin
  have hs4_4 : c4.σ.regs.get? Register.x20 = some aEnv := by
    rw [habi4 _ (by decide)]
    show c3.σ.regs.get? Register.x20 = _
    rw [P3.abi _ (by decide)]; exact hs4_2
  have htext4 : FixedTextLoaded c4.σ.mem := by
    apply htext2.transport
    intro a h1 h2
    have hna := hOffText a h1 h2
    have hoffV : a < pvals ∨ pvals + 24 * cap ≤ a := by
      rcases Nat.lt_or_ge a pvals with h | h
      · exact Or.inl h
      · rcases Nat.lt_or_ge a (pvals + 24 * cap) with h' | h'
        · exact absurd (hvalsInArena a h h') hna
        · exact Or.inr h'
    have hoffNV : a < pValsNew ∨ pValsNew + 24 * cap' ≤ a := by
      rcases Nat.lt_or_ge a pValsNew with h | h
      · exact Or.inl h
      · right; omega
    have hoffR : a < aEnv.toNat + 8 ∨ aEnv.toNat + 16 ≤ a := by
      rw [henvNat]
      rcases Nat.lt_or_ge a (φf env + 8) with h | h
      · exact Or.inl h
      · right; omega
    rw [A4 a (fun hp => hna (LM.alloc.priv_arena a hp)) (hOffTextStack a h1 h2) hoffV hoffNV]
    exact A3 a hoffR
  have hnzBV : BitVec.ofNat 64 pNamesNew ≠ 0#64 := by
    intro hz
    have := congrArg BitVec.toNat hz
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpNamesLt] at this
    exact hnz2 this
  have hvzBV : BitVec.ofNat 64 pValsNew ≠ 0#64 := by
    intro hz
    have := congrArg BitVec.toNat hz
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpValsLt] at this
    exact hnz4 this
  obtain ⟨c5, D⟩ := envDefineRejoinDone_of aEnv (BitVec.ofNat 64 pNamesNew)
    (BitVec.ofNat 64 pValsNew) c4 henvGeom
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpNamesLt]; exact hnames4) hnzBV hvzBV hG4 hpc4
    hx10_4 hs4_4 htext4.Env_defineLoaded htick4
  have A5 : ∀ k, (k < aEnv.toNat + 16 ∨ aEnv.toNat + 24 ≤ k) → c5.σ.mem[k]? = c4.σ.mem[k]? := by
    intro k hk
    rw [D.mem]
    exact getElem_writeMap8_disjoint _ _ _ _ hk
  refine ⟨c1, c2, c3, c4, c5, cap', pNamesNew, pValsNew, exts1, exts2, ?_⟩
  exact
    { steps := P1.steps.trans (hs2.trans (P3.steps.trans (hs4.trans D.steps)))
      good5 := D.good
      tick5 := D.tick
      pc5 := D.pc
      minstret5 := D.minstret
      out5 := D.out.trans (out4.trans R.out.symm)
      abi5 := by
        intro R hR
        rw [D.abi R hR, habi4 R hR]
        show c3.σ.regs.get? R = _
        rw [P3.abi R hR, habi2 R hR]
        show c1.σ.regs.get? R = _
        rw [P1.abi R hR]
      capLt := hcapLt
      capPos := hcapPos
      capS := hcapS'
      privA := hprivA
      mem1 := hmem1
      A2 := A2
      C1 := C1
      mem3 := P3.mem
      A4 := A4
      C2 := C2
      mem5 := D.mem
      ext2 := ext2
      ext4 := ext4
      nz2 := hnz2
      al2 := hal2
      hA2 := hA2
      nz4 := hnz4
      al4 := hal4
      hA4 := hA4
      fresh2 := hfresh2
      fresh4 := hfresh4
      exts1_def := hexts1.symm
      exts2_def := hexts2.symm
      ainv2 := hainv2
      ainv4 := hainv4
      x3_54 := D.abi _ (by decide)
      text4 := htext4 }

/-- **The grow lane's memory core** from the calls and the arm's ownership. -/
theorem envDefineGrowMemCore
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts extsA : List Extent) (mA : Mem)
    (cap pn pvals : Nat) (c0 : Config)
    (hE : EnvDefineMem N A SL φf φc st env x v aEnv aName pv esp m)
    (L : EnvDefineUpdateLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (LM : EnvDefineMissLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (F : EnvDefineMissFacts g N A SL φf φc st env x v esp aEnv aName pv r m extsA mA cap)
    (R : EnvDefineMissRegs g A SL st env esp aEnv aName pv r out M extsA mA F.env_lt c0)
    (hfull : (st.store.frames[env]'F.env_lt).vars.length = cap)
    (hpn : read64 mA (φf env + 8) = some pn)
    (hpvals : read64 mA (φf env + 16) = some pvals)
    (hgrowReq : 48 * cap ≤ maxReq)
    (c1 c2 c3 c4 c5 : Config) (cap' pNamesNew pValsNew : Nat) (exts1 exts2 : List Extent)
    (D : GrowCallsData A SL M mA aEnv esp extsA pn pvals cap c0 c1 c2 c3 c4 c5
      cap' pNamesNew pValsNew exts1 exts2)
    (alloc : Allocations) (shared readable writes : Nat → Prop)
    (hheap : HeapOwned A extsA mA φf φc alloc shared readable writes st.store)
    (hstackW : ∀ k, SL.lo ≤ k → k < SL.hi → writes k) :
    GrowMemCore A SL M mA c5.σ.mem φf env aEnv esp pn pvals cap pNamesNew pValsNew cap' := by
  have hcapLt := D.capLt
  have hcapPos := D.capPos
  have hcapS' := D.capS
  have hprivA := D.privA
  have hmem1 := D.mem1
  have A2 := D.A2
  have C1 := D.C1
  have hmem3 := D.mem3
  have A4 := D.A4
  have C2 := D.C2
  have hmem5 := D.mem5
  have ext2 := D.ext2
  have ext4 := D.ext4
  have hnz2 := D.nz2
  have hal2 := D.al2
  have hA2 := D.hA2
  have hnz4 := D.nz4
  have hal4 := D.al4
  have hA4 := D.hA4
  have hfresh2 := D.fresh2
  have hfresh4 := D.fresh4
  have hexts1 := D.exts1_def
  have hexts2 := D.exts2_def
  have hainv2 := D.ainv2
  have hainv4 := D.ainv4
  have htext4 := D.text4
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
  have henvLt := F.env_lt
  have hfull' : (st.store.frames[env]).vars.length = cap := hfull
  have hfo := hheap.store.frames env henvLt
  obtain ⟨arr, harr⟩ := hfo.arrays
  obtain ⟨hcountR, ⟨cap0, hcap0, hcaple⟩, ⟨pn0, pvals0, hpn0, hpvals0, hslots⟩, hpar⟩ :=
    F.store.frames env henvLt
  have hcapEq : cap0 = cap := Option.some.inj (hcap0.symm.trans F.cap_read)
  subst cap0
  have hpnEq : pn0 = pn := Option.some.inj (hpn0.symm.trans hpn)
  subst pn0
  have hpvEq : pvals0 = pvals := Option.some.inj (hpvals0.symm.trans hpvals)
  subst pvals0
  have ecap : arr.cap = cap := Option.some.inj (harr.capRead.symm.trans F.cap_read)
  have enames : arr.names = pn := Option.some.inj (harr.namesRead.symm.trans hpn)
  have evals : arr.values = pvals := Option.some.inj (harr.valuesRead.symm.trans hpvals)
  have hnamesO : ArrayOwned alloc (.names env) pn 8 cap := by
    have := harr.names; rwa [enames, ecap] at this
  have hvalsO : ArrayOwned alloc (.values env) pvals 24 cap := by
    have := harr.values; rwa [evals, ecap] at this
  have hrA : Allocated alloc (.frame env) (φf env) 32 := hfo.record
  have hrecMem : (φf env, 32) ∈ extsA := hheap.ledger.live _ _ _ hrA
  obtain ⟨_, hrLo, hrHi⟩ := hheap.ledger.arena.1 _ hrecMem
  have hcapS : cap < 2^31 := hfo.capSigned hheap.ledger F.cap_read (by omega)
  have henvGeom : EnvRecordGeom aEnv :=
    { lo := by rw [F.env_addr]; omega
      hi := by rw [F.env_addr]; omega
      htif := by rw [F.env_addr]; omega
      align := by rw [F.env_addr]; exact (F.store.frames_arena env henvLt).2
      code := by rw [F.env_addr]; rcases hAimg with h | h <;> omega }
  -- old arrays: allocated when the capacity is positive, `NULL` otherwise
  have hnamesMem : 0 < cap → (pn, 8 * cap) ∈ extsA :=
    fun hc => hheap.ledger.live _ _ _ (hnamesO.nonempty hc)
  have hvalsMem : 0 < cap → (pvals, 24 * cap) ∈ extsA :=
    fun hc => hheap.ledger.live _ _ _ (hvalsO.nonempty hc)
  have hzero : cap = 0 → pn = 0 ∧ pvals = 0 := by
    intro hc
    rcases hnamesO with ⟨_, h1⟩ | ⟨h1, _⟩
    · rcases hvalsO with ⟨_, h2⟩ | ⟨h2, _⟩
      · exact ⟨h1, h2⟩
      · omega
    · omega
  have hsepNV : ExtDisjoint (pn, 8 * cap) (pvals, 24 * cap) := by
    rcases Nat.eq_zero_or_pos cap with hc | hc
    · obtain ⟨h1, h2⟩ := hzero hc
      subst h1; subst h2
      exact Or.inl (by omega)
    · exact hheap.ledger.separated _ _ _ _ _ _ (hnamesO.nonempty hc) (hvalsO.nonempty hc) nofun
  have hsepNR : ExtDisjoint (pn, 8 * cap) (φf env, 32) := by
    rcases Nat.eq_zero_or_pos cap with hc | hc
    · obtain ⟨h1, _⟩ := hzero hc
      subst h1
      exact Or.inl (by omega)
    · exact hheap.ledger.separated _ _ _ _ _ _ (hnamesO.nonempty hc) hrA nofun
  have hsepVR : ExtDisjoint (pvals, 24 * cap) (φf env, 32) := by
    rcases Nat.eq_zero_or_pos cap with hc | hc
    · obtain ⟨_, h2⟩ := hzero hc
      subst h2
      exact Or.inl (by omega)
    · exact hheap.ledger.separated _ _ _ _ _ _ (hvalsO.nonempty hc) hrA nofun
  change pn + 8 * cap ≤ pvals ∨ pvals + 24 * cap ≤ pn at hsepNV
  change pn + 8 * cap ≤ φf env ∨ φf env + 32 ≤ pn at hsepNR
  change pvals + 24 * cap ≤ φf env ∨ φf env + 32 ≤ pvals at hsepVR
  have hnamesArena : 0 < cap → A.lo ≤ pn ∧ pn + 8 * cap ≤ A.hi := by
    intro hc
    obtain ⟨_, h1, h2⟩ := hheap.ledger.arena.1 _ (hnamesMem hc)
    exact ⟨h1, h2⟩
  have hvalsArena : 0 < cap → A.lo ≤ pvals ∧ pvals + 24 * cap ≤ A.hi := by
    intro hc
    obtain ⟨_, h1, h2⟩ := hheap.ledger.arena.1 _ (hvalsMem hc)
    exact ⟨h1, h2⟩
  have hcap30 : cap < 2^30 := by
    rcases Nat.eq_zero_or_pos cap with hc | hc
    · omega
    · have := hvalsArena hc; omega
  have hsharedPriv : ∀ k, shared k → ¬ M.privFoot k :=
    hheap.reserved.outsidePrivate hheap.immutable hprivA
      (fun k hk hnot => absurd (LM.alloc.priv_arena k hk) hnot)
  have hsharedStack : ∀ k, shared k → ¬ (SL.lo ≤ k ∧ k < SL.hi) := by
    intro k hk hin
    exact hheap.immutable.outsideWrites k hk (hstackW k hin.1 hin.2)
  have hextArena : ∀ e ∈ extsA, ∀ k, ExtentByte e k → A.lo ≤ k ∧ k < A.hi := by
    intro e he k hk
    obtain ⟨_, hlo, hhi⟩ := hheap.ledger.arena.1 _ he
    change e.1 ≤ k ∧ k < e.1 + e.2 at hk
    omega
  have henvNat : aEnv.toNat = φf env := F.env_addr
  have hA2' : A.lo ≤ pNamesNew ∧ pNamesNew + 8 * cap' ≤ A.hi := hA2
  have hA4' : A.lo ≤ pValsNew ∧ pValsNew + 24 * cap' ≤ A.hi := hA4
  have A1 : ∀ k, (k < aEnv.toNat + 4 ∨ aEnv.toNat + 8 ≤ k) → c1.σ.mem[k]? = mA[k]? := by
    intro k hk
    rw [hmem1]
    exact getElem_writeMap4_disjoint _ _ _ _ hk
  have A3 : ∀ k, (k < aEnv.toNat + 8 ∨ aEnv.toNat + 16 ≤ k) → c3.σ.mem[k]? = c2.σ.mem[k]? := by
    intro k hk
    rw [hmem3]
    exact getElem_writeMap8_disjoint _ _ _ _ hk
  have A5 : ∀ k, (k < aEnv.toNat + 16 ∨ aEnv.toNat + 24 ≤ k) → c5.σ.mem[k]? = c4.σ.mem[k]? := by
    intro k hk
    rw [hmem5]
    exact getElem_writeMap8_disjoint _ _ _ _ hk
  have hrecNotPriv : ∀ a, φf env ≤ a → a < φf env + 32 → ¬ M.privFoot a :=
    fun a h1 h2 => privOff hprivA hrecMem ⟨h1, h2⟩
  have hrecNotStack : ∀ a, φf env ≤ a → a < φf env + 32 → ¬ (SL.lo ≤ a ∧ a < esp.toNat - 64) := by
    intro a h1 h2 hin
    rcases hAstack with h | h <;> omega
  have hrecNe : (φf env, 32) ≠ (pn, 8 * cap) := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    omega
  have hvalsNeNames : 0 < cap → (pvals, 24 * cap) ≠ (pn, 8 * cap) := by
    intro hc h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    omega
  have hpriv1 : ∀ e ∈ exts1, ∀ i < e.2, ¬ M.privFoot (e.1 + i) :=
    M.privFoot_disjoint c2.σ exts1 hainv2
  have hpriv2 : ∀ e ∈ exts2, ∀ i < e.2, ¬ M.privFoot (e.1 + i) :=
    M.privFoot_disjoint c4.σ exts2 hainv4
  have hrec1 : (φf env, 32) ∈ exts1 := by
    rw [hexts1]
    exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne hrecNe).mpr hrecMem)
  have hnew1 : (pNamesNew, 8 * cap') ∈ exts1 := by rw [hexts1]; exact List.mem_cons_self
  have hrecOffNew : ExtDisjoint (pNamesNew, 8 * cap') (φf env, 32) := hfresh2 _ hrecMem hrecNe
  change pNamesNew + 8 * cap' ≤ φf env ∨ φf env + 32 ≤ pNamesNew at hrecOffNew
  have hrecNeV : (φf env, 32) ≠ (pvals, 24 * cap) := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    omega
  have hrec2 : (φf env, 32) ∈ exts2 := by
    rw [hexts2]
    exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne hrecNeV).mpr hrec1)
  have hrecOffNewV : ExtDisjoint (pValsNew, 24 * cap') (φf env, 32) := hfresh4 _ hrec1 hrecNeV
  change pValsNew + 24 * cap' ≤ φf env ∨ φf env + 32 ≤ pValsNew at hrecOffNewV
  have hnewNe : (pNamesNew, 8 * cap') ≠ (pvals, 24 * cap) := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    rcases Nat.eq_zero_or_pos cap with hc | hc
    · omega
    · have := hfresh2 _ (hvalsMem hc) (hvalsNeNames hc)
      change pNamesNew + 8 * cap' ≤ pvals ∨ pvals + 24 * cap ≤ pNamesNew at this
      omega
  have hnewNewDisj : ExtDisjoint (pValsNew, 24 * cap') (pNamesNew, 8 * cap') :=
    hfresh4 _ hnew1 hnewNe
  change pValsNew + 24 * cap' ≤ pNamesNew ∨ pNamesNew + 8 * cap' ≤ pValsNew at hnewNewDisj
  have hnewOldV : 0 < cap → ExtDisjoint (pNamesNew, 8 * cap') (pvals, 24 * cap) :=
    fun hc => hfresh2 _ (hvalsMem hc) (hvalsNeNames hc)
  have hrecAg34 : ∀ a, φf env ≤ a → a < φf env + 32 → c4.σ.mem[a]? = c3.σ.mem[a]? := by
    intro a h1 h2
    exact A4 a (hrecNotPriv a h1 h2) (hrecNotStack a h1 h2) (by omega) (by omega)
  have hrecAg12 : ∀ a, φf env ≤ a → a < φf env + 32 → c2.σ.mem[a]? = c1.σ.mem[a]? := by
    intro a h1 h2
    exact A2 a (hrecNotPriv a h1 h2) (hrecNotStack a h1 h2) (by omega) (by omega)
  have hpNamesLt : pNamesNew < 2^64 := by omega
  have hpValsLt : pValsNew < 2^64 := by omega
  have hcap2 : read32 c2.σ.mem (aEnv.toNat + 4) = some cap' := by
    rw [← read32_agreeP (P := fun a => φf env ≤ a ∧ a < φf env + 32)
      (fun a ha => (hrecAg12 a ha.1 ha.2).symm) (fun k hk => by rw [henvNat] at *; omega)]
    rw [hmem1, read32_writeMap4, swData_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hnames4 : read64 c4.σ.mem (aEnv.toNat + 8) = some pNamesNew := by
    rw [← read64_agreeP (P := fun a => φf env ≤ a ∧ a < φf env + 32)
      (fun a ha => (hrecAg34 a ha.1 ha.2).symm) (fun k hk => by rw [henvNat] at *; omega)]
    rw [hmem3, read64_writeMap8, sdData_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpNamesLt]
  have hOffText : ∀ a, 0x80000000 ≤ a → a < 0x80018be0 → ¬ (A.lo ≤ a ∧ a < A.hi) := by
    intro a h1 h2 hin
    rcases hAimg with h | h <;> omega
  have hOffTextStack : ∀ a, 0x80000000 ≤ a → a < 0x80018be0 →
      ¬ (SL.lo ≤ a ∧ a < esp.toNat - 64) := by
    intro a h1 h2 hin
    omega
  have hnamesInArena : ∀ k, pn ≤ k → k < pn + 8 * cap → A.lo ≤ k ∧ k < A.hi := by
    intro k h1 h2
    have hc : 0 < cap := by omega
    have := hnamesArena hc
    omega
  have hvalsInArena : ∀ k, pvals ≤ k → k < pvals + 24 * cap → A.lo ≤ k ∧ k < A.hi := by
    intro k h1 h2
    have hc : 0 < cap := by omega
    have := hvalsArena hc
    omega
  -- ── the master agreement with the arm memory
  have hagOff : ∀ k, ¬ M.privFoot k → ¬ (SL.lo ≤ k ∧ k < esp.toNat - 64) →
      (k < pn ∨ pn + 8 * cap ≤ k) → (k < pNamesNew ∨ pNamesNew + 8 * cap' ≤ k) →
      (k < pvals ∨ pvals + 24 * cap ≤ k) → (k < pValsNew ∨ pValsNew + 24 * cap' ≤ k) →
      (k < aEnv.toNat + 4 ∨ aEnv.toNat + 24 ≤ k) → c5.σ.mem[k]? = mA[k]? := by
    intro k h1 h2 h3 h4 h5 h6 h7
    rw [A5 k (by omega), A4 k h1 h2 h5 h6, A3 k (by omega), A2 k h1 h2 h3 h4, A1 k (by omega)]
  -- the record's surviving words
  have hrecAg5 : ∀ a, φf env ≤ a → a < φf env + 32 → (a < φf env + 4 ∨ φf env + 24 ≤ a) →
      c5.σ.mem[a]? = mA[a]? := by
    intro a h1 h2 h3
    have hoffN : a < pn ∨ pn + 8 * cap ≤ a := by
      rcases hsepNR with h | h
      · right; omg
      · left; omg
    have hoffNN : a < pNamesNew ∨ pNamesNew + 8 * cap' ≤ a := by
      rcases hrecOffNew with h | h
      · right; omg
      · left; omg
    have hoffV : a < pvals ∨ pvals + 24 * cap ≤ a := by
      rcases hsepVR with h | h
      · right; omg
      · left; omg
    have hoffNV : a < pValsNew ∨ pValsNew + 24 * cap' ≤ a := by
      rcases hrecOffNewV with h | h
      · right; omg
      · left; omg
    exact hagOff a (hrecNotPriv a h1 h2) (hrecNotStack a h1 h2) hoffN hoffNN hoffV hoffNV
      (by rw [henvNat]; exact h3)
  have hcount5 : read32 c5.σ.mem (φf env) = some (st.store.frames[env]).vars.length := by
    rw [← read32_agreeP (P := fun a => φf env ≤ a ∧ a < φf env + 4)
      (fun a ha => (hrecAg5 a ha.1 (by omg) (Or.inl ha.2)).symm) (fun k hk => by omg)]
    exact hcountR
  have hparent5 : read64 c5.σ.mem (φf env + 24) = read64 mA (φf env + 24) :=
    (read64_agreeP (P := fun a => φf env + 24 ≤ a ∧ a < φf env + 32)
      (fun a ha => (hrecAg5 a (by omg) ha.2 (Or.inr ha.1)).symm) (fun k hk => by omg)).symm
  have hcap5 : read32 c5.σ.mem (φf env + 4) = some cap' := by
    have hag : ∀ a, φf env + 4 ≤ a → a < φf env + 8 → c5.σ.mem[a]? = c2.σ.mem[a]? := by
      intro a h1 h2
      rw [A5 a (by rw [henvNat]; omg), hrecAg34 a (by omg) (by omg), A3 a (by rw [henvNat]; omg)]
    rw [← read32_agreeP (P := fun a => φf env + 4 ≤ a ∧ a < φf env + 8)
      (fun a ha => (hag a ha.1 ha.2).symm) (fun k hk => by omg)]
    rw [← henvNat]; exact hcap2
  have hpn5 : read64 c5.σ.mem (φf env + 8) = some pNamesNew := by
    have hag : ∀ a, φf env + 8 ≤ a → a < φf env + 16 → c5.σ.mem[a]? = c4.σ.mem[a]? := by
      intro a h1 h2
      rw [A5 a (by rw [henvNat]; omg)]
    rw [← read64_agreeP (P := fun a => φf env + 8 ≤ a ∧ a < φf env + 16)
      (fun a ha => (hag a ha.1 ha.2).symm) (fun k hk => by omg)]
    rw [← henvNat]; exact hnames4
  have hpv5 : read64 c5.σ.mem (φf env + 16) = some pValsNew := by
    rw [hmem5, ← henvNat, read64_writeMap8, sdData_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hpValsLt]
  -- the copied slots
  have hkeys : ∀ i, i < (st.store.frames[env]).vars.length → ∀ k, k < 8 →
      c5.σ.mem[pNamesNew + 8 * i + k]? = mA[pn + 8 * i + k]? := by
    intro i hi k hk
    have hc : 0 < cap := by omg
    have hj : 8 * i + k < 8 * cap := by omg
    have hkNew : pNamesNew ≤ pNamesNew + 8 * i + k ∧
        pNamesNew + 8 * i + k < pNamesNew + 8 * cap' := by omg
    have hnewV := hnewOldV hc
    change pNamesNew + 8 * cap' ≤ pvals ∨ pvals + 24 * cap ≤ pNamesNew at hnewV
    have h5 : pNamesNew + 8 * i + k < aEnv.toNat + 16 ∨ aEnv.toNat + 24 ≤ pNamesNew + 8 * i + k := by
      rw [henvNat]
      rcases hrecOffNew with h | h
      · left; omg
      · right; omg
    have h3 : pNamesNew + 8 * i + k < aEnv.toNat + 8 ∨ aEnv.toNat + 16 ≤ pNamesNew + 8 * i + k := by
      rw [henvNat]
      rcases hrecOffNew with h | h
      · left; omg
      · right; omg
    have h4v : pNamesNew + 8 * i + k < pvals ∨ pvals + 24 * cap ≤ pNamesNew + 8 * i + k := by
      rcases hnewV with h | h
      · left; omg
      · right; omg
    have h4n : pNamesNew + 8 * i + k < pValsNew ∨ pValsNew + 24 * cap' ≤ pNamesNew + 8 * i + k := by
      rcases hnewNewDisj with h | h
      · right; omg
      · left; omg
    have h1 : pn + 8 * i + k < aEnv.toNat + 4 ∨ aEnv.toNat + 8 ≤ pn + 8 * i + k := by
      rw [henvNat]
      rcases hsepNR with h | h
      · left; omg
      · right; omg
    have hns : ¬ (SL.lo ≤ pNamesNew + 8 * i + k ∧ pNamesNew + 8 * i + k < esp.toNat - 64) := by
      intro hin
      rcases hAstack with h | h <;> omg
    rw [A5 _ h5, A4 _ (privOff hpriv1 hnew1 hkNew) hns h4v h4n, A3 _ h3,
      show pNamesNew + 8 * i + k = pNamesNew + (8 * i + k) by omg, C1 _ hj,
      show pn + (8 * i + k) = pn + 8 * i + k by omg, A1 _ h1]
  have hvals : ∀ i, i < (st.store.frames[env]).vars.length → ∀ k, k < 24 →
      c5.σ.mem[pValsNew + 24 * i + k]? = mA[pvals + 24 * i + k]? := by
    intro i hi k hk
    have hc : 0 < cap := by omg
    have hj : 24 * i + k < 24 * cap := by omg
    have hkOld : pvals ≤ pvals + 24 * i + k ∧ pvals + 24 * i + k < pvals + 24 * cap := by omg
    have hkNew : pValsNew ≤ pValsNew + 24 * i + k ∧
        pValsNew + 24 * i + k < pValsNew + 24 * cap' := by omg
    have hnewV := hnewOldV hc
    change pNamesNew + 8 * cap' ≤ pvals ∨ pvals + 24 * cap ≤ pNamesNew at hnewV
    have h5 : pValsNew + 24 * i + k < aEnv.toNat + 16 ∨ aEnv.toNat + 24 ≤ pValsNew + 24 * i + k := by
      rw [henvNat]
      rcases hrecOffNewV with h | h
      · left; omg
      · right; omg
    have h3 : pvals + 24 * i + k < aEnv.toNat + 8 ∨ aEnv.toNat + 16 ≤ pvals + 24 * i + k := by
      rw [henvNat]
      rcases hsepVR with h | h
      · left; omg
      · right; omg
    have h2n : pvals + 24 * i + k < pn ∨ pn + 8 * cap ≤ pvals + 24 * i + k := by
      rcases hsepNV with h | h
      · right; omg
      · left; omg
    have h2nn : pvals + 24 * i + k < pNamesNew ∨ pNamesNew + 8 * cap' ≤ pvals + 24 * i + k := by
      rcases hnewV with h | h
      · right; omg
      · left; omg
    have h1 : pvals + 24 * i + k < aEnv.toNat + 4 ∨ aEnv.toNat + 8 ≤ pvals + 24 * i + k := by
      rw [henvNat]
      rcases hsepVR with h | h
      · left; omg
      · right; omg
    have hns : ¬ (SL.lo ≤ pvals + 24 * i + k ∧ pvals + 24 * i + k < esp.toNat - 64) := by
      intro hin
      have := hvalsArena hc
      rcases hAstack with h | h <;> omg
    rw [A5 _ h5, show pValsNew + 24 * i + k = pValsNew + (24 * i + k) by omg, C2 _ hj,
      show pvals + (24 * i + k) = pvals + 24 * i + k by omg, A3 _ h3,
      A2 _ (privOff hprivA (hvalsMem hc) hkOld) hns h2n h2nn, A1 _ h1]
  have htext5 : FixedTextLoaded c5.σ.mem := by
    apply htext4.transport
    intro a h1 h2
    have hoffR : a < aEnv.toNat + 16 ∨ aEnv.toNat + 24 ≤ a := by
      rw [henvNat]
      rcases Nat.lt_or_ge a (φf env + 16) with h | h
      · exact Or.inl h
      · right; omg
    exact A5 a hoffR
  have hext5 : MemExtends mA c5.σ.mem := by
    rw [hmem5]
    refine ((((?_ : MemExtends mA c1.σ.mem).trans ext2).trans ?_).trans ext4).trans
      (memExtends_writeMap8 _ _ _)
    · rw [hmem1]; exact memExtends_writeMap4 _ _ _
    · rw [hmem3]; exact memExtends_writeMap8 _ _ _
  exact
    { agOff := hagOff
      count := by
        exact (read32_agreeP (P := fun a => φf env ≤ a ∧ a < φf env + 4)
          (fun a ha => (hrecAg5 a ha.1 (by omg) (Or.inl ha.2)).symm) (fun k hk => by omg)).symm
      parent := hparent5
      capRead := hcap5
      namesRead := hpn5
      valsRead := hpv5
      keys := fun i hi k hk => hkeys i (by omg) k hk
      values := fun i hi k hk => hvals i (by omg) k hk
      ext := hext5
      text := htext5 }

/-- **The grow lane's untouched bytes** from the memory core. -/
theorem envDefineGrowMemOff
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts extsA : List Extent) (mA : Mem)
    (cap pn pvals : Nat) (c0 : Config)
    (hE : EnvDefineMem N A SL φf φc st env x v aEnv aName pv esp m)
    (L : EnvDefineUpdateLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (LM : EnvDefineMissLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (F : EnvDefineMissFacts g N A SL φf φc st env x v esp aEnv aName pv r m extsA mA cap)
    (R : EnvDefineMissRegs g A SL st env esp aEnv aName pv r out M extsA mA F.env_lt c0)
    (hfull : (st.store.frames[env]'F.env_lt).vars.length = cap)
    (hpn : read64 mA (φf env + 8) = some pn)
    (hpvals : read64 mA (φf env + 16) = some pvals)
    (hgrowReq : 48 * cap ≤ maxReq)
    (c1 c2 c3 c4 c5 : Config) (cap' pNamesNew pValsNew : Nat) (exts1 exts2 : List Extent)
    (D : GrowCallsData A SL M mA aEnv esp extsA pn pvals cap c0 c1 c2 c3 c4 c5
      cap' pNamesNew pValsNew exts1 exts2)
    (alloc : Allocations) (shared readable writes : Nat → Prop)
    (hheap : HeapOwned A extsA mA φf φc alloc shared readable writes st.store)
    (hstackW : ∀ k, SL.lo ≤ k → k < SL.hi → writes k)
    (K : GrowMemCore A SL M mA c5.σ.mem φf env aEnv esp pn pvals cap pNamesNew pValsNew cap') :
    GrowMemFacts A SL mA c5.σ.mem φf env esp pv alloc shared pn pvals cap pNamesNew pValsNew cap' := by
  have hcapLt := D.capLt
  have hcapPos := D.capPos
  have hcapS' := D.capS
  have hprivA := D.privA
  have hmem1 := D.mem1
  have A2 := D.A2
  have C1 := D.C1
  have hmem3 := D.mem3
  have A4 := D.A4
  have C2 := D.C2
  have hmem5 := D.mem5
  have ext2 := D.ext2
  have ext4 := D.ext4
  have hnz2 := D.nz2
  have hal2 := D.al2
  have hA2 := D.hA2
  have hnz4 := D.nz4
  have hal4 := D.al4
  have hA4 := D.hA4
  have hfresh2 := D.fresh2
  have hfresh4 := D.fresh4
  have hexts1 := D.exts1_def
  have hexts2 := D.exts2_def
  have hainv2 := D.ainv2
  have hainv4 := D.ainv4
  have htext4 := D.text4
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
  have henvLt := F.env_lt
  have hfull' : (st.store.frames[env]).vars.length = cap := hfull
  have hfo := hheap.store.frames env henvLt
  obtain ⟨arr, harr⟩ := hfo.arrays
  obtain ⟨hcountR, ⟨cap0, hcap0, hcaple⟩, ⟨pn0, pvals0, hpn0, hpvals0, hslots⟩, hpar⟩ :=
    F.store.frames env henvLt
  have hcapEq : cap0 = cap := Option.some.inj (hcap0.symm.trans F.cap_read)
  subst cap0
  have hpnEq : pn0 = pn := Option.some.inj (hpn0.symm.trans hpn)
  subst pn0
  have hpvEq : pvals0 = pvals := Option.some.inj (hpvals0.symm.trans hpvals)
  subst pvals0
  have ecap : arr.cap = cap := Option.some.inj (harr.capRead.symm.trans F.cap_read)
  have enames : arr.names = pn := Option.some.inj (harr.namesRead.symm.trans hpn)
  have evals : arr.values = pvals := Option.some.inj (harr.valuesRead.symm.trans hpvals)
  have hnamesO : ArrayOwned alloc (.names env) pn 8 cap := by
    have := harr.names; rwa [enames, ecap] at this
  have hvalsO : ArrayOwned alloc (.values env) pvals 24 cap := by
    have := harr.values; rwa [evals, ecap] at this
  have hrA : Allocated alloc (.frame env) (φf env) 32 := hfo.record
  have hrecMem : (φf env, 32) ∈ extsA := hheap.ledger.live _ _ _ hrA
  obtain ⟨_, hrLo, hrHi⟩ := hheap.ledger.arena.1 _ hrecMem
  have hcapS : cap < 2^31 := hfo.capSigned hheap.ledger F.cap_read (by omega)
  have henvGeom : EnvRecordGeom aEnv :=
    { lo := by rw [F.env_addr]; omega
      hi := by rw [F.env_addr]; omega
      htif := by rw [F.env_addr]; omega
      align := by rw [F.env_addr]; exact (F.store.frames_arena env henvLt).2
      code := by rw [F.env_addr]; rcases hAimg with h | h <;> omega }
  -- old arrays: allocated when the capacity is positive, `NULL` otherwise
  have hnamesMem : 0 < cap → (pn, 8 * cap) ∈ extsA :=
    fun hc => hheap.ledger.live _ _ _ (hnamesO.nonempty hc)
  have hvalsMem : 0 < cap → (pvals, 24 * cap) ∈ extsA :=
    fun hc => hheap.ledger.live _ _ _ (hvalsO.nonempty hc)
  have hzero : cap = 0 → pn = 0 ∧ pvals = 0 := by
    intro hc
    rcases hnamesO with ⟨_, h1⟩ | ⟨h1, _⟩
    · rcases hvalsO with ⟨_, h2⟩ | ⟨h2, _⟩
      · exact ⟨h1, h2⟩
      · omega
    · omega
  have hsepNV : ExtDisjoint (pn, 8 * cap) (pvals, 24 * cap) := by
    rcases Nat.eq_zero_or_pos cap with hc | hc
    · obtain ⟨h1, h2⟩ := hzero hc
      subst h1; subst h2
      exact Or.inl (by omega)
    · exact hheap.ledger.separated _ _ _ _ _ _ (hnamesO.nonempty hc) (hvalsO.nonempty hc) nofun
  have hsepNR : ExtDisjoint (pn, 8 * cap) (φf env, 32) := by
    rcases Nat.eq_zero_or_pos cap with hc | hc
    · obtain ⟨h1, _⟩ := hzero hc
      subst h1
      exact Or.inl (by omega)
    · exact hheap.ledger.separated _ _ _ _ _ _ (hnamesO.nonempty hc) hrA nofun
  have hsepVR : ExtDisjoint (pvals, 24 * cap) (φf env, 32) := by
    rcases Nat.eq_zero_or_pos cap with hc | hc
    · obtain ⟨_, h2⟩ := hzero hc
      subst h2
      exact Or.inl (by omega)
    · exact hheap.ledger.separated _ _ _ _ _ _ (hvalsO.nonempty hc) hrA nofun
  change pn + 8 * cap ≤ pvals ∨ pvals + 24 * cap ≤ pn at hsepNV
  change pn + 8 * cap ≤ φf env ∨ φf env + 32 ≤ pn at hsepNR
  change pvals + 24 * cap ≤ φf env ∨ φf env + 32 ≤ pvals at hsepVR
  have hnamesArena : 0 < cap → A.lo ≤ pn ∧ pn + 8 * cap ≤ A.hi := by
    intro hc
    obtain ⟨_, h1, h2⟩ := hheap.ledger.arena.1 _ (hnamesMem hc)
    exact ⟨h1, h2⟩
  have hvalsArena : 0 < cap → A.lo ≤ pvals ∧ pvals + 24 * cap ≤ A.hi := by
    intro hc
    obtain ⟨_, h1, h2⟩ := hheap.ledger.arena.1 _ (hvalsMem hc)
    exact ⟨h1, h2⟩
  have hcap30 : cap < 2^30 := by
    rcases Nat.eq_zero_or_pos cap with hc | hc
    · omega
    · have := hvalsArena hc; omega
  have hsharedPriv : ∀ k, shared k → ¬ M.privFoot k :=
    hheap.reserved.outsidePrivate hheap.immutable hprivA
      (fun k hk hnot => absurd (LM.alloc.priv_arena k hk) hnot)
  have hsharedStack : ∀ k, shared k → ¬ (SL.lo ≤ k ∧ k < SL.hi) := by
    intro k hk hin
    exact hheap.immutable.outsideWrites k hk (hstackW k hin.1 hin.2)
  have hextArena : ∀ e ∈ extsA, ∀ k, ExtentByte e k → A.lo ≤ k ∧ k < A.hi := by
    intro e he k hk
    obtain ⟨_, hlo, hhi⟩ := hheap.ledger.arena.1 _ he
    change e.1 ≤ k ∧ k < e.1 + e.2 at hk
    omega
  have henvNat : aEnv.toNat = φf env := F.env_addr
  have hA2' : A.lo ≤ pNamesNew ∧ pNamesNew + 8 * cap' ≤ A.hi := hA2
  have hA4' : A.lo ≤ pValsNew ∧ pValsNew + 24 * cap' ≤ A.hi := hA4
  have hagOff := K.agOff
  have hrecNe : (φf env, 32) ≠ (pn, 8 * cap) := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    omega
  have hnamesInArena : ∀ k, pn ≤ k → k < pn + 8 * cap → A.lo ≤ k ∧ k < A.hi := by
    intro k h1 h2
    have hc : 0 < cap := by omega
    have := hnamesArena hc
    omega
  have hvalsInArena : ∀ k, pvals ≤ k → k < pvals + 24 * cap → A.lo ≤ k ∧ k < A.hi := by
    intro k h1 h2
    have hc : 0 < cap := by omega
    have := hvalsArena hc
    omega
  -- bytes of every other allocation are untouched
  have hOtherOff : ∀ role q nn, role ≠ .frame env → role ≠ .names env → role ≠ .values env →
      Allocated alloc role q nn → ∀ k, ExtentByte (q, nn) k → c5.σ.mem[k]? = mA[k]? := by
    intro role q nn h1 h2 h3 hq k hk
    have hqMem := hheap.ledger.live _ _ _ hq
    have hkA := hextArena _ hqMem k hk
    have hkE : q ≤ k ∧ k < q + nn := hk
    obtain ⟨hqPos, _⟩ := hheap.ledger.arena.1 _ hqMem
    have hsepR := hheap.ledger.separated _ _ _ _ _ _ hq hrA h1
    change q + nn ≤ φf env ∨ φf env + 32 ≤ q at hsepR
    have hoffN : k < pn ∨ pn + 8 * cap ≤ k := by
      rcases Nat.eq_zero_or_pos cap with hc | hc
      · obtain ⟨hz, _⟩ := hzero hc; subst hz; right; omg
      · have := hheap.ledger.separated _ _ _ _ _ _ hq (hnamesO.nonempty hc) h2
        change q + nn ≤ pn ∨ pn + 8 * cap ≤ q at this
        rcases this with h | h
        · left; omg
        · right; omg
    have hoffV : k < pvals ∨ pvals + 24 * cap ≤ k := by
      rcases Nat.eq_zero_or_pos cap with hc | hc
      · obtain ⟨_, hz⟩ := hzero hc; subst hz; right; omg
      · have := hheap.ledger.separated _ _ _ _ _ _ hq (hvalsO.nonempty hc) h3
        change q + nn ≤ pvals ∨ pvals + 24 * cap ≤ q at this
        rcases this with h | h
        · left; omg
        · right; omg
    have hqNeN : (q, nn) ≠ (pn, 8 * cap) := by
      intro h
      have e1 := congrArg Prod.fst h
      have e2 := congrArg Prod.snd h
      simp only at e1 e2
      rcases hoffN with h' | h' <;> omg
    have hqNeV : (q, nn) ≠ (pvals, 24 * cap) := by
      intro h
      have e1 := congrArg Prod.fst h
      have e2 := congrArg Prod.snd h
      simp only at e1 e2
      rcases hoffV with h' | h' <;> omg
    have hfN := hfresh2 _ hqMem hqNeN
    change pNamesNew + 8 * cap' ≤ q ∨ q + nn ≤ pNamesNew at hfN
    have hq1 : (q, nn) ∈ exts1 := by
      rw [hexts1]
      exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne hqNeN).mpr hqMem)
    have hfV := hfresh4 _ hq1 hqNeV
    change pValsNew + 24 * cap' ≤ q ∨ q + nn ≤ pValsNew at hfV
    have hnp : ¬ M.privFoot k := privOff hprivA hqMem hk
    have hns : ¬ (SL.lo ≤ k ∧ k < esp.toNat - 64) := by
      intro hin
      rcases hAstack with h | h <;> omg
    have hoffNN : k < pNamesNew ∨ pNamesNew + 8 * cap' ≤ k := by
      rcases hfN with h | h
      · right; omg
      · left; omg
    have hoffNV : k < pValsNew ∨ pValsNew + 24 * cap' ≤ k := by
      rcases hfV with h | h
      · right; omg
      · left; omg
    have hoffR : k < aEnv.toNat + 4 ∨ aEnv.toNat + 24 ≤ k := by
      rw [henvNat]
      rcases hsepR with h | h
      · left; omg
      · right; omg
    exact hagOff k hnp hns hoffN hoffNN hoffV hoffNV hoffR
  -- shared bytes are untouched
  have hSharedOff : ∀ k, shared k → c5.σ.mem[k]? = mA[k]? := by
    intro k hk
    have hp := hsharedPriv k hk
    have hst := hsharedStack k hk
    have hoffRec := hheap.immutable.outsideMutable (.frame env) _ _ (by trivial) hrA k hk
    change ¬ (φf env ≤ k ∧ k < φf env + 32) at hoffRec
    have hoffN : k < pn ∨ pn + 8 * cap ≤ k := by
      rcases Nat.eq_zero_or_pos cap with hc | hc
      · obtain ⟨hz, _⟩ := hzero hc; subst hz; right; omg
      · have := hheap.immutable.outsideMutable (.names env) _ _ (by trivial)
          (hnamesO.nonempty hc) k hk
        change ¬ (pn ≤ k ∧ k < pn + 8 * cap) at this
        rcases Nat.lt_or_ge k pn with h | h
        · left; exact h
        · right; omg
    have hoffV : k < pvals ∨ pvals + 24 * cap ≤ k := by
      rcases Nat.eq_zero_or_pos cap with hc | hc
      · obtain ⟨_, hz⟩ := hzero hc; subst hz; right; omg
      · have := hheap.immutable.outsideMutable (.values env) _ _ (by trivial)
          (hvalsO.nonempty hc) k hk
        change ¬ (pvals ≤ k ∧ k < pvals + 24 * cap) at this
        rcases Nat.lt_or_ge k pvals with h | h
        · left; exact h
        · right; omg
    -- the fresh arrays lie in the arena: a shared arena byte has a live cover
    have hcover : (A.lo ≤ k ∧ k < A.hi) → ∃ e ∈ extsA, ExtentByte e k ∧ e ≠ (pn, 8 * cap) ∧
        e ≠ (pvals, 24 * cap) := by
      intro hkA
      obtain ⟨e, he, hek⟩ := hheap.reserved.live k hk hkA.1 hkA.2
      have hek' : e.1 ≤ k ∧ k < e.1 + e.2 := hek
      refine ⟨e, he, hek, ?_, ?_⟩
      · intro h; subst h; simp only at hek'; rcases hoffN with h' | h' <;> omg
      · intro h; subst h; simp only at hek'; rcases hoffV with h' | h' <;> omg
    have hoffNN : k < pNamesNew ∨ pNamesNew + 8 * cap' ≤ k := by
      by_cases hkA : A.lo ≤ k ∧ k < A.hi
      · obtain ⟨e, he, hek, hne1, _⟩ := hcover hkA
        have := hfresh2 e he hne1
        change pNamesNew + 8 * cap' ≤ e.1 ∨ e.1 + e.2 ≤ pNamesNew at this
        have hek' : e.1 ≤ k ∧ k < e.1 + e.2 := hek
        rcases this with h | h
        · right; omg
        · left; omg
      · rcases Nat.lt_or_ge k pNamesNew with h | h
        · left; exact h
        · right; omg
    have hoffNV : k < pValsNew ∨ pValsNew + 24 * cap' ≤ k := by
      by_cases hkA : A.lo ≤ k ∧ k < A.hi
      · obtain ⟨e, he, hek, hne1, hne2⟩ := hcover hkA
        have he1 : e ∈ exts1 := by
          rw [hexts1]
          exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne hne1).mpr he)
        have := hfresh4 e he1 hne2
        change pValsNew + 24 * cap' ≤ e.1 ∨ e.1 + e.2 ≤ pValsNew at this
        have hek' : e.1 ≤ k ∧ k < e.1 + e.2 := hek
        rcases this with h | h
        · right; omg
        · left; omg
      · rcases Nat.lt_or_ge k pValsNew with h | h
        · left; exact h
        · right; omg
    have hns : ¬ (SL.lo ≤ k ∧ k < esp.toNat - 64) := fun hin => hst ⟨hin.1, by omg⟩
    have hoffR : k < aEnv.toNat + 4 ∨ aEnv.toNat + 24 ≤ k := by
      rw [henvNat]
      rcases Nat.lt_or_ge k (φf env + 4) with h | h
      · left; exact h
      · right; omg
    exact hagOff k hp hns hoffN hoffNN hoffV hoffNV hoffR
  -- bytes outside the arena and outside the callee's window are untouched
  have hOffArena : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → ¬ (SL.lo ≤ k ∧ k < esp.toNat - 64) →
      c5.σ.mem[k]? = mA[k]? := by
    intro k hkA hkS
    have hoffN : k < pn ∨ pn + 8 * cap ≤ k := by
      rcases Nat.lt_or_ge k pn with h | h
      · exact Or.inl h
      · rcases Nat.lt_or_ge k (pn + 8 * cap) with h' | h'
        · exact absurd (hnamesInArena k h h') hkA
        · exact Or.inr h'
    have hoffV : k < pvals ∨ pvals + 24 * cap ≤ k := by
      rcases Nat.lt_or_ge k pvals with h | h
      · exact Or.inl h
      · rcases Nat.lt_or_ge k (pvals + 24 * cap) with h' | h'
        · exact absurd (hvalsInArena k h h') hkA
        · exact Or.inr h'
    have hoffNN : k < pNamesNew ∨ pNamesNew + 8 * cap' ≤ k := by
      rcases Nat.lt_or_ge k pNamesNew with h | h
      · left; exact h
      · right; omg
    have hoffNV : k < pValsNew ∨ pValsNew + 24 * cap' ≤ k := by
      rcases Nat.lt_or_ge k pValsNew with h | h
      · left; exact h
      · right; omg
    have hoffR : k < aEnv.toNat + 4 ∨ aEnv.toNat + 24 ≤ k := by
      rw [henvNat]
      rcases Nat.lt_or_ge k (φf env + 4) with h | h
      · left; exact h
      · right; omg
    exact hagOff k (fun hp => hkA (LM.alloc.priv_arena k hp)) hkS hoffN hoffNN hoffV hoffNV hoffR
  -- the staged value slot is untouched
  have hSlotOff : ∀ k, valHeader pv.toNat k → c5.σ.mem[k]? = mA[k]? := by
    intro k hk
    unfold valHeader at hk
    have hkNA : ¬ (A.lo ≤ k ∧ k < A.hi) := by
      intro hin
      rcases hAstack with h | h <;> omg
    exact hOffArena k hkNA (by omg)
  exact
    { other := hOtherOff
      sharedOff := hSharedOff
      offArena := hOffArena
      slot := hSlotOff }

/-- **The grow lane.**  From either entry, under both ledgers and the entry
facts, the helper reaches the append head over the post-`realloc` ledger. -/
theorem envDefineGrowLane
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts extsA : List Extent) (mA : Mem)
    (cap pn pvals : Nat) (c0 : Config)
    (hE : EnvDefineMem N A SL φf φc st env x v aEnv aName pv esp m)
    (L : EnvDefineUpdateLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (LM : EnvDefineMissLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (F : EnvDefineMissFacts g N A SL φf φc st env x v esp aEnv aName pv r m extsA mA cap)
    (R : EnvDefineMissRegs g A SL st env esp aEnv aName pv r out M extsA mA F.env_lt c0)
    (hfull : (st.store.frames[env]'F.env_lt).vars.length = cap)
    (hpn : read64 mA (φf env + 8) = some pn)
    (hpvals : read64 mA (φf env + 16) = some pvals)
    (hgrowReq : 48 * cap ≤ maxReq)
    (K : EnvDefineGrowKind cap c0)
    (hs6 : c0.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 pn)) :
    ∃ (c' : Config) (extsA' : List Extent) (mA' : Mem) (cap' : Nat),
      Steps c0 c' ∧
      EnvDefineAppendHead g N A SL φf φc st env x v esp aEnv aName pv r m out M extsA' mA' cap' c' := by
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
  have hAstack := LM.alloc.arena_stack
  have hAimg := hE.arena_image
  have hpvNat := hE.pv_frame
  have hslot := hE.slot_in_stack
  have henvLt := F.env_lt
  have hfull' : (st.store.frames[env]).vars.length = cap := hfull
  obtain ⟨alloc, shared, readable, writes, hheap, hstackW, hvalO, hnameO⟩ := F.owned
  have hfo := hheap.store.frames env henvLt
  obtain ⟨arr, harr⟩ := hfo.arrays
  obtain ⟨hcountR, ⟨cap0, hcap0, hcaple⟩, ⟨pn0, pvals0, hpn0, hpvals0, hslots⟩, hpar⟩ :=
    F.store.frames env henvLt
  have hcapEq : cap0 = cap := Option.some.inj (hcap0.symm.trans F.cap_read)
  subst cap0
  have hpnEq : pn0 = pn := Option.some.inj (hpn0.symm.trans hpn)
  subst pn0
  have hpvEq : pvals0 = pvals := Option.some.inj (hpvals0.symm.trans hpvals)
  subst pvals0
  have ecap : arr.cap = cap := Option.some.inj (harr.capRead.symm.trans F.cap_read)
  have enames : arr.names = pn := Option.some.inj (harr.namesRead.symm.trans hpn)
  have evals : arr.values = pvals := Option.some.inj (harr.valuesRead.symm.trans hpvals)
  have hnamesO : ArrayOwned alloc (.names env) pn 8 cap := by
    have := harr.names; rwa [enames, ecap] at this
  have hvalsO : ArrayOwned alloc (.values env) pvals 24 cap := by
    have := harr.values; rwa [evals, ecap] at this
  have hrA : Allocated alloc (.frame env) (φf env) 32 := hfo.record
  have hrecMem : (φf env, 32) ∈ extsA := hheap.ledger.live _ _ _ hrA
  obtain ⟨_, hrLo, hrHi⟩ := hheap.ledger.arena.1 _ hrecMem
  have hzero : cap = 0 → pn = 0 ∧ pvals = 0 := by
    intro hc
    rcases hnamesO with ⟨_, h1⟩ | ⟨h1, _⟩
    · rcases hvalsO with ⟨_, h2⟩ | ⟨h2, _⟩
      · exact ⟨h1, h2⟩
      · omega
    · omega
  have hsepNV : ExtDisjoint (pn, 8 * cap) (pvals, 24 * cap) := by
    rcases Nat.eq_zero_or_pos cap with hc | hc
    · obtain ⟨h1, h2⟩ := hzero hc
      subst h1; subst h2
      exact Or.inl (by omega)
    · exact hheap.ledger.separated _ _ _ _ _ _ (hnamesO.nonempty hc) (hvalsO.nonempty hc) nofun
  have hsepNR : ExtDisjoint (pn, 8 * cap) (φf env, 32) := by
    rcases Nat.eq_zero_or_pos cap with hc | hc
    · obtain ⟨h1, _⟩ := hzero hc
      subst h1
      exact Or.inl (by omega)
    · exact hheap.ledger.separated _ _ _ _ _ _ (hnamesO.nonempty hc) hrA nofun
  have hsepVR : ExtDisjoint (pvals, 24 * cap) (φf env, 32) := by
    rcases Nat.eq_zero_or_pos cap with hc | hc
    · obtain ⟨_, h2⟩ := hzero hc
      subst h2
      exact Or.inl (by omega)
    · exact hheap.ledger.separated _ _ _ _ _ _ (hvalsO.nonempty hc) hrA nofun
  change pn + 8 * cap ≤ pvals ∨ pvals + 24 * cap ≤ pn at hsepNV
  change pn + 8 * cap ≤ φf env ∨ φf env + 32 ≤ pn at hsepNR
  change pvals + 24 * cap ≤ φf env ∨ φf env + 32 ≤ pvals at hsepVR
  -- ── the calls and the memory facts
  obtain ⟨c1, c2, c3, c4, c5, cap', pNamesNew, pValsNew, exts1, exts2, D⟩ :=
    envDefineGrowCalls g N A SL φf φc st env x v esp aEnv aName pv r m out M exts extsA
      mA cap pn pvals c0 hE L LM F R hfull hpn hpvals hgrowReq K hs6
  have K := envDefineGrowMemCore g N A SL φf φc st env x v esp aEnv aName pv r m out M exts
    extsA mA cap pn pvals c0 hE L LM F R hfull hpn hpvals hgrowReq c1 c2 c3 c4 c5 cap'
    pNamesNew pValsNew exts1 exts2 D alloc shared readable writes hheap hstackW
  have GM := envDefineGrowMemOff g N A SL φf φc st env x v esp aEnv aName pv r m out M exts
    extsA mA cap pn pvals c0 hE L LM F R hfull hpn hpvals hgrowReq c1 c2 c3 c4 c5 cap'
    pNamesNew pValsNew exts1 exts2 D alloc shared readable writes hheap hstackW K
  have henvNat : aEnv.toNat = φf env := F.env_addr
  have hcapLt := D.capLt
  have hcapPos := D.capPos
  have hA2 := D.hA2
  have hA4 := D.hA4
  have hfresh2 := D.fresh2
  have hfresh4 := D.fresh4
  have hexts1 := D.exts1_def
  have hexts2 := D.exts2_def
  have hrecNe : (φf env, 32) ≠ (pn, 8 * cap) := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    omega
  have hrecNeV : (φf env, 32) ≠ (pvals, 24 * cap) := by
    intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    omega
  have hrec1 : (φf env, 32) ∈ exts1 := by
    rw [hexts1]
    exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne hrecNe).mpr hrecMem)
  have hrec2 : (φf env, 32) ∈ exts2 := by
    rw [hexts2]
    exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne hrecNeV).mpr hrec1)
  have hpriv2 : ∀ e ∈ exts2, ∀ i < e.2, ¬ M.privFoot (e.1 + i) :=
    M.privFoot_disjoint c4.σ exts2 D.ainv4
  -- ── ownership and the represented store with the replaced arrays
  let P : Nat → Prop := fun k => mA[k]? = c5.σ.mem[k]?
  have hagP : AgreeP P mA c5.σ.mem := fun k hk => hk
  have hP : ∀ role q nn, role ≠ .frame env → role ≠ .names env → role ≠ .values env →
      Allocated alloc role q nn → ∀ k, ExtentByte (q, nn) k → P k :=
    fun role q nn h1 h2 h3 hq k hk => (GM.other role q nn h1 h2 h3 hq k hk).symm
  have hs : ∀ k, shared k → P k := fun k hk => (GM.sharedOff k hk).symm
  have hSlot : ∀ k, valHeader pv.toNat k → P k := fun k hk => (GM.slot k hk).symm
  let alloc1 : Allocations := alloc.insert (.names env) pNamesNew (8 * cap')
  have hvalsO1 : ArrayOwned alloc1 (.values env) pvals 24 cap :=
    hvalsO.congr (Vsa.Sim.RuntimeOwnership.Allocations.insert_other nofun)
  have ledger1 : Vsa.Sim.RuntimeOwnership.Ledger A exts1 alloc1 := by
    rw [hexts1]
    exact hheap.ledger.replaceArray hnamesO (by omega) hA2 hfresh2
  let alloc2 : Allocations := alloc1.insert (.values env) pValsNew (24 * cap')
  have halloc : ∀ r, r ≠ .names env → r ≠ .values env → alloc2 r = alloc r := by
    intro r h1 h2
    show alloc1.insert (.values env) pValsNew (24 * cap') r = alloc r
    rw [Vsa.Sim.RuntimeOwnership.Allocations.insert_other h2]
    exact Vsa.Sim.RuntimeOwnership.Allocations.insert_other h1
  have hnamesO' : ArrayOwned alloc2 (.names env) pNamesNew 8 cap' := by
    refine Or.inr ⟨hcapPos, ?_⟩
    show alloc1.insert (.values env) pValsNew (24 * cap') (.names env) = some (pNamesNew, 8 * cap')
    rw [Vsa.Sim.RuntimeOwnership.Allocations.insert_other
      (r := Role.names env) (role := Role.values env) nofun]
    exact Vsa.Sim.RuntimeOwnership.Allocations.insert_same
  have hvalsO' : ArrayOwned alloc2 (.values env) pValsNew 24 cap' :=
    Or.inr ⟨hcapPos, Vsa.Sim.RuntimeOwnership.Allocations.insert_same⟩
  let a' : ArrayState := ⟨cap', pNamesNew, pValsNew⟩
  have hkeys' : ∀ i, i < (st.store.frames[env]).vars.length → ∀ k, k < 8 →
      c5.σ.mem[a'.names + 8 * i + k]? = mA[arr.names + 8 * i + k]? := by
    intro i hi k hk
    rw [enames]; exact K.keys i (by omega) k hk
  have hvals' : ∀ i, i < (st.store.frames[env]).vars.length → ∀ k, k < 24 →
      c5.σ.mem[a'.values + 24 * i + k]? = mA[arr.values + 24 * i + k]? := by
    intro i hi k hk
    rw [evals]; exact K.values i (by omega) k hk
  have hcount5 : read32 c5.σ.mem (φf env) = some (st.store.frames[env]).vars.length := by
    rw [K.count]; exact hcountR
  have store2 : Vsa.Sim.RuntimeOwnership.StoreOwned c5.σ.mem φf φc alloc2 shared st.store :=
    hheap.store.replaceArrays henvLt harr halloc hnamesO' hvalsO' K.capRead K.namesRead
      K.valsRead (by show _ ≤ cap'; rw [hfull']; exact Nat.le_of_lt hcapLt) hagP hP hs hkeys' hvals'
  have imm1 : Vsa.Sim.RuntimeOwnership.Immutable alloc1 shared readable writes :=
    hheap.immutable.replaceArray hheap.ledger hheap.reserved (by trivial) hnamesO hA2 hfresh2
  have res1 : Vsa.Sim.RuntimeOwnership.Reserved A exts1 shared := by
    rw [hexts1]
    exact hheap.reserved.replaceArray hheap.ledger hheap.immutable (by trivial) hnamesO
  have ledger2 : Vsa.Sim.RuntimeOwnership.Ledger A exts2 alloc2 := by
    rw [hexts2]
    exact ledger1.replaceArray hvalsO1 (by omega) hA4 hfresh4
  have imm2 : Vsa.Sim.RuntimeOwnership.Immutable alloc2 shared readable writes :=
    imm1.replaceArray ledger1 res1 (by trivial) hvalsO1 hA4 hfresh4
  have res2 : Vsa.Sim.RuntimeOwnership.Reserved A exts2 shared := by
    rw [hexts2]
    exact res1.replaceArray ledger1 imm1 (by trivial) hvalsO1
  have heap2 : HeapOwned A exts2 c5.σ.mem φf φc alloc2 shared readable writes st.store :=
    ⟨ledger2, imm2, res2, store2⟩
  have hstore5 : StoreRepr c5.σ.mem N A φf φc st.store :=
    Vsa.Sim.RuntimeOwnership.storeRepr_replaceArrays F.store hheap.store henvLt hpn hpvals
      hcount5 K.capRead (by omega) K.namesRead K.valsRead K.parent hagP hP hs
      (fun i hi k hk => K.keys i (by omega) k hk) (fun i hi k hk => K.values i (by omega) k hk)
  -- ── the registers, the spill image and the allocator invariant
  have hainv5 : M.AInv c5.σ exts2 := by
    apply LM.alloc.ainv_private exts2 c4.σ c5.σ D.x3_54.symm _ D.ainv4
    intro a hpa
    rw [D.mem5]
    apply Eq.symm
    apply getElem_writeMap8_disjoint
    rw [henvNat]
    rcases Nat.lt_or_ge a (φf env + 16) with h | h
    · left; exact h
    · rcases Nat.lt_or_ge a (φf env + 24) with h' | h'
      · exact absurd hpa (privOff hpriv2 hrec2 ⟨by omega, by omega⟩)
      · right; exact h'
  have hsaved5 : EnvDefineSavedSpillFrame (esp - 64#64) (envDefineSaved g r) c5 := by
    apply R.saved.of_interval_agree
    · intro a ha0 ha1
      rw [R.mem]
      exact GM.offArena a (by rcases hAimg with h | h <;> omega) (by omega)
    · intro a ha0 ha1
      rw [R.mem]
      rw [hsp64] at ha0 ha1
      exact GM.offArena a (by rcases hAstack with h | h <;> omega) (by omega)
  have hmemAgree : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → ¬ (SL.lo ≤ k ∧ k < esp.toNat) →
      c5.σ.mem[k]? = m[k]? := by
    intro k hkA hkS
    rw [← F.mem_agree k hkA hkS]
    exact GM.offArena k hkA (by omega)
  refine ⟨c5, exts2, c5.σ.mem, cap', D.steps, ?_⟩
  refine
    { facts :=
        { ra_align := F.ra_align
          g_sp := F.g_sp
          env_lt := henvLt
          env_addr := F.env_addr
          text := K.text
          store := hstore5
          owned := ⟨alloc2, shared, readable, writes, heap2, hstackW,
            hvalO.transport hagP hSlot hs, hnameO.transport (fun k hk => hagP k (hs k hk))⟩
          word := ⟨valueRepr_agreeP hagP hSlot (hvalO.covered hs) F.word.repr,
            Vsa.Sim.RuntimeOwnership.valueWordsTotal_transport F.word.total hagP hSlot⟩
          cap_read := K.capRead
          names_align := by
            intro pn' hpn'
            have := Option.some.inj (hpn'.symm.trans K.namesRead)
            subst this
            have := D.al2
            omega
          vals_align := by
            intro pv' hpv'
            have := Option.some.inj (hpv'.symm.trans K.valsRead)
            subst this
            have := D.al4
            omega
          miss := F.miss
          mem_agree := hmemAgree
          mem_extends := F.mem_extends.trans K.ext }
      regs :=
        { good := D.good5
          tick := D.tick5
          mem := rfl
          out := D.out5.trans R.out
          minstret := D.minstret5
          sp := by rw [D.abi5 _ (by decide)]; exact R.sp
          gp := by rw [D.abi5 _ (by decide)]; exact R.gp
          s2 := by rw [D.abi5 _ (by decide)]; exact R.s2
          s3 := by rw [D.abi5 _ (by decide)]; exact R.s3
          s4 := by rw [D.abi5 _ (by decide)]; exact R.s4
          s5 := by rw [D.abi5 _ (by decide)]; exact R.s5
          rest := fun R' hR h1 h2 => by rw [D.abi5 R' hR]; exact R.rest R' hR h1 h2
          saved := hsaved5
          stack := R.stack
          ainv := hainv5 }
      pc := D.pc5
      room := by rw [hfull]; exact hcapLt }

#print axioms envDefineGrowCalls
#print axioms envDefineGrowMemCore
#print axioms envDefineGrowMemOff
#print axioms envDefineGrowLane

end Vsa.Sim
