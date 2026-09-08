import Vsa.Sim.HelperCall

/-!
# `HelperCallEnvNew` — the `env_new` contract and its adapter

`env_new(parent)` allocates a fresh 32-byte frame whose parent is the given
environment and returns its address (`Store.allocFrame`).  `env_new_spec`
(`EnvNewSpec.lean`) proves the machine path over a `MallocContract`; what the
statement arms need beyond it is the store representation of the pushed
store under an extended frame map, which requires the fresh address to be
disjoint from every represented frame (the allocation ledger of task 2).
This file states the contract the block and for arms consume, ONCE, as a
named premise:

* `EnvNewEntryState`: the parametric call parked at `env_new` with `a0` the
  parent frame pointer, plus the memory facts every consumer has
  (`EnvNewMem`);
* `EnvNewReturnState`: the return at the link PC with the fresh frame
  pointer in `a0`, the extended map (`EnvNewFresh`), memory unchanged outside
  the arena and the callee's stack window, presence preserved;
* `EnvNewContract`: the Triple between them, for all ghosts.

**Supplier.** `env_new_spec` with `MallocContract`, `storeRepr_allocFrame`
(`rows/CallClosureEnvNewMarshal.lean`) for the pushed store, the freshness of
the returned block against the represented frames (the ownership ledger
relating `StoreRepr` images to the allocator's extents), and the
allocator-private footprint inside the arena.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

/-- The memory-side facts at the `env_new` entry, at the parked memory `m`. -/
structure EnvNewMem (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat) (st : Vsa.While.St) (env : Addr)
    (aEnv esp : BitVec 64) (m : Mem) : Prop where
  text : FixedTextLoaded m
  store : StoreRepr m N A φf φc st.store
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → m[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  env_valid : EnvValid st env
  env_addr : aEnv = BitVec.ofNat 64 (φf env)
  stack : StackOK SL esp 1088
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  stack_bytes : StackBytesPresent m SL
  arena_stack : A.hi ≤ SL.lo ∨ esp.toNat + 176 ≤ A.lo

/-- The state at the `env_new` entry reached by the parametric call. -/
structure EnvNewEntryState (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (esp aEnv r : BitVec 64) (m : Mem)
    (out : Array String) (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some 0x800029fc#64
  a0 : cfg.σ.regs.get? Register.x10 = some aEnv
  ra : cfg.σ.regs.get? Register.x1 = some r
  ra_align : r.toNat % 4 = 0
  sp : cfg.σ.regs.get? Register.x2 = some esp
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  mem : cfg.σ.mem = m
  out : cfg.σ.sailOutput = out
  frame : ∀ R, AbiPreserved R = true → cfg.σ.regs.get? R = g R
  facts : EnvNewMem N A SL φf φc st env aEnv esp m

/-- The fresh frame: its address, the extended frame map, and the pushed
store represented under it. -/
structure EnvNewFresh (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat) (st : Vsa.While.St) (env : Addr)
    (p : BitVec 64) (φf' : Addr → Nat) (m : Mem) : Prop where
  map_extends : PhiExtends φf φf' st.store.frames.size
  addr : φf' st.store.frames.size = p.toNat
  nonzero : p ≠ 0#64
  arena : A.contains p.toNat 32
  align : p.toNat % 8 = 0
  store : StoreRepr m N A φf' φc (st.store.allocFrame (some env)).1
  survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → m[k]? = m'[k]?) →
    StoreRepr m' N A φf' φc (st.store.allocFrame (some env)).1

/-- The state at the `env_new` return: the fresh frame is allocated. -/
structure EnvNewReturnState (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (esp r : BitVec 64) (m0 : Mem)
    (out : Array String) (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some r
  ra : cfg.σ.regs.get? Register.x1 = some r
  sp : cfg.σ.regs.get? Register.x2 = some esp
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  out : cfg.σ.sailOutput = out
  frame : ∀ R, AbiPreserved R = true → cfg.σ.regs.get? R = g R
  fresh : ∃ (p : BitVec 64) (φf' : Addr → Nat),
    cfg.σ.regs.get? Register.x10 = some p ∧
    EnvNewFresh N A SL φf φc st env p φf' cfg.σ.mem
  mem_frame : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → ¬ (SL.lo ≤ k ∧ k < esp.toNat) →
    cfg.σ.mem[k]? = m0[k]?
  mem_extends : MemExtends m0 cfg.σ.mem

/-- **The `env_new` contract** (named premise; see the module doc for its
supplier). -/
def EnvNewContract : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (esp aEnv r : BitVec 64) (m : Mem)
    (out : Array String),
    Triple (EnvNewEntryState g N A SL φf φc st env esp aEnv r m out)
      (EnvNewReturnState g N A SL φf φc st env esp r m out)

namespace HelperCall

/-- The `env_new` helper returns with the fresh frame in `a0`; only the arena
and the callee's stack window changed. -/
theorem envNewReturn_of_parked (H : HelperCall) (C : H.Cert)
    (hentry : H.entry = 0x800029fc#64) (hEN : EnvNewContract)
    {L : GRegs} {lds : List (List (BitVec 8))} {mR : Mem} {out : Array String}
    {gC : (R : Register) → Option (RegisterType R)} {cfg : Config}
    (hP : H.Parked L lds mR out gC cfg)
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {env : Addr}
    {aEnv esp s0 s1 s2 s3 : BitVec 64}
    (h10 : lookupG 10 (H.out L lds).regs = some aEnv)
    (h2 : lookupG 2 (H.out L lds).regs = some esp)
    (h8 : lookupG 8 (H.out L lds).regs = some s0)
    (h9 : lookupG 9 (H.out L lds).regs = some s1)
    (h18 : lookupG 18 (H.out L lds).regs = some s2)
    (h19 : lookupG 19 (H.out L lds).regs = some s3)
    (hM : EnvNewMem N A SL φf φc st env aEnv esp (writeLog mR (H.out L lds).log)) :
    ∃ (cfg' : Config) (p : BitVec 64) (φf' : Addr → Nat), Steps cfg cfg' ∧
      H.Return gC p esp s0 s1 s2 s3 (writeLog mR (H.out L lds).log) cfg'.σ.mem
        (fun k => (A.lo ≤ k ∧ k < A.hi) ∨ (SL.lo ≤ k ∧ k < esp.toNat)) out cfg' ∧
      EnvNewFresh N A SL φf φc st env p φf' cfg'.σ.mem := by
  have hreg : ∀ (n : Nat) (w : BitVec 64), lookupG n (H.out L lds).regs = some w →
      gprGet cfg.σ n = some w := fun n w h => gholds_lookup _ hP.regs h
  obtain ⟨cR, hsR, hR⟩ := hEN (fun R => cfg.σ.regs.get? R) N A SL φf φc st env esp aEnv
    H.retPC (writeLog mR (H.out L lds).log) out cfg
    { good := hP.good
      tick := hP.tick
      pc := by rw [hP.pc, hentry]
      a0 := by simpa only [gprGet] using hreg 10 aEnv h10
      ra := hP.ra
      ra_align := C.ret_align
      sp := by simpa only [gprGet] using hreg 2 esp h2
      minstret := hP.minstret
      mem := hP.mem
      out := hP.out
      frame := fun _ _ => rfl
      facts := hM }
  obtain ⟨p, φf', ha0, hfresh⟩ := hR.fresh
  refine ⟨cR, p, φf', hsR, ⟨?_, ?_, hR.mem_extends⟩, hfresh⟩
  · exact
      { good := hR.good
        tick := hR.tick
        pc := hR.pc
        a0 := ha0
        ra := hR.ra
        minstret := hR.minstret
        mem := rfl
        out := hR.out
        sp := hR.sp
        s0 := (hR.frame Register.x8 (by decide)).trans (by simpa only [gprGet] using hreg 8 s0 h8)
        s1 := (hR.frame Register.x9 (by decide)).trans (by simpa only [gprGet] using hreg 9 s1 h9)
        s2 := (hR.frame Register.x18 (by decide)).trans
          (by simpa only [gprGet] using hreg 18 s2 h18)
        s3 := (hR.frame Register.x19 (by decide)).trans
          (by simpa only [gprGet] using hreg 19 s3 h19)
        frame := fun R hR' => (hR.frame R hR').trans (hP.frame R hR') }
  · intro k hk
    exact hR.mem_frame k (fun h => hk (Or.inl h)) (fun h => hk (Or.inr h))

#print axioms envNewReturn_of_parked

end HelperCall

end Vsa.Sim
