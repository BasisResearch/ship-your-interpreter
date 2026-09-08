import Vsa.Sim.HelperCall

/-!
# `HelperCallEnvDefine` — the `env_define` contract and its adapter

`env_define(env, name, pv)` binds `name` to the value at `pv` in the frame at
`env` (`Store.define`): the update path rewrites an existing slot, the append
path grows the frame's arrays through the allocator.  No whole-function
contract of `env_define` is proved (`EnvDefSpec.lean` records the composed
proof as remaining; `EnvDefCompose` composes the paths over their
straight-line bridges).  This file states the contract the statement arms
consume, ONCE, as a named premise:

* `EnvDefineEntryState`: the state the parametric call parks at
  (`HelperCall.Parked` with `a0 = env`, `a1 = name`, `a2 = pv`) together
  with the memory facts every consumer has (`EnvDefineMem`: the fixed code
  image, the represented store and its stack survival, the name string, the
  represented value, the in-frame buffer, the stack budget);
* `EnvDefineReturnState`: the return at the link PC with the `Store.define`
  result represented, memory unchanged outside the arena and the callee's
  stack window, presence preserved, output unchanged;
* `EnvDefineContract`: the Triple between them, for all ghosts.

**Supplier.** `EnvDefCompose.envDefContract` over the update
(`EnvDefSpec3.env_define_update_post`), append and grow paths; the append and
grow paths need the allocator contracts (`MallocContract`, `ReallocOps`) and
the allocator-private footprint inside the arena (task 2 of the plan).  The
contract is consumed by `hSVarInit` and `hSVarNull` (below), and is the same
seam `hAssign` and `hCallClosure` need.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

/-- The memory-side facts at the `env_define` entry, at the parked memory `m`. -/
structure EnvDefineMem (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat) (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (aEnv aName pv esp : BitVec 64) (m : Mem) : Prop where
  text : FixedTextLoaded m
  store : StoreRepr m N A φf φc st.store
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → m[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  store_bodies : Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget
  env_valid : EnvValid st env
  env_addr : aEnv = BitVec.ofNat 64 (φf env)
  name : CString m aName.toNat x
  value : ValueRepr m N φc pv.toNat v
  stack : StackOK SL esp 1088
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  stack_bytes : StackBytesPresent m SL
  arena_stack : A.hi ≤ SL.lo ∨ esp.toNat + 176 ≤ A.lo
  /-- The value buffer is the caller's in-frame slot. -/
  pv_frame : pv.toNat = esp.toNat + 16
  /-- The caller's staged value slot `[esp+16, esp+40)` lies inside the stack
  region (the caller's own frame geometry). -/
  slot_in_stack : esp.toNat + 40 ≤ SL.hi
  /-- The staged 24-byte slot is fully written (the caller's in-frame copy). -/
  value_words : ValueWordsTotal m pv.toNat
  /-- The arena lies outside the fixed text and rodata image
  (`StaticImageSupport.arena`). -/
  arena_image : A.hi ≤ 0x80000000 ∨ 0x8001acf0 ≤ A.lo

/-- The state at the `env_define` entry reached by the parametric call. -/
structure EnvDefineEntryState (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some 0x80002a5c#64
  a0 : cfg.σ.regs.get? Register.x10 = some aEnv
  a1 : cfg.σ.regs.get? Register.x11 = some aName
  a2 : cfg.σ.regs.get? Register.x12 = some pv
  ra : cfg.σ.regs.get? Register.x1 = some r
  ra_align : r.toNat % 4 = 0
  sp : cfg.σ.regs.get? Register.x2 = some esp
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  mem : cfg.σ.mem = m
  out : cfg.σ.sailOutput = out
  frame : ∀ R, AbiPreserved R = true → cfg.σ.regs.get? R = g R
  facts : EnvDefineMem N A SL φf φc st env x v aEnv aName pv esp m

/-- The state at the `env_define` return: the binding is defined. -/
structure EnvDefineReturnState (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp r : BitVec 64) (m0 : Mem) (out : Array String) (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some r
  ra : cfg.σ.regs.get? Register.x1 = some r
  sp : cfg.σ.regs.get? Register.x2 = some esp
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  a0_defined : ∃ w, cfg.σ.regs.get? Register.x10 = some w
  out : cfg.σ.sailOutput = out
  frame : ∀ R, AbiPreserved R = true → cfg.σ.regs.get? R = g R
  store : StoreRepr cfg.σ.mem N A φf φc (st.store.define env x v)
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → cfg.σ.mem[k]? = m'[k]?) →
    StoreRepr m' N A φf φc (st.store.define env x v)
  mem_frame : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → ¬ (SL.lo ≤ k ∧ k < esp.toNat) →
    cfg.σ.mem[k]? = m0[k]?
  mem_extends : MemExtends m0 cfg.σ.mem

/-- **The `env_define` contract** (named premise; see the module doc for its
supplier).  For every ghost frame and every represented store, name and
value, the callee runs from its entry state to its return state. -/
def EnvDefineContract : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String),
    Triple (EnvDefineEntryState g N A SL φf φc st env x v esp aEnv aName pv r m out)
      (EnvDefineReturnState g N A SL φf φc st env x v esp r m out)

namespace HelperCall

/-- The `env_define` helper returns with the binding defined; only the arena
and the callee's stack window changed. -/
theorem envDefineReturn_of_parked (H : HelperCall) (C : H.Cert)
    (hentry : H.entry = 0x80002a5c#64) (hED : EnvDefineContract)
    {L : GRegs} {lds : List (List (BitVec 8))} {mR : Mem} {out : Array String}
    {gC : (R : Register) → Option (RegisterType R)} {cfg : Config}
    (hP : H.Parked L lds mR out gC cfg)
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {x : String} {v : Value}
    {aEnv aName pv esp s0 s1 s2 s3 : BitVec 64}
    (h10 : lookupG 10 (H.out L lds).regs = some aEnv)
    (h11 : lookupG 11 (H.out L lds).regs = some aName)
    (h12 : lookupG 12 (H.out L lds).regs = some pv)
    (h2 : lookupG 2 (H.out L lds).regs = some esp)
    (h8 : lookupG 8 (H.out L lds).regs = some s0)
    (h9 : lookupG 9 (H.out L lds).regs = some s1)
    (h18 : lookupG 18 (H.out L lds).regs = some s2)
    (h19 : lookupG 19 (H.out L lds).regs = some s3)
    (hM : EnvDefineMem N A SL φf φc st env x v aEnv aName pv esp
      (writeLog mR (H.out L lds).log)) :
    ∃ (cfg' : Config) (a0 : BitVec 64), Steps cfg cfg' ∧
      H.Return gC a0 esp s0 s1 s2 s3 (writeLog mR (H.out L lds).log) cfg'.σ.mem
        (fun k => (A.lo ≤ k ∧ k < A.hi) ∨ (SL.lo ≤ k ∧ k < esp.toNat)) out cfg' ∧
      StoreRepr cfg'.σ.mem N A φf φc (st.store.define env x v) ∧
      (∀ m' : Mem, (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → cfg'.σ.mem[k]? = m'[k]?) →
        StoreRepr m' N A φf φc (st.store.define env x v)) := by
  have hreg : ∀ (n : Nat) (w : BitVec 64), lookupG n (H.out L lds).regs = some w →
      gprGet cfg.σ n = some w := fun n w h => gholds_lookup _ hP.regs h
  obtain ⟨cR, hsR, hR⟩ := hED (fun R => cfg.σ.regs.get? R) N A SL φf φc st env x v
    esp aEnv aName pv H.retPC (writeLog mR (H.out L lds).log) out cfg
    { good := hP.good
      tick := hP.tick
      pc := by rw [hP.pc, hentry]
      a0 := by simpa only [gprGet] using hreg 10 aEnv h10
      a1 := by simpa only [gprGet] using hreg 11 aName h11
      a2 := by simpa only [gprGet] using hreg 12 pv h12
      ra := hP.ra
      ra_align := C.ret_align
      sp := by simpa only [gprGet] using hreg 2 esp h2
      minstret := hP.minstret
      mem := hP.mem
      out := hP.out
      frame := fun _ _ => rfl
      facts := hM }
  obtain ⟨a0, ha0⟩ := hR.a0_defined
  refine ⟨cR, a0, hsR, ⟨?_, ?_, hR.mem_extends⟩, hR.store, hR.store_survives⟩
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

#print axioms envDefineReturn_of_parked

end HelperCall

end Vsa.Sim
