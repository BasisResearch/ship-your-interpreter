import Vsa.Sim.rows.EnvDefineContractUpdate
import Vsa.Sim.RuntimeAllocatorState
import Vsa.Sim.EnvGetReflected.EnvGetFrameScan
import Vsa.Sim.Code.FixedImage_Env_define
import Vsa.Sim.InterpEntry

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Owned helper entry after its actual spills, for a value anywhere above the caller sp. -/
structure EnvDefinePrologueAllocatorPost
    (g : (R : Register) → Option (RegisterType R))
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    (N : NativeAddrs) {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (credits : Nat) (store : Store)
    (target : Addr) (valid : target < store.frames.size) (name : String) (v : Value)
    (after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some 0x80002a90#64
  sp : after.σ.regs.get? Register.x2 = some (esp - 64#64)
  a0 : after.σ.regs.get? Register.x10 = some aEnv
  s4 : after.σ.regs.get? Register.x20 = some aEnv
  s2 : after.σ.regs.get? Register.x18 = some aName
  s5 : after.σ.regs.get? Register.x21 = some pv
  s3 : after.σ.regs.get? Register.x19 = some (BitVec.ofNat 64 store.frames[target].vars.length)
  countSigned : store.frames[target].vars.length < 2^31
  saved : EnvDefineSavedSpillFrame (esp - 64#64) (envDefineSaved g r) after
  allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits store after.σ.mem
  word : ValueWordRepr after.σ.mem N phiC pv.toNat v
  owned : ValueOwned after.σ.mem shared pv.toNat v
  nameOwned : SharedCString after.σ.mem shared aName.toNat name
  support : EvalCallSupport after.σ.mem SL A esp
  agreement : AgreeP shared m after.σ.mem
  outside : ∀ k, (k < esp.toNat - 64 ∨ esp.toNat ≤ k) → m[k]? = after.σ.mem[k]?
  presence : MemExtends m after.σ.mem
  frame : ∀ R, PrologueKeep R = true → after.σ.regs.get? R = g R
  gp : after.σ.regs.get? Register.x3 = some gpv
  output : after.σ.sailOutput = out

/-- Execute the existing prologue while retaining the caller's owned argument and store. -/
theorem envDefinePrologueAllocator_run
    {g : (R : Register) → Option (RegisterType R)}
    {esp aEnv aName pv r : BitVec 64} {m : Mem} {out : Array String}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {store : Store}
    {target : Addr} {name : String} {v : Value} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (entry : EnvDefineProloguePre g esp aEnv aName pv r m out before)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared credits store m)
    (valid : target < store.frames.size) (envAddr : aEnv.toNat = phiF target)
    (word : ValueWordRepr m N phiC pv.toNat v)
    (owned : ValueOwned m shared pv.toNat v)
    (nameOwned : SharedCString m shared aName.toNat name)
    (slotAbove : esp.toNat ≤ pv.toNat)
    (stack : StackOK SL esp 1088)
    (stackRam : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000)
    (stackWin : tohostAddr + 16 ≤ SL.lo)
    (support : EvalCallSupport m SL A esp)
    (present : EnvDefineSavedPresent g)
    (gp : g Register.x3 = some gpv) (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧
      EnvDefinePrologueAllocatorPost g esp aEnv aName pv r m out N M
        phiF phiC alloc exts shared credits store target valid name v after := by
  obtain ⟨v8, hg8⟩ := Option.isSome_iff_exists.mp present.s0
  obtain ⟨v9, hg9⟩ := Option.isSome_iff_exists.mp present.s1
  obtain ⟨v18, hg18⟩ := Option.isSome_iff_exists.mp present.s2
  obtain ⟨v19, hg19⟩ := Option.isSome_iff_exists.mp present.s3
  obtain ⟨v20, hg20⟩ := Option.isSome_iff_exists.mp present.s4
  obtain ⟨v21, hg21⟩ := Option.isSome_iff_exists.mp present.s5
  obtain ⟨v22, hg22⟩ := Option.isSome_iff_exists.mp present.s6
  obtain ⟨stackLo, stackHi, stackAlign⟩ := stack
  obtain ⟨ramLo, ramHi⟩ := stackRam
  have h64 : 64 ≤ esp.toNat := by omega
  have sp64 := sp_sub64_toNat esp h64
  have frame := allocator.heap.store.frames target valid
  obtain ⟨arrays, arrayFacts⟩ := frame.arrays
  have capSigned := frame.capSigned allocator.heap.ledger arrayFacts.capRead L.arena_ram.2
  have countSigned : store.frames[target].vars.length < 2^31 := by
    have := arrayFacts.bound; omega
  have envArena := (allocator.repr.frames_arena target valid).1
  obtain ⟨envLo, envHi⟩ := envArena
  have arenaRam := L.arena_ram
  have arenaHtif := L.arena_htif
  have arenaStack := L.arena_stack
  obtain ⟨after, steps, post⟩ := envDefinePrologueFramed g esp aEnv aName pv r
    v8 v9 v18 v19 v20 v21 v22 store.frames[target].vars.length m out SL
    hg8 hg9 hg18 hg19 hg20 hg21 hg22 support.image.text.Env_defineLoaded
    (by rw [envAddr]; exact EnvGetReflected.frame_count_read (allocator.repr.frames target valid))
    countSigned (by omega) (by omega) (by right; omega)
    (by rcases arenaStack with left | right
        · left; omega
        · right; omega)
    ⟨stackLo, stackHi, stackAlign⟩ ⟨ramLo, ramHi⟩ stackWin before entry
  have outside : ∀ k, (k < esp.toNat - 64 ∨ esp.toNat ≤ k) → m[k]? = after.σ.mem[k]? := by
    intro k hk
    rw [post.mem]
    exact (envDefineSpillMem_outside m _ k r v8 v9 v18 v19 v20 v21 v22 (by omega)).symm
  have stackFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → m[k]? = after.σ.mem[k]? := by
    intro k hk; exact outside k (by omega)
  have data := allocator.runtime L
  have agreement : AgreeP shared m after.σ.mem :=
    fun k hk => stackFrame k (data.shared_off_stack hk)
  have header : ∀ k, valHeader pv.toNat k → k < esp.toNat - 64 ∨ esp.toNat ≤ k := by
    intro k hk; unfold valHeader at hk; right; omega
  have sharedOff : ∀ k, shared k → k < esp.toNat - 64 ∨ esp.toNat ≤ k := by
    intro k hk
    have := data.shared_off_stack hk
    omega
  have support' : EvalCallSupport after.σ.mem SL A esp :=
    support.transport_stack (fun k hk => (stackFrame k hk).symm)
  have saved : EnvDefineSavedSpillFrame (esp - 64#64) (envDefineSaved g r) after :=
    envDefineSavedSpills_of_mem r v8 v9 v18 v19 v20 v21 v22 (envDefineSaved_x1 g r)
      ((envDefineSaved_ne g r (by decide)).trans hg8)
      ((envDefineSaved_ne g r (by decide)).trans hg9)
      ((envDefineSaved_ne g r (by decide)).trans hg18)
      ((envDefineSaved_ne g r (by decide)).trans hg19)
      ((envDefineSaved_ne g r (by decide)).trans hg20)
      ((envDefineSaved_ne g r (by decide)).trans hg21)
      ((envDefineSaved_ne g r (by decide)).trans hg22)
      post.mem support'.image.text.Env_defineLoaded (by omega) (by omega) (by omega) (by omega)
      (envDefineEpilogueTermFacts (esp - 64#64) r v8 v9 v18 v19 v20 v21 v22 retAlign)
  have presence : MemExtends m after.σ.mem := by
    rw [post.mem]
    have writes := memExtends_writeLog m (evalBlocks envDefinePrologueSeg
      (SegEvalState.init (envDefinePrologueL esp v19 aEnv v18 v20 v21 r v8 v9 v22 aName pv) [[]])).log
    rw [envDefinePrologueMem m esp v19 aEnv v18 v20 v21 r v8 v9 v22 aName pv [] h64] at writes
    exact writes
  refine ⟨after, steps,
    { good := post.good, tick := post.tick, pc := post.pc, sp := post.sp
      a0 := post.a0, s4 := post.s4, s2 := post.s2, s5 := post.s5, s3 := post.s3
      countSigned := countSigned, saved := saved, allocator := allocator.after_stack L stackFrame
      word := ⟨valueRepr_agreeP outside header (owned.covered sharedOff) word.repr,
        valueWordsTotal_transport word.words outside header⟩
      owned := owned.transport outside header sharedOff
      nameOwned := nameOwned.transport agreement
      support := support', agreement := agreement, outside := outside, presence := presence
      frame := post.keep, gp := (post.keep .x3 (by decide)).trans gp, output := post.out }⟩

#print axioms envDefinePrologueAllocator_run

end Vsa.Sim
