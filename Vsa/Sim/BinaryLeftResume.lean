import Vsa.Sim.MemPresence
import Vsa.Sim.BinaryArmReady
import Vsa.Sim.BinaryRightStage
import Vsa.Sim.EvalGroundOwned
import Vsa.Sim.SubEvalReturnFacts
import Vsa.Sim.AllocatorResult
import Vsa.While.StoreBodiesBoundPreservation

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine Vsa.Logic

namespace Vsa.Sim
open RuntimeOwnership

/-- Construct the right call from the actual left return and its selected maps. -/
theorem BinaryArmReady.stage_right
    {g gpre : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC middleF middleC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {entryShared shared : Nat → Prop}
    {credits : Nat} {st middle : Vsa.While.St} {d env : Nat}
    {op : BinOp} {el er : Expr} {vl : Value}
    {sp ret dst node interp left right envReg v8 v9 v18 v19 : BitVec 64}
    {out : Array String} {m0 : Mem} {before called after : Config}
    {FirstOwned : (Addr → Nat) → (Addr → Nat) → Mem → Prop}
    (h : BinaryArmReady g gpre N A SL phiF phiC st d env op el er
      sp ret dst node interp left right envReg v8 v9 v18 v19 out m0 before)
    (staged : BinaryLeftStaged gpre N A SL phiF phiC st d env el
      sp ret dst node interp left envReg v8 v9 v18 v19 out before called)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (semantic : EvalE st d env el middle vl)
    (returned : SubEvalReturn gpre N A SL phiF phiC st.store.frames.size
      st.store.closures.size middle vl sp ret dst
      ((sp - 1088#64) + sign_extend (m := 64) (0x078#12))
      0x800034fc#64 v8 v9 v18 called.σ.mem after)
    (first : ReturnRepr N A phiF phiC middleF middleC st.store.frames.size
      st.store.closures.size middle.store
      [(((sp - 1088#64) + 120#64).toNat, vl)] FirstOwned
      (fun k => SL.lo ≤ k ∧ k < SL.hi) after.σ.mem)
    (data : AllocatorResultAt M N entryShared credits middle.store
      [(((sp - 1088#64) + 120#64).toNat, vl)] before.σ.mem
      middleF middleC alloc exts shared after.σ.mem)
    (ast : ExprReprWithin before.σ.mem entryShared node.toNat (.binary op el er)) :
    LandedN 7 after (BinaryRightStaged gpre N A SL middleF middleC middle d env er
      sp ret dst node interp right v8 v9 v18 after) := by
  have p := ArmEntryK.destruct g N A SL phiF phiC st 0x800034e8#64 UnaryArmCallee
    (.binary op el er) sp ret dst node interp v8 v9 v18 out m0 before.σ.mem before h.arm
  have q := SubEvalReturn.destruct gpre N A SL phiF phiC st.store.frames.size
    st.store.closures.size middle vl sp ret dst
    ((sp - 1088#64) + sign_extend (m := 64) (0x078#12))
    0x800034fc#64 v8 v9 v18 called.σ.mem after returned
  have room := h.geometry.sproom
  have high := h.geometry.spSLhi
  have ram := h.geometry.SLhiRam
  have lowered : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]
    have := sp.isLt
    omega
  have child : ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat =
      sp.toNat - 968 := spill_addr sp (0x078#12) 968 (by decide) (by omega) (by omega)
  obtain ⟨bs, segment⟩ := staged.segment
  have prefixPresence : MemExtends before.σ.mem called.σ.mem := by
    rw [segment.mem]
    exact memExtends_writeLog _ _
  have agree (k : Nat) (hs : ¬ (SL.lo ≤ k ∧ k < sp.toNat))
      (ha : ¬ (A.lo ≤ k ∧ k < A.hi)) : before.σ.mem[k]? = after.σ.mem[k]? := by
    have hp := segment.outside k (by unfold BinaryPrefix.firstFoot; rw [lowered]; omega)
    rcases q.memFrame k (by omega) ha with slot | same
    · rw [child] at slot
      exact False.elim (hs (by omega))
    · exact hp.trans same.symm
  have support := h.ground.eval_call.transport_frame (sp' := sp) (cut := sp.toNat)
    (ret := ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat)
    high (by rw [child]; omega) (fun k hs ha => Or.inr (agree k hs ha).symm)
  have parentGround : EvalGround after.σ.mem SL A sp dst node.toNat (.binary op el er) :=
    h.ground.transport_owned ast data.agreement support (prefixPresence.trans q.presence)
  have rightRead : read64 after.σ.mem (node.toNat + 24) = some right.toNat := by
    have eq := (ast.fieldCovers (.word64 24) (by simp [exprReadFields])).read64_eq data.agreement
    exact eq.symm.trans h.rightRead
  have ground := parentGround.child_node (fun lo hi within =>
    exprIn_binary_right within right.toNat rightRead)
  have rightAst := ast.child (.binaryRight op el er) h.rightRead
  have ownedAst := (rightAst.transport data.agreement).mono data.includes
  have astSurv : ∀ m : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → after.σ.mem[k]? = m[k]?) →
      ExprRepr m right.toNat er := by
    intro m hm
    exact (ownedAst.transport (fun k hk => hm k (by
      have off := (data.allocator.runtime L).shared_off_stack hk
      omega))).erase
  have saved : BinaryPrefix.FirstSaved called.σ.mem (sp - 1088#64) v19 envReg := by
    rw [segment.mem, BinaryPrefix.first_log _ _ _ _ _ (by rw [lowered]; omega)]
    exact BinaryPrefix.first_saved _ _ _ _
  have savedLeft := saved.after_left (returned.toExit (by decide) lowered) staged.window
    (by rw [lowered]; omega) L.arena_stack
  have envRead : read64 after.σ.mem (sp.toNat - 1088) =
      some (BitVec.ofNat 64 (middleF env)).toNat := by
    have eq : phiF env = middleF env := (first.frames env h.recursion.env_valid).symm
    rw [← lowered]
    rw [← eq, ← h.recursion.env_addr]
    exact savedLeft.environment
  obtain ⟨w20, hw20⟩ := h.recursion.x20_defined
  obtain ⟨w21, hw21⟩ := h.recursion.x21_defined
  obtain ⟨_, vi, _, slot, pins, _⟩ := parentGround.eval_call.pins after.σ.mem (fun _ _ => rfl)
  exact binaryR_midStaged_of_nodeWindow gpre N A SL middleF middleC middle d env er
    sp ret dst node interp right v8 v9 v18 after q.good q.tick q.pc q.sret q.spReg
    q.minstret q.out q.frame ((q.frame .x8 (by decide)).trans h.ghostNode)
    ((q.frame .x18 (by decide)).trans h.ghostInterp) h.ghostNode h.ghostInterp
    (h.recursion.env_valid.mono (evalE_store_mono semantic).1) envRead
    ⟨v19, w20, w21, h.ghost19, hw20, hw21⟩ q.code rightRead first.storeRepr
    (fun m hm => first.survives m (fun k hk => hm k hk (by
      have := h.geometry.sret_inSL; omega)))
    astSurv vi slot pins q.slotRa q.slotS0 q.slotS1 q.slotS2
    h.geometry.node_hi p.exprLo p.exprWin
    h.geometry.rop_ram h.geometry.rop_win h.geometry.rop_stk h.geometry.rop_stkfull
    p.spRoom room high h.geometry.sp16 p.spHi p.stackLo ram p.stackWin
    h.geometry.codeStk h.geometry.viStk h.geometry.tableStk
    h.geometry.arenaStk h.geometry.arenaCode h.rightBudget h.rightBodies
    (StoreBodiesBound.afterEvalE semantic h.leftBodies h.storeBodies) ground

#print axioms BinaryArmReady.stage_right

end Vsa.Sim
