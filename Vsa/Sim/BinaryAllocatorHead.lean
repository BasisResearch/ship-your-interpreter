import Vsa.Sim.BinaryLeftAllocator
import Vsa.Sim.BinaryLeftResume
import Vsa.Sim.BinaryRightBind
import Vsa.Sim.rows.StoreWF

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine Vsa.Logic

namespace Vsa.Sim
open RuntimeOwnership

theorem BinaryPrefix.right_frame {m0 mc m : Mem} {SL : StackLayout} {A : Arena}
    {cut : Nat} (room : SL.lo ≤ cut)
    (segment : ∀ k, ¬ (cut ≤ k ∧ k < cut + 8) → m0[k]? = mc[k]?)
    (child : ∀ k, ¬ (SL.lo ≤ k ∧ k < cut) → ¬ (A.lo ≤ k ∧ k < A.hi) →
      (cut + 144 ≤ k ∧ k < cut + 144 + 24) ∨ m[k]? = mc[k]?) :
    ∀ k, ¬ (SL.lo ≤ k ∧ k < cut + 8) → ¬ (A.lo ≤ k ∧ k < A.hi) →
      ¬ (cut + 144 ≤ k ∧ k < cut + 144 + 24) → m0[k]? = m[k]? := by
  intro k hs ha hr
  have same := segment k (by omega)
  rcases child k (by omega) ha with slot | eq
  · exact False.elim (hr slot)
  · exact same.trans eq.symm

#print axioms BinaryPrefix.right_frame

/-- The binary dispatch state retains machine facts and both owned operand values. -/
structure BinaryAllocatorHeadReturn
    (gpre : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (nf nc : Nat) (shared : Nat → Prop) (reserve : Nat)
    (middle final : Vsa.While.St) (vl vr : Value)
    (sp ret dst v8 v9 v18 : BitVec 64) (m0 : Mem) (after : Config) : Prop where
  ordinary : TwoSubReturn gpre N A SL phiF phiC nf nc middle final vl vr
    sp ret dst v8 v9 v18 m0 after
  owned : BinaryAllocatorReturnData N M phiF phiC nf nc shared reserve
    final vl vr (sp - 1088#64) m0 after
  machine : BinaryReturnData SL sp dst after

/-- Execute both owned children at the same native addresses. -/
theorem BinaryArmReady.run_allocator_at
    {g gpre : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {st middle final : Vsa.While.St} {d env : Nat} {op : BinOp} {el er : Expr}
    {vl vr : Value} {costL costR maxRequest reserve : Nat}
    {sp ret dst node interp left right envReg v8 v9 v18 v19 : BitVec 64}
    {out : Array String} {m0 : Mem} {before : Config}
    (h : BinaryArmReady g gpre N A SL phiF phiC st d env op el er
      sp ret dst node interp left right envReg v8 v9 v18 v19 out m0 before)
    (L : AllocLedger A SL gpv headroom maxReq M) (request : maxRequest ≤ maxReq)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared
      (costL + (costR + reserve)) st.store before.σ.mem)
    (ast : ExprReprWithin before.σ.mem shared node.toNat (.binary op el er))
    (gp : before.σ.regs.get? .x3 = some gpv)
    (leftSem : EvalE st d env el middle vl)
    (bounded : StoreClosuresBounded st.store)
    (leftIH : EvalAllocatorAt N st d env el middle vl costL maxRequest)
    (rightIH : EvalAllocatorAt N middle d env er final vr costR maxRequest) :
    ∃ after, Steps before after ∧ BinaryAllocatorHeadReturn gpre N M phiF phiC
      st.store.frames.size st.store.closures.size shared reserve middle final vl vr
      sp ret dst v8 v9 v18 m0 after := by
  have p := ArmEntryK.destruct g N A SL phiF phiC st 0x800034e8#64 UnaryArmCallee
    (.binary op el er) sp ret dst node interp v8 v9 v18 out m0 before.σ.mem before h.arm
  have room := h.geometry.sproom
  have high := h.geometry.spSLhi
  have ram := h.geometry.SLhiRam
  have lowered : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]
    have := sp.isLt
    omega
  have leftAddr : ((sp - 1088#64) + 120#64).toNat = sp.toNat - 968 :=
    spill_addr sp (0x078#12) 968 (by decide) (by omega) (by omega)
  have rightAddr : ((sp - 1088#64) + 144#64).toNat = sp.toNat - 944 :=
    spill_addr sp (0x090#12) 944 (by decide) (by omega) (by omega)
  have rightAst := ast.child (.binaryRight op el er) h.rightRead
  obtain ⟨_, calledL, _, _, stagedL⟩ := h.stage_left
  obtain ⟨afterL, stepsL, returnedL⟩ := stagedL.call_allocator_at L request allocator
    (ast.child (.binaryLeft op el er) h.leftRead) gp leftIH
  obtain ⟨middleF, middleC, first⟩ := returnedL.extra.repr.selected
  obtain ⟨middleAlloc, middleExts, middleShared, data⟩ := first.owned.selected
  obtain ⟨_, calledR, _, _, stagedR⟩ := h.stage_right stagedL L leftSem
    returnedL.result first data ast
  obtain ⟨afterR, stepsR, returnedR⟩ := stagedR.bind_allocator_at L request data first
    ((rightAst.transport data.agreement).mono data.includes) returnedL.extra.gp rightIH
    lowered (by rw [lowered]; omega) (evalE_store_mono leftSem).1
    (evalE_store_mono leftSem).2 (storeClosuresBounded_mutual.onEvalE leftSem bounded).2
  have qL := SubEvalReturn.destruct gpre N A SL phiF phiC st.store.frames.size
    st.store.closures.size middle vl sp ret dst ((sp - 1088#64) + 120#64)
    0x800034fc#64 v8 v9 v18 calledL.σ.mem afterL returnedL.result
  have qR := SubEvalReturn.destruct (fun R => calledR.σ.regs.get? R) N A SL middleF middleC
    middle.store.frames.size middle.store.closures.size final vr sp ret dst
    ((sp - 1088#64) + 144#64) 0x8000351c#64 v8 v9 v18 calledR.σ.mem afterR returnedR.result
  obtain ⟨bs, segmentL⟩ := stagedL.segment
  obtain ⟨br, segmentR⟩ := stagedR.segment
  have presenceL : MemExtends before.σ.mem calledL.σ.mem := by
    rw [segmentL.mem]; exact memExtends_writeLog _ _
  have presenceR : MemExtends afterL.σ.mem calledR.σ.mem := by
    rw [segmentR.mem]; exact memExtends_writeLog _ _
  have presence : MemExtends before.σ.mem afterR.σ.mem :=
    presenceL.trans (qL.presence.trans (presenceR.trans qR.presence))
  have rightOffset : ((sp - 1088#64) + 144#64).toNat = (sp - 1088#64).toNat + 144 := by
    rw [BitVec.toNat_add]
    change ((sp - 1088#64).toNat + 144) % 2^64 = (sp - 1088#64).toNat + 144
    exact Nat.mod_eq_of_lt (by rw [lowered]; omega)
  have segmentFrame := segmentR.outside
  simp only [BinaryPrefix.secondFoot] at segmentFrame
  have childFrame := qR.memFrame
  rw [← lowered, rightOffset] at childFrame
  have rightFrame := BinaryPrefix.right_frame stagedR.window.lo segmentFrame childFrame
  have rightSlot : (sp - 1088#64).toNat + 144 = sp.toNat - 944 := rightOffset.symm.trans rightAddr
  rw [rightSlot, lowered] at rightFrame
  have frame : ∀ R, AbiPreservedNoise R → (Register.x19 == R) = false →
      afterR.σ.regs.get? R = gpre R := by
    have keep : ∀ R, AbiPreservedNoise R → (Register.x19 == R) = false →
        BinaryPrefix.secondKeep R = true := by intro R; cases R <;> decide
    intro R hR h19
    exact (qR.frame R hR).trans ((segmentR.reg_frame R (keep R hR h19)).trans (qL.frame R hR))
  have saved : BinaryPrefix.FirstSaved calledL.σ.mem (sp - 1088#64) v19 envReg := by
    rw [segmentL.mem, BinaryPrefix.first_log _ _ _ _ _ (by rw [lowered]; omega)]
    exact BinaryPrefix.first_saved _ _ _ _
  have savedLeft := saved.after_left (returnedL.result.toExit (by decide) lowered)
    stagedL.window (by rw [lowered]; omega) L.arena_stack
  have savedFinal : read64 afterR.σ.mem (sp.toNat - 40) = some v19.toNat := by
    have eq := read64_agreeP (P := fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat - 32)
      (fun k hk => rightFrame k (by omega) (by
        have := L.arena_stack; omega) (by omega))
      (a := sp.toNat - 40) (fun j hj => by constructor <;> omega)
    have hs := savedLeft.saved
    rw [lowered, show sp.toNat - 1088 + 1048 = sp.toNat - 40 from by omega] at hs
    exact eq.symm.trans hs
  obtain ⟨resultF, resultC, both⟩ := returnedR.extra.selected
  have leftValue := both.values _ _ (List.mem_cons_self ..)
  rw [leftAddr] at leftValue
  obtain ⟨valueC, valueExtends, rightValue⟩ := qR.value
  obtain ⟨storeF, storeC, storeFrames, storeClosures, store, survives⟩ := qR.store
  have ordinary : TwoSubReturn gpre N A SL phiF phiC st.store.frames.size
      st.store.closures.size middle final vl vr sp ret dst v8 v9 v18 m0 afterR := by
    refine ⟨qR.good, qR.tick, qR.pc, qR.ra, qR.sret, qR.spReg, qR.minstret, qR.out,
      frame, ⟨v19, h.ghost19, savedFinal⟩,
      ⟨middleF, middleC, first.frames, first.closures,
        ⟨valueC, valueExtends, ?_⟩, ⟨resultC, leftValue⟩,
        ⟨storeF, storeC, storeFrames, storeClosures, store, survives⟩⟩,
      qR.code, qR.slotRa, qR.slotS0, qR.slotS1, qR.slotS2,
      h.presence.trans presence, ?_⟩
    · rw [← rightAddr]; exact rightValue.repr
    · intro k hs ha
      have firstSegmentFrame := segmentL.outside k (by unfold BinaryPrefix.firstFoot; rw [lowered]; omega)
      have child : calledL.σ.mem[k]? = afterL.σ.mem[k]? := by
        rcases qL.memFrame k (by omega) ha with slot | eq
        · rw [leftAddr] at slot; exact False.elim (hs (by omega))
        · exact eq.symm
      have right := rightFrame k (by omega) ha (by omega)
      exact right.symm.trans (child.symm.trans (firstSegmentFrame.symm.trans (p.memFrame k hs)))
  have initialAgreement : AgreeP shared m0 before.σ.mem := by
    intro k hk
    have off := (allocator.runtime L).shared_off_stack hk
    exact (p.memFrame k (by omega)).symm
  have owned : BinaryAllocatorReturnData N M phiF phiC st.store.frames.size
      st.store.closures.size shared reserve final vl vr (sp - 1088#64) m0 afterR :=
    { selected := ⟨resultF, resultC,
        both.withOwnership (both.owned.rebase (fun _ hk => hk) initialAgreement)⟩
      gp := returnedR.extra.gp }
  have stackBytes := h.ground.stack_bytes_extend presence
  have payloadEq : bytesT8 afterL.σ.mem (sp.toNat - 960) =
      bytesT8 afterR.σ.mem (sp.toNat - 960) :=
    bytesT8_agree _ (fun j hj => rightFrame _ (by omega)
      (by have := L.arena_stack; omega) (by omega))
  have kindEq : bytesT4 afterL.σ.mem (sp.toNat - 968) =
      bytesT4 afterR.σ.mem (sp.toNat - 968) :=
    bytesT4_agree _ (fun j hj => rightFrame _ (by omega)
      (by have := L.arena_stack; omega) (by omega))
  have payloadRead : BinaryPrefix.leftPayload afterL.σ.mem (sp - 1088#64) =
      bytesT8 afterL.σ.mem (sp.toNat - 960) := by
    simp only [BinaryPrefix.leftPayload, EvalChildArm.wordLds8, bytesVal,
      List.getD_cons_zero, List.getD_cons_succ, sext_full]
    rw [lowered, show sp.toNat - 1088 + 128 = sp.toNat - 960 from by omega]
  have kindRead : BinaryPrefix.leftKind afterL.σ.mem (sp - 1088#64) =
      sign_extend (m := 64) (bytesT4 afterL.σ.mem (sp.toNat - 968)) := by
    simp only [BinaryPrefix.leftKind, EvalChildArm.wordLds8, bytesVal,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [lowered, show sp.toNat - 1088 + 120 = sp.toNat - 968 from by omega]
  obtain ⟨_r12, _r13, _r16, _r10, _r11, payloadReg, _r2, _r8, _r18, _⟩ := segmentR.selected_regs
  have payloadRegister : afterR.σ.regs.get? Register.x19 =
      some (bytesT8 afterR.σ.mem (sp.toNat - 960)) := by
    have hp := (qR.frame .x19 (by decide)).trans payloadReg
    rw [payloadRead, payloadEq] at hp
    exact hp
  have kindSaved : read64 calledR.σ.mem (sp.toNat - 1088) =
      some (sign_extend (m := 64) (bytesT4 afterL.σ.mem (sp.toNat - 968))).toNat := by
    rw [segmentR.mem]
    simp only [BinaryPrefix.secondLoads]
    rw [BinaryPrefix.second_log]
    change read64 (writeMap8 afterL.σ.mem (sp - 1088#64).toNat
      (sdData_val (BinaryPrefix.leftKind afterL.σ.mem (sp - 1088#64)))) _ = _
    rw [lowered, read64_writeMap8, sdData_toNat, kindRead]
  have kindSpill : read64 afterR.σ.mem (sp.toNat - 1088) =
      some (sign_extend (m := 64) (bytesT4 afterR.σ.mem (sp.toNat - 968))).toNat := by
    have eq := read64_agreeP (P := fun k => sp.toNat - 1088 ≤ k ∧ k < sp.toNat - 1080)
      (m := calledR.σ.mem) (m' := afterR.σ.mem) (fun k hk => by
        rcases qR.memFrame k (by omega) (by have := L.arena_stack; omega) with slot | same
        · rw [rightAddr] at slot; omega
        · exact same.symm) (a := sp.toNat - 1088) (fun j hj => by constructor <;> omega)
    rw [← eq, kindSaved, kindEq]
  exact ⟨afterR, stepsL.trans stepsR,
    { ordinary := ordinary
      owned := owned
      machine :=
        { stack_bytes := stackBytes
          sret_words := valueWordsTotal_of_interval stackBytes
            h.geometry.sret_inSL.1 h.geometry.sret_inSL.2
          payload_register := payloadRegister
          kind_spill := kindSpill } }⟩

/-- Execute both children from the reached binary arm and retain both results. -/
theorem BinaryArmReady.run_allocator
    {g gpre : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {st middle final : Vsa.While.St} {d env : Nat} {op : BinOp} {el er : Expr}
    {vl vr : Value} {costL costR maxRequest reserve : Nat}
    {sp ret dst node interp left right envReg v8 v9 v18 v19 : BitVec 64}
    {out : Array String} {m0 : Mem} {before : Config}
    (h : BinaryArmReady g gpre N A SL phiF phiC st d env op el er
      sp ret dst node interp left right envReg v8 v9 v18 v19 out m0 before)
    (L : AllocLedger A SL gpv headroom maxReq M) (request : maxRequest ≤ maxReq)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared
      (costL + (costR + reserve)) st.store before.σ.mem)
    (ast : ExprReprWithin before.σ.mem shared node.toNat (.binary op el er))
    (gp : before.σ.regs.get? .x3 = some gpv)
    (leftSem : EvalE st d env el middle vl)
    (bounded : StoreClosuresBounded st.store)
    (leftIH : EvalAllocatorIH st d env el middle vl costL maxRequest)
    (rightIH : EvalAllocatorIH middle d env er final vr costR maxRequest) :
    ∃ after, Steps before after ∧ BinaryAllocatorHeadReturn gpre N M phiF phiC
      st.store.frames.size st.store.closures.size shared reserve middle final vl vr
      sp ret dst v8 v9 v18 m0 after :=
  h.run_allocator_at L request allocator ast gp leftSem bounded (leftIH.at N) (rightIH.at N)

#print axioms BinaryArmReady.run_allocator_at
#print axioms BinaryArmReady.run_allocator

end Vsa.Sim
