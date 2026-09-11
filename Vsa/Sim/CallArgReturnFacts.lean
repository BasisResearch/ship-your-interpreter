import Vsa.Sim.CallArgReturnData

namespace Vsa.Sim.CallArgReturn

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

/-- Later reads retain their original bytes through disjoint argument-slot stores. -/
private theorem loadFacts {node base sp : BitVec 64} {index count : Nat}
    (G : CallArgStage.Geometry node base sp index count) {m m' : Mem} {L : GRegs} {a : MInstr}
    (off : Nat) (bound : off ≤ 80) (kind : a.kind = .ld)
    (address : (eaddrM a L).toNat = sp.toNat + off)
    (agree : ∀ j, j < 8 → m'[sp.toNat + off + j]? = m[sp.toNat + off + j]?) :
    MemFacts m' L (EvalChildArm.wordLds8 m (sp.toNat + off)) a := by
  have zero := agree 0 (by decide)
  simp only [Nat.add_zero] at zero
  simp only [MemFacts, kind, address]
  refine ⟨⟨by have := G.caller.stackLo; omega, by have := G.caller.stackHi; omega,
    Or.inr (by have := G.caller.stackHtif; omega)⟩, ?_⟩
  simp [LPins8, EvalChildArm.wordLds8, agree, zero]

/-- Discharge all seven reads, three writes, and the actual argument-loop branch. -/
theorem facts {node base sp : BitVec 64} {index count : Nat}
    (G : CallArgStage.Geometry node base sp index count) (m : Mem) (env : BitVec 64)
    (saved : CallArgStage.Saved m sp env index count) (code : Code.Eval_exprLoaded m) :
    ChainFacts m m (argsReturnL sp) (loads m sp) (seg (decide (index + 1 < count))) := by
  have dest := EvalChildArm.bytesVal_ld_wordLds m sp.toNat (CallArgStage.destination sp index) saved.destinationRead
  have ix := EvalChildArm.bytesVal_ld_wordLds m (sp.toNat + 16) (BitVec.ofNat 64 index) saved.indexRead
  have len := EvalChildArm.bytesVal_ld_wordLds m (sp.toNat + 24) (BitVec.ofNat 64 count) saved.countRead
  have address0 : (bytesVal .ld (EvalChildArm.wordLds8 m sp.toNat) + sign_extend (m := 64) (0xd00#12)).toNat =
      slot sp index + 0 := by rw [dest]; exact storeAddress G 0 (by decide)
  have address8 : (bytesVal .ld (EvalChildArm.wordLds8 m sp.toNat) + sign_extend (m := 64) (0xd08#12)).toNat =
      slot sp index + 8 := by rw [dest]; exact storeAddress G 8 (by decide)
  have address16 : (bytesVal .ld (EvalChildArm.wordLds8 m sp.toNat) + sign_extend (m := 64) (0xd10#12)).toNat =
      slot sp index + 16 := by rw [dest]; exact storeAddress G 16 (by decide)
  have stackAddr (off : Nat) (bound : off ≤ 80) : (sp + BitVec.ofNat 64 off).toNat = sp.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show off < 2^64 by omega),
      Nat.mod_eq_of_lt (show sp.toNat + off < 2^64 by have := G.caller.stackHi; omega)]
  have intact1 (v : BitVec (8 * 8)) (off j : Nat) (ho : off ≤ 80) (hj : j < 8) :
      (writeMap8 m (bytesVal .ld (EvalChildArm.wordLds8 m sp.toNat) + sign_extend (m := 64) (0xd00#12)).toNat v)[sp.toNat + off + j]? = m[sp.toNat + off + j]? := by
    rw [address0]
    exact getElem_writeMap8_disjoint _ _ _ _ (Or.inl (by unfold slot; omega))
  have intact2 (v w : BitVec (8 * 8)) (off j : Nat) (ho : off ≤ 80) (hj : j < 8) :
      (writeMap8
        (writeMap8 m (bytesVal .ld (EvalChildArm.wordLds8 m sp.toNat) + sign_extend (m := 64) (0xd00#12)).toNat v)
        (bytesVal .ld (EvalChildArm.wordLds8 m sp.toNat) + sign_extend (m := 64) (0xd08#12)).toNat w)[sp.toNat + off + j]? = m[sp.toNat + off + j]? := by
    rw [address8, getElem_writeMap8_disjoint _ _ _ _ (Or.inl (by unfold slot; omega))]
    exact intact1 v off j ho hj
  have guard : guardB bop.BNE
      (bytesVal .ld (EvalChildArm.wordLds8 m (sp.toNat + 16)) + 1#64)
      (bytesVal .ld (EvalChildArm.wordLds8 m (sp.toNat + 24))) = decide (index + 1 < count) := by
    rw [ix, len]
    exact branch index count G.indexBound G.countBound
  generalize he : decide (index + 1 < count) = more
  cases more <;> simp only [seg, Bool.false_eq_true, if_false, if_true]
  all_goals
    chain_facts code with "Vsa.Sim.Code.eval_expr_at_"
    · exact BinaryPrefix.stack_load_facts G.caller 64 (Or.inl rfl) rfl rfl (by decide)
    · simpa only [Nat.add_zero] using BinaryPrefix.stack_load_facts G.caller 0 (Or.inl rfl) rfl rfl (by decide)
    · exact BinaryPrefix.stack_load_facts G.caller 16 (Or.inl rfl) rfl rfl (by decide)
    · exact BinaryPrefix.stack_load_facts G.caller 24 (Or.inl rfl) rfl rfl (by decide)
    · exact storeFacts G 0 (by decide) (by decide) rfl address0
    · apply loadFacts G 72 (by decide) rfl
      · exact stackAddr 72 (by decide)
      · intro j hj
        exact intact1 _ 72 j (by decide) hj
    · apply loadFacts G 8 (by decide) rfl
      · exact stackAddr 8 (by decide)
      · intro j hj
        exact intact1 _ 8 j (by decide) hj
    · exact storeFacts G 8 (by decide) (by decide) rfl address8
    · apply loadFacts G 80 (by decide) rfl
      · exact stackAddr 80 (by decide)
      · intro j hj
        exact intact2 _ _ 80 j (by decide) hj
    · exact storeFacts G 16 (by decide) (by decide) rfl address16
    · exact guard.trans he

end Vsa.Sim.CallArgReturn
