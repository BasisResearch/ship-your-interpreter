import Vsa.Sim.StrlenHeadRun
import Vsa.Sim.EvalChildArm

namespace Vsa.Sim.StrlenRun

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

def wordSeg (back : Bool) : List BBlock :=
  if back then strlenX6d10TSeg else strlenX6d10FSeg

/-- Execute one complete word scan, selecting the branch from the string bytes. -/
theorem word {p r : BitVec 64} {len off j : Nat} {cs : List Char} {m0 : Mem}
    {before : Config} (h : WStG p r len cs m0 off j before)
    (back : Bool) (hb : decide (off + 8*(j+1) ≤ len) = back) :
    ∃ after, Steps before after ∧ Retained
      (if back then WStG p r len cs m0 off (j+1) else WTailG p r len cs m0 off j)
      before after := by
  let pos := p + BitVec.ofNat 64 (off + 8*j)
  let L : GRegs := [(14, pos), (13, magic7f), (11, BitVec.allOnes 64), (10, p), (1, r)]
  let bytes := EvalChildArm.wordLds8 m0 (p.toNat + (off + 8*j))
  obtain ⟨position, lo, hi, htif, _⟩ := wload_boundsG p len off j h.regions h.qalign h.jle
  have load : MemFacts before.σ.mem L bytes (mkLine 0x80006d10#64 0x00073603#32) := by
    change (0x80000000 ≤ _ ∧ _ + 8 ≤ 0x100000000 ∧
      (_ + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ _)) ∧ _
    refine ⟨⟨lo, hi, htif⟩, ?_⟩
    change LPins8 before.σ.mem ((p + BitVec.ofNat 64 (off + 8*j)) + 0#64).toNat bytes
    rw [BitVec.add_zero, position, h.mem]
    simp [LPins8, bytes, EvalChildArm.wordLds8]
  have value : bytesVal .ld bytes = strlenWordAt m0 (p.toNat + (off + 8*j)) := by
    change sign_extend (m := 64) (strlenWordAt m0 (p.toNat + (off + 8*j))) = _
    exact sext64_self _
  have detection : (strlenWordVal (strlenWordAt m0 (p.toNat + (off + 8*j))) ==
      BitVec.allOnes 64) = back := by
    have wordAt : strlenWordAt m0 (p.toNat + (off + 8*j)) = ldBytesT before.σ pos := by
      rw [ldBytesT_wordAt, h.mem, position]
    rw [wordAt]
    cases back
    · apply beq_eq_false_iff_ne.mpr
      exact detect_nottakenG before.σ p len (off + 8*j) cs
        (by rw [h.mem]; exact h.cstr) h.hlen h.jle
        (by have := of_decide_eq_false hb; omega) position
    · have detected := detect_takenG before.σ p len (off + 8*j) cs
        (by rw [h.mem]; exact h.cstr) h.hlen position
        (by have := of_decide_eq_true hb; omega)
      exact beq_iff_eq.mpr detected
  have guard : guardB bop.BEQ
      (((((bytesVal .ld bytes) &&& magic7f) + magic7f) ||| bytesVal .ld bytes) ||| magic7f)
      (BitVec.allOnes 64) = back := by
    change (_ == _) = back
    rw [value, strlenWordVal_eq]
    exact detection
  have facts : ChainFacts before.σ.mem before.σ.mem L [bytes] (wordSeg back) := by
    cases back <;> unfold wordSeg <;>
      chain_facts h.loaded with "Vsa.Sim.Code.strlen_at_"
    all_goals first | exact load | exact guard
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed (wordSeg back) L [bytes] 0x80006d10#64 vm
    (fun _ => False) AbiPreserved
    [(14, p + BitVec.ofNat 64 (off + 8*(j+1))), (13, magic7f),
      (11, BitVec.allOnes 64), (10, p), (1, r)] before
    h.good h.pc hvm ⟨h.a4, h.a3, h.a1, h.a0, h.ra, trivial⟩
    (by change KeysOK [14, 13, 11, 10, 1]; decide) facts
    (by change ChainOK 0x80006d10#64 [14, 13, 11, 10, 1] (wordSeg back)
        cases back <;> decide) h.tick (by intro k _; cases back <;> rfl)
    (by decide) (by cases back <;> decide) (by
      cases back <;>
        change some (pos + sign_extend (m := 64) (0x008#12)) =
          some (p + BitVec.ofNat 64 (off + 8*(j+1))) ∧
          some magic7f = some magic7f ∧ some (BitVec.allOnes 64) = some (BitVec.allOnes 64) ∧
          some p = some p ∧ some r = some r ∧ True
      all_goals simp only [pos, a4_incrG, and_self])
  obtain ⟨ha4, ha3, ha1, ha0, hra, _⟩ := C.selected_regs
  have mem : after.σ.mem = before.σ.mem := by cases back <;> exact C.mem
  refine ⟨after, C.steps, { output := C.output, frame := C.reg_frame, state := ?_ }⟩
  cases back
  · exact { good := C.good, loaded := by rw [mem]; exact h.loaded
            mem := mem.trans h.mem, pc := C.pc, a0 := ha0, a4 := ha4, ra := hra
            minstret := C.minstret, tick := C.tick, regions := h.regions, qalign := h.qalign
            cstr := h.cstr, hlen := h.hlen, jlo := h.jle
            jhi := by have := of_decide_eq_false hb; omega }
  · exact { good := C.good, loaded := by rw [mem]; exact h.loaded
            mem := mem.trans h.mem, pc := C.pc, a0 := ha0, a1 := ha1, a3 := ha3
            a4 := ha4, ra := hra, minstret := C.minstret, tick := C.tick
            regions := h.regions, qalign := h.qalign, cstr := h.cstr, hlen := h.hlen
            jle := of_decide_eq_true hb }

/-- Each reflected word iteration decreases the existing scan measure. -/
theorem wordIteration (p r : BitVec 64) (len : Nat) (cs : List Char) (m0 : Mem)
    (off : Nat) (origin : Config) (n : Nat) :
    Triple (fun c => Retained (WLoopIG p r len cs m0 off) origin c ∧
        WLoopBG p r len cs m0 off c ∧ WLoopMuG p len c = n)
      (fun c => Retained (WLoopIG p r len cs m0 off) origin c ∧ WLoopMuG p len c < n) := by
  intro before pre
  obtain ⟨kept, ⟨j, head⟩, measure⟩ := pre
  rw [wloopmuG_head p r len cs m0 off j before head] at measure
  have bound := head.jle
  by_cases back : off + 8*(j+1) ≤ len
  · obtain ⟨after, steps, next⟩ := word head true (by simp [back])
    have carried := kept.then next
    refine ⟨after, steps, { carried with state := Or.inl ⟨j+1, next.state⟩ }, ?_⟩
    rw [wloopmuG_head p r len cs m0 off (j+1) after next.state]
    omega
  · obtain ⟨after, steps, next⟩ := word head false (by simp [back])
    have carried := kept.then next
    refine ⟨after, steps, { carried with state := Or.inr ⟨j, next.state⟩ }, ?_⟩
    have pc := next.state.pc
    have measureZero : WLoopMuG p len after = 0 := by
      simp only [WLoopMuG, pc]
      rfl
    rw [measureZero]
    omega

/-- Scan all complete words and reach the NUL-containing word's byte tail. -/
theorem words {p r : BitVec 64} {len off j : Nat} {cs : List Char} {m0 : Mem}
    {before : Config} (h : WStG p r len cs m0 off j before) :
    ∃ after, Steps before after ∧ Retained (WAtTailG p r len cs m0 off) before after := by
  have initial : Retained (WLoopIG p r len cs m0 off) before before :=
    { state := Or.inl ⟨j, h⟩, output := rfl, frame := fun _ _ => rfl }
  obtain ⟨after, steps, reached, stopped⟩ :=
    loopFromBody (I := Retained (WLoopIG p r len cs m0 off) before)
      (B := WLoopBG p r len cs m0 off) (WLoopMuG p len)
      (wordIteration p r len cs m0 off before) before initial
  refine ⟨after, steps, { reached with state := ?_ }⟩
  rcases reached.state with atHead | atTail
  · exact False.elim (stopped atHead)
  · exact atTail

#print axioms word
#print axioms wordIteration
#print axioms words

end Vsa.Sim.StrlenRun
