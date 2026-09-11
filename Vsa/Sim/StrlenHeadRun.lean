import Vsa.Sim.StrlenSegments
import Vsa.Sim.StrlenReadState
import Vsa.Sim.SegEffect
import Vsa.Sim.DeriveLoop

namespace Vsa.Sim.StrlenRun

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc
open Vsa.Logic

/-- The actual scan endpoint retains the caller observations. -/
structure Retained (P : Config → Prop) (before after : Config) : Prop where
  state : P after
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, AbiPreserved R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Enter the byte peel using the reflected alignment branch. -/
theorem entry {p r : BitVec 64} {len : Nat} {cs : List Char} {m0 : Mem}
    {before : Config} (h : UPre p r len cs m0 before) :
    ∃ after, Steps before after ∧ Retained (HSt p r len cs m0 0) before after := by
  have facts : ChainFacts before.σ.mem before.σ.mem [(10, p), (1, r)] []
      strlenX6cf0TSeg := by
    chain_facts h.loaded with "Vsa.Sim.Code.strlen_at_"
    change ((p &&& sign_extend (m := 64) (0x007#12)) != 0#64) = true
    exact bnez_nonzero_true _ (andi7_unaligned p h.align)
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed strlenX6cf0TSeg [(10, p), (1, r)] []
    0x80006cf0#64 vm (fun _ => False) AbiPreserved [(10, p), (1, r), (14, p)] before
    h.good h.pc hvm ⟨h.a0, h.ra, trivial⟩ (by change KeysOK [10, 1]; decide) facts
    (by change ChainOK 0x80006cf0#64 [10, 1] strlenX6cf0TSeg; decide) h.tick
    (by intro k _; rfl) (by decide) (by decide) (by
      change some p = some p ∧ some r = some r ∧ some (p + 0#64) = some p ∧ True
      simp)
  obtain ⟨ha0, hra, ha4, _⟩ := C.selected_regs
  refine ⟨after, C.steps, ?_⟩
  exact { output := C.output, frame := C.reg_frame
          state := { good := C.good, loaded := by rw [C.mem]; exact h.loaded
                     mem := C.mem.trans h.mem, pc := C.pc, a0 := ha0
                     a4 := by simpa using ha4, ra := hra, minstret := C.minstret
                     tick := C.tick, regions := h.regions, cstr := h.cstr
                     hlen := h.hlen, mle := Nat.zero_le _ } }

/- Stop before the common head return, keeping its PC distinct from the loop. -/
#derive_case strlenHeadNulExitSeg chain
  [(0x80006d88#64, 0x40a70733#32),
   (0x80006d8c#64, 0xfff70513#32)]

def nonzeroSeg (aligned : Bool) : List BBlock :=
  strlenX6d78TSeg ++ if aligned then strlenX6d74TSeg else strlenX6d74FSeg

def nulSeg : List BBlock := strlenX6d78FSeg ++ strlenHeadNulExitSeg

/-- One total byte load, supplied by the represented string. -/
theorem headLoad {p r : BitVec 64} {len m : Nat} {cs : List Char} {m0 : Mem}
    {before : Config} (h : HSt p r len cs m0 m before) :
    MemFacts before.σ.mem [(14, p + BitVec.ofNat 64 m), (10, p), (1, r)]
      [(m0[p.toNat + m]?).getD 0] (mkLine 0x80006d78#64 0x00074783#32) := by
  obtain ⟨_, lo, hi, htif⟩ := head_lbu_bounds p len m h.regions h.mle
  have addr : ((p + BitVec.ofNat 64 m) + sign_extend (m := 64) (0x000#12)).toNat =
      p.toNat + m := by
    rw [sext0_add]
    exact ptrN p m (by have := h.regions.nowrap; have := h.mle; omega)
  change (0x80000000 ≤ _ ∧ _ + 1 ≤ 0x100000000 ∧
      (_ + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ _)) ∧ _
  refine ⟨⟨lo, hi, htif⟩, ?_⟩
  change (before.σ.mem[((p + BitVec.ofNat 64 m) + sign_extend (m := 64) (0x000#12)).toNat]?).getD 0 = _
  rw [addr, h.mem]
  rfl

/-- Advance a nonzero byte and take the actual next-pointer alignment branch. -/
theorem nonzero {p r : BitVec 64} {len m : Nat} {cs : List Char} {m0 : Mem}
    {before : Config} (h : HSt p r len cs m0 m before) (hlt : m < len)
    (aligned : Bool) (hal : decide ((p.toNat + (m+1)) % 8 = 0) = aligned) :
    ∃ after, Steps before after ∧ Retained
      (if aligned then HAlign p r len cs m0 (m+1) else HSt p r len cs m0 (m+1))
      before after := by
  let L : GRegs := [(14, p + BitVec.ofNat 64 m), (10, p), (1, r)]
  let bytes := [[(m0[p.toNat + m]?).getD 0]]
  have nonzeroByte : guardB bop.BNE (bytesVal .lbu bytes.head!) 0#64 = true := by
    change ((zero_extend (m := 64) ((m0[p.toNat + m]?).getD 0)) != 0#64) = true
    rw [hdec_guard p len m cs m0 h.cstr h.hlen h.mle]
    simp [Nat.ne_of_lt hlt]
  have alignGuard : guardB bop.BEQ
      (((p + BitVec.ofNat 64 m) + sign_extend (m := 64) (0x001#12)) &&&
        sign_extend (m := 64) (0x007#12)) 0#64 = aligned := by
    change (_ == 0#64) = aligned
    rw [a4_incr1, head_align_guard p m (by have := h.regions.nowrap; omega)]
    exact hal
  have facts : ChainFacts before.σ.mem before.σ.mem L bytes (nonzeroSeg aligned) := by
    cases aligned <;> unfold nonzeroSeg <;>
      chain_facts h.loaded with "Vsa.Sim.Code.strlen_at_"
    all_goals first | exact headLoad h | exact nonzeroByte | exact alignGuard
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed (nonzeroSeg aligned) L bytes
    0x80006d78#64 vm (fun _ => False) AbiPreserved
    [(14, p + BitVec.ofNat 64 (m+1)), (10, p), (1, r)] before
    h.good h.pc hvm ⟨h.a4, h.a0, h.ra, trivial⟩ (by change KeysOK [14, 10, 1]; decide) facts
    (by change ChainOK 0x80006d78#64 [14, 10, 1] (nonzeroSeg aligned)
        cases aligned <;> decide) h.tick
    (by intro k _; cases aligned <;> rfl) (by decide)
    (by cases aligned <;> decide) (by
      cases aligned <;>
        change some ((p + BitVec.ofNat 64 m) + sign_extend (m := 64) (0x001#12)) =
          some (p + BitVec.ofNat 64 (m+1)) ∧ some p = some p ∧ some r = some r ∧ True
      all_goals simp only [a4_incr1, and_self])
  obtain ⟨ha4, ha0, hra, _⟩ := C.selected_regs
  have mem : after.σ.mem = before.σ.mem := by cases aligned <;> exact C.mem
  refine ⟨after, C.steps, { output := C.output, frame := C.reg_frame, state := ?_ }⟩
  cases aligned
  · exact { good := C.good, loaded := by rw [mem]; exact h.loaded
            mem := mem.trans h.mem, pc := C.pc, a0 := ha0, a4 := ha4, ra := hra
            minstret := C.minstret, tick := C.tick, regions := h.regions
            cstr := h.cstr, hlen := h.hlen, mle := by omega }
  · exact { good := C.good, loaded := by rw [mem]; exact h.loaded
            mem := mem.trans h.mem, pc := C.pc, a0 := ha0, a4 := ha4, ra := hra
            minstret := C.minstret, tick := C.tick, regions := h.regions
            cstr := h.cstr, hlen := h.hlen, off0le := by omega
            qalign := of_decide_eq_true hal, offpos := by omega }

/-- A NUL byte reaches the head return with the exact string length. -/
theorem nul {p r : BitVec 64} {len m : Nat} {cs : List Char} {m0 : Mem}
    {before : Config} (h : HSt p r len cs m0 m before) (hm : m = len) :
    ∃ after, Steps before after ∧
      Retained (AtRet r len m0 0x80006d90#64) before after := by
  let L : GRegs := [(14, p + BitVec.ofNat 64 m), (10, p), (1, r)]
  let bytes := [[(m0[p.toNat + m]?).getD 0]]
  have facts : ChainFacts before.σ.mem before.σ.mem L bytes nulSeg := by
    chain_facts h.loaded with "Vsa.Sim.Code.strlen_at_"
    · exact headLoad h
    · change ((zero_extend (m := 64) ((m0[p.toNat + m]?).getD 0)) != 0#64) = false
      rw [hdec_guard p len m cs m0 h.cstr h.hlen h.mle]
      simp [hm]
  have lengthValue : (((p + BitVec.ofNat 64 m) + sign_extend (m := 64) (0x001#12)) - p) +
      sign_extend (m := 64) (0xfff#12) = BitVec.ofNat 64 len := by
    rw [a4_incr1, sub_a4_a0_val]
    rw [show (sign_extend (m := 64) (0xfff#12) : BitVec 64) = -(BitVec.ofNat 64 1) by decide,
      BitVec.add_neg_eq_sub, ofNat_sub (m+1) 1 (by omega)]
    congr 1
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed nulSeg L bytes 0x80006d78#64 vm
    (fun _ => False) AbiPreserved [(10, BitVec.ofNat 64 len), (1, r)] before
    h.good h.pc hvm ⟨h.a4, h.a0, h.ra, trivial⟩
    (by change KeysOK [14, 10, 1]; decide) facts
    (by change ChainOK 0x80006d78#64 [14, 10, 1] nulSeg; decide) h.tick
    (by intro k _; rfl) (by decide) (by decide) (by
      change some ((((p + BitVec.ofNat 64 m) + sign_extend (m := 64) (0x001#12)) - p) +
        sign_extend (m := 64) (0xfff#12)) = some (BitVec.ofNat 64 len) ∧ some r = some r ∧ True
      simp only [lengthValue, and_self])
  obtain ⟨ha0, hra, _⟩ := C.selected_regs
  exact ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame
      state := ⟨C.good, by rw [C.mem]; exact h.loaded, C.mem.trans h.mem,
        C.pc, ha0, hra, C.minstret, C.tick⟩ }⟩

/-- Rebase retained observations after another actual run. -/
theorem Retained.then {P Q : Config → Prop} {origin before after : Config}
    (first : Retained P origin before) (second : Retained Q before after) :
    Retained Q origin after :=
  { state := second.state, output := second.output.trans first.output
    frame := fun R hR => (second.frame R hR).trans (first.frame R hR) }

/-- One reflected peel iteration decreases the existing string-scan measure. -/
theorem headIteration (p r : BitVec 64) (len : Nat) (cs : List Char) (m0 : Mem)
    (origin : Config) (n : Nat) :
    Triple (fun c => Retained (HLoopI p r len cs m0) origin c ∧
        HLoopB p r len cs m0 c ∧ HLoopMu p len c = n)
      (fun c => Retained (HLoopI p r len cs m0) origin c ∧ HLoopMu p len c < n) := by
  intro before pre
  obtain ⟨kept, ⟨m, head⟩, measure⟩ := pre
  rw [hloopmu_head p r len cs m0 m before head] at measure
  have bound := head.mle
  by_cases zero : m = len
  · obtain ⟨after, steps, next⟩ := nul head zero
    have carried := kept.then next
    refine ⟨after, steps,
      { carried with state := Or.inr (Or.inl next.state) }, ?_⟩
    rw [hloopmu_atret p r len m0 after next.state]
    omega
  · have lt : m < len := by omega
    by_cases aligned : (p.toNat + (m+1)) % 8 = 0
    · obtain ⟨after, steps, next⟩ := nonzero head lt true (by simp [aligned])
      have carried := kept.then next
      refine ⟨after, steps,
        { carried with state := Or.inr (Or.inr ⟨m+1, next.state⟩) }, ?_⟩
      rw [hloopmu_align p r len cs m0 (m+1) after next.state]
      omega
    · obtain ⟨after, steps, next⟩ := nonzero head lt false (by simp [aligned])
      have carried := kept.then next
      refine ⟨after, steps,
        { carried with state := Or.inl ⟨m+1, next.state⟩ }, ?_⟩
      rw [hloopmu_head p r len cs m0 (m+1) after next.state]
      omega

/-- Complete the unaligned entry and peel with the caller frame intact. -/
theorem head {p r : BitVec 64} {len : Nat} {cs : List Char} {m0 : Mem}
    {before : Config} (h : UPre p r len cs m0 before) :
    ∃ after, Steps before after ∧ Retained
      (fun c => AtRet r len m0 0x80006d90#64 c ∨ HAtAlign p r len cs m0 c)
      before after := by
  obtain ⟨entered, entrySteps, started⟩ := entry h
  have initial : Retained (HLoopI p r len cs m0) before entered :=
    { started with state := Or.inl ⟨0, started.state⟩ }
  obtain ⟨after, loopSteps, reached, stopped⟩ :=
    loopFromBody (I := Retained (HLoopI p r len cs m0) before)
      (B := HLoopB p r len cs m0) (HLoopMu p len)
      (headIteration p r len cs m0 before) entered initial
  refine ⟨after, entrySteps.trans loopSteps, { reached with state := ?_ }⟩
  rcases reached.state with atHead | atReturn | aligned
  · exact False.elim (stopped atHead)
  · exact Or.inl atReturn
  · exact Or.inr aligned

#print axioms entry
#print axioms headLoad
#print axioms nonzero
#print axioms nul
#print axioms headIteration
#print axioms head

end Vsa.Sim.StrlenRun
