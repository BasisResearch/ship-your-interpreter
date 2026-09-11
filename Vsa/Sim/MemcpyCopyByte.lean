import Vsa.Sim.MemcpyCopySegments
import Vsa.Sim.MemcpyCopyState
import Vsa.Sim.SegEffect
import Vsa.Sim.DeriveLoop

namespace Vsa.Sim.MemcpyCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

def byteSeg (more : Bool) : List BBlock :=
  if more then memcpyX6c48TSeg else memcpyX6c48FSeg

def byteRegs (dst src r : BitVec 64) (n i : Nat) : GRegs :=
  [(11, src + BitVec.ofNat 64 i), (14, dst + BitVec.ofNat 64 i),
   (17, dst + BitVec.ofNat 64 n), (10, dst), (1, r)]

/-- The reflected store writes exactly the current destination byte. -/
theorem byteMemory (dst src r : BitVec 64) (n i : Nat) (b : BitVec 8) (m : Mem)
    (more : Bool) (bound : dst.toNat + i < 2^64) :
    writeLog m (evalBlocks (byteSeg more)
      (SegEvalState.init (byteRegs dst src r n i) [[b]])).log =
      m.insert (dst.toNat + i) b := by
  cases more <;>
    change m.insert
      (((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x001#12)) +
        sign_extend (m := 64) (0xfff#12)).toNat (sbData (zero_extend (m := 64) b)) = _
  all_goals
    rw [ptr_succ]
    change m.insert (sbAddr (dst + BitVec.ofNat 64 (i+1))).toNat _ = _
    rw [sbAddr_succ, ptr_toNat dst i bound, sbData_zext]

/-- Execute the byte load, pointer increments, store, and loop branch. -/
theorem byte {dst src r : BitVec 64} {n i : Nat} {bs : Nat → BitVec 8} {m0 : Mem}
    {before : Config} (h : ByteState dst src r n i bs m0 before) (remaining : i < n) :
    ∃ after, Steps before after ∧ Retained (ByteState dst src r n (i+1) bs m0) before after := by
  let more := decide (i+1 < n)
  let L := byteRegs dst src r n i
  have srcAddr : ((src + BitVec.ofNat 64 i) + sign_extend (m := 64) (0#12)).toNat =
      src.toNat + i := by
    rw [show sign_extend (m := 64) (0#12) = (0#64) from rfl, BitVec.add_zero]
    exact ptr_toNat src i (by have := h.regions.src_hi; omega)
  have dstAddr : (((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x001#12)) +
      sign_extend (m := 64) (0xfff#12)).toNat = dst.toNat + i := by
    rw [ptr_succ]
    change (sbAddr (dst + BitVec.ofNat 64 (i+1))).toNat = _
    rw [sbAddr_succ]
    exact ptr_toNat dst i (by have := h.regions.dst_hi; omega)
  have guard : guardB bop.BNE (dst + BitVec.ofNat 64 n)
      ((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x001#12)) = more := by
    rw [ptr_succ]
    change ((dst + BitVec.ofNat 64 n) != (dst + BitVec.ofNat 64 (i+1))) = more
    by_cases next : i+1 < n
    · have ne : dst + BitVec.ofNat 64 n ≠ dst + BitVec.ofNat 64 (i+1) := by
        intro equal
        have eqNat := congrArg BitVec.toNat equal
        rw [ptr_toNat dst n (by have := h.regions.dst_hi; omega),
          ptr_toNat dst (i+1) (by have := h.regions.dst_hi; omega)] at eqNat
        omega
      simp [more, next, ne]
    · have equal : i+1 = n := by omega
      simp [more, equal]
  have load : MemFacts before.σ.mem L [bs i] (mkLine 0x80006c48#64 0x0005c783#32) := by
    let addr := ((src + BitVec.ofNat 64 i) + sign_extend (m := 64) (0#12)).toNat
    change (0x80000000 ≤ addr ∧ addr + 1 ≤ 0x100000000 ∧
      (addr + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ addr)) ∧
      (before.σ.mem[addr]?).getD 0 = bs i
    dsimp only [addr]
    rw [srcAddr]
    refine ⟨⟨by have := h.regions.src_lo; omega,
      by have := h.regions.src_hi; omega,
      by have := h.regions.src_win; omega⟩, ?_⟩
    exact lpin_of_present (h.meminv.src_intact i (Nat.le_refl _) remaining)
  have store : 0x80000000 ≤ dst.toNat + i ∧ dst.toNat + i + 1 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ dst.toNat + i :=
    ⟨by have := h.regions.dst_lo; omega, by have := h.regions.dst_hi; omega,
      by have := h.regions.dst_win; omega⟩
  have facts : ChainFacts before.σ.mem before.σ.mem L [[bs i]] (byteSeg more) := by
    cases chosen : more <;> unfold byteSeg <;>
      chain_facts h.loaded with "Vsa.Sim.Code.memcpy_at_"
    all_goals first
      | exact load
      | (let addr := (((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x001#12)) +
           sign_extend (m := 64) (0xfff#12)).toNat
         change 0x80000000 ≤ addr ∧ addr + 1 ≤ 0x100000000 ∧ tohostAddr + 16 ≤ addr
         dsimp only [addr]
         rw [dstAddr]; exact store)
      | exact guard.trans chosen
  obtain ⟨vm, hvm⟩ := h.good.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed (byteSeg more) L [[bs i]]
    0x80006c48#64 vm (fun a => a = dst.toNat + i) AbiPreserved
    (byteRegs dst src r n (i+1)) before h.good (by simpa [remaining] using h.pc) hvm
    ⟨h.a1, h.a4, h.a7, h.a0, h.ra, trivial⟩ (by change KeysOK [11,14,17,10,1]; decide)
    facts (by change ChainOK 0x80006c48#64 [11,14,17,10,1] (byteSeg more)
              cases more <;> decide) h.tick
    (by
      intro a outside
      rw [byteMemory dst src r n i (bs i) before.σ.mem more
        (by have := h.regions.dst_hi; omega)]
      rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)])
    (by decide) (by cases more <;> decide) (by
      cases more <;>
        change some ((src + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x001#12)) = _ ∧
          some ((dst + BitVec.ofNat 64 i) + sign_extend (m := 64) (0x001#12)) = _ ∧
          some (dst + BitVec.ofNat 64 n) = _ ∧ some dst = _ ∧ some r = _ ∧ True
      all_goals simp only [ptr_succ, and_self])
  obtain ⟨a1, a4, a7, a0, ra, _⟩ := C.selected_regs
  have mem : after.σ.mem = before.σ.mem.insert (dst.toNat + i) (bs i) :=
    C.mem.trans (byteMemory dst src r n i (bs i) before.σ.mem more
      (by have := h.regions.dst_hi; omega))
  refine ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame
      presence := by rw [mem]; exact memExtends_insert _ _ _
      state := { good := C.good, tick := C.tick, a0 := a0, ra := ra
                 regions := h.regions, bound := by omega
                 a1 := a1, a4 := a4, a7 := a7
                 meminv := by rw [mem]; exact storeByte h.meminv h.regions.disjoint remaining
                 loaded := ?_, pc := ?_ } }⟩
  · rw [mem]
    exact loaded_insert _ _ _ (by have := h.regions.code_disjoint; omega) h.loaded
  · have pc := C.pc
    by_cases next : i+1 < n
    · simp only [more, next, decide_true] at pc
      simpa only [next, if_true] using pc
    · simp only [more, next, decide_false] at pc
      simpa only [next, if_false] using pc

#print axioms byteMemory
#print axioms byte

end Vsa.Sim.MemcpyCopy
