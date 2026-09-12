import EnvGetCopyLog
import Vsa.Sim.WordLoadData
import Vsa.Sim.EnvGetSpec5
import Vsa.Sim.Code.Env_get

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr

namespace Vsa.Sim.EnvGetReflected

/-- Access geometry supplied by the reached frame and caller output window. -/
structure CopyGeom (env out : BitVec 64) (pv i : Nat) : Prop where
  envLo : 0x80000000 ≤ env.toNat + 16
  envHi : env.toNat + 24 ≤ 0x100000000
  envHtif : tohostAddr + 8 ≤ env.toNat + 16
  sourceLo : 0x80000000 ≤ pv + 24 * i
  sourceHi : pv + 24 * i + 24 ≤ 0x100000000
  sourceHtif : tohostAddr + 8 ≤ pv + 24 * i
  outLo : 0x80000000 ≤ out.toNat
  outHi : out.toNat + 24 ≤ 0x100000000
  outHtif : tohostAddr + 16 ≤ out.toNat
  outAlign : out.toNat % 8 = 0
  disjoint : pv + 24 * i + 24 ≤ out.toNat ∨ out.toNat + 24 ≤ pv + 24 * i
  index : i < 2^32

def copyInput (env out sp : BitVec 64) (i : Nat) : GRegs :=
  env_getX2c70L env (BitVec.ofNat 64 i) out ++ [(2, sp)]

/-- Keeping the stack register does not change the copy's write log. -/
theorem copy_input_log (env out sp : BitVec 64) (i : Nat)
    (be b0 b1 b2 : List (BitVec 8)) :
    (evalBlocks env_getX2c70Seg
      (SegEvalState.init (copyInput env out sp i) [be, b0, b1, b2])).log =
    (evalBlocks env_getX2c70Seg
      (SegEvalState.init (env_getX2c70L env (BitVec.ofNat 64 i) out) [be, b0, b1, b2])).log := rfl

/-- One destination store uses only its 24-byte output window. -/
theorem copy_store_facts {m : Mem} {L : GRegs} {a : MInstr} {bs : List (BitVec 8)}
    {env out : BitVec 64} {pv i : Nat} (h : CopyGeom env out pv i) (off : Nat)
    (hk : a.kind = .sd) (hsrc : srcVal a.rs1 L = out)
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hoff : off + 8 ≤ 24) (halign : off % 8 = 0) : MemFacts m L bs a := by
  have hea : (eaddrM a L).toNat = out.toNat + off := by
    unfold eaddrM
    rw [hsrc, BitVec.toNat_add, himm, Nat.mod_eq_of_lt (by have := h.outHi; omega)]
  apply memFacts_sd_frame m L a bs hk
  · rw [hea]; have := h.outLo; omega
  · rw [hea]; have := h.outHi; omega
  · rw [hea]; have := h.outHtif; omega
  · rw [hea]; have := h.outAlign; omega

/-- Reflected inputs and the concrete resulting copy memory. -/
structure CopyData (m : Mem) (env out sp : BitVec 64) (pv i : Nat)
    (lds : List (List (BitVec 8))) : Prop where
  facts : ChainFacts m m (copyInput env out sp i) lds env_getX2c70Seg
  log : writeLog m (evalBlocks env_getX2c70Seg
    (SegEvalState.init (copyInput env out sp i) lds)).log = copy3Log m (pv + 24 * i) out.toNat

/-- Assemble the segment from the four reads at their actual memories. -/
theorem copy_facts (m : Mem) (env out sp : BitVec 64) (pv i : Nat)
    (h : CopyGeom env out pv i) (hcode : Code.Env_getLoaded m)
    (be b0 b1 b2 : List (BitVec 8))
    (we : MemFacts m (copyInput env out sp i) be (mkLine 0x80002c70#64 0x010a3783#32))
    (slot : BitVec 64)
    (hslot : slot = bytesVal .ld be + shift_bits_left
      (shift_bits_left (BitVec.ofNat 64 i) (Sail.BitVec.extractLsb (0x01#6) 5 0) + BitVec.ofNat 64 i)
      (Sail.BitVec.extractLsb (0x03#6) 5 0))
    (w0 : MemFacts m [(15, slot)] b0 (mkLine 0x80002c84#64 0x0007b703#32))
    (m1 m2 : Mem)
    (hm1 : m1 = writeMap8 m (out + sign_extend (m := 64) (0#12)).toNat
      (sdData_val (bytesVal .ld b0)))
    (hm2 : m2 = writeMap8 m1 (out + sign_extend (m := 64) (0x008#12)).toNat
      (sdData_val (bytesVal .ld b1)))
    (w1 : MemFacts m1 [(15, slot)] b1 (mkLine 0x80002c90#64 0x0087b703#32))
    (w2 : MemFacts m2 [(15, slot)] b2 (mkLine 0x80002c98#64 0x0107b783#32)) :
    ChainFacts m m (copyInput env out sp i) [be, b0, b1, b2] env_getX2c70Seg := by
  subst slot m2 m1
  chain_facts hcode with "Vsa.Sim.Code.env_get_at_"
  · exact we
  · exact w0
  · exact copy_store_facts h 0 (by rfl) (by rfl) (by decide) (by decide) (by decide)
  · exact w1
  · exact copy_store_facts h 8 (by rfl) (by rfl) (by decide) (by decide) (by decide)
  · exact w2
  · exact copy_store_facts h 16 (by rfl) (by rfl) (by decide) (by decide) (by decide)

/-- Supply all four loads at their actual memories, including the two reads
after destination stores. The shared word-read adapter supplies facts and values. -/
theorem copy_data (m : Mem) (env out sp : BitVec 64) (pv i : Nat)
    (h : CopyGeom env out pv i) (hcode : Code.Env_getLoaded m)
    (hvalues : read64 m (env.toNat + 16) = some pv)
    (hwords : ValueWordsTotal m (pv + 24 * i)) :
    ∃ lds, CopyData m env out sp pv i lds := by
  have henv := off_ed_10 env (by have := h.envHi; omega)
  have hpv : (BitVec.ofNat 64 pv).toNat = pv := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.sourceHi; omega)]
  let ae := mkLine 0x80002c70#64 0x010a3783#32
  have he : (eaddrM ae (copyInput env out sp i)).toNat = env.toNat + 16 := henv
  obtain ⟨be, we⟩ := wordLoadFacts_of_read64 m (copyInput env out sp i) ae
    (BitVec.ofNat 64 pv) (by rfl)
    (by rw [he]; exact h.envLo) (by rw [he]; have := h.envHi; omega)
    (by rw [he]; right; have := h.envHtif; omega)
    (by rw [he, hpv]; exact hvalues)
  let slot := bytesVal .ld be + shift_bits_left
    (shift_bits_left (BitVec.ofNat 64 i) (Sail.BitVec.extractLsb (0x01#6) 5 0) + BitVec.ofNat 64 i)
    (Sail.BitVec.extractLsb (0x03#6) 5 0)
  have hslot : slot.toNat = pv + 24 * i := by
    change (bytesVal .ld be + _).toNat = _
    rw [we.value, stride_24 i h.index, BitVec.toNat_add, hpv, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := h.sourceHi; omega : 24 * i < 2^64),
      Nat.mod_eq_of_lt (by have := h.sourceHi; omega)]
  have hs0 : (slot + sign_extend (m := 64) (0#12)).toNat = pv + 24 * i :=
    (off_ed_00 slot).trans hslot
  have hs8 : (slot + sign_extend (m := 64) (0x008#12)).toNat = pv + 24 * i + 8 := by
    rw [off_ed_08 slot (by have := h.sourceHi; omega), hslot]
  have hs16 : (slot + sign_extend (m := 64) (0x010#12)).toNat = pv + 24 * i + 16 := by
    rw [off_ed_10 slot (by have := h.sourceHi; omega), hslot]
  obtain ⟨d0, d1, d2, hr0, hr1, hr2⟩ := hwords
  let ls : GRegs := [(15, slot)]
  let a0 := mkLine 0x80002c84#64 0x0007b703#32
  let a1 := mkLine 0x80002c90#64 0x0087b703#32
  let a2 := mkLine 0x80002c98#64 0x0107b783#32
  have hea0 : (eaddrM a0 ls).toNat = pv + 24 * i := hs0
  have hea1 : (eaddrM a1 ls).toNat = pv + 24 * i + 8 := hs8
  have hea2 : (eaddrM a2 ls).toNat = pv + 24 * i + 16 := hs16
  obtain ⟨b0, w0⟩ := wordLoadFacts_of_read64 m ls a0 d0 (by rfl)
    (by rw [hea0]; exact h.sourceLo) (by rw [hea0]; have := h.sourceHi; omega)
    (by rw [hea0]; right; have := h.sourceHtif; omega) (by rw [hea0]; exact hr0)
  let m1 := writeMap8 m (out + sign_extend (m := 64) (0#12)).toNat
    (sdData_val (bytesVal .ld b0))
  have hm1 : ∀ k, pv + 24 * i ≤ k ∧ k < pv + 24 * i + 24 → m1[k]? = m[k]? := by
    intro k hk
    dsimp only [m1]
    rw [off_ed_00]
    exact getElem_writeMap8_disjoint _ _ _ _ (by have := h.disjoint; omega)
  have hr1' : read64 m1 (pv + 24 * i + 8) = some d1.toNat :=
    (read64_agreeP hm1 (fun k hk => by omega)).trans hr1
  obtain ⟨b1, w1⟩ := wordLoadFacts_of_read64 m1 ls a1 d1 (by rfl)
    (by rw [hea1]; have := h.sourceLo; omega) (by rw [hea1]; have := h.sourceHi; omega)
    (by rw [hea1]; right; have := h.sourceHtif; omega) (by rw [hea1]; exact hr1')
  let m2 := writeMap8 m1 (out + sign_extend (m := 64) (0x008#12)).toNat
    (sdData_val (bytesVal .ld b1))
  have hm2 : ∀ k, pv + 24 * i ≤ k ∧ k < pv + 24 * i + 24 → m2[k]? = m[k]? := by
    intro k hk
    dsimp only [m2]
    rw [getElem_writeMap8_disjoint _ _ _ _ (by
      rw [off_ed_08 out (by have := h.outHi; omega)]
      have := h.disjoint; omega)]
    exact hm1 k hk
  have hr2' : read64 m2 (pv + 24 * i + 16) = some d2.toNat :=
    (read64_agreeP hm2 (fun k hk => by omega)).trans hr2
  obtain ⟨b2, w2⟩ := wordLoadFacts_of_read64 m2 ls a2 d2 (by rfl)
    (by rw [hea2]; have := h.sourceLo; omega) (by rw [hea2]; have := h.sourceHi; omega)
    (by rw [hea2]; right; have := h.sourceHtif; omega) (by rw [hea2]; exact hr2')
  refine ⟨[be, b0, b1, b2], ?_⟩
  constructor
  · exact copy_facts m env out sp pv i h hcode be b0 b1 b2 we.facts
      slot rfl w0.facts m1 m2 rfl rfl w1.facts w2.facts
  · rw [copy_input_log]
    exact copy_log_of_loads m env (BitVec.ofNat 64 i) out (pv + 24 * i) be b0 b1 b2
      (by have := h.outHi; omega)
      (w0.value.trans (EvalChildArm.bytesVal_ld_wordLds m _ d0 hr0).symm)
      (w1.value.trans (EvalChildArm.bytesVal_ld_wordLds m _ d1 hr1).symm)
      (w2.value.trans (EvalChildArm.bytesVal_ld_wordLds m _ d2 hr2).symm)

#print axioms copy_store_facts
#print axioms copy_input_log
#print axioms copy_facts
#print axioms copy_data

end Vsa.Sim.EnvGetReflected
