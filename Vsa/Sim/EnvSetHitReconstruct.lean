import Vsa.Sim.EnvSetHit
import Vsa.Sim.EnvSetScanIter
import Vsa.Sim.StoreSetFootprint
import Vsa.Sim.EqNeReprReadback

/-! Byte-level reconstruction for the three `sd` instructions in the
successful `env_set` block. -/

open LeanRV64DExecutable Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While

namespace Vsa.Sim

set_option maxHeartbeats 800000

#derive_case envSetHitLoadSeg chain
  [(0x80002d3c#64, 0x010a3783#32),
   (0x80002d40#64, 0x00141713#32),
   (0x80002d44#64, 0x000ab583#32),
   (0x80002d48#64, 0x008ab603#32),
   (0x80002d4c#64, 0x010ab683#32)]

#derive_case envSetHitCalcSeg chain
  [(0x80002d50#64, 0x00870733#32),
   (0x80002d54#64, 0x00371713#32),
   (0x80002d58#64, 0x00e787b3#32)]

#derive_case envSetHitStore0Seg chain
  [(0x80002d5c#64, 0x00b7b023#32)]

#derive_case envSetHitStore1Seg chain
  [(0x80002d60#64, 0x00c7b423#32)]

#derive_case envSetHitStore2Seg chain
  [(0x80002d64#64, 0x00d7b823#32)]

def envSetHitStoresL (dst w0 w1 w2 : BitVec 64) : GRegs :=
  [(15, dst), (11, w0), (12, w1), (13, w2)]

def envSetHitCalcL (pv idx w0 w1 w2 : BitVec 64) : GRegs :=
  [(15, pv), (8, idx), (14, idx <<< 1), (11, w0), (12, w1), (13, w2)]

def envSetHitLoadLiveL (env valuePtr idx sp : BitVec 64) : GRegs :=
  envSetHitL env valuePtr idx ++ [(2, sp)]

def envSetHitCalcLiveL (pv idx w0 w1 w2 sp : BitVec 64) : GRegs :=
  envSetHitCalcL pv idx w0 w1 w2 ++ [(2, sp)]

def envSetHitStoresLiveL (dst w0 w1 w2 sp : BitVec 64) : GRegs :=
  envSetHitStoresL dst w0 w1 w2 ++ [(2, sp)]

def envSetHitDst (pv idx : BitVec 64) : BitVec 64 :=
  pv + (((idx <<< 1) + idx) <<< 3)

def EnvSetHitLoadPost (pv idx w0 w1 w2 sp : BitVec 64)
    (m : Mem) (out0 : Array String) (c : Vsa.Machine.Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧ c.σ.mem = m ∧ c.σ.sailOutput = out0 ∧
  c.σ.regs.get? Register.PC = some (0x80002d50#64 : BitVec 64) ∧
  (∃ mi, c.σ.regs.get? Register.minstret = some mi) ∧
  GHolds c.σ (envSetHitCalcLiveL pv idx w0 w1 w2 sp)

def EnvSetHitCalcPost (pv idx w0 w1 w2 sp : BitVec 64)
    (m : Mem) (out0 : Array String) (c : Vsa.Machine.Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧ c.σ.mem = m ∧ c.σ.sailOutput = out0 ∧
  c.σ.regs.get? Register.PC = some (0x80002d5c#64 : BitVec 64) ∧
  (∃ mi, c.σ.regs.get? Register.minstret = some mi) ∧
  GHolds c.σ (envSetHitStoresLiveL (envSetHitDst pv idx) w0 w1 w2 sp)

/-- Repackage the concrete scan hit into the exact reflected load-prefix pre.
The only extra input is that prefix's byte/decode geometry. -/
theorem setHitAt_to_hitLoad_pre
    {env valuePtr sp : BitVec 64} {idx : Nat} {f : Vsa.While.Frame}
    {nameStr : String} {m : Mem} {c : Vsa.Machine.Config}
    (pv w0 w1 w2 : BitVec 64) (out0 : Array String)
    (hHit : EnvSetScan.SetHitAt env valuePtr sp idx f nameStr m c)
    (hout : c.σ.sailOutput = out0)
    (hFacts : ChainFacts c.σ.mem c.σ.mem
      (envSetHitLoadLiveL env valuePtr (BitVec.ofNat 64 idx) sp)
      (envSetHitLds pv w0 w1 w2) envSetHitLoadSeg) :
    SegPreO envSetHitLoadSeg
      (envSetHitLoadLiveL env valuePtr (BitVec.ofNat 64 idx) sp)
      (envSetHitLds pv w0 w1 w2) 0x80002d3c#64 m out0 c := by
  have hk : KeysOK
      (keysG (envSetHitLoadLiveL env valuePtr (BitVec.ofNat 64 idx) sp)) := by
    show KeysOK [20, 21, 8, 2]
    decide
  refine ⟨⟨hHit.good, hHit.mem, hHit.pc, hHit.minstret, ?_, hk, hFacts, hHit.tick⟩, hout⟩
  exact ⟨hHit.env4, hHit.out5, hHit.idx0, hHit.sp2, trivial⟩

theorem env_set_hit_load_row
    (env valuePtr idx pv w0 w1 w2 sp : BitVec 64) (m : Mem) (out0 : Array String) :
    Vsa.Logic.Triple
      (SegPreO envSetHitLoadSeg (envSetHitLoadLiveL env valuePtr idx sp)
        (envSetHitLds pv w0 w1 w2) 0x80002d3c#64 m out0)
      (EnvSetHitLoadPost pv idx w0 w1 w2 sp m out0) := by
  apply segToTripleOut envSetHitLoadSeg (envSetHitLoadLiveL env valuePtr idx sp)
    (envSetHitLds pv w0 w1 w2) 0x80002d3c#64 m out0 _
    (by show ChainOK 0x80002d3c#64 [20, 21, 8, 2] envSetHitLoadSeg; decide)
  intro σ' i' u' hg ht hm ho hp hmi hr
  refine ⟨hg, ht, by simpa using hm, ho, by simpa using hp, hmi, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · rw [← envSetWordBytes_val pv]; exact gholds_lookup (n := 15) _ hr (by rfl)
  · exact gholds_lookup (n := 8) _ hr (by rfl)
  · exact gholds_lookup (n := 14) _ hr (by rfl)
  · rw [← envSetWordBytes_val w0]; exact gholds_lookup (n := 11) _ hr (by rfl)
  · rw [← envSetWordBytes_val w1]; exact gholds_lookup (n := 12) _ hr (by rfl)
  · rw [← envSetWordBytes_val w2]; exact gholds_lookup (n := 13) _ hr (by rfl)
  · exact gholds_lookup (n := 2) _ hr (by rfl)

theorem env_set_hit_calc_row (pv idx w0 w1 w2 sp : BitVec 64)
    (m : Mem) (out0 : Array String) :
    Vsa.Logic.Triple
      (SegPreO envSetHitCalcSeg (envSetHitCalcLiveL pv idx w0 w1 w2 sp) []
        0x80002d50#64 m out0)
      (EnvSetHitCalcPost pv idx w0 w1 w2 sp m out0) := by
  apply segToTripleOut envSetHitCalcSeg (envSetHitCalcLiveL pv idx w0 w1 w2 sp) []
    0x80002d50#64 m out0 _
    (by show ChainOK 0x80002d50#64 [15, 8, 14, 11, 12, 13, 2] envSetHitCalcSeg; decide)
  intro σ' i' u' hg ht hm ho hp hmi hr
  refine ⟨hg, ht, by simpa using hm, ho, by simpa using hp, hmi, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact gholds_lookup (n := 15) _ hr (by rfl)
  · exact gholds_lookup (n := 11) _ hr (by rfl)
  · exact gholds_lookup (n := 12) _ hr (by rfl)
  · exact gholds_lookup (n := 13) _ hr (by rfl)
  · exact gholds_lookup (n := 2) _ hr (by rfl)

/-- The exact memory produced by the three adjacent value-word stores. -/
def EnvSetValueTower (m : Mem) (slot : Nat)
    (b0 b1 b2 : List (BitVec 8)) : Mem :=
  writeMap8 (writeMap8 (writeMap8 m slot
    (sdData_val (bytesVal .ld b0))) (slot + 8)
    (sdData_val (bytesVal .ld b1))) (slot + 16)
    (sdData_val (bytesVal .ld b2))

/-- The reflected three-instruction suffix is exactly `EnvSetValueTower`.
Only the ordinary 64-bit address no-wrap premise is needed to turn its second
and third effective addresses into `slot+8` and `slot+16`. -/
theorem envSetHitStore0_mem (m : Mem) (dst w0 w1 w2 sp : BitVec 64) :
    writeLog m (evalBlocks envSetHitStore0Seg
      (SegEvalState.init (envSetHitStoresLiveL dst w0 w1 w2 sp) [])).log =
    writeMap8 m (dst + Functions.sign_extend (m := 64) (0x000#12)).toNat
      (sdData_val w0) := rfl

theorem envSetHitStore1_mem (m : Mem) (dst w0 w1 w2 sp : BitVec 64) :
    writeLog m (evalBlocks envSetHitStore1Seg
      (SegEvalState.init (envSetHitStoresLiveL dst w0 w1 w2 sp) [])).log =
    writeMap8 m (dst + Functions.sign_extend (m := 64) (0x008#12)).toNat
      (sdData_val w1) := rfl

theorem envSetHitStore2_mem (m : Mem) (dst w0 w1 w2 sp : BitVec 64) :
    writeLog m (evalBlocks envSetHitStore2Seg
      (SegEvalState.init (envSetHitStoresLiveL dst w0 w1 w2 sp) [])).log =
    writeMap8 m (dst + Functions.sign_extend (m := 64) (0x010#12)).toNat
      (sdData_val w2) := rfl

def EnvSetHitStorePost (dst w0 w1 w2 sp pc : BitVec 64)
    (m : Mem) (out0 : Array String) (c : Vsa.Machine.Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧ c.σ.mem = m ∧ c.σ.sailOutput = out0 ∧
  c.σ.regs.get? Register.PC = some pc ∧
  (∃ mi, c.σ.regs.get? Register.minstret = some mi) ∧
  GHolds c.σ (envSetHitStoresLiveL dst w0 w1 w2 sp)

theorem env_set_hit_store0_row (dst w0 w1 w2 sp : BitVec 64)
    (m : Mem) (out0 : Array String) :
    Vsa.Logic.Triple
      (SegPreO envSetHitStore0Seg (envSetHitStoresLiveL dst w0 w1 w2 sp) []
        0x80002d5c#64 m out0)
      (EnvSetHitStorePost dst w0 w1 w2 sp 0x80002d60#64
        (writeMap8 m (dst + Functions.sign_extend (m := 64) (0x000#12)).toNat
          (sdData_val w0)) out0) := by
  apply segToTripleOut envSetHitStore0Seg (envSetHitStoresLiveL dst w0 w1 w2 sp) []
    0x80002d5c#64 m out0 _
    (by show ChainOK 0x80002d5c#64 [15, 11, 12, 13, 2] envSetHitStore0Seg; decide)
  intro σ' i' u' hg ht hm ho hp hmi hr
  refine ⟨hg, ht, hm.trans (envSetHitStore0_mem m dst w0 w1 w2 sp), ho,
    by simpa using hp, hmi, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
    exact gholds_lookup _ hr (by rfl)

theorem env_set_hit_store1_row (dst w0 w1 w2 sp : BitVec 64)
    (m : Mem) (out0 : Array String) :
    Vsa.Logic.Triple
      (SegPreO envSetHitStore1Seg (envSetHitStoresLiveL dst w0 w1 w2 sp) []
        0x80002d60#64 m out0)
      (EnvSetHitStorePost dst w0 w1 w2 sp 0x80002d64#64
        (writeMap8 m (dst + Functions.sign_extend (m := 64) (0x008#12)).toNat
          (sdData_val w1)) out0) := by
  apply segToTripleOut envSetHitStore1Seg (envSetHitStoresLiveL dst w0 w1 w2 sp) []
    0x80002d60#64 m out0 _
    (by show ChainOK 0x80002d60#64 [15, 11, 12, 13, 2] envSetHitStore1Seg; decide)
  intro σ' i' u' hg ht hm ho hp hmi hr
  refine ⟨hg, ht, hm.trans (envSetHitStore1_mem m dst w0 w1 w2 sp), ho,
    by simpa using hp, hmi, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
    exact gholds_lookup _ hr (by rfl)

theorem env_set_hit_store2_row (dst w0 w1 w2 sp : BitVec 64)
    (m : Mem) (out0 : Array String) :
    Vsa.Logic.Triple
      (SegPreO envSetHitStore2Seg (envSetHitStoresLiveL dst w0 w1 w2 sp) []
        0x80002d64#64 m out0)
      (EnvSetHitStorePost dst w0 w1 w2 sp 0x80002d68#64
        (writeMap8 m (dst + Functions.sign_extend (m := 64) (0x010#12)).toNat
          (sdData_val w2)) out0) := by
  apply segToTripleOut envSetHitStore2Seg (envSetHitStoresLiveL dst w0 w1 w2 sp) []
    0x80002d64#64 m out0 _
    (by show ChainOK 0x80002d64#64 [15, 11, 12, 13, 2] envSetHitStore2Seg; decide)
  intro σ' i' u' hg ht hm ho hp hmi hr
  refine ⟨hg, ht, hm.trans (envSetHitStore2_mem m dst w0 w1 w2 sp), ho,
    by simpa using hp, hmi, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
    exact gholds_lookup _ hr (by rfl)

def envSetHitMem1 (m : Mem) (dst w0 : BitVec 64) : Mem :=
  writeMap8 m (dst + Functions.sign_extend (m := 64) (0x000#12)).toNat
    (sdData_val w0)

def envSetHitMem2 (m : Mem) (dst w0 w1 : BitVec 64) : Mem :=
  writeMap8 (envSetHitMem1 m dst w0)
    (dst + Functions.sign_extend (m := 64) (0x008#12)).toNat (sdData_val w1)

def envSetHitMem3 (m : Mem) (dst w0 w1 w2 : BitVec 64) : Mem :=
  writeMap8 (envSetHitMem2 m dst w0 w1)
    (dst + Functions.sign_extend (m := 64) (0x010#12)).toNat (sdData_val w2)

/-- Exact `ChainFacts` needed to splice the reflected calculation and store
segments.  These are machine-side decode, load and store-window facts, not a
semantic store-update oracle. -/
structure EnvSetHitSuffixFacts (m : Mem) (pv idx w0 w1 w2 sp : BitVec 64) : Prop where
  calcFacts : ChainFacts m m (envSetHitCalcLiveL pv idx w0 w1 w2 sp) [] envSetHitCalcSeg
  store0 : ChainFacts m m
    (envSetHitStoresLiveL (envSetHitDst pv idx) w0 w1 w2 sp) [] envSetHitStore0Seg
  store1 : ChainFacts
    (envSetHitMem1 m (envSetHitDst pv idx) w0)
    (envSetHitMem1 m (envSetHitDst pv idx) w0)
    (envSetHitStoresLiveL (envSetHitDst pv idx) w0 w1 w2 sp) [] envSetHitStore1Seg
  store2 : ChainFacts
    (envSetHitMem2 m (envSetHitDst pv idx) w0 w1)
    (envSetHitMem2 m (envSetHitDst pv idx) w0 w1)
    (envSetHitStoresLiveL (envSetHitDst pv idx) w0 w1 w2 sp) [] envSetHitStore2Seg

def EnvSetHitTowerPost (dst w0 w1 w2 sp : BitVec 64) (slot : Nat)
    (m : Mem) (out0 : Array String) (c : Vsa.Machine.Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.mem = EnvSetValueTower m slot
    (envSetWordBytes w0) (envSetWordBytes w1) (envSetWordBytes w2) ∧
  c.σ.sailOutput = out0 ∧
  c.σ.regs.get? Register.PC = some (0x80002d68#64 : BitVec 64) ∧
  (∃ mi, c.σ.regs.get? Register.minstret = some mi) ∧
  GHolds c.σ (envSetHitStoresLiveL dst w0 w1 w2 sp)

/-- The successful hit suffix, split into five reflected rows, produces exactly
the three-write `EnvSetValueTower`. -/
theorem env_set_hit_tower
    (env valuePtr idx pv w0 w1 w2 sp : BitVec 64) (slot : Nat)
    (m : Mem) (out0 : Array String)
    (hF : EnvSetHitSuffixFacts m pv idx w0 w1 w2 sp)
    (h0 : (envSetHitDst pv idx +
      Functions.sign_extend (m := 64) (0x000#12)).toNat = slot)
    (h8 : (envSetHitDst pv idx +
      Functions.sign_extend (m := 64) (0x008#12)).toNat = slot + 8)
    (h16 : (envSetHitDst pv idx +
      Functions.sign_extend (m := 64) (0x010#12)).toNat = slot + 16) :
    Vsa.Logic.Triple
      (SegPreO envSetHitLoadSeg (envSetHitLoadLiveL env valuePtr idx sp)
        (envSetHitLds pv w0 w1 w2) 0x80002d3c#64 m out0)
      (EnvSetHitTowerPost (envSetHitDst pv idx) w0 w1 w2 sp slot m out0) := by
  have hkCalc : KeysOK (keysG (envSetHitCalcLiveL pv idx w0 w1 w2 sp)) := by
    show KeysOK [15, 8, 14, 11, 12, 13, 2]
    decide
  have hkStores : KeysOK
      (keysG (envSetHitStoresLiveL (envSetHitDst pv idx) w0 w1 w2 sp)) := by
    show KeysOK [15, 11, 12, 13, 2]
    decide
  refine Vsa.Logic.Triple.seq
    (env_set_hit_load_row env valuePtr idx pv w0 w1 w2 sp m out0) ?_
  refine Vsa.Logic.Triple.seq
    (Vsa.Logic.Triple.lmap ?_ (env_set_hit_calc_row pv idx w0 w1 w2 sp m out0)) ?_
  · intro c hc
    rcases hc with ⟨hg, ht, hm, ho, hp, hmi, hr⟩
    exact ⟨⟨hg, hm, hp, hmi, hr, hkCalc,
      by simpa [hm] using hF.calcFacts, ht⟩, ho⟩
  refine Vsa.Logic.Triple.seq
    (Vsa.Logic.Triple.lmap ?_
      (env_set_hit_store0_row (envSetHitDst pv idx) w0 w1 w2 sp m out0)) ?_
  · intro c hc
    rcases hc with ⟨hg, ht, hm, ho, hp, hmi, hr⟩
    exact ⟨⟨hg, hm, hp, hmi, hr, hkStores,
      by simpa [hm] using hF.store0, ht⟩, ho⟩
  refine Vsa.Logic.Triple.seq
    (Vsa.Logic.Triple.lmap ?_
      (env_set_hit_store1_row (envSetHitDst pv idx) w0 w1 w2 sp
        (envSetHitMem1 m (envSetHitDst pv idx) w0) out0)) ?_
  · intro c hc
    rcases hc with ⟨hg, ht, hm, ho, hp, hmi, hr⟩
    have hm1 : c.σ.mem = envSetHitMem1 m (envSetHitDst pv idx) w0 := by
      simpa [envSetHitMem1] using hm
    exact ⟨⟨hg, hm1, hp, hmi, hr, hkStores,
      by simpa [hm1] using hF.store1, ht⟩, ho⟩
  refine Vsa.Logic.Triple.rmap ?_
    (Vsa.Logic.Triple.lmap ?_
      (env_set_hit_store2_row (envSetHitDst pv idx) w0 w1 w2 sp
        (envSetHitMem2 m (envSetHitDst pv idx) w0 w1) out0))
  · intro c hc
    rcases hc with ⟨hg, ht, hm, ho, hp, hmi, hr⟩
    refine ⟨hg, ht, ?_, ho, hp, hmi, hr⟩
    rw [hm]
    unfold envSetHitMem2 envSetHitMem1 EnvSetValueTower
    rw [h0, h8, h16]
    simp only [envSetWordBytes_val]
  · intro c hc
    rcases hc with ⟨hg, ht, hm, ho, hp, hmi, hr⟩
    have hm2 : c.σ.mem = envSetHitMem2 m (envSetHitDst pv idx) w0 w1 := by
      simpa [envSetHitMem2] using hm
    exact ⟨⟨hg, hm2, hp, hmi, hr, hkStores,
      by simpa [hm2] using hF.store2, ht⟩, ho⟩

/-- The three stores change no byte outside the 24-byte target slot. -/
theorem envSetValueTower_outside (m : Mem) (slot a : Nat)
    (b0 b1 b2 : List (BitVec 8)) (ha : OutsideSetSlot slot a) :
    (EnvSetValueTower m slot b0 b1 b2)[a]? = m[a]? := by
  unfold EnvSetValueTower
  unfold OutsideSetSlot at ha
  rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
      getElem_writeMap8_disjoint _ _ _ _ (by omega),
      getElem_writeMap8_disjoint _ _ _ _ (by omega)]

/-- The three adjacent stored words reproduce the 24 total-read source bytes. -/
theorem envSetValueTower_copy (m : Mem) (src slot : Nat)
    (b0 b1 b2 : List (BitVec 8))
    (h0 : LPins8 m src b0) (h1 : LPins8 m (src + 8) b1)
    (h2 : LPins8 m (src + 16) b2) :
    ∀ j, j < 24 →
      (EnvSetValueTower m slot b0 b1 b2)[slot + j]? =
        some ((m[src + j]?).getD 0) := by
  intro j hj
  unfold EnvSetValueTower
  by_cases hj0 : j < 8
  · rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        writeMap8_ld_byte _ slot b0 j hj0]
    exact congrArg some (lpins8_byte m src b0 h0 j hj0).symm
  · by_cases hj1 : j < 16
    · have hk : j - 8 < 8 := by omega
      rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]
      rw [show slot + j = slot + 8 + (j - 8) by omega,
          writeMap8_ld_byte _ (slot + 8) b1 (j - 8) hk,
          show src + j = src + 8 + (j - 8) by omega]
      exact congrArg some (lpins8_byte m (src + 8) b1 h1 (j - 8) hk).symm
    · have hk : j - 16 < 8 := by omega
      rw [show slot + j = slot + 16 + (j - 16) by omega,
          writeMap8_ld_byte _ (slot + 16) b2 (j - 16) hk,
          show src + j = src + 16 + (j - 16) by omega]
      exact congrArg some (lpins8_byte m (src + 16) b2 h2 (j - 16) hk).symm

/-- Exact byte agreement outside the target slot. -/
theorem envSetValueTower_agree (m : Mem) (slot : Nat)
    (b0 b1 b2 : List (BitVec 8)) :
    AgreeP (OutsideSetSlot slot) m (EnvSetValueTower m slot b0 b1 b2) :=
  fun a ha => (envSetValueTower_outside m slot a b0 b1 b2 ha).symm

/-- The exact three-store tower copies a represented source `Value` into the
target slot.  String payloads must be outside the overwritten header. -/
theorem envSetValueTower_valueRepr
    (m : Mem) (src slot : Nat) (b0 b1 b2 : List (BitVec 8))
    (N : NativeAddrs) (φc : Addr → Nat) (v : Value)
    (h0 : LPins8 m src b0) (h1 : LPins8 m (src + 8) b1)
    (h2 : LPins8 m (src + 16) b2)
    (hpayload : ∀ (p : Nat) (s : String), read64 m (src + 8) = some p →
      ∀ k, k ≤ s.length → OutsideSetSlot slot (p + k))
    (hv : ValueRepr m N φc src v) :
    ValueRepr (EnvSetValueTower m slot b0 b1 b2) N φc slot v := by
  apply valueRepr_copy_total_of_writeWindow
    (envSetValueTower_copy m src slot b0 b1 b2 h0 h1 h2)
    (envSetValueTower_outside m slot · b0 b1 b2)
    hpayload hv

/-- Reconstruct the represented semantic store from the exact hit-row output.
The semantic target decomposition and allocator separation remain explicit;
the post `StoreRepr` itself is derived. -/
theorem envSetHitTower_storeAdvance
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat}
    {store store' : Store} {start target : Addr} {x : String} {v : Value}
    {bridge : AssignStoreBridge store store' start x v}
    {frame : Vsa.While.Frame} {hit src slot : Nat}
    {dst w0 w1 w2 sp : BitVec 64} {m : Mem} {out0 : Array String}
    {c : Vsa.Machine.Config}
    (hc : EnvSetHitTowerPost dst w0 w1 w2 sp slot m out0 c)
    (hpre : StoreRepr m N A φf φc store)
    (hsemantic : ∃ (foundFrame : Vsa.While.Frame) (oldValue : Value)
        (beforeVars afterVars : List (String × Value)),
      store.frames[target]? = some foundFrame ∧
      foundFrame.vars = beforeVars ++ (x, oldValue) :: afterVars ∧
      foundFrame.vars.map (replaceBindingValue x v) =
        beforeVars ++ (x, v) :: afterVars ∧
      store' = { store with frames := store.frames.modify target fun current =>
        { current with vars := current.vars.map (replaceBindingValue x v) } })
    (hframe : store.frames[target]? = some frame)
    (hframeRepr : FrameRepr m N φf φc (φf target) frame)
    (hhit : hit < frame.vars.length) (hmatch : frame.vars[hit].1 = x)
    (huniq : FrameNamesUnique frame.vars)
    (hslot : ∀ pv, read64 m (φf target + 16) = some pv → slot = pv + 24 * hit)
    (hshell : TargetFrameOutsideSetSlot m N φf φc
      (φf target) slot frame hit)
    (hfoot : StoreSetFootprint m
      (EnvSetValueTower m slot (envSetWordBytes w0)
        (envSetWordBytes w1) (envSetWordBytes w2))
      N φf φc store target slot)
    (hld0 : LPins8 m src (envSetWordBytes w0))
    (hld1 : LPins8 m (src + 8) (envSetWordBytes w1))
    (hld2 : LPins8 m (src + 16) (envSetWordBytes w2))
    (hpayload : ∀ (p : Nat) (s : String), read64 m (src + 8) = some p →
      ∀ k, k ≤ s.length → OutsideSetSlot slot (p + k))
    (hvalue : ValueRepr m N φc src v) :
    StoreSetAdvance N A φf φc store store' start x v bridge target c.σ.mem := by
  rcases hc with ⟨_hg, _ht, hm, _ho, _hp, _hmi, _hr⟩
  rw [hm]
  apply StoreSetAdvance.of_target_repr hpre hfoot hsemantic
  intro foundFrame oldValue beforeVars afterVars hfound _hsplit _hupdate
  have hframeEq : foundFrame = frame := by
    rw [hfound] at hframe
    exact Option.some.inj hframe
  subst foundFrame
  apply hshell.rebuild (envSetValueTower_agree m slot
    (envSetWordBytes w0) (envSetWordBytes w1) (envSetWordBytes w2))
    hframeRepr hhit hmatch huniq hslot
  exact envSetValueTower_valueRepr m src slot
    (envSetWordBytes w0) (envSetWordBytes w1) (envSetWordBytes w2)
    N φc v hld0 hld1 hld2 hpayload hvalue

/-- The concrete epilogue preserves any predicate depending only on memory. -/
theorem env_set_return_frame_mem
    (sp ret r8 r9 r18 r19 r20 r21 : BitVec 64)
    (m : Mem) (out0 : Array String) (R : Mem → Prop)
    (hret : BitVec.update (ret + Functions.sign_extend (m := 64) (0x000#12))
      0 0#1 = ret) :
    Vsa.Logic.Triple
      (fun c => SegPreO envSetReturnSeg (envSetReturnL sp)
        (envSetReturnLds ret r8 r9 r18 r19 r20 r21)
        0x80002d68#64 m out0 c ∧ R c.σ.mem)
      (fun c => EnvSetReturnExactPost sp ret r8 r9 r18 r19 r20 r21 m out0 c ∧
        R c.σ.mem) := by
  intro c hc
  obtain ⟨hpre, hR⟩ := hc
  obtain ⟨c', hs, hpost⟩ :=
    env_set_return_exact sp ret r8 r9 r18 r19 r20 r21 m out0 hret c hpre
  refine ⟨c', hs, hpost, ?_⟩
  obtain ⟨⟨_, hmem, _, _, _, _, _, _⟩, _⟩ := hpre
  rw [hpost.mem, ← hmem]
  exact hR

/-- Hit-row execution, semantic store reconstruction, and the concrete
`env_set` epilogue composed through the actual updated memory. -/
theorem env_set_hit_return_advance
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat}
    {store store' : Store} {start target : Addr} {x : String} {v : Value}
    {bridge : AssignStoreBridge store store' start x v}
    (env valuePtr idx pv w0 w1 w2 sp : BitVec 64) (slot : Nat)
    (ret r8 r9 r18 r19 r20 r21 : BitVec 64) (m : Mem) (out0 : Array String)
    (hF : EnvSetHitSuffixFacts m pv idx w0 w1 w2 sp)
    (h0 : (envSetHitDst pv idx + Functions.sign_extend (m := 64) (0x000#12)).toNat = slot)
    (h8 : (envSetHitDst pv idx + Functions.sign_extend (m := 64) (0x008#12)).toNat = slot + 8)
    (h16 : (envSetHitDst pv idx + Functions.sign_extend (m := 64) (0x010#12)).toNat = slot + 16)
    (hReturnFacts : ChainFacts
      (EnvSetValueTower m slot (envSetWordBytes w0)
        (envSetWordBytes w1) (envSetWordBytes w2))
      (EnvSetValueTower m slot (envSetWordBytes w0)
        (envSetWordBytes w1) (envSetWordBytes w2))
      (envSetReturnL sp) (envSetReturnLds ret r8 r9 r18 r19 r20 r21)
      envSetReturnSeg)
    (hret : BitVec.update (ret + Functions.sign_extend (m := 64) (0x000#12))
      0 0#1 = ret)
    (hAdvance : ∀ c, EnvSetHitTowerPost (envSetHitDst pv idx) w0 w1 w2 sp
      slot m out0 c →
      StoreSetAdvance N A φf φc store store' start x v bridge target c.σ.mem) :
    Vsa.Logic.Triple
      (SegPreO envSetHitLoadSeg (envSetHitLoadLiveL env valuePtr idx sp)
        (envSetHitLds pv w0 w1 w2) 0x80002d3c#64 m out0)
      (fun c =>
        EnvSetReturnExactPost sp ret r8 r9 r18 r19 r20 r21
          (EnvSetValueTower m slot (envSetWordBytes w0)
            (envSetWordBytes w1) (envSetWordBytes w2)) out0 c ∧
        StoreSetAdvance N A φf φc store store' start x v bridge target c.σ.mem) := by
  let m' := EnvSetValueTower m slot (envSetWordBytes w0)
    (envSetWordBytes w1) (envSetWordBytes w2)
  have hHit := env_set_hit_tower env valuePtr idx pv w0 w1 w2 sp slot m out0
    hF h0 h8 h16
  have hHitAdvance : Vsa.Logic.Triple
      (SegPreO envSetHitLoadSeg (envSetHitLoadLiveL env valuePtr idx sp)
        (envSetHitLds pv w0 w1 w2) 0x80002d3c#64 m out0)
      (fun c => EnvSetHitTowerPost (envSetHitDst pv idx) w0 w1 w2 sp
        slot m out0 c ∧
        StoreSetAdvance N A φf φc store store' start x v bridge target c.σ.mem) :=
    Vsa.Logic.Triple.rmap (fun c hc => ⟨hc, hAdvance c hc⟩) hHit
  refine Vsa.Logic.Triple.seq hHitAdvance
    (Vsa.Logic.Triple.lmap ?_
      (env_set_return_frame_mem sp ret r8 r9 r18 r19 r20 r21 m' out0
        (fun mem => StoreSetAdvance N A φf φc store store' start x v bridge target mem)
        hret))
  intro c hc
  obtain ⟨⟨hg, ht, hm, ho, hp, hmi, hr⟩, hAdv⟩ := hc
  have hsp : GHolds c.σ (envSetReturnL sp) := by
    exact ⟨gholds_lookup (n := 2) _ hr (by rfl), trivial⟩
  have hk : KeysOK (keysG (envSetReturnL sp)) := by
    show KeysOK [2]
    decide
  have hrf : ChainFacts c.σ.mem c.σ.mem (envSetReturnL sp)
      (envSetReturnLds ret r8 r9 r18 r19 r20 r21) envSetReturnSeg := by
    rw [hm]
    simpa [m'] using hReturnFacts
  exact ⟨⟨⟨hg, hm, hp, hmi, hsp, hk, hrf, ht⟩, ho⟩,
    hAdv⟩

#print axioms envSetValueTower_outside
#print axioms env_set_hit_load_row
#print axioms env_set_hit_calc_row
#print axioms envSetHitStore0_mem
#print axioms envSetHitStore1_mem
#print axioms envSetHitStore2_mem
#print axioms envSetValueTower_copy
#print axioms envSetValueTower_agree
#print axioms envSetValueTower_valueRepr
#print axioms env_set_hit_tower
#print axioms envSetHitTower_storeAdvance
#print axioms env_set_return_frame_mem
#print axioms env_set_hit_return_advance

end Vsa.Sim
