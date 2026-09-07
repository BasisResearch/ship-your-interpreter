import Vsa.Sim.rows.EnvDefineScanLoop
import Vsa.Sim.EnvDefBridges4
import Vsa.Sim.SegFrameFacts
import Vsa.Sim.ValueWordRepr
import Vsa.Sim.ReprCopy
import Vsa.Sim.EqNeReprReadback
import Vsa.Sim.SegToTripleFramed
import Vsa.Sim.rows.EnvDefineEpilogue
import Vsa.Sim.StoreSetFootprint

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.MemRepr
open Vsa.RuntimeRepr
open Vsa.Logic (Triple)

namespace Vsa.Sim

@[simp] private theorem updLine0 : mkLine 0x80002ac0#64 0x010a3783#32 =
    ⟨0x80002ac0#64, 0x010a3783#32, 0x83#8, 0x37#8, 0x0a#8, 0x01#8,
      .ld, 15, 20, 0, 0x010#12⟩ := by rfl
@[simp] private theorem updLine1 : mkLine 0x80002ac4#64 0x00141713#32 =
    ⟨0x80002ac4#64, 0x00141713#32, 0x13#8, 0x17#8, 0x14#8, 0x00#8,
      .slli, 14, 8, 0, 0x001#12⟩ := by rfl
@[simp] private theorem updLine2 : mkLine 0x80002ac8#64 0x000ab583#32 =
    ⟨0x80002ac8#64, 0x000ab583#32, 0x83#8, 0xb5#8, 0x0a#8, 0x00#8,
      .ld, 11, 21, 0, 0x000#12⟩ := by rfl
@[simp] private theorem updLine3 : mkLine 0x80002acc#64 0x008ab603#32 =
    ⟨0x80002acc#64, 0x008ab603#32, 0x03#8, 0xb6#8, 0x8a#8, 0x00#8,
      .ld, 12, 21, 0, 0x008#12⟩ := by rfl
@[simp] private theorem updLine4 : mkLine 0x80002ad0#64 0x010ab683#32 =
    ⟨0x80002ad0#64, 0x010ab683#32, 0x83#8, 0xb6#8, 0x0a#8, 0x01#8,
      .ld, 13, 21, 0, 0x010#12⟩ := by rfl
@[simp] private theorem updLine5 : mkLine 0x80002ad4#64 0x00870733#32 =
    ⟨0x80002ad4#64, 0x00870733#32, 0x33#8, 0x07#8, 0x87#8, 0x00#8,
      .add, 14, 14, 8, 0x000#12⟩ := by rfl
@[simp] private theorem updLine6 : mkLine 0x80002ad8#64 0x00371713#32 =
    ⟨0x80002ad8#64, 0x00371713#32, 0x13#8, 0x17#8, 0x37#8, 0x00#8,
      .slli, 14, 14, 0, 0x003#12⟩ := by rfl
@[simp] private theorem updLine7 : mkLine 0x80002adc#64 0x00e787b3#32 =
    ⟨0x80002adc#64, 0x00e787b3#32, 0xb3#8, 0x87#8, 0xe7#8, 0x00#8,
      .add, 15, 15, 14, 0x000#12⟩ := by rfl
@[simp] private theorem updLine8 : mkLine 0x80002ae0#64 0x00b7b023#32 =
    ⟨0x80002ae0#64, 0x00b7b023#32, 0x23#8, 0xb0#8, 0xb7#8, 0x00#8,
      .sd, 0, 15, 11, 0x000#12⟩ := by rfl
@[simp] private theorem updLine9 : mkLine 0x80002ae4#64 0x00c7b423#32 =
    ⟨0x80002ae4#64, 0x00c7b423#32, 0x23#8, 0xb4#8, 0xc7#8, 0x00#8,
      .sd, 0, 15, 12, 0x008#12⟩ := by rfl
@[simp] private theorem updLine10 : mkLine 0x80002ae8#64 0x00d7b823#32 =
    ⟨0x80002ae8#64, 0x00d7b823#32, 0x23#8, 0xb8#8, 0xd7#8, 0x00#8,
      .sd, 0, 15, 13, 0x010#12⟩ := by rfl

/-- Update block with the live reflected registers and tick retained. -/
def UpdateStoreLivePost (env src idx : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks updateStoreSeg
    (SegEvalState.init (updateStoreL env src idx) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x80002aec#64 ∧
  GHolds c.σ (evalBlocks updateStoreSeg
    (SegEvalState.init (updateStoreL env src idx) lds)).regs ∧
  c.tick < 2

theorem updateStoreLiveRow (env src idx : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) :
    Triple
      (SegPre updateStoreSeg (updateStoreL env src idx) lds 0x80002ac0#64 m0)
      (UpdateStoreLivePost env src idx lds m0) := by
  apply segToTriple updateStoreSeg (updateStoreL env src idx) lds 0x80002ac0#64 m0 _
    (by show ChainOK 0x80002ac0#64 [20, 21, 8] updateStoreSeg; decide)
  intro σ' i' u' hG' hi' hmem' hpc' _ hregs'
  refine ⟨hG', hmem', ?_, hregs', hi'⟩
  rw [hpc']; rfl

/-- Framed update row retaining the helper stack pointer for the epilogue. -/
theorem updateStoreLiveRowSp (env src idx sp : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) :
    Triple
      (fun c =>
        SegPre updateStoreSeg (updateStoreL env src idx) lds 0x80002ac0#64 m0 c ∧
        c.σ.regs.get? Register.x2 = some sp)
      (fun c => UpdateStoreLivePost env src idx lds m0 c ∧
        c.σ.regs.get? Register.x2 = some sp) := by
  intro c ⟨hpre, hsp⟩
  obtain ⟨hG, hmem, hpc, ⟨vm, hmi⟩, hL, hkeys, hfacts, htick⟩ := hpre
  obtain ⟨σ', i', hs, hi', hG', hmem', _hout, hpc', _hmi', hregs', hframe⟩ :=
    segEval_sound updateStoreSeg c.σ c.tick c.steps 0x80002ac0#64 vm
      (updateStoreL env src idx) lds hG hpc hmi hL hkeys hfacts
      (by show ChainOK 0x80002ac0#64 [20, 21, 8] updateStoreSeg; decide) htick
  rw [hmem] at hmem'
  refine ⟨⟨σ', i', c.steps + evalBlocksFuel updateStoreSeg⟩, hs,
    ⟨⟨hG', hmem', ?_, hregs', hi'⟩, ?_⟩⟩
  · rw [hpc']; rfl
  · exact (hframe Register.x2 (by decide) (by
      intro n hn
      simp [updateStoreSeg, wrChain, wrRegsM] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).trans hsp

/-- Honest address geometry used by the four loads and three stores of the
update block. Source and destination are separate addresses. -/
structure EnvDefineUpdateGeom
    (env src vals dst : BitVec 64) (idx : Nat) (m : Mem) : Prop where
  valsRead : read64 m (env.toNat + 16) = some vals.toNat
  envLo : 0x80000000 ≤ env.toNat + 16
  envHi : env.toNat + 24 ≤ 0x100000000
  envHtif : env.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 8 ≤ env.toNat + 16
  envAlign : (env.toNat + 16) % 8 = 0
  srcLo : 0x80000000 ≤ src.toNat
  srcHi : src.toNat + 24 ≤ 0x100000000
  srcHtif : src.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 8 ≤ src.toNat
  srcAlign : src.toNat % 8 = 0
  dstEq : dst.toNat = vals.toNat + 24 * idx
  idx3 : (BitVec.ofNat 64 idx <<< 1) + BitVec.ofNat 64 idx = BitVec.ofNat 64 (3 * idx)
  idx24 : BitVec.ofNat 64 (3 * idx) <<< 3 = BitVec.ofNat 64 (24 * idx)
  strideCalc :
    shift_bits_left
        (shift_bits_left (BitVec.ofNat 64 idx)
          (Sail.BitVec.extractLsb (1#6) 5 0) + BitVec.ofNat 64 idx)
        (Sail.BitVec.extractLsb (3#6) 5 0) =
      BitVec.ofNat 64 (24 * idx)
  addrCalc : vals + BitVec.ofNat 64 (24 * idx) = dst
  dstLo : 0x80000000 ≤ dst.toNat
  dstHi : dst.toNat + 24 ≤ 0x100000000
  dstHtif : tohostAddr + 16 ≤ dst.toNat
  dstAlign : dst.toNat % 8 = 0

/-- Exact load bytes consumed by `updateStoreSeg`. -/
def updateStoreLds
    (vb0 vb1 vb2 vb3 vb4 vb5 vb6 vb7
     s00 s01 s02 s03 s04 s05 s06 s07
     s10 s11 s12 s13 s14 s15 s16 s17
     s20 s21 s22 s23 s24 s25 s26 s27 : BitVec 8) : List (List (BitVec 8)) :=
  [[vb0, vb1, vb2, vb3, vb4, vb5, vb6, vb7],
   [s00, s01, s02, s03, s04, s05, s06, s07],
   [s10, s11, s12, s13, s14, s15, s16, s17],
   [s20, s21, s22, s23, s24, s25, s26, s27]]

private theorem updateMemFactsLd
    {m : Mem} {L : GRegs} {a : MInstr} {bs : List (BitVec 8)}
    (base : Nat) (hk : a.kind = .ld) (hea : (eaddrM a L).toNat = base)
    (hlo : 0x80000000 ≤ base) (hhi : base + 8 ≤ 0x100000000)
    (hht : base + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ base)
    (hal : base % 8 = 0) (hp : LPins8 m base bs) : MemFacts m L bs a := by
  unfold MemFacts
  rw [hk, hea]
  exact ⟨⟨hlo, hhi, hht⟩, hp⟩

private theorem updateMemFactsSd
    {m : Mem} {L : GRegs} {a : MInstr} {bs : List (BitVec 8)}
    (base : Nat) (hk : a.kind = .sd) (hea : (eaddrM a L).toNat = base)
    (hlo : 0x80000000 ≤ base) (hhi : base + 8 ≤ 0x100000000)
    (hht : tohostAddr + 16 ≤ base) (hal : base % 8 = 0) :
    MemFacts m L bs a := by
  unfold MemFacts
  rw [hk, hea]
  exact ⟨hlo, hhi, hht, hal⟩

/-- All data bytes and machine-side facts for the exact update block. -/
theorem updateStoreFacts
    (env src vals dst : BitVec 64) (idx : Nat) (m : Mem)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (v : Vsa.While.Value)
    (hcode : Vsa.Sim.Code.Env_defineLoaded m)
    (hword : ValueWordRepr m N φc src.toNat v)
    (hgeom : EnvDefineUpdateGeom env src vals dst idx m) :
    ∃ lds,
      ChainFacts m m (updateStoreL env src (BitVec.ofNat 64 idx)) lds
        updateStoreSeg ∧
      bytesVal .ld (lds.getD 0 []) = vals ∧
      ∃ d0 d1 d2 : BitVec 64,
        read64 m src.toNat = some d0.toNat ∧
        read64 m (src.toNat + 8) = some d1.toNat ∧
        read64 m (src.toNat + 16) = some d2.toNat ∧
        bytesVal .ld (lds.getD 1 []) = d0 ∧
        bytesVal .ld (lds.getD 2 []) = d1 ∧
        bytesVal .ld (lds.getD 3 []) = d2 ∧
        LPins8 m src.toNat (lds.getD 1 []) ∧
        LPins8 m (src.toNat + 8) (lds.getD 2 []) ∧
        LPins8 m (src.toNat + 16) (lds.getD 3 []) := by
  obtain ⟨_, d0, d1, d2, h0, h1, h2⟩ := hword
  obtain ⟨v0,v1,v2,v3,v4,v5,v6,v7,hv0,hv1,hv2,hv3,hv4,hv5,hv6,hv7,_⟩ :=
    read64_bytes_eg4 m (env.toNat + 16) vals.toNat hgeom.valsRead
  have hvals : sign_extend (m := 64)
      ((((((((v7.append v6).append v5).append v4).append v3).append v2).append v1).append v0)
        : BitVec (8 * 8)) = vals :=
    by
      have h := ld_value_eq_read64 m (env.toNat + 16) vals.toNat
        v0 v1 v2 v3 v4 v5 v6 v7 hgeom.valsRead hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7
      simpa using h
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,_⟩ :=
    read64_bytes_eg4 m src.toNat d0.toNat h0
  obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,hb0,hb1,hb2,hb3,hb4,hb5,hb6,hb7,_⟩ :=
    read64_bytes_eg4 m (src.toNat + 8) d1.toNat h1
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,c7,hc0,hc1,hc2,hc3,hc4,hc5,hc6,hc7,_⟩ :=
    read64_bytes_eg4 m (src.toNat + 16) d2.toNat h2
  let lds := updateStoreLds v0 v1 v2 v3 v4 v5 v6 v7 a0 a1 a2 a3 a4 a5 a6 a7
    b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7
  have hpv : LPins8 m (env.toNat + 16) [v0,v1,v2,v3,v4,v5,v6,v7] :=
    ⟨lpin_of_present hv0, lpin_of_present hv1, lpin_of_present hv2,
      lpin_of_present hv3, lpin_of_present hv4, lpin_of_present hv5,
      lpin_of_present hv6, lpin_of_present hv7⟩
  have hpa : LPins8 m src.toNat [a0,a1,a2,a3,a4,a5,a6,a7] :=
    ⟨lpin_of_present ha0, lpin_of_present ha1, lpin_of_present ha2,
      lpin_of_present ha3, lpin_of_present ha4, lpin_of_present ha5,
      lpin_of_present ha6, lpin_of_present ha7⟩
  have hpb : LPins8 m (src.toNat + 8) [b0,b1,b2,b3,b4,b5,b6,b7] :=
    ⟨lpin_of_present hb0, lpin_of_present hb1, lpin_of_present hb2,
      lpin_of_present hb3, lpin_of_present hb4, lpin_of_present hb5,
      lpin_of_present hb6, lpin_of_present hb7⟩
  have hpc : LPins8 m (src.toNat + 16) [c0,c1,c2,c3,c4,c5,c6,c7] :=
    ⟨lpin_of_present hc0, lpin_of_present hc1, lpin_of_present hc2,
      lpin_of_present hc3, lpin_of_present hc4, lpin_of_present hc5,
      lpin_of_present hc6, lpin_of_present hc7⟩
  have henvHi := hgeom.envHi
  have hsrcLo := hgeom.srcLo
  have hsrcHi := hgeom.srcHi
  have hsrcAlign := hgeom.srcAlign
  have hdstLo := hgeom.dstLo
  have hdstHi := hgeom.dstHi
  have hdstHtif := hgeom.dstHtif
  have hdstAlign := hgeom.dstAlign
  have hvalsNat := congrArg BitVec.toNat hvals
  have hvalsNat' :
      (sign_extend (m := 64)
        (v7 +++ v6 +++ v5 +++ v4 +++ v3 +++ v2 +++ v1 +++ v0)).toNat =
        vals.toNat := by
    simpa using hvalsNat
  have hbase : vals +
      shift_bits_left
        (shift_bits_left (BitVec.ofNat 64 idx)
          (Sail.BitVec.extractLsb (1#6) 5 0) + BitVec.ofNat 64 idx)
        (Sail.BitVec.extractLsb (3#6) 5 0) = dst := by
    rw [hgeom.strideCalc]
    exact hgeom.addrCalc
  have hbaseNat := congrArg BitVec.toNat hbase
  refine ⟨lds, ?_⟩
  constructor
  · chain_facts hcode with "Vsa.Sim.Code.env_define_at_"
    · refine updateMemFactsLd (env.toNat + 16) (by rfl) ?_
        hgeom.envLo hgeom.envHi hgeom.envHtif hgeom.envAlign ?_
      · rw [updLine0]
        simp [eaddrM, updateStoreL, srcVal, lookupG]
        rw [show (sign_extend (m := 64) (0x010#12) : BitVec 64) = 16#64 by decide]
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by decide)]
      · simpa [lds, updateStoreLds] using hpv
    · refine updateMemFactsLd src.toNat (by rfl) ?_ hgeom.srcLo (by omega)
        (by rcases hgeom.srcHtif with h | h <;> omega) hgeom.srcAlign ?_
      · simp [eaddrM, updLine0, updLine1, stepMemM, stepGM, stepLdsM,
          updateStoreL, wvalM, bytesVal, srcVal, lookupG, eraseG, lds,
          updateStoreLds]
        rw [show (sign_extend (m := 64) (0#12) : BitVec 64).toNat = 0 by decide,
          Nat.add_zero, Nat.mod_eq_of_lt src.isLt]
      · simpa [lds, updateStoreLds] using hpa
    · refine updateMemFactsLd (src.toNat + 8) (by rfl) ?_ (by omega) (by omega)
        (by rcases hgeom.srcHtif with h | h <;> omega) (by omega) ?_
      · simp [eaddrM, updLine0, updLine1, updLine2, stepMemM, stepGM, stepLdsM,
          updateStoreL, wvalM, bytesVal, srcVal, lookupG, eraseG, lds,
          updateStoreLds]
        rw [show (sign_extend (m := 64) (0x008#12) : BitVec 64).toNat = 8 by decide,
          Nat.mod_eq_of_lt (by omega)]
      · simpa [lds, updateStoreLds] using hpb
    · refine updateMemFactsLd (src.toNat + 16) (by rfl) ?_ (by omega) (by omega)
        (by rcases hgeom.srcHtif with h | h <;> omega) (by omega) ?_
      · simp [eaddrM, updLine0, updLine1, updLine2, updLine3, stepMemM, stepGM,
          stepLdsM, updateStoreL, wvalM, bytesVal, srcVal, lookupG, eraseG, lds,
          updateStoreLds]
        rw [show (sign_extend (m := 64) (0x010#12) : BitVec 64).toNat = 16 by decide,
          Nat.mod_eq_of_lt (by omega)]
      · simpa [lds, updateStoreLds] using hpc
    · refine updateMemFactsSd dst.toNat (by rfl) ?_ hgeom.dstLo (by omega)
        hgeom.dstHtif hgeom.dstAlign
      simp [eaddrM, updLine0, updLine1, updLine2, updLine3, updLine4, updLine5,
        updLine6, updLine7, stepMemM, stepGM, stepLdsM, updateStoreL, wvalM,
        bytesVal, srcVal, lookupG, eraseG, lds, updateStoreLds, shamtOf]
      rw [hvalsNat']
      simpa [BitVec.toNat_add] using hbaseNat
    · refine updateMemFactsSd (dst.toNat + 8) (by rfl) ?_ (by omega) (by omega)
        (by omega) (by omega)
      simp [eaddrM, updLine0, updLine1, updLine2, updLine3, updLine4, updLine5,
        updLine6, updLine7, updLine8, stepMemM, stepGM, stepLdsM, updateStoreL,
        wvalM, bytesVal, srcVal, lookupG, eraseG, lds, updateStoreLds, shamtOf]
      rw [hvalsNat']
      have h := congrArg BitVec.toNat
        (congrArg (fun z : BitVec 64 => z + 8#64) hbase)
      rw [show (sign_extend (m := 64) (8#12) : BitVec 64).toNat = 8 by decide]
      have hdst8 : dst.toNat + 8 < 2^64 := by omega
      rw [← Nat.mod_eq_of_lt hdst8]
      simpa [BitVec.toNat_add] using h
    · refine updateMemFactsSd (dst.toNat + 16) (by rfl) ?_ (by omega) (by omega)
        (by omega) (by omega)
      simp [eaddrM, updLine0, updLine1, updLine2, updLine3, updLine4, updLine5,
        updLine6, updLine7, updLine8, updLine9, stepMemM, stepGM, stepLdsM,
        updateStoreL, wvalM, bytesVal, srcVal, lookupG, eraseG, lds,
        updateStoreLds, shamtOf]
      rw [hvalsNat']
      have h := congrArg BitVec.toNat
        (congrArg (fun z : BitVec 64 => z + 16#64) hbase)
      rw [show (sign_extend (m := 64) (16#12) : BitVec 64).toNat = 16 by decide]
      have hdst16 : dst.toNat + 16 < 2^64 := by omega
      rw [← Nat.mod_eq_of_lt hdst16]
      simpa [BitVec.toNat_add] using h
  · refine ⟨?_, d0, d1, d2, h0, h1, h2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [lds, updateStoreLds] using hvals
    · simpa [lds, updateStoreLds] using
      (ld_value_eq_read64 m src.toNat d0.toNat
        a0 a1 a2 a3 a4 a5 a6 a7 h0 ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7)
    · simpa [lds, updateStoreLds] using
      (ld_value_eq_read64 m (src.toNat + 8) d1.toNat
        b0 b1 b2 b3 b4 b5 b6 b7 h1 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7)
    · simpa [lds, updateStoreLds] using
      (ld_value_eq_read64 m (src.toNat + 16) d2.toNat
        c0 c1 c2 c3 c4 c5 c6 c7 h2 hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7)
    · simpa [lds, updateStoreLds] using hpa
    · simpa [lds, updateStoreLds] using hpb
    · simpa [lds, updateStoreLds] using hpc

/-- The reflected update log is exactly three adjacent value-word stores. -/
theorem updateStoreLog
    (env src vals dst : BitVec 64) (idx : Nat)
    (lds : List (List (BitVec 8))) (m : Mem)
    (hvals : bytesVal .ld (lds.getD 0 []) = vals)
    (hgeom : EnvDefineUpdateGeom env src vals dst idx m) :
    (evalBlocks updateStoreSeg
      (SegEvalState.init (updateStoreL env src (BitVec.ofNat 64 idx)) lds)).log =
      [(dst.toNat, 8, bytesVal .ld (lds.getD 1 [])),
       (dst.toNat + 8, 8, bytesVal .ld (lds.getD 2 [])),
       (dst.toNat + 16, 8, bytesVal .ld (lds.getD 3 []))] := by
  have hhead : lds.head?.getD [] = lds.getD 0 [] := by cases lds <;> rfl
  have hvalsHead : bytesVal .ld (lds.head?.getD []) = vals :=
    (congrArg (bytesVal .ld) hhead).trans hvals
  have hidxA :
      (lookupG 8 (eraseG 15
        (updateStoreL env src (BitVec.ofNat 64 idx)))).getD 0#64 =
        BitVec.ofNat 64 idx := by
    simp [updateStoreL, lookupG, eraseG]
  have hidxB :
      (lookupG 8 (eraseG 13 (eraseG 12 (eraseG 11 (eraseG 14 (eraseG 15
        (updateStoreL env src (BitVec.ofNat 64 idx)))))))).getD 0#64 =
        BitVec.ofNat 64 idx := by
    simp [updateStoreL, lookupG, eraseG]
  have hbaseNat := congrArg BitVec.toNat hgeom.addrCalc
  have hidx24lt : 24 * idx < 2^64 := by
    have heq := hgeom.dstEq
    have hhi := hgeom.dstHi
    omega
  simp [updateStoreSeg, evalBlocks, evalBlock, SegEvalState.init, wlogM,
    wentryM, widthOfM, runGM, stepGM, stepLdsM, ldsRunM, wvalM,
    srcVal, lookupG, eraseG, eaddrM, shamtOf]
  constructor
  · rw [congrArg BitVec.toNat hvalsHead, hidxA, hidxB, hgeom.strideCalc]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hidx24lt,
      show (sign_extend (m := 64) (0#12) : BitVec 64).toNat = 0 by decide,
      Nat.add_zero]
    simpa [BitVec.toNat_add] using hbaseNat
  constructor
  · rw [congrArg BitVec.toNat hvalsHead, hidxA, hidxB, hgeom.strideCalc]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hidx24lt]
    have h := congrArg BitVec.toNat
      (congrArg (fun z : BitVec 64 => z + 8#64) hgeom.addrCalc)
    rw [show (sign_extend (m := 64) (8#12) : BitVec 64).toNat = 8 by decide]
    have hdst8 : dst.toNat + 8 < 2^64 := by have := hgeom.dstHi; omega
    rw [← Nat.mod_eq_of_lt hdst8]
    simpa [BitVec.toNat_add] using h
  · rw [congrArg BitVec.toNat hvalsHead, hidxA, hidxB, hgeom.strideCalc]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hidx24lt]
    have h := congrArg BitVec.toNat
      (congrArg (fun z : BitVec 64 => z + 16#64) hgeom.addrCalc)
    rw [show (sign_extend (m := 64) (16#12) : BitVec 64).toNat = 16 by decide]
    have hdst16 : dst.toNat + 16 < 2^64 := by have := hgeom.dstHi; omega
    rw [← Nat.mod_eq_of_lt hdst16]
    simpa [BitVec.toNat_add] using h

/-- Rebuild the copied semantic value and its three total machine words. -/
def UpdateValueTower (m : Mem) (dst : Nat)
    (b0 b1 b2 : List (BitVec 8)) : Mem :=
  writeMap8 (writeMap8 (writeMap8 m dst
    (sdData_val (bytesVal .ld b0))) (dst + 8)
    (sdData_val (bytesVal .ld b1))) (dst + 16)
    (sdData_val (bytesVal .ld b2))

theorem updateValueTowerOutside (m : Mem) (dst a : Nat)
    (b0 b1 b2 : List (BitVec 8))
    (ha : a < dst ∨ dst + 24 ≤ a) :
    (UpdateValueTower m dst b0 b1 b2)[a]? = m[a]? := by
  unfold UpdateValueTower
  rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
      getElem_writeMap8_disjoint _ _ _ _ (by omega),
      getElem_writeMap8_disjoint _ _ _ _ (by omega)]

theorem updateValueTowerCopy (m : Mem) (src dst : Nat)
    (b0 b1 b2 : List (BitVec 8))
    (h0 : LPins8 m src b0) (h1 : LPins8 m (src + 8) b1)
    (h2 : LPins8 m (src + 16) b2) :
    ∀ j, j < 24 →
      (UpdateValueTower m dst b0 b1 b2)[dst + j]? =
        some ((m[src + j]?).getD 0) := by
  intro j hj
  unfold UpdateValueTower
  by_cases hj0 : j < 8
  · rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        writeMap8_ld_byte _ dst b0 j hj0]
    exact congrArg some (lpins8_byte m src b0 h0 j hj0).symm
  · by_cases hj1 : j < 16
    · have hk : j - 8 < 8 := by omega
      rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]
      rw [show dst + j = dst + 8 + (j - 8) by omega,
          writeMap8_ld_byte _ (dst + 8) b1 (j - 8) hk,
          show src + j = src + 8 + (j - 8) by omega]
      exact congrArg some (lpins8_byte m (src + 8) b1 h1 (j - 8) hk).symm
    · have hk : j - 16 < 8 := by omega
      rw [show dst + j = dst + 16 + (j - 16) by omega,
          writeMap8_ld_byte _ (dst + 16) b2 (j - 16) hk,
          show src + j = src + 16 + (j - 16) by omega]
      exact congrArg some (lpins8_byte m (src + 16) b2 h2 (j - 16) hk).symm

theorem updateStoreValueWordRepr
    (env src vals dst : BitVec 64) (idx : Nat)
    (lds : List (List (BitVec 8))) (m0 : Mem) (c : Config)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (v : Vsa.While.Value)
    (hpost : UpdateStoreLivePost env src (BitVec.ofNat 64 idx) lds m0 c)
    (hvals : bytesVal .ld (lds.getD 0 []) = vals)
    (hgeom : EnvDefineUpdateGeom env src vals dst idx m0)
    (hpin0 : LPins8 m0 src.toNat (lds.getD 1 []))
    (hpin1 : LPins8 m0 (src.toNat + 8) (lds.getD 2 []))
    (hpin2 : LPins8 m0 (src.toNat + 16) (lds.getD 3 []))
    (hpayload : ValuePayloadCovered
      (fun a => a < dst.toNat ∨ dst.toNat + 24 ≤ a) m0 src.toNat v)
    (hword : ValueWordRepr m0 N φc src.toNat v) :
    ValueWordRepr c.σ.mem N φc dst.toNat v := by
  have hmem : c.σ.mem = UpdateValueTower m0 dst.toNat
      (lds.getD 1 []) (lds.getD 2 []) (lds.getD 3 []) := by
    rw [hpost.2.1, updateStoreLog env src vals dst idx lds m0 hvals hgeom]
    rfl
  rw [hmem]
  exact valueWordRepr_copy_total_exact
    (updateValueTowerCopy m0 src.toNat dst.toNat
      (lds.getD 1 []) (lds.getD 2 []) (lds.getD 3 []) hpin0 hpin1 hpin2)
    (by
      cases v with
      | str s => exact fun p hp k hk =>
          (updateValueTowerOutside m0 dst.toNat (p + k)
            (lds.getD 1 []) (lds.getD 2 []) (lds.getD 3 [])
            (hpayload p hp k hk)).symm
      | native f => exact fun p hp k hk =>
          (updateValueTowerOutside m0 dst.toNat (p + k)
            (lds.getD 1 []) (lds.getD 2 []) (lds.getD 3 [])
            (hpayload p hp k hk)).symm
      | null | bool | int | closure => trivial)
    hword

/-- A scan hit parked at the exact update block entry. -/
def EnvDefineUpdateHitPre
    (saved : (R : Register) → Option (RegisterType R))
    (env name src count cursor sp : BitVec 64) (idx : Nat)
    (m0 : Mem) (c : Config) : Prop :=
  ∃ cmp,
    EnvDefineScanLivePost envDefineScanHitSeg 0x80002ac0#64
      cmp (BitVec.ofNat 64 idx) cursor count env name src sp [] m0 c ∧
    EnvDefineSavedSpillFrame sp saved c

/-- Exact update post with the copied value and outer spill image retained. -/
def EnvDefineUpdatePost
    (saved : (R : Register) → Option (RegisterType R))
    (env src dst sp : BitVec 64) (idx : Nat) (m0 : Mem)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat)
    (v : Vsa.While.Value) (c : Config) : Prop :=
  ∃ lds,
    UpdateStoreLivePost env src (BitVec.ofNat 64 idx) lds m0 c ∧
    ValueWordRepr c.σ.mem N φc dst.toNat v ∧
    EnvDefineSavedSpillFrame sp saved c ∧
    c.σ.regs.get? Register.x2 = some sp ∧
    c.σ.mem = UpdateValueTower m0 dst.toNat
      (lds.getD 1 []) (lds.getD 2 []) (lds.getD 3 [])

/-- The exact update write tower preserves every byte outside its value slot. -/
theorem EnvDefineUpdatePost.agree_outside
    {saved : (R : Register) → Option (RegisterType R)}
    {env src dst sp : BitVec 64} {idx : Nat} {m0 : Mem}
    {N : NativeAddrs} {φc : Vsa.While.Addr → Nat} {v : Vsa.While.Value} {c : Config}
    (h : EnvDefineUpdatePost saved env src dst sp idx m0 N φc v c) :
    AgreeP (SetOutside dst.toNat) m0 c.σ.mem := by
  obtain ⟨lds, _, _, _, _, hmem⟩ := h
  intro k hk
  rw [hmem]
  exact (updateValueTowerOutside m0 dst.toNat k
    (lds.getD 1 []) (lds.getD 2 []) (lds.getD 3 []) hk).symm

/-- Exact value-copy evidence retained at the update's epilogue entry. -/
structure EnvDefineCopiedUpdatePost
    (saved : (R : Register) → Option (RegisterType R))
    (env src dst sp : BitVec 64) (idx : Nat) (m0 : Mem)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (v : Vsa.While.Value) (c : Config) : Prop where
  update : EnvDefineUpdatePost saved env src dst sp idx m0 N φc v c
  copied : ∀ k, k < 24 →
    c.σ.mem[dst.toNat + k]? = some ((m0[src.toNat + k]?).getD 0)

/-- Compose a reflected scan hit with the exact three-word update block. -/
theorem envDefineUpdateFromHitCopied
    (saved : (R : Register) → Option (RegisterType R))
    (env name src count cursor sp vals dst : BitVec 64) (idx : Nat)
    (m0 : Mem) (N : NativeAddrs) (φc : Vsa.While.Addr → Nat)
    (v : Vsa.While.Value) (A : Arena)
    (hcode : Vsa.Sim.Code.Env_defineLoaded m0)
    (hword : ValueWordRepr m0 N φc src.toNat v)
    (hgeom : EnvDefineUpdateGeom env src vals dst idx m0)
    (hpayload : ValuePayloadCovered
      (fun a => a < dst.toNat ∨ dst.toNat + 24 ≤ a) m0 src.toNat v)
    (hdstArena : A.contains dst.toNat 24)
    (harenaStack : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo) :
    Triple
      (EnvDefineUpdateHitPre saved env name src count cursor sp idx m0)
      (EnvDefineCopiedUpdatePost saved env src dst sp idx m0 N φc v) := by
  intro c h
  obtain ⟨cmp, hp, _hsaved⟩ := h
  obtain ⟨hgood, hmemRaw, hpc, hregs, htick⟩ := hp
  have hmem : c.σ.mem = m0 := by
    simpa [envDefineScanHitSeg, evalBlocks, SegEvalState.init, writeLog] using hmemRaw
  obtain ⟨lds, hfacts, hevidence⟩ :=
    updateStoreFacts env src vals dst idx m0 N φc v hcode hword hgeom
  obtain ⟨hvals, d0, d1, d2, h0, h1, h2, hw0, hw1, hw2,
    hpin0, hpin1, hpin2⟩ := hevidence
  have reg (n : Nat) (w : BitVec 64)
      (hl : lookupG n (evalBlocks envDefineScanHitSeg
        (SegEvalState.init
          (envDefineScanLiveL cmp (BitVec.ofNat 64 idx) cursor count
            env name src sp) [])).regs = some w) :
      gprGet c.σ n = some w :=
    gholds_lookup _ hregs hl
  have hL : GHolds c.σ (updateStoreL env src (BitVec.ofNat 64 idx)) := by
    exact ⟨by simpa [gprGet] using reg 20 env (by rfl),
      by simpa [gprGet] using reg 21 src (by rfl),
      by simpa [gprGet] using reg 8 (BitVec.ofNat 64 idx) (by rfl), trivial⟩
  have hpre : SegPre updateStoreSeg
      (updateStoreL env src (BitVec.ofNat 64 idx)) lds 0x80002ac0#64 m0 c :=
    ⟨hgood, hmem, hpc, hgood.minstret, hL,
      (by show KeysOK [20, 21, 8]; decide),
      (by rw [hmem]; exact hfacts), htick⟩
  have hsp : c.σ.regs.get? Register.x2 = some sp := by
    simpa [gprGet] using reg 2 sp (by rfl)
  obtain ⟨c', hs, hp', hsp'⟩ :=
    updateStoreLiveRowSp env src (BitVec.ofNat 64 idx) sp lds m0 c ⟨hpre, hsp⟩
  have hrepr : ValueWordRepr c'.σ.mem N φc dst.toNat v :=
    updateStoreValueWordRepr env src vals dst idx lds m0 c' N φc v hp'
      hvals hgeom hpin0 hpin1 hpin2 hpayload hword
  have hmemTower : c'.σ.mem = UpdateValueTower m0 dst.toNat
      (lds.getD 1 []) (lds.getD 2 []) (lds.getD 3 []) := by
    rw [hp'.2.1, updateStoreLog env src vals dst idx lds m0 hvals hgeom]
    rfl
  have hsaved' : EnvDefineSavedSpillFrame sp saved c' := by
    apply _hsaved.of_arena_frame A hdstArena harenaStack harenaCode
    intro a ha
    rw [hmemTower, hmem]
    exact updateValueTowerOutside m0 dst.toNat a
      (lds.getD 1 []) (lds.getD 2 []) (lds.getD 3 []) ha
  refine ⟨c', hs, ⟨lds, hp', hrepr, hsaved', hsp', hmemTower⟩, ?_⟩
  intro k hk
  rw [hmemTower]
  exact updateValueTowerCopy m0 src.toNat dst.toNat
    (lds.getD 1 []) (lds.getD 2 []) (lds.getD 3 []) hpin0 hpin1 hpin2 k hk

/-- Project the exact copied update to the existing semantic update contract. -/
theorem envDefineUpdateFromHit
    (saved : (R : Register) → Option (RegisterType R))
    (env name src count cursor sp vals dst : BitVec 64) (idx : Nat)
    (m0 : Mem) (N : NativeAddrs) (φc : Vsa.While.Addr → Nat)
    (v : Vsa.While.Value) (A : Arena)
    (hcode : Vsa.Sim.Code.Env_defineLoaded m0)
    (hword : ValueWordRepr m0 N φc src.toNat v)
    (hgeom : EnvDefineUpdateGeom env src vals dst idx m0)
    (hpayload : ValuePayloadCovered
      (fun a => a < dst.toNat ∨ dst.toNat + 24 ≤ a) m0 src.toNat v)
    (hdstArena : A.contains dst.toNat 24)
    (harenaStack : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo) :
    Triple
      (EnvDefineUpdateHitPre saved env name src count cursor sp idx m0)
      (EnvDefineUpdatePost saved env src dst sp idx m0 N φc v) := by
  intro c hpre
  obtain ⟨after, hsteps, hpost⟩ := envDefineUpdateFromHitCopied saved env name src count
    cursor sp vals dst idx m0 N φc v A hcode hword hgeom hpayload hdstArena
    harenaStack harenaCode c hpre
  exact ⟨after, hsteps, hpost.update⟩

/-- Heap ownership of the staged source value derives the payload separation
needed by the exact update copy. -/
theorem envDefineUpdateFromHit_of_heap_owned
    (saved : (R : Register) → Option (RegisterType R))
    (env name src count cursor sp valsBV dst : BitVec 64) (idx : Nat)
    (m0 : Mem) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (v : Vsa.While.Value) (A : Arena) (exts : List Extent)
    (store : Vsa.While.Store) (target : Vsa.While.Addr)
    (htarget : target < store.frames.size)
    (hidx : idx < store.frames[target].vars.length)
    (hvals : read64 m0 (φf target + 16) = some valsBV.toNat)
    (hdst : dst.toNat = valsBV.toNat + 24 * idx)
    (howned : StoreHeapOwned m0 φf φc exts store)
    (hsrcOwned : ValueHeapOwned m0 exts src.toNat v)
    (hcode : Vsa.Sim.Code.Env_defineLoaded m0)
    (hword : ValueWordRepr m0 N φc src.toNat v)
    (hgeom : EnvDefineUpdateGeom env src valsBV dst idx m0)
    (hdstArena : A.contains dst.toNat 24)
    (harenaStack : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo) :
    Triple
      (EnvDefineUpdateHitPre saved env name src count cursor sp idx m0)
      (EnvDefineUpdatePost saved env src dst sp idx m0 N φc v) := by
  apply envDefineUpdateFromHit saved env name src count cursor sp valsBV dst idx
    m0 N φc v A hcode hword hgeom
  · have hp := howned.valuePayloadOutsideSet htarget hidx hvals hsrcOwned
    simpa [SetOutside, hdst] using hp
  · exact hdstArena
  · exact harenaStack
  · exact harenaCode

/-- Every target-frame byte except the overwritten value slot is outside the
three-store window.  This is the exact layout certificate needed to rebuild
`FrameRepr`; no post-state representation is assumed. -/
structure EnvDefineUpdateFrameFootprint
    (m : Mem) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (e slot : Nat) (f : Vsa.While.Frame) (hit : Nat) : Prop where
  header : ∀ k, envHeader e k → k < slot ∨ slot + 24 ≤ k
  nameSlots : ∀ pn pv, read64 m (e + 8) = some pn →
    read64 m (e + 16) = some pv → ∀ i, i < f.vars.length →
      ∀ k, k < 8 → pn + 8 * i + k < slot ∨ slot + 24 ≤ pn + 8 * i + k
  names : ∀ pn pv, read64 m (e + 8) = some pn →
    read64 m (e + 16) = some pv → ∀ i, (hi : i < f.vars.length) →
      ∀ qn, read64 m (pn + 8 * i) = some qn →
        ∀ k, k ≤ (f.vars[i].1).length → qn + k < slot ∨ slot + 24 ≤ qn + k
  otherValueHeaders : ∀ pn pv, read64 m (e + 8) = some pn →
    read64 m (e + 16) = some pv → ∀ i, i < f.vars.length → i ≠ hit →
      ∀ k, valHeader (pv + 24 * i) k → k < slot ∨ slot + 24 ≤ k
  otherValueStrings : ∀ pn pv, read64 m (e + 8) = some pn →
    read64 m (e + 16) = some pv → ∀ i, (hi : i < f.vars.length) → i ≠ hit →
      ValuePayloadCovered (fun a => a < slot ∨ slot + 24 ≤ a)
        m (pv + 24 * i) f.vars[i].2

/-- Reconstruct the exact updated `FrameRepr` from the old represented frame,
the reflected three-store result, and its explicit represented-footprint
separation certificate. -/
theorem envDefineUpdateFrameRepr
    (saved : (R : Register) → Option (RegisterType R))
    (env src dst sp : BitVec 64) (idx : Nat) (m0 : Mem)
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (f : Vsa.While.Frame) (name : String) (v : Vsa.While.Value)
    (c : Config)
    (hp : EnvDefineUpdatePost saved env src dst sp idx m0 N φc v c)
    (hframe : FrameRepr m0 N φf φc env.toNat f)
    (hidx : idx < f.vars.length) (hmatch : f.vars[idx].1 = name)
    (huniq : FrameUnique f)
    (hslot : ∀ pv, read64 m0 (env.toNat + 16) = some pv →
      dst.toNat = pv + 24 * idx)
    (hfoot : EnvDefineUpdateFrameFootprint m0 N φf φc
      env.toNat dst.toNat f idx) :
    FrameRepr c.σ.mem N φf φc env.toNat
      { f with vars :=
          if f.vars.any (·.1 == name) then
            f.vars.map fun p => if p.1 == name then (name, v) else p
          else f.vars ++ [(name, v)] } := by
  have hagree : AgreeP (fun a => a < dst.toNat ∨ dst.toNat + 24 ≤ a)
      m0 c.σ.mem := hp.agree_outside
  obtain ⟨_lds, _hrow, hword, _hsaved, _hsp, _hmem⟩ := hp
  obtain ⟨hcount, ⟨cap, hcap, hcaple⟩,
    ⟨pn, pv, hpn, hpv, hbind⟩, hparent⟩ := hframe
  have hslotEq := hslot pv hpv
  apply frameRepr_after_update c.σ.mem N φf φc env.toNat f name v idx
    hidx hmatch huniq
  · rw [← read32_agreeP hagree (fun k hk => hfoot.header _ ⟨by omega, by omega⟩)]
    exact hcount
  · refine ⟨cap, ?_, hcaple⟩
    rw [← read32_agreeP hagree (fun k hk => hfoot.header _ ⟨by omega, by omega⟩)]
    exact hcap
  · rw [← read64_agreeP hagree (fun k hk => hfoot.header _ ⟨by omega, by omega⟩)]
    exact hpn
  · rw [← read64_agreeP hagree (fun k hk => hfoot.header _ ⟨by omega, by omega⟩)]
    exact hpv
  · intro i hi
    obtain ⟨⟨q, hq, hqstr⟩, _⟩ := hbind i hi
    refine ⟨q, ?_, ?_⟩
    · rw [← read64_agreeP hagree (hfoot.nameSlots pn pv hpn hpv i hi)]
      exact hq
    · exact cstring_agreeP hagree hqstr (hfoot.names pn pv hpn hpv i hi q hq)
  · rw [← hslotEq]
    exact hword.repr
  · intro i hi hne
    obtain ⟨_, hval⟩ := hbind i hi
    exact valueRepr_agreeP hagree
      (hfoot.otherValueHeaders pn pv hpn hpv i hi hne)
      (hfoot.otherValueStrings pn pv hpn hpv i hi hne)
      hval
  · cases hpar : f.parent with
    | none =>
      simp only [hpar] at hparent ⊢
      rw [← read64_agreeP hagree (fun k hk => hfoot.header _ ⟨by omega, by omega⟩)]
      exact hparent
    | some pa =>
      simp only [hpar] at hparent ⊢
      exact ⟨by
        rw [← read64_agreeP hagree (fun k hk => hfoot.header _ ⟨by omega, by omega⟩)]
        exact hparent.1, hparent.2⟩

/-- Lift one reconstructed hit frame to the exact whole-store `define`
advance.  All untouched objects are transported through the explicit
one-slot footprint certificate. -/
theorem storeDefineAdvance_of_update
    {m m' : Mem} {N : NativeAddrs} {A : Arena}
    {φf φc : Vsa.While.Addr → Nat} {store : Vsa.While.Store}
    {target : Vsa.While.Addr} {f : Vsa.While.Frame}
    {name : String} {v : Vsa.While.Value} {slot : Nat}
    (hstore : StoreRepr m N A φf φc store)
    (hget : store.frames[target]? = some f)
    (hnew : FrameRepr m' N φf φc (φf target)
      { f with vars :=
          if f.vars.any (·.1 == name) then
            f.vars.map fun p => if p.1 == name then (name, v) else p
          else f.vars ++ [(name, v)] })
    (hfoot : StoreSetFootprint m m' N φf φc store target slot) :
    StoreDefineAdvance N A φf φc store target name v m' := by
  obtain ⟨htargetBound, htargetGet⟩ := Array.getElem?_eq_some_iff.mp hget
  refine
    { mutated := ?_
      others := ?_
      closures := ?_
      φf_inj := ?_
      φc_inj := ?_
      frames_arena := ?_
      closures_arena := ?_ }
  · intro htargetNew
    simp only [Vsa.While.Store.define, Array.getElem_modify, if_pos]
    rw [htargetGet]
    exact hnew
  · intro fa hfa hne
    have hfaOld : fa < store.frames.size := by
      simpa [Vsa.While.Store.define] using hfa
    have hsurvive := (hfoot.frames fa hfaOld hne).survive hfoot.outside
      (hstore.frames fa hfaOld)
    simpa [Vsa.While.Store.define, Array.getElem_modify, hne, Ne.symm hne] using hsurvive
  · intro ca hca
    have hcaOld : ca < store.closures.size := by
      simpa [Vsa.While.Store.define] using hca
    simpa [Vsa.While.Store.define] using
      (hfoot.closures ca hcaOld).survive hfoot.outside
        (hstore.closures ca hcaOld)
  · intro p q hp hq heq
    exact hstore.φf_inj p q (by simpa [Vsa.While.Store.define] using hp)
      (by simpa [Vsa.While.Store.define] using hq) heq
  · intro p q hp hq heq
    exact hstore.φc_inj p q (by simpa [Vsa.While.Store.define] using hp)
      (by simpa [Vsa.While.Store.define] using hq) heq
  · intro fa hfa
    exact hstore.frames_arena fa (by simpa [Vsa.While.Store.define] using hfa)
  · intro ca hca
    exact hstore.closures_arena ca (by simpa [Vsa.While.Store.define] using hca)

/-- Execute the reflected restore-and-return row once, retaining its exact
register result and unchanged memory. -/
theorem EnvDefineUpdatePost.restore
    {saved : (R : Register) → Option (RegisterType R)}
    {env src dst sp : BitVec 64} {idx : Nat} {m0 : Mem}
    {N : NativeAddrs} {phiC : Vsa.While.Addr → Nat} {v : Vsa.While.Value} {c : Config}
    (hp : EnvDefineUpdatePost saved env src dst sp idx m0 N phiC v c) :
    ∃ after, Vsa.Machine.Steps c after ∧ EnvDefineEpilogueExactPost sp saved c.σ.mem after := by
  obtain ⟨_ldsUpdate, hrow, _hword, hsaved, hsp, _hmemTower⟩ := hp
  obtain ⟨hgood, _hmem, hpc, _hregs, htick⟩ := hrow
  obtain ⟨lds, hfacts, hvalues⟩ := hsaved.chainFacts
  have hpre : SegPre envDefineEpilogueSeg (envDefineEpilogueL sp) lds
      0x80002aec#64 c.σ.mem c :=
    ⟨hgood, rfl, hpc, hgood.minstret, ⟨hsp, trivial⟩,
      (by show KeysOK [2]; decide), hfacts, htick⟩
  obtain ⟨c', hs, hpost⟩ := envDefineEpilogueRow sp lds c.σ.mem c hpre
  exact ⟨c', hs, envDefineEpilogueExact_of_post sp saved lds c.σ.mem c' hvalues hpost⟩

/-- Execute the shared restore-and-ret tail after the exact hit update while
retaining the reconstructed semantic frame. -/
theorem envDefineUpdateEpilogue
    (saved : (R : Register) → Option (RegisterType R))
    (env src dst sp : BitVec 64) (idx : Nat) (m0 : Mem)
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (f : Vsa.While.Frame) (name : String) (v : Vsa.While.Value)
    (hframe : FrameRepr m0 N φf φc env.toNat f)
    (hidx : idx < f.vars.length) (hmatch : f.vars[idx].1 = name)
    (huniq : FrameUnique f)
    (hslot : ∀ pv, read64 m0 (env.toNat + 16) = some pv →
      dst.toNat = pv + 24 * idx)
    (hfoot : EnvDefineUpdateFrameFootprint m0 N φf φc
      env.toNat dst.toNat f idx) :
    Triple
      (EnvDefineUpdatePost saved env src dst sp idx m0 N φc v)
      (fun c => ∃ m,
        EnvDefineEpilogueExactPost sp saved m c ∧
        FrameRepr c.σ.mem N φf φc env.toNat
          { f with vars :=
              if f.vars.any (·.1 == name) then
                f.vars.map fun p => if p.1 == name then (name, v) else p
              else f.vars ++ [(name, v)] }) := by
  intro c hp
  have hfr := envDefineUpdateFrameRepr saved env src dst sp idx m0 N φf φc
    f name v c hp hframe hidx hmatch huniq hslot hfoot
  obtain ⟨c', hs, hret⟩ := hp.restore
  have hfr' : FrameRepr c'.σ.mem N φf φc env.toNat
      { f with vars :=
          if f.vars.any (·.1 == name) then
            f.vars.map fun p => if p.1 == name then (name, v) else p
          else f.vars ++ [(name, v)] } := by
    rw [hret.mem]
    exact hfr
  exact ⟨c', hs, c.σ.mem, hret, hfr'⟩

/-- The global heap invariant closes both update footprint premises and retains
the exact semantic store advance through the memory-pure epilogue. -/
theorem envDefineUpdateEpilogueAdvance
    (saved : (R : Register) → Option (RegisterType R))
    (env src dst sp : BitVec 64) (idx : Nat) (m0 : Mem)
    (N : NativeAddrs) (A : Arena) (φf φc : Vsa.While.Addr → Nat)
    (exts : List Extent) (store : Vsa.While.Store) (target : Vsa.While.Addr)
    (f : Vsa.While.Frame) (name : String) (v : Vsa.While.Value)
    (hget : store.frames[target]? = some f)
    (henv : env.toNat = φf target)
    (hstore : StoreRepr m0 N A φf φc store)
    (howned : StoreHeapOwned m0 φf φc exts store)
    (hframe : FrameRepr m0 N φf φc env.toNat f)
    (hidx : idx < f.vars.length) (hmatch : f.vars[idx].1 = name)
    (huniq : FrameUnique f)
    (hslot : ∀ pv, read64 m0 (env.toNat + 16) = some pv →
      dst.toNat = pv + 24 * idx) :
    Triple
      (EnvDefineUpdatePost saved env src dst sp idx m0 N φc v)
      (fun c => ∃ m,
        EnvDefineEpilogueExactPost sp saved m c ∧
        FrameRepr c.σ.mem N φf φc env.toNat
          { f with vars :=
              if f.vars.any (·.1 == name) then
                f.vars.map fun p => if p.1 == name then (name, v) else p
              else f.vars ++ [(name, v)] } ∧
        StoreDefineAdvance N A φf φc store target name v c.σ.mem) := by
  intro c hp
  obtain ⟨_pn, pv, _hpn, hpv, _hbind⟩ := hframe.2.2.1
  obtain ⟨htarget, htargetEq⟩ := Array.getElem?_eq_some_iff.mp hget
  have hpvTarget : read64 m0 (φf target + 16) = some pv := by
    rw [← henv]
    exact hpv
  have hidxTarget : idx < store.frames[target].vars.length := by
    simpa [htargetEq] using hidx
  have hslotEq : dst.toNat = pv + 24 * idx := hslot pv hpv
  have hshell0 := StoreSetFootprint.target_of_heap_owned
    (N := N) htarget hidxTarget hpvTarget hslotEq howned
  have hshell : TargetFrameOutsideSetSlot m0 N φf φc env.toNat dst.toNat f idx := by
    simpa [henv, htargetEq] using hshell0
  have hframeFoot : EnvDefineUpdateFrameFootprint m0 N φf φc
      env.toNat dst.toNat f idx :=
    { header := hshell.header
      nameSlots := hshell.nameSlots
      names := hshell.names
      otherValueHeaders := hshell.otherValueHeaders
      otherValueStrings := hshell.otherValueStrings }
  have hnew := envDefineUpdateFrameRepr saved env src dst sp idx m0 N φf φc
    f name v c hp hframe hidx hmatch huniq hslot hframeFoot
  have hagree : AgreeP (OutsideSetSlot dst.toNat) m0 c.σ.mem := hp.agree_outside
  have hwhole := StoreSetFootprint.of_heap_owned
    (N := N) htarget hidxTarget hpvTarget hslotEq howned hagree
  have hnewTarget : FrameRepr c.σ.mem N φf φc (φf target)
      { f with vars :=
          if f.vars.any (·.1 == name) then
            f.vars.map fun p => if p.1 == name then (name, v) else p
          else f.vars ++ [(name, v)] } := by
    rw [← henv]
    exact hnew
  have hadv : StoreDefineAdvance N A φf φc store target name v c.σ.mem :=
    storeDefineAdvance_of_update hstore hget hnewTarget hwhole
  obtain ⟨c', hs, hepi⟩ := hp.restore
  have hframe' : FrameRepr c'.σ.mem N φf φc env.toNat
      { f with vars :=
          if f.vars.any (·.1 == name) then
            f.vars.map fun p => if p.1 == name then (name, v) else p
          else f.vars ++ [(name, v)] } := by
    rw [hepi.mem]
    exact hnew
  refine ⟨c', hs, c.σ.mem, hepi, hframe', ?_⟩
  rw [hepi.mem]
  exact hadv

/-- Complete existing-name lane: reflected hit, exact three-word copy, global
footprint reconstruction, and concrete epilogue. -/
theorem envDefineUpdateClosed_of_heap_owned
    (saved : (R : Register) → Option (RegisterType R))
    (env namePtr src count cursor sp valsBV dst : BitVec 64) (idx : Nat)
    (m0 : Mem) (N : NativeAddrs) (A : Arena)
    (φf φc : Vsa.While.Addr → Nat) (exts : List Extent)
    (store : Vsa.While.Store) (target : Vsa.While.Addr)
    (f : Vsa.While.Frame) (name : String) (v : Vsa.While.Value)
    (hget : store.frames[target]? = some f)
    (henv : env.toNat = φf target)
    (hstore : StoreRepr m0 N A φf φc store)
    (howned : StoreHeapOwned m0 φf φc exts store)
    (hframe : FrameRepr m0 N φf φc env.toNat f)
    (hidx : idx < f.vars.length) (hmatch : f.vars[idx].1 = name)
    (huniq : FrameUnique f)
    (hvals : read64 m0 (φf target + 16) = some valsBV.toNat)
    (hdst : dst.toNat = valsBV.toNat + 24 * idx)
    (hslot : ∀ pv, read64 m0 (env.toNat + 16) = some pv →
      dst.toNat = pv + 24 * idx)
    (hsrcOwned : ValueHeapOwned m0 exts src.toNat v)
    (hcode : Vsa.Sim.Code.Env_defineLoaded m0)
    (hword : ValueWordRepr m0 N φc src.toNat v)
    (hgeom : EnvDefineUpdateGeom env src valsBV dst idx m0)
    (hdstArena : A.contains dst.toNat 24)
    (harenaStack : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo) :
    Triple
      (EnvDefineUpdateHitPre saved env namePtr src count cursor sp idx m0)
      (fun c => ∃ m,
        EnvDefineEpilogueExactPost sp saved m c ∧
        FrameRepr c.σ.mem N φf φc env.toNat
          { f with vars :=
              if f.vars.any (·.1 == name) then
                f.vars.map fun p => if p.1 == name then (name, v) else p
              else f.vars ++ [(name, v)] } ∧
        StoreDefineAdvance N A φf φc store target name v c.σ.mem) := by
  obtain ⟨htarget, htargetEq⟩ := Array.getElem?_eq_some_iff.mp hget
  apply Triple.seq
    (envDefineUpdateFromHit_of_heap_owned saved env namePtr src count cursor sp
      valsBV dst idx m0 N φf φc v A exts store target htarget
      (by simpa [htargetEq] using hidx) hvals hdst howned hsrcOwned hcode hword
      hgeom hdstArena harenaStack harenaCode)
  exact envDefineUpdateEpilogueAdvance saved env src dst sp idx m0 N A φf φc
    exts store target f name v hget henv hstore howned hframe hidx hmatch
    huniq hslot

#print axioms updateStoreLiveRow
#print axioms envDefineUpdateFromHit
#print axioms updateStoreValueWordRepr
#print axioms envDefineUpdateFrameRepr
#print axioms storeDefineAdvance_of_update
#print axioms envDefineUpdateEpilogue
#print axioms envDefineUpdateEpilogueAdvance
#print axioms envDefineUpdateClosed_of_heap_owned


#print axioms envDefineUpdateFromHitCopied
#print axioms EnvDefineUpdatePost.restore

end Vsa.Sim
