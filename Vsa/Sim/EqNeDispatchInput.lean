import Vsa.Sim.EvalBinSim
import Vsa.Sim.EvalEqNeArm
import Vsa.Sim.StackSlotGeom
import Vsa.Sim.ValueTruthySpec

/-!
# Value-generic eq/ne dispatch input

The common binary entry linkage used to hardcode both operand kinds to `VAL_INT`.
Equality is value-generic.  This file packages the raw post-recursion facts once and
derives either eq or ne dispatch without assuming an operand kind.

No completed `Steps` chain is stored in the input.  The theorem below constructs it.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (Config Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc

namespace Vsa.Sim

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

inductive EqNeOp where
  | eq
  | ne

namespace EqNeOp

def token : EqNeOp → Nat
  | .eq => 19
  | .ne => 17

def slotPinned (op : EqNeOp) (m : Mem) : Prop :=
  match op with
  | .eq => SlotPinned 0x80019fa4#64 0x60#8 0x97#8 0xfe#8 0xff#8 m
  | .ne => SlotPinned 0x80019f9c#64 0xb0#8 0x97#8 0xfe#8 0xff#8 m

def DispatchPost (op : EqNeOp) (base : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) (out0 : Array String)
    (gpre : (R : Register) → Option (RegisterType R)) (c : Config) : Prop :=
  match op with
  | .eq => EqDispatchPostS base lds m0 out0 gpre c
  | .ne => NeDispatchPostS base lds m0 out0 gpre c

/-- The memory and source-load facts used to reconstruct the copied operands. -/
structure DispatchReadback (op : EqNeOp) (base : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) (c : Config) : Prop where
  memory : c.σ.mem = writeLog m0
    (evalBlocks (match op with | .eq => eqDispatch | .ne => neDispatch)
      (SegEvalState.init (eqDispL base) lds)).log
  pins : EqNeSrcPins base lds m0

/-- Destructure either landed dispatch post once, behind named fields. -/
theorem DispatchPost.readback {op : EqNeOp} {base : BitVec 64}
    {lds : List (List (BitVec 8))} {m0 : Mem} {out0 : Array String}
    {gpre : (R : Register) → Option (RegisterType R)} {c : Config}
    (h : DispatchPost op base lds m0 out0 gpre c) :
    DispatchReadback op base lds m0 c := by
  cases op <;>
    obtain ⟨_, hmem, _, _, _, _, _, _, _, hpins⟩ := h <;>
    exact ⟨hmem, hpins⟩

end EqNeOp

/-- Raw facts not supplied by `TwoSubReturn`.  They contain data and geometry only;
the dispatch execution is derived by `evalEqNeChain_dispatch_of_twoSubReturn`. -/
structure EqNeDispatchInput
    (op : EqNeOp) (gpre : (R : Register) → Option (RegisterType R))
    (SL : StackLayout) (sp aExpr : BitVec 64) (c : Config) : Prop where
  gx8 : gpre Register.x8 = some aExpr
  opTok : read32 c.σ.mem (aExpr.toNat + 8) = some op.token
  slot : op.slotPinned c.σ.mem
  expr : ExprBounds aExpr
  stack : StackBounds sp SL

/-- The dispatch frame bundle at the arm's frame base `sp - 1088`, from the entry
stack bounds (the geometry `evalEqNeChain_dispatch_of_twoSubReturn` builds
internally, exposed so consumers can state the dispatch's memory frame). -/
theorem frameBundle_of_stackBounds {sp : BitVec 64} {SL : StackLayout} {m : Mem}
    (hSB : StackBounds sp SL) : FrameBundle m (sp - 1088#64) := by
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]
    have := sp.isLt
    have := hSB.SLloSp
    have := hSB.SLlo
    omega
  exact ⟨hspsub ▸ (frameBaseGeom hSB).1, hspsub ▸ (frameBaseGeom hSB).2.1,
    hspsub ▸ (frameBaseGeom hSB).2.2.1, hspsub ▸ (frameBaseGeom hSB).2.2.2⟩

#print axioms frameBundle_of_stackBounds

/-- The actual left value tag identifies the kind respilled by the binary head. -/
theorem BinaryReturnLoads.kind_readback {sp : BitVec 64} {c : Config}
    {N : NativeAddrs} {φ : Addr → Nat} {v : Value}
    (h : BinaryReturnLoads sp c)
    (hv : ValueRepr c.σ.mem N φ (sp.toNat - 968) v) :
    read64 c.σ.mem (sp.toNat - 1088) = some (BitVec.ofNat 64 (kindTag v)).toNat := by
  have hk := kind_read32 c.σ.mem (sp.toNat - 968) v (truthyHeaderRepr_of_valueRepr hv)
  have hnat : (BitVec.ofNat 32 (kindTag v)).toNat = kindTag v := by cases v <;> rfl
  have hword : bytesT4 c.σ.mem (sp.toNat - 968) = BitVec.ofNat 32 (kindTag v) :=
    bytesT4_of_read32 (hnat.symm ▸ hk)
  have hext : sign_extend (m := 64) (BitVec.ofNat 32 (kindTag v)) =
      BitVec.ofNat 64 (kindTag v) := by cases v <;> rfl
  rw [h.kind_spill, hword, hext]

#print axioms BinaryReturnLoads.kind_readback

/-- Run the shared entry linkage and the selected eq/ne reflected dispatch from a
`TwoSubReturn` state.  Operand kind tags are recovered from `ValueRepr`; no integer
specialization remains. -/
theorem evalEqNeChain_dispatch_of_twoSubReturn
    (op : EqNeOp)
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' st'' : Vsa.While.St) (vl vr : Value)
    (sp r sret aExpr : BitVec 64) (v8 v9 v18 : BitVec 64)
    (m0 : Mem) (c : Config)
    (hTS : TwoSubReturn gpre N A SL φf φc nf nc st' st'' vl vr
      sp r sret v8 v9 v18 m0 c)
    (hLoads : BinaryReturnLoads sp c)
    (hIn : EqNeDispatchInput op gpre SL sp aExpr c) :
    ∃ (cD : Config) (lds : List (List (BitVec 8))),
      Steps c cD ∧
      op.DispatchPost (sp - 1088#64) lds c.σ.mem c.σ.sailOutput
        (fun R => c.σ.regs.get? R) cD := by
  obtain ⟨hG, htick, hpc, _hra, hs1, hsp, ⟨vmi, hmi⟩, _hout, hframe,
    _hs3, hstoreBundle, hcode, _hslotRa, _hslotS0, _hslotS1, _hslotS2,
    _hMemExt, _hmemframe⟩ := hTS
  obtain ⟨_φfm, _φcm, _hpfm, _hpcm, ⟨φcr, _hpcr, hvalR⟩,
    ⟨φcl, hvalL⟩, _hstoreTail⟩ := hstoreBundle
  let Wl : BitVec 64 := bytesT8 c.σ.mem (sp.toNat - 960)
  have hX19 : c.σ.regs.get? Register.x19 = some Wl := hLoads.payload_register
  have hKindResp := hLoads.kind_readback hvalL
  have hx8 : c.σ.regs.get? Register.x8 = some aExpr :=
    (hframe Register.x8 (by decide) (by decide)).trans hIn.gx8
  have hAr : SpArith sp SL := spArith hIn.stack
  have hsp1088 : 1088 ≤ sp.toNat := hAr.sp1088
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]
    have := sp.isLt
    omega
  have gExpr8 := exprGeom4 hIn.expr 8 (by decide)
  have gExpr4 := exprGeom4 hIn.expr 4 (by decide)
  have g944 := slotGeom8 hIn.stack 944 (by decide) (by decide) (by decide)
  have g936 := slotGeom8 hIn.stack 936 (by decide) (by decide) (by decide)
  have g1088 := slotGeom8 hIn.stack 1088 (by decide) (by decide) (by decide)
  have haddr944 :
      ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 944 :=
    spill_addr sp (0x090#12) 944 (by decide) (by decide) hsp1088
  have haddr936 :
      ((sp - 1088#64) + sign_extend (m := 64) (0x098#12)).toNat = sp.toNat - 936 :=
    spill_addr sp (0x098#12) 936 (by decide) (by decide) hsp1088
  have haddr0 :
      ((sp - 1088#64) + sign_extend (m := 64) (0x000#12)).toNat = sp.toNat - 1088 := by
    have hz : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      decide
    rw [hz, BitVec.add_zero]
    exact hspsub
  have hop8 :
      (aExpr + sign_extend (m := 64) (0x008#12)).toNat = aExpr.toNat + 8 := by
    have hs : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
      apply BitVec.eq_of_toNat_eq
      decide
    rw [hs, BitVec.toNat_add]
    have hv : (8#64 : BitVec 64).toNat = 8 := by decide
    rw [hv]
    have := aExpr.isLt
    rw [Nat.mod_eq_of_lt (by omega)]
  have hline4 :
      (aExpr + sign_extend (m := 64) (0x004#12)).toNat = aExpr.toNat + 4 := by
    have hs : (sign_extend (m := 64) (0x004#12) : BitVec 64) = 4#64 := by
      apply BitVec.eq_of_toNat_eq
      decide
    rw [hs, BitVec.toNat_add]
    have hv : (4#64 : BitVec 64).toNat = 4 := by decide
    rw [hv]
    have := aExpr.isLt
    rw [Nat.mod_eq_of_lt (by omega)]
  obtain ⟨tb0, tb1, tb2, tb3, htb0, htb1, htb2, htb3, htbrec⟩ :=
    read32_bytes c.σ.mem (aExpr.toNat + 8) op.token hIn.opTok
  have htok :
      bytesVal MKind.lw [tb0, tb1, tb2, tb3] = BitVec.ofNat 64 op.token :=
    sext_kind tb0 tb1 tb2 tb3 op.token (by cases op <;> decide) htbrec
  let lb0 := bytesT1 c.σ.mem (aExpr.toNat + 4)
  have hlb0 : bytesT1 c.σ.mem (aExpr.toNat + 4) = lb0 := rfl
  let lb1 := bytesT1 c.σ.mem (aExpr.toNat + 4 + 1)
  have hlb1 : bytesT1 c.σ.mem (aExpr.toNat + 4 + 1) = lb1 := rfl
  let lb2 := bytesT1 c.σ.mem (aExpr.toNat + 4 + 2)
  have hlb2 : bytesT1 c.σ.mem (aExpr.toNat + 4 + 2) = lb2 := rfl
  let lb3 := bytesT1 c.σ.mem (aExpr.toNat + 4 + 3)
  have hlb3 : bytesT1 c.σ.mem (aExpr.toNat + 4 + 3) = lb3 := rfl
  have hkindR : read32 c.σ.mem (sp.toNat - 944) = some (kindTag vr) :=
    kind_read32 c.σ.mem (sp.toNat - 944) vr (truthyHeaderRepr_of_valueRepr hvalR)
  obtain ⟨rkb0, rkb1, rkb2, rkb3, hrkb0, hrkb1, hrkb2, hrkb3, hrkbrec⟩ :=
    read32_bytes c.σ.mem (sp.toNat - 944) (kindTag vr) hkindR
  have hrk : bytesVal MKind.lw [rkb0, rkb1, rkb2, rkb3]
      = BitVec.ofNat 64 (kindTag vr) :=
    sext_kind rkb0 rkb1 rkb2 rkb3 (kindTag vr)
      (by cases vr <;> simp [kindTag]) hrkbrec
  let dp0 := bytesT1 c.σ.mem (sp.toNat - 936)
  have hdp0 : bytesT1 c.σ.mem (sp.toNat - 936) = dp0 := rfl
  let dp1 := bytesT1 c.σ.mem (sp.toNat - 936 + 1)
  have hdp1 : bytesT1 c.σ.mem (sp.toNat - 936 + 1) = dp1 := rfl
  let dp2 := bytesT1 c.σ.mem (sp.toNat - 936 + 2)
  have hdp2 : bytesT1 c.σ.mem (sp.toNat - 936 + 2) = dp2 := rfl
  let dp3 := bytesT1 c.σ.mem (sp.toNat - 936 + 3)
  have hdp3 : bytesT1 c.σ.mem (sp.toNat - 936 + 3) = dp3 := rfl
  let dp4 := bytesT1 c.σ.mem (sp.toNat - 936 + 4)
  have hdp4 : bytesT1 c.σ.mem (sp.toNat - 936 + 4) = dp4 := rfl
  let dp5 := bytesT1 c.σ.mem (sp.toNat - 936 + 5)
  have hdp5 : bytesT1 c.σ.mem (sp.toNat - 936 + 5) = dp5 := rfl
  let dp6 := bytesT1 c.σ.mem (sp.toNat - 936 + 6)
  have hdp6 : bytesT1 c.σ.mem (sp.toNat - 936 + 6) = dp6 := rfl
  let dp7 := bytesT1 c.σ.mem (sp.toNat - 936 + 7)
  have hdp7 : bytesT1 c.σ.mem (sp.toNat - 936 + 7) = dp7 := rfl
  obtain ⟨kb0, kb1, kb2, kb3, kb4, kb5, kb6, kb7,
    hkb0, hkb1, hkb2, hkb3, hkb4, hkb5, hkb6, hkb7, hkbrec⟩ :=
    read64_bytes c.σ.mem (sp.toNat - 1088)
      (BitVec.ofNat 64 (kindTag vl)).toNat hKindResp
  have hlk : bytesVal MKind.ld [kb0, kb1, kb2, kb3, kb4, kb5, kb6, kb7]
      = BitVec.ofNat 64 (kindTag vl) := by
    apply BitVec.eq_of_toNat_eq
    show (sign_extend (m := 64)
      ((((((((kb7.append kb6).append kb5).append kb4).append kb3).append kb2).append kb1).append kb0)
        : BitVec (8 * 8))).toNat = _
    rw [sext_full, word8_toNat_recon, hkbrec]
  have hfb : FrameBundle c.σ.mem (sp - 1088#64) :=
    ⟨hspsub ▸ (frameBaseGeom hIn.stack).1,
      hspsub ▸ (frameBaseGeom hIn.stack).2.1,
      hspsub ▸ (frameBaseGeom hIn.stack).2.2.1,
      hspsub ▸ (frameBaseGeom hIn.stack).2.2.2⟩
  cases op with
  | eq =>
      have hSlot := hIn.slot
      change SlotPinned 0x80019fa4#64 0x60#8 0x97#8 0xfe#8 0xff#8 c.σ.mem at hSlot
      have htok' : bytesVal MKind.lw [tb0, tb1, tb2, tb3] = (19#64 : BitVec 64) := by
        simpa [EqNeOp.token] using htok
      simpa [EqNeOp.DispatchPost] using
        (evalEqChain_dispatch c.σ c.tick c.steps vmi (sp - 1088#64) aExpr sret Wl
          (BitVec.ofNat 64 (kindTag vr)) (BitVec.ofNat 64 (kindTag vl))
          tb0 tb1 tb2 tb3 lb0 lb1 lb2 lb3 rkb0 rkb1 rkb2 rkb3
          dp0 dp1 dp2 dp3 dp4 dp5 dp6 dp7 kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7
          0x60#8 0x97#8 0xfe#8 0xff#8 hG hpc hmi hsp hx8 hs1 hX19 hcode
          htok' hrk hlk
          (by rw [hop8]; exact gExpr8.1)
          (by rw [hop8]; exact gExpr8.2.1)
          (by rw [hop8]; exact gExpr8.2.2)
          (by rw [hop8]; exact lpin_of_present htb0) (by rw [hop8]; exact lpin_of_present htb1)
          (by rw [hop8]; exact lpin_of_present htb2) (by rw [hop8]; exact lpin_of_present htb3)
          (by rw [hline4]; exact gExpr4.1)
          (by rw [hline4]; exact gExpr4.2.1)
          (by rw [hline4]; exact gExpr4.2.2)
          (by simpa only [hline4] using hlb0) (by simpa only [hline4] using hlb1)
          (by simpa only [hline4] using hlb2) (by simpa only [hline4] using hlb3)
          (by rw [haddr944]; exact g944.lo) (by rw [haddr944]; exact g944.hi4)
          (by rw [haddr944]; exact g944.ht4) (by rw [haddr944]; exact g944.al4)
          (by rw [haddr944]; exact lpin_of_present hrkb0) (by rw [haddr944]; exact lpin_of_present hrkb1)
          (by rw [haddr944]; exact lpin_of_present hrkb2) (by rw [haddr944]; exact lpin_of_present hrkb3)
          (by rw [haddr936]; exact g936.lo) (by rw [haddr936]; exact g936.hi8)
          (by rw [haddr936]; exact g936.ht8) (by rw [haddr936]; exact g936.al8)
          (by simpa only [haddr936] using hdp0) (by simpa only [haddr936] using hdp1)
          (by simpa only [haddr936] using hdp2) (by simpa only [haddr936] using hdp3)
          (by simpa only [haddr936] using hdp4) (by simpa only [haddr936] using hdp5)
          (by simpa only [haddr936] using hdp6) (by simpa only [haddr936] using hdp7)
          hSlot rfl rfl rfl rfl
          (by rw [haddr0]; exact g1088.lo) (by rw [haddr0]; exact g1088.hi8)
          (by rw [haddr0]; exact g1088.ht8) (by rw [haddr0]; exact g1088.al8)
          (by rw [haddr0]; exact lpin_of_present hkb0) (by rw [haddr0]; exact lpin_of_present hkb1)
          (by rw [haddr0]; exact lpin_of_present hkb2) (by rw [haddr0]; exact lpin_of_present hkb3)
          (by rw [haddr0]; exact lpin_of_present hkb4) (by rw [haddr0]; exact lpin_of_present hkb5)
          (by rw [haddr0]; exact lpin_of_present hkb6) (by rw [haddr0]; exact lpin_of_present hkb7)
          htick hfb)
  | ne =>
      have hSlot := hIn.slot
      change SlotPinned 0x80019f9c#64 0xb0#8 0x97#8 0xfe#8 0xff#8 c.σ.mem at hSlot
      have htok' : bytesVal MKind.lw [tb0, tb1, tb2, tb3] = (17#64 : BitVec 64) := by
        simpa [EqNeOp.token] using htok
      simpa [EqNeOp.DispatchPost] using
        (evalNeChain_dispatch c.σ c.tick c.steps vmi (sp - 1088#64) aExpr sret Wl
          (BitVec.ofNat 64 (kindTag vr)) (BitVec.ofNat 64 (kindTag vl))
          tb0 tb1 tb2 tb3 lb0 lb1 lb2 lb3 rkb0 rkb1 rkb2 rkb3
          dp0 dp1 dp2 dp3 dp4 dp5 dp6 dp7 kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7
          0xb0#8 0x97#8 0xfe#8 0xff#8 hG hpc hmi hsp hx8 hs1 hX19 hcode
          htok' hrk hlk
          (by rw [hop8]; exact gExpr8.1)
          (by rw [hop8]; exact gExpr8.2.1)
          (by rw [hop8]; exact gExpr8.2.2)
          (by rw [hop8]; exact lpin_of_present htb0) (by rw [hop8]; exact lpin_of_present htb1)
          (by rw [hop8]; exact lpin_of_present htb2) (by rw [hop8]; exact lpin_of_present htb3)
          (by rw [hline4]; exact gExpr4.1)
          (by rw [hline4]; exact gExpr4.2.1)
          (by rw [hline4]; exact gExpr4.2.2)
          (by simpa only [hline4] using hlb0) (by simpa only [hline4] using hlb1)
          (by simpa only [hline4] using hlb2) (by simpa only [hline4] using hlb3)
          (by rw [haddr944]; exact g944.lo) (by rw [haddr944]; exact g944.hi4)
          (by rw [haddr944]; exact g944.ht4) (by rw [haddr944]; exact g944.al4)
          (by rw [haddr944]; exact lpin_of_present hrkb0) (by rw [haddr944]; exact lpin_of_present hrkb1)
          (by rw [haddr944]; exact lpin_of_present hrkb2) (by rw [haddr944]; exact lpin_of_present hrkb3)
          (by rw [haddr936]; exact g936.lo) (by rw [haddr936]; exact g936.hi8)
          (by rw [haddr936]; exact g936.ht8) (by rw [haddr936]; exact g936.al8)
          (by simpa only [haddr936] using hdp0) (by simpa only [haddr936] using hdp1)
          (by simpa only [haddr936] using hdp2) (by simpa only [haddr936] using hdp3)
          (by simpa only [haddr936] using hdp4) (by simpa only [haddr936] using hdp5)
          (by simpa only [haddr936] using hdp6) (by simpa only [haddr936] using hdp7)
          hSlot rfl rfl rfl rfl
          (by rw [haddr0]; exact g1088.lo) (by rw [haddr0]; exact g1088.hi8)
          (by rw [haddr0]; exact g1088.ht8) (by rw [haddr0]; exact g1088.al8)
          (by rw [haddr0]; exact lpin_of_present hkb0) (by rw [haddr0]; exact lpin_of_present hkb1)
          (by rw [haddr0]; exact lpin_of_present hkb2) (by rw [haddr0]; exact lpin_of_present hkb3)
          (by rw [haddr0]; exact lpin_of_present hkb4) (by rw [haddr0]; exact lpin_of_present hkb5)
          (by rw [haddr0]; exact lpin_of_present hkb6) (by rw [haddr0]; exact lpin_of_present hkb7)
          htick hfb)

#print axioms evalEqNeChain_dispatch_of_twoSubReturn

end Vsa.Sim
