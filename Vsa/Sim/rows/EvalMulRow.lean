import Vsa.Sim.EvalBinSim3
import Vsa.Sim.ChainFrameOut
import Vsa.Sim.StackSlotGeom
import Vsa.Sim.EvalMulChain
import Vsa.Sim.MulTailSites
import Vsa.Sim.Muldi3Spec
import Vsa.Sim.rows.IntPostEpilogue
import Vsa.Sim.BinopTailGen

/-!
# `EvalMulRow` — Wave-D M4 row: `evalMulSim` (the `EvalE.binary .mul` int case)

Clones the `.sub` row (`EvalSubRow`), swapping the operator dispatch for `.mul`
(token 13, slot `0x80019f8c` → MUL-int arm @0x80003834) and, crucially, the arm
TAIL: where `.sub` emits `sub a1,s3,a7` inline, `.mul` calls libgcc `__muldi3`
(`mv a1,s3; mv a0,a7; jal __muldi3; mv a1,a0; mv a0,s1; jal value_int; ld s3; j`).

The `__muldi3` seam is discharged by `muldi3_spec` (`Vsa/Sim/Muldi3Spec.lean`,
strengthened with a `sailOut` field so `value_int`'s `int_pre` sailOutput hypothesis
survives the intervening call).  The value bridge commutes `Wr*Wl → a*b`
(`mul_wrap_bridge`, using `BitVec.mul_comm`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- `__muldi3Loaded` survives a `writeMap8` disjoint from `[0x80004640, 0x80004664)`. -/
theorem loaded_muldi3_writeMap8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ 0x80004640 ∨ 0x80004664 ≤ a8) (h : Vsa.Sim.Code.__muldi3Loaded mem) :
    Vsa.Sim.Code.__muldi3Loaded (writeMap8 mem a8 d) := by
  simp only [Vsa.Sim.Code.__muldi3Loaded, Vsa.Sim.Code.__muldi3Chunk0] at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])

theorem blockC_mul
    (gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' st'' : Vsa.While.St) (a b : Int)
    (sp r sret aExpr : BitVec 64) (v8 v9 v18 v19 Wl : BitVec 64) (out0 : Array String)
    (m0 : Mem) :
    Triple
      (fun c =>
        TwoSubReturn gpre N A SL φf φc nf nc st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c ∧
        gpre Register.x8 = some aExpr ∧
        read32 c.σ.mem (aExpr.toNat + 8) = some 13 ∧      -- op token = binOpTok .mul
        MulSlotPinned c.σ.mem ∧
        (∀ k : Nat, ∃ w : BitVec 8, c.σ.mem[k]? = some w) ∧
        c.σ.regs.get? Register.x19 = some Wl ∧              -- s3 = LEFT payload word
        read64 c.σ.mem (sp.toNat - 960) = some Wl.toNat ∧   -- vl payload buffer = Wl
        read64 c.σ.mem (sp.toNat - 1088) = some (2#64 : BitVec 64).toNat ∧  -- respilled vl.kind
        -- === geometry ===
        aExpr.toNat % 4 = 0 ∧
        0x80000000 ≤ aExpr.toNat ∧ aExpr.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 8 ≤ aExpr.toNat ∧
        (aExpr.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat) ∧
        String.join out0.toList = st''.out ∧
        c.σ.sailOutput = out0 ∧
        sret.toNat % 8 = 0 ∧ 0x80000000 ≤ sret.toNat ∧ sret.toNat + 24 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ sret.toNat ∧
        (sret.toNat + 24 ≤ 0x8000280c ∨ 0x8000281c ≤ sret.toNat) ∧
        (sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat) ∧
        (sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat) ∧
        r.toNat % 4 = 0 ∧
        Value_intLoaded c.σ.mem ∧
        -- === the two MUL-specific extra conjuncts ===
        Vsa.Sim.Code.__muldi3Loaded c.σ.mem ∧
        (sp.toNat ≤ 0x80004640 ∨ 0x80004664 ≤ SL.lo) ∧   -- muldi3 code disjoint from stack
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        (sp.toNat ≤ 0x8000280c ∨ 0x8000281c ≤ SL.lo) ∧
        (opTableBase + 12 ≤ SL.lo ∨ sp.toNat ≤ opTableBase) ∧
        (SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi) ∧
        SL.lo + 1088 ≤ sp.toNat ∧ 0x80000000 ≤ SL.lo ∧ tohostAddr + 16 ≤ SL.lo ∧
        sp.toNat ≤ 0x100000000 ∧ sp.toNat % 8 = 0 ∧ SL.hi ≤ 0x100000000 ∧ sp.toNat ≤ SL.hi ∧
        g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
        g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧
        gpre Register.x19 = some v19 ∧ g Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x2 == R) = false →
          gpre R = g R))
      (fun c => ∃ (mpre : Mem) (φfm φcm φfe φce : Addr → Nat),
        PhiExtends φf φfm nf ∧
        PhiExtends φc φcm nc ∧
        PhiExtends φfm φfe st'.store.frames.size ∧
        PhiExtends φcm φce st'.store.closures.size ∧
        PreEpilogueVD g N A SL φfe φce st'' (.int (wrap64 (a * b))) sp r sret v8 v9 v18 out0 m0 mpre c) := by
  intro c hpre
  obtain ⟨hTS, hgx8, hopTok, hSlot, hFullPop, hX19, hWlBuf, hKindResp,
    hexprAl, hexprLo, hexprHi, hexprWin, hexprSL, houtStr, hout0eq,
    hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEvalCode, hraAl,
    hVint, hMuldi3, hmuldiStk, hcodeStk, hviStk, hTableStk, hsretInSL,
    hSLloSp, hSLlo, hSLwin, hsphiRam, hsp8, hSLhiRam, hspSLhi,
    hgv8, hgv9, hgv18, hgv2, hgprex19, hgx19, hbridge⟩ := hpre
  obtain ⟨hG, htick, hpc, hra, hs1, hsp, ⟨vmi, hmi⟩, hout, hframe,
    ⟨w19, hgprex19', hs3slot⟩, hstoreBundle, hcode,
    hslotRa, hslotS0, hslotS1, hslotS2, hMemExt, hmemframe⟩ := hTS
  have hw19 : w19 = v19 := by rw [hgprex19] at hgprex19'; exact (Option.some.inj hgprex19').symm
  obtain ⟨φfm, φcm, hpfm, hpcm, ⟨φcr, hpcr, hvalR⟩, ⟨φcl, hvalL⟩,
    φf', φc', hpf', hpc', hstore', hstoreSurv'⟩ := hstoreBundle
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- Phase-0: all scalar sp/SL arithmetic derived ONCE in a small-context lemma
  -- (`spArith`), not re-`omega`'d in the row's 60-hyp body (each such omega costs
  -- ~0.5–0.9s from context size — elab-wall memo).  `hSB`/`hEB` bundles built up
  -- front so `spArith` can consume them.
  have hSB : StackBounds sp SL := ⟨hSLloSp, hSLlo, hSLwin, hsp8, hsphiRam⟩
  have hEB : ExprBounds aExpr := ⟨hexprAl, hexprLo, hexprHi, hexprWin⟩
  have hAr : SpArith sp SL := spArith hSB
  have hsp1088 : 1088 ≤ sp.toNat := hAr.sp1088
  have hspLoc : 0x80000000 ≤ sp.toNat := hAr.spLo
  have hspHtifLoc : tohostAddr + 16 + 1088 ≤ sp.toNat := hAr.spHtif
  have hSLlo40 : SL.lo ≤ sp.toNat - 40 := hAr.SLlo40
  have hSLlo32 : SL.lo ≤ sp.toNat - 32 := hAr.SLlo32
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  have hx8c : c.σ.regs.get? Register.x8 = some aExpr :=
    (hframe Register.x8 (by decide) (by decide)).trans hgx8
  have hop8 : (aExpr + sign_extend (m := 64) (0x008#12)).toNat = aExpr.toNat + 8 := by
    have hs : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
      apply BitVec.eq_of_toNat_eq; decide
    rw [hs, BitVec.toNat_add]; have hv : (8#64 : BitVec 64).toNat = 8 := by decide
    rw [hv]; have := aExpr.isLt; rw [Nat.mod_eq_of_lt (by omega)]
  have hline4 : (aExpr + sign_extend (m := 64) (0x004#12)).toNat = aExpr.toNat + 4 := by
    have hs : (sign_extend (m := 64) (0x004#12) : BitVec 64) = 4#64 := by
      apply BitVec.eq_of_toNat_eq; decide
    rw [hs, BitVec.toNat_add]; have hv : (4#64 : BitVec 64).toNat = 4 := by decide
    rw [hv]; have := aExpr.isLt; rw [Nat.mod_eq_of_lt (by omega)]
  obtain ⟨ob0, ob1, ob2, ob3, hob0, hob1, hob2, hob3, hobrec⟩ :=
    read32_bytes c.σ.mem (aExpr.toNat + 8) 13 hopTok
  obtain ⟨lb0, hlb0⟩ := hFullPop (aExpr.toNat + 4)
  obtain ⟨lb1, hlb1⟩ := hFullPop (aExpr.toNat + 4 + 1)
  obtain ⟨lb2, hlb2⟩ := hFullPop (aExpr.toNat + 4 + 2)
  obtain ⟨lb3, hlb3⟩ := hFullPop (aExpr.toNat + 4 + 3)
  have hvalR' : ValueRepr c.σ.mem N φcr (sp.toNat - 944) (.int b) := hvalR
  obtain ⟨hkindR, pR, hpayR64, hpRb⟩ := valueRepr_int_pay64 hvalR'
  obtain ⟨rkb0, rkb1, rkb2, rkb3, hrkb0, hrkb1, hrkb2, hrkb3, hrkbrec⟩ :=
    read32_bytes c.σ.mem (sp.toNat - 944) 2 hkindR
  obtain ⟨rpb0, rpb1, rpb2, rpb3, rpb4, rpb5, rpb6, rpb7, hrpb0, hrpb1, hrpb2, hrpb3, hrpb4, hrpb5, hrpb6, hrpb7, hrprec⟩ :=
    read64_bytes c.σ.mem (sp.toNat - 944 + 8) pR hpayR64
  let Wr : BitVec 64 := sign_extend (m := 64)
    ((((((((rpb7.append rpb6).append rpb5).append rpb4).append rpb3).append rpb2).append rpb1).append rpb0) : BitVec (8*8))
  have hWrNat : Wr.toNat = pR := by
    show (sign_extend (m := 64)
      ((((((((rpb7.append rpb6).append rpb5).append rpb4).append rpb3).append rpb2).append rpb1).append rpb0) : BitVec (8*8))).toNat = pR
    rw [sext_full, word8_toNat_recon, hrprec]
  have hWr_toInt : Wr.toInt = b := by
    have hpe : Wr = BitVec.ofNat 64 pR := by rw [← hWrNat]; exact (ofNat_toNat_self64 Wr).symm
    rw [hpe]; exact hpRb
  have hvalL' : ValueRepr c.σ.mem N φcl (sp.toNat - 968) (.int a) := hvalL
  obtain ⟨hkindL, pL, hpayL64, hpLa⟩ := valueRepr_int_pay64 hvalL'
  have hpayL64' : read64 c.σ.mem (sp.toNat - 960) = some pL := by
    rw [hAr.e968] at hpayL64; exact hpayL64
  have hWlNat : Wl.toNat = pL := by
    have := hWlBuf.symm.trans hpayL64'; exact Option.some.inj this
  have hWl_toInt : Wl.toInt = a := by
    have hpe : Wl = BitVec.ofNat 64 pL := by rw [← hWlNat]; exact (ofNat_toNat_self64 Wl).symm
    rw [hpe]; exact hpLa
  have hopVal : (sign_extend (m := 64) ((((ob3.append ob2).append ob1).append ob0) : BitVec (8*4)))
      = (13#64 : BitVec 64) := by
    rw [sext_word_small _ 13 (by decide) (by rw [word_toNat_recon]; exact hobrec)]
  have hRkindVal : (sign_extend (m := 64) ((((rkb3.append rkb2).append rkb1).append rkb0) : BitVec (8*4)))
      = (2#64 : BitVec 64) := by
    rw [sext_word_small _ 2 (by decide) (by rw [word_toNat_recon]; exact hrkbrec)]
  have haddr144 : ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 944 :=
    spill_addr sp (0x090#12) 944 (by decide) (by decide) hsp1088
  have haddr152 : ((sp - 1088#64) + sign_extend (m := 64) (0x098#12)).toNat = sp.toNat - 936 :=
    spill_addr sp (0x098#12) 936 (by decide) (by decide) hsp1088
  have haddr120 : ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat = sp.toNat - 968 :=
    spill_addr sp (0x078#12) 968 (by decide) (by decide) hsp1088
  have haddr128 : ((sp - 1088#64) + sign_extend (m := 64) (0x080#12)).toNat = sp.toNat - 960 :=
    spill_addr sp (0x080#12) 960 (by decide) (by decide) hsp1088
  have haddr136 : ((sp - 1088#64) + sign_extend (m := 64) (0x088#12)).toNat = sp.toNat - 952 :=
    spill_addr sp (0x088#12) 952 (by decide) (by decide) hsp1088
  have haddr160 : ((sp - 1088#64) + sign_extend (m := 64) (0x0a0#12)).toNat = sp.toNat - 928 :=
    spill_addr sp (0x0a0#12) 928 (by decide) (by decide) hsp1088
  have haddr0 : ((sp - 1088#64) + sign_extend (m := 64) (0x000#12)).toNat = sp.toNat - 1088 := by
    have : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by apply BitVec.eq_of_toNat_eq; decide
    rw [this, BitVec.add_zero]; exact hspsub
  have haddr240 : ((sp - 1088#64) + sign_extend (m := 64) (0x0f0#12)).toNat = sp.toNat - 848 :=
    spill_addr sp (0x0f0#12) 848 (by decide) (by decide) hsp1088
  have haddr248 : ((sp - 1088#64) + sign_extend (m := 64) (0x0f8#12)).toNat = sp.toNat - 840 :=
    spill_addr sp (0x0f8#12) 840 (by decide) (by decide) hsp1088
  have haddr256 : ((sp - 1088#64) + sign_extend (m := 64) (0x100#12)).toNat = sp.toNat - 832 :=
    spill_addr sp (0x100#12) 832 (by decide) (by decide) hsp1088
  have haddr1048 : ((sp - 1088#64) + sign_extend (m := 64) (0x418#12)).toNat = sp.toNat - 40 :=
    spill_addr sp (0x418#12) 40 (by decide) (by decide) hsp1088
  -- ── Phase-0 geometry precompute: from the front-built bounds bundles derive
  -- each distinct slot's geometry facts (lo/hi/ht/win/al) in ONE `omega` (over the
  -- tiny bundle context) instead of re-omega'ing at every load/store site. ──────
  -- expr-relative operand fetches (4-byte reads at aExpr+8 / aExpr+4)
  have gExpr8 := exprGeom4 hEB 8 (by decide) (by decide)
  have gExpr4 := exprGeom4 hEB 4 (by decide) (by decide)
  -- sp-relative spill slots (K = 1088 - off); width 8 covers every 4-byte read too.
  have g1088 := slotGeom8 hSB 1088 (by decide) (by decide) (by decide)
  have g968  := slotGeom8 hSB 968  (by decide) (by decide) (by decide)
  have g960  := slotGeom8 hSB 960  (by decide) (by decide) (by decide)
  have g952  := slotGeom8 hSB 952  (by decide) (by decide) (by decide)
  have g944  := slotGeom8 hSB 944  (by decide) (by decide) (by decide)
  have g936  := slotGeom8 hSB 936  (by decide) (by decide) (by decide)
  have g928  := slotGeom8 hSB 928  (by decide) (by decide) (by decide)
  have g848  := slotGeom8 hSB 848  (by decide) (by decide) (by decide)
  have g840  := slotGeom8 hSB 840  (by decide) (by decide) (by decide)
  have g832  := slotGeom8 hSB 832  (by decide) (by decide) (by decide)
  have g40   := slotGeom8 hSB 40   (by decide) (by decide) (by decide)
  -- Phase-0: precompute the three store slots' disjointness from each static
  -- region (code / value_int / __muldi3) as ONE bundle each (three added hyps,
  -- not nine `have`s — context-bloat law), from the single `hXStk` per region.
  -- Every store site then projects `.d848/.d840/.d832` instead of re-`omega`ing.
  have hcodeD : StoreRegionDis sp SL 0x80003164 0x80003fe0 := storeRegionDis hSB _ _ hcodeStk
  have hviD   : StoreRegionDis sp SL 0x8000280c 0x8000281c := storeRegionDis hSB _ _ hviStk
  have hmdD   : StoreRegionDis sp SL 0x80004640 0x80004664 := storeRegionDis hSB _ _ hmuldiStk
  -- store slots ⊂ windows + s3-slot inter-slot disjointness — packed in ONE
  -- `SlotWindows` hypothesis (context-bloat law: minimise added `have`s), feeding
  -- `slotDisj_of_notInSL/notInStack/topWin` at every per-`k` mem-frame site,
  -- killing 20 in-body omegas for the price of ONE added hypothesis.
  have hSW : SlotWindows sp SL := slotWindows hSB hspSLhi
  -- the arm's five `hnXX` v2-relative address normalisations (`sp-K = v2+off`),
  -- derived once in a small-context lemma (`armNorms`), not omega'd in the body.
  have hNorm := armNorms hsp1088 hspsub
  -- arm right-payload byte-shift equalities + epilogue restore-slot window
  -- memberships, each derived once (small-context) instead of per-byte in the body.
  have hRpb := rpbShift (by omega : (944 : Nat) ≤ sp.toNat)
  have hTopW := topSlotWin (by omega : (32 : Nat) ≤ sp.toNat)
  have hobv : ob0.toNat = 13 ∧ ob1.toNat = 0 ∧ ob2.toNat = 0 ∧ ob3.toNat = 0 :=
    word32_split (by decide) hobrec
  have hob0' : c.σ.mem[aExpr.toNat + 8]? = some (0x0d#8) := by
    have hb : ob0 = 0x0d#8 := by apply BitVec.eq_of_toNat_eq; rw [hobv.1]; rfl
    rw [← hb]; exact hob0
  have hob1' : c.σ.mem[aExpr.toNat + 8 + 1]? = some (0#8) := by
    have hb : ob1 = 0#8 := by apply BitVec.eq_of_toNat_eq; rw [hobv.2.1]; rfl
    rw [← hb]; exact hob1
  have hob2' : c.σ.mem[aExpr.toNat + 8 + 2]? = some (0#8) := by
    have hb : ob2 = 0#8 := by apply BitVec.eq_of_toNat_eq; rw [hobv.2.2.1]; rfl
    rw [← hb]; exact hob2
  have hob3' : c.σ.mem[aExpr.toNat + 8 + 3]? = some (0#8) := by
    have hb : ob3 = 0#8 := by apply BitVec.eq_of_toNat_eq; rw [hobv.2.2.2]; rfl
    rw [← hb]; exact hob3
  obtain ⟨kb0, kb1, kb2, kb3, kb4, kb5, kb6, kb7, hkb0, hkb1, hkb2, hkb3, hkb4, hkb5, hkb6, hkb7, hkbrec⟩ :=
    read64_bytes c.σ.mem (sp.toNat - 1088) ((2#64 : BitVec 64).toNat) hKindResp
  have hkVal : bytesVal MKind.ld [kb0, kb1, kb2, kb3, kb4, kb5, kb6, kb7] = (2#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq
    show (sign_extend (m := 64)
      ((((((((kb7.append kb6).append kb5).append kb4).append kb3).append kb2).append kb1).append kb0) : BitVec (8*8))).toNat = _
    rw [sext_full, word8_toNat_recon, hkbrec]
  -- ── chain 0x8000351c → 0x80003834 (evalMulChain_run) ────────────────────────
  obtain ⟨sC0, iC0, hStepsChain, hiC0, hGC0, hpcC0, hx10C0, hx12C0, hx16C0, hx17C0,
      hx2C0, hx9C0, hx19C0, hmemC0eq, houtC0, hmiC0ex, hframeChain⟩ :=
    evalMulChain_run c.σ c.tick c.steps vmi (sp - 1088#64) aExpr sret Wl
      lb0 lb1 lb2 lb3 rkb0 rkb1 rkb2 rkb3 rpb0 rpb1 rpb2 rpb3 rpb4 rpb5 rpb6 rpb7
      kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7
      hG hpc hmi hsp hx8c hs1 hX19 hcode hRkindVal hkVal
      (by rw [hop8]; first | exact gExpr8.1 | exact gExpr8.2.1 | exact gExpr8.2.2.1 | exact gExpr8.2.2.2) (by rw [hop8]; first | exact gExpr8.1 | exact gExpr8.2.1 | exact gExpr8.2.2.1 | exact gExpr8.2.2.2)
      (by rw [hop8]; first | exact gExpr8.1 | exact gExpr8.2.1 | exact gExpr8.2.2.1 | exact gExpr8.2.2.2) (by rw [hop8]; first | exact gExpr8.1 | exact gExpr8.2.1 | exact gExpr8.2.2.1 | exact gExpr8.2.2.2)
      (by rw [hop8]; exact hob0') (by rw [hop8]; exact hob1')
      (by rw [hop8]; exact hob2') (by rw [hop8]; exact hob3')
      (by rw [hline4]; first | exact gExpr4.1 | exact gExpr4.2.1 | exact gExpr4.2.2.1 | exact gExpr4.2.2.2) (by rw [hline4]; first | exact gExpr4.1 | exact gExpr4.2.1 | exact gExpr4.2.2.1 | exact gExpr4.2.2.2)
      (by rw [hline4]; first | exact gExpr4.1 | exact gExpr4.2.1 | exact gExpr4.2.2.1 | exact gExpr4.2.2.2) (by rw [hline4]; first | exact gExpr4.1 | exact gExpr4.2.1 | exact gExpr4.2.2.1 | exact gExpr4.2.2.2)
      (by rw [hline4]; exact hlb0) (by rw [hline4]; exact hlb1)
      (by rw [hline4]; exact hlb2) (by rw [hline4]; exact hlb3)
      (by rw [haddr144]; first | exact g944.lo | exact g944.hi4 | exact g944.hi8 | exact g944.ht4 | exact g944.ht8 | exact g944.win | exact g944.al4 | exact g944.al8) (by rw [haddr144]; first | exact g944.lo | exact g944.hi4 | exact g944.hi8 | exact g944.ht4 | exact g944.ht8 | exact g944.win | exact g944.al4 | exact g944.al8)
      (by rw [haddr144]; first | exact g944.lo | exact g944.hi4 | exact g944.hi8 | exact g944.ht4 | exact g944.ht8 | exact g944.win | exact g944.al4 | exact g944.al8) (by rw [haddr144]; first | exact g944.lo | exact g944.hi4 | exact g944.hi8 | exact g944.ht4 | exact g944.ht8 | exact g944.win | exact g944.al4 | exact g944.al8)
      (by rw [haddr144]; exact hrkb0) (by rw [haddr144]; exact hrkb1)
      (by rw [haddr144]; exact hrkb2) (by rw [haddr144]; exact hrkb3)
      (by rw [haddr152]; first | exact g936.lo | exact g936.hi4 | exact g936.hi8 | exact g936.ht4 | exact g936.ht8 | exact g936.win | exact g936.al4 | exact g936.al8) (by rw [haddr152]; first | exact g936.lo | exact g936.hi4 | exact g936.hi8 | exact g936.ht4 | exact g936.ht8 | exact g936.win | exact g936.al4 | exact g936.al8)
      (by rw [haddr152]; first | exact g936.lo | exact g936.hi4 | exact g936.hi8 | exact g936.ht4 | exact g936.ht8 | exact g936.win | exact g936.al4 | exact g936.al8) (by rw [haddr152]; first | exact g936.lo | exact g936.hi4 | exact g936.hi8 | exact g936.ht4 | exact g936.ht8 | exact g936.win | exact g936.al4 | exact g936.al8)
      (by rw [haddr152, hRpb.1]; exact hrpb0)
      (by rw [haddr152, hRpb.2.1]; exact hrpb1)
      (by rw [haddr152, hRpb.2.2.1]; exact hrpb2)
      (by rw [haddr152, hRpb.2.2.2.1]; exact hrpb3)
      (by rw [haddr152, hRpb.2.2.2.2.1]; exact hrpb4)
      (by rw [haddr152, hRpb.2.2.2.2.2.1]; exact hrpb5)
      (by rw [haddr152, hRpb.2.2.2.2.2.2.1]; exact hrpb6)
      (by rw [haddr152, hRpb.2.2.2.2.2.2.2]; exact hrpb7)
      hSlot
      (by rw [haddr0]; first | exact g1088.lo | exact g1088.hi4 | exact g1088.hi8 | exact g1088.ht4 | exact g1088.ht8 | exact g1088.win | exact g1088.al4 | exact g1088.al8) (by rw [haddr0]; first | exact g1088.lo | exact g1088.hi4 | exact g1088.hi8 | exact g1088.ht4 | exact g1088.ht8 | exact g1088.win | exact g1088.al4 | exact g1088.al8)
      (by rw [haddr0]; first | exact g1088.lo | exact g1088.hi4 | exact g1088.hi8 | exact g1088.ht4 | exact g1088.ht8 | exact g1088.win | exact g1088.al4 | exact g1088.al8) (by rw [haddr0]; first | exact g1088.lo | exact g1088.hi4 | exact g1088.hi8 | exact g1088.ht4 | exact g1088.ht8 | exact g1088.win | exact g1088.al4 | exact g1088.al8)
      (by rw [haddr0]; exact hkb0) (by rw [haddr0]; exact hkb1)
      (by rw [haddr0]; exact hkb2) (by rw [haddr0]; exact hkb3)
      (by rw [haddr0]; exact hkb4) (by rw [haddr0]; exact hkb5)
      (by rw [haddr0]; exact hkb6) (by rw [haddr0]; exact hkb7)
      htick
  obtain ⟨vmC0, hmiC0⟩ := hmiC0ex
  have hcodeC0 : Vsa.Sim.Code.Eval_exprLoaded sC0.mem := by rw [hmemC0eq]; exact hcode
  obtain ⟨fa0, hfa0⟩ := hFullPop (sp.toNat - 968)
  obtain ⟨fa1, hfa1⟩ := hFullPop (sp.toNat - 968 + 1)
  obtain ⟨fa2, hfa2⟩ := hFullPop (sp.toNat - 968 + 2)
  obtain ⟨fa3, hfa3⟩ := hFullPop (sp.toNat - 968 + 3)
  obtain ⟨fa4, hfa4⟩ := hFullPop (sp.toNat - 968 + 4)
  obtain ⟨fa5, hfa5⟩ := hFullPop (sp.toNat - 968 + 5)
  obtain ⟨fa6, hfa6⟩ := hFullPop (sp.toNat - 968 + 6)
  obtain ⟨fa7, hfa7⟩ := hFullPop (sp.toNat - 968 + 7)
  obtain ⟨fb0, hfb0⟩ := hFullPop (sp.toNat - 952)
  obtain ⟨fb1, hfb1⟩ := hFullPop (sp.toNat - 952 + 1)
  obtain ⟨fb2, hfb2⟩ := hFullPop (sp.toNat - 952 + 2)
  obtain ⟨fb3, hfb3⟩ := hFullPop (sp.toNat - 952 + 3)
  obtain ⟨fb4, hfb4⟩ := hFullPop (sp.toNat - 952 + 4)
  obtain ⟨fb5, hfb5⟩ := hFullPop (sp.toNat - 952 + 5)
  obtain ⟨fb6, hfb6⟩ := hFullPop (sp.toNat - 952 + 6)
  obtain ⟨fb7, hfb7⟩ := hFullPop (sp.toNat - 952 + 7)
  obtain ⟨fc0, hfc0⟩ := hFullPop (sp.toNat - 944)
  obtain ⟨fc1, hfc1⟩ := hFullPop (sp.toNat - 944 + 1)
  obtain ⟨fc2, hfc2⟩ := hFullPop (sp.toNat - 944 + 2)
  obtain ⟨fc3, hfc3⟩ := hFullPop (sp.toNat - 944 + 3)
  obtain ⟨fc4, hfc4⟩ := hFullPop (sp.toNat - 944 + 4)
  obtain ⟨fc5, hfc5⟩ := hFullPop (sp.toNat - 944 + 5)
  obtain ⟨fc6, hfc6⟩ := hFullPop (sp.toNat - 944 + 6)
  obtain ⟨fc7, hfc7⟩ := hFullPop (sp.toNat - 944 + 7)
  obtain ⟨fd0, hfd0⟩ := hFullPop (sp.toNat - 936)
  obtain ⟨fd1, hfd1⟩ := hFullPop (sp.toNat - 936 + 1)
  obtain ⟨fd2, hfd2⟩ := hFullPop (sp.toNat - 936 + 2)
  obtain ⟨fd3, hfd3⟩ := hFullPop (sp.toNat - 936 + 3)
  obtain ⟨fd4, hfd4⟩ := hFullPop (sp.toNat - 936 + 4)
  obtain ⟨fd5, hfd5⟩ := hFullPop (sp.toNat - 936 + 5)
  obtain ⟨fd6, hfd6⟩ := hFullPop (sp.toNat - 936 + 6)
  obtain ⟨fd7, hfd7⟩ := hFullPop (sp.toNat - 936 + 7)
  obtain ⟨fe0, hfe0⟩ := hFullPop (sp.toNat - 928)
  obtain ⟨fe1, hfe1⟩ := hFullPop (sp.toNat - 928 + 1)
  obtain ⟨fe2, hfe2⟩ := hFullPop (sp.toNat - 928 + 2)
  obtain ⟨fe3, hfe3⟩ := hFullPop (sp.toNat - 928 + 3)
  obtain ⟨fe4, hfe4⟩ := hFullPop (sp.toNat - 928 + 4)
  obtain ⟨fe5, hfe5⟩ := hFullPop (sp.toNat - 928 + 5)
  obtain ⟨fe6, hfe6⟩ := hFullPop (sp.toNat - 928 + 6)
  obtain ⟨fe7, hfe7⟩ := hFullPop (sp.toNat - 928 + 7)
  -- ── arm 0x80003834 → 0x80003868 (evalMulArm_run) ────────────────────────────
  obtain ⟨τ13, j13, D1, D2, D3, D4, D5, hStepsArm, hi13, hGτ13, hmemArm, hpcτ13,
      hx17τ13, hspτ13, hs1τ13, hx19τ13, hx12τ13, hx13τ13ex, houtArm, hmiArmex, hframeArm⟩ :=
    evalMulArm_run sC0 iC0 (c.steps + 16) vmC0 (sp - 1088#64) (13#64) sret Wl Wr
      fa0 fa1 fa2 fa3 fa4 fa5 fa6 fa7 fb0 fb1 fb2 fb3 fb4 fb5 fb6 fb7
      fc0 fc1 fc2 fc3 fc4 fc5 fc6 fc7 fd0 fd1 fd2 fd3 fd4 fd5 fd6 fd7
      fe0 fe1 fe2 fe3 fe4 fe5 fe6 fe7
      hGC0 hpcC0 hmiC0 hx2C0 hx9C0 hx10C0 hx12C0 hx16C0 hx17C0 hx19C0 hcodeC0
      (by rw [haddr144]; exact hNorm.1) (by rw [haddr152]; exact hNorm.2.1)
      (by rw [haddr160]; exact hNorm.2.2.1) (by rw [haddr240]; exact hNorm.2.2.2.1)
      (by rw [haddr256]; exact hNorm.2.2.2.2)
      (by rw [haddr240]; exact hcodeD.d848)
      (by rw [haddr248]; exact hcodeD.d840)
      (by rw [haddr256]; exact hcodeD.d832)
      (by rw [haddr120]; first | exact g968.lo | exact g968.hi4 | exact g968.hi8 | exact g968.ht4 | exact g968.ht8 | exact g968.win | exact g968.al4 | exact g968.al8) (by rw [haddr120]; first | exact g968.lo | exact g968.hi4 | exact g968.hi8 | exact g968.ht4 | exact g968.ht8 | exact g968.win | exact g968.al4 | exact g968.al8)
      (by rw [haddr120]; first | exact g968.lo | exact g968.hi4 | exact g968.hi8 | exact g968.ht4 | exact g968.ht8 | exact g968.win | exact g968.al4 | exact g968.al8) (by rw [haddr120]; first | exact g968.lo | exact g968.hi4 | exact g968.hi8 | exact g968.ht4 | exact g968.ht8 | exact g968.win | exact g968.al4 | exact g968.al8)
      (by rw [haddr120, hmemC0eq]; exact hfa0) (by rw [haddr120, hmemC0eq]; exact hfa1)
      (by rw [haddr120, hmemC0eq]; exact hfa2) (by rw [haddr120, hmemC0eq]; exact hfa3)
      (by rw [haddr120, hmemC0eq]; exact hfa4) (by rw [haddr120, hmemC0eq]; exact hfa5)
      (by rw [haddr120, hmemC0eq]; exact hfa6) (by rw [haddr120, hmemC0eq]; exact hfa7)
      (by rw [haddr136]; first | exact g952.lo | exact g952.hi4 | exact g952.hi8 | exact g952.ht4 | exact g952.ht8 | exact g952.win | exact g952.al4 | exact g952.al8) (by rw [haddr136]; first | exact g952.lo | exact g952.hi4 | exact g952.hi8 | exact g952.ht4 | exact g952.ht8 | exact g952.win | exact g952.al4 | exact g952.al8)
      (by rw [haddr136]; first | exact g952.lo | exact g952.hi4 | exact g952.hi8 | exact g952.ht4 | exact g952.ht8 | exact g952.win | exact g952.al4 | exact g952.al8) (by rw [haddr136]; first | exact g952.lo | exact g952.hi4 | exact g952.hi8 | exact g952.ht4 | exact g952.ht8 | exact g952.win | exact g952.al4 | exact g952.al8)
      (by rw [haddr136, hmemC0eq]; exact hfb0) (by rw [haddr136, hmemC0eq]; exact hfb1)
      (by rw [haddr136, hmemC0eq]; exact hfb2) (by rw [haddr136, hmemC0eq]; exact hfb3)
      (by rw [haddr136, hmemC0eq]; exact hfb4) (by rw [haddr136, hmemC0eq]; exact hfb5)
      (by rw [haddr136, hmemC0eq]; exact hfb6) (by rw [haddr136, hmemC0eq]; exact hfb7)
      (by rw [haddr144]; first | exact g944.lo | exact g944.hi4 | exact g944.hi8 | exact g944.ht4 | exact g944.ht8 | exact g944.win | exact g944.al4 | exact g944.al8) (by rw [haddr144]; first | exact g944.lo | exact g944.hi4 | exact g944.hi8 | exact g944.ht4 | exact g944.ht8 | exact g944.win | exact g944.al4 | exact g944.al8)
      (by rw [haddr144]; first | exact g944.lo | exact g944.hi4 | exact g944.hi8 | exact g944.ht4 | exact g944.ht8 | exact g944.win | exact g944.al4 | exact g944.al8) (by rw [haddr144]; first | exact g944.lo | exact g944.hi4 | exact g944.hi8 | exact g944.ht4 | exact g944.ht8 | exact g944.win | exact g944.al4 | exact g944.al8)
      (by rw [haddr144, hmemC0eq]; exact hfc0) (by rw [haddr144, hmemC0eq]; exact hfc1)
      (by rw [haddr144, hmemC0eq]; exact hfc2) (by rw [haddr144, hmemC0eq]; exact hfc3)
      (by rw [haddr144, hmemC0eq]; exact hfc4) (by rw [haddr144, hmemC0eq]; exact hfc5)
      (by rw [haddr144, hmemC0eq]; exact hfc6) (by rw [haddr144, hmemC0eq]; exact hfc7)
      (by rw [haddr152]; first | exact g936.lo | exact g936.hi4 | exact g936.hi8 | exact g936.ht4 | exact g936.ht8 | exact g936.win | exact g936.al4 | exact g936.al8) (by rw [haddr152]; first | exact g936.lo | exact g936.hi4 | exact g936.hi8 | exact g936.ht4 | exact g936.ht8 | exact g936.win | exact g936.al4 | exact g936.al8)
      (by rw [haddr152]; first | exact g936.lo | exact g936.hi4 | exact g936.hi8 | exact g936.ht4 | exact g936.ht8 | exact g936.win | exact g936.al4 | exact g936.al8) (by rw [haddr152]; first | exact g936.lo | exact g936.hi4 | exact g936.hi8 | exact g936.ht4 | exact g936.ht8 | exact g936.win | exact g936.al4 | exact g936.al8)
      (by rw [haddr152, hmemC0eq]; exact hfd0) (by rw [haddr152, hmemC0eq]; exact hfd1)
      (by rw [haddr152, hmemC0eq]; exact hfd2) (by rw [haddr152, hmemC0eq]; exact hfd3)
      (by rw [haddr152, hmemC0eq]; exact hfd4) (by rw [haddr152, hmemC0eq]; exact hfd5)
      (by rw [haddr152, hmemC0eq]; exact hfd6) (by rw [haddr152, hmemC0eq]; exact hfd7)
      (by rw [haddr160]; first | exact g928.lo | exact g928.hi4 | exact g928.hi8 | exact g928.ht4 | exact g928.ht8 | exact g928.win | exact g928.al4 | exact g928.al8) (by rw [haddr160]; first | exact g928.lo | exact g928.hi4 | exact g928.hi8 | exact g928.ht4 | exact g928.ht8 | exact g928.win | exact g928.al4 | exact g928.al8)
      (by rw [haddr160]; first | exact g928.lo | exact g928.hi4 | exact g928.hi8 | exact g928.ht4 | exact g928.ht8 | exact g928.win | exact g928.al4 | exact g928.al8) (by rw [haddr160]; first | exact g928.lo | exact g928.hi4 | exact g928.hi8 | exact g928.ht4 | exact g928.ht8 | exact g928.win | exact g928.al4 | exact g928.al8)
      (by rw [haddr160, hmemC0eq]; exact hfe0) (by rw [haddr160, hmemC0eq]; exact hfe1)
      (by rw [haddr160, hmemC0eq]; exact hfe2) (by rw [haddr160, hmemC0eq]; exact hfe3)
      (by rw [haddr160, hmemC0eq]; exact hfe4) (by rw [haddr160, hmemC0eq]; exact hfe5)
      (by rw [haddr160, hmemC0eq]; exact hfe6) (by rw [haddr160, hmemC0eq]; exact hfe7)
      (by rw [haddr240]; first | exact g848.lo | exact g848.hi4 | exact g848.hi8 | exact g848.ht4 | exact g848.ht8 | exact g848.win | exact g848.al4 | exact g848.al8) (by rw [haddr240]; first | exact g848.lo | exact g848.hi4 | exact g848.hi8 | exact g848.ht4 | exact g848.ht8 | exact g848.win | exact g848.al4 | exact g848.al8)
      (by rw [haddr240]; first | exact g848.lo | exact g848.hi4 | exact g848.hi8 | exact g848.ht4 | exact g848.ht8 | exact g848.win | exact g848.al4 | exact g848.al8) (by rw [haddr240]; first | exact g848.lo | exact g848.hi4 | exact g848.hi8 | exact g848.ht4 | exact g848.ht8 | exact g848.win | exact g848.al4 | exact g848.al8)
      (by rw [haddr248]; first | exact g840.lo | exact g840.hi4 | exact g840.hi8 | exact g840.ht4 | exact g840.ht8 | exact g840.win | exact g840.al4 | exact g840.al8) (by rw [haddr248]; first | exact g840.lo | exact g840.hi4 | exact g840.hi8 | exact g840.ht4 | exact g840.ht8 | exact g840.win | exact g840.al4 | exact g840.al8)
      (by rw [haddr248]; first | exact g840.lo | exact g840.hi4 | exact g840.hi8 | exact g840.ht4 | exact g840.ht8 | exact g840.win | exact g840.al4 | exact g840.al8) (by rw [haddr248]; first | exact g840.lo | exact g840.hi4 | exact g840.hi8 | exact g840.ht4 | exact g840.ht8 | exact g840.win | exact g840.al4 | exact g840.al8)
      (by rw [haddr256]; first | exact g832.lo | exact g832.hi4 | exact g832.hi8 | exact g832.ht4 | exact g832.ht8 | exact g832.win | exact g832.al4 | exact g832.al8) (by rw [haddr256]; first | exact g832.lo | exact g832.hi4 | exact g832.hi8 | exact g832.ht4 | exact g832.ht8 | exact g832.win | exact g832.al4 | exact g832.al8)
      (by rw [haddr256]; first | exact g832.lo | exact g832.hi4 | exact g832.hi8 | exact g832.ht4 | exact g832.ht8 | exact g832.win | exact g832.al4 | exact g832.al8) (by rw [haddr256]; first | exact g832.lo | exact g832.hi4 | exact g832.hi8 | exact g832.ht4 | exact g832.ht8 | exact g832.win | exact g832.al4 | exact g832.al8)
      hiC0
  obtain ⟨vmiτ13, hmiτ13⟩ := hmiArmex
  have hmemB2 : τ13.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 c.σ.mem
      (sp.toNat - 848) D1) (sp.toNat - 832) D2) (sp.toNat - 848) D3) (sp.toNat - 840) D4)
      (sp.toNat - 832) D5 := by
    rw [hmemArm, hmemC0eq]; simp only [haddr240, haddr248, haddr256]
  let m1 : Mem := writeMap8 c.σ.mem (sp.toNat - 848) D1
  let m2 : Mem := writeMap8 m1 (sp.toNat - 832) D2
  let m3 : Mem := writeMap8 m2 (sp.toNat - 848) D3
  let m4 : Mem := writeMap8 m3 (sp.toNat - 840) D4
  let m5 : Mem := writeMap8 m4 (sp.toNat - 832) D5
  have hmemτ13e : τ13.mem = m5 := hmemB2
  have hcodem1 : Vsa.Sim.Code.Eval_exprLoaded m1 :=
    loaded_eval_expr_agreeP c.σ.mem m1
      (fun k hk => (getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) k D1
        (slotDisj_of_inRegion hcodeD.d848 hk)).symm) hcode
  have hcodem2 : Vsa.Sim.Code.Eval_exprLoaded m2 :=
    loaded_eval_expr_agreeP m1 m2
      (fun k hk => (getElem_writeMap8_disjoint m1 (sp.toNat - 832) k D2
        (slotDisj_of_inRegion hcodeD.d832 hk)).symm) hcodem1
  have hcodem3 : Vsa.Sim.Code.Eval_exprLoaded m3 :=
    loaded_eval_expr_agreeP m2 m3
      (fun k hk => (getElem_writeMap8_disjoint m2 (sp.toNat - 848) k D3
        (slotDisj_of_inRegion hcodeD.d848 hk)).symm) hcodem2
  have hcodem4 : Vsa.Sim.Code.Eval_exprLoaded m4 :=
    loaded_eval_expr_agreeP m3 m4
      (fun k hk => (getElem_writeMap8_disjoint m3 (sp.toNat - 840) k D4
        (slotDisj_of_inRegion hcodeD.d840 hk)).symm) hcodem3
  have hcodem5 : Vsa.Sim.Code.Eval_exprLoaded m5 :=
    loaded_eval_expr_agreeP m4 m5
      (fun k hk => (getElem_writeMap8_disjoint m4 (sp.toNat - 832) k D5
        (slotDisj_of_inRegion hcodeD.d832 hk)).symm) hcodem4
  have hcodeτ13 : Vsa.Sim.Code.Eval_exprLoaded τ13.mem := by rw [hmemτ13e]; exact hcodem5
  -- `Value_intLoaded m5` and `__muldi3Loaded m5` (survive the 5 stack stores)
  have hVint5 : Value_intLoaded m5 := by
    have h1 : Value_intLoaded m1 := loaded_int_writeMap8 c.σ.mem (sp.toNat - 848) D1 hviD.d848 hVint
    have h2 : Value_intLoaded m2 := loaded_int_writeMap8 m1 (sp.toNat - 832) D2 hviD.d832 h1
    have h3 : Value_intLoaded m3 := loaded_int_writeMap8 m2 (sp.toNat - 848) D3 hviD.d848 h2
    have h4 : Value_intLoaded m4 := loaded_int_writeMap8 m3 (sp.toNat - 840) D4 hviD.d840 h3
    exact loaded_int_writeMap8 m4 (sp.toNat - 832) D5 hviD.d832 h4
  have hMuldi35 : Vsa.Sim.Code.__muldi3Loaded m5 := by
    have h1 : Vsa.Sim.Code.__muldi3Loaded m1 := loaded_muldi3_writeMap8 c.σ.mem (sp.toNat - 848) D1 hmdD.d848 hMuldi3
    have h2 : Vsa.Sim.Code.__muldi3Loaded m2 := loaded_muldi3_writeMap8 m1 (sp.toNat - 832) D2 hmdD.d832 h1
    have h3 : Vsa.Sim.Code.__muldi3Loaded m3 := loaded_muldi3_writeMap8 m2 (sp.toNat - 848) D3 hmdD.d848 h2
    have h4 : Vsa.Sim.Code.__muldi3Loaded m4 := loaded_muldi3_writeMap8 m3 (sp.toNat - 840) D4 hmdD.d840 h3
    exact loaded_muldi3_writeMap8 m4 (sp.toNat - 832) D5 hmdD.d832 h4
  have houtτ13 : τ13.sailOutput = out0 := houtArm.trans (houtC0.trans hout0eq)
  let u16 : Nat := c.steps + 16
  have hLadderSteps : Steps ⟨c.σ, c.tick, c.steps⟩ ⟨τ13, j13, u16 + 13⟩ :=
    hStepsChain.trans hStepsArm
  have hLadderFrame : ∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
      τ13.regs.get? R = c.σ.regs.get? R := by
    intro R hR he8
    exact (hframeArm R hR he8).trans (hframeChain R hR he8)
  --------------------------------------------------------------------------------
  -- 0x80003868: mv a1,s3 → x11 := Wl
  --------------------------------------------------------------------------------
  obtain ⟨τ14, j14, ht14, hj14, hGτ14, hmemτ14, hoτ14⟩ :=
    site_80003868_ee τ13 j13 (u16 + 13) (0x80003868#64) vmiτ13 Wl
      hGτ13 hpcτ13 hmiτ13 hx19τ13 hcodeτ13 rfl hi13
  have hstepτ14 : Step ⟨τ13, j13, u16 + 13⟩ ⟨τ14, j14, u16 + 13 + 1⟩ := ht14
  have hmemτ14e : τ14.mem = m5 := by rw [hmemτ14]; exact hmemτ13e
  have hpcτ14 : τ14.regs.get? Register.PC = some (0x8000386c#64) := by
    have := obs_alu_pc hoτ14
    rwa [show BitVec.addInt (0x80003868#64) 4 = (0x8000386c#64 : BitVec 64) from by decide] at this
  have hx11τ14 : τ14.regs.get? Register.x11 = some Wl := by
    have := obs_alu_rd hoτ14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (Wl + sign_extend (m := 64) (0x000#12)) = Wl from by rw [sext_zero, BitVec.add_zero]] at this
  have hx17τ14 : τ14.regs.get? Register.x17 = some Wr := obs_alu_other hoτ14 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ13
  have hs1τ14 : τ14.regs.get? Register.x9 = some sret := obs_alu_other hoτ14 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ13
  have hspτ14 : τ14.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ14 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ13
  have hx19τ14 : τ14.regs.get? Register.x19 = some Wl := obs_alu_other hoτ14 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ13
  have hx12τ14 : τ14.regs.get? Register.x12 = some (13#64) := obs_alu_other hoτ14 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ13
  have hx13τ14ex : ∃ w, τ14.regs.get? Register.x13 = some w := by
    obtain ⟨w13, hw13⟩ := hx13τ13ex
    exact ⟨w13, obs_alu_other hoτ14 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw13⟩
  obtain ⟨vmiτ14, hmiτ14⟩ := obs_alu_minstret hoτ14
  have houtτ14 : τ14.sailOutput = out0 := by rw [hoτ14.out, sailOutput_sigmaPost_alu]; exact houtτ13
  have hcodeτ14 : Eval_exprLoaded τ14.mem := by rw [hmemτ14e]; exact hcodem5
  --------------------------------------------------------------------------------
  -- 0x8000386c: mv a0,a7 → x10 := Wr
  --------------------------------------------------------------------------------
  obtain ⟨τ15, j15, ht15, hj15, hGτ15, hmemτ15, hoτ15⟩ :=
    site_8000386c_ee τ14 j14 (u16 + 13 + 1) (0x8000386c#64) vmiτ14 Wr
      hGτ14 hpcτ14 hmiτ14 hx17τ14 hcodeτ14 rfl hj14
  have hstepτ15 : Step ⟨τ14, j14, u16 + 13 + 1⟩ ⟨τ15, j15, u16 + 13 + 1 + 1⟩ := ht15
  have hmemτ15e : τ15.mem = m5 := by rw [hmemτ15]; exact hmemτ14e
  have hpcτ15 : τ15.regs.get? Register.PC = some (0x80003870#64) := by
    have := obs_alu_pc hoτ15
    rwa [show BitVec.addInt (0x8000386c#64) 4 = (0x80003870#64 : BitVec 64) from by decide] at this
  have hx10τ15 : τ15.regs.get? Register.x10 = some Wr := by
    have := obs_alu_rd hoτ15 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (Wr + sign_extend (m := 64) (0x000#12)) = Wr from by rw [sext_zero, BitVec.add_zero]] at this
  have hx11τ15 : τ15.regs.get? Register.x11 = some Wl := obs_alu_other hoτ15 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ14
  have hs1τ15 : τ15.regs.get? Register.x9 = some sret := obs_alu_other hoτ15 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ14
  have hspτ15 : τ15.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ15 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ14
  have hx19τ15 : τ15.regs.get? Register.x19 = some Wl := obs_alu_other hoτ15 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ14
  have hx12τ15 : τ15.regs.get? Register.x12 = some (13#64) := obs_alu_other hoτ15 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ14
  have hx13τ15ex : ∃ w, τ15.regs.get? Register.x13 = some w := by
    obtain ⟨w13, hw13⟩ := hx13τ14ex
    exact ⟨w13, obs_alu_other hoτ15 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw13⟩
  obtain ⟨vmiτ15, hmiτ15⟩ := obs_alu_minstret hoτ15
  have houtτ15 : τ15.sailOutput = out0 := by rw [hoτ15.out, sailOutput_sigmaPost_alu]; exact houtτ14
  have hcodeτ15 : Eval_exprLoaded τ15.mem := by rw [hmemτ15e]; exact hcodem5
  --------------------------------------------------------------------------------
  -- 0x80003870: jal __muldi3 → x1 := 0x80003874, PC := 0x80004640
  --------------------------------------------------------------------------------
  obtain ⟨τ16, j16, ht16, hj16, hGτ16, hmemτ16, hoτ16⟩ :=
    site_80003870_ee τ15 j15 (u16 + 13 + 1 + 1) (0x80003870#64) vmiτ15
      hGτ15 hpcτ15 hmiτ15 hcodeτ15 rfl hj15
  have hstepτ16 : Step ⟨τ15, j15, u16 + 13 + 1 + 1⟩ ⟨τ16, j16, u16 + 13 + 1 + 1 + 1⟩ := ht16
  have hmemτ16e : τ16.mem = m5 := by rw [hmemτ16]; exact hmemτ15e
  have hpcτ16 : τ16.regs.get? Register.PC = some (0x80004640#64) := by
    have := obs_jal_pc hoτ16
    rwa [show ((0x80003870#64 : BitVec 64) + sign_extend (m := 64) (0x000dd0#21)) = 0x80004640#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hlinkτ16 : τ16.regs.get? Register.x1 = some (0x80003874#64) := by
    have := obs_jal_rd hoτ16 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80003870#64 : BitVec 64) 4 = (0x80003874#64:BitVec 64) from by decide] at this
  have hx10τ16 : τ16.regs.get? Register.x10 = some Wr := obs_jal_other hoτ16 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ15
  have hx11τ16 : τ16.regs.get? Register.x11 = some Wl := obs_jal_other hoτ16 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ15
  have hs1τ16 : τ16.regs.get? Register.x9 = some sret := obs_jal_other hoτ16 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ15
  have hspτ16 : τ16.regs.get? Register.x2 = some (sp - 1088#64) := obs_jal_other hoτ16 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ15
  have hx19τ16 : τ16.regs.get? Register.x19 = some Wl := obs_jal_other hoτ16 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ15
  have hx12τ16 : τ16.regs.get? Register.x12 = some (13#64) := obs_jal_other hoτ16 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ15
  have hx13τ16ex : ∃ w, τ16.regs.get? Register.x13 = some w := by
    obtain ⟨w13, hw13⟩ := hx13τ15ex
    exact ⟨w13, obs_jal_other hoτ16 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw13⟩
  obtain ⟨vmiτ16, hmiτ16⟩ := obs_jal_minstret hoτ16
  have houtτ16 : τ16.sailOutput = out0 := by rw [hoτ16.out, sailOutput_sigmaPost_jal]; exact houtτ15
  have hMuldi3τ16 : Vsa.Sim.Code.__muldi3Loaded τ16.mem := by rw [hmemτ16e]; exact hMuldi35
  --------------------------------------------------------------------------------
  -- __muldi3 callee (via muldi3_spec): x = Wr (x10), y = Wl (x11) → x10 = Wr*Wl
  --------------------------------------------------------------------------------
  -- the ghost frame `gm` at τ16 (for `muldi3_post`'s NotWrittenM restore; we only
  -- need x2/x9/x19 restored, so `gm` = τ16.regs).
  obtain ⟨w13τ16, hw13τ16⟩ := hx13τ16ex
  have hmuldipre : muldi3_pre (fun R => τ16.regs.get? R) Wr Wl (0x80003874#64) τ16.mem out0
      ⟨τ16, j16, u16 + 13 + 1 + 1 + 1⟩ := by
    refine ⟨⟨(13#64), w13τ16, ?_⟩, by decide⟩
    exact ⟨hGτ16, hMuldi3τ16, rfl, houtτ16, hpcτ16, hx10τ16, hx11τ16, hx12τ16, hw13τ16, hlinkτ16,
      ⟨vmiτ16, hmiτ16⟩, hj16, fun R _ => rfl⟩
  obtain ⟨cmd, hsmd, hGmd, hmemmd, houtmd, hpcmd, hx10md, hramd, htickmd, hframemd⟩ :=
    muldi3_spec (fun R => τ16.regs.get? R) Wr Wl (0x80003874#64) τ16.mem out0
      ⟨τ16, j16, u16 + 13 + 1 + 1 + 1⟩ hmuldipre
  -- muldi3_post gives x10 = Wr * Wl, mem = τ16.mem = m5, sailOutput = out0, x1 = 0x80003874
  have hx10md' : cmd.σ.regs.get? Register.x10 = some (Wr * Wl) := hx10md
  have hmemmd5 : cmd.σ.mem = m5 := by rw [hmemmd]; exact hmemτ16e
  have hpcmd' : cmd.σ.regs.get? Register.PC = some (0x80003874#64) := hpcmd
  have hs1md : cmd.σ.regs.get? Register.x9 = some sret := by
    have := hframemd Register.x9 (by decide); rw [this]; exact hs1τ16
  have hspmd : cmd.σ.regs.get? Register.x2 = some (sp - 1088#64) := by
    have := hframemd Register.x2 (by decide); rw [this]; exact hspτ16
  have hx19md : cmd.σ.regs.get? Register.x19 = some Wl := by
    have := hframemd Register.x19 (by decide); rw [this]; exact hx19τ16
  obtain ⟨vmimd, hmimd⟩ := hGmd.minstret
  have hcodemd : Eval_exprLoaded cmd.σ.mem := by rw [hmemmd5]; exact hcodem5
  have hVintmd : Value_intLoaded cmd.σ.mem := by rw [hmemmd5]; exact hVint5
  --------------------------------------------------------------------------------
  -- 0x80003874: mv a1,a0 → x11 := Wr*Wl (the product)
  --------------------------------------------------------------------------------
  obtain ⟨τ17, j17, ht17, hj17, hGτ17, hmemτ17, hoτ17⟩ :=
    site_80003874_ee cmd.σ cmd.tick cmd.steps (0x80003874#64) vmimd (Wr * Wl)
      hGmd hpcmd' hmimd hx10md' hcodemd rfl htickmd
  have hstepτ17 : Step cmd ⟨τ17, j17, cmd.steps + 1⟩ := by cases cmd; exact ht17
  have hmemτ17e : τ17.mem = m5 := by rw [hmemτ17]; exact hmemmd5
  have hpcτ17 : τ17.regs.get? Register.PC = some (0x80003878#64) := by
    have := obs_alu_pc hoτ17
    rwa [show BitVec.addInt (0x80003874#64) 4 = (0x80003878#64 : BitVec 64) from by decide] at this
  have hx11τ17 : τ17.regs.get? Register.x11 = some (Wr * Wl) := by
    have := obs_alu_rd hoτ17 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((Wr * Wl) + sign_extend (m := 64) (0x000#12)) = Wr * Wl from by rw [sext_zero, BitVec.add_zero]] at this
  have hs1τ17 : τ17.regs.get? Register.x9 = some sret := obs_alu_other hoτ17 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1md
  have hspτ17 : τ17.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ17 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspmd
  have hx19τ17 : τ17.regs.get? Register.x19 = some Wl := obs_alu_other hoτ17 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19md
  obtain ⟨vmiτ17, hmiτ17⟩ := obs_alu_minstret hoτ17
  have houtτ17 : τ17.sailOutput = out0 := by rw [hoτ17.out, sailOutput_sigmaPost_alu]; exact houtmd
  have hcodeτ17 : Eval_exprLoaded τ17.mem := by rw [hmemτ17e]; exact hcodem5
  have hVintτ17 : Value_intLoaded τ17.mem := by rw [hmemτ17e]; exact hVint5
  --------------------------------------------------------------------------------
  -- 0x80003878: mv a0,s1 → x10 := sret
  --------------------------------------------------------------------------------
  obtain ⟨τ18, j18, ht18, hj18, hGτ18, hmemτ18, hoτ18⟩ :=
    site_80003878_ee τ17 j17 (cmd.steps + 1) (0x80003878#64) vmiτ17 sret
      hGτ17 hpcτ17 hmiτ17 hs1τ17 hcodeτ17 rfl hj17
  have hstepτ18 : Step ⟨τ17, j17, cmd.steps + 1⟩ ⟨τ18, j18, cmd.steps + 1 + 1⟩ := ht18
  have hmemτ18e : τ18.mem = m5 := by rw [hmemτ18]; exact hmemτ17e
  have hpcτ18 : τ18.regs.get? Register.PC = some (0x8000387c#64) := by
    have := obs_alu_pc hoτ18
    rwa [show BitVec.addInt (0x80003878#64) 4 = (0x8000387c#64 : BitVec 64) from by decide] at this
  have hx10τ18 : τ18.regs.get? Register.x10 = some sret := by
    have := obs_alu_rd hoτ18 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sret + sign_extend (m := 64) (0x000#12)) = sret from by rw [sext_zero, BitVec.add_zero]] at this
  have hx11τ18 : τ18.regs.get? Register.x11 = some (Wr * Wl) := obs_alu_other hoτ18 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ17
  have hs1τ18 : τ18.regs.get? Register.x9 = some sret := obs_alu_other hoτ18 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ17
  have hspτ18 : τ18.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ18 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ17
  have hx19τ18 : τ18.regs.get? Register.x19 = some Wl := obs_alu_other hoτ18 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ17
  obtain ⟨vmiτ18, hmiτ18⟩ := obs_alu_minstret hoτ18
  have houtτ18 : τ18.sailOutput = out0 := by rw [hoτ18.out, sailOutput_sigmaPost_alu]; exact houtτ17
  have hcodeτ18 : Eval_exprLoaded τ18.mem := by rw [hmemτ18e]; exact hcodem5
  have hVintτ18 : Value_intLoaded τ18.mem := by rw [hmemτ18e]; exact hVint5
  --------------------------------------------------------------------------------
  -- 0x8000387c: jal value_int → x1 := 0x80003880, PC := 0x8000280c
  --------------------------------------------------------------------------------
  obtain ⟨τ19, j19, ht19, hj19, hGτ19, hmemτ19, hoτ19⟩ :=
    site_8000387c_ee τ18 j18 (cmd.steps + 1 + 1) (0x8000387c#64) vmiτ18
      hGτ18 hpcτ18 hmiτ18 hcodeτ18 rfl hj18
  have hstepτ19 : Step ⟨τ18, j18, cmd.steps + 1 + 1⟩ ⟨τ19, j19, cmd.steps + 1 + 1 + 1⟩ := ht19
  have hmemτ19e : τ19.mem = m5 := by rw [hmemτ19]; exact hmemτ18e
  have hpcτ19 : τ19.regs.get? Register.PC = some (0x8000280c#64) := by
    have := obs_jal_pc hoτ19
    rwa [show ((0x8000387c#64 : BitVec 64) + sign_extend (m := 64) (0x1fef90#21)) = 0x8000280c#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hlinkτ19 : τ19.regs.get? Register.x1 = some (0x80003880#64) := by
    have := obs_jal_rd hoτ19 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x8000387c#64 : BitVec 64) 4 = (0x80003880#64:BitVec 64) from by decide] at this
  have hx10τ19 : τ19.regs.get? Register.x10 = some sret := obs_jal_other hoτ19 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ18
  have hx11τ19 : τ19.regs.get? Register.x11 = some (Wr * Wl) := obs_jal_other hoτ19 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ18
  have hs1τ19 : τ19.regs.get? Register.x9 = some sret := obs_jal_other hoτ19 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ18
  have hspτ19 : τ19.regs.get? Register.x2 = some (sp - 1088#64) := obs_jal_other hoτ19 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ18
  have hx19τ19 : τ19.regs.get? Register.x19 = some Wl := obs_jal_other hoτ19 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ18
  obtain ⟨vmiτ19, hmiτ19⟩ := obs_jal_minstret hoτ19
  have houtτ19 : τ19.sailOutput = out0 := by rw [hoτ19.out, sailOutput_sigmaPost_jal]; exact houtτ18
  have hVintτ19 : Value_intLoaded τ19.mem := by rw [hmemτ19e]; exact hVint5
  --------------------------------------------------------------------------------
  -- value_int callee (via value_int_spec): buf = sret, pay = Wr * Wl
  --------------------------------------------------------------------------------
  have hIntRegion : IntRegion sret := ⟨hsretAl, hsretLo, hsretHi, hsretWin, hsretVi⟩
  have hval_bridge : (BitVec.ofNat 64 (Wr * Wl).toNat).toInt = wrap64 (a * b) :=
    mul_wrap_bridge Wl Wr a b hWl_toInt hWr_toInt
  -- ── Phase-4a: the whole `value_int ; ld s3 ; j` tail + `PreEpilogueVD` packaging
  --    is now the GENERATED `intBoxEpilogue` (`Vsa/Sim/BinopTailGen.lean`).  The `.mul`
  --    front supplies `τ19` (the `jal value_int` entry) and its transport facts. ──
  have hcodeτ19 : Eval_exprLoaded τ19.mem := by rw [hmemτ19e]; exact hcodem5
  -- s3 restore slot at τ19.mem = m5
  have hs3m5 : read64 m5 (sp.toNat - 40) = some w19.toNat := by
    show read64 (writeMap8 m4 (sp.toNat - 832) D5) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj m4 (sp.toNat - 40) (sp.toNat - 832) D5 hSW.s3d832]
    show read64 (writeMap8 m3 (sp.toNat - 840) D4) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj m3 (sp.toNat - 40) (sp.toNat - 840) D4 hSW.s3d840]
    show read64 (writeMap8 m2 (sp.toNat - 848) D3) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj m2 (sp.toNat - 40) (sp.toNat - 848) D3 hSW.s3d848]
    show read64 (writeMap8 m1 (sp.toNat - 832) D2) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj m1 (sp.toNat - 40) (sp.toNat - 832) D2 hSW.s3d832]
    show read64 (writeMap8 c.σ.mem (sp.toNat - 848) D1) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj c.σ.mem (sp.toNat - 40) (sp.toNat - 848) D1 hSW.s3d848]
    exact hs3slot
  have hs3τ19 : read64 τ19.mem (sp.toNat - 40) = some w19.toNat := by rw [hmemτ19e]; exact hs3m5
  -- top spill slots at τ19.mem
  have hAgTop_m5 : AgreeP (fun k => sp.toNat - 32 ≤ k ∧ k < sp.toNat) c.σ.mem m5 := by
    intro k hk
    show c.σ.mem[k]? = (writeMap8 m4 (sp.toNat - 832) D5)[k]?
    rw [getElem_writeMap8_disjoint m4 (sp.toNat - 832) k D5 (slotDisj_of_topWin hSW.top832 hk)]
    show c.σ.mem[k]? = (writeMap8 m3 (sp.toNat - 840) D4)[k]?
    rw [getElem_writeMap8_disjoint m3 (sp.toNat - 840) k D4 (slotDisj_of_topWin hSW.top840 hk)]
    show c.σ.mem[k]? = (writeMap8 m2 (sp.toNat - 848) D3)[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat - 848) k D3 (slotDisj_of_topWin hSW.top848 hk)]
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat - 832) D2)[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat - 832) k D2 (slotDisj_of_topWin hSW.top832 hk)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat - 848) D1)[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) k D1 (slotDisj_of_topWin hSW.top848 hk)]
  have hslotRaτ19 : read64 τ19.mem (sp.toNat - 8) = some r.toNat := by
    rw [hmemτ19e, ← read64_agreeP hAgTop_m5 hTopW.1]; exact hslotRa
  have hslotS0τ19 : read64 τ19.mem (sp.toNat - 16) = some v8.toNat := by
    rw [hmemτ19e, ← read64_agreeP hAgTop_m5 hTopW.2.1]; exact hslotS0
  have hslotS1τ19 : read64 τ19.mem (sp.toNat - 24) = some v9.toNat := by
    rw [hmemτ19e, ← read64_agreeP hAgTop_m5 hTopW.2.2.1]; exact hslotS1
  have hslotS2τ19 : read64 τ19.mem (sp.toNat - 32) = some v18.toNat := by
    rw [hmemτ19e, ← read64_agreeP hAgTop_m5 hTopW.2.2.2]; exact hslotS2
  -- store survival outside SL, phrased at τ19.mem = m5
  have hAgSL_m5 : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = m5[k]? := by
    intro k hk
    show c.σ.mem[k]? = (writeMap8 m4 (sp.toNat - 832) D5)[k]?
    rw [getElem_writeMap8_disjoint m4 (sp.toNat - 832) k D5 (slotDisj_of_notInSL hSW.inSL832 hk)]
    show c.σ.mem[k]? = (writeMap8 m3 (sp.toNat - 840) D4)[k]?
    rw [getElem_writeMap8_disjoint m3 (sp.toNat - 840) k D4 (slotDisj_of_notInSL hSW.inSL840 hk)]
    show c.σ.mem[k]? = (writeMap8 m2 (sp.toNat - 848) D3)[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat - 848) k D3 (slotDisj_of_notInSL hSW.inSL848 hk)]
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat - 832) D2)[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat - 832) k D2 (slotDisj_of_notInSL hSW.inSL832 hk)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat - 848) D1)[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) k D1 (slotDisj_of_notInSL hSW.inSL848 hk)]
  have hSurvSLτ19 : ∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → τ19.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st''.store :=
    fun m' hm' => hstoreSurv' m' (fun k hk => ((hAgSL_m5 k hk).trans (by rw [← hmemτ19e])).trans (hm' k hk))
  -- MemExtends m0 → τ19.mem
  have hMemExt_c_5 : MemExtends c.σ.mem m5 :=
    ((memExtends_writeMap8 c.σ.mem (sp.toNat - 848) D1).trans
      (memExtends_writeMap8 m1 (sp.toNat - 832) D2)).trans
      (((memExtends_writeMap8 m2 (sp.toNat - 848) D3).trans
        (memExtends_writeMap8 m3 (sp.toNat - 840) D4)).trans
        (memExtends_writeMap8 m4 (sp.toNat - 832) D5))
  have hMemExtτ19 : MemExtends m0 τ19.mem := by
    rw [hmemτ19e]; exact hMemExt.trans hMemExt_c_5
  -- memory frame vs m0 at τ19.mem = m5
  have hmemframeτ19 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ τ19.mem[a]? = m0[a]? := by
    intro a ha hA
    refine Or.inr ?_
    rw [hmemτ19e]
    have hm5c : m5[a]? = c.σ.mem[a]? := by
      show (writeMap8 m4 (sp.toNat - 832) D5)[a]? = c.σ.mem[a]?
      rw [getElem_writeMap8_disjoint m4 (sp.toNat - 832) a D5 (slotDisj_of_notInStack hSW.inStk832 ha)]
      show (writeMap8 m3 (sp.toNat - 840) D4)[a]? = c.σ.mem[a]?
      rw [getElem_writeMap8_disjoint m3 (sp.toNat - 840) a D4 (slotDisj_of_notInStack hSW.inStk840 ha)]
      show (writeMap8 m2 (sp.toNat - 848) D3)[a]? = c.σ.mem[a]?
      rw [getElem_writeMap8_disjoint m2 (sp.toNat - 848) a D3 (slotDisj_of_notInStack hSW.inStk848 ha)]
      show (writeMap8 m1 (sp.toNat - 832) D2)[a]? = c.σ.mem[a]?
      rw [getElem_writeMap8_disjoint m1 (sp.toNat - 832) a D2 (slotDisj_of_notInStack hSW.inStk832 ha)]
      show (writeMap8 c.σ.mem (sp.toNat - 848) D1)[a]? = c.σ.mem[a]?
      rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) a D1 (slotDisj_of_notInStack hSW.inStk848 ha)]
    rw [hm5c]; exact hmemframe a ha hA
  -- frame collapse τ19.regs → g for R ≠ x19 (through the muldi3 tail, to c.σ = gpre, then → g)
  have sfoSeg3 :
      StepFrameOut ((Register.x11 :: noiseRegs) ++ (Register.x10 :: noiseRegs)
        ++ (Register.x1 :: noiseRegs)) τ13 τ16 := by
    chain_frame_out [hoτ14, hoτ15, hoτ16]
  have sfoSeg2 :
      StepFrameOut ((Register.x11 :: noiseRegs) ++ (Register.x10 :: noiseRegs)
        ++ (Register.x1 :: noiseRegs)) cmd.σ τ19 := by
    chain_frame_out [hoτ17, hoτ18, hoτ19]
  have hframeGτ19 : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      (Register.x19 == R) = false → τ19.regs.get? R = g R := by
    intro R hR he8 he9 he18 he2 h19ne
    obtain ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    have hR' : AbiPreservedNoise R := ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    have ne : ∀ {X : Register}, AbiPreserved X = false → (X == R) = false := by
      intro X hX
      rcases hXR : (X == R) with _ | _
      · rfl
      · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hab; exact absurd hab (by decide)
    have hNoise : ∀ r ∈ noiseRegs, (r == R) = false :=
      noiseAvoid hmi' hpc' hnpc' hmii' hmc' hmt' hmip'
    have hne1 : (Register.x1 == R) = false := ne (X := Register.x1) (by decide)
    have hne10 : (Register.x10 == R) = false := ne (X := Register.x10) (by decide)
    have hne11 : (Register.x11 == R) = false := ne (X := Register.x11) (by decide)
    have f_19_17 : τ19.regs.get? R = cmd.σ.regs.get? R :=
      sfoSeg2.frame R (appendAvoid (appendAvoid (consAvoid hne11 hNoise) (consAvoid hne10 hNoise))
        (consAvoid hne1 hNoise))
    have f_16_14 : τ16.regs.get? R = τ13.regs.get? R :=
      sfoSeg3.frame R (appendAvoid (appendAvoid (consAvoid hne11 hNoise) (consAvoid hne10 hNoise))
        (consAvoid hne1 hNoise))
    have fmd : cmd.σ.regs.get? R = τ16.regs.get? R :=
      hframemd R ⟨ne (by decide), ne (by decide), ne (by decide), ne (by decide), hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    rw [f_19_17, fmd, f_16_14, hLadderFrame R hR' he8]
    exact (hframe R hR' h19ne).trans (hbridge R hR' he8 he9 he18 he2)
  -- === invoke the GENERATED shared tail ===
  obtain ⟨mpre, φfm2, φcm2, φfe, φce, cfin, hStepsFin, hp1, hp2, hp3, hp4, hPreD⟩ :=
    intBoxEpilogue g N A SL φf φc φfm φcm φf' φc' nf nc st'.store.frames.size st'.store.closures.size st' st''
      sp r sret v8 v9 v18 v19 w19 (Wr * Wl) (wrap64 (a * b)) out0 m0
      ⟨τ19, j19, cmd.steps + 1 + 1 + 1⟩ (0x80003880#64) (0x80003880#64) (0x80003884#64) (0x1ffb68#21)
      (fun σ i u pc vminstret v2 b0 b1 b2 b3 b4 b5 b6 b7 => site_80003880_ee σ i u pc vminstret v2 b0 b1 b2 b3 b4 b5 b6 b7)
      (fun σ i u pc vminstret => site_80003884_ee σ i u pc vminstret)
      rfl (by apply BitVec.eq_of_toNat_eq; decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by decide)
      haddr1048
      hGτ19 hVintτ19 hpcτ19 hx10τ19 hx11τ19 hlinkτ19 hs1τ19 hspτ19 ⟨vmiτ19, hmiτ19⟩ hj19 houtτ19
      hcodeτ19 hIntRegion (by decide) hval_bridge
      hpfm hpcm hpf' hpc' houtStr
      hSurvSLτ19 hs3τ19 hslotRaτ19 hslotS0τ19 hslotS1τ19 hslotS2τ19
      hgv8 hgv9 hgv18 hgv2 hgx19 hw19 hframeGτ19 hMemExtτ19 hmemframeτ19
      hsretEvalCode hsretStk hsretInSL hSLlo40 hSLlo32
      hsp1088 hsphiRam hspLoc hspHtifLoc hsp8 hraAl
      g40.lo g40.hi8 g40.ht8 g40.al8
  have hchain : Steps c cfin :=
    (hLadderSteps.trans <|
      (Steps.single hstepτ14).trans <| (Steps.single hstepτ15).trans <|
      (Steps.single hstepτ16).trans <| hsmd.trans <| (Steps.single hstepτ17).trans <|
      (Steps.single hstepτ18).trans (Steps.single hstepτ19)).trans hStepsFin
  exact ⟨cfin, hchain, mpre, φfm2, φcm2, φfe, φce, hp1, hp2, hp3, hp4, hPreD⟩

/-! ## `binOpSem_mul_int` — the spec-side mul bridge -/

theorem binOpSem_mul_int (s : Store) (a b : Int) :
    binOpSem s .mul (.int a) (.int b) = some (.int (wrap64 (a * b))) := rfl

/-! ## `MulResid` — the blockC_mul residuals about the POST-`TwoSubReturn` config -/

structure MulResid
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (sp r sret aExpr : BitVec 64) (Wl : BitVec 64) (c' : Vsa.Machine.Config) : Prop where
  gx8 : gpre Register.x8 = some aExpr
  opTok : read32 c'.σ.mem (aExpr.toNat + 8) = some 13
  slot : MulSlotPinned c'.σ.mem
  fullpop : ∀ k : Nat, ∃ w : BitVec 8, c'.σ.mem[k]? = some w
  x19 : c'.σ.regs.get? Register.x19 = some Wl
  wlbuf : read64 c'.σ.mem (sp.toNat - 960) = some Wl.toNat
  kindresp : read64 c'.σ.mem (sp.toNat - 1088) = some (2#64 : BitVec 64).toNat
  exprAl : aExpr.toNat % 4 = 0
  exprLo : 0x80000000 ≤ aExpr.toNat
  exprHi : aExpr.toNat + 16 ≤ 0x100000000
  exprWin : tohostAddr + 8 ≤ aExpr.toNat
  exprSL : aExpr.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat
  sretAl : sret.toNat % 8 = 0
  sretLo : 0x80000000 ≤ sret.toNat
  sretHi : sret.toNat + 24 ≤ 0x100000000
  sretWin : tohostAddr + 16 ≤ sret.toNat
  sretVi : sret.toNat + 24 ≤ 0x8000280c ∨ 0x8000281c ≤ sret.toNat
  sretStk : sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat
  sretEvalCode : sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat
  raAl : r.toNat % 4 = 0
  vint : Value_intLoaded c'.σ.mem
  muldi3 : Vsa.Sim.Code.__muldi3Loaded c'.σ.mem
  muldiStk : sp.toNat ≤ 0x80004640 ∨ 0x80004664 ≤ SL.lo
  codeStk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  viStk : sp.toNat ≤ 0x8000280c ∨ 0x8000281c ≤ SL.lo
  tableStk : opTableBase + 12 ≤ SL.lo ∨ sp.toNat ≤ opTableBase
  sretInSL : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi
  SLloSp : SL.lo + 1088 ≤ sp.toNat
  SLlo : 0x80000000 ≤ SL.lo
  SLwin : tohostAddr + 16 ≤ SL.lo
  sphiRam : sp.toNat ≤ 0x100000000
  sp8 : sp.toNat % 8 = 0
  SLhiRam : SL.hi ≤ 0x100000000
  spSLhi : sp.toNat ≤ SL.hi

/-! ## `evalMulSim` — the `EvalE.binary .mul` int recursive case -/

def EvalMulSimGoal : Prop :=
  ∀ (gouter gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (a b : Int)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 Wl : BitVec 64)
    (out0 : Array String) (m0 : Mem),
    EvalIH st d env el st' (.int a) →
    EvalIH st' d env er st'' (.int b) →
    EvalE st d env (.binary .mul el er) st'' (.int (wrap64 (a * b))) →
    st'.store.frames.size = st''.store.frames.size →
    st'.store.closures.size = st''.store.closures.size →
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary .mul el er)
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        BinExtras N A SL el er ment sp sret aExpr aLOp aROp ∧
        c.σ.regs.get? Register.x11 = some aEnv ∧
        c.σ.regs.get? Register.x13 = some aEnvReg ∧
        c.σ.regs.get? Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧
        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧
        gpre Register.x8 = some aExpr ∧ gpre Register.x18 = some aEnv ∧
        gpre Register.x19 = some v19 ∧
        read64 ment (aExpr.toNat + 16) = some aLOp.toNat ∧
        ExprRepr ment aLOp.toNat el ∧
        read64 ment (aExpr.toNat + 24) = some aROp.toNat ∧
        ExprRepr ment aROp.toNat er ∧
        (∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ bb, ment[a]? = some bb)) ∧
        MemExtends m0 ment ∧
        -- WAVE 47i: the parent node's entry-ground bundle at the arm entry.
        EvalGround ment SL A sp sret aExpr.toNat (.binary .mul el er) ∧
        -- ITEM ZERO B1: BOTH operands' recursion-sound budgets at `sp - 1088`,
        -- their `.fn`-bodies bounds, and the store-bodies invariants (LEFT over
        -- the entry store `st`, RIGHT over the post-left store `st'`) --
        -- forwarded to `blockB_binary`'s amended pre.
        StackOK SL (sp - 1088#64)
          (el.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget el = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget ∧
        StackOK SL (sp - 1088#64)
          (er.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget er = true ∧
        Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget ∧
        (∀ c' : Vsa.Machine.Config,
          TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
            st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
          MulResid gpre N A SL sp r sret aExpr Wl c') ∧
        g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
        g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧ g Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x2 == R) = false →
          gpre R = g R))
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st'' (.int (wrap64 (a * b))) sp r sret m0)

/-- **`evalMulSim`**: the `EvalE.binary .mul` (int) recursive case, composing
`blockB_binary ≫ blockC_mul ≫ blockD_v_rec` in the `EvalIH` motive shape. -/
theorem evalMulSim : EvalMulSimGoal := by
  intro gouter gpre g N A SL φf φc st st' st'' d env el er a b
    sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 Wl out0 m0 hIHl hIHr _hEvalE hSizeF hSizeC
  intro c hpre
  obtain ⟨ment, hArm, hBE, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
    hpayL, hexprL, hpayR, hexprR, hMentPop, hMemExtM0, hGmt47,
    hstackBudgetL, hexprBodiesL, hstoreBodiesL,
    hstackBudgetR, hexprBodiesR, hstoreBodiesR, hResid,
    hgv8, hgv9, hgv18, hgv2, hgvx19, hbridge⟩ := hpre
  have hVlSurv : ∀ (φ : Addr → Nat) (mm mm' : Mem),
      ValueRepr mm N φ (sp.toNat - 968) (.int a) →
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat - 1080) → ¬ (A.lo ≤ k ∧ k < A.hi) →
        ¬ ((sp.toNat - 944) ≤ k ∧ k < (sp.toNat - 944) + 24) → mm[k]? = mm'[k]?) →
      ValueRepr mm' N φ (sp.toNat - 968) (.int a) := by
    intro φ mm mm' hv hag
    have hsproom := hBE.sproom
    obtain ⟨hk, hp⟩ := hv
    have hAg : AgreeP (fun k => sp.toNat - 968 ≤ k ∧ k < sp.toNat - 952) mm mm' := by
      intro k hk'
      exact hag k (by omega) (by rcases hBE.arenaStk with h | h <;> omega) (by omega)
    refine ⟨?_, ?_⟩
    · rw [← read32_agreeP hAg (fun j hj => ⟨by omega, by omega⟩)]; exact hk
    · rw [readI64] at hp ⊢
      rw [← read64_agreeP hAg (fun j hj => ⟨by omega, by omega⟩)]; exact hp
  -- === block B: two-operand head + IHs → TwoSubReturn @0x8000351c ===
  obtain ⟨c2, hs2, hTS⟩ :=
    blockB_binary gouter gpre N A SL φf φc st st' st'' d env .mul el er (.int a) (.int b)
      sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0 hIHl hIHr hVlSurv
      c ⟨ment, hArm, hBE, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
        hpayL, hexprL, hpayR, hexprR, hMentPop, hMemExtM0, hGmt47,
        hstackBudgetL, hexprBodiesL, hstoreBodiesL,
        hstackBudgetR, hexprBodiesR, hstoreBodiesR⟩
  have hR : MulResid gpre N A SL sp r sret aExpr Wl c2 := hResid c2 hTS
  have hOutC2 : String.join c2.σ.sailOutput.toList = st''.out := hTS.2.2.2.2.2.2.2.1
  -- === block C: dispatch + mul tail → PreEpilogueVD @0x800033ec ===
  obtain ⟨c3, hs3, mpre, φfm, φcm, φfe, φce, hpfm, hpcm, hpfe, hpce, hPreD⟩ :=
    blockC_mul gpre g N A SL φf φc st.store.frames.size st.store.closures.size
      st' st'' a b sp r sret aExpr v8 v9 v18 v19 Wl c2.σ.sailOutput m0
      c2 ⟨hTS, hR.gx8, hR.opTok, hR.slot, hR.fullpop, hR.x19, hR.wlbuf, hR.kindresp,
        hR.exprAl, hR.exprLo, hR.exprHi, hR.exprWin, hR.exprSL, hOutC2, rfl,
        hR.sretAl, hR.sretLo, hR.sretHi, hR.sretWin, hR.sretVi, hR.sretStk, hR.sretEvalCode, hR.raAl,
        hR.vint, hR.muldi3, hR.muldiStk, hR.codeStk, hR.viStk, hR.tableStk, hR.sretInSL,
        hR.SLloSp, hR.SLlo, hR.SLwin, hR.sphiRam, hR.sp8, hR.SLhiRam, hR.spSLhi,
        hgv8, hgv9, hgv18, hgv2, hgx19, hgvx19, hbridge⟩
  -- === block D: shared epilogue → EvalExitD ===
  obtain ⟨c4, hs4, hExitDe⟩ :=
    blockD_v_rec g N A SL φfe φce st'' (.int (wrap64 (a * b))) sp r sret v8 v9 v18 c2.σ.sailOutput m0
      c3 ⟨mpre, hPreD⟩
  obtain ⟨hExitE, hMemExt, φf', φc', hpf', hpc', hSurv⟩ := hExitDe
  have hmono := evalE_store_mono _hEvalE
  have hleF' : st.store.frames.size ≤ st'.store.frames.size := hSizeF ▸ hmono.1
  have hleC' : st.store.closures.size ≤ st'.store.closures.size := hSizeC ▸ hmono.2
  have hpfF : PhiExtends φf φfe st.store.frames.size := hpfm.trans (PhiExtends.mono hleF' hpfe)
  have hpcF : PhiExtends φc φce st.store.closures.size := hpcm.trans (PhiExtends.mono hleC' hpce)
  have hExit : EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st'' (.int (wrap64 (a * b))) sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfF hpcF hExitE hmono.1 hmono.2
  exact ⟨c4, ((hs2.trans hs3).trans hs4), hExit, hMemExt,
    φf', φc', hpfF.trans (PhiExtends.mono hmono.1 hpf'),
    hpcF.trans (PhiExtends.mono hmono.2 hpc'), hSurv⟩

end Vsa.Sim
