import Vsa.Sim.EvalBinSim2
import Vsa.Sim.EvalAddChain

/-!
# `EvalAddRow` — Wave-D M4 row: `evalAddSim` (the `EvalE.binary .add` int pilot)

Relocated out of `EvalBinSim2` (which must stay a BASE that `EvalAddChain` imports —
`blockC_add` now consumes the `.add` block-reflection ladder `evalAddChain_run` +
`evalAddArm_run`, so it cannot live in a file the ladder imports).  `EvalBinSim2`
keeps only the shared `add_wrap_bridge` / `opTableBase` / `AddSlotPinned` /
`addSlot_writeMap8` machinery.

The `.add` operator dispatch → ADD-int arm @0x80003888 → `add a1,s3,a7`
(`x11 = Wl+Wr`) → `value_int` → `PreEpilogueVD .int(wrap64 (a+b))`.

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

theorem blockC_add
    (gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' st'' : Vsa.While.St) (a b : Int)
    (sp r sret aExpr : BitVec 64) (v8 v9 v18 v19 Wl : BitVec 64) (out0 : Array String)
    (m0 : Mem) :
    Triple
      (fun c =>
        TwoSubReturn gpre N A SL φf φc nf nc st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c ∧
        -- the operator-token node (`.binary` node, offsets 4/8 read after the calls)
        gpre Register.x8 = some aExpr ∧
        read32 c.σ.mem (aExpr.toNat + 8) = some 11 ∧      -- op token = binOpTok .add
        AddSlotPinned c.σ.mem ∧
        (∀ k : Nat, ∃ w : BitVec 8, c.σ.mem[k]? = some w) ∧  -- fully-populated post-call mem
        -- === the two head-dropped residuals ===
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
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        (sp.toNat ≤ 0x8000280c ∨ 0x8000281c ≤ SL.lo) ∧
        (opTableBase + 4 ≤ SL.lo ∨ sp.toNat ≤ opTableBase) ∧
        (SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi) ∧
        SL.lo + 1088 ≤ sp.toNat ∧ 0x80000000 ≤ SL.lo ∧ tohostAddr + 16 ≤ SL.lo ∧
        sp.toNat ≤ 0x100000000 ∧ sp.toNat % 8 = 0 ∧ SL.hi ≤ 0x100000000 ∧ sp.toNat ≤ SL.hi ∧
        -- entry ghost bridge (as in `blockC_neg`)
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
        PreEpilogueVD g N A SL φfe φce st'' (.int (wrap64 (a + b))) sp r sret v8 v9 v18 out0 m0 mpre c) := by
  intro c hpre
  obtain ⟨hTS, hgx8, hopTok, hSlot, hFullPop, hX19, hWlBuf, hKindResp,
    hexprAl, hexprLo, hexprHi, hexprWin, hexprSL, houtStr, hout0eq,
    hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEvalCode, hraAl,
    hVint, hcodeStk, hviStk, hTableStk, hsretInSL,
    hSLloSp, hSLlo, hSLwin, hsphiRam, hsp8, hSLhiRam, hspSLhi,
    hgv8, hgv9, hgv18, hgv2, hgprex19, hgx19, hbridge⟩ := hpre
  obtain ⟨hG, htick, hpc, hra, hs1, hsp, ⟨vmi, hmi⟩, hout, hframe,
    ⟨w19, hgprex19', hs3slot⟩, hstoreBundle, hcode,
    hslotRa, hslotS0, hslotS1, hslotS2, hMemExt, hmemframe⟩ := hTS
  -- the s3-spill field's `w19` = the ghost `v19`
  have hw19 : w19 = v19 := by rw [hgprex19] at hgprex19'; exact (Option.some.inj hgprex19').symm
  obtain ⟨φfm, φcm, hpfm, hpcm, ⟨φcr, hpcr, hvalR⟩, ⟨φcl, hvalL⟩,
    φf', φc', hpf', hpc', hstore', hstoreSurv'⟩ := hstoreBundle
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hsp1088 : 1088 ≤ sp.toNat := by omega
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  -- x8 = aExpr (callee-saved, survives both sub-calls; s0 is clobbered by
  -- `lw s0,4(s0)` in the dispatch tail, but is live here = gpre x8 = aExpr)
  have hx8c : c.σ.regs.get? Register.x8 = some aExpr :=
    (hframe Register.x8 (by decide) (by decide)).trans hgx8
  -- op-token addr aExpr+8, e->line addr aExpr+4
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
  -- op-token bytes (value 11) at aExpr+8
  obtain ⟨ob0, ob1, ob2, ob3, hob0, hob1, hob2, hob3, hobrec⟩ :=
    read32_bytes c.σ.mem (aExpr.toNat + 8) 11 hopTok
  -- e->line bytes at aExpr+4 (present, values arbitrary — s0 is dead)
  obtain ⟨lb0, hlb0⟩ := hFullPop (aExpr.toNat + 4)
  obtain ⟨lb1, hlb1⟩ := hFullPop (aExpr.toNat + 4 + 1)
  obtain ⟨lb2, hlb2⟩ := hFullPop (aExpr.toNat + 4 + 2)
  obtain ⟨lb3, hlb3⟩ := hFullPop (aExpr.toNat + 4 + 3)
  -- kind+payload of the RIGHT sub-value (.int b) @ sp-944
  have hvalR' : ValueRepr c.σ.mem N φcr (sp.toNat - 944) (.int b) := hvalR
  obtain ⟨hkindR, pR, hpayR64, hpRb⟩ := valueRepr_int_pay64 hvalR'
  obtain ⟨rkb0, rkb1, rkb2, rkb3, hrkb0, hrkb1, hrkb2, hrkb3, hrkbrec⟩ :=
    read32_bytes c.σ.mem (sp.toNat - 944) 2 hkindR
  obtain ⟨rpb0, rpb1, rpb2, rpb3, rpb4, rpb5, rpb6, rpb7, hrpb0, hrpb1, hrpb2, hrpb3, hrpb4, hrpb5, hrpb6, hrpb7, hrprec⟩ :=
    read64_bytes c.σ.mem (sp.toNat - 944 + 8) pR hpayR64
  -- the RIGHT payload word `Wr`
  let Wr : BitVec 64 := sign_extend (m := 64)
    ((((((((rpb7.append rpb6).append rpb5).append rpb4).append rpb3).append rpb2).append rpb1).append rpb0) : BitVec (8*8))
  have hWrNat : Wr.toNat = pR := by
    show (sign_extend (m := 64)
      ((((((((rpb7.append rpb6).append rpb5).append rpb4).append rpb3).append rpb2).append rpb1).append rpb0) : BitVec (8*8))).toNat = pR
    rw [sext_full, word8_toNat_recon, hrprec]
  have hWr_toInt : Wr.toInt = b := by
    have hpe : Wr = BitVec.ofNat 64 pR := by rw [← hWrNat]; exact (ofNat_toNat_self64 Wr).symm
    rw [hpe]; exact hpRb
  -- the LEFT payload word `Wl` (residual `hX19`) ties to `a` via `hWlBuf` + LEFT ValueRepr
  have hvalL' : ValueRepr c.σ.mem N φcl (sp.toNat - 968) (.int a) := hvalL
  obtain ⟨hkindL, pL, hpayL64, hpLa⟩ := valueRepr_int_pay64 hvalL'
  have hpayL64' : read64 c.σ.mem (sp.toNat - 960) = some pL := by
    have e : sp.toNat - 968 + 8 = sp.toNat - 960 := by omega
    rw [e] at hpayL64; exact hpayL64
  have hWlNat : Wl.toNat = pL := by
    have := hWlBuf.symm.trans hpayL64'; exact Option.some.inj this
  have hWl_toInt : Wl.toInt = a := by
    have hpe : Wl = BitVec.ofNat 64 pL := by rw [← hWlNat]; exact (ofNat_toNat_self64 Wl).symm
    rw [hpe]; exact hpLa
  -- respilled vl.kind word @ sp-1088 = 2#64 (residual `hKindResp`)
  -- (used by `ld a6,0(sp)` and the int-kind `bne`/`beqz` guards)
  -- op-token loaded value = 11#64
  have hopVal : (sign_extend (m := 64) ((((ob3.append ob2).append ob1).append ob0) : BitVec (8*4)))
      = (11#64 : BitVec 64) := by
    rw [sext_word_small _ 11 (by decide) (by rw [word_toNat_recon]; exact hobrec)]
  -- RIGHT kind loaded value (lw a0,144(sp)) = 2#64
  have hRkindVal : (sign_extend (m := 64) ((((rkb3.append rkb2).append rkb1).append rkb0) : BitVec (8*4)))
      = (2#64 : BitVec 64) := by
    rw [sext_word_small _ 2 (by decide) (by rw [word_toNat_recon]; exact hrkbrec)]
  -- addresses of the dispatch/add-path loads and stores as sp - k
  have haddr144 : ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 944 :=
    spill_addr sp (0x090#12) 944 (by decide) (by omega) hsp1088
  have haddr152 : ((sp - 1088#64) + sign_extend (m := 64) (0x098#12)).toNat = sp.toNat - 936 :=
    spill_addr sp (0x098#12) 936 (by decide) (by omega) hsp1088
  have haddr120 : ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat = sp.toNat - 968 :=
    spill_addr sp (0x078#12) 968 (by decide) (by omega) hsp1088
  have haddr128 : ((sp - 1088#64) + sign_extend (m := 64) (0x080#12)).toNat = sp.toNat - 960 :=
    spill_addr sp (0x080#12) 960 (by decide) (by omega) hsp1088
  have haddr136 : ((sp - 1088#64) + sign_extend (m := 64) (0x088#12)).toNat = sp.toNat - 952 :=
    spill_addr sp (0x088#12) 952 (by decide) (by omega) hsp1088
  have haddr160 : ((sp - 1088#64) + sign_extend (m := 64) (0x0a0#12)).toNat = sp.toNat - 928 :=
    spill_addr sp (0x0a0#12) 928 (by decide) (by omega) hsp1088
  have haddr0 : ((sp - 1088#64) + sign_extend (m := 64) (0x000#12)).toNat = sp.toNat - 1088 := by
    have : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by apply BitVec.eq_of_toNat_eq; decide
    rw [this, BitVec.add_zero]; exact hspsub
  have haddr240 : ((sp - 1088#64) + sign_extend (m := 64) (0x0f0#12)).toNat = sp.toNat - 848 :=
    spill_addr sp (0x0f0#12) 848 (by decide) (by omega) hsp1088
  have haddr248 : ((sp - 1088#64) + sign_extend (m := 64) (0x0f8#12)).toNat = sp.toNat - 840 :=
    spill_addr sp (0x0f8#12) 840 (by decide) (by omega) hsp1088
  have haddr256 : ((sp - 1088#64) + sign_extend (m := 64) (0x100#12)).toNat = sp.toNat - 832 :=
    spill_addr sp (0x100#12) 832 (by decide) (by omega) hsp1088
  have haddr1048 : ((sp - 1088#64) + sign_extend (m := 64) (0x418#12)).toNat = sp.toNat - 40 :=
    spill_addr sp (0x418#12) 40 (by decide) (by omega) hsp1088
  -- present bytes for the RIGHT payload load (ld a7,152(sp)) — from full-pop
  -- (values known from hrpb*); dead a6 word (ld a6,0(sp)) — value 2#64 via hKindResp.
  -- op-token bytes with VALUE in c.σ.mem are directly `read32 (aExpr+8) = 11`.
  --------------------------------------------------------------------------------
  --------------------------------------------------------------------------------
  -- op-token bytes forced concrete (little-endian, 11 = 0x0b,0,0,0) by read32 = 11.
  --------------------------------------------------------------------------------
  have hobv : ob0.toNat = 11 ∧ ob1.toNat = 0 ∧ ob2.toNat = 0 ∧ ob3.toNat = 0 := by
    have h0 := ob0.isLt; have h1 := ob1.isLt; have h2 := ob2.isLt; have h3 := ob3.isLt
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  have hob0' : c.σ.mem[aExpr.toNat + 8]? = some (0x0b#8) := by
    have hb : ob0 = 0x0b#8 := by apply BitVec.eq_of_toNat_eq; rw [hobv.1]; rfl
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
  -- kind-reload bytes @ v2+0 (= sp-1088), value 2, from the Pre read64.
  obtain ⟨kb0, kb1, kb2, kb3, kb4, kb5, kb6, kb7, hkb0, hkb1, hkb2, hkb3, hkb4, hkb5, hkb6, hkb7, hkbrec⟩ :=
    read64_bytes c.σ.mem (sp.toNat - 1088) ((2#64 : BitVec 64).toNat) hKindResp
  have hkVal : bytesVal MKind.ld [kb0, kb1, kb2, kb3, kb4, kb5, kb6, kb7] = (2#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq
    show (sign_extend (m := 64)
      ((((((((kb7.append kb6).append kb5).append kb4).append kb3).append kb2).append kb1).append kb0) : BitVec (8*8))).toNat = _
    rw [sext_full, word8_toNat_recon, hkbrec]
  -- ── chain 0x8000351c → 0x80003888 (evalAddChain_run) ────────────────────────
  obtain ⟨sC0, iC0, hStepsChain, hiC0, hGC0, hpcC0, hx10C0, hx12C0, hx16C0, hx17C0,
      hx2C0, hx9C0, hx19C0, hmemC0eq, houtC0, hmiC0ex, hframeChain⟩ :=
    evalAddChain_run c.σ c.tick c.steps vmi (sp - 1088#64) aExpr sret Wl
      lb0 lb1 lb2 lb3 rkb0 rkb1 rkb2 rkb3 rpb0 rpb1 rpb2 rpb3 rpb4 rpb5 rpb6 rpb7
      kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7
      hG hpc hmi hsp hx8c hs1 hX19 hcode hRkindVal hkVal
      (by rw [hop8]; omega) (by rw [hop8]; omega)
      (by rw [hop8, htoh]; right; omega) (by rw [hop8]; omega)
      (by rw [hop8]; exact hob0') (by rw [hop8]; exact hob1')
      (by rw [hop8]; exact hob2') (by rw [hop8]; exact hob3')
      (by rw [hline4]; omega) (by rw [hline4]; omega)
      (by rw [hline4, htoh]; right; omega) (by rw [hline4]; omega)
      (by rw [hline4]; exact hlb0) (by rw [hline4]; exact hlb1)
      (by rw [hline4]; exact hlb2) (by rw [hline4]; exact hlb3)
      (by rw [haddr144]; omega) (by rw [haddr144]; omega)
      (by rw [haddr144, htoh]; right; omega) (by rw [haddr144]; omega)
      (by rw [haddr144]; exact hrkb0) (by rw [haddr144]; exact hrkb1)
      (by rw [haddr144]; exact hrkb2) (by rw [haddr144]; exact hrkb3)
      (by rw [haddr152]; omega) (by rw [haddr152]; omega)
      (by rw [haddr152, htoh]; right; omega) (by rw [haddr152]; omega)
      (by rw [haddr152, show sp.toNat - 936 = sp.toNat - 944 + 8 from by omega]; exact hrpb0)
      (by rw [haddr152, show sp.toNat - 936 + 1 = sp.toNat - 944 + 8 + 1 from by omega]; exact hrpb1)
      (by rw [haddr152, show sp.toNat - 936 + 2 = sp.toNat - 944 + 8 + 2 from by omega]; exact hrpb2)
      (by rw [haddr152, show sp.toNat - 936 + 3 = sp.toNat - 944 + 8 + 3 from by omega]; exact hrpb3)
      (by rw [haddr152, show sp.toNat - 936 + 4 = sp.toNat - 944 + 8 + 4 from by omega]; exact hrpb4)
      (by rw [haddr152, show sp.toNat - 936 + 5 = sp.toNat - 944 + 8 + 5 from by omega]; exact hrpb5)
      (by rw [haddr152, show sp.toNat - 936 + 6 = sp.toNat - 944 + 8 + 6 from by omega]; exact hrpb6)
      (by rw [haddr152, show sp.toNat - 936 + 7 = sp.toNat - 944 + 8 + 7 from by omega]; exact hrpb7)
      hSlot
      (by rw [haddr0]; omega) (by rw [haddr0]; omega)
      (by rw [haddr0, htoh]; right; omega) (by rw [haddr0]; omega)
      (by rw [haddr0]; exact hkb0) (by rw [haddr0]; exact hkb1)
      (by rw [haddr0]; exact hkb2) (by rw [haddr0]; exact hkb3)
      (by rw [haddr0]; exact hkb4) (by rw [haddr0]; exact hkb5)
      (by rw [haddr0]; exact hkb6) (by rw [haddr0]; exact hkb7)
      htick
  obtain ⟨vmC0, hmiC0⟩ := hmiC0ex
  have hcodeC0 : Vsa.Sim.Code.Eval_exprLoaded sC0.mem := by rw [hmemC0eq]; exact hcode
  -- arm dead-load bytes (abstract, from full-population)
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
  -- ── arm 0x80003888 → 0x800038d4 (evalAddArm_run) ────────────────────────────
  obtain ⟨τ19, j19, D1, D2, D3, D4, D5, hStepsArm, hj19, hGτ19, hmemArm, hpcτ19,
      hx11τ19, hx10τ19, hspτ19, hs1τ19, hx19τ19, houtArm, hmiArmex, hframeArm⟩ :=
    evalAddArm_run sC0 iC0 (c.steps + 16) vmC0 (sp - 1088#64) sret Wl Wr
      fa0 fa1 fa2 fa3 fa4 fa5 fa6 fa7 fb0 fb1 fb2 fb3 fb4 fb5 fb6 fb7
      fc0 fc1 fc2 fc3 fc4 fc5 fc6 fc7 fd0 fd1 fd2 fd3 fd4 fd5 fd6 fd7
      fe0 fe1 fe2 fe3 fe4 fe5 fe6 fe7
      hGC0 hpcC0 hmiC0 hx2C0 hx9C0 hx10C0 hx16C0 hx17C0 hx19C0 hcodeC0
      (by rw [haddr144, hspsub]; omega) (by rw [haddr152, hspsub]; omega)
      (by rw [haddr160, hspsub]; omega) (by rw [haddr240, hspsub]; omega)
      (by rw [haddr256, hspsub]; omega)
      (by rw [haddr240]; rcases hcodeStk with h | h <;> omega)
      (by rw [haddr248]; rcases hcodeStk with h | h <;> omega)
      (by rw [haddr256]; rcases hcodeStk with h | h <;> omega)
      (by rw [haddr120]; omega) (by rw [haddr120]; omega)
      (by rw [haddr120, htoh]; right; omega) (by rw [haddr120]; omega)
      (by rw [haddr120, hmemC0eq]; exact hfa0) (by rw [haddr120, hmemC0eq]; exact hfa1)
      (by rw [haddr120, hmemC0eq]; exact hfa2) (by rw [haddr120, hmemC0eq]; exact hfa3)
      (by rw [haddr120, hmemC0eq]; exact hfa4) (by rw [haddr120, hmemC0eq]; exact hfa5)
      (by rw [haddr120, hmemC0eq]; exact hfa6) (by rw [haddr120, hmemC0eq]; exact hfa7)
      (by rw [haddr136]; omega) (by rw [haddr136]; omega)
      (by rw [haddr136, htoh]; right; omega) (by rw [haddr136]; omega)
      (by rw [haddr136, hmemC0eq]; exact hfb0) (by rw [haddr136, hmemC0eq]; exact hfb1)
      (by rw [haddr136, hmemC0eq]; exact hfb2) (by rw [haddr136, hmemC0eq]; exact hfb3)
      (by rw [haddr136, hmemC0eq]; exact hfb4) (by rw [haddr136, hmemC0eq]; exact hfb5)
      (by rw [haddr136, hmemC0eq]; exact hfb6) (by rw [haddr136, hmemC0eq]; exact hfb7)
      (by rw [haddr144]; omega) (by rw [haddr144]; omega)
      (by rw [haddr144, htoh]; right; omega) (by rw [haddr144]; omega)
      (by rw [haddr144, hmemC0eq]; exact hfc0) (by rw [haddr144, hmemC0eq]; exact hfc1)
      (by rw [haddr144, hmemC0eq]; exact hfc2) (by rw [haddr144, hmemC0eq]; exact hfc3)
      (by rw [haddr144, hmemC0eq]; exact hfc4) (by rw [haddr144, hmemC0eq]; exact hfc5)
      (by rw [haddr144, hmemC0eq]; exact hfc6) (by rw [haddr144, hmemC0eq]; exact hfc7)
      (by rw [haddr152]; omega) (by rw [haddr152]; omega)
      (by rw [haddr152, htoh]; right; omega) (by rw [haddr152]; omega)
      (by rw [haddr152, hmemC0eq]; exact hfd0) (by rw [haddr152, hmemC0eq]; exact hfd1)
      (by rw [haddr152, hmemC0eq]; exact hfd2) (by rw [haddr152, hmemC0eq]; exact hfd3)
      (by rw [haddr152, hmemC0eq]; exact hfd4) (by rw [haddr152, hmemC0eq]; exact hfd5)
      (by rw [haddr152, hmemC0eq]; exact hfd6) (by rw [haddr152, hmemC0eq]; exact hfd7)
      (by rw [haddr160]; omega) (by rw [haddr160]; omega)
      (by rw [haddr160, htoh]; right; omega) (by rw [haddr160]; omega)
      (by rw [haddr160, hmemC0eq]; exact hfe0) (by rw [haddr160, hmemC0eq]; exact hfe1)
      (by rw [haddr160, hmemC0eq]; exact hfe2) (by rw [haddr160, hmemC0eq]; exact hfe3)
      (by rw [haddr160, hmemC0eq]; exact hfe4) (by rw [haddr160, hmemC0eq]; exact hfe5)
      (by rw [haddr160, hmemC0eq]; exact hfe6) (by rw [haddr160, hmemC0eq]; exact hfe7)
      (by rw [haddr240]; omega) (by rw [haddr240]; omega)
      (by rw [haddr240, htoh]; omega) (by rw [haddr240]; omega)
      (by rw [haddr248]; omega) (by rw [haddr248]; omega)
      (by rw [haddr248, htoh]; omega) (by rw [haddr248]; omega)
      (by rw [haddr256]; omega) (by rw [haddr256]; omega)
      (by rw [haddr256, htoh]; omega) (by rw [haddr256]; omega)
      hiC0
  obtain ⟨vmiτ19, hmiτ19⟩ := hmiArmex
  -- normalise the arm's memory image to the sp-relative store addresses (m1..m5)
  have hmemB2 : τ19.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 c.σ.mem
      (sp.toNat - 848) D1) (sp.toNat - 832) D2) (sp.toNat - 848) D3) (sp.toNat - 840) D4)
      (sp.toNat - 832) D5 := by
    rw [hmemArm, hmemC0eq]; simp only [haddr240, haddr248, haddr256]
  let m1 : Mem := writeMap8 c.σ.mem (sp.toNat - 848) D1
  let m2 : Mem := writeMap8 m1 (sp.toNat - 832) D2
  let m3 : Mem := writeMap8 m2 (sp.toNat - 848) D3
  let m4 : Mem := writeMap8 m3 (sp.toNat - 840) D4
  let m5 : Mem := writeMap8 m4 (sp.toNat - 832) D5
  have hmemτ19e : τ19.mem = m5 := hmemB2
  have hcodem1 : Vsa.Sim.Code.Eval_exprLoaded m1 :=
    loaded_eval_expr_agreeP c.σ.mem m1
      (fun k hk => (getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) k D1
        (by rcases hcodeStk with h | h <;> omega)).symm) hcode
  have hcodem2 : Vsa.Sim.Code.Eval_exprLoaded m2 :=
    loaded_eval_expr_agreeP m1 m2
      (fun k hk => (getElem_writeMap8_disjoint m1 (sp.toNat - 832) k D2
        (by rcases hcodeStk with h | h <;> omega)).symm) hcodem1
  have hcodem3 : Vsa.Sim.Code.Eval_exprLoaded m3 :=
    loaded_eval_expr_agreeP m2 m3
      (fun k hk => (getElem_writeMap8_disjoint m2 (sp.toNat - 848) k D3
        (by rcases hcodeStk with h | h <;> omega)).symm) hcodem2
  have hcodem4 : Vsa.Sim.Code.Eval_exprLoaded m4 :=
    loaded_eval_expr_agreeP m3 m4
      (fun k hk => (getElem_writeMap8_disjoint m3 (sp.toNat - 840) k D4
        (by rcases hcodeStk with h | h <;> omega)).symm) hcodem3
  have hcodem5 : Vsa.Sim.Code.Eval_exprLoaded m5 :=
    loaded_eval_expr_agreeP m4 m5
      (fun k hk => (getElem_writeMap8_disjoint m4 (sp.toNat - 832) k D5
        (by rcases hcodeStk with h | h <;> omega)).symm) hcodem4
  have hcodeτ19 : Vsa.Sim.Code.Eval_exprLoaded τ19.mem := by rw [hmemτ19e]; exact hcodem5
  have houtτ19 : τ19.sailOutput = out0 := houtArm.trans (houtC0.trans hout0eq)
  let u16 : Nat := c.steps + 16
  -- composed ladder Steps (16 + 19 = 35) and the ABI-noise frame
  have hLadderSteps : Steps ⟨c.σ, c.tick, c.steps⟩ ⟨τ19, j19, u16 + 19⟩ :=
    hStepsChain.trans hStepsArm
  have hLadderFrame : ∀ R : Register, AbiPreservedNoise R → (Register.x8 == R) = false →
      τ19.regs.get? R = c.σ.regs.get? R := by
    intro R hR he8
    exact (hframeArm R hR he8).trans (hframeChain R hR he8)
  --------------------------------------------------------------------------------
  -- 0x800038d4: jal value_int → PC := 0x8000280c, x1 := 0x800038d8
  --------------------------------------------------------------------------------
  -- `Value_intLoaded m5` (from `c.σ.mem`, survives the 5 stack stores)
  have hVint5 : Value_intLoaded m5 := by
    have h1 : Value_intLoaded m1 := loaded_int_writeMap8 c.σ.mem (sp.toNat - 848) D1 (by rcases hviStk with h | h <;> omega) hVint
    have h2 : Value_intLoaded m2 := loaded_int_writeMap8 m1 (sp.toNat - 832) D2 (by rcases hviStk with h | h <;> omega) h1
    have h3 : Value_intLoaded m3 := loaded_int_writeMap8 m2 (sp.toNat - 848) D3 (by rcases hviStk with h | h <;> omega) h2
    have h4 : Value_intLoaded m4 := loaded_int_writeMap8 m3 (sp.toNat - 840) D4 (by rcases hviStk with h | h <;> omega) h3
    exact loaded_int_writeMap8 m4 (sp.toNat - 832) D5 (by rcases hviStk with h | h <;> omega) h4
  obtain ⟨τ20, j20, ht20', hj20, hGτ20, hmemτ20, hoτ20⟩ :=
    site_800038d4_ee τ19 j19 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800038d4#64) vmiτ19
      hGτ19 hpcτ19 hmiτ19 hcodeτ19 rfl hj19
  have hstepτ20 : Step ⟨τ19, j19, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ20, j20, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht20'
  have hmemτ20e : τ20.mem = m5 := by rw [hmemτ20]; exact hmemτ19e
  have hpcτ20 : τ20.regs.get? Register.PC = some (0x8000280c#64) := by
    have := obs_jal_pc hoτ20
    rwa [show ((0x800038d4#64 : BitVec 64) + sign_extend (m := 64) (0x1fef38#21)) = 0x8000280c#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hlinkτ20 : τ20.regs.get? Register.x1 = some (0x800038d8#64) := by
    have := obs_jal_rd hoτ20 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x800038d4#64 : BitVec 64) 4 = (0x800038d8#64:BitVec 64) from by decide] at this
  have hx10τ20 : τ20.regs.get? Register.x10 = some sret := obs_jal_other hoτ20 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ19
  have hx11τ20 : τ20.regs.get? Register.x11 = some (Wl + Wr) := obs_jal_other hoτ20 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ19
  have hs1τ20 : τ20.regs.get? Register.x9 = some sret := obs_jal_other hoτ20 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ19
  have hspτ20 : τ20.regs.get? Register.x2 = some (sp - 1088#64) := obs_jal_other hoτ20 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ19
  have hx19τ20 : τ20.regs.get? Register.x19 = some Wl := obs_jal_other hoτ20 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ19
  obtain ⟨vmiτ20, hmiτ20⟩ := obs_jal_minstret hoτ20
  have houtτ20 : τ20.sailOutput = out0 := by rw [hoτ20.out, sailOutput_sigmaPost_jal]; exact houtτ19
  have hVintτ20 : Value_intLoaded τ20.mem := by rw [hmemτ20e]; exact hVint5
  --------------------------------------------------------------------------------
  -- value_int callee (via value_int_spec): buf = sret, pay = Wl + Wr
  --------------------------------------------------------------------------------
  have hIntRegion : IntRegion sret := ⟨hsretAl, hsretLo, hsretHi, hsretWin, hsretVi⟩
  have hcallpre : int_pre (fun R => τ20.regs.get? R) sret (Wl + Wr) (0x800038d8#64) τ20.mem out0
      ⟨τ20, j20, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := by
    refine ⟨hGτ20, hVintτ20, rfl, hpcτ20, hx10τ20, hx11τ20, hlinkτ20, ⟨vmiτ20, hmiτ20⟩, hj20, hIntRegion,
      (by decide), houtτ20, fun R _ => rfl⟩
  obtain ⟨cvi, hsvi, hGvi, hpcvi, hx10vi, hravi, ⟨vmivi, hmivi⟩, htickvi, hvalvi, houtvi,
      hmemframevi, hpresvi, hframevi⟩ :=
    value_int_spec (fun R => τ20.regs.get? R) sret (Wl + Wr) (0x800038d8#64) N φc' τ20.mem out0
      ⟨τ20, j20, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ hcallpre
  -- the produced value is `.int (wrap64 (a + b))`
  have hval_bridge : (BitVec.ofNat 64 (Wl + Wr).toNat).toInt = wrap64 (a + b) :=
    add_wrap_bridge Wl Wr a b hWl_toInt hWr_toInt
  have hvalfinal : ValueRepr cvi.σ.mem N φc' sret.toNat (.int (wrap64 (a + b))) := by
    rw [← hval_bridge]; exact hvalvi
  have hpcvi' : cvi.σ.regs.get? Register.PC = some (0x800038d8#64) := by
    rw [hpcvi, show (BitVec.update ((0x800038d8#64:BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1)
      = 0x800038d8#64 from by apply BitVec.eq_of_toNat_eq; decide]
  have hcodeτ20 : Eval_exprLoaded τ20.mem := by rw [hmemτ20e]; exact hcodem5
  have hcode_vi : Eval_exprLoaded cvi.σ.mem :=
    loaded_eval_expr_agreeP τ20.mem cvi.σ.mem
      (fun k hk => hmemframevi k (by rcases hsretEvalCode with h | h <;> omega)) hcodeτ20
  have hs1_vi : cvi.σ.regs.get? Register.x9 = some sret := by
    rw [hframevi Register.x9 (by decide)]; exact hs1τ20
  have hsp_vi : cvi.σ.regs.get? Register.x2 = some (sp - 1088#64) := by
    rw [hframevi Register.x2 (by decide)]; exact hspτ20
  have hx19_vi : cvi.σ.regs.get? Register.x19 = some Wl := by
    rw [hframevi Register.x19 (by decide)]; exact hx19τ20
  --------------------------------------------------------------------------------
  -- `s3` restore slot `[sp-40, sp-32)`: holds the entry s3 value `v19` (from the
  -- TwoSubReturn s3-spill field `hs3slot`), survives all 5 stack stores + the
  -- value_int sret write (all disjoint from sp-40).
  --------------------------------------------------------------------------------
  -- `read64 m5 (sp-40) = w19.toNat` (hs3slot at c.σ.mem survives the 5 stores)
  have hs3m5 : read64 m5 (sp.toNat - 40) = some w19.toNat := by
    show read64 (writeMap8 m4 (sp.toNat - 832) D5) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj m4 (sp.toNat - 40) (sp.toNat - 832) D5 (by omega)]
    show read64 (writeMap8 m3 (sp.toNat - 840) D4) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj m3 (sp.toNat - 40) (sp.toNat - 840) D4 (by omega)]
    show read64 (writeMap8 m2 (sp.toNat - 848) D3) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj m2 (sp.toNat - 40) (sp.toNat - 848) D3 (by omega)]
    show read64 (writeMap8 m1 (sp.toNat - 832) D2) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj m1 (sp.toNat - 40) (sp.toNat - 832) D2 (by omega)]
    show read64 (writeMap8 c.σ.mem (sp.toNat - 848) D1) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj c.σ.mem (sp.toNat - 40) (sp.toNat - 848) D1 (by omega)]
    exact hs3slot
  -- survives value_int's sret write (sret disjoint from [sp-40,sp-32) since sret ∈ SL,
  -- and sp-40 ≥ SL.lo... actually sp-40 could be inside SL; use memframevi with sret window)
  have hs3vi : read64 cvi.σ.mem (sp.toNat - 40) = some w19.toNat := by
    rw [← read64_agreeP (P := fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat - 32)
      (a := sp.toNat - 40) (m := τ20.mem) (m' := cvi.σ.mem)
      (fun k hk => hmemframevi k (by rcases hsretStk with h | h <;> omega))
      (fun j hj => ⟨by omega, by omega⟩)]
    rw [hmemτ20e]; exact hs3m5
  obtain ⟨s3b0, s3b1, s3b2, s3b3, s3b4, s3b5, s3b6, s3b7, hs3b0, hs3b1, hs3b2, hs3b3, hs3b4, hs3b5, hs3b6, hs3b7, hs3rec⟩ :=
    read64_bytes cvi.σ.mem (sp.toNat - 40) w19.toNat hs3vi
  --------------------------------------------------------------------------------
  -- 0x800038d8: ld s3,1048(sp) → x19 := w19 (restore entry s3)
  --------------------------------------------------------------------------------
  obtain ⟨τ21, j21, ht21', hj21, hGτ21, hmemτ21, hoτ21⟩ :=
    site_800038d8_ee cvi.σ cvi.tick cvi.steps (0x800038d8#64) vmivi (sp - 1088#64)
      s3b0 s3b1 s3b2 s3b3 s3b4 s3b5 s3b6 s3b7 hGvi hpcvi' hmivi hsp_vi hcode_vi rfl
      (by rw [haddr1048]; omega) (by rw [haddr1048]; omega)
      (by rw [haddr1048, htoh]; right; omega) (by rw [haddr1048]; omega)
      (by rw [haddr1048]; exact hs3b0) (by rw [haddr1048]; exact hs3b1)
      (by rw [haddr1048]; exact hs3b2) (by rw [haddr1048]; exact hs3b3)
      (by rw [haddr1048]; exact hs3b4) (by rw [haddr1048]; exact hs3b5)
      (by rw [haddr1048]; exact hs3b6) (by rw [haddr1048]; exact hs3b7) htickvi
  have hstepτ21 : Step cvi ⟨τ21, j21, cvi.steps + 1⟩ := by cases cvi; exact ht21'
  have hmemτ21e : τ21.mem = cvi.σ.mem := hmemτ21
  have hpcτ21 : τ21.regs.get? Register.PC = some (0x800038dc#64) := by
    have := obs_alu_pc hoτ21
    rwa [show BitVec.addInt (0x800038d8#64) 4 = (0x800038dc#64 : BitVec 64) from by decide] at this
  have hx19τ21 : τ21.regs.get? Register.x19 = some w19 := by
    have := obs_alu_rd hoτ21 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64) ((((((((s3b7.append s3b6).append s3b5).append s3b4).append s3b3).append s3b2).append s3b1).append s3b0) : BitVec (8*8))) = w19 from by
      apply BitVec.eq_of_toNat_eq; rw [sext_full, word8_toNat_recon, hs3rec]] at this
  have hs1τ21 : τ21.regs.get? Register.x9 = some sret := obs_alu_other hoτ21 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_vi
  have hspτ21 : τ21.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ21 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_vi
  obtain ⟨vmiτ21, hmiτ21⟩ := obs_alu_minstret hoτ21
  have houtτ21 : τ21.sailOutput = out0 := by rw [hoτ21.out, sailOutput_sigmaPost_alu]; exact houtvi
  have hcodeτ21 : Eval_exprLoaded τ21.mem := by rw [hmemτ21e]; exact hcode_vi
  --------------------------------------------------------------------------------
  -- 0x800038dc: j 0x800033ec → shared epilogue entry
  --------------------------------------------------------------------------------
  obtain ⟨τ22, j22, ht22', hj22, hGτ22, hmemτ22, hoτ22⟩ :=
    site_800038dc_ee τ21 j21 (cvi.steps + 1) (0x800038dc#64) vmiτ21 hGτ21 hpcτ21 hmiτ21 hcodeτ21 rfl (by decide) hj21
  have hstepτ22 : Step ⟨τ21, j21, cvi.steps + 1⟩ ⟨τ22, j22, cvi.steps + 1 + 1⟩ := ht22'
  have hmemτ22e : τ22.mem = cvi.σ.mem := by rw [hmemτ22]; exact hmemτ21e
  have hpc_fin : τ22.regs.get? Register.PC = some (0x800033ec#64) := by
    have := obs_jr_pc hoτ22
    rwa [show ((0x800038dc#64:BitVec 64) + sign_extend (m := 64) (0x1ffb10#21)) = 0x800033ec#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hs1_fin : τ22.regs.get? Register.x9 = some sret := obs_jr_other hoτ22 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ21
  have hsp_fin : τ22.regs.get? Register.x2 = some (sp - 1088#64) := obs_jr_other hoτ22 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ21
  have hx19_fin : τ22.regs.get? Register.x19 = some w19 := obs_jr_other hoτ22 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ21
  obtain ⟨vmifin, hmifin⟩ := obs_jr_minstret hoτ22
  have hout_fin : τ22.sailOutput = out0 := by rw [hoτ22.out, sailOutput_sigmaPost_jump_x0]; exact houtτ21
  have hcode_fin : Eval_exprLoaded τ22.mem := by rw [hmemτ22e]; exact hcode_vi
  --------------------------------------------------------------------------------
  -- ASSEMBLE `PreEpilogueVD` at 0x800033ec.
  --------------------------------------------------------------------------------
  -- agreement `c.σ.mem ↔ m5` outside the whole stack region `[SL.lo, SL.hi)`
  -- (the 5 error stores land at `sp-{848,840,832}`, all `≥ SL.lo`).
  have hAgSL_m5 : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = m5[k]? := by
    intro k hk
    show c.σ.mem[k]? = (writeMap8 m4 (sp.toNat - 832) D5)[k]?
    rw [getElem_writeMap8_disjoint m4 (sp.toNat - 832) k D5 (by omega)]
    show c.σ.mem[k]? = (writeMap8 m3 (sp.toNat - 840) D4)[k]?
    rw [getElem_writeMap8_disjoint m3 (sp.toNat - 840) k D4 (by omega)]
    show c.σ.mem[k]? = (writeMap8 m2 (sp.toNat - 848) D3)[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat - 848) k D3 (by omega)]
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat - 832) D2)[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat - 832) k D2 (by omega)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat - 848) D1)[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) k D1 (by omega)]
  -- `c.σ.mem ↔ τ22.mem (= cvi.σ.mem)` outside `[SL.lo, SL.hi)`: also value_int's
  -- `sret` write is inside SL (`sret ∈ SL`).
  have hSLfin : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = τ22.mem[k]? := by
    intro k hk
    rw [hmemτ22e]
    rw [← hmemframevi k (by rcases hsretInSL with ⟨hl, hr⟩; omega), hmemτ20e]
    exact hAgSL_m5 k hk
  -- StoreRepr at the extended maps survives to τ22.mem
  have hstore_fin : StoreRepr τ22.mem N A φf' φc' st''.store :=
    hstoreSurv' τ22.mem (fun k hk => hSLfin k hk)
  have hSurvSL_fin : ∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → τ22.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st''.store :=
    fun m' hm' => hstoreSurv' m' (fun k hk => (hSLfin k hk).trans (hm' k hk))
  -- MemExtends m0 τ22.mem (m0 → c.σ.mem via TwoSubReturn's MemExtends... wait m0 is the
  -- case-entry mem; `hMemExt : MemExtends m0 c.σ.mem`). Chain through the 5 stores + sret.
  have hMemExt_c_5 : MemExtends c.σ.mem m5 :=
    ((memExtends_writeMap8 c.σ.mem (sp.toNat - 848) D1).trans
      (memExtends_writeMap8 m1 (sp.toNat - 832) D2)).trans
      (((memExtends_writeMap8 m2 (sp.toNat - 848) D3).trans
        (memExtends_writeMap8 m3 (sp.toNat - 840) D4)).trans
        (memExtends_writeMap8 m4 (sp.toNat - 832) D5))
  have hMemExt_5_22 : MemExtends m5 τ22.mem := by
    intro k bb hbb
    rw [hmemτ22e]
    exact hpresvi k bb (by rw [hmemτ20e]; exact hbb)
  have hMemExt_fin : MemExtends m0 τ22.mem :=
    (hMemExt.trans hMemExt_c_5).trans hMemExt_5_22
  -- the four OUTER spill slots survive (top 32 bytes, disjoint from all writes)
  -- `c.σ.mem ↔ m5` on the top 32 bytes (disjoint from the 5 store windows below sp-40)
  have hAgTop_m5 : AgreeP (fun k => sp.toNat - 32 ≤ k ∧ k < sp.toNat) c.σ.mem m5 := by
    intro k hk
    show c.σ.mem[k]? = (writeMap8 m4 (sp.toNat - 832) D5)[k]?
    rw [getElem_writeMap8_disjoint m4 (sp.toNat - 832) k D5 (by omega)]
    show c.σ.mem[k]? = (writeMap8 m3 (sp.toNat - 840) D4)[k]?
    rw [getElem_writeMap8_disjoint m3 (sp.toNat - 840) k D4 (by omega)]
    show c.σ.mem[k]? = (writeMap8 m2 (sp.toNat - 848) D3)[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat - 848) k D3 (by omega)]
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat - 832) D2)[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat - 832) k D2 (by omega)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat - 848) D1)[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) k D1 (by omega)]
  have hAgTop : AgreeP (fun k => sp.toNat - 32 ≤ k ∧ k < sp.toNat) c.σ.mem τ22.mem := by
    intro k hk
    rw [hmemτ22e, ← hmemframevi k (by rcases hsretStk with h | h <;> omega), hmemτ20e]
    exact hAgTop_m5 k hk
  have hslotRa_f : read64 τ22.mem (sp.toNat - 8) = some r.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => ⟨by omega, by omega⟩)]; exact hslotRa
  have hslotS0_f : read64 τ22.mem (sp.toNat - 16) = some v8.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS0
  have hslotS1_f : read64 τ22.mem (sp.toNat - 24) = some v9.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS1
  have hslotS2_f : read64 τ22.mem (sp.toNat - 32) = some v18.toNat := by
    rw [← read64_agreeP hAgTop (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS2
  -- the callee-saved (noise) frame: threads gpre through the whole tail, then the
  -- prologue bridge gpre → g. x19 is restored to v19 (= g x19) by `ld s3`.
  have hframeG : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      τ22.regs.get? R = g R := by
    intro R hR he8 he9 he18 he2
    obtain ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    have hR' : AbiPreservedNoise R := ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    have ne : ∀ {X : Register}, AbiPreserved X = false → (X == R) = false := by
      intro X hX
      rcases hXR : (X == R) with _ | _
      · rfl
      · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hab; exact absurd hab (by decide)
    -- x19 (s3) case: the tail restores it to v19 = g x19; every other AbiPreservedNoise
    -- register is restored to gpre by TwoSubReturn (excl x19) then bridged to g.
    by_cases hx19R : Register.x19 = R
    · subst hx19R
      have : τ22.regs.get? Register.x19 = some v19 := by rw [hx19_fin]; rw [hw19]
      rw [this]; exact hgx19.symm
    · have h19ne : (Register.x19 == R) = false := by
        rcases hXR : (Register.x19 == R) with _ | _
        · rfl
        · rw [beq_iff_eq] at hXR; exact absurd hXR hx19R
      -- collapse the whole tail frame: τ22 ← ... ← c.σ (= gpre) then gpre → g.
      -- every step writes only caller-saved regs (x10..x17) / x1 (jal) / PC / minstret,
      -- plus x19 (excluded above); s3 restore also writes x19 (excluded).
      have fchain : τ22.regs.get? R = c.σ.regs.get? R := by
        have f22 : τ22.regs.get? R = τ21.regs.get? R :=
          (hoτ22.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')
        have f21 : τ21.regs.get? R = cvi.σ.regs.get? R :=
          (hoτ21.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' h19ne hnpc' hmii')
        have fvi : cvi.σ.regs.get? R = τ20.regs.get? R :=
          hframevi R ⟨ne (by decide), ne (by decide), hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
        have f20 : τ20.regs.get? R = τ19.regs.get? R :=
          (hoτ20.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jal _ _ _ _ _ _ R hmi' hpc' (ne (X := Register.x1) (by decide)) hnpc' hmii')
        rw [f22, f21, fvi, f20]
        exact hLadderFrame R hR' he8
      rw [fchain]
      exact (hframe R hR' h19ne).trans (hbridge R hR' he8 he9 he18 he2)
  -- memframe: τ22.mem vs the entry m0
  have hmemframe_fin : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ τ22.mem[a]? = m0[a]? := by
    intro a ha hA
    by_cases hsr : sret.toNat ≤ a ∧ a < sret.toNat + 24
    · exact Or.inl hsr
    · refine Or.inr ?_
      rw [hmemτ22e, ← hmemframevi a hsr, hmemτ20e]
      -- m5[a]? = c.σ.mem[a]? (a outside [SL.lo, sp) ⊇ the 5 store windows) then
      -- c.σ.mem[a]? = m0[a]? (via TwoSubReturn's memframe)
      have hm5c : m5[a]? = c.σ.mem[a]? := by
        show (writeMap8 m4 (sp.toNat - 832) D5)[a]? = c.σ.mem[a]?
        rw [getElem_writeMap8_disjoint m4 (sp.toNat - 832) a D5 (by omega)]
        show (writeMap8 m3 (sp.toNat - 840) D4)[a]? = c.σ.mem[a]?
        rw [getElem_writeMap8_disjoint m3 (sp.toNat - 840) a D4 (by omega)]
        show (writeMap8 m2 (sp.toNat - 848) D3)[a]? = c.σ.mem[a]?
        rw [getElem_writeMap8_disjoint m2 (sp.toNat - 848) a D3 (by omega)]
        show (writeMap8 m1 (sp.toNat - 832) D2)[a]? = c.σ.mem[a]?
        rw [getElem_writeMap8_disjoint m1 (sp.toNat - 832) a D2 (by omega)]
        show (writeMap8 c.σ.mem (sp.toNat - 848) D1)[a]? = c.σ.mem[a]?
        rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) a D1 (by omega)]
      rw [hm5c]; exact hmemframe a ha hA
  -- the full Steps chain c → τ22
  have hchain : Steps c ⟨τ22, j22, cvi.steps + 1 + 1⟩ :=
    hLadderSteps.trans <| (Steps.single hstepτ20).trans <|
    hsvi.trans <| (Steps.single hstepτ21).trans (Steps.single hstepτ22)
  refine ⟨⟨τ22, j22, cvi.steps + 1 + 1⟩, hchain, τ22.mem, φfm, φcm, φf', φc', hpfm, hpcm, hpf', hpc',
    ⟨?_, hMemExt_fin, hSurvSL_fin⟩⟩
  refine ⟨hGτ22, hj22, hpc_fin, hs1_fin, hsp_fin, ⟨vmifin, hmifin⟩,
    hout_fin, houtStr, rfl, hcode_fin, (by rw [hmemτ22e]; exact hvalfinal),
    hstore_fin, hframeG,
    hslotRa_f, hslotS0_f, hslotS1_f, hslotS2_f, hgv8, hgv9, hgv18, hgv2, hmemframe_fin,
    (by omega), hsphiRam, (by omega), (by omega), hsp8, hraAl⟩

/-! ## `binOpSem_add_int` — the spec-side add bridge -/

/-- `binOpSem … .add (.int a) (.int b) = some (.int (wrap64 (a+b)))` (from the
`binOpSem` definition). -/
theorem binOpSem_add_int (s : Store) (a b : Int) :
    binOpSem s .add (.int a) (.int b) = some (.int (wrap64 (a + b))) := rfl

/-! ## `AddResid` — the blockC_add residuals about the POST-`TwoSubReturn` config

Beyond `TwoSubReturn` (which `blockB_binary` produces) and the geometry threaded
through, `blockC_add` needs facts about the post-both-calls machine state `c'`:
the operator token, the operator jump-table slot pin, a fully-populated post-call
memory, and the two head-dropped register/memory values (the LEFT payload word in
`s3`/`x19` and the respilled `vl.kind` word). These are program-structure /
M6-Layout residuals of the two-operand head that a `TwoSubReturn` widening would
carry; here they are gathered as a predicate on the post-call config `c'`. -/
structure AddResid
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (sp r sret aExpr : BitVec 64) (Wl : BitVec 64) (c' : Vsa.Machine.Config) : Prop where
  gx8 : gpre Register.x8 = some aExpr
  opTok : read32 c'.σ.mem (aExpr.toNat + 8) = some 11
  slot : AddSlotPinned c'.σ.mem
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
  codeStk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  viStk : sp.toNat ≤ 0x8000280c ∨ 0x8000281c ≤ SL.lo
  tableStk : opTableBase + 4 ≤ SL.lo ∨ sp.toNat ≤ opTableBase
  sretInSL : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi
  SLloSp : SL.lo + 1088 ≤ sp.toNat
  SLlo : 0x80000000 ≤ SL.lo
  SLwin : tohostAddr + 16 ≤ SL.lo
  sphiRam : sp.toNat ≤ 0x100000000
  sp8 : sp.toNat % 8 = 0
  SLhiRam : SL.hi ≤ 0x100000000
  spSLhi : sp.toNat ≤ SL.hi

/-! ## `evalAddSim` — the `EvalE.binary .add` int-pilot recursive case

Composes `blockB_binary` (two-operand head + TWO recursive calls ⋈ IH_l/IH_r →
`TwoSubReturn` @0x8000351c) ≫ `blockC_add` (operator dispatch + add-int path + s3
restore → `PreEpilogueVD` @0x800033ec) ≫ `blockD_v_rec` (shared epilogue →
`EvalExitD`). RESTRICTED to `op = .add`, `vl = .int a`, `vr = .int b`.

`blockA_k` (prologue + dispatch → the `ArmEntryK` entry `blockB_binary` consumes)
is not re-run here; the `ArmEntryK` at the EX_BINARY arm is taken as the entry
(as `blockB_binary`'s precondition), and the composition threads the two IH.

Conditional on:
* `BinExtras` + the two-operand-head register extras (geometry, the +4352 recursive
  headroom, arena/code/table disjunctions, the `.binary` node `ExprRepr`, the
  pre-call layout population, `MemExtends m0 ment`);
* `hVlSurv` — the LEFT value's survival across the RIGHT sub-call (VACUOUS for the
  int `vl`, discharged inline);
* `AddResid` — the blockC_add residuals about the post-`TwoSubReturn` config (the
  operator token, `AddSlotPinned`, post-call population, and the head-dropped
  s3/kind register+memory values);
* the entry-ghost bridge `g ↔ gpre`. -/
def EvalAddSimGoal : Prop :=
  ∀ (gouter gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (a b : Int)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 Wl : BitVec 64)
    (out0 : Array String) (m0 : Mem),
    EvalIH st d env el st' (.int a) →
    EvalIH st' d env er st'' (.int b) →
    EvalE st d env (.binary .add el er) st'' (.int (wrap64 (a + b))) →
    -- store-size stability across the RIGHT sub-derivation (the intermediate `φfm`/`φcm`
    -- maps carry the sub-store; the two-phase `PhiExtends` chain composes to the OUTER
    -- entry maps only when the frame/closure counts agree — true for the pilot's
    -- store-preserving int-operand evaluations; a general depth-indexed φ-monotonicity
    -- lemma would discharge this from `_hEvalE`).
    st'.store.frames.size = st''.store.frames.size →
    st'.store.closures.size = st''.store.closures.size →
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary .add el er)
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
        -- the blockC_add residuals hold at EVERY config reachable as the
        -- post-`TwoSubReturn` landing (stated ∀-closed over the post config):
        (∀ c' : Vsa.Machine.Config,
          TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
            st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
          AddResid gpre N A SL sp r sret aExpr Wl c') ∧
        -- entry-ghost g bridge (as blockC_add / blockC_neg consume it)
        g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
        g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧ g Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x2 == R) = false →
          gpre R = g R))
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st'' (.int (wrap64 (a + b))) sp r sret m0)

/-- **`evalAddSim`**: the `EvalE.binary .add` (int-pilot) recursive case, composing
`blockB_binary ≫ blockC_add ≫ blockD_v_rec` in the `EvalIH` motive shape. -/
theorem evalAddSim : EvalAddSimGoal := by
  intro gouter gpre g N A SL φf φc st st' st'' d env el er a b
    sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 Wl out0 m0 hIHl hIHr _hEvalE hSizeF hSizeC
  intro c hpre
  obtain ⟨ment, hArm, hBE, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
    hpayL, hexprL, hpayR, hexprR, hMentPop, hMemExtM0,
    hstackBudgetL, hexprBodiesL, hstoreBodiesL,
    hstackBudgetR, hexprBodiesR, hstoreBodiesR, hResid,
    hgv8, hgv9, hgv18, hgv2, hgvx19, hbridge⟩ := hpre
  -- hVlSurv: LEFT value survival across the RIGHT sub-call — VACUOUS for int `vl`.
  have hVlSurv : ∀ (φ : Addr → Nat) (mm mm' : Mem),
      ValueRepr mm N φ (sp.toNat - 968) (.int a) →
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat - 1080) → ¬ (A.lo ≤ k ∧ k < A.hi) →
        ¬ ((sp.toNat - 944) ≤ k ∧ k < (sp.toNat - 944) + 24) → mm[k]? = mm'[k]?) →
      ValueRepr mm' N φ (sp.toNat - 968) (.int a) := by
    intro φ mm mm' hv hag
    have hsproom := hBE.sproom
    obtain ⟨hk, hp⟩ := hv
    -- both the kind word `[sp-968,+4)` and the payload `[sp-960,+8)` live in the
    -- outer frame `[sp-1088, sp)`: disjoint from the right-call frame `[SL.lo, sp-1080)`,
    -- the arena, and the right-sret window `[sp-944, +24)`. So `mm ↔ mm'` there.
    have hAg : AgreeP (fun k => sp.toNat - 968 ≤ k ∧ k < sp.toNat - 952) mm mm' := by
      intro k hk'
      exact hag k (by omega) (by rcases hBE.arenaStk with h | h <;> omega) (by omega)
    refine ⟨?_, ?_⟩
    · rw [← read32_agreeP hAg (fun j hj => ⟨by omega, by omega⟩)]; exact hk
    · rw [readI64] at hp ⊢
      rw [← read64_agreeP hAg (fun j hj => ⟨by omega, by omega⟩)]; exact hp
  -- === block B: two-operand head + IHs → TwoSubReturn @0x8000351c ===
  obtain ⟨c2, hs2, hTS⟩ :=
    blockB_binary gouter gpre N A SL φf φc st st' st'' d env .add el er (.int a) (.int b)
      sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0 hIHl hIHr hVlSurv
      c ⟨ment, hArm, hBE, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
        hpayL, hexprL, hpayR, hexprR, hMentPop, hMemExtM0,
        hstackBudgetL, hexprBodiesL, hstoreBodiesL,
        hstackBudgetR, hexprBodiesR, hstoreBodiesR⟩
  -- the blockC_add residuals at c2
  have hR : AddResid gpre N A SL sp r sret aExpr Wl c2 := hResid c2 hTS
  -- the post-both-calls console output correspondence (`OutRepr c2 st''`)
  have hOutC2 : String.join c2.σ.sailOutput.toList = st''.out := hTS.2.2.2.2.2.2.2.1
  -- === block C: dispatch + add tail → PreEpilogueVD @0x800033ec ===
  obtain ⟨c3, hs3, mpre, φfm, φcm, φfe, φce, hpfm, hpcm, hpfe, hpce, hPreD⟩ :=
    blockC_add gpre g N A SL φf φc st.store.frames.size st.store.closures.size
      st' st'' a b sp r sret aExpr v8 v9 v18 v19 Wl c2.σ.sailOutput m0
      c2 ⟨hTS, hR.gx8, hR.opTok, hR.slot, hR.fullpop, hR.x19, hR.wlbuf, hR.kindresp,
        hR.exprAl, hR.exprLo, hR.exprHi, hR.exprWin, hR.exprSL, hOutC2, rfl,
        hR.sretAl, hR.sretLo, hR.sretHi, hR.sretWin, hR.sretVi, hR.sretStk, hR.sretEvalCode, hR.raAl,
        hR.vint, hR.codeStk, hR.viStk, hR.tableStk, hR.sretInSL,
        hR.SLloSp, hR.SLlo, hR.SLwin, hR.sphiRam, hR.sp8, hR.SLhiRam, hR.spSLhi,
        hgv8, hgv9, hgv18, hgv2, hgx19, hgvx19, hbridge⟩
  -- === block D: shared epilogue → EvalExitD ===
  obtain ⟨c4, hs4, hExitDe⟩ :=
    blockD_v_rec g N A SL φfe φce st'' (.int (wrap64 (a + b))) sp r sret v8 v9 v18 c2.σ.sailOutput m0
      c3 ⟨mpre, hPreD⟩
  obtain ⟨hExitE, hMemExt, φf', φc', hpf', hpc', hSurv⟩ := hExitDe
  -- compose the two-phase φ-chain to the OUTER entry maps (size stability lets the
  -- `st'`-sized left leg meet the `st''`-sized right leg).
  have hmono := evalE_store_mono _hEvalE
  have hleF' : st.store.frames.size ≤ st'.store.frames.size := hSizeF ▸ hmono.1
  have hleC' : st.store.closures.size ≤ st'.store.closures.size := hSizeC ▸ hmono.2
  have hpfF : PhiExtends φf φfe st.store.frames.size := hpfm.trans (PhiExtends.mono hleF' hpfe)
  have hpcF : PhiExtends φc φce st.store.closures.size := hpcm.trans (PhiExtends.mono hleC' hpce)
  have hExit : EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st'' (.int (wrap64 (a + b))) sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfF hpcF hExitE hmono.1 hmono.2
  exact ⟨c4, ((hs2.trans hs3).trans hs4), hExit, hMemExt,
    φf', φc', hpfF.trans (PhiExtends.mono hmono.1 hpf'),
    hpcF.trans (PhiExtends.mono hmono.2 hpc'), hSurv⟩

end Vsa.Sim
