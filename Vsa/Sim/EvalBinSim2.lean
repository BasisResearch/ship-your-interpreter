import Vsa.Sim.EvalBinSim
import Vsa.Sim.EvalNegSim3
import Vsa.Sim.AddTailSites

/-!
# Layer 4 — M4 RECURSIVE case: `evalAddSim` (the `EvalE.binary .add` int pilot)

Composes the two-operand binary arm of `eval_expr` for `op = .add` on two
integer operands, in the `EvalIH` motive shape (`EvalEntry → EvalExitD`) taking
TWO induction hypotheses (LEFT `el` over `st→st'`, RIGHT `er` over `st'→st''`):

```
blockA_k        (prologue + dispatch → widened ArmEntryK @0x800034e8)
  ≫ blockB_binary (arm head + TWO recursive calls ⋈ IH_l/IH_r → TwoSubReturn @0x8000351c)
  ≫ blockC_add    (operator dispatch tail + add-int path + s3 restore
                    → PreEpilogueVD .int(wrap64 (a+b)) @0x800033ec)
  ≫ blockD_v_rec  (shared epilogue → EvalExitD .int(wrap64 (a+b)))
```

The operator dispatch tail decodes the token (`lw a2,8(s0)`; `addiw a5,a2,-11`;
`bltu a4,a5` range-check; `slli`/`srli`/`auipc`/`lw`/`jr` jump-table dispatch off
the `CSWTCH.18` operator table at `0x80019f84`) landing at the ADD-int arm
`0x80003888`, where the machine computes `add a1,s3,a7` (`s3 = vl.payload`,
`a7 = vr.payload`), wrapping at 64 bits, and calls `value_int(sret, a+b)` — so
the produced value is `.int (wrap64 (a+b))` (`add_wrap_bridge`).

`blockD_v_rec` (not a bespoke `blockD_add`) is reused: the `ld s3,1048(sp)` s3
restore sits INSIDE the add tail (before the `j 0x800033ec`), so by the epilogue
entry `x19` is already back to its entry value, and the epilogue register set is
the standard one.

RESTRICTED to `op = .add`, `vl = .int a`, `vr = .int b`. `blockC_add` carries two
register/memory residuals that a `blockB_binary`/`TwoSubReturn` widening would
discharge (they are values the head knows but `TwoSubReturn` drops):
* `hX19` — `x19 (s3) = Wl`, the LEFT payload word (read by `add a1,s3,a7`), tied
  to `a` via `read64 (sp-960) = Wl.toNat` + the LEFT `ValueRepr`;
* `hKindResp` — `read64 (sp-1088) = (2#64).toNat`, the respilled `vl.kind` word
  (read by `ld a6,0(sp)` and used in the `bne`/`beqz` int-kind guards).

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

/-! ## The `wrap64` bridge for the `add` exit value -/

/-- `value_int` produces `.int (BitVec.ofNat 64 pay.toNat).toInt` with the payload
`pay = Wl + Wr` (the machine 64-bit `add`). Since `Wl.toInt = a`, `Wr.toInt = b`
(the operands' `.int` `ValueRepr` payloads), this equals `.int (wrap64 (a + b))`. -/
theorem add_wrap_bridge (Wl Wr : BitVec 64) (a b : Int)
    (ha : Wl.toInt = a) (hb : Wr.toInt = b) :
    (BitVec.ofNat 64 (Wl + Wr).toNat).toInt = wrap64 (a + b) := by
  rw [ofNat_toNat_self64, ← ha, ← hb]
  unfold wrap64
  rw [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt]

/-! ## `AddSlotPinned` — the operator jump-table slot pin for `.add`

The `CSWTCH.18` operator table lives at `0x80019f84` (`= 0x80019f58 + 0x2c`);
slot `op-index` (`= binOpTok op - 11`) at `+ 4*index`, storing a signed 32-bit
offset added back to the table base. `.add` (token 11, index 0) → slot bytes
`04 99 fe ff` @ `0x80019f84`, target `0x80019f84 + (Int32)0xfffe9904 = 0x80003888`. -/
def opTableBase : Nat := 0x80019f84

def AddSlotPinned (m : Mem) : Prop :=
  m[(opTableBase + 0 : Nat)]? = some (0x04 : BitVec 8) ∧
  m[(opTableBase + 1 : Nat)]? = some (0x99 : BitVec 8) ∧
  m[(opTableBase + 2 : Nat)]? = some (0xfe : BitVec 8) ∧
  m[(opTableBase + 3 : Nat)]? = some (0xff : BitVec 8)

/-- `AddSlotPinned` survives a `writeMap8` disjoint from `[opTableBase, +4)`. -/
theorem addSlot_writeMap8 (m : Mem) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ opTableBase ∨ opTableBase + 4 ≤ a8) (h : AddSlotPinned m) :
    AddSlotPinned (writeMap8 m a8 d) := by
  obtain ⟨p0, p1, p2, p3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (rw [getElem_writeMap8_disjoint m a8 _ d (by omega)]; assumption)

/-! ## `blockC_add` — the operator dispatch tail + add-int path → `PreEpilogueVD`

From `TwoSubReturn @0x8000351c` (both sub-values `vl=.int a`@sp-968,
`vr=.int b`@sp-944 represented; s3 spill slot holds the entry s3; store
re-represented for `st''`) plus the geometry + the two head-dropped register/mem
residuals, `blockC_add` runs the operator dispatch (→ arm `0x80003888`), the
add-int path (kind checks, `add a1,s3,a7`, `value_int`, `ld s3` restore), and the
`j 0x800033ec`, producing `PreEpilogueVD g … .int(wrap64 (a+b))`. -/
theorem blockC_add
    (gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' st'' : Vsa.While.St) (a b : Int)
    (sp r sret aExpr : BitVec 64) (v8 v9 v18 v19 Wl : BitVec 64) (out0 : Array String)
    (m0 : Mem) :
    Triple
      (fun c =>
        TwoSubReturn gpre N A SL φf φc st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c ∧
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
        PhiExtends φf φfm st'.store.frames.size ∧
        PhiExtends φc φcm st'.store.closures.size ∧
        PhiExtends φfm φfe st''.store.frames.size ∧
        PhiExtends φcm φce st''.store.closures.size ∧
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
  -- 0x8000351c: lw a2,8(s0) → x12 := 11#64
  --------------------------------------------------------------------------------
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    site_8000351c_ee c.σ c.tick c.steps (0x8000351c#64) vmi aExpr ob0 ob1 ob2 ob3
      hG hpc hmi hx8c hcode rfl
      (by rw [hop8]; omega) (by rw [hop8]; omega)
      (by rw [hop8, htoh]; right; omega) (by rw [hop8]; omega)
      (by rw [hop8]; exact hob0) (by rw [hop8]; exact hob1)
      (by rw [hop8]; exact hob2) (by rw [hop8]; exact hob3) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = c.σ.mem := hmem1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80003520#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000351c#64) 4 = (0x80003520#64 : BitVec 64) from by decide] at this
  have hx12_1 : σ1.regs.get? Register.x12 = some (11#64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hopVal] at this
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_alu_other hobs1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp
  have hx19_1 : σ1.regs.get? Register.x19 = some Wl := obs_alu_other hobs1 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hX19
  have hx8_1 : σ1.regs.get? Register.x8 = some aExpr := obs_alu_other hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8c
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by rw [hobs1.out, sailOutput_sigmaPost_alu]; exact hout0eq
  have hcode1 : Eval_exprLoaded σ1.mem := by rw [hmem1e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003520: li a4,12 → x14 := 12#64
  --------------------------------------------------------------------------------
  obtain ⟨σ2, i2, hs2', hi2, hG2, hmem2, hobs2⟩ :=
    site_80003520_ee σ1 i1 (c.steps + 1) (0x80003520#64) vmi1 hG1 hpc1 hmi1 hcode1 rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2'
  have hmem2e : σ2.mem = c.σ.mem := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x80003524#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80003520#64) 4 = (0x80003524#64 : BitVec 64) from by decide] at this
  have hx14_2 : σ2.regs.get? Register.x14 = some (12#64) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64 : BitVec 64) + sign_extend (m := 64) (0x00c#12)) = (12#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx12_2 : σ2.regs.get? Register.x12 = some (11#64) := obs_alu_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_1
  have hs1_2 : σ2.regs.get? Register.x9 = some sret := obs_alu_other hobs2 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_1
  have hx19_2 : σ2.regs.get? Register.x19 = some Wl := obs_alu_other hobs2 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_1
  have hx8_2 : σ2.regs.get? Register.x8 = some aExpr := obs_alu_other hobs2 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hout2 : σ2.sailOutput = out0 := by rw [hobs2.out, sailOutput_sigmaPost_alu]; exact hout1
  have hcode2 : Eval_exprLoaded σ2.mem := by rw [hmem2e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003524: lw s0,4(s0) → x8 := e->line (dead)
  --------------------------------------------------------------------------------
  obtain ⟨σ3, i3, hs3', hi3, hG3, hmem3, hobs3⟩ :=
    site_80003524_ee σ2 i2 (c.steps + 1 + 1) (0x80003524#64) vmi2 aExpr lb0 lb1 lb2 lb3
      hG2 hpc2 hmi2 hx8_2 hcode2 rfl
      (by rw [hline4]; omega) (by rw [hline4]; omega)
      (by rw [hline4, htoh]; right; omega) (by rw [hline4]; omega)
      (by rw [hline4, hmem2e]; exact hlb0) (by rw [hline4, hmem2e]; exact hlb1)
      (by rw [hline4, hmem2e]; exact hlb2) (by rw [hline4, hmem2e]; exact hlb3) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3'
  have hmem3e : σ3.mem = c.σ.mem := by rw [hmem3]; exact hmem2e
  have hpc3 : σ3.regs.get? Register.PC = some (0x80003528#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80003524#64) 4 = (0x80003528#64 : BitVec 64) from by decide] at this
  have hx14_3 : σ3.regs.get? Register.x14 = some (12#64) := obs_alu_other hobs3 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_2
  have hx12_3 : σ3.regs.get? Register.x12 = some (11#64) := obs_alu_other hobs3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_2
  have hs1_3 : σ3.regs.get? Register.x9 = some sret := obs_alu_other hobs3 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_2
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_2
  have hx19_3 : σ3.regs.get? Register.x19 = some Wl := obs_alu_other hobs3 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hout3 : σ3.sailOutput = out0 := by rw [hobs3.out, sailOutput_sigmaPost_alu]; exact hout2
  have hcode3 : Eval_exprLoaded σ3.mem := by rw [hmem3e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003528: addiw a5,a2,-11 → x15 := 0#64
  --------------------------------------------------------------------------------
  obtain ⟨σ4, i4, hs4', hi4, hG4, hmem4, hobs4⟩ :=
    site_80003528_ee σ3 i3 (c.steps + 1 + 1 + 1) (0x80003528#64) vmi3 (11#64) hG3 hpc3 hmi3 hx12_3 hcode3 rfl hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4'
  have hmem4e : σ4.mem = c.σ.mem := by rw [hmem4]; exact hmem3e
  have hpc4 : σ4.regs.get? Register.PC = some (0x8000352c#64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x80003528#64) 4 = (0x8000352c#64 : BitVec 64) from by decide] at this
  have hx15_4 : σ4.regs.get? Register.x15 = some (0#64) := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((11#64 : BitVec 64) + sign_extend (m := 64) (0xff5#12)) 31 0)) = (0#64 : BitVec 64) from by
        apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_4 : σ4.regs.get? Register.x14 = some (12#64) := obs_alu_other hobs4 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_3
  have hs1_4 : σ4.regs.get? Register.x9 = some sret := obs_alu_other hobs4 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_3
  have hsp_4 : σ4.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_3
  have hx19_4 : σ4.regs.get? Register.x19 = some Wl := obs_alu_other hobs4 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hout4 : σ4.sailOutput = out0 := by rw [hobs4.out, sailOutput_sigmaPost_alu]; exact hout3
  have hcode4 : Eval_exprLoaded σ4.mem := by rw [hmem4e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x8000352c: lw a0,144(sp) → x10 := vr.kind = 2#64
  --------------------------------------------------------------------------------
  obtain ⟨σ5, i5, hs5', hi5, hG5, hmem5, hobs5⟩ :=
    site_8000352c_ee σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x8000352c#64) vmi4 (sp - 1088#64)
      rkb0 rkb1 rkb2 rkb3 hG4 hpc4 hmi4 hsp_4 hcode4 rfl
      (by rw [haddr144]; omega) (by rw [haddr144]; omega)
      (by rw [haddr144, htoh]; right; omega) (by rw [haddr144]; omega)
      (by rw [haddr144, hmem4e]; exact hrkb0) (by rw [haddr144, hmem4e]; exact hrkb1)
      (by rw [haddr144, hmem4e]; exact hrkb2) (by rw [haddr144, hmem4e]; exact hrkb3) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5'
  have hmem5e : σ5.mem = c.σ.mem := by rw [hmem5]; exact hmem4e
  have hpc5 : σ5.regs.get? Register.PC = some (0x80003530#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x8000352c#64) 4 = (0x80003530#64 : BitVec 64) from by decide] at this
  have hx10_5 : σ5.regs.get? Register.x10 = some (2#64) := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hRkindVal] at this
  have hx15_5 : σ5.regs.get? Register.x15 = some (0#64) := obs_alu_other hobs5 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_4
  have hx14_5 : σ5.regs.get? Register.x14 = some (12#64) := obs_alu_other hobs5 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_4
  have hs1_5 : σ5.regs.get? Register.x9 = some sret := obs_alu_other hobs5 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_4
  have hsp_5 : σ5.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_4
  have hx19_5 : σ5.regs.get? Register.x19 = some Wl := obs_alu_other hobs5 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_4
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hout5 : σ5.sailOutput = out0 := by rw [hobs5.out, sailOutput_sigmaPost_alu]; exact hout4
  have hcode5 : Eval_exprLoaded σ5.mem := by rw [hmem5e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003530: ld a7,152(sp) → x17 := vr.payload word = Wr
  --------------------------------------------------------------------------------
  obtain ⟨σ6, i6, hs6', hi6, hG6, hmem6, hobs6⟩ :=
    site_80003530_ee σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80003530#64) vmi5 (sp - 1088#64)
      rpb0 rpb1 rpb2 rpb3 rpb4 rpb5 rpb6 rpb7 hG5 hpc5 hmi5 hsp_5 hcode5 rfl
      (by rw [haddr152]; omega) (by rw [haddr152]; omega)
      (by rw [haddr152, htoh]; right; omega) (by rw [haddr152]; omega)
      (by rw [haddr152, hmem5e]; have e : sp.toNat - 944 + 8 = sp.toNat - 936 := by omega
          rw [← e]; exact hrpb0)
      (by rw [haddr152, hmem5e]; have e : sp.toNat - 944 + 8 = sp.toNat - 936 := by omega
          rw [show sp.toNat - 936 + 1 = sp.toNat - 944 + 8 + 1 from by omega]; exact hrpb1)
      (by rw [haddr152, hmem5e]; rw [show sp.toNat - 936 + 2 = sp.toNat - 944 + 8 + 2 from by omega]; exact hrpb2)
      (by rw [haddr152, hmem5e]; rw [show sp.toNat - 936 + 3 = sp.toNat - 944 + 8 + 3 from by omega]; exact hrpb3)
      (by rw [haddr152, hmem5e]; rw [show sp.toNat - 936 + 4 = sp.toNat - 944 + 8 + 4 from by omega]; exact hrpb4)
      (by rw [haddr152, hmem5e]; rw [show sp.toNat - 936 + 5 = sp.toNat - 944 + 8 + 5 from by omega]; exact hrpb5)
      (by rw [haddr152, hmem5e]; rw [show sp.toNat - 936 + 6 = sp.toNat - 944 + 8 + 6 from by omega]; exact hrpb6)
      (by rw [haddr152, hmem5e]; rw [show sp.toNat - 936 + 7 = sp.toNat - 944 + 8 + 7 from by omega]; exact hrpb7) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs6'
  have hmem6e : σ6.mem = c.σ.mem := by rw [hmem6]; exact hmem5e
  have hpc6 : σ6.regs.get? Register.PC = some (0x80003534#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x80003530#64) 4 = (0x80003534#64 : BitVec 64) from by decide] at this
  have hx17_6 : σ6.regs.get? Register.x17 = some Wr := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    exact this
  have hx10_6 : σ6.regs.get? Register.x10 = some (2#64) := obs_alu_other hobs6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_5
  have hx15_6 : σ6.regs.get? Register.x15 = some (0#64) := obs_alu_other hobs6 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_5
  have hx14_6 : σ6.regs.get? Register.x14 = some (12#64) := obs_alu_other hobs6 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_5
  have hs1_6 : σ6.regs.get? Register.x9 = some sret := obs_alu_other hobs6 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_5
  have hsp_6 : σ6.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs6 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_5
  have hx19_6 : σ6.regs.get? Register.x19 = some Wl := obs_alu_other hobs6 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_5
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hout6 : σ6.sailOutput = out0 := by rw [hobs6.out, sailOutput_sigmaPost_alu]; exact hout5
  have hcode6 : Eval_exprLoaded σ6.mem := by rw [hmem6e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003534: bltu a4,a5 (NOT taken; 12 <u 0 is false)
  --------------------------------------------------------------------------------
  obtain ⟨σ7, i7, hs7', hi7, hG7, hmem7, hobs7⟩ :=
    site_80003534_nottaken_ee σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80003534#64) vmi6 (12#64) (0#64)
      hG6 hpc6 hmi6 hx14_6 hx15_6 hcode6 rfl (by decide) hi6
  have hstep7 : Step ⟨σ6, i6, _⟩ ⟨σ7, i7, _⟩ := hs7'
  have hmem7e : σ7.mem = c.σ.mem := by rw [hmem7]; exact hmem6e
  have hpc7 : σ7.regs.get? Register.PC = some (0x80003538#64) := by
    have := obs_branch_nottaken_pc hobs7
    rwa [show BitVec.addInt (0x80003534#64) 4 = (0x80003538#64 : BitVec 64) from by decide] at this
  have hx15_7 : σ7.regs.get? Register.x15 = some (0#64) := obs_branch_nottaken_other hobs7 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_6
  have hx17_7 : σ7.regs.get? Register.x17 = some Wr := obs_branch_nottaken_other hobs7 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_6
  have hx10_7 : σ7.regs.get? Register.x10 = some (2#64) := obs_branch_nottaken_other hobs7 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_6
  have hs1_7 : σ7.regs.get? Register.x9 = some sret := obs_branch_nottaken_other hobs7 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_6
  have hsp_7 : σ7.regs.get? Register.x2 = some (sp - 1088#64) := obs_branch_nottaken_other hobs7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_6
  have hx19_7 : σ7.regs.get? Register.x19 = some Wl := obs_branch_nottaken_other hobs7 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_6
  obtain ⟨vmi7, hmi7⟩ := obs_branch_nottaken_minstret hobs7
  have hout7 : σ7.sailOutput = out0 := by rw [hobs7.out, sailOutput_sigmaPost_branch_nottaken]; exact hout6
  have hcode7 : Eval_exprLoaded σ7.mem := by rw [hmem7e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003538: slli a4,a5,0x20 → x14 := 0
  --------------------------------------------------------------------------------
  obtain ⟨σ8, i8, hs8', hi8, hG8, hmem8, hobs8⟩ :=
    site_80003538_ee σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003538#64) vmi7 (0#64) hG7 hpc7 hmi7 hx15_7 hcode7 rfl hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs8'
  have hmem8e : σ8.mem = c.σ.mem := by rw [hmem8]; exact hmem7e
  have hpc8 : σ8.regs.get? Register.PC = some (0x8000353c#64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x80003538#64) 4 = (0x8000353c#64 : BitVec 64) from by decide] at this
  have hx14_8 : σ8.regs.get? Register.x14 = some (0#64) := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (shift_bits_left (0#64 : BitVec 64) (Sail.BitVec.extractLsb (0x20#6) 5 0)) = (0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx17_8 : σ8.regs.get? Register.x17 = some Wr := obs_alu_other hobs8 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_7
  have hx10_8 : σ8.regs.get? Register.x10 = some (2#64) := obs_alu_other hobs8 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_7
  have hs1_8 : σ8.regs.get? Register.x9 = some sret := obs_alu_other hobs8 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_7
  have hsp_8 : σ8.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs8 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_7
  have hx19_8 : σ8.regs.get? Register.x19 = some Wl := obs_alu_other hobs8 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_7
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hout8 : σ8.sailOutput = out0 := by rw [hobs8.out, sailOutput_sigmaPost_alu]; exact hout7
  have hcode8 : Eval_exprLoaded σ8.mem := by rw [hmem8e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x8000353c: srli a5,a4,0x1e → x15 := 0
  --------------------------------------------------------------------------------
  obtain ⟨σ9, i9, hs9', hi9, hG9, hmem9, hobs9⟩ :=
    site_8000353c_ee σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000353c#64) vmi8 (0#64) hG8 hpc8 hmi8 hx14_8 hcode8 rfl hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs9'
  have hmem9e : σ9.mem = c.σ.mem := by rw [hmem9]; exact hmem8e
  have hpc9 : σ9.regs.get? Register.PC = some (0x80003540#64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x8000353c#64) 4 = (0x80003540#64 : BitVec 64) from by decide] at this
  have hx15_9 : σ9.regs.get? Register.x15 = some (0#64) := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (shift_bits_right (0#64 : BitVec 64) (Sail.BitVec.extractLsb (0x1e#6) 5 0)) = (0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx17_9 : σ9.regs.get? Register.x17 = some Wr := obs_alu_other hobs9 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_8
  have hx10_9 : σ9.regs.get? Register.x10 = some (2#64) := obs_alu_other hobs9 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_8
  have hs1_9 : σ9.regs.get? Register.x9 = some sret := obs_alu_other hobs9 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_8
  have hsp_9 : σ9.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs9 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_8
  have hx19_9 : σ9.regs.get? Register.x19 = some Wl := obs_alu_other hobs9 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_8
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have hout9 : σ9.sailOutput = out0 := by rw [hobs9.out, sailOutput_sigmaPost_alu]; exact hout8
  have hcode9 : Eval_exprLoaded σ9.mem := by rw [hmem9e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003540: auipc a4,0x17 → x14 := 0x80003540 + 0x17000
  --------------------------------------------------------------------------------
  obtain ⟨σ10, i10, hs10', hi10, hG10, hmem10, hobs10⟩ :=
    site_80003540_ee σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003540#64) vmi9 hG9 hpc9 hmi9 hcode9 rfl hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ10, i10, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs10'
  have hmem10e : σ10.mem = c.σ.mem := by rw [hmem10]; exact hmem9e
  have hpc10 : σ10.regs.get? Register.PC = some (0x80003544#64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x80003540#64) 4 = (0x80003544#64 : BitVec 64) from by decide] at this
  have hx14_10 : σ10.regs.get? Register.x14 = some ((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12)) :=
    obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx15_10 : σ10.regs.get? Register.x15 = some (0#64) := obs_alu_other hobs10 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_9
  have hx17_10 : σ10.regs.get? Register.x17 = some Wr := obs_alu_other hobs10 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_9
  have hx10_10 : σ10.regs.get? Register.x10 = some (2#64) := obs_alu_other hobs10 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_9
  have hs1_10 : σ10.regs.get? Register.x9 = some sret := obs_alu_other hobs10 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_9
  have hsp_10 : σ10.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs10 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_9
  have hx19_10 : σ10.regs.get? Register.x19 = some Wl := obs_alu_other hobs10 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_9
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hout10 : σ10.sailOutput = out0 := by rw [hobs10.out, sailOutput_sigmaPost_alu]; exact hout9
  have hcode10 : Eval_exprLoaded σ10.mem := by rw [hmem10e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003544: addi a4,a4,-1468 → x14 := 0x80019f84 (op table base)
  --------------------------------------------------------------------------------
  obtain ⟨σ11, i11, hs11', hi11, hG11, hmem11, hobs11⟩ :=
    site_80003544_ee σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003544#64) vmi10 ((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
      hG10 hpc10 hmi10 hx14_10 hcode10 rfl hi10
  have hstep11 : Step ⟨σ10, i10, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ11, i11, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs11'
  have hmem11e : σ11.mem = c.σ.mem := by rw [hmem11]; exact hmem10e
  have hpc11 : σ11.regs.get? Register.PC = some (0x80003548#64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x80003544#64) 4 = (0x80003548#64 : BitVec 64) from by decide] at this
  have hx14_11 : σ11.regs.get? Register.x14 = some (0x80019f84#64) := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
      + sign_extend (m := 64) (0xa44#12)) = (0x80019f84#64 : BitVec 64) from by
        apply BitVec.eq_of_toNat_eq; decide] at this
  have hx15_11 : σ11.regs.get? Register.x15 = some (0#64) := obs_alu_other hobs11 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_10
  have hx17_11 : σ11.regs.get? Register.x17 = some Wr := obs_alu_other hobs11 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_10
  have hx10_11 : σ11.regs.get? Register.x10 = some (2#64) := obs_alu_other hobs11 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_10
  have hs1_11 : σ11.regs.get? Register.x9 = some sret := obs_alu_other hobs11 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_10
  have hsp_11 : σ11.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs11 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_10
  have hx19_11 : σ11.regs.get? Register.x19 = some Wl := obs_alu_other hobs11 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_10
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hout11 : σ11.sailOutput = out0 := by rw [hobs11.out, sailOutput_sigmaPost_alu]; exact hout10
  have hcode11 : Eval_exprLoaded σ11.mem := by rw [hmem11e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003548: add a5,a5,a4 → x15 := 0 + 0x80019f84 = 0x80019f84
  --------------------------------------------------------------------------------
  obtain ⟨σ12, i12, hs12', hi12, hG12, hmem12, hobs12⟩ :=
    site_80003548_ee σ11 i11 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003548#64) vmi11 (0#64) (0x80019f84#64) hG11 hpc11 hmi11 hx15_11 hx14_11 hcode11 rfl hi11
  have hstep12 : Step ⟨σ11, i11, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ12, i12, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs12'
  have hmem12e : σ12.mem = c.σ.mem := by rw [hmem12]; exact hmem11e
  have hpc12 : σ12.regs.get? Register.PC = some (0x8000354c#64) := by
    have := obs_alu_pc hobs12
    rwa [show BitVec.addInt (0x80003548#64) 4 = (0x8000354c#64 : BitVec 64) from by decide] at this
  have hx15_12 : σ12.regs.get? Register.x15 = some (0x80019f84#64) := by
    have := obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64 : BitVec 64) + (0x80019f84#64 : BitVec 64)) = (0x80019f84#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_12 : σ12.regs.get? Register.x14 = some (0x80019f84#64) := obs_alu_other hobs12 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_11
  have hx17_12 : σ12.regs.get? Register.x17 = some Wr := obs_alu_other hobs12 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_11
  have hx10_12 : σ12.regs.get? Register.x10 = some (2#64) := obs_alu_other hobs12 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_11
  have hs1_12 : σ12.regs.get? Register.x9 = some sret := obs_alu_other hobs12 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_11
  have hsp_12 : σ12.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs12 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_11
  have hx19_12 : σ12.regs.get? Register.x19 = some Wl := obs_alu_other hobs12 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_11
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  have hout12 : σ12.sailOutput = out0 := by rw [hobs12.out, sailOutput_sigmaPost_alu]; exact hout11
  have hcode12 : Eval_exprLoaded σ12.mem := by rw [hmem12e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x8000354c: lw a5,0(a5) → x15 := sext(slot bytes @0x80019f84)
  --------------------------------------------------------------------------------
  obtain ⟨hsb0, hsb1, hsb2, hsb3⟩ := hSlot
  have hslotAddr : ((0x80019f84#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)).toNat = 0x80019f84 := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide,
      BitVec.add_zero]; decide
  obtain ⟨σ13, i13, hs13', hi13, hG13, hmem13, hobs13⟩ :=
    site_8000354c_ee σ12 i12 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000354c#64) vmi12 (0x80019f84#64)
      (0x04#8) (0x99#8) (0xfe#8) (0xff#8) hG12 hpc12 hmi12 hx15_12 hcode12 rfl
      (by rw [hslotAddr]; omega) (by rw [hslotAddr]; omega)
      (by rw [hslotAddr]; rw [htoh]; left; omega) (by rw [hslotAddr])
      (by rw [hslotAddr]; exact (hmem12e ▸ hsb0)) (by rw [hslotAddr]; exact (hmem12e ▸ hsb1))
      (by rw [hslotAddr]; exact (hmem12e ▸ hsb2)) (by rw [hslotAddr]; exact (hmem12e ▸ hsb3)) hi12
  have hstep13 : Step ⟨σ12, i12, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ13, i13, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs13'
  have hmem13e : σ13.mem = c.σ.mem := by rw [hmem13]; exact hmem12e
  have hpc13 : σ13.regs.get? Register.PC = some (0x80003550#64) := by
    have := obs_alu_pc hobs13
    rwa [show BitVec.addInt (0x8000354c#64) 4 = (0x80003550#64 : BitVec 64) from by decide] at this
  have hx15_13 : σ13.regs.get? Register.x15 = some (0xfffffffffffe9904#64) := by
    have := obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64) ((((0xff#8).append (0xfe#8)).append (0x99#8)).append (0x04#8) : BitVec (8*4)))
      = (0xfffffffffffe9904#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx14_13 : σ13.regs.get? Register.x14 = some (0x80019f84#64) := obs_alu_other hobs13 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_12
  have hx17_13 : σ13.regs.get? Register.x17 = some Wr := obs_alu_other hobs13 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_12
  have hx10_13 : σ13.regs.get? Register.x10 = some (2#64) := obs_alu_other hobs13 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_12
  have hs1_13 : σ13.regs.get? Register.x9 = some sret := obs_alu_other hobs13 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_12
  have hsp_13 : σ13.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs13 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_12
  have hx19_13 : σ13.regs.get? Register.x19 = some Wl := obs_alu_other hobs13 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_12
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  have hout13 : σ13.sailOutput = out0 := by rw [hobs13.out, sailOutput_sigmaPost_alu]; exact hout12
  have hcode13 : Eval_exprLoaded σ13.mem := by rw [hmem13e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003550: ld a6,0(sp) → x16 := respilled vl.kind = 2#64
  --------------------------------------------------------------------------------
  obtain ⟨kb0, kb1, kb2, kb3, kb4, kb5, kb6, kb7, hkb0, hkb1, hkb2, hkb3, hkb4, hkb5, hkb6, hkb7, hkbrec⟩ :=
    read64_bytes c.σ.mem (sp.toNat - 1088) (2#64 : BitVec 64).toNat hKindResp
  obtain ⟨σ14, i14, hs14', hi14, hG14, hmem14, hobs14⟩ :=
    site_80003550_ee σ13 i13 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003550#64) vmi13 (sp - 1088#64)
      kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7 hG13 hpc13 hmi13 hsp_13 hcode13 rfl
      (by rw [haddr0]; omega) (by rw [haddr0]; omega)
      (by rw [haddr0, htoh]; right; omega) (by rw [haddr0]; omega)
      (by rw [haddr0, hmem13e]; exact hkb0) (by rw [haddr0, hmem13e]; exact hkb1)
      (by rw [haddr0, hmem13e]; exact hkb2) (by rw [haddr0, hmem13e]; exact hkb3)
      (by rw [haddr0, hmem13e]; exact hkb4) (by rw [haddr0, hmem13e]; exact hkb5)
      (by rw [haddr0, hmem13e]; exact hkb6) (by rw [haddr0, hmem13e]; exact hkb7) hi13
  have hstep14 : Step ⟨σ13, i13, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ14, i14, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs14'
  have hmem14e : σ14.mem = c.σ.mem := by rw [hmem14]; exact hmem13e
  have hpc14 : σ14.regs.get? Register.PC = some (0x80003554#64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x80003550#64) 4 = (0x80003554#64 : BitVec 64) from by decide] at this
  have hx16_14 : σ14.regs.get? Register.x16 = some (2#64) := by
    have := obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64) ((((((((kb7.append kb6).append kb5).append kb4).append kb3).append kb2).append kb1).append kb0) : BitVec (8*8)))
        = (2#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; rw [sext_full, word8_toNat_recon, hkbrec]] at this
  have hx15_14 : σ14.regs.get? Register.x15 = some (0xfffffffffffe9904#64) := obs_alu_other hobs14 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_13
  have hx14_14 : σ14.regs.get? Register.x14 = some (0x80019f84#64) := obs_alu_other hobs14 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_13
  have hx17_14 : σ14.regs.get? Register.x17 = some Wr := obs_alu_other hobs14 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_13
  have hx10_14 : σ14.regs.get? Register.x10 = some (2#64) := obs_alu_other hobs14 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_13
  have hs1_14 : σ14.regs.get? Register.x9 = some sret := obs_alu_other hobs14 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_13
  have hsp_14 : σ14.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs14 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_13
  have hx19_14 : σ14.regs.get? Register.x19 = some Wl := obs_alu_other hobs14 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_13
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  have hout14 : σ14.sailOutput = out0 := by rw [hobs14.out, sailOutput_sigmaPost_alu]; exact hout13
  have hcode14 : Eval_exprLoaded σ14.mem := by rw [hmem14e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003554: add a5,a5,a4 → x15 := sext(slot) + 0x80019f84 = 0x80003888 (jr target)
  --------------------------------------------------------------------------------
  obtain ⟨σ15, i15, hs15', hi15, hG15, hmem15, hobs15⟩ :=
    site_80003554_ee σ14 i14 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003554#64) vmi14
      (0xfffffffffffe9904#64) (0x80019f84#64)
      hG14 hpc14 hmi14 hx15_14 hx14_14 hcode14 rfl hi14
  have hstep15 : Step ⟨σ14, i14, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ15, i15, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs15'
  have hmem15e : σ15.mem = c.σ.mem := by rw [hmem15]; exact hmem14e
  have hpc15 : σ15.regs.get? Register.PC = some (0x80003558#64) := by
    have := obs_alu_pc hobs15
    rwa [show BitVec.addInt (0x80003554#64) 4 = (0x80003558#64 : BitVec 64) from by decide] at this
  have hx15_15 : σ15.regs.get? Register.x15 = some (0x80003888#64) := by
    have := obs_alu_rd hobs15 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0xfffffffffffe9904#64 : BitVec 64) + (0x80019f84#64 : BitVec 64))
        = (0x80003888#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx17_15 : σ15.regs.get? Register.x17 = some Wr := obs_alu_other hobs15 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_14
  have hx10_15 : σ15.regs.get? Register.x10 = some (2#64) := obs_alu_other hobs15 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_14
  have hx16_15 : σ15.regs.get? Register.x16 = some (2#64) := obs_alu_other hobs15 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_14
  have hs1_15 : σ15.regs.get? Register.x9 = some sret := obs_alu_other hobs15 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_14
  have hsp_15 : σ15.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs15 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_14
  have hx19_15 : σ15.regs.get? Register.x19 = some Wl := obs_alu_other hobs15 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_14
  obtain ⟨vmi15, hmi15⟩ := obs_alu_minstret hobs15
  have hout15 : σ15.sailOutput = out0 := by rw [hobs15.out, sailOutput_sigmaPost_alu]; exact hout14
  have hcode15 : Eval_exprLoaded σ15.mem := by rw [hmem15e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003558: jr a5 → PC := 0x80003888 (ADD-int arm)
  --------------------------------------------------------------------------------
  obtain ⟨σ16, i16, hs16', hi16, hG16, hmem16, hobs16⟩ :=
    site_80003558_ee σ15 i15 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003558#64) vmi15 (0x80003888#64)
      hG15 hpc15 hmi15 hx15_15 hcode15 rfl (by decide) hi15
  have hstep16 : Step ⟨σ15, i15, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ16, i16, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs16'
  have hmem16e : σ16.mem = c.σ.mem := by rw [hmem16]; exact hmem15e
  have hpc16 : σ16.regs.get? Register.PC = some (0x80003888#64) := by
    have := obs_jr_pc hobs16
    rwa [show (BitVec.update ((0x80003888#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1) = (0x80003888#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx17_16 : σ16.regs.get? Register.x17 = some Wr := obs_jr_other hobs16 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_15
  have hx10_16 : σ16.regs.get? Register.x10 = some (2#64) := obs_jr_other hobs16 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_15
  have hx16_16 : σ16.regs.get? Register.x16 = some (2#64) := obs_jr_other hobs16 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_15
  have hs1_16 : σ16.regs.get? Register.x9 = some sret := obs_jr_other hobs16 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_15
  have hsp_16 : σ16.regs.get? Register.x2 = some (sp - 1088#64) := obs_jr_other hobs16 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_15
  have hx19_16 : σ16.regs.get? Register.x19 = some Wl := obs_jr_other hobs16 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_15
  obtain ⟨vmi16, hmi16⟩ := obs_jr_minstret hobs16
  have hout16 : σ16.sailOutput = out0 := by rw [hobs16.out, sailOutput_sigmaPost_jump_x0]; exact hout15
  have hcode16 : Eval_exprLoaded σ16.mem := by rw [hmem16e]; exact hcode
  --------------------------------------------------------------------------------
  -- ADD-int path from 0x80003888. Present bytes for the various error-staging
  -- `sd`s of the two payloads/kinds come from `hFullPop`; their concrete VALUES
  -- are irrelevant (runtime-error argument staging, never read on the int path).
  --------------------------------------------------------------------------------
  -- present dead bytes for the staging loads (ld a4,120(sp); ld a5,136(sp);
  -- ld a4,144(sp); ld a3,152(sp); ld a5,160(sp)).
  obtain ⟨d120_0, hd120_0⟩ := hFullPop (sp.toNat - 968)
  obtain ⟨d120_1, hd120_1⟩ := hFullPop (sp.toNat - 968 + 1)
  obtain ⟨d120_2, hd120_2⟩ := hFullPop (sp.toNat - 968 + 2)
  obtain ⟨d120_3, hd120_3⟩ := hFullPop (sp.toNat - 968 + 3)
  obtain ⟨d120_4, hd120_4⟩ := hFullPop (sp.toNat - 968 + 4)
  obtain ⟨d120_5, hd120_5⟩ := hFullPop (sp.toNat - 968 + 5)
  obtain ⟨d120_6, hd120_6⟩ := hFullPop (sp.toNat - 968 + 6)
  obtain ⟨d120_7, hd120_7⟩ := hFullPop (sp.toNat - 968 + 7)
  obtain ⟨d136_0, hd136_0⟩ := hFullPop (sp.toNat - 952)
  obtain ⟨d136_1, hd136_1⟩ := hFullPop (sp.toNat - 952 + 1)
  obtain ⟨d136_2, hd136_2⟩ := hFullPop (sp.toNat - 952 + 2)
  obtain ⟨d136_3, hd136_3⟩ := hFullPop (sp.toNat - 952 + 3)
  obtain ⟨d136_4, hd136_4⟩ := hFullPop (sp.toNat - 952 + 4)
  obtain ⟨d136_5, hd136_5⟩ := hFullPop (sp.toNat - 952 + 5)
  obtain ⟨d136_6, hd136_6⟩ := hFullPop (sp.toNat - 952 + 6)
  obtain ⟨d136_7, hd136_7⟩ := hFullPop (sp.toNat - 952 + 7)
  obtain ⟨d144_0, hd144_0⟩ := hFullPop (sp.toNat - 944)
  obtain ⟨d144_1, hd144_1⟩ := hFullPop (sp.toNat - 944 + 1)
  obtain ⟨d144_2, hd144_2⟩ := hFullPop (sp.toNat - 944 + 2)
  obtain ⟨d144_3, hd144_3⟩ := hFullPop (sp.toNat - 944 + 3)
  obtain ⟨d144_4, hd144_4⟩ := hFullPop (sp.toNat - 944 + 4)
  obtain ⟨d144_5, hd144_5⟩ := hFullPop (sp.toNat - 944 + 5)
  obtain ⟨d144_6, hd144_6⟩ := hFullPop (sp.toNat - 944 + 6)
  obtain ⟨d144_7, hd144_7⟩ := hFullPop (sp.toNat - 944 + 7)
  obtain ⟨d152_0, hd152_0⟩ := hFullPop (sp.toNat - 936)
  obtain ⟨d152_1, hd152_1⟩ := hFullPop (sp.toNat - 936 + 1)
  obtain ⟨d152_2, hd152_2⟩ := hFullPop (sp.toNat - 936 + 2)
  obtain ⟨d152_3, hd152_3⟩ := hFullPop (sp.toNat - 936 + 3)
  obtain ⟨d152_4, hd152_4⟩ := hFullPop (sp.toNat - 936 + 4)
  obtain ⟨d152_5, hd152_5⟩ := hFullPop (sp.toNat - 936 + 5)
  obtain ⟨d152_6, hd152_6⟩ := hFullPop (sp.toNat - 936 + 6)
  obtain ⟨d152_7, hd152_7⟩ := hFullPop (sp.toNat - 936 + 7)
  obtain ⟨d160_0, hd160_0⟩ := hFullPop (sp.toNat - 928)
  obtain ⟨d160_1, hd160_1⟩ := hFullPop (sp.toNat - 928 + 1)
  obtain ⟨d160_2, hd160_2⟩ := hFullPop (sp.toNat - 928 + 2)
  obtain ⟨d160_3, hd160_3⟩ := hFullPop (sp.toNat - 928 + 3)
  obtain ⟨d160_4, hd160_4⟩ := hFullPop (sp.toNat - 928 + 4)
  obtain ⟨d160_5, hd160_5⟩ := hFullPop (sp.toNat - 928 + 5)
  obtain ⟨d160_6, hd160_6⟩ := hFullPop (sp.toNat - 928 + 6)
  obtain ⟨d160_7, hd160_7⟩ := hFullPop (sp.toNat - 928 + 7)
  -- running step count at σ16 (16 steps consumed since `c`)
  let u16 : Nat := c.steps + 16
  have hu16eq : (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = u16 := by
    show _ = c.steps + 16; omega
  rw [hu16eq] at hstep16
  --------------------------------------------------------------------------------
  -- 0x80003888: addi a5,a0,-3 → x15 := 2 - 3 (dead; null-kind check)
  --------------------------------------------------------------------------------
  obtain ⟨τ1, j1, ht1', hj1, hGτ1, hmemτ1, hoτ1⟩ :=
    site_80003888_ee σ16 i16 u16 (0x80003888#64) vmi16 (2#64) hG16 hpc16 hmi16 hx10_16 hcode16 rfl hi16
  have hstepτ1 : Step ⟨σ16, i16, u16⟩ ⟨τ1, j1, u16 + 1⟩ := ht1'
  have hmemτ1e : τ1.mem = c.σ.mem := by rw [hmemτ1]; exact hmem16e
  have hpcτ1 : τ1.regs.get? Register.PC = some (0x8000388c#64) := by
    have := obs_alu_pc hoτ1
    rwa [show BitVec.addInt (0x80003888#64) 4 = (0x8000388c#64 : BitVec 64) from by decide] at this
  have hx15τ1 : τ1.regs.get? Register.x15 = some ((2#64) + sign_extend (m := 64) (0xffd#12)) :=
    obs_alu_rd hoτ1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx16τ1 : τ1.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ1 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_16
  have hx10τ1 : τ1.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_16
  have hx17τ1 : τ1.regs.get? Register.x17 = some Wr := obs_alu_other hoτ1 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17_16
  have hs1τ1 : τ1.regs.get? Register.x9 = some sret := obs_alu_other hoτ1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_16
  have hspτ1 : τ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_16
  have hx19τ1 : τ1.regs.get? Register.x19 = some Wl := obs_alu_other hoτ1 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19_16
  obtain ⟨vmiτ1, hmiτ1⟩ := obs_alu_minstret hoτ1
  have houtτ1 : τ1.sailOutput = out0 := by rw [hoτ1.out, sailOutput_sigmaPost_alu]; exact hout16
  have hcodeτ1 : Eval_exprLoaded τ1.mem := by rw [hmemτ1e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x8000388c: beqz a5 (NOT taken; 2-3 ≠ 0)
  --------------------------------------------------------------------------------
  obtain ⟨τ2, j2, ht2', hj2, hGτ2, hmemτ2, hoτ2⟩ :=
    site_8000388c_nottaken_ee τ1 j1 (u16 + 1) (0x8000388c#64) vmiτ1 ((2#64) + sign_extend (m := 64) (0xffd#12))
      hGτ1 hpcτ1 hmiτ1 hx15τ1 hcodeτ1 rfl (by decide) hj1
  have hstepτ2 : Step ⟨τ1, j1, u16 + 1⟩ ⟨τ2, j2, u16 + 1 + 1⟩ := ht2'
  have hmemτ2e : τ2.mem = c.σ.mem := by rw [hmemτ2]; exact hmemτ1e
  have hpcτ2 : τ2.regs.get? Register.PC = some (0x80003890#64) := by
    have := obs_branch_nottaken_pc hoτ2
    rwa [show BitVec.addInt (0x8000388c#64) 4 = (0x80003890#64 : BitVec 64) from by decide] at this
  have hx16τ2 : τ2.regs.get? Register.x16 = some (2#64) := obs_branch_nottaken_other hoτ2 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ1
  have hx10τ2 : τ2.regs.get? Register.x10 = some (2#64) := obs_branch_nottaken_other hoτ2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ1
  have hx17τ2 : τ2.regs.get? Register.x17 = some Wr := obs_branch_nottaken_other hoτ2 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ1
  have hs1τ2 : τ2.regs.get? Register.x9 = some sret := obs_branch_nottaken_other hoτ2 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ1
  have hspτ2 : τ2.regs.get? Register.x2 = some (sp - 1088#64) := obs_branch_nottaken_other hoτ2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ1
  have hx19τ2 : τ2.regs.get? Register.x19 = some Wl := obs_branch_nottaken_other hoτ2 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ1
  obtain ⟨vmiτ2, hmiτ2⟩ := obs_branch_nottaken_minstret hoτ2
  have houtτ2 : τ2.sailOutput = out0 := by rw [hoτ2.out, sailOutput_sigmaPost_branch_nottaken]; exact houtτ1
  have hcodeτ2 : Eval_exprLoaded τ2.mem := by rw [hmemτ2e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003890: addi a5,a6,-3 → x15 := 2 - 3 (dead); 0x80003894: beqz (NOT taken)
  --------------------------------------------------------------------------------
  obtain ⟨τ3, j3, ht3', hj3, hGτ3, hmemτ3, hoτ3⟩ :=
    site_80003890_ee τ2 j2 (u16 + 1 + 1) (0x80003890#64) vmiτ2 (2#64) hGτ2 hpcτ2 hmiτ2 hx16τ2 hcodeτ2 rfl hj2
  have hstepτ3 : Step ⟨τ2, j2, u16 + 1 + 1⟩ ⟨τ3, j3, u16 + 1 + 1 + 1⟩ := ht3'
  have hmemτ3e : τ3.mem = c.σ.mem := by rw [hmemτ3]; exact hmemτ2e
  have hpcτ3 : τ3.regs.get? Register.PC = some (0x80003894#64) := by
    have := obs_alu_pc hoτ3
    rwa [show BitVec.addInt (0x80003890#64) 4 = (0x80003894#64 : BitVec 64) from by decide] at this
  have hx15τ3 : τ3.regs.get? Register.x15 = some ((2#64) + sign_extend (m := 64) (0xffd#12)) :=
    obs_alu_rd hoτ3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx16τ3 : τ3.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ3 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ2
  have hx10τ3 : τ3.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ2
  have hx17τ3 : τ3.regs.get? Register.x17 = some Wr := obs_alu_other hoτ3 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ2
  have hs1τ3 : τ3.regs.get? Register.x9 = some sret := obs_alu_other hoτ3 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ2
  have hspτ3 : τ3.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ2
  have hx19τ3 : τ3.regs.get? Register.x19 = some Wl := obs_alu_other hoτ3 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ2
  obtain ⟨vmiτ3, hmiτ3⟩ := obs_alu_minstret hoτ3
  have houtτ3 : τ3.sailOutput = out0 := by rw [hoτ3.out, sailOutput_sigmaPost_alu]; exact houtτ2
  have hcodeτ3 : Eval_exprLoaded τ3.mem := by rw [hmemτ3e]; exact hcode
  obtain ⟨τ4, j4, ht4', hj4, hGτ4, hmemτ4, hoτ4⟩ :=
    site_80003894_nottaken_ee τ3 j3 (u16 + 1 + 1 + 1) (0x80003894#64) vmiτ3 ((2#64) + sign_extend (m := 64) (0xffd#12))
      hGτ3 hpcτ3 hmiτ3 hx15τ3 hcodeτ3 rfl (by decide) hj3
  have hstepτ4 : Step ⟨τ3, j3, u16 + 1 + 1 + 1⟩ ⟨τ4, j4, u16 + 1 + 1 + 1 + 1⟩ := ht4'
  have hmemτ4e : τ4.mem = c.σ.mem := by rw [hmemτ4]; exact hmemτ3e
  have hpcτ4 : τ4.regs.get? Register.PC = some (0x80003898#64) := by
    have := obs_branch_nottaken_pc hoτ4
    rwa [show BitVec.addInt (0x80003894#64) 4 = (0x80003898#64 : BitVec 64) from by decide] at this
  have hx16τ4 : τ4.regs.get? Register.x16 = some (2#64) := obs_branch_nottaken_other hoτ4 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ3
  have hx10τ4 : τ4.regs.get? Register.x10 = some (2#64) := obs_branch_nottaken_other hoτ4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ3
  have hx17τ4 : τ4.regs.get? Register.x17 = some Wr := obs_branch_nottaken_other hoτ4 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ3
  have hs1τ4 : τ4.regs.get? Register.x9 = some sret := obs_branch_nottaken_other hoτ4 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ3
  have hspτ4 : τ4.regs.get? Register.x2 = some (sp - 1088#64) := obs_branch_nottaken_other hoτ4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ3
  have hx19τ4 : τ4.regs.get? Register.x19 = some Wl := obs_branch_nottaken_other hoτ4 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ3
  obtain ⟨vmiτ4, hmiτ4⟩ := obs_branch_nottaken_minstret hoτ4
  have houtτ4 : τ4.sailOutput = out0 := by rw [hoτ4.out, sailOutput_sigmaPost_branch_nottaken]; exact houtτ3
  have hcodeτ4 : Eval_exprLoaded τ4.mem := by rw [hmemτ4e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x80003898: ld a4,120(sp) (dead); 0x8000389c: ld a5,136(sp) (dead)
  --------------------------------------------------------------------------------
  obtain ⟨τ5, j5, ht5', hj5, hGτ5, hmemτ5, hoτ5⟩ :=
    site_80003898_ee τ4 j4 (u16 + 1 + 1 + 1 + 1) (0x80003898#64) vmiτ4 (sp - 1088#64)
      d120_0 d120_1 d120_2 d120_3 d120_4 d120_5 d120_6 d120_7 hGτ4 hpcτ4 hmiτ4 hspτ4 hcodeτ4 rfl
      (by rw [haddr120]; omega) (by rw [haddr120]; omega)
      (by rw [haddr120, htoh]; right; omega) (by rw [haddr120]; omega)
      (by rw [haddr120, hmemτ4e]; exact hd120_0) (by rw [haddr120, hmemτ4e]; exact hd120_1)
      (by rw [haddr120, hmemτ4e]; exact hd120_2) (by rw [haddr120, hmemτ4e]; exact hd120_3)
      (by rw [haddr120, hmemτ4e]; exact hd120_4) (by rw [haddr120, hmemτ4e]; exact hd120_5)
      (by rw [haddr120, hmemτ4e]; exact hd120_6) (by rw [haddr120, hmemτ4e]; exact hd120_7) hj4
  have hstepτ5 : Step ⟨τ4, j4, u16 + 1 + 1 + 1 + 1⟩ ⟨τ5, j5, u16 + 1 + 1 + 1 + 1 + 1⟩ := ht5'
  have hmemτ5e : τ5.mem = c.σ.mem := by rw [hmemτ5]; exact hmemτ4e
  have hpcτ5 : τ5.regs.get? Register.PC = some (0x8000389c#64) := by
    have := obs_alu_pc hoτ5
    rwa [show BitVec.addInt (0x80003898#64) 4 = (0x8000389c#64 : BitVec 64) from by decide] at this
  have hx10τ5 : τ5.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ4
  have hx16τ5 : τ5.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ5 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ4
  have hx17τ5 : τ5.regs.get? Register.x17 = some Wr := obs_alu_other hoτ5 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ4
  have hs1τ5 : τ5.regs.get? Register.x9 = some sret := obs_alu_other hoτ5 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ4
  have hspτ5 : τ5.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ4
  have hx19τ5 : τ5.regs.get? Register.x19 = some Wl := obs_alu_other hoτ5 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ4
  obtain ⟨vmiτ5, hmiτ5⟩ := obs_alu_minstret hoτ5
  have houtτ5 : τ5.sailOutput = out0 := by rw [hoτ5.out, sailOutput_sigmaPost_alu]; exact houtτ4
  have hcodeτ5 : Eval_exprLoaded τ5.mem := by rw [hmemτ5e]; exact hcode
  obtain ⟨τ6, j6, ht6', hj6, hGτ6, hmemτ6, hoτ6⟩ :=
    site_8000389c_ee τ5 j5 (u16 + 1 + 1 + 1 + 1 + 1) (0x8000389c#64) vmiτ5 (sp - 1088#64)
      d136_0 d136_1 d136_2 d136_3 d136_4 d136_5 d136_6 d136_7 hGτ5 hpcτ5 hmiτ5 hspτ5 hcodeτ5 rfl
      (by rw [haddr136]; omega) (by rw [haddr136]; omega)
      (by rw [haddr136, htoh]; right; omega) (by rw [haddr136]; omega)
      (by rw [haddr136, hmemτ5e]; exact hd136_0) (by rw [haddr136, hmemτ5e]; exact hd136_1)
      (by rw [haddr136, hmemτ5e]; exact hd136_2) (by rw [haddr136, hmemτ5e]; exact hd136_3)
      (by rw [haddr136, hmemτ5e]; exact hd136_4) (by rw [haddr136, hmemτ5e]; exact hd136_5)
      (by rw [haddr136, hmemτ5e]; exact hd136_6) (by rw [haddr136, hmemτ5e]; exact hd136_7) hj5
  have hstepτ6 : Step ⟨τ5, j5, u16 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ6, j6, u16 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht6'
  have hmemτ6e : τ6.mem = c.σ.mem := by rw [hmemτ6]; exact hmemτ5e
  have hpcτ6 : τ6.regs.get? Register.PC = some (0x800038a0#64) := by
    have := obs_alu_pc hoτ6
    rwa [show BitVec.addInt (0x8000389c#64) 4 = (0x800038a0#64 : BitVec 64) from by decide] at this
  have hx10τ6 : τ6.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ5
  have hx16τ6 : τ6.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ6 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ5
  have hx17τ6 : τ6.regs.get? Register.x17 = some Wr := obs_alu_other hoτ6 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ5
  have hs1τ6 : τ6.regs.get? Register.x9 = some sret := obs_alu_other hoτ6 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ5
  have hspτ6 : τ6.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ6 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ5
  have hx19τ6 : τ6.regs.get? Register.x19 = some Wl := obs_alu_other hoτ6 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ5
  obtain ⟨vmiτ6, hmiτ6⟩ := obs_alu_minstret hoτ6
  have houtτ6 : τ6.sailOutput = out0 := by rw [hoτ6.out, sailOutput_sigmaPost_alu]; exact houtτ5
  have hcodeτ6 : Eval_exprLoaded τ6.mem := by rw [hmemτ6e]; exact hcode
  --------------------------------------------------------------------------------
  -- 0x800038a0: li a3,2 → x13 := 2
  --------------------------------------------------------------------------------
  obtain ⟨τ7, j7, ht7', hj7, hGτ7, hmemτ7, hoτ7⟩ :=
    site_800038a0_ee τ6 j6 (u16 + 1 + 1 + 1 + 1 + 1 + 1) (0x800038a0#64) vmiτ6 hGτ6 hpcτ6 hmiτ6 hcodeτ6 rfl hj6
  have hstepτ7 : Step ⟨τ6, j6, u16 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ7, j7, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht7'
  have hmemτ7e : τ7.mem = c.σ.mem := by rw [hmemτ7]; exact hmemτ6e
  have hpcτ7 : τ7.regs.get? Register.PC = some (0x800038a4#64) := by
    have := obs_alu_pc hoτ7
    rwa [show BitVec.addInt (0x800038a0#64) 4 = (0x800038a4#64 : BitVec 64) from by decide] at this
  have hx13τ7 : τ7.regs.get? Register.x13 = some (2#64) := by
    have := obs_alu_rd hoτ7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64 : BitVec 64) + sign_extend (m := 64) (0x002#12)) = (2#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx10τ7 : τ7.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ7 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ6
  have hx16τ7 : τ7.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ7 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ6
  have hx17τ7 : τ7.regs.get? Register.x17 = some Wr := obs_alu_other hoτ7 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ6
  have hs1τ7 : τ7.regs.get? Register.x9 = some sret := obs_alu_other hoτ7 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ6
  have hspτ7 : τ7.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ6
  have hx19τ7 : τ7.regs.get? Register.x19 = some Wl := obs_alu_other hoτ7 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ6
  obtain ⟨vmiτ7, hmiτ7⟩ := obs_alu_minstret hoτ7
  have houtτ7 : τ7.sailOutput = out0 := by rw [hoτ7.out, sailOutput_sigmaPost_alu]; exact houtτ6
  have hcodeτ7 : Eval_exprLoaded τ7.mem := by rw [hmemτ7e]; exact hcode
  -- the a4/a5 loaded (dead) values for the two staging stores
  let V120 : BitVec 64 := sign_extend (m := 64)
    ((((((((d120_7.append d120_6).append d120_5).append d120_4).append d120_3).append d120_2).append d120_1).append d120_0) : BitVec (8*8))
  let V136 : BitVec 64 := sign_extend (m := 64)
    ((((((((d136_7.append d136_6).append d136_5).append d136_4).append d136_3).append d136_2).append d136_1).append d136_0) : BitVec (8*8))
  have hx14τ7 : τ7.regs.get? Register.x14 = some V120 := by
    -- a4 = V120 from ld a4,120(sp) @τ5, unchanged through τ6/τ7 (li/ld don't touch a4)
    have e5 : τ5.regs.get? Register.x14 = some V120 :=
      obs_alu_rd hoτ5 (by decide) (by decide) (by decide) (by decide) (by decide)
    have e6 : τ6.regs.get? Register.x14 = some V120 := obs_alu_other hoτ6 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e5
    exact obs_alu_other hoτ7 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e6
  have hx15τ7 : τ7.regs.get? Register.x15 = some V136 := by
    have e6 : τ6.regs.get? Register.x15 = some V136 :=
      obs_alu_rd hoτ6 (by decide) (by decide) (by decide) (by decide) (by decide)
    exact obs_alu_other hoτ7 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e6
  --------------------------------------------------------------------------------
  -- 0x800038a4: sd a4,240(sp) → m1 @sp-848; 0x800038a8: sd a5,256(sp) → m2 @sp-832
  --------------------------------------------------------------------------------
  let m1 : Mem := writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val V120)
  let m2 : Mem := writeMap8 m1 (sp.toNat - 832) (sdData_val V136)
  obtain ⟨τ8, j8, ht8', hj8, hGτ8, hmemτ8, hoτ8⟩ :=
    site_800038a4_ee τ7 j7 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800038a4#64) vmiτ7 (sp - 1088#64) V120
      hGτ7 hpcτ7 hmiτ7 hspτ7 hx14τ7 hcodeτ7 rfl
      (by rw [haddr240]; omega) (by rw [haddr240]; omega)
      (by rw [haddr240, htoh]; omega) (by rw [haddr240]; omega) hj7
  have hstepτ8 : Step ⟨τ7, j7, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ8, j8, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht8'
  have hmemτ8e : τ8.mem = m1 := by rw [hmemτ8, mem_afterNextPC, haddr240]; rw [hmemτ7e]
  have hpcτ8 : τ8.regs.get? Register.PC = some (0x800038a8#64) := by
    have := obs_store_pc_val hoτ8
    rwa [show BitVec.addInt (0x800038a4#64) 4 = (0x800038a8#64 : BitVec 64) from by decide] at this
  have hx15τ8 := obs_store_other_val hoτ8 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15τ7
  have hx10τ8 := obs_store_other_val hoτ8 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ7
  have hx16τ8 := obs_store_other_val hoτ8 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ7
  have hx13τ8 := obs_store_other_val hoτ8 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13τ7
  have hx17τ8 := obs_store_other_val hoτ8 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ7
  have hs1τ8 := obs_store_other_val hoτ8 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ7
  have hspτ8 := obs_store_other_val hoτ8 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ7
  have hx19τ8 := obs_store_other_val hoτ8 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ7
  obtain ⟨vmiτ8, hmiτ8⟩ := obs_store_minstret_val hoτ8
  have houtτ8 : τ8.sailOutput = out0 := by rw [hoτ8.out, sailOutput_sigmaPost_store]; exact houtτ7
  have hcodeτ8 : Eval_exprLoaded τ8.mem := by
    rw [hmemτ8e]
    exact loaded_eval_expr_agreeP c.σ.mem m1
      (fun k hk => (getElem_writeMap8_disjoint c.σ.mem (sp.toNat-848) k (sdData_val V120)
        (by rcases hcodeStk with h | h <;> omega)).symm) hcode
  obtain ⟨τ9, j9, ht9', hj9, hGτ9, hmemτ9, hoτ9⟩ :=
    site_800038a8_ee τ8 j8 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800038a8#64) vmiτ8 (sp - 1088#64) V136
      hGτ8 hpcτ8 hmiτ8 hspτ8 hx15τ8 hcodeτ8 rfl
      (by rw [haddr256]; omega) (by rw [haddr256]; omega)
      (by rw [haddr256, htoh]; omega) (by rw [haddr256]; omega) hj8
  have hstepτ9 : Step ⟨τ8, j8, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ9, j9, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht9'
  have hmemτ9e : τ9.mem = m2 := by rw [hmemτ9, mem_afterNextPC, haddr256]; rw [hmemτ8e]
  have hpcτ9 : τ9.regs.get? Register.PC = some (0x800038ac#64) := by
    have := obs_store_pc_val hoτ9
    rwa [show BitVec.addInt (0x800038a8#64) 4 = (0x800038ac#64 : BitVec 64) from by decide] at this
  have hx10τ9 := obs_store_other_val hoτ9 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ8
  have hx16τ9 := obs_store_other_val hoτ9 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ8
  have hx13τ9 := obs_store_other_val hoτ9 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13τ8
  have hx17τ9 := obs_store_other_val hoτ9 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ8
  have hs1τ9 := obs_store_other_val hoτ9 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ8
  have hspτ9 := obs_store_other_val hoτ9 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ8
  have hx19τ9 := obs_store_other_val hoτ9 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ8
  obtain ⟨vmiτ9, hmiτ9⟩ := obs_store_minstret_val hoτ9
  have houtτ9 : τ9.sailOutput = out0 := by rw [hoτ9.out, sailOutput_sigmaPost_store]; exact houtτ8
  have hcodem1 : Eval_exprLoaded m1 := by rw [← hmemτ8e]; exact hcodeτ8
  have hcodeτ9 : Eval_exprLoaded τ9.mem := by
    rw [hmemτ9e]
    exact loaded_eval_expr_agreeP m1 m2
      (fun k hk => (getElem_writeMap8_disjoint m1 (sp.toNat-832) k (sdData_val V136)
        (by rcases hcodeStk with h | h <;> omega)).symm) hcodem1
  -- `m2` agrees with `c.σ.mem` outside the two store windows [sp-848,+8), [sp-832,+8)
  have hcodem2 : Eval_exprLoaded m2 := by rw [← hmemτ9e]; exact hcodeτ9
  have hAgM2 : ∀ k : Nat, k + 8 ≤ sp.toNat - 848 → c.σ.mem[k]? = m2[k]? := by
    intro k hk
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat - 832) (sdData_val V136))[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat - 832) k (sdData_val V136) (by omega)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val V120))[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) k (sdData_val V120) (by omega)]
  --------------------------------------------------------------------------------
  -- 0x800038ac: bne a6,a3 (NOT taken; a6=2, a3=2)
  --------------------------------------------------------------------------------
  obtain ⟨τ10, j10, ht10', hj10, hGτ10, hmemτ10, hoτ10⟩ :=
    site_800038ac_nottaken_ee τ9 j9 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800038ac#64) vmiτ9 (2#64) (2#64)
      hGτ9 hpcτ9 hmiτ9 hx16τ9 hx13τ9 hcodeτ9 rfl (by decide) hj9
  have hstepτ10 : Step ⟨τ9, j9, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ10, j10, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht10'
  have hmemτ10e : τ10.mem = m2 := by rw [hmemτ10]; exact hmemτ9e
  have hpcτ10 : τ10.regs.get? Register.PC = some (0x800038b0#64) := by
    have := obs_branch_nottaken_pc hoτ10
    rwa [show BitVec.addInt (0x800038ac#64) 4 = (0x800038b0#64 : BitVec 64) from by decide] at this
  have hx10τ10 : τ10.regs.get? Register.x10 = some (2#64) := obs_branch_nottaken_other hoτ10 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ9
  have hx16τ10 : τ10.regs.get? Register.x16 = some (2#64) := obs_branch_nottaken_other hoτ10 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ9
  have hx17τ10 : τ10.regs.get? Register.x17 = some Wr := obs_branch_nottaken_other hoτ10 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ9
  have hs1τ10 : τ10.regs.get? Register.x9 = some sret := obs_branch_nottaken_other hoτ10 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ9
  have hspτ10 : τ10.regs.get? Register.x2 = some (sp - 1088#64) := obs_branch_nottaken_other hoτ10 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ9
  have hx19τ10 : τ10.regs.get? Register.x19 = some Wl := obs_branch_nottaken_other hoτ10 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ9
  obtain ⟨vmiτ10, hmiτ10⟩ := obs_branch_nottaken_minstret hoτ10
  have houtτ10 : τ10.sailOutput = out0 := by rw [hoτ10.out, sailOutput_sigmaPost_branch_nottaken]; exact houtτ9
  have hcodeτ10 : Eval_exprLoaded τ10.mem := by rw [hmemτ10e]; exact hcodem2
  --------------------------------------------------------------------------------
  -- 0x800038b0: ld a4,144(sp) (dead); 0x800038b4: ld a3,152(sp)=Wr (dead here);
  -- 0x800038b8: ld a5,160(sp) (dead). All read from m2 = c.σ.mem on disjoint addrs.
  --------------------------------------------------------------------------------
  obtain ⟨τ11, j11, ht11', hj11, hGτ11, hmemτ11, hoτ11⟩ :=
    site_800038b0_ee τ10 j10 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800038b0#64) vmiτ10 (sp - 1088#64)
      d144_0 d144_1 d144_2 d144_3 d144_4 d144_5 d144_6 d144_7 hGτ10 hpcτ10 hmiτ10 hspτ10 hcodeτ10 rfl
      (by rw [haddr144]; omega) (by rw [haddr144]; omega)
      (by rw [haddr144, htoh]; right; omega) (by rw [haddr144]; omega)
      (by rw [haddr144, hmemτ10e]; rw [← hAgM2 (sp.toNat - 944) (by omega)]; exact hd144_0)
      (by rw [haddr144, hmemτ10e]; rw [← hAgM2 (sp.toNat - 944 + 1) (by omega)]; exact hd144_1)
      (by rw [haddr144, hmemτ10e]; rw [← hAgM2 (sp.toNat - 944 + 2) (by omega)]; exact hd144_2)
      (by rw [haddr144, hmemτ10e]; rw [← hAgM2 (sp.toNat - 944 + 3) (by omega)]; exact hd144_3)
      (by rw [haddr144, hmemτ10e]; rw [← hAgM2 (sp.toNat - 944 + 4) (by omega)]; exact hd144_4)
      (by rw [haddr144, hmemτ10e]; rw [← hAgM2 (sp.toNat - 944 + 5) (by omega)]; exact hd144_5)
      (by rw [haddr144, hmemτ10e]; rw [← hAgM2 (sp.toNat - 944 + 6) (by omega)]; exact hd144_6)
      (by rw [haddr144, hmemτ10e]; rw [← hAgM2 (sp.toNat - 944 + 7) (by omega)]; exact hd144_7) hj10
  have hstepτ11 : Step ⟨τ10, j10, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ11, j11, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht11'
  have hmemτ11e : τ11.mem = m2 := by rw [hmemτ11]; exact hmemτ10e
  have hpcτ11 : τ11.regs.get? Register.PC = some (0x800038b4#64) := by
    have := obs_alu_pc hoτ11
    rwa [show BitVec.addInt (0x800038b0#64) 4 = (0x800038b4#64 : BitVec 64) from by decide] at this
  have hx10τ11 : τ11.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ11 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ10
  have hx16τ11 : τ11.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ11 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ10
  have hx17τ11 : τ11.regs.get? Register.x17 = some Wr := obs_alu_other hoτ11 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ10
  have hs1τ11 : τ11.regs.get? Register.x9 = some sret := obs_alu_other hoτ11 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ10
  have hspτ11 : τ11.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ11 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ10
  have hx19τ11 : τ11.regs.get? Register.x19 = some Wl := obs_alu_other hoτ11 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ10
  obtain ⟨vmiτ11, hmiτ11⟩ := obs_alu_minstret hoτ11
  have houtτ11 : τ11.sailOutput = out0 := by rw [hoτ11.out, sailOutput_sigmaPost_alu]; exact houtτ10
  have hcodeτ11 : Eval_exprLoaded τ11.mem := by rw [hmemτ11e]; exact hcodem2
  obtain ⟨τ12, j12, ht12', hj12, hGτ12, hmemτ12, hoτ12⟩ :=
    site_800038b4_ee τ11 j11 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800038b4#64) vmiτ11 (sp - 1088#64)
      rpb0 rpb1 rpb2 rpb3 rpb4 rpb5 rpb6 rpb7 hGτ11 hpcτ11 hmiτ11 hspτ11 hcodeτ11 rfl
      (by rw [haddr152]; omega) (by rw [haddr152]; omega)
      (by rw [haddr152, htoh]; right; omega) (by rw [haddr152]; omega)
      (by rw [haddr152, hmemτ11e]; rw [← hAgM2 (sp.toNat - 936) (by omega)]
          rw [show sp.toNat - 936 = sp.toNat - 944 + 8 from by omega]; exact hrpb0)
      (by rw [haddr152, hmemτ11e]; rw [← hAgM2 (sp.toNat - 936 + 1) (by omega)]
          rw [show sp.toNat - 936 + 1 = sp.toNat - 944 + 8 + 1 from by omega]; exact hrpb1)
      (by rw [haddr152, hmemτ11e]; rw [← hAgM2 (sp.toNat - 936 + 2) (by omega)]
          rw [show sp.toNat - 936 + 2 = sp.toNat - 944 + 8 + 2 from by omega]; exact hrpb2)
      (by rw [haddr152, hmemτ11e]; rw [← hAgM2 (sp.toNat - 936 + 3) (by omega)]
          rw [show sp.toNat - 936 + 3 = sp.toNat - 944 + 8 + 3 from by omega]; exact hrpb3)
      (by rw [haddr152, hmemτ11e]; rw [← hAgM2 (sp.toNat - 936 + 4) (by omega)]
          rw [show sp.toNat - 936 + 4 = sp.toNat - 944 + 8 + 4 from by omega]; exact hrpb4)
      (by rw [haddr152, hmemτ11e]; rw [← hAgM2 (sp.toNat - 936 + 5) (by omega)]
          rw [show sp.toNat - 936 + 5 = sp.toNat - 944 + 8 + 5 from by omega]; exact hrpb5)
      (by rw [haddr152, hmemτ11e]; rw [← hAgM2 (sp.toNat - 936 + 6) (by omega)]
          rw [show sp.toNat - 936 + 6 = sp.toNat - 944 + 8 + 6 from by omega]; exact hrpb6)
      (by rw [haddr152, hmemτ11e]; rw [← hAgM2 (sp.toNat - 936 + 7) (by omega)]
          rw [show sp.toNat - 936 + 7 = sp.toNat - 944 + 8 + 7 from by omega]; exact hrpb7) hj11
  have hstepτ12 : Step ⟨τ11, j11, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ12, j12, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht12'
  have hmemτ12e : τ12.mem = m2 := by rw [hmemτ12]; exact hmemτ11e
  have hpcτ12 : τ12.regs.get? Register.PC = some (0x800038b8#64) := by
    have := obs_alu_pc hoτ12
    rwa [show BitVec.addInt (0x800038b4#64) 4 = (0x800038b8#64 : BitVec 64) from by decide] at this
  have hx13τ12 : τ12.regs.get? Register.x13 = some Wr :=
    obs_alu_rd hoτ12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx10τ12 : τ12.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ12 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ11
  have hx16τ12 : τ12.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ12 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ11
  have hx17τ12 : τ12.regs.get? Register.x17 = some Wr := obs_alu_other hoτ12 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ11
  have hs1τ12 : τ12.regs.get? Register.x9 = some sret := obs_alu_other hoτ12 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ11
  have hspτ12 : τ12.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ12 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ11
  have hx19τ12 : τ12.regs.get? Register.x19 = some Wl := obs_alu_other hoτ12 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ11
  obtain ⟨vmiτ12, hmiτ12⟩ := obs_alu_minstret hoτ12
  have houtτ12 : τ12.sailOutput = out0 := by rw [hoτ12.out, sailOutput_sigmaPost_alu]; exact houtτ11
  have hcodeτ12 : Eval_exprLoaded τ12.mem := by rw [hmemτ12e]; exact hcodem2
  obtain ⟨τ13, j13, ht13', hj13, hGτ13, hmemτ13, hoτ13⟩ :=
    site_800038b8_ee τ12 j12 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800038b8#64) vmiτ12 (sp - 1088#64)
      d160_0 d160_1 d160_2 d160_3 d160_4 d160_5 d160_6 d160_7 hGτ12 hpcτ12 hmiτ12 hspτ12 hcodeτ12 rfl
      (by rw [haddr160]; omega) (by rw [haddr160]; omega)
      (by rw [haddr160, htoh]; right; omega) (by rw [haddr160]; omega)
      (by rw [haddr160, hmemτ12e]; rw [← hAgM2 (sp.toNat - 928) (by omega)]; exact hd160_0)
      (by rw [haddr160, hmemτ12e]; rw [← hAgM2 (sp.toNat - 928 + 1) (by omega)]; exact hd160_1)
      (by rw [haddr160, hmemτ12e]; rw [← hAgM2 (sp.toNat - 928 + 2) (by omega)]; exact hd160_2)
      (by rw [haddr160, hmemτ12e]; rw [← hAgM2 (sp.toNat - 928 + 3) (by omega)]; exact hd160_3)
      (by rw [haddr160, hmemτ12e]; rw [← hAgM2 (sp.toNat - 928 + 4) (by omega)]; exact hd160_4)
      (by rw [haddr160, hmemτ12e]; rw [← hAgM2 (sp.toNat - 928 + 5) (by omega)]; exact hd160_5)
      (by rw [haddr160, hmemτ12e]; rw [← hAgM2 (sp.toNat - 928 + 6) (by omega)]; exact hd160_6)
      (by rw [haddr160, hmemτ12e]; rw [← hAgM2 (sp.toNat - 928 + 7) (by omega)]; exact hd160_7) hj12
  have hstepτ13 : Step ⟨τ12, j12, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ13, j13, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht13'
  have hmemτ13e : τ13.mem = m2 := by rw [hmemτ13]; exact hmemτ12e
  have hpcτ13 : τ13.regs.get? Register.PC = some (0x800038bc#64) := by
    have := obs_alu_pc hoτ13
    rwa [show BitVec.addInt (0x800038b8#64) 4 = (0x800038bc#64 : BitVec 64) from by decide] at this
  have hx14τ13 : τ13.regs.get? Register.x14 = some (sign_extend (m := 64)
      ((((((((d144_7.append d144_6).append d144_5).append d144_4).append d144_3).append d144_2).append d144_1).append d144_0) : BitVec (8*8))) := by
    have e11 : τ11.regs.get? Register.x14 = some (sign_extend (m := 64)
        ((((((((d144_7.append d144_6).append d144_5).append d144_4).append d144_3).append d144_2).append d144_1).append d144_0) : BitVec (8*8))) :=
      obs_alu_rd hoτ11 (by decide) (by decide) (by decide) (by decide) (by decide)
    have e12 := obs_alu_other hoτ12 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e11
    exact obs_alu_other hoτ13 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) e12
  have hx15τ13 : τ13.regs.get? Register.x15 = some (sign_extend (m := 64)
      ((((((((d160_7.append d160_6).append d160_5).append d160_4).append d160_3).append d160_2).append d160_1).append d160_0) : BitVec (8*8))) :=
    obs_alu_rd hoτ13 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx13τ13 : τ13.regs.get? Register.x13 = some Wr := obs_alu_other hoτ13 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13τ12
  have hx10τ13 : τ13.regs.get? Register.x10 = some (2#64) := obs_alu_other hoτ13 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ12
  have hx16τ13 : τ13.regs.get? Register.x16 = some (2#64) := obs_alu_other hoτ13 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ12
  have hx17τ13 : τ13.regs.get? Register.x17 = some Wr := obs_alu_other hoτ13 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ12
  have hs1τ13 : τ13.regs.get? Register.x9 = some sret := obs_alu_other hoτ13 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ12
  have hspτ13 : τ13.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ13 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ12
  have hx19τ13 : τ13.regs.get? Register.x19 = some Wl := obs_alu_other hoτ13 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ12
  obtain ⟨vmiτ13, hmiτ13⟩ := obs_alu_minstret hoτ13
  have houtτ13 : τ13.sailOutput = out0 := by rw [hoτ13.out, sailOutput_sigmaPost_alu]; exact houtτ12
  have hcodeτ13 : Eval_exprLoaded τ13.mem := by rw [hmemτ13e]; exact hcodem2
  --------------------------------------------------------------------------------
  -- 0x800038bc: sd a4,240(sp) → m3 @sp-848; 0x800038c0: sd a3,248(sp) → m4 @sp-840;
  -- 0x800038c4: sd a5,256(sp) → m5 @sp-832
  --------------------------------------------------------------------------------
  let V144 : BitVec 64 := sign_extend (m := 64)
    ((((((((d144_7.append d144_6).append d144_5).append d144_4).append d144_3).append d144_2).append d144_1).append d144_0) : BitVec (8*8))
  let V160 : BitVec 64 := sign_extend (m := 64)
    ((((((((d160_7.append d160_6).append d160_5).append d160_4).append d160_3).append d160_2).append d160_1).append d160_0) : BitVec (8*8))
  let m3 : Mem := writeMap8 m2 (sp.toNat - 848) (sdData_val V144)
  let m4 : Mem := writeMap8 m3 (sp.toNat - 840) (sdData_val Wr)
  let m5 : Mem := writeMap8 m4 (sp.toNat - 832) (sdData_val V160)
  obtain ⟨τ14, j14, ht14', hj14, hGτ14, hmemτ14, hoτ14⟩ :=
    site_800038bc_ee τ13 j13 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800038bc#64) vmiτ13 (sp - 1088#64) V144
      hGτ13 hpcτ13 hmiτ13 hspτ13 hx14τ13 hcodeτ13 rfl
      (by rw [haddr240]; omega) (by rw [haddr240]; omega)
      (by rw [haddr240, htoh]; omega) (by rw [haddr240]; omega) hj13
  have hstepτ14 : Step ⟨τ13, j13, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ14, j14, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht14'
  have hmemτ14e : τ14.mem = m3 := by rw [hmemτ14, mem_afterNextPC, haddr240]; rw [hmemτ13e]
  have hpcτ14 : τ14.regs.get? Register.PC = some (0x800038c0#64) := by
    have := obs_store_pc_val hoτ14
    rwa [show BitVec.addInt (0x800038bc#64) 4 = (0x800038c0#64 : BitVec 64) from by decide] at this
  have hx13τ14 := obs_store_other_val hoτ14 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13τ13
  have hx15τ14 := obs_store_other_val hoτ14 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15τ13
  have hx10τ14 := obs_store_other_val hoτ14 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ13
  have hx16τ14 := obs_store_other_val hoτ14 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ13
  have hx17τ14 := obs_store_other_val hoτ14 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ13
  have hs1τ14 := obs_store_other_val hoτ14 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ13
  have hspτ14 := obs_store_other_val hoτ14 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ13
  have hx19τ14 := obs_store_other_val hoτ14 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ13
  obtain ⟨vmiτ14, hmiτ14⟩ := obs_store_minstret_val hoτ14
  have houtτ14 : τ14.sailOutput = out0 := by rw [hoτ14.out, sailOutput_sigmaPost_store]; exact houtτ13
  have hcodeτ14 : Eval_exprLoaded τ14.mem := by
    rw [hmemτ14e]
    exact loaded_eval_expr_agreeP m2 m3
      (fun k hk => (getElem_writeMap8_disjoint m2 (sp.toNat-848) k (sdData_val V144)
        (by rcases hcodeStk with h | h <;> omega)).symm) hcodem2
  obtain ⟨τ15, j15, ht15', hj15, hGτ15, hmemτ15, hoτ15⟩ :=
    site_800038c0_ee τ14 j14 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800038c0#64) vmiτ14 (sp - 1088#64) Wr
      hGτ14 hpcτ14 hmiτ14 hspτ14 hx13τ14 hcodeτ14 rfl
      (by rw [haddr248]; omega) (by rw [haddr248]; omega)
      (by rw [haddr248, htoh]; omega) (by rw [haddr248]; omega) hj14
  have hstepτ15 : Step ⟨τ14, j14, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ15, j15, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht15'
  have hmemτ15e : τ15.mem = m4 := by rw [hmemτ15, mem_afterNextPC, haddr248]; rw [hmemτ14e]
  have hpcτ15 : τ15.regs.get? Register.PC = some (0x800038c4#64) := by
    have := obs_store_pc_val hoτ15
    rwa [show BitVec.addInt (0x800038c0#64) 4 = (0x800038c4#64 : BitVec 64) from by decide] at this
  have hx15τ15 := obs_store_other_val hoτ15 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15τ14
  have hx10τ15 := obs_store_other_val hoτ15 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ14
  have hx16τ15 := obs_store_other_val hoτ15 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ14
  have hx17τ15 := obs_store_other_val hoτ15 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ14
  have hs1τ15 := obs_store_other_val hoτ15 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ14
  have hspτ15 := obs_store_other_val hoτ15 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ14
  have hx19τ15 := obs_store_other_val hoτ15 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ14
  obtain ⟨vmiτ15, hmiτ15⟩ := obs_store_minstret_val hoτ15
  have houtτ15 : τ15.sailOutput = out0 := by rw [hoτ15.out, sailOutput_sigmaPost_store]; exact houtτ14
  have hcodem3 : Eval_exprLoaded m3 := by rw [← hmemτ14e]; exact hcodeτ14
  have hcodeτ15 : Eval_exprLoaded τ15.mem := by
    rw [hmemτ15e]
    exact loaded_eval_expr_agreeP m3 m4
      (fun k hk => (getElem_writeMap8_disjoint m3 (sp.toNat-840) k (sdData_val Wr)
        (by rcases hcodeStk with h | h <;> omega)).symm) hcodem3
  obtain ⟨τ16, j16, ht16', hj16, hGτ16, hmemτ16, hoτ16⟩ :=
    site_800038c4_ee τ15 j15 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800038c4#64) vmiτ15 (sp - 1088#64) V160
      hGτ15 hpcτ15 hmiτ15 hspτ15 hx15τ15 hcodeτ15 rfl
      (by rw [haddr256]; omega) (by rw [haddr256]; omega)
      (by rw [haddr256, htoh]; omega) (by rw [haddr256]; omega) hj15
  have hstepτ16 : Step ⟨τ15, j15, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ16, j16, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht16'
  have hmemτ16e : τ16.mem = m5 := by rw [hmemτ16, mem_afterNextPC, haddr256]; rw [hmemτ15e]
  have hpcτ16 : τ16.regs.get? Register.PC = some (0x800038c8#64) := by
    have := obs_store_pc_val hoτ16
    rwa [show BitVec.addInt (0x800038c4#64) 4 = (0x800038c8#64 : BitVec 64) from by decide] at this
  have hx10τ16 := obs_store_other_val hoτ16 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ15
  have hx16τ16 := obs_store_other_val hoτ16 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16τ15
  have hx17τ16 := obs_store_other_val hoτ16 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ15
  have hs1τ16 := obs_store_other_val hoτ16 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ15
  have hspτ16 := obs_store_other_val hoτ16 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ15
  have hx19τ16 := obs_store_other_val hoτ16 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ15
  obtain ⟨vmiτ16, hmiτ16⟩ := obs_store_minstret_val hoτ16
  have houtτ16 : τ16.sailOutput = out0 := by rw [hoτ16.out, sailOutput_sigmaPost_store]; exact houtτ15
  have hcodem4 : Eval_exprLoaded m4 := by rw [← hmemτ15e]; exact hcodeτ15
  have hcodeτ16 : Eval_exprLoaded τ16.mem := by
    rw [hmemτ16e]
    exact loaded_eval_expr_agreeP m4 m5
      (fun k hk => (getElem_writeMap8_disjoint m4 (sp.toNat-832) k (sdData_val V160)
        (by rcases hcodeStk with h | h <;> omega)).symm) hcodem4
  --------------------------------------------------------------------------------
  -- 0x800038c8: bne a0,a6 (NOT taken; a0=2, a6=2)
  --------------------------------------------------------------------------------
  obtain ⟨τ17, j17, ht17', hj17, hGτ17, hmemτ17, hoτ17⟩ :=
    site_800038c8_nottaken_ee τ16 j16 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800038c8#64) vmiτ16 (2#64) (2#64)
      hGτ16 hpcτ16 hmiτ16 hx10τ16 hx16τ16 hcodeτ16 rfl (by decide) hj16
  have hstepτ17 : Step ⟨τ16, j16, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ17, j17, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht17'
  have hmemτ17e : τ17.mem = m5 := by rw [hmemτ17]; exact hmemτ16e
  have hpcτ17 : τ17.regs.get? Register.PC = some (0x800038cc#64) := by
    have := obs_branch_nottaken_pc hoτ17
    rwa [show BitVec.addInt (0x800038c8#64) 4 = (0x800038cc#64 : BitVec 64) from by decide] at this
  have hx17τ17 : τ17.regs.get? Register.x17 = some Wr := obs_branch_nottaken_other hoτ17 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx17τ16
  have hs1τ17 : τ17.regs.get? Register.x9 = some sret := obs_branch_nottaken_other hoτ17 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ16
  have hspτ17 : τ17.regs.get? Register.x2 = some (sp - 1088#64) := obs_branch_nottaken_other hoτ17 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ16
  have hx19τ17 : τ17.regs.get? Register.x19 = some Wl := obs_branch_nottaken_other hoτ17 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ16
  obtain ⟨vmiτ17, hmiτ17⟩ := obs_branch_nottaken_minstret hoτ17
  have houtτ17 : τ17.sailOutput = out0 := by rw [hoτ17.out, sailOutput_sigmaPost_branch_nottaken]; exact houtτ16
  have hcodeτ17 : Eval_exprLoaded τ17.mem := by rw [hmemτ17e, ← hmemτ16e]; exact hcodeτ16
  --------------------------------------------------------------------------------
  -- 0x800038cc: add a1,s3,a7 → x11 := Wl + Wr (= a + b, wrapped)
  --------------------------------------------------------------------------------
  obtain ⟨τ18, j18, ht18', hj18, hGτ18, hmemτ18, hoτ18⟩ :=
    site_800038cc_ee τ17 j17 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800038cc#64) vmiτ17 Wl Wr
      hGτ17 hpcτ17 hmiτ17 hx19τ17 hx17τ17 hcodeτ17 rfl hj17
  have hstepτ18 : Step ⟨τ17, j17, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ18, j18, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht18'
  have hmemτ18e : τ18.mem = m5 := by rw [hmemτ18]; exact hmemτ17e
  have hpcτ18 : τ18.regs.get? Register.PC = some (0x800038d0#64) := by
    have := obs_alu_pc hoτ18
    rwa [show BitVec.addInt (0x800038cc#64) 4 = (0x800038d0#64 : BitVec 64) from by decide] at this
  have hx11τ18 : τ18.regs.get? Register.x11 = some (Wl + Wr) :=
    obs_alu_rd hoτ18 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1τ18 : τ18.regs.get? Register.x9 = some sret := obs_alu_other hoτ18 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ17
  have hspτ18 : τ18.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ18 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ17
  have hx19τ18 : τ18.regs.get? Register.x19 = some Wl := obs_alu_other hoτ18 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ17
  obtain ⟨vmiτ18, hmiτ18⟩ := obs_alu_minstret hoτ18
  have houtτ18 : τ18.sailOutput = out0 := by rw [hoτ18.out, sailOutput_sigmaPost_alu]; exact houtτ17
  have hcodeτ18 : Eval_exprLoaded τ18.mem := by rw [hmemτ18e, ← hmemτ17e]; exact hcodeτ17
  --------------------------------------------------------------------------------
  -- 0x800038d0: mv a0,s1 → x10 := sret
  --------------------------------------------------------------------------------
  obtain ⟨τ19, j19, ht19', hj19, hGτ19, hmemτ19, hoτ19⟩ :=
    site_800038d0_ee τ18 j18 (u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x800038d0#64) vmiτ18 sret
      hGτ18 hpcτ18 hmiτ18 hs1τ18 hcodeτ18 rfl hj18
  have hstepτ19 : Step ⟨τ18, j18, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨τ19, j19, u16 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := ht19'
  have hmemτ19e : τ19.mem = m5 := by rw [hmemτ19]; exact hmemτ18e
  have hpcτ19 : τ19.regs.get? Register.PC = some (0x800038d4#64) := by
    have := obs_alu_pc hoτ19
    rwa [show BitVec.addInt (0x800038d0#64) 4 = (0x800038d4#64 : BitVec 64) from by decide] at this
  have hx10τ19 : τ19.regs.get? Register.x10 = some sret := by
    have := obs_alu_rd hoτ19 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sret + sign_extend (m := 64) (0x000#12)) = sret from by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add]
      have : (sign_extend (m := 64) (0x000#12) : BitVec 64).toNat = 0 := by decide
      rw [this]; have := sret.isLt; omega] at this
  have hx11τ19 : τ19.regs.get? Register.x11 = some (Wl + Wr) := obs_alu_other hoτ19 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ18
  have hs1τ19 : τ19.regs.get? Register.x9 = some sret := obs_alu_other hoτ19 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ18
  have hspτ19 : τ19.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ19 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ18
  have hx19τ19 : τ19.regs.get? Register.x19 = some Wl := obs_alu_other hoτ19 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ18
  obtain ⟨vmiτ19, hmiτ19⟩ := obs_alu_minstret hoτ19
  have houtτ19 : τ19.sailOutput = out0 := by rw [hoτ19.out, sailOutput_sigmaPost_alu]; exact houtτ18
  have hcodeτ19 : Eval_exprLoaded τ19.mem := by rw [hmemτ19e, ← hmemτ18e]; exact hcodeτ18
  --------------------------------------------------------------------------------
  -- 0x800038d4: jal value_int → PC := 0x8000280c, x1 := 0x800038d8
  --------------------------------------------------------------------------------
  -- `Value_intLoaded m5` (from `c.σ.mem`, survives the 5 stack stores)
  have hVint5 : Value_intLoaded m5 := by
    have h1 : Value_intLoaded m1 := loaded_int_writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val V120) (by rcases hviStk with h | h <;> omega) hVint
    have h2 : Value_intLoaded m2 := loaded_int_writeMap8 m1 (sp.toNat - 832) (sdData_val V136) (by rcases hviStk with h | h <;> omega) h1
    have h3 : Value_intLoaded m3 := loaded_int_writeMap8 m2 (sp.toNat - 848) (sdData_val V144) (by rcases hviStk with h | h <;> omega) h2
    have h4 : Value_intLoaded m4 := loaded_int_writeMap8 m3 (sp.toNat - 840) (sdData_val Wr) (by rcases hviStk with h | h <;> omega) h3
    exact loaded_int_writeMap8 m4 (sp.toNat - 832) (sdData_val V160) (by rcases hviStk with h | h <;> omega) h4
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
  have hcodem5 : Eval_exprLoaded m5 := by rw [← hmemτ16e]; exact hcodeτ16
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
    show read64 (writeMap8 m4 (sp.toNat - 832) (sdData_val V160)) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj m4 (sp.toNat - 40) (sp.toNat - 832) (sdData_val V160) (by omega)]
    show read64 (writeMap8 m3 (sp.toNat - 840) (sdData_val Wr)) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj m3 (sp.toNat - 40) (sp.toNat - 840) (sdData_val Wr) (by omega)]
    show read64 (writeMap8 m2 (sp.toNat - 848) (sdData_val V144)) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj m2 (sp.toNat - 40) (sp.toNat - 848) (sdData_val V144) (by omega)]
    show read64 (writeMap8 m1 (sp.toNat - 832) (sdData_val V136)) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj m1 (sp.toNat - 40) (sp.toNat - 832) (sdData_val V136) (by omega)]
    show read64 (writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val V120)) (sp.toNat - 40) = _
    rw [read64_writeMap8_disj c.σ.mem (sp.toNat - 40) (sp.toNat - 848) (sdData_val V120) (by omega)]
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
    show c.σ.mem[k]? = (writeMap8 m4 (sp.toNat - 832) (sdData_val V160))[k]?
    rw [getElem_writeMap8_disjoint m4 (sp.toNat - 832) k (sdData_val V160) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m3 (sp.toNat - 840) (sdData_val Wr))[k]?
    rw [getElem_writeMap8_disjoint m3 (sp.toNat - 840) k (sdData_val Wr) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m2 (sp.toNat - 848) (sdData_val V144))[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat - 848) k (sdData_val V144) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat - 832) (sdData_val V136))[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat - 832) k (sdData_val V136) (by omega)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val V120))[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) k (sdData_val V120) (by omega)]
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
    ((memExtends_writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val V120)).trans
      (memExtends_writeMap8 m1 (sp.toNat - 832) (sdData_val V136))).trans
      (((memExtends_writeMap8 m2 (sp.toNat - 848) (sdData_val V144)).trans
        (memExtends_writeMap8 m3 (sp.toNat - 840) (sdData_val Wr))).trans
        (memExtends_writeMap8 m4 (sp.toNat - 832) (sdData_val V160)))
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
    show c.σ.mem[k]? = (writeMap8 m4 (sp.toNat - 832) (sdData_val V160))[k]?
    rw [getElem_writeMap8_disjoint m4 (sp.toNat - 832) k (sdData_val V160) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m3 (sp.toNat - 840) (sdData_val Wr))[k]?
    rw [getElem_writeMap8_disjoint m3 (sp.toNat - 840) k (sdData_val Wr) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m2 (sp.toNat - 848) (sdData_val V144))[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat - 848) k (sdData_val V144) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat - 832) (sdData_val V136))[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat - 832) k (sdData_val V136) (by omega)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val V120))[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) k (sdData_val V120) (by omega)]
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
        have f19 : τ19.regs.get? R = τ18.regs.get? R :=
          (hoτ19.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f18 : τ18.regs.get? R = τ17.regs.get? R :=
          (hoτ18.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f17 : τ17.regs.get? R = τ16.regs.get? R :=
          (hoτ17.1 R hmc' hmt' hmip').trans (get?_sigmaPost_branch_nottaken _ _ _ R hmi' hpc' hnpc' hmii')
        have f16 : τ16.regs.get? R = τ15.regs.get? R :=
          (hoτ16.1 R hmc' hmt' hmip').trans (get?_sigmaPost_store _ _ _ _ R hmi' hpc' hnpc' hmii')
        have f15 : τ15.regs.get? R = τ14.regs.get? R :=
          (hoτ15.1 R hmc' hmt' hmip').trans (get?_sigmaPost_store _ _ _ _ R hmi' hpc' hnpc' hmii')
        have f14 : τ14.regs.get? R = τ13.regs.get? R :=
          (hoτ14.1 R hmc' hmt' hmip').trans (get?_sigmaPost_store _ _ _ _ R hmi' hpc' hnpc' hmii')
        have f13 : τ13.regs.get? R = τ12.regs.get? R :=
          (hoτ13.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f12 : τ12.regs.get? R = τ11.regs.get? R :=
          (hoτ12.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f11 : τ11.regs.get? R = τ10.regs.get? R :=
          (hoτ11.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f10 : τ10.regs.get? R = τ9.regs.get? R :=
          (hoτ10.1 R hmc' hmt' hmip').trans (get?_sigmaPost_branch_nottaken _ _ _ R hmi' hpc' hnpc' hmii')
        have f9 : τ9.regs.get? R = τ8.regs.get? R :=
          (hoτ9.1 R hmc' hmt' hmip').trans (get?_sigmaPost_store _ _ _ _ R hmi' hpc' hnpc' hmii')
        have f8 : τ8.regs.get? R = τ7.regs.get? R :=
          (hoτ8.1 R hmc' hmt' hmip').trans (get?_sigmaPost_store _ _ _ _ R hmi' hpc' hnpc' hmii')
        have f7 : τ7.regs.get? R = τ6.regs.get? R :=
          (hoτ7.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f6 : τ6.regs.get? R = τ5.regs.get? R :=
          (hoτ6.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f5 : τ5.regs.get? R = τ4.regs.get? R :=
          (hoτ5.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f4 : τ4.regs.get? R = τ3.regs.get? R :=
          (hoτ4.1 R hmc' hmt' hmip').trans (get?_sigmaPost_branch_nottaken _ _ _ R hmi' hpc' hnpc' hmii')
        have f3 : τ3.regs.get? R = τ2.regs.get? R :=
          (hoτ3.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have f2 : τ2.regs.get? R = τ1.regs.get? R :=
          (hoτ2.1 R hmc' hmt' hmip').trans (get?_sigmaPost_branch_nottaken _ _ _ R hmi' hpc' hnpc' hmii')
        have f1 : τ1.regs.get? R = σ16.regs.get? R :=
          (hoτ1.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g16 : σ16.regs.get? R = σ15.regs.get? R :=
          (hobs16.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')
        have g15 : σ15.regs.get? R = σ14.regs.get? R :=
          (hobs15.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g14 : σ14.regs.get? R = σ13.regs.get? R :=
          (hobs14.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g13 : σ13.regs.get? R = σ12.regs.get? R :=
          (hobs13.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g12 : σ12.regs.get? R = σ11.regs.get? R :=
          (hobs12.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g11 : σ11.regs.get? R = σ10.regs.get? R :=
          (hobs11.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g10 : σ10.regs.get? R = σ9.regs.get? R :=
          (hobs10.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g9 : σ9.regs.get? R = σ8.regs.get? R :=
          (hobs9.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g8 : σ8.regs.get? R = σ7.regs.get? R :=
          (hobs8.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g7 : σ7.regs.get? R = σ6.regs.get? R :=
          (hobs7.1 R hmc' hmt' hmip').trans (get?_sigmaPost_branch_nottaken _ _ _ R hmi' hpc' hnpc' hmii')
        have g6 : σ6.regs.get? R = σ5.regs.get? R :=
          (hobs6.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g5 : σ5.regs.get? R = σ4.regs.get? R :=
          (hobs5.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g4 : σ4.regs.get? R = σ3.regs.get? R :=
          (hobs4.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g3 : σ3.regs.get? R = σ2.regs.get? R :=
          (hobs3.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' he8 hnpc' hmii')
        have g2 : σ2.regs.get? R = σ1.regs.get? R :=
          (hobs2.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        have g1 : σ1.regs.get? R = c.σ.regs.get? R :=
          (hobs1.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (by decide)) hnpc' hmii')
        rw [f22, f21, fvi, f20, f19, f18, f17, f16, f15, f14, f13, f12, f11, f10, f9, f8, f7, f6, f5, f4, f3, f2, f1,
          g16, g15, g14, g13, g12, g11, g10, g9, g8, g7, g6, g5, g4, g3, g2, g1]
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
        show (writeMap8 m4 (sp.toNat - 832) (sdData_val V160))[a]? = c.σ.mem[a]?
        rw [getElem_writeMap8_disjoint m4 (sp.toNat - 832) a (sdData_val V160) (by omega)]
        show (writeMap8 m3 (sp.toNat - 840) (sdData_val Wr))[a]? = c.σ.mem[a]?
        rw [getElem_writeMap8_disjoint m3 (sp.toNat - 840) a (sdData_val Wr) (by omega)]
        show (writeMap8 m2 (sp.toNat - 848) (sdData_val V144))[a]? = c.σ.mem[a]?
        rw [getElem_writeMap8_disjoint m2 (sp.toNat - 848) a (sdData_val V144) (by omega)]
        show (writeMap8 m1 (sp.toNat - 832) (sdData_val V136))[a]? = c.σ.mem[a]?
        rw [getElem_writeMap8_disjoint m1 (sp.toNat - 832) a (sdData_val V136) (by omega)]
        show (writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val V120))[a]? = c.σ.mem[a]?
        rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat - 848) a (sdData_val V120) (by omega)]
      rw [hm5c]; exact hmemframe a ha hA
  -- the full Steps chain c → τ22
  have hchain : Steps c ⟨τ22, j22, cvi.steps + 1 + 1⟩ :=
    (Steps.single hstep1).trans <| (Steps.single hstep2).trans <| (Steps.single hstep3).trans <|
    (Steps.single hstep4).trans <| (Steps.single hstep5).trans <| (Steps.single hstep6).trans <|
    (Steps.single hstep7).trans <| (Steps.single hstep8).trans <| (Steps.single hstep9).trans <|
    (Steps.single hstep10).trans <| (Steps.single hstep11).trans <| (Steps.single hstep12).trans <|
    (Steps.single hstep13).trans <| (Steps.single hstep14).trans <| (Steps.single hstep15).trans <|
    (Steps.single hstep16).trans <| (Steps.single hstepτ1).trans <| (Steps.single hstepτ2).trans <|
    (Steps.single hstepτ3).trans <| (Steps.single hstepτ4).trans <| (Steps.single hstepτ5).trans <|
    (Steps.single hstepτ6).trans <| (Steps.single hstepτ7).trans <| (Steps.single hstepτ8).trans <|
    (Steps.single hstepτ9).trans <| (Steps.single hstepτ10).trans <| (Steps.single hstepτ11).trans <|
    (Steps.single hstepτ12).trans <| (Steps.single hstepτ13).trans <| (Steps.single hstepτ14).trans <|
    (Steps.single hstepτ15).trans <| (Steps.single hstepτ16).trans <| (Steps.single hstepτ17).trans <|
    (Steps.single hstepτ18).trans <| (Steps.single hstepτ19).trans <| (Steps.single hstepτ20).trans <|
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
        -- the blockC_add residuals hold at EVERY config reachable as the
        -- post-`TwoSubReturn` landing (stated ∀-closed over the post config):
        (∀ c' : Vsa.Machine.Config,
          TwoSubReturn gpre N A SL φf φc st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
          AddResid gpre N A SL sp r sret aExpr Wl c') ∧
        -- entry-ghost g bridge (as blockC_add / blockC_neg consume it)
        g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
        g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧ g Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x2 == R) = false →
          gpre R = g R))
      (EvalExitD g N A SL φf φc st'' (.int (wrap64 (a + b))) sp r sret m0)

/-- **`evalAddSim`**: the `EvalE.binary .add` (int-pilot) recursive case, composing
`blockB_binary ≫ blockC_add ≫ blockD_v_rec` in the `EvalIH` motive shape. -/
theorem evalAddSim : EvalAddSimGoal := by
  intro gouter gpre g N A SL φf φc st st' st'' d env el er a b
    sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 Wl out0 m0 hIHl hIHr _hEvalE hSizeF hSizeC
  intro c hpre
  obtain ⟨ment, hArm, hBE, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
    hpayL, hexprL, hpayR, hexprR, hMentPop, hMemExtM0, hResid,
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
        hpayL, hexprL, hpayR, hexprR, hMentPop, hMemExtM0⟩
  -- the blockC_add residuals at c2
  have hR : AddResid gpre N A SL sp r sret aExpr Wl c2 := hResid c2 hTS
  -- the post-both-calls console output correspondence (`OutRepr c2 st''`)
  have hOutC2 : String.join c2.σ.sailOutput.toList = st''.out := hTS.2.2.2.2.2.2.2.1
  -- === block C: dispatch + add tail → PreEpilogueVD @0x800033ec ===
  obtain ⟨c3, hs3, mpre, φfm, φcm, φfe, φce, hpfm, hpcm, hpfe, hpce, hPreD⟩ :=
    blockC_add gpre g N A SL φf φc st' st'' a b sp r sret aExpr v8 v9 v18 v19 Wl c2.σ.sailOutput m0
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
  have hpfm' : PhiExtends φf φfm st''.store.frames.size := hSizeF ▸ hpfm
  have hpcm' : PhiExtends φc φcm st''.store.closures.size := hSizeC ▸ hpcm
  have hpfF : PhiExtends φf φfe st''.store.frames.size := hpfm'.trans hpfe
  have hpcF : PhiExtends φc φce st''.store.closures.size := hpcm'.trans hpce
  have hExit : EvalExit g N A SL φf φc st'' (.int (wrap64 (a + b))) sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfF hpcF hExitE
  exact ⟨c4, ((hs2.trans hs3).trans hs4), hExit, hMemExt,
    φf', φc', hpfF.trans hpf', hpcF.trans hpc', hSurv⟩

end Vsa.Sim
