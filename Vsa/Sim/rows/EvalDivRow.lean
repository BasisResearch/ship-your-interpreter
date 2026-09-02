import Vsa.Sim.EvalBinSim3
import Vsa.Sim.EvalDivArm
import Vsa.Sim.DivTailSites
import Vsa.Sim.DivSpec3
import Vsa.Sim.DivDispatchSeg
import Vsa.Sim.EvalDivValueTail
import Vsa.Sim.LoopStep
import Vsa.Sim.rows.EvalMulRow
import Vsa.Sim.rows.IntPostEpilogue
import Vsa.Sim.BinopTailGen

/-!
# `EvalDivRow` — Wave-D M4 row: `evalDivSim` (the `EvalE.binary .div` int case)

Mirrors the `.mul` row (`rows/EvalMulRow.lean`), swapping the operator dispatch for
`.div` (token 14, slot `opTableBase+12` → DIV-int arm `0x800037dc`) and, crucially,
the arm TAIL: where `.mul` calls libgcc `__muldi3`, `.div` calls libgcc `__divdi3`.

Unlike `.mul`, the `.div` arm entry+dispatch (`0x8000351c → 0x8000381c`, landing
`DivDispatchPost` with `x10=Wl`, `x11=Wr`, `x9=sret`, `x2=v2`) is ALREADY PROVEN as
`evalDivChain_dispatch` (`Vsa/Sim/EvalDivArm.lean`), so `blockC_div` uses it directly
instead of re-deriving mul's inline dispatch.  The value tail then runs the six
`DivTailSites` steps `0x8000381c…0x80003830`:

  `jal __divdi3 ; mv a1,a0 ; mv a0,s1 ; jal value_int ; ld s3,0x418(sp) ; j 0x800033ec`.

The `__divdi3` seam is discharged by the STRONG `divdi3_spec` (`Vsa/Sim/DivSpec3.lean`,
`x10.toInt = n.toInt.tdiv d.toInt` + `sailOutput=o` + `NotWrittenD` frame).  The value
bridge commutes `res → wrap64 (a.tdiv b)` via `div_wrap_bridge` (`res.toInt` pins
`res` uniquely by `BitVec.toInt` injectivity).

Assembled INLINE (not via the `divValueTail` combinator, which cannot host a runtime
value_int-entry ghost snapshot — see `experiments/binop-value-tail-wiring.md` VERDICT).

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
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- The `.div` value bridge: `res` (the `__divdi3` quotient, pinned uniquely by
`res.toInt = Wl.toInt.tdiv Wr.toInt`) boxes to `.int (wrap64 (a.tdiv b))`. -/
theorem div_wrap_bridge (Wl Wr res : BitVec 64) (a b : Int)
    (ha : Wl.toInt = a) (hb : Wr.toInt = b)
    (hres : res.toInt = Wl.toInt.tdiv Wr.toInt) :
    (BitVec.ofNat 64 res.toNat).toInt = wrap64 (a.tdiv b) := by
  rw [ofNat_toNat_self64, hres, ha, hb]
  unfold wrap64
  have h : (BitVec.ofInt 64 (a.tdiv b)) = res := by
    rw [← ha, ← hb, ← hres, BitVec.ofInt_toInt]
  rw [h, ← ha, ← hb, ← hres]

/-- The reflected chain log only depends on `s`'s log through a prefix: evaluating
`bs` on `s` yields `s.log ++ (evaluating `bs` on the log-cleared state)`. -/
theorem evalBlocks_log_shift :
    ∀ (bs : List BBlock) (s : SegEvalState),
      (evalBlocks bs s).log
        = s.log ++ (evalBlocks bs { s with log := [] }).log := by
  intro bs
  induction bs with
  | nil => intro s; simp only [evalBlocks, List.append_nil]
  | cons b rest ih =>
    intro s
    rw [evalBlocks_cons, evalBlocks_cons, ih (evalBlock s b),
        ih (evalBlock { s with log := [] } b)]
    -- both log-cleared inner states are structurally identical (same regs/loads)
    have hstate : { (evalBlock { s with log := [] } b) with log := [] }
        = { (evalBlock s b) with log := [] } := rfl
    rw [hstate]
    -- (evalBlock s b).log = s.log ++ wlogM …
    have hlog : (evalBlock s b).log = s.log ++ wlogM b.body s.regs s.loads := rfl
    have hlog0 : (evalBlock { s with log := [] } b).log = wlogM b.body s.regs s.loads := by
      simp only [evalBlock, List.nil_append]
    rw [hlog, hlog0, List.append_assoc]

/-- Store-window containment for a whole `evalBlocks` chain whose every block is a
frame chain (`x2 = base` preserved, all stores `base`-relative at `off ≤ 0x108`):
every store window lies in `[base.toNat, base.toNat + 0x108)`.  Generalizes
`wlogM_store_offsets` from one block body to the reflected chain log. -/
theorem evalBlocks_frame_offsets :
    ∀ (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
      (base : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) (fb : FrameBundle m base),
      srcVal 2 L = base →
      (∀ b ∈ bs, ∀ a ∈ b.body, a.rd ≠ 2) →
      (∀ b ∈ bs, ∀ a ∈ b.body, (a.kind = .sw ∨ a.kind = .sd ∨ a.kind = .sb ∨ a.kind = .sh) →
        a.rs1 = 2 ∧ (sign_extend (m := 64) a.imm : BitVec 64).toNat + 8 ≤ 0x108) →
      ∀ e ∈ (evalBlocks bs (SegEvalState.init L lds)).log,
        base.toNat ≤ e.1 ∧ e.1 + e.2.1 ≤ base.toNat + 0x108 := by
  intro bs
  induction bs with
  | nil =>
    intro L lds base m fb _ _ _ e he
    simp only [evalBlocks, SegEvalState.init, List.not_mem_nil] at he
  | cons b rest ih =>
    intro L lds base m fb h2 hrd hst e he
    rw [evalBlocks_cons] at he
    -- the chain's log = (evalBlock init b).log ++ (rest chain over evalBlock's state)
    -- but evalBlocks accumulates: log of `evalBlocks rest (evalBlock (init L lds) b)`
    -- contains this block's log as a prefix.  Split on membership.
    have hlog_split := evalBlocks_log_shift rest (evalBlock (SegEvalState.init L lds) b)
    rw [hlog_split, List.mem_append] at he
    rcases he with hb | hrest
    · -- e is in this block's own log = wlogM b.body L lds
      have hbb : e ∈ wlogM b.body L lds := by
        simpa only [evalBlock, SegEvalState.init, List.nil_append] using hb
      obtain ⟨a, ha, hk, haddr⟩ :=
        wlogM_store_offsets b.body L lds base m fb h2
          (fun x hx => hrd b (List.mem_cons_self ..) x hx)
          (fun x hx hkx => ⟨(hst b (List.mem_cons_self ..) x hx hkx).1,
            by have := (hst b (List.mem_cons_self ..) x hx hkx).2; omega⟩) e hbb
      obtain ⟨hrs1, hoff⟩ := hst b (List.mem_cons_self ..) a ha hk
      have hw : e.2.1 = 1 ∨ e.2.1 = 2 ∨ e.2.1 = 4 ∨ e.2.1 = 8 :=
        wlogM_width b.body L lds e hbb
      refine ⟨by rw [haddr]; omega, ?_⟩
      rw [haddr]; rcases hw with h | h | h | h <;> omega
    · -- e is in the rest chain; base preserved because b doesn't write x2
      have hbase' : srcVal 2 (evalBlock (SegEvalState.init L lds) b).regs = base := by
        show srcVal 2 (runGM b.body (SegEvalState.init L lds).regs (SegEvalState.init L lds).loads) = base
        rw [srcVal_runGM_ne 2 b.body (fun x hx => hrd b (List.mem_cons_self ..) x hx)]
        exact h2
      exact ih (evalBlock (SegEvalState.init L lds) b).regs
        (evalBlock (SegEvalState.init L lds) b).loads base m fb hbase'
        (fun x hx => hrd x (List.mem_cons_of_mem _ hx))
        (fun x hx => hst x (List.mem_cons_of_mem _ hx)) e hrest

/-- **The div-dispatch memory frame.**  The dispatch writeLog `mA` only touches the
frame window `[v2.toNat, v2.toNat + 0x108)` — every store lands there (all `x2`-relative
at off ≤ 0x100, width 8) — so outside that window `mA` agrees with the input memory.
Specialized to `divDispatch` via `evalBlocks_frame_offsets` + `writeLog_getElem_disjoint`. -/
theorem divDispatch_mem_frame (v2 sret Wr Wl : BitVec 64) (lds : List (List (BitVec 8)))
    (m : Std.ExtHashMap Nat (BitVec 8)) (fb : FrameBundle m v2) :
    ∀ k : Nat, ¬ (v2.toNat ≤ k ∧ k < v2.toNat + 0x108) →
      (writeLog m (evalBlocks divDispatch (SegEvalState.init (divDispL v2 sret Wr Wl) lds)).log)[k]?
        = m[k]? := by
  intro k hk
  refine writeLog_getElem_disjoint k _ m
    (fun e he => evalBlocks_init_log_width divDispatch (divDispL v2 sret Wr Wl) lds e he)
    (fun e he => ?_)
  obtain ⟨hlo, hhi⟩ :=
    evalBlocks_frame_offsets divDispatch (divDispL v2 sret Wr Wl) lds v2 m fb
      (by rfl)
      (by decide)
      (by decide) e he
  -- e's window ⊂ [v2, v2+0x108); k outside ⇒ disjoint
  by_cases hc : v2.toNat ≤ k
  · exact Or.inr (by omega)
  · exact Or.inl (by omega)

/-- `__divdi3Loaded` survives on any memory agreeing over `[0x800046a4, 0x800046ac)`. -/
theorem loaded_divdi3_agreeP (m m' : Mem)
    (ha : ∀ a, (0x800046a4 ≤ a ∧ a < 0x800046ac) → m[a]? = m'[a]?)
    (h : Vsa.Sim.Code.__divdi3Loaded m) : Vsa.Sim.Code.__divdi3Loaded m' := by
  simp only [Vsa.Sim.Code.__divdi3Loaded, Vsa.Sim.Code.__divdi3Chunk0] at h ⊢
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [← ha _ (by omega)]; assumption)

/-- `__umoddi3Loaded` survives on any memory agreeing over `[0x800046f4, 0x80004728)`. -/
theorem loaded_umoddi3_agreeP (m m' : Mem)
    (ha : ∀ a, (0x800046f4 ≤ a ∧ a < 0x80004728) → m[a]? = m'[a]?)
    (h : Vsa.Sim.Code.__umoddi3Loaded m) : Vsa.Sim.Code.__umoddi3Loaded m' := by
  simp only [Vsa.Sim.Code.__umoddi3Loaded, Vsa.Sim.Code.__umoddi3Chunk0] at h ⊢
  repeat' apply And.intro
  all_goals (first
    | (rw [← ha _ (by omega)]; simp_all only [])
    | simp_all only [])

/-- `__hidden___udivdi3Loaded` survives on any memory agreeing over
`[0x800046ac, 0x800046f4)`. -/
theorem loaded_udivdi3_agreeP (m m' : Mem)
    (ha : ∀ a, (0x800046ac ≤ a ∧ a < 0x800046f4) → m[a]? = m'[a]?)
    (h : __hidden___udivdi3Loaded m) : __hidden___udivdi3Loaded m' := by
  obtain ⟨hc0, hc1⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [Vsa.Sim.Code.__hidden___udivdi3Chunk0] at hc0 ⊢
    repeat' apply And.intro
    all_goals (first
      | (rw [← ha _ (by omega)]; simp_all only [])
      | simp_all only [])
  · simp only [Vsa.Sim.Code.__hidden___udivdi3Chunk1] at hc1 ⊢
    repeat' apply And.intro
    all_goals (first
      | (rw [← ha _ (by omega)]; simp_all only [])
      | simp_all only [])

/-! ## `blockC_div` — the `.div` int dispatch + `__divdi3` value tail -/

theorem blockC_div
    (gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' st'' : Vsa.While.St) (a b : Int)
    (sp r sret aExpr : BitVec 64) (v8 v9 v18 v19 Wl : BitVec 64) (out0 : Array String)
    (m0 : Mem)
    (hbNe : b ≠ 0)
    (hOv : ¬(a = -2^63 ∧ b = -1)) :
    Triple
      (fun c =>
        TwoSubReturn gpre N A SL φf φc nf nc st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c ∧
        gpre Register.x8 = some aExpr ∧
        read32 c.σ.mem (aExpr.toNat + 8) = some 14 ∧      -- op token = binOpTok .div
        DivSlotPinned c.σ.mem ∧
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
        -- === the DIV-specific extra conjuncts (libgcc __divdi3 code images) ===
        Vsa.Sim.Code.__divdi3Loaded c.σ.mem ∧
        Vsa.Sim.Code.__umoddi3Loaded c.σ.mem ∧
        __hidden___udivdi3Loaded c.σ.mem ∧
        (sp.toNat ≤ 0x800046a4 ∨ 0x80004728 ≤ SL.lo) ∧  -- libgcc div block disjoint from stack
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        (sp.toNat ≤ 0x8000280c ∨ 0x8000281c ≤ SL.lo) ∧
        (opTableBase + 20 ≤ SL.lo ∨ sp.toNat ≤ opTableBase) ∧
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
        PreEpilogueVD g N A SL φfe φce st'' (.int (wrap64 (a.tdiv b))) sp r sret v8 v9 v18 out0 m0 mpre c) := by
  intro c hpre
  obtain ⟨hTS, hgx8, hopTok, hSlot, hFullPop, hX19, hWlBuf, hKindResp,
    hexprAl, hexprLo, hexprHi, hexprWin, hexprSL, houtStr, hout0eq,
    hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEvalCode, hraAl,
    hVint, hDivdi3, hUmoddi3, hUdivdi3, hdivStk, hcodeStk, hviStk, hTableStk, hsretInSL,
    hSLloSp, hSLlo, hSLwin, hsphiRam, hsp8, hSLhiRam, hspSLhi,
    hgv8, hgv9, hgv18, hgv2, hgprex19, hgx19, hbridge⟩ := hpre
  obtain ⟨hG, htick, hpc, hra, hs1, hsp, ⟨vmi, hmi⟩, hout, hframe,
    ⟨w19, hgprex19', hs3slot⟩, hstoreBundle, hcode,
    hslotRa, hslotS0, hslotS1, hslotS2, hMemExt, hmemframe⟩ := hTS
  have hw19 : w19 = v19 := by rw [hgprex19] at hgprex19'; exact (Option.some.inj hgprex19').symm
  obtain ⟨φfm, φcm, hpfm, hpcm, ⟨φcr, hpcr, hvalR⟩, ⟨φcl, hvalL⟩,
    φf', φc', hpf', hpc', hstore', hstoreSurv'⟩ := hstoreBundle
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- Phase-0: scalar sp/SL arithmetic + geometry bundles derived ONCE in small-context
  -- lemmas (`spArith`/`slotGeom8`/`exprGeom4`), not re-omega'd in the row body.
  have hSB : StackBounds sp SL := ⟨hSLloSp, hSLlo, hSLwin, hsp8, hsphiRam⟩
  have hEB : ExprBounds aExpr := ⟨hexprAl, hexprLo, hexprHi, hexprWin⟩
  have hAr : SpArith sp SL := spArith hSB
  have hsp1088 : 1088 ≤ sp.toNat := hAr.sp1088
  have hspLoc : 0x80000000 ≤ sp.toNat := hAr.spLo
  have hspHtifLoc : tohostAddr + 16 + 1088 ≤ sp.toNat := hAr.spHtif
  have hSLlo40 : SL.lo ≤ sp.toNat - 40 := hAr.SLlo40
  have hSLlo32 : SL.lo ≤ sp.toNat - 32 := hAr.SLlo32
  have gExpr8 := exprGeom4 hEB 8 (by decide) (by decide)
  have gExpr4 := exprGeom4 hEB 4 (by decide) (by decide)
  have g1088 := slotGeom8 hSB 1088 (by decide) (by decide) (by decide)
  have g944  := slotGeom8 hSB 944  (by decide) (by decide) (by decide)
  have g936  := slotGeom8 hSB 936  (by decide) (by decide) (by decide)
  have g40   := slotGeom8 hSB 40   (by decide) (by decide) (by decide)
  have hTopW := topSlotWin (by omega : (32 : Nat) ≤ sp.toNat)
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  have hNorm := armNorms hsp1088 hspsub
  have hRpb := rpbShift (by omega : (944 : Nat) ≤ sp.toNat)
  have hAbove40 : sp.toNat - 824 ≤ sp.toNat - 40 := Nat.sub_le_sub_left (by decide) _
  have hAbove32 : sp.toNat - 824 ≤ sp.toNat - 32 := Nat.sub_le_sub_left (by decide) _
  have hx8c : c.σ.regs.get? Register.x8 = some aExpr :=
    (hframe Register.x8 (by decide) (by decide)).trans hgx8
  -- === extract the value-tail operand data (right payload = Wr; left payload = Wl) ===
  have hvalR' : ValueRepr c.σ.mem N φcr (sp.toNat - 944) (.int b) := hvalR
  obtain ⟨hkindR, pR, hpayR64, hpRb⟩ := valueRepr_int_pay64 hvalR'
  obtain ⟨rkb0, rkb1, rkb2, rkb3, hrkb0, hrkb1, hrkb2, hrkb3, hrkbrec⟩ :=
    read32_bytes c.σ.mem (sp.toNat - 944) 2 hkindR
  obtain ⟨rpb0, rpb1, rpb2, rpb3, rpb4, rpb5, rpb6, rpb7, hrpb0, hrpb1, hrpb2, hrpb3, hrpb4, hrpb5, hrpb6, hrpb7, hrprec⟩ :=
    read64_bytes c.σ.mem (sp.toNat - 944 + 8) pR hpayR64
  have hWrNat : (bytesVal MKind.ld [rpb0, rpb1, rpb2, rpb3, rpb4, rpb5, rpb6, rpb7] : BitVec 64).toNat = pR := by
    show (sign_extend (m := 64)
      ((((((((rpb7.append rpb6).append rpb5).append rpb4).append rpb3).append rpb2).append rpb1).append rpb0) : BitVec (8*8))).toNat = pR
    rw [sext_full, word8_toNat_recon, hrprec]
  have hWr_toInt : (bytesVal MKind.ld [rpb0, rpb1, rpb2, rpb3, rpb4, rpb5, rpb6, rpb7] : BitVec 64).toInt = b := by
    have hpe : (bytesVal MKind.ld [rpb0, rpb1, rpb2, rpb3, rpb4, rpb5, rpb6, rpb7] : BitVec 64)
        = BitVec.ofNat 64 pR := by rw [← hWrNat]; exact (ofNat_toNat_self64 _).symm
    rw [hpe]; exact hpRb
  have hWrNe : (bytesVal MKind.ld [rpb0, rpb1, rpb2, rpb3, rpb4, rpb5, rpb6, rpb7] : BitVec 64) ≠ 0 := by
    intro hz; apply hbNe; rw [← hWr_toInt, hz]; simp
  have hvalL' : ValueRepr c.σ.mem N φcl (sp.toNat - 968) (.int a) := hvalL
  obtain ⟨hkindL, pL, hpayL64, hpLa⟩ := valueRepr_int_pay64 hvalL'
  have hpayL64' : read64 c.σ.mem (sp.toNat - 960) = some pL := by
    rw [hAr.e968] at hpayL64; exact hpayL64
  have hWlNat : Wl.toNat = pL := by
    have := hWlBuf.symm.trans hpayL64'; exact Option.some.inj this
  have hWl_toInt : Wl.toInt = a := by
    have hpe : Wl = BitVec.ofNat 64 pL := by rw [← hWlNat]; exact (ofNat_toNat_self64 Wl).symm
    rw [hpe]; exact hpLa
  -- === op-token bytes (14 = [0x0e,0,0,0]) ===
  obtain ⟨ob0, ob1, ob2, ob3, hob0, hob1, hob2, hob3, hobrec⟩ :=
    read32_bytes c.σ.mem (aExpr.toNat + 8) 14 hopTok
  have hobv : ob0.toNat = 14 ∧ ob1.toNat = 0 ∧ ob2.toNat = 0 ∧ ob3.toNat = 0 :=
    word32_split (by decide) hobrec
  have hob0' : c.σ.mem[aExpr.toNat + 8]? = some (0x0e#8) := by
    have hbb : ob0 = 0x0e#8 := by apply BitVec.eq_of_toNat_eq; rw [hobv.1]; rfl
    rw [← hbb]; exact hob0
  have hob1' : c.σ.mem[aExpr.toNat + 8 + 1]? = some (0#8) := by
    have hbb : ob1 = 0#8 := by apply BitVec.eq_of_toNat_eq; rw [hobv.2.1]; rfl
    rw [← hbb]; exact hob1
  have hob2' : c.σ.mem[aExpr.toNat + 8 + 2]? = some (0#8) := by
    have hbb : ob2 = 0#8 := by apply BitVec.eq_of_toNat_eq; rw [hobv.2.2.1]; rfl
    rw [← hbb]; exact hob2
  have hob3' : c.σ.mem[aExpr.toNat + 8 + 3]? = some (0#8) := by
    have hbb : ob3 = 0#8 := by apply BitVec.eq_of_toNat_eq; rw [hobv.2.2.2]; rfl
    rw [← hbb]; exact hob3
  -- === left-kind reload byte (e-window, sp-1088 = 2) ===
  obtain ⟨kb0, kb1, kb2, kb3, kb4, kb5, kb6, kb7, hkb0, hkb1, hkb2, hkb3, hkb4, hkb5, hkb6, hkb7, hkbrec⟩ :=
    read64_bytes c.σ.mem (sp.toNat - 1088) ((2#64 : BitVec 64).toNat) hKindResp
  have hkVal : bytesVal MKind.ld [kb0, kb1, kb2, kb3, kb4, kb5, kb6, kb7] = (2#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq
    show (sign_extend (m := 64)
      ((((((((kb7.append kb6).append kb5).append kb4).append kb3).append kb2).append kb1).append kb0) : BitVec (8*8))).toNat = _
    rw [sext_full, word8_toNat_recon, hkbrec]
  -- === right-kind read byte (c-window, sp-944 = 2), as lw bytes ===
  have hcVal : bytesVal MKind.lw [rkb0, rkb1, rkb2, rkb3] = (2#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq
    show (sign_extend (m := 64) ((((rkb3.append rkb2).append rkb1).append rkb0) : BitVec (8*4))).toNat = _
    rw [sext_word_small _ 2 (by decide) (by rw [word_toNat_recon]; exact hrkbrec)]
  -- === frame addresses ===
  have haddr944 : ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 944 :=
    spill_addr sp (0x090#12) 944 (by decide) (by decide) hsp1088
  have haddr936 : ((sp - 1088#64) + sign_extend (m := 64) (0x098#12)).toNat = sp.toNat - 936 :=
    spill_addr sp (0x098#12) 936 (by decide) (by decide) hsp1088
  have haddr0 : ((sp - 1088#64) + sign_extend (m := 64) (0x000#12)).toNat = sp.toNat - 1088 := by
    have : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by apply BitVec.eq_of_toNat_eq; decide
    rw [this, BitVec.add_zero]; exact hspsub
  have haddr1048 : ((sp - 1088#64) + sign_extend (m := 64) (0x418#12)).toNat = sp.toNat - 40 :=
    spill_addr sp (0x418#12) 40 (by decide) (by decide) hsp1088
  -- === op-token / left-payload window byte offsets ===
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
  obtain ⟨lb0, hlb0⟩ := hFullPop (aExpr.toNat + 4)
  obtain ⟨lb1, hlb1⟩ := hFullPop (aExpr.toNat + 4 + 1)
  obtain ⟨lb2, hlb2⟩ := hFullPop (aExpr.toNat + 4 + 2)
  obtain ⟨lb3, hlb3⟩ := hFullPop (aExpr.toNat + 4 + 3)
  -- === the FrameBundle at v2 = sp-1088 ===
  have hfb : FrameBundle c.σ.mem (sp - 1088#64) :=
    ⟨fun k => hFullPop k, hspsub ▸ (frameBaseGeom hSB).1, hspsub ▸ (frameBaseGeom hSB).2.1,
      hspsub ▸ (frameBaseGeom hSB).2.2.1, hspsub ▸ (frameBaseGeom hSB).2.2.2⟩
  -- ── entry linkage + dispatch: 0x8000351c → 0x8000381c (DivDispatchPost) ──────
  have hdisp :=
    evalDivChain_dispatch c.σ c.tick c.steps vmi (sp - 1088#64) aExpr sret Wl
      lb0 lb1 lb2 lb3 rkb0 rkb1 rkb2 rkb3
      rpb0 rpb1 rpb2 rpb3 rpb4 rpb5 rpb6 rpb7
      kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7
      hG hpc hmi hsp hx8c hs1 hX19 hcode hcVal hkVal
      (by rw [hop8]; first | exact gExpr8.1 | exact gExpr8.2.1 | exact gExpr8.2.2.1 | exact gExpr8.2.2.2) (by rw [hop8]; first | exact gExpr8.1 | exact gExpr8.2.1 | exact gExpr8.2.2.1 | exact gExpr8.2.2.2)
      (by rw [hop8]; first | exact gExpr8.1 | exact gExpr8.2.1 | exact gExpr8.2.2.1 | exact gExpr8.2.2.2) (by rw [hop8]; first | exact gExpr8.1 | exact gExpr8.2.1 | exact gExpr8.2.2.1 | exact gExpr8.2.2.2)
      (by rw [hop8]; exact hob0') (by rw [hop8]; exact hob1')
      (by rw [hop8]; exact hob2') (by rw [hop8]; exact hob3')
      (by rw [hline4]; first | exact gExpr4.1 | exact gExpr4.2.1 | exact gExpr4.2.2.1 | exact gExpr4.2.2.2) (by rw [hline4]; first | exact gExpr4.1 | exact gExpr4.2.1 | exact gExpr4.2.2.1 | exact gExpr4.2.2.2)
      (by rw [hline4]; first | exact gExpr4.1 | exact gExpr4.2.1 | exact gExpr4.2.2.1 | exact gExpr4.2.2.2) (by rw [hline4]; first | exact gExpr4.1 | exact gExpr4.2.1 | exact gExpr4.2.2.1 | exact gExpr4.2.2.2)
      (by rw [hline4]; exact hlb0) (by rw [hline4]; exact hlb1)
      (by rw [hline4]; exact hlb2) (by rw [hline4]; exact hlb3)
      (by rw [haddr944]; first | exact g944.lo | exact g944.hi4 | exact g944.hi8 | exact g944.ht4 | exact g944.ht8 | exact g944.win | exact g944.al4 | exact g944.al8) (by rw [haddr944]; first | exact g944.lo | exact g944.hi4 | exact g944.hi8 | exact g944.ht4 | exact g944.ht8 | exact g944.win | exact g944.al4 | exact g944.al8)
      (by rw [haddr944]; first | exact g944.lo | exact g944.hi4 | exact g944.hi8 | exact g944.ht4 | exact g944.ht8 | exact g944.win | exact g944.al4 | exact g944.al8) (by rw [haddr944]; first | exact g944.lo | exact g944.hi4 | exact g944.hi8 | exact g944.ht4 | exact g944.ht8 | exact g944.win | exact g944.al4 | exact g944.al8)
      (by rw [haddr944]; exact hrkb0) (by rw [haddr944]; exact hrkb1)
      (by rw [haddr944]; exact hrkb2) (by rw [haddr944]; exact hrkb3)
      (by rw [haddr936]; first | exact g936.lo | exact g936.hi4 | exact g936.hi8 | exact g936.ht4 | exact g936.ht8 | exact g936.win | exact g936.al4 | exact g936.al8) (by rw [haddr936]; first | exact g936.lo | exact g936.hi4 | exact g936.hi8 | exact g936.ht4 | exact g936.ht8 | exact g936.win | exact g936.al4 | exact g936.al8)
      (by rw [haddr936]; first | exact g936.lo | exact g936.hi4 | exact g936.hi8 | exact g936.ht4 | exact g936.ht8 | exact g936.win | exact g936.al4 | exact g936.al8) (by rw [haddr936]; first | exact g936.lo | exact g936.hi4 | exact g936.hi8 | exact g936.ht4 | exact g936.ht8 | exact g936.win | exact g936.al4 | exact g936.al8)
      (by rw [haddr936, hRpb.1]; exact hrpb0)
      (by rw [haddr936, hRpb.2.1]; exact hrpb1)
      (by rw [haddr936, hRpb.2.2.1]; exact hrpb2)
      (by rw [haddr936, hRpb.2.2.2.1]; exact hrpb3)
      (by rw [haddr936, hRpb.2.2.2.2.1]; exact hrpb4)
      (by rw [haddr936, hRpb.2.2.2.2.2.1]; exact hrpb5)
      (by rw [haddr936, hRpb.2.2.2.2.2.2.1]; exact hrpb6)
      (by rw [haddr936, hRpb.2.2.2.2.2.2.2]; exact hrpb7)
      hSlot
      (by rw [haddr0]; first | exact g1088.lo | exact g1088.hi4 | exact g1088.hi8 | exact g1088.ht4 | exact g1088.ht8 | exact g1088.win | exact g1088.al4 | exact g1088.al8) (by rw [haddr0]; first | exact g1088.lo | exact g1088.hi4 | exact g1088.hi8 | exact g1088.ht4 | exact g1088.ht8 | exact g1088.win | exact g1088.al4 | exact g1088.al8)
      (by rw [haddr0]; first | exact g1088.lo | exact g1088.hi4 | exact g1088.hi8 | exact g1088.ht4 | exact g1088.ht8 | exact g1088.win | exact g1088.al4 | exact g1088.al8) (by rw [haddr0]; first | exact g1088.lo | exact g1088.hi4 | exact g1088.hi8 | exact g1088.ht4 | exact g1088.ht8 | exact g1088.win | exact g1088.al4 | exact g1088.al8)
      (by rw [haddr0]; exact hkb0) (by rw [haddr0]; exact hkb1)
      (by rw [haddr0]; exact hkb2) (by rw [haddr0]; exact hkb3)
      (by rw [haddr0]; exact hkb4) (by rw [haddr0]; exact hkb5)
      (by rw [haddr0]; exact hkb6) (by rw [haddr0]; exact hkb7)
      htick hWrNe hfb
  obtain ⟨cD, ldsD, hStepsD, hDDP⟩ := hdisp
  simp only [hout0eq] at hDDP
  -- DivDispatchPost: cD parked at 0x8000381c, x10=Wl, x11=Wr, x9=sret, x2=v2, mem = mA
  obtain ⟨hGD, hmemD, hpcD, hx10D, hx11D, hx9D, hx2D, ⟨w12D, hx12D⟩, ⟨w13D, hx13D⟩,
    htickD, houtD, hframeD⟩ := hDDP
  -- cD's sailOutput = out0
  have houtD0 : cD.σ.sailOutput = out0 := houtD
  -- the dispatch memory frame: mA agrees with c.σ.mem outside [v2, v2+0x108) ⊂ [SL.lo, SL.hi)
  have hv2lo : (sp - 1088#64).toNat = sp.toNat - 1088 := hspsub
  have hframeA : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → cD.σ.mem[k]? = c.σ.mem[k]? := by
    intro k hk
    rw [hmemD]
    refine divDispatch_mem_frame (sp - 1088#64) sret (bytesVal MKind.ld [rpb0, rpb1, rpb2, rpb3, rpb4, rpb5, rpb6, rpb7] : BitVec 64) Wl ldsD c.σ.mem hfb k ?_
    rw [hv2lo]; omega
  -- everything survives onto cD.σ.mem = mA
  have hcodeA : Vsa.Sim.Code.Eval_exprLoaded cD.σ.mem :=
    loaded_eval_expr_agreeP c.σ.mem cD.σ.mem
      (fun k hk => (hframeA k (by rcases hcodeStk with h | h <;> omega)).symm) hcode
  have hVintA : Value_intLoaded cD.σ.mem :=
    loaded_value_int_agreeP c.σ.mem cD.σ.mem
      (fun k hk => (hframeA k (by rcases hviStk with h | h <;> omega)).symm) hVint
  have hDivdi3A : Vsa.Sim.Code.__divdi3Loaded cD.σ.mem :=
    loaded_divdi3_agreeP c.σ.mem cD.σ.mem
      (fun k hk => (hframeA k (by rcases hdivStk with h | h <;> omega)).symm) hDivdi3
  have hUmoddi3A : Vsa.Sim.Code.__umoddi3Loaded cD.σ.mem :=
    loaded_umoddi3_agreeP c.σ.mem cD.σ.mem
      (fun k hk => (hframeA k (by rcases hdivStk with h | h <;> omega)).symm) hUmoddi3
  have hUdivdi3A : __hidden___udivdi3Loaded cD.σ.mem :=
    loaded_udivdi3_agreeP c.σ.mem cD.σ.mem
      (fun k hk => (hframeA k (by rcases hdivStk with h | h <;> omega)).symm) hUdivdi3
  obtain ⟨vmiD, hmiD⟩ := hGD.minstret
  have hx10D' : cD.σ.regs.get? Register.x10 = some Wl := hx10D
  have hx11D' : cD.σ.regs.get? Register.x11 = some (bytesVal MKind.ld [rpb0, rpb1, rpb2, rpb3, rpb4, rpb5, rpb6, rpb7] : BitVec 64) := hx11D
  have hx9D' : cD.σ.regs.get? Register.x9 = some sret := hx9D
  have hx2D' : cD.σ.regs.get? Register.x2 = some (sp - 1088#64) := hx2D
  --------------------------------------------------------------------------------
  -- 0x8000381c: jal __divdi3 → x1 := 0x80003820, PC := 0x800046a4 (via divPreBridge)
  --------------------------------------------------------------------------------
  have hWr_toInt' : (bytesVal MKind.ld [rpb0, rpb1, rpb2, rpb3, rpb4, rpb5, rpb6, rpb7] : BitVec 64).toInt = b := hWr_toInt
  -- the `divdi3_pre` ghost is the __divdi3-entry snapshot; supply via divPreBridge
  obtain ⟨cP, hStepsP, hDivPre⟩ :=
    divPreBridge (fun R => cD.σ.regs.get? R) (fun R => c.σ.regs.get? R)
      (sp - 1088#64) sret (bytesVal MKind.ld [rpb0, rpb1, rpb2, rpb3, rpb4, rpb5, rpb6, rpb7] : BitVec 64) Wl ldsD
      c.σ.mem cD.σ.mem out0 hmemD hcodeA hDivdi3A hUmoddi3A hUdivdi3A
      (by rw [hWr_toInt']; exact hbNe)
      (by rw [hWl_toInt, hWr_toInt']; exact hOv)
      cD ⟨⟨hGD, hmemD, hpcD, hx10D, hx11D, hx9D, hx2D, ⟨w12D, hx12D⟩, ⟨w13D, hx13D⟩,
        htickD, houtD, hframeD⟩, fun R _ => rfl⟩
  -- divdi3_spec: from divdi3_pre run to divdi3_post (quotient in x10, mem=mA, out=out0, frame)
  obtain ⟨cQ, hStepsQ, hDivPost⟩ :=
    divdi3_spec (fun R => cD.σ.regs.get? R) Wl (bytesVal MKind.ld [rpb0, rpb1, rpb2, rpb3, rpb4, rpb5, rpb6, rpb7] : BitVec 64) (0x80003820#64) cD.σ.mem out0 cP hDivPre
  obtain ⟨hGQ, hmemQ, houtQ, hpcQ, htickQ, hframeQ, resQ, hx10Q, hresQ⟩ := hDivPost
  -- mem of cQ = mA = cD.σ.mem; recover the loaded/geometry facts on cQ
  have hmemQe : cQ.σ.mem = cD.σ.mem := hmemQ
  have hcodeQ : Eval_exprLoaded cQ.σ.mem := by rw [hmemQe]; exact hcodeA
  have hVintQ : Value_intLoaded cQ.σ.mem := by rw [hmemQe]; exact hVintA
  -- x9 (sret), x2 (v2) survive __divdi3 (callee-saved ∈ NotWrittenD)
  have hs1Q : cQ.σ.regs.get? Register.x9 = some sret := by
    rw [hframeQ Register.x9 ⟨by decide, by decide, by decide⟩]; exact hx9D
  have hspQ : cQ.σ.regs.get? Register.x2 = some (sp - 1088#64) := by
    rw [hframeQ Register.x2 ⟨by decide, by decide, by decide⟩]; exact hx2D
  obtain ⟨vmiQ, hmiQ⟩ := hGQ.minstret
  -- the value the value_int suffix must box: res, pinned by res.toInt = Wl.tdiv (bytesVal MKind.ld [rpb0, rpb1, rpb2, rpb3, rpb4, rpb5, rpb6, rpb7] : BitVec 64)
  have hresQ' : resQ.toInt = Wl.toInt.tdiv (bytesVal MKind.ld [rpb0, rpb1, rpb2, rpb3, rpb4, rpb5, rpb6, rpb7] : BitVec 64).toInt := hresQ
  --------------------------------------------------------------------------------
  -- 0x80003820: mv a1,a0 → x11 := resQ (the quotient)
  --------------------------------------------------------------------------------
  obtain ⟨τ1, j1, ht1, hj1, hGτ1, hmemτ1, hoτ1⟩ :=
    site_80003820_ee cQ.σ cQ.tick cQ.steps (0x80003820#64) vmiQ resQ
      hGQ hpcQ hmiQ hx10Q hcodeQ rfl htickQ
  have hstepτ1 : Step cQ ⟨τ1, j1, cQ.steps + 1⟩ := by cases cQ; exact ht1
  have hmemτ1e : τ1.mem = cD.σ.mem := by rw [hmemτ1]; exact hmemQe
  have hpcτ1 : τ1.regs.get? Register.PC = some (0x80003824#64) := by
    have := obs_alu_pc hoτ1
    rwa [show BitVec.addInt (0x80003820#64) 4 = (0x80003824#64 : BitVec 64) from by decide] at this
  have hx11τ1 : τ1.regs.get? Register.x11 = some resQ := by
    have := obs_alu_rd hoτ1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (resQ + sign_extend (m := 64) (0x000#12)) = resQ from by rw [sext_zero, BitVec.add_zero]] at this
  have hs1τ1 : τ1.regs.get? Register.x9 = some sret := obs_alu_other hoτ1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1Q
  have hspτ1 : τ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspQ
  obtain ⟨vmiτ1, hmiτ1⟩ := obs_alu_minstret hoτ1
  have houtτ1 : τ1.sailOutput = out0 := by rw [hoτ1.out, sailOutput_sigmaPost_alu]; exact houtQ
  have hcodeτ1 : Eval_exprLoaded τ1.mem := by rw [hmemτ1e]; exact hcodeA
  have hVintτ1 : Value_intLoaded τ1.mem := by rw [hmemτ1e]; exact hVintA
  --------------------------------------------------------------------------------
  -- 0x80003824: mv a0,s1 → x10 := sret
  --------------------------------------------------------------------------------
  obtain ⟨τ2, j2, ht2, hj2, hGτ2, hmemτ2, hoτ2⟩ :=
    site_80003824_ee τ1 j1 (cQ.steps + 1) (0x80003824#64) vmiτ1 sret
      hGτ1 hpcτ1 hmiτ1 hs1τ1 hcodeτ1 rfl hj1
  have hstepτ2 : Step ⟨τ1, j1, cQ.steps + 1⟩ ⟨τ2, j2, cQ.steps + 1 + 1⟩ := ht2
  have hmemτ2e : τ2.mem = cD.σ.mem := by rw [hmemτ2]; exact hmemτ1e
  have hpcτ2 : τ2.regs.get? Register.PC = some (0x80003828#64) := by
    have := obs_alu_pc hoτ2
    rwa [show BitVec.addInt (0x80003824#64) 4 = (0x80003828#64 : BitVec 64) from by decide] at this
  have hx10τ2 : τ2.regs.get? Register.x10 = some sret := by
    have := obs_alu_rd hoτ2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sret + sign_extend (m := 64) (0x000#12)) = sret from by rw [sext_zero, BitVec.add_zero]] at this
  have hx11τ2 : τ2.regs.get? Register.x11 = some resQ := obs_alu_other hoτ2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ1
  have hs1τ2 : τ2.regs.get? Register.x9 = some sret := obs_alu_other hoτ2 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ1
  have hspτ2 : τ2.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ1
  obtain ⟨vmiτ2, hmiτ2⟩ := obs_alu_minstret hoτ2
  have houtτ2 : τ2.sailOutput = out0 := by rw [hoτ2.out, sailOutput_sigmaPost_alu]; exact houtτ1
  have hcodeτ2 : Eval_exprLoaded τ2.mem := by rw [hmemτ2e]; exact hcodeA
  have hVintτ2 : Value_intLoaded τ2.mem := by rw [hmemτ2e]; exact hVintA
  --------------------------------------------------------------------------------
  -- 0x80003828: jal value_int → x1 := 0x8000382c, PC := 0x8000280c
  --------------------------------------------------------------------------------
  obtain ⟨τ3, j3, ht3, hj3, hGτ3, hmemτ3, hoτ3⟩ :=
    site_80003828_ee τ2 j2 (cQ.steps + 1 + 1) (0x80003828#64) vmiτ2
      hGτ2 hpcτ2 hmiτ2 hcodeτ2 rfl hj2
  have hstepτ3 : Step ⟨τ2, j2, cQ.steps + 1 + 1⟩ ⟨τ3, j3, cQ.steps + 1 + 1 + 1⟩ := ht3
  have hmemτ3e : τ3.mem = cD.σ.mem := by rw [hmemτ3]; exact hmemτ2e
  have hpcτ3 : τ3.regs.get? Register.PC = some (0x8000280c#64) := by
    have := obs_jal_pc hoτ3
    rwa [show ((0x80003828#64 : BitVec 64) + sign_extend (m := 64) (0x1fefe4#21)) = 0x8000280c#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hlinkτ3 : τ3.regs.get? Register.x1 = some (0x8000382c#64) := by
    have := obs_jal_rd hoτ3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80003828#64 : BitVec 64) 4 = (0x8000382c#64:BitVec 64) from by decide] at this
  have hx10τ3 : τ3.regs.get? Register.x10 = some sret := obs_jal_other hoτ3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10τ2
  have hx11τ3 : τ3.regs.get? Register.x11 = some resQ := obs_jal_other hoτ3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ2
  have hs1τ3 : τ3.regs.get? Register.x9 = some sret := obs_jal_other hoτ3 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ2
  have hspτ3 : τ3.regs.get? Register.x2 = some (sp - 1088#64) := obs_jal_other hoτ3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ2
  obtain ⟨vmiτ3, hmiτ3⟩ := obs_jal_minstret hoτ3
  have houtτ3 : τ3.sailOutput = out0 := by rw [hoτ3.out, sailOutput_sigmaPost_jal]; exact houtτ2
  have hVintτ3 : Value_intLoaded τ3.mem := by rw [hmemτ3e]; exact hVintA
  --------------------------------------------------------------------------------
  -- value_int callee (via value_int_spec): buf = sret, pay = resQ
  --------------------------------------------------------------------------------
  have hIntRegion : IntRegion sret := ⟨hsretAl, hsretLo, hsretHi, hsretWin, hsretVi⟩
  have hval_bridge : (BitVec.ofNat 64 resQ.toNat).toInt = wrap64 (a.tdiv b) :=
    div_wrap_bridge Wl (bytesVal MKind.ld [rpb0, rpb1, rpb2, rpb3, rpb4, rpb5, rpb6, rpb7] : BitVec 64) resQ a b hWl_toInt hWr_toInt' hresQ'
  -- ── Phase-4a: the whole `value_int ; ld s3 ; j` tail + `PreEpilogueVD` packaging
  --    is now the GENERATED `intBoxEpilogue` (`Vsa/Sim/BinopTailGen.lean`).  The `.div`
  --    front supplies `τ3` (the `jal value_int` entry) and its transport facts. ──
  -- s3 restore slot at τ3.mem = mA (agrees with c.σ.mem outside [v2,v2+0x108))
  have hframeA40 : ∀ k : Nat, ¬ (sp.toNat - 1088 ≤ k ∧ k < sp.toNat - 1088 + 0x108) →
      cD.σ.mem[k]? = c.σ.mem[k]? := by
    intro k hk
    rw [hmemD]
    refine divDispatch_mem_frame (sp - 1088#64) sret (bytesVal MKind.ld [rpb0, rpb1, rpb2, rpb3, rpb4, rpb5, rpb6, rpb7] : BitVec 64) Wl ldsD c.σ.mem hfb k ?_
    rw [hspsub]; exact hk
  have hs3D : read64 cD.σ.mem (sp.toNat - 40) = some w19.toNat := by
    rw [← read64_agreeP (P := fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat - 32)
      (a := sp.toNat - 40) (m := c.σ.mem) (m' := cD.σ.mem)
      (fun k hk => (hframeA40 k (notInDispWin_of_above hsp1088 hAbove40 hk.1)).symm)
      hAr.s3win]
    exact hs3slot
  have hs3τ3 : read64 τ3.mem (sp.toNat - 40) = some w19.toNat := by rw [hmemτ3e]; exact hs3D
  -- top spill slots at τ3.mem (agree with c.σ.mem, all above sp-824)
  have hAgTopD : AgreeP (fun k => sp.toNat - 32 ≤ k ∧ k < sp.toNat) c.σ.mem cD.σ.mem := by
    intro k hk
    exact (hframeA40 k (notInDispWin_of_above hsp1088 hAbove32 hk.1)).symm
  have hslotRaτ3 : read64 τ3.mem (sp.toNat - 8) = some r.toNat := by
    rw [hmemτ3e, ← read64_agreeP hAgTopD hTopW.1]; exact hslotRa
  have hslotS0τ3 : read64 τ3.mem (sp.toNat - 16) = some v8.toNat := by
    rw [hmemτ3e, ← read64_agreeP hAgTopD hTopW.2.1]; exact hslotS0
  have hslotS1τ3 : read64 τ3.mem (sp.toNat - 24) = some v9.toNat := by
    rw [hmemτ3e, ← read64_agreeP hAgTopD hTopW.2.2.1]; exact hslotS1
  have hslotS2τ3 : read64 τ3.mem (sp.toNat - 32) = some v18.toNat := by
    rw [hmemτ3e, ← read64_agreeP hAgTopD hTopW.2.2.2]; exact hslotS2
  -- store survival outside SL, phrased at τ3.mem = mA
  have hSLatτ3 : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = τ3.mem[k]? := by
    intro k hk; rw [hmemτ3e]; exact (hframeA k hk).symm
  have hSurvSLτ3 : ∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → τ3.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st''.store :=
    fun m' hm' => hstoreSurv' m' (fun k hk => (hSLatτ3 k hk).trans (hm' k hk))
  -- MemExtends m0 → τ3.mem
  have hMemExt_c_D : MemExtends c.σ.mem cD.σ.mem := by
    intro k bb hk; rw [hmemD]; exact pop_writeLog _ c.σ.mem (fun j => hFullPop j) k
  have hMemExtτ3 : MemExtends m0 τ3.mem := by
    rw [hmemτ3e]; exact hMemExt.trans hMemExt_c_D
  -- memory frame vs m0, at τ3.mem = mA
  have hmemframeτ3 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ τ3.mem[a]? = m0[a]? := by
    intro a ha hA
    refine Or.inr ?_
    rw [hmemτ3e]
    have haSL : a < SL.lo ∨ sp.toNat ≤ a := by
      rcases (Nat.lt_or_ge a SL.lo) with h | h
      · exact Or.inl h
      · rcases (Nat.lt_or_ge a sp.toNat) with h2 | h2
        · exact absurd ⟨h, h2⟩ ha
        · exact Or.inr h2
    have hmDc : cD.σ.mem[a]? = c.σ.mem[a]? := hframeA40 a (by rcases haSL with h | h <;> omega)
    rw [hmDc]; exact hmemframe a ha hA
  -- frame collapse τ3.regs → g for R ≠ x19 (through the divdi3/dispatch tail, to gpre → g)
  have hframeGτ3 : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      (Register.x19 == R) = false → τ3.regs.get? R = g R := by
    intro R hR he8 he9 he18 he2 h19ne
    obtain ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    have hR' : AbiPreservedNoise R := ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    have ne : ∀ {X : Register}, AbiPreserved X = false → (X == R) = false := by
      intro X hX
      rcases hXR : (X == R) with _ | _
      · rfl
      · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hab; exact absurd hab (by decide)
    have f_3 : τ3.regs.get? R = τ2.regs.get? R :=
      (hoτ3.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jal _ _ _ _ _ _ R hmi' hpc' (ne (X := Register.x1) (by decide)) hnpc' hmii')
    have f_2 : τ2.regs.get? R = τ1.regs.get? R :=
      (hoτ2.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (X := Register.x10) (by decide)) hnpc' hmii')
    have f_1 : τ1.regs.get? R = cQ.σ.regs.get? R :=
      (hoτ1.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (ne (X := Register.x11) (by decide)) hnpc' hmii')
    have fQ : cQ.σ.regs.get? R = cD.σ.regs.get? R :=
      hframeQ R ⟨⟨ne (X := Register.x10) (by decide), ne (X := Register.x11) (by decide),
          ne (X := Register.x12) (by decide), ne (X := Register.x13) (by decide),
          hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩,
        ne (X := Register.x1) (by decide), ne (X := Register.x5) (by decide)⟩
    have fD : cD.σ.regs.get? R = c.σ.regs.get? R := hframeD R hR' he8
    rw [f_3, f_2, f_1, fQ, fD]
    exact (hframe R hR' h19ne).trans (hbridge R hR' he8 he9 he18 he2)
  -- === invoke the GENERATED shared tail ===
  obtain ⟨mpre, φfm2, φcm2, φfe, φce, cfin, hStepsFin, hp1, hp2, hp3, hp4, hPreD⟩ :=
    intBoxEpilogue g N A SL φf φc φfm φcm φf' φc' nf nc st'.store.frames.size st'.store.closures.size st' st''
      sp r sret v8 v9 v18 v19 w19 resQ (wrap64 (a.tdiv b)) out0 m0
      ⟨τ3, j3, cQ.steps + 1 + 1 + 1⟩ (0x8000382c#64) (0x8000382c#64) (0x80003830#64) (0x1ffbbc#21)
      (fun σ i u pc vminstret v2 b0 b1 b2 b3 b4 b5 b6 b7 => site_8000382c_ee σ i u pc vminstret v2 b0 b1 b2 b3 b4 b5 b6 b7)
      (fun σ i u pc vminstret => site_80003830_ee σ i u pc vminstret)
      rfl (by apply BitVec.eq_of_toNat_eq; decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by decide)
      haddr1048
      hGτ3 hVintτ3 hpcτ3 hx10τ3 hx11τ3 hlinkτ3 hs1τ3 hspτ3 ⟨vmiτ3, hmiτ3⟩ hj3 houtτ3
      (by rw [hmemτ3e]; exact hcodeA) hIntRegion (by decide) hval_bridge
      hpfm hpcm hpf' hpc' houtStr
      hSurvSLτ3 hs3τ3 hslotRaτ3 hslotS0τ3 hslotS1τ3 hslotS2τ3
      hgv8 hgv9 hgv18 hgv2 hgx19 hw19 hframeGτ3 hMemExtτ3 hmemframeτ3
      hsretEvalCode hsretStk hsretInSL hSLlo40 hSLlo32
      hsp1088 hsphiRam hspLoc hspHtifLoc hsp8 hraAl
      g40.lo g40.hi8 g40.ht8 g40.al8
  have hchain : Steps c cfin :=
    (hStepsD.trans <| hStepsP.trans <| hStepsQ.trans <|
      (Steps.single hstepτ1).trans <| (Steps.single hstepτ2).trans <|
      (Steps.single hstepτ3)).trans hStepsFin
  exact ⟨cfin, hchain, mpre, φfm2, φcm2, φfe, φce, hp1, hp2, hp3, hp4, hPreD⟩

/-! ## `DivResid` — the blockC_div residuals about the POST-`TwoSubReturn` config -/

structure DivResid
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (sp r sret aExpr : BitVec 64) (Wl : BitVec 64) (c' : Vsa.Machine.Config) : Prop where
  gx8 : gpre Register.x8 = some aExpr
  opTok : read32 c'.σ.mem (aExpr.toNat + 8) = some 14
  slot : DivSlotPinned c'.σ.mem
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
  divdi3 : Vsa.Sim.Code.__divdi3Loaded c'.σ.mem
  umoddi3 : Vsa.Sim.Code.__umoddi3Loaded c'.σ.mem
  udivdi3 : __hidden___udivdi3Loaded c'.σ.mem
  divStk : sp.toNat ≤ 0x800046a4 ∨ 0x80004728 ≤ SL.lo
  codeStk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  viStk : sp.toNat ≤ 0x8000280c ∨ 0x8000281c ≤ SL.lo
  tableStk : opTableBase + 20 ≤ SL.lo ∨ sp.toNat ≤ opTableBase
  sretInSL : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi
  SLloSp : SL.lo + 1088 ≤ sp.toNat
  SLlo : 0x80000000 ≤ SL.lo
  SLwin : tohostAddr + 16 ≤ SL.lo
  sphiRam : sp.toNat ≤ 0x100000000
  sp8 : sp.toNat % 8 = 0
  SLhiRam : SL.hi ≤ 0x100000000
  spSLhi : sp.toNat ≤ SL.hi

/-! ## `evalDivSim` — the `EvalE.binary .div` int recursive case -/

def EvalDivSimGoal : Prop :=
  ∀ (gouter gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (a b : Int)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 Wl : BitVec 64)
    (out0 : Array String) (m0 : Mem),
    b ≠ 0 →
    ¬(a = -2^63 ∧ b = -1) →
    EvalIH st d env el st' (.int a) →
    EvalIH st' d env er st'' (.int b) →
    EvalE st d env (.binary .div el er) st'' (.int (wrap64 (a.tdiv b))) →
    st'.store.frames.size = st''.store.frames.size →
    st'.store.closures.size = st''.store.closures.size →
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary .div el er)
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
        (∀ c' : Vsa.Machine.Config,
          TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
            st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c' →
          DivResid gpre N A SL sp r sret aExpr Wl c') ∧
        g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
        g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧ g Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x2 == R) = false →
          gpre R = g R))
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st'' (.int (wrap64 (a.tdiv b))) sp r sret m0)

/-- **`evalDivSim`**: the `EvalE.binary .div` (int) recursive case, composing
`blockB_binary ≫ blockC_div ≫ blockD_v_rec` in the `EvalIH` motive shape.  Caller
obligations `b ≠ 0` (value-path; `b = 0` is the M5 error case) and no-overflow
`¬(a = INT64_MIN ∧ b = -1)` are carried into the goal. -/
theorem evalDivSim : EvalDivSimGoal := by
  intro gouter gpre g N A SL φf φc st st' st'' d env el er a b
    sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 Wl out0 m0 hbNe hOv hIHl hIHr _hEvalE hSizeF hSizeC
  intro c hpre
  obtain ⟨ment, hArm, hBE, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
    hpayL, hexprL, hpayR, hexprR, hMentPop, hMemExtM0,
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
    blockB_binary gouter gpre N A SL φf φc st st' st'' d env .div el er (.int a) (.int b)
      sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0 hIHl hIHr hVlSurv
      c ⟨ment, hArm, hBE, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
        hpayL, hexprL, hpayR, hexprR, hMentPop, hMemExtM0,
        hstackBudgetL, hexprBodiesL, hstoreBodiesL,
        hstackBudgetR, hexprBodiesR, hstoreBodiesR⟩
  have hR : DivResid gpre N A SL sp r sret aExpr Wl c2 := hResid c2 hTS
  have hOutC2 : String.join c2.σ.sailOutput.toList = st''.out := hTS.2.2.2.2.2.2.2.1
  -- === block C: dispatch + __divdi3 tail → PreEpilogueVD @0x800033ec ===
  obtain ⟨c3, hs3, mpre, φfm, φcm, φfe, φce, hpfm, hpcm, hpfe, hpce, hPreD⟩ :=
    blockC_div gpre g N A SL φf φc st.store.frames.size st.store.closures.size
      st' st'' a b sp r sret aExpr v8 v9 v18 v19 Wl c2.σ.sailOutput m0
      hbNe hOv
      c2 ⟨hTS, hR.gx8, hR.opTok, hR.slot, hR.fullpop, hR.x19, hR.wlbuf, hR.kindresp,
        hR.exprAl, hR.exprLo, hR.exprHi, hR.exprWin, hR.exprSL, hOutC2, rfl,
        hR.sretAl, hR.sretLo, hR.sretHi, hR.sretWin, hR.sretVi, hR.sretStk, hR.sretEvalCode, hR.raAl,
        hR.vint, hR.divdi3, hR.umoddi3, hR.udivdi3, hR.divStk, hR.codeStk, hR.viStk, hR.tableStk, hR.sretInSL,
        hR.SLloSp, hR.SLlo, hR.SLwin, hR.sphiRam, hR.sp8, hR.SLhiRam, hR.spSLhi,
        hgv8, hgv9, hgv18, hgv2, hgx19, hgvx19, hbridge⟩
  -- === block D: shared epilogue → EvalExitD ===
  obtain ⟨c4, hs4, hExitDe⟩ :=
    blockD_v_rec g N A SL φfe φce st'' (.int (wrap64 (a.tdiv b))) sp r sret v8 v9 v18 c2.σ.sailOutput m0
      c3 ⟨mpre, hPreD⟩
  obtain ⟨hExitE, hMemExt, φf', φc', hpf', hpc', hSurv⟩ := hExitDe
  have hmono := evalE_store_mono _hEvalE
  have hleF' : st.store.frames.size ≤ st'.store.frames.size := hSizeF ▸ hmono.1
  have hleC' : st.store.closures.size ≤ st'.store.closures.size := hSizeC ▸ hmono.2
  have hpfF : PhiExtends φf φfe st.store.frames.size := hpfm.trans (PhiExtends.mono hleF' hpfe)
  have hpcF : PhiExtends φc φce st.store.closures.size := hpcm.trans (PhiExtends.mono hleC' hpce)
  have hExit : EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st'' (.int (wrap64 (a.tdiv b))) sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfF hpcF hExitE hmono.1 hmono.2
  exact ⟨c4, ((hs2.trans hs3).trans hs4), hExit, hMemExt,
    φf', φc', hpfF.trans (PhiExtends.mono hmono.1 hpf'),
    hpcF.trans (PhiExtends.mono hmono.2 hpc'), hSurv⟩

end Vsa.Sim
