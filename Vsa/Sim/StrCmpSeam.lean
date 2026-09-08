import Vsa.Sim.rows.StrArmChain
import Vsa.Sim.BridgeSegOut
import Vsa.Sim.SegToTripleFramed
import Vsa.Sim.StrCmpSeamSites
import Vsa.Sim.StaticImageSupport
import Vsa.Sim.Code.FixedImage_Strcmp
import Vsa.Sim.Code.FixedImage_Eval_expr
import Vsa.Sim.EvalChildArm
import Vsa.Sim.ReprSurvival
import Vsa.Sim.EnvGetSpec9
import Vsa.Sim.BlockTactics2
import Vsa.Sim.PinW
import Vsa.Sim.FixedOperatorTable

/-!
# `StrCmpSeam` — the string-comparison arm from its kind check to the sign tail

The four string-comparison cells of `eval_binary_row` (`<`, `≤`, `>`, `≥` on two
string operands) share ONE machine middle: after the operator dispatch lands the
comparison arm at `0x80003628` with both operand kinds equal to `3`, the arm runs

```
80003628  kind check (both str)           →  80003b0c      strKindCheck  (landed)
80003b0c  mv a1,a7 ; mv a0,s3 ; sd a2,0(sp) ; jal strcmp     strSeamSeg + site_80003b18_sc
80006ea0  strcmp                          →  80003b1c      strcmp_full_spec (landed)
80003b1c  ld a2,0(sp) ; mv a1,a0 ; j 0x800036a4              strRejoin     (landed)
```

and parks at the operator sign-test tail entry `0x800036a4` with the `strcmp`
result in `a1`, the operator token reloaded into `a2`, and the result buffer in
`s1`.  Only the sign tail after this point depends on the operator.

This file states that middle ONCE (`strCmpTailReady_of_kindEntry`) over named
entry/exit records.  The geometry it needs about the two operand strings is the
named record `StrCmpSeamGeom`; the exit record `StrCmpTailReady` carries the
`strcmp` sign fact in the form every sign tail consumes (through the proved
`StrCmpOrderBridge`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

/-! ## The seam seg `0x80003b0c → jal strcmp` -/

/-! `mv a1,a7 ; mv a0,s3 ; sd a2,0(sp)`: stage the two operand pointers as the
`strcmp` arguments and spill the operator token below the call. -/
#derive_case strSeamSeg chain
  [(0x80003b0c#64, 0x00088593#32),                -- mv x11,x17  -- discipline: allow(R13-strcmp-cell) this file DEFINES the layer's seam seg
   (0x80003b10#64, 0x00098513#32),                -- mv x10,x19
   (0x80003b14#64, 0x00c13023#32)]                -- sd x12,0(x2)

/-- The seam pin list: frame base, right pointer, left pointer, operator token. -/
def strSeamL (sp' pl pr tok : BitVec 64) : GRegs := [(2, sp'), (17, pr), (19, pl), (12, tok)]

/-- The seam's only memory obligation is the token spill at `sp'`. -/
theorem strSeam_facts (σ : MState) (sp' pl pr tok : BitVec 64) (lds : List (List (BitVec 8)))
    (h : Eval_exprLoaded σ.mem)
    (hlo : 0x80000000 ≤ sp'.toNat) (hhi : sp'.toNat + 8 ≤ 0x100000000)
    (hwin : tohostAddr + 16 ≤ sp'.toNat) (hal : sp'.toNat % 8 = 0) :
    ChainFacts σ.mem σ.mem (strSeamL sp' pl pr tok) lds strSeamSeg := by
  chain_facts h with "Vsa.Sim.Code.eval_expr_at_"
  · have e : (sp' + sign_extend (m := 64) (0x000#12)) = sp' := by
      rw [sext_zero, BitVec.add_zero]
    change 0x80000000 ≤ (sp' + sign_extend (m := 64) (0x000#12)).toNat ∧
      (sp' + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (sp' + sign_extend (m := 64) (0x000#12)).toNat ∧
      (sp' + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0
    rw [e]
    exact ⟨hlo, hhi, hwin, hal⟩

/-- The seam's write log is the one token spill. -/
theorem strSeam_log (m : Mem) (sp' pl pr tok : BitVec 64) (lds : List (List (BitVec 8))) :
    writeLog m (evalBlocks strSeamSeg (SegEvalState.init (strSeamL sp' pl pr tok) lds)).log =
      writeMap8 m (sp' + sign_extend (m := 64) (0x000#12)).toNat (sdData_val tok) := rfl

/-- The seam parks at the `jal`. -/
theorem strSeam_end (sp' pl pr tok : BitVec 64) (lds : List (List (BitVec 8))) :
    evalBlocksPC 0x80003b0c#64 (SegEvalState.init (strSeamL sp' pl pr tok) lds) strSeamSeg =
      0x80003b18#64 := by
  show chainEndPC 0x80003b0c#64 (strSeamL sp' pl pr tok) lds strSeamSeg = _
  rw [chainEndPC_eq_bt strSeamSeg _ _ _ (by decide)]
  rfl

/-! ## The rejoin readback of the reloaded token -/

/-- The rejoin's `ld x12,0(x2)` reads back the spilled word. -/
theorem strRejoin_x12 (sp x sret : BitVec 64) (lds : List (List (BitVec 8))) :
    lookupG 12 (evalBlocks strRejoin (SegEvalState.init (strRejoinL sp x sret) lds)).regs
      = some (bytesVal MKind.ld (lds.headD [])) := by
  rw [evalBlocks_regs]
  show lookupG 12 (runChain strRejoin (strRejoinL sp x sret) lds) = _
  simp only [strRejoin, runChain, runGM, stepGM, wvalM, srcVal, lookupG, eraseG,
    strRejoinL,
    show (mkLine 0x80003b1c#64 0x00013603#32).kind = MKind.ld from rfl,
    show (mkLine 0x80003b20#64 0x00050593#32).kind = MKind.addi from rfl,
    show (mkLine 0x80003b20#64 0x00050593#32).rd = 11 from rfl,
    show (mkLine 0x80003b20#64 0x00050593#32).rs1 = 10 from rfl,
    show (mkLine 0x80003b1c#64 0x00013603#32).rd = 12 from rfl,
    Nat.reduceEqDiff, if_true, if_false, Option.getD_some]

/-! ## Static image transport across the token spill -/

/-- A spill inside the stack leaves the fixed image alone. -/
theorem StaticImageSupport.writeMap8 {m : Mem} {SL : StackLayout} {A : Arena}
    (h : StaticImageSupport m SL A) (a : Nat) (d : BitVec (8 * 8))
    (hlo : SL.lo ≤ a) (hhi : a + 8 ≤ SL.hi) :
    StaticImageSupport (writeMap8 m a d) SL A :=
  h.transport (fun k hk => getElem_writeMap8_disjoint m a k d (by
    obtain ⟨hk1, hk2⟩ := hk
    rcases h.stack with hs | hs
    · right; omega
    · left; omega))

/-- The `strcmp` word mask lives in the fixed read-only image. -/
theorem FixedRodataLoaded.maskPinned {m : Mem} (h : FixedRodataLoaded m) : MaskPinned m := by
  have s0 := FixedRodataLoaded.slotPinned h 0x8001ac80#64 (by decide) (by decide)
  have s1 := FixedRodataLoaded.slotPinned h 0x8001ac84#64 (by decide) (by decide)
  exact ⟨s0.1, s0.2.1, s0.2.2.1, s0.2.2.2, s1.1, s1.2.1, s1.2.2.1, s1.2.2.2⟩

/-! ## Entry, geometry, and exit records -/

/-- The comparison arm at its kind check, after the shared operator dispatch:
both kind tags are `3`, the right pointer is in `a7`, the left pointer in `s3`,
the token in `a2`, the frame base in `sp`, the result buffer in `s1`. -/
structure StrCmpKindEntry
    (gC : (R : Register) → Option (RegisterType R))
    (sp' pl pr tok sret : BitVec 64) (mA : Mem) (out : Array String)
    (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some 0x80003628#64
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  mem : c.σ.mem = mA
  out : c.σ.sailOutput = out
  rKind : c.σ.regs.get? Register.x10 = some 3#64
  lKind : c.σ.regs.get? Register.x16 = some 3#64
  rPtr : c.σ.regs.get? Register.x17 = some pr
  lPtr : c.σ.regs.get? Register.x19 = some pl
  tok : c.σ.regs.get? Register.x12 = some tok
  sp : c.σ.regs.get? Register.x2 = some sp'
  sret : c.σ.regs.get? Register.x9 = some sret
  frame : ∀ R, AbiPreservedNoise R → (Register.x8 == R) = false →
    (Register.x19 == R) = false → c.σ.regs.get? R = gC R

/-- What `strcmp` needs of one operand payload: the landed byte- and word-path
regions, and separation from the token spill slot `[sp', sp'+8)`. -/
structure StrCmpRegion (sp' p : BitVec 64) (len : Nat) : Prop where
  byteRegion : StrcmpRegion p len
  wordRegion : StrcmpWRegion p len
  offScratch : p.toNat + len + 1 ≤ sp'.toNat ∨ sp'.toNat + 8 ≤ p.toNat

/-- Geometry of the seam at the kind-check memory `mA`: the fixed image, the
spill slot inside the stack, and both operand strings with their regions. -/
structure StrCmpSeamGeom (SL : StackLayout) (A : Arena)
    (sp' pl pr : BitVec 64) (sl sr : String) (mA : Mem) : Prop where
  image : StaticImageSupport mA SL A
  spLo : SL.lo ≤ sp'.toNat
  spHi : sp'.toNat + 8 ≤ SL.hi
  spRam : 0x80000000 ≤ sp'.toNat
  spRamHi : sp'.toNat + 8 ≤ 0x100000000
  spWin : tohostAddr + 16 ≤ sp'.toNat
  sp8 : sp'.toNat % 8 = 0
  left : CString mA pl.toNat sl
  right : CString mA pr.toNat sr
  leftRegion : ∀ cs, CStr mA pl.toNat cs → StrCmpRegion sp' pl cs.length
  rightRegion : ∀ cs, CStr mA pr.toNat cs → StrCmpRegion sp' pr cs.length

/-- Parked at the sign-tail entry `0x800036a4`: the `strcmp` result word in
`a1` (tied to the operand strings through any proved order bridge), the token
back in `a2`, the result buffer in `s1`, the frame base in `sp`, memory the
kind-check memory with the token spilled. -/
structure StrCmpTailReady
    (gC : (R : Register) → Option (RegisterType R))
    (sp' tok sret : BitVec 64) (sl sr : String) (mB : Mem) (out : Array String)
    (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some 0x800036a4#64
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  mem : c.σ.mem = mB
  out : c.σ.sailOutput = out
  sign : ∃ x, c.σ.regs.get? Register.x11 = some x ∧
    ∀ (op : BinOp) (bres : String → String → Bool), StrCmpOrderBridge op bres →
      (sTailWord op x != 0#64) = bres sl sr
  tok : c.σ.regs.get? Register.x12 = some tok
  sret : c.σ.regs.get? Register.x9 = some sret
  sp : c.σ.regs.get? Register.x2 = some sp'
  frame : ∀ R, AbiPreservedNoise R → (Register.x8 == R) = false →
    (Register.x19 == R) = false → c.σ.regs.get? R = gC R

/-- The memory after the seam: the kind-check memory with the token spilled. -/
def strCmpSeamMem (mA : Mem) (sp' tok : BitVec 64) : Mem :=
  writeMap8 mA sp'.toNat tok

/-- The spill leaves every byte outside its slot alone. -/
theorem strCmpSeamMem_agree (mA : Mem) (sp' tok : BitVec 64) (k : Nat)
    (hk : ¬ (sp'.toNat ≤ k ∧ k < sp'.toNat + 8)) :
    (strCmpSeamMem mA sp' tok)[k]? = mA[k]? :=
  getElem_writeMap8_disjoint mA sp'.toNat k tok (by omega)

/-! ## The parked seam entry (after the kind check) -/

/-- Parked at `0x80003b0c` with the seam's registers. -/
structure StrCmpSeamEntry
    (gC : (R : Register) → Option (RegisterType R))
    (sp' pl pr tok sret : BitVec 64) (mA : Mem) (out : Array String)
    (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some 0x80003b0c#64
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  mem : c.σ.mem = mA
  out : c.σ.sailOutput = out
  rPtr : c.σ.regs.get? Register.x17 = some pr
  lPtr : c.σ.regs.get? Register.x19 = some pl
  tok : c.σ.regs.get? Register.x12 = some tok
  sp : c.σ.regs.get? Register.x2 = some sp'
  sret : c.σ.regs.get? Register.x9 = some sret
  frame : ∀ R, AbiPreservedNoise R → (Register.x8 == R) = false →
    (Register.x19 == R) = false → c.σ.regs.get? R = gC R

/-- The landed kind-check seg from the kind entry, keeping the seam registers. -/
theorem strCmpSeamEntry_of_kindEntry
    {gC : (R : Register) → Option (RegisterType R)}
    {sp' pl pr tok sret : BitVec 64} {mA : Mem} {out : Array String} {c : Config}
    (h : StrCmpKindEntry gC sp' pl pr tok sret mA out c)
    (hcode : Eval_exprLoaded mA) :
    ∃ c', Steps c c' ∧ StrCmpSeamEntry gC sp' pl pr tok sret mA out c' := by
  obtain ⟨vm, hvm⟩ := h.minstret
  have hL : GHolds c.σ strKindL := by
    simp only [strKindL, GHolds, gprGet]
    exact ⟨h.rKind, h.lKind, True.intro⟩
  have hcodeC : Eval_exprLoaded c.σ.mem := by rw [h.mem]; exact hcode
  obtain ⟨σ', i', hs, hi', hG', hmem', hout', hpc', hmi', _hregs, hframe⟩ :=
    segEval_sound strKindCheck c.σ c.tick c.steps 0x80003628#64 vm strKindL []
      h.good h.pc hvm hL (by decide) (strKindCheck_facts c.σ [] hcodeC)
      (by show ChainOK 0x80003628#64 [10, 16] strKindCheck; decide) h.tick
  have hfr : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ n ∈ wrChain strKindCheck, (gprReg n == R) = false) →
      σ'.regs.get? R = c.σ.regs.get? R := hframe
  refine ⟨⟨σ', i', c.steps + evalBlocksFuel strKindCheck⟩, hs, ?_⟩
  exact
    { good := hG'
      tick := hi'
      pc := by
        rw [hpc']
        show some (chainEndPC 0x80003628#64 strKindL [] strKindCheck) = some 0x80003b0c#64
        rw [chainEndPC_eq_bt strKindCheck 0x80003628#64 strKindL [] (by decide)]
        rfl
      minstret := hmi'
      mem := by rw [hmem', h.mem]; rfl
      out := hout'.trans h.out
      rPtr := (hfr Register.x17 (by decide) (by decide)).trans h.rPtr
      lPtr := (hfr Register.x19 (by decide) (by decide)).trans h.lPtr
      tok := (hfr Register.x12 (by decide) (by decide)).trans h.tok
      sp := (hfr Register.x2 (by decide) (by decide)).trans h.sp
      sret := (hfr Register.x9 (by decide) (by decide)).trans h.sret
      frame := fun R hR h8 h19 => by
        have hab := hR.1
        exact (hfr R (abiNoise_noiseRegs hR) (by block_frame_wr [15, 15])).trans
          (h.frame R hR h8 h19) }

/-! ## The seam: `jal strcmp` ≫ `strcmp` ≫ rejoin -/

/-- From the parked seam entry, call `strcmp`, run the rejoin, and park at the
sign-tail entry with the result tied to the operand strings. -/
theorem strCmpTailReady_of_seamEntry
    {gC : (R : Register) → Option (RegisterType R)}
    {SL : StackLayout} {A : Arena}
    {sp' pl pr tok sret : BitVec 64} {sl sr : String} {mA : Mem} {out : Array String}
    {c : Config}
    (h : StrCmpSeamEntry gC sp' pl pr tok sret mA out c)
    (G : StrCmpSeamGeom SL A sp' pl pr sl sr mA) :
    ∃ c', Steps c c' ∧ StrCmpTailReady gC sp' tok sret sl sr (strCmpSeamMem mA sp' tok) out c' := by
  -- geometry at the two memories
  have hcodeA : Eval_exprLoaded mA := G.image.text.Eval_exprLoaded
  have himageB : StaticImageSupport (strCmpSeamMem mA sp' tok) SL A :=
    G.image.writeMap8 sp'.toNat tok G.spLo G.spHi
  have hcodeB : Eval_exprLoaded (strCmpSeamMem mA sp' tok) := himageB.text.Eval_exprLoaded
  have hlogB : writeLog mA
      (evalBlocks strSeamSeg (SegEvalState.init (strSeamL sp' pl pr tok) [])).log =
      strCmpSeamMem mA sp' tok := by
    rw [strSeam_log, sext_zero, BitVec.add_zero, sdData_val_id]
    rfl
  obtain ⟨vm, hvm⟩ := h.minstret
  have hL : GHolds c.σ (strSeamL sp' pl pr tok) := by
    simp only [strSeamL, GHolds, gprGet]
    exact ⟨h.sp, h.rPtr, h.lPtr, h.tok, True.intro⟩
  have hcodeC : Eval_exprLoaded c.σ.mem := by rw [h.mem]; exact hcodeA
  -- (1) the seam prefix and the `jal strcmp`
  obtain ⟨σ2, i2, hs2, hi2, hG2, hpc2, hra2, hmi2, hregs2, hmem2, hout2, hframe2⟩ :=
    bridgeOfSegOut strSeamSeg (strSeamL sp' pl pr tok) [] c.σ c.tick c.steps
      0x80003b0c#64 0x80006ea0#64 0x80003b1c#64 vm mA
      h.good h.pc hvm h.mem hL (by change KeysOK [2, 17, 19, 12]; decide)
      (strSeam_facts c.σ sp' pl pr tok [] hcodeC G.spRam G.spRamHi G.spWin G.sp8)
      h.tick (by show ChainOK 0x80003b0c#64 [2, 17, 19, 12] strSeamSeg; decide) (by decide)
      (by change KeysOK [10, 11, 2, 17, 19, 12]; decide)
      (by change ∀ n ∈ [10, 11, 2, 17, 19, 12], n ≠ 1; decide)
      (by
        intro σ' i' u' hG' hi' hpc' hmi' hm' _hregs'
        obtain ⟨vm', hvm'⟩ := hmi'
        rw [strSeam_end] at hpc'
        have hc' : Eval_exprLoaded σ'.mem := by rw [hm', hlogB]; exact hcodeB
        obtain ⟨σ'', i'', hs'', hi'', hG'', hm'', ho''⟩ :=
          site_80003b18_sc σ' i' u' 0x80003b18#64 vm' hG' hpc' hvm' hc' rfl hi'
        exact jalStepO_of_obs hs'' hi'' hG'' hm'' ho''
          (by apply BitVec.eq_of_toNat_eq; decide))
  have hmemB : σ2.mem = strCmpSeamMem mA sp' tok := by rw [hmem2, hlogB]
  have hx10 : σ2.regs.get? Register.x10 = some pl := by
    have := gholds_lookup (n := 10) (v := pl + sign_extend (m := 64) (0x000#12)) _ hregs2 (by rfl)
    rw [sext_zero, BitVec.add_zero] at this
    exact this
  have hx11 : σ2.regs.get? Register.x11 = some pr := by
    have := gholds_lookup (n := 11) (v := pr + sign_extend (m := 64) (0x000#12)) _ hregs2 (by rfl)
    rw [sext_zero, BitVec.add_zero] at this
    exact this
  -- (2) the operand strings survive the token spill
  obtain ⟨csa, hcsaA, hsa⟩ := G.left
  obtain ⟨csb, hcsbA, hsb⟩ := G.right
  have hRegA := G.leftRegion csa hcsaA
  have hRegB := G.rightRegion csb hcsbA
  have hAgA : AgreeP (fun k => pl.toNat ≤ k ∧ k ≤ pl.toNat + csa.length)
      mA (strCmpSeamMem mA sp' tok) := by
    intro k hk
    exact (strCmpSeamMem_agree mA sp' tok k
      (by rcases hRegA.offScratch with h1 | h1 <;> omega)).symm
  have hAgB : AgreeP (fun k => pr.toNat ≤ k ∧ k ≤ pr.toNat + csb.length)
      mA (strCmpSeamMem mA sp' tok) := by
    intro k hk
    exact (strCmpSeamMem_agree mA sp' tok k
      (by rcases hRegB.offScratch with h1 | h1 <;> omega)).symm
  have hcsaB : CStr (strCmpSeamMem mA sp' tok) pl.toNat csa :=
    cstr_agreeP hAgA hcsaA (fun k hk => ⟨by omega, by omega⟩)
  have hcsbB : CStr (strCmpSeamMem mA sp' tok) pr.toNat csb :=
    cstr_agreeP hAgB hcsbA (fun k hk => ⟨by omega, by omega⟩)
  -- (3) `strcmp`
  let cfg2 : Config := ⟨σ2, i2, c.steps + evalBlocksFuel strSeamSeg + 1⟩
  have hStrcmp2 : StrcmpLoaded σ2.mem := by rw [hmemB]; exact himageB.text.StrcmpLoaded
  have hMask2 : MaskPinned (strCmpSeamMem mA sp' tok) := FixedRodataLoaded.maskPinned himageB.rodata
  have hpre : strcmp_full_pre (fun R => σ2.regs.get? R) pl pr 0x80003b1c#64 sl sr
      (strCmpSeamMem mA sp' tok) out cfg2 := by
    refine ⟨hG2, hStrcmp2, hmemB, hout2.trans h.out, hpc2, hx10, hx11, hra2,
      hmi2, hi2, by decide, ⟨csa, hcsaB, hsa⟩, ⟨csb, hcsbB, hsb⟩, hMask2,
      ?_, ?_, ?_, ?_, fun R _ => rfl⟩
    · intro cs hcs
      rw [cstr_unique_eg9 _ _ cs csa hcs hcsaB]
      exact hRegA.byteRegion
    · intro cs hcs
      rw [cstr_unique_eg9 _ _ cs csb hcs hcsbB]
      exact hRegB.byteRegion
    · intro cs hcs
      rw [cstr_unique_eg9 _ _ cs csa hcs hcsaB]
      exact hRegA.wordRegion
    · intro cs hcs
      rw [cstr_unique_eg9 _ _ cs csb hcs hcsbB]
      exact hRegB.wordRegion
  obtain ⟨c3, hs3, hpost⟩ :=
    strcmp_full_spec (fun R => σ2.regs.get? R) pl pr 0x80003b1c#64 sl sr
      (strCmpSeamMem mA sp' tok) out cfg2 hpre
  obtain ⟨hG3, hpc3, _hra3, hmem3, hout3, htick3, hframe3,
    csa', csb', x, hcsa', hcsb', hsa', hsb', hx10_3, hsign⟩ := hpost
  -- (4) the rejoin `ld a2,0(sp) ; mv a1,a0 ; j 0x800036a4`
  have hx2_3 : c3.σ.regs.get? Register.x2 = some sp' := by
    rw [hframe3 Register.x2 (by decide)]
    exact (hframe2 Register.x2 (by decide)).trans h.sp
  have hx9_3 : c3.σ.regs.get? Register.x9 = some sret := by
    rw [hframe3 Register.x9 (by decide)]
    exact (hframe2 Register.x9 (by decide)).trans h.sret
  obtain ⟨vm3, hvm3⟩ := hG3.minstret
  have hLR : GHolds c3.σ (strRejoinL sp' x sret) := by
    simp only [strRejoinL, GHolds, gprGet]
    exact ⟨hx2_3, hx10_3, hx9_3, True.intro⟩
  have e0 : (sp' + sign_extend (m := 64) (0x000#12)) = sp' := by
    rw [sext_zero, BitVec.add_zero]
  have hfactsR : ChainFacts c3.σ.mem c3.σ.mem (strRejoinL sp' x sret)
      [EvalChildArm.wordLds8 (strCmpSeamMem mA sp' tok) sp'.toNat] strRejoin := by
    rw [hmem3]
    chain_facts hcodeB with "Vsa.Sim.Code.eval_expr_at_"
    · change ((0x80000000 ≤ (sp' + sign_extend (m := 64) (0x000#12)).toNat ∧
        (sp' + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000 ∧
        ((sp' + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr ∨
          tohostAddr + 8 ≤ (sp' + sign_extend (m := 64) (0x000#12)).toNat)) ∧
        LPins8 (strCmpSeamMem mA sp' tok) (sp' + sign_extend (m := 64) (0x000#12)).toNat
          (EvalChildArm.wordLds8 (strCmpSeamMem mA sp' tok) sp'.toNat))
      rw [e0]
      refine ⟨⟨G.spRam, G.spRamHi, Or.inr (by have := G.spWin; omega)⟩, ?_⟩
      simp only [EvalChildArm.wordLds8, LPins8, List.getD_cons_zero, List.getD_cons_succ]
      repeat' apply And.intro <;> trivial
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hout4, hpc4, hmi4, hregs4, hframe4⟩ :=
    segEval_sound strRejoin c3.σ c3.tick c3.steps 0x80003b1c#64 vm3 (strRejoinL sp' x sret)
      [EvalChildArm.wordLds8 (strCmpSeamMem mA sp' tok) sp'.toNat]
      hG3 hpc3 hvm3 hLR (by change KeysOK [2, 10, 9]; decide) hfactsR
      (by show ChainOK 0x80003b1c#64 [2, 10, 9] strRejoin; decide) htick3
  have hfr4 : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ n ∈ wrChain strRejoin, (gprReg n == R) = false) →
      σ4.regs.get? R = c3.σ.regs.get? R := hframe4
  have hx12_4 : σ4.regs.get? Register.x12 = some tok := by
    have := gholds_lookup
      (v := bytesVal MKind.ld
        ([EvalChildArm.wordLds8 (strCmpSeamMem mA sp' tok) sp'.toNat].getD 0 []))
      _ hregs4 (strRejoin_x12 sp' x sret _)
    rw [show [EvalChildArm.wordLds8 (strCmpSeamMem mA sp' tok) sp'.toNat].getD 0 []
        = EvalChildArm.wordLds8 (strCmpSeamMem mA sp' tok) sp'.toNat from rfl,
      EvalChildArm.bytesVal_ld_wordLds (strCmpSeamMem mA sp' tok) sp'.toNat tok
        (read64_writeMap8 mA sp'.toNat tok)] at this
    exact this
  refine ⟨⟨σ4, i4, c3.steps + evalBlocksFuel strRejoin⟩, (hs2.trans hs3).trans hs4, ?_⟩
  exact
    { good := hG4
      tick := hi4
      pc := by
        rw [hpc4]
        show some (chainEndPC 0x80003b1c#64 (strRejoinL sp' x sret) _ strRejoin)
          = some 0x800036a4#64
        rw [chainEndPC_eq_bt strRejoin 0x80003b1c#64 (strRejoinL sp' x sret) _ (by decide)]
        rfl
      minstret := hmi4
      mem := by rw [hmem4, hmem3]; rfl
      out := hout4.trans hout3
      sign := ⟨x, gholds_lookup (v := x) _ hregs4 (strRejoin_x11 sp' x sret _),
        fun op bres hbr => by
          rw [hsa', hsb']
          exact hbr x csa' csb' (cstr_allNonzero hcsa') (cstr_allNonzero hcsb') hsign⟩
      tok := hx12_4
      sret := gholds_lookup (v := sret) _ hregs4 (strRejoin_x9 sp' x sret _)
      sp := (hfr4 Register.x2 (by decide) (by decide)).trans hx2_3
      frame := fun R hR h8 h19 => by
        have hnoise := abiNoise_noiseRegs hR
        have hRk := hR
        obtain ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
        have hns : NotWrittenStrcmp R :=
          ⟨abiPreserved_ne hab (by decide), abiPreserved_ne hab (by decide),
           abiPreserved_ne hab (by decide), abiPreserved_ne hab (by decide),
           abiPreserved_ne hab (by decide), abiPreserved_ne hab (by decide),
           abiPreserved_ne hab (by decide), abiPreserved_ne hab (by decide),
           abiPreserved_ne hab (by decide), hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
        rw [hfr4 R hnoise (by block_frame_wr [12, 11]), hframe3 R hns]
        exact (hframe2 R hab).trans (h.frame R hRk h8 h19) }

/-- The whole middle: kind check ≫ seam ≫ `strcmp` ≫ rejoin. -/
theorem strCmpTailReady_of_kindEntry
    {gC : (R : Register) → Option (RegisterType R)}
    {SL : StackLayout} {A : Arena}
    {sp' pl pr tok sret : BitVec 64} {sl sr : String} {mA : Mem} {out : Array String}
    {c : Config}
    (h : StrCmpKindEntry gC sp' pl pr tok sret mA out c)
    (G : StrCmpSeamGeom SL A sp' pl pr sl sr mA) :
    ∃ c', Steps c c' ∧ StrCmpTailReady gC sp' tok sret sl sr (strCmpSeamMem mA sp' tok) out c' := by
  obtain ⟨c1, hs1, h1⟩ := strCmpSeamEntry_of_kindEntry h G.image.text.Eval_exprLoaded
  obtain ⟨c2, hs2, h2⟩ := strCmpTailReady_of_seamEntry h1 G
  exact ⟨c2, hs1.trans hs2, h2⟩

#print axioms strSeam_facts
#print axioms strRejoin_x12
#print axioms FixedRodataLoaded.maskPinned
#print axioms strCmpSeamEntry_of_kindEntry
#print axioms strCmpTailReady_of_seamEntry
#print axioms strCmpTailReady_of_kindEntry

end Vsa.Sim
