import Vsa.Sim.StrCmpSeam
import Vsa.Sim.BinopChainGen
import Vsa.Sim.EqNeDispatchInput
import Vsa.Sim.BinaryPostGeom
import Vsa.Sim.BoolBoxEpilogue
import Vsa.Sim.Code.FixedImage_Value_bool
import Vsa.Sim.rows.EvalEqNeRow
import Vsa.Sim.rows.BinStrReadback
import Vsa.Sim.rows.BinDispatchRow
import Vsa.Sim.ExitFootprint

/-!
# `StrCmpCell` — the four string-comparison cells of `eval_binary_row`, ONCE

`hStrLt`/`hStrLe`/`hStrGt`/`hStrGe` are whole-node simulations of
`.binary op el er` at two string operands.  Their machine route is

```
blockA_binaryArm ≫ blockB_binary (both children)          shared front (landed)
0x8000351c → 0x80003628   operator dispatch                 evalBinopChain_run (landed, generic)
0x80003628 → 0x800036a4   kind check ≫ strcmp ≫ rejoin     StrCmpSeam (landed, op-independent)
0x800036a4 → jal value_bool   the op's sign tail            one #derive_case seg per op (landed)
value_bool ≫ ld s3 ≫ j 0x800033ec                          boolBoxEpilogue (landed)
blockD_v_rec                                               shared epilogue (landed)
```

Only the operator token, the jump-table slot, the sign-tail seg, and the
`value_bool` call site differ between the four cells.  This file names those
data in a descriptor `StrCmpOp` with a decided certificate `StrCmpOp.Cert`, and
proves every stage above ONCE over the descriptor:

* `strCmpKindEntry_of_twoSubReturn` — the dispatch from the actual return of
  both children (`TwoSubReturn`) to the seam's kind entry;
* `blockC_strcmp` — dispatch ≫ seam ≫ sign tail ≫ `value_bool` box, landing
  `PreEpilogueVD` (the same post as the integer `blockC_<op>` rows);
* `evalStrCmpSim` / `binRow_strcmp` — the recursive case from the arm entry and
  from the node entry (the shapes of `evalEqSimD` / `binRow_eq`);
* `binStrCmpCell_of` — the field supplier.

The residual surface is TWO named premises shared by the four cells:
`StrCmpOperandsSupply` (both operand payloads are `strcmp`-admissible regions
outside the callee's spill slot, at the actual return) and
`StrLeftPayloadSurvives` (the left string survives the right child's
execution — the `hVlSurv` premise of `blockB_binary_data`).  Both are facts about
where string payloads live (arena or AST region) that the ownership layer
supplies; see `PROOF_CLOSURE_PLAN.md`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-! ## The descriptor -/

/-- Per-operator data of a string-comparison cell. -/
structure StrCmpOp where
  /-- The source operator. -/
  op : BinOp
  /-- The boolean the cell produces from the two operand strings. -/
  bres : String → String → Bool
  /-- The operator token stored in the node (`binOpTok op`). -/
  tok : Nat
  /-- `tok - 11`, the jump-table index. -/
  idx : BitVec 64
  /-- The jump-table slot of the operator. -/
  slotAddr : BitVec 64
  /-- The landed slot-pinning predicate of the operator (`LtSlotPinned`, …). -/
  slotDef : Mem → Prop
  /-- The sign-test tail from `0x800036a4` to the operator's `jal value_bool`. -/
  tailSeg : List BBlock
  /-- The operator's `jal value_bool` PC. -/
  vbPC : BitVec 64
  /-- The `ld s3,1048(sp)` after the call. -/
  ldPC : BitVec 64
  /-- The `j 0x800033ec` after the reload. -/
  jPC : BitVec 64
  /-- The `jal value_bool` immediate. -/
  jalImm : BitVec 21
  /-- The `j 0x800033ec` immediate. -/
  jImm : BitVec 21

namespace StrCmpOp

/-- The token word the dispatch reads and the sign tail tests. -/
def tokW (D : StrCmpOp) : BitVec 64 := BitVec.ofNat 64 D.tok

/-- The sign-tail pin list: the `strcmp` word, the token, the result buffer. -/
def tailL (D : StrCmpOp) (x sret : BitVec 64) : GRegs := [(11, x), (12, D.tokW), (9, sret)]

/-- Decided and landed facts about one operator. -/
structure Cert (D : StrCmpOp) : Prop where
  tok_eq : binOpTok D.op = D.tok
  tok_lt : D.tok < 128
  sem : ∀ (s : Store) (sl sr : String),
    binOpSem s D.op (.str sl) (.str sr) = some (.bool (D.bres sl sr))
  order : StrCmpOrderBridge D.op D.bres
  slot_of_rodata : ∀ m, FixedRodataLoaded m → D.slotDef m
  slot_pinned : ∀ m, D.slotDef m → SlotPinned D.slotAddr 0xa4#8 0x96#8 0xfe#8 0xff#8 m
  index : (sign_extend (m := 64) (Sail.BitVec.extractLsb
    (D.tokW + sign_extend (m := 64) (0xff5#12)) 31 0) : BitVec 64) = D.idx
  slot_addr : (shift_bits_right (shift_bits_left D.idx
      (Sail.BitVec.extractLsb (0x20#6) 5 0)) (Sail.BitVec.extractLsb (0x1e#6) 5 0)
    + (((0x80003540#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
        + sign_extend (m := 64) (0xa44#12))) = D.slotAddr
  bltu : guardB bop.BLTU
      ((0#64 : BitVec 64) + sign_extend (m := 64) (0x00c#12))
      (sign_extend (m := 64) (Sail.BitVec.extractLsb
        (D.tokW + sign_extend (m := 64) (0xff5#12)) 31 0)) = false
  slot_lo : 0x80000000 ≤ D.slotAddr.toNat
  slot_hi : D.slotAddr.toNat + 4 ≤ 0x100000000
  slot_ht : D.slotAddr.toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ D.slotAddr.toNat
  slot_al : D.slotAddr.toNat % 4 = 0
  tail_ok : ChainOK 0x800036a4#64 [11, 12, 9] D.tailSeg
  tail_avoid : WrChainAvoidAbi D.tailSeg
  tail_facts : ∀ (σ : MState) (x sret : BitVec 64) (lds : List (List (BitVec 8))),
    Eval_exprLoaded σ.mem → ChainFacts σ.mem σ.mem (D.tailL x sret) lds D.tailSeg
  tail_end : ∀ x sret,
    evalBlocksPC 0x800036a4#64 (SegEvalState.init (D.tailL x sret) []) D.tailSeg = D.vbPC
  tail_log : ∀ (m : Mem) x sret,
    writeLog m (evalBlocks D.tailSeg (SegEvalState.init (D.tailL x sret) [])).log = m
  tail_x11 : ∀ x sret,
    lookupG 11 (evalBlocks D.tailSeg (SegEvalState.init (D.tailL x sret) [])).regs
      = some (sTailWord D.op x)
  tail_x10 : ∀ x sret,
    lookupG 10 (evalBlocks D.tailSeg (SegEvalState.init (D.tailL x sret) [])).regs
      = some (sret + sign_extend (m := 64) (0x000#12))
  jal_site : EqNeJalVboolSite D.vbPC D.jalImm
  ld_site : LdS3Site D.ldPC
  j_site : JExitSite D.jPC D.jImm
  jal_tgt : D.vbPC + sign_extend (m := 64) D.jalImm = 0x800027f8#64
  box_link : BitVec.addInt D.vbPC 4 = D.ldPC
  ld_update : BitVec.update (D.ldPC + sign_extend (m := 64) (0x000#12)) 0 0#1 = D.ldPC
  ld_after : BitVec.addInt D.ldPC 4 = D.jPC
  j_tgt : D.jPC + sign_extend (m := 64) D.jImm = 0x800033ec#64
  j_tgt_al : (D.jPC + sign_extend (m := 64) D.jImm).toNat % 4 = 0
  link_al : (BitVec.update (D.ldPC + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0

end StrCmpOp

/-- Every comparison slot routes the dispatch to `0x80003628`. -/
theorem strCmp_routes :
    (BitVec.update ((bytesVal MKind.lw [0xa4#8, 0x96#8, 0xfe#8, 0xff#8]
      + 0x80019f84#64) + sign_extend (m := 64) (0x000#12)) 0 0#1) = 0x80003628#64 := by
  decide

theorem strCmp_routes_al :
    (BitVec.update ((bytesVal MKind.lw [0xa4#8, 0x96#8, 0xfe#8, 0xff#8]
      + 0x80019f84#64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
  decide

/-! ## The operand pointers and the named residuals -/

/-- The left payload pointer the arm holds in `s3` (`ld s3,128(sp)`). -/
def strLeftPtr (m : Mem) (sp : BitVec 64) : BitVec 64 := bytesT8 m (sp.toNat - 960)

/-- The right payload pointer the dispatch loads into `a7` (`ld a7,152(sp)`). -/
def strRightPtr (m : Mem) (sp : BitVec 64) : BitVec 64 := bytesT8 m (sp.toNat - 936)

/-- **Residual 1** — at the actual return of both children, both payloads are
`strcmp`-admissible regions outside the callee's spill slot `[sp-1088, sp-1080)`.
String payloads live in the arena or the AST region; the ownership layer names
their location.  Stated over the memory and frame only. -/
structure StrCmpOperandsAt (sp : BitVec 64) (m : Mem) : Prop where
  left : ∀ cs, CStr m (strLeftPtr m sp).toNat cs →
    StrCmpRegion (sp - 1088#64) (strLeftPtr m sp) cs.length
  right : ∀ cs, CStr m (strRightPtr m sp).toNat cs →
    StrCmpRegion (sp - 1088#64) (strRightPtr m sp) cs.length

/-- Reached data of a string-comparison tail: the shared result geometry, the
fixed image at the return, and the operand regions. -/
structure StrCmpResid (D : StrCmpOp)
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (sp r sret aExpr : BitVec 64) (c' : Config) : Prop where
  geom : ArmPostGeomV gpre N A SL D.tok D.slotDef Value_boolLoaded 0x800027f8 0x8000280c 4
    sp r sret aExpr c'
  image : StaticImageSupport c'.σ.mem SL A
  ops : StrCmpOperandsAt sp c'.σ.mem

/-! ## The dispatch from the actual return -/

/-- Run the shared operator dispatch from a string/string `TwoSubReturn` and land
the seam's kind entry with the actual payload pointers. -/
theorem strCmpKindEntry_of_twoSubReturn (D : StrCmpOp) (C : D.Cert)
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat) (st' st'' : Vsa.While.St) (sl sr : String)
    (sp r sret aExpr : BitVec 64) (v8 v9 v18 : BitVec 64) (m0 : Mem) (c : Config)
    (hTS : TwoSubReturn gpre N A SL φf φc nf nc st' st'' (.str sl) (.str sr)
      sp r sret v8 v9 v18 m0 c)
    (hLoads : BinaryReturnLoads sp c)
    (hgeom : ArmPostGeomV gpre N A SL D.tok D.slotDef Value_boolLoaded 0x800027f8 0x8000280c 4
      sp r sret aExpr c) :
    ∃ c1, Steps c c1 ∧
      StrCmpKindEntry gpre (sp - 1088#64) (strLeftPtr c.σ.mem sp) (strRightPtr c.σ.mem sp)
        D.tokW sret c.σ.mem c.σ.sailOutput c1 := by
  have parts := TwoSubReturn.destruct gpre N A SL φf φc nf nc st' st'' (.str sl) (.str sr)
    sp r sret v8 v9 v18 m0 c hTS
  have hstaged := strOperandsStaged_of_twoSubReturn gpre N A SL φf φc nf nc st' st'' sl sr
    sp r sret v8 v9 v18 m0 c hTS
  obtain ⟨vmi, hmi⟩ := parts.p7
  have hx8 : c.σ.regs.get? Register.x8 = some aExpr :=
    (parts.p9 Register.x8 (by decide) (by decide)).trans hgeom.gx8
  have hSB : StackBounds sp SL :=
    ⟨hgeom.SLloSp, hgeom.SLlo, hgeom.SLwin, hgeom.sp8, hgeom.sphiRam⟩
  have hEB : ExprBounds aExpr := ⟨hgeom.exprLo, hgeom.exprHi, hgeom.exprWin⟩
  have hAr : SpArith sp SL := spArith hSB
  have hsp1088 : 1088 ≤ sp.toNat := hAr.sp1088
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]
    have := sp.isLt
    omega
  have gExpr8 := exprGeom4 hEB 8 (by decide)
  have gExpr4 := exprGeom4 hEB 4 (by decide)
  have g944 := slotGeom8 hSB 944 (by decide) (by decide) (by decide)
  have g936 := slotGeom8 hSB 936 (by decide) (by decide) (by decide)
  have g1088 := slotGeom8 hSB 1088 (by decide) (by decide) (by decide)
  have haddr944 :
      ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 944 :=
    spill_addr sp (0x090#12) 944 (by decide) (by decide) hsp1088
  have haddr936 :
      ((sp - 1088#64) + sign_extend (m := 64) (0x098#12)).toNat = sp.toNat - 936 :=
    spill_addr sp (0x098#12) 936 (by decide) (by decide) hsp1088
  have haddr0 :
      ((sp - 1088#64) + sign_extend (m := 64) (0x000#12)).toNat = sp.toNat - 1088 := by
    rw [sext_zero, BitVec.add_zero]
    exact hspsub
  have hop8 : (aExpr + sign_extend (m := 64) (0x008#12)).toNat = aExpr.toNat + 8 := by
    have hs : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
      apply BitVec.eq_of_toNat_eq
      decide
    rw [hs, BitVec.toNat_add]
    have hv : (8#64 : BitVec 64).toNat = 8 := by decide
    rw [hv]
    have := aExpr.isLt
    rw [Nat.mod_eq_of_lt (by omega)]
  have hline4 : (aExpr + sign_extend (m := 64) (0x004#12)).toNat = aExpr.toNat + 4 := by
    have hs : (sign_extend (m := 64) (0x004#12) : BitVec 64) = 4#64 := by
      apply BitVec.eq_of_toNat_eq
      decide
    rw [hs, BitVec.toNat_add]
    have hv : (4#64 : BitVec 64).toNat = 4 := by decide
    rw [hv]
    have := aExpr.isLt
    rw [Nat.mod_eq_of_lt (by omega)]
  -- the token word
  obtain ⟨tb0, tb1, tb2, tb3, htb0, htb1, htb2, htb3, htbrec⟩ :=
    read32_bytes c.σ.mem (aExpr.toNat + 8) D.tok hgeom.opTokRead
  have htok : bytesVal MKind.lw [tb0, tb1, tb2, tb3] = D.tokW :=
    sext_kind tb0 tb1 tb2 tb3 D.tok C.tok_lt htbrec
  -- the node's second word (dead, total)
  let lb0 := bytesT1 c.σ.mem (aExpr.toNat + 4)
  have hlb0 : bytesT1 c.σ.mem (aExpr.toNat + 4) = lb0 := rfl
  let lb1 := bytesT1 c.σ.mem (aExpr.toNat + 4 + 1)
  have hlb1 : bytesT1 c.σ.mem (aExpr.toNat + 4 + 1) = lb1 := rfl
  let lb2 := bytesT1 c.σ.mem (aExpr.toNat + 4 + 2)
  have hlb2 : bytesT1 c.σ.mem (aExpr.toNat + 4 + 2) = lb2 := rfl
  let lb3 := bytesT1 c.σ.mem (aExpr.toNat + 4 + 3)
  have hlb3 : bytesT1 c.σ.mem (aExpr.toNat + 4 + 3) = lb3 := rfl
  -- the right kind tag (3)
  obtain ⟨rkb0, rkb1, rkb2, rkb3, hrkb0, hrkb1, hrkb2, hrkb3, hrkbrec⟩ :=
    read32_bytes c.σ.mem (sp.toNat - 944) 3 hstaged.rKind
  have hrk : bytesVal MKind.lw [rkb0, rkb1, rkb2, rkb3] = (3#64 : BitVec 64) :=
    sext_kind rkb0 rkb1 rkb2 rkb3 3 (by decide) hrkbrec
  -- the right payload pointer (total)
  have hrread : read64 c.σ.mem (sp.toNat - 936) = some (strRightPtr c.σ.mem sp).toNat := by
    obtain ⟨pr, hpr, _, _⟩ := hstaged.rPtr
    have e : sp.toNat - 944 + 8 = sp.toNat - 936 := by omega
    rw [e] at hpr
    rw [hpr]
    unfold strRightPtr
    rw [bytesT8_toNat_of_read64 hpr]
  have hdp : bytesVal MKind.ld (EvalChildArm.wordLds8 c.σ.mem (sp.toNat - 936))
      = strRightPtr c.σ.mem sp :=
    EvalChildArm.bytesVal_ld_wordLds c.σ.mem (sp.toNat - 936) _ hrread
  -- the respilled left kind tag (3) and the left payload register
  obtain ⟨φfm, φcm, _hpfm, _hpcm, ⟨_φcr, _hpcr, _hvalR⟩, ⟨φcl, hvalL⟩, _hstoreTail⟩ := parts.p11
  have hKindResp := hLoads.kind_readback hvalL
  obtain ⟨kb0, kb1, kb2, kb3, kb4, kb5, kb6, kb7,
    hkb0, hkb1, hkb2, hkb3, hkb4, hkb5, hkb6, hkb7, hkbrec⟩ :=
    read64_bytes c.σ.mem (sp.toNat - 1088)
      (BitVec.ofNat 64 (kindTag (.str sl))).toNat hKindResp
  have hlk : bytesVal MKind.ld [kb0, kb1, kb2, kb3, kb4, kb5, kb6, kb7]
      = BitVec.ofNat 64 (kindTag (.str sl)) := by
    apply BitVec.eq_of_toNat_eq
    show (sign_extend (m := 64)
      ((((((((kb7.append kb6).append kb5).append kb4).append kb3).append kb2).append kb1).append kb0)
        : BitVec (8 * 8))).toNat = _
    rw [sext_full, word8_toNat_recon, hkbrec]
  have hX19 : c.σ.regs.get? Register.x19 = some (strLeftPtr c.σ.mem sp) :=
    hLoads.payload_register
  have hfb : FrameBundle c.σ.mem (sp - 1088#64) :=
    ⟨hspsub ▸ (frameBaseGeom hSB).1,
      hspsub ▸ (frameBaseGeom hSB).2.1,
      hspsub ▸ (frameBaseGeom hSB).2.2.1,
      hspsub ▸ (frameBaseGeom hSB).2.2.2⟩
  have hSlot : SlotPinned D.slotAddr 0xa4#8 0x96#8 0xfe#8 0xff#8 c.σ.mem :=
    C.slot_pinned _ hgeom.slot
  -- the dispatch run
  obtain ⟨σ', i', hsteps, hi', hG', hpc', hx10', hx12', hx16', hx17', hx2', hx9', hx19',
      hmem', hout', hmi', hframe'⟩ :=
    evalBinopChain_run c.σ c.tick c.steps vmi (sp - 1088#64) aExpr sret (strLeftPtr c.σ.mem sp)
      (3#64) (BitVec.ofNat 64 (kindTag (.str sl)))
      D.tokW D.idx D.slotAddr 0x80003628#64
      tb0 tb1 tb2 tb3 0xa4#8 0x96#8 0xfe#8 0xff#8
      lb0 lb1 lb2 lb3 rkb0 rkb1 rkb2 rkb3
      (bytesT1 c.σ.mem (sp.toNat - 936)) (bytesT1 c.σ.mem (sp.toNat - 936 + 1))
      (bytesT1 c.σ.mem (sp.toNat - 936 + 2)) (bytesT1 c.σ.mem (sp.toNat - 936 + 3))
      (bytesT1 c.σ.mem (sp.toNat - 936 + 4)) (bytesT1 c.σ.mem (sp.toNat - 936 + 5))
      (bytesT1 c.σ.mem (sp.toNat - 936 + 6)) (bytesT1 c.σ.mem (sp.toNat - 936 + 7))
      kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7
      htok (by rw [htok]; exact C.index) C.slot_addr strCmp_routes (by rw [htok]; exact C.bltu)
      C.slot_lo C.slot_hi C.slot_ht C.slot_al strCmp_routes_al
      parts.p1 parts.p3 hmi parts.p6 hx8 parts.p5 hX19 parts.p12 hrk hlk
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
      (by rw [haddr936]) (by rw [haddr936]) (by rw [haddr936]) (by rw [haddr936])
      (by rw [haddr936]) (by rw [haddr936]) (by rw [haddr936]) (by rw [haddr936])
      hSlot
      (by rw [haddr0]; exact g1088.lo) (by rw [haddr0]; exact g1088.hi8)
      (by rw [haddr0]; exact g1088.ht8) (by rw [haddr0]; exact g1088.al8)
      (by rw [haddr0]; exact lpin_of_present hkb0) (by rw [haddr0]; exact lpin_of_present hkb1)
      (by rw [haddr0]; exact lpin_of_present hkb2) (by rw [haddr0]; exact lpin_of_present hkb3)
      (by rw [haddr0]; exact lpin_of_present hkb4) (by rw [haddr0]; exact lpin_of_present hkb5)
      (by rw [haddr0]; exact lpin_of_present hkb6) (by rw [haddr0]; exact lpin_of_present hkb7)
      parts.p2
  refine ⟨⟨σ', i', c.steps + 16⟩, hsteps, ?_⟩
  exact
    { good := hG'
      tick := hi'
      pc := hpc'
      minstret := hmi'
      mem := hmem'
      out := hout'
      rKind := hx10'
      lKind := hx16'
      rPtr := by rw [hx17']; exact congrArg some hdp
      lPtr := hx19'
      tok := hx12'
      sp := hx2'
      sret := hx9'
      frame := fun R hR h8 h19 => (hframe' R hR h8).trans (parts.p9 R hR h19) }

/-! ## The seam geometry at the actual return -/

/-- The seam's geometry from the reached data. -/
theorem strCmpSeamGeom_of_resid (D : StrCmpOp)
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {nf nc : Nat} {st' st'' : Vsa.While.St} {sl sr : String}
    {sp r sret aExpr : BitVec 64} {v8 v9 v18 : BitVec 64} {m0 : Mem} {c : Config}
    (hTS : TwoSubReturn gpre N A SL φf φc nf nc st' st'' (.str sl) (.str sr)
      sp r sret v8 v9 v18 m0 c)
    (R : StrCmpResid D gpre N A SL sp r sret aExpr c) :
    StrCmpSeamGeom SL A (sp - 1088#64) (strLeftPtr c.σ.mem sp) (strRightPtr c.σ.mem sp)
      sl sr c.σ.mem := by
  have hstaged := strOperandsStaged_of_twoSubReturn gpre N A SL φf φc nf nc st' st'' sl sr
    sp r sret v8 v9 v18 m0 c hTS
  have hsp1088 : 1088 ≤ sp.toNat := by have := R.geom.SLloSp; omega
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]
    have := sp.isLt
    omega
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine
    { image := R.image
      spLo := by rw [hspsub]; have := R.geom.SLloSp; omega
      spHi := by rw [hspsub]; have := R.geom.spSLhi; omega
      spRam := by rw [hspsub]; have := R.geom.SLloSp; have := R.geom.SLlo; omega
      spRamHi := by rw [hspsub]; have := R.geom.sphiRam; omega
      spWin := by rw [hspsub]; have := R.geom.SLloSp; have := R.geom.SLwin; omega
      sp8 := by rw [hspsub]; have := R.geom.sp8; omega
      left := ?_
      right := ?_
      leftRegion := R.ops.left
      rightRegion := R.ops.right }
  · obtain ⟨pl, hpl, _, hcs⟩ := hstaged.lPtr
    have e : sp.toNat - 968 + 8 = sp.toNat - 960 := by omega
    rw [e] at hpl
    have : (strLeftPtr c.σ.mem sp).toNat = pl := bytesT8_toNat_of_read64 hpl
    rw [this]
    exact hcs
  · obtain ⟨pr, hpr, _, hcs⟩ := hstaged.rPtr
    have e : sp.toNat - 944 + 8 = sp.toNat - 936 := by omega
    rw [e] at hpr
    have : (strRightPtr c.σ.mem sp).toNat = pr := bytesT8_toNat_of_read64 hpr
    rw [this]
    exact hcs

/-! ## `blockC_strcmp` — dispatch ≫ seam ≫ sign tail ≫ box -/

/-- The exact memory footprint of a string-comparison cell from the return of
both children to the epilogue entry: the token spill `[sp-1088, sp-1080)` (the
seam's `sd a2,0(sp)`; `strcmp` and the sign tail write nothing) and the
`value_bool` box `[sret, sret+24)`. -/
def strCmpCellFoot (sp sret : Nat) (k : Nat) : Prop :=
  word8 (sp - 1088) k ∨ resultSlot sret k

/-- From the actual return of both children (memory `mret`) to the shared
pre-epilogue, for any string comparison, RETAINING the cell's footprint
`strCmpCellFoot` from `mret` to the epilogue-entry memory.  `blockC_strcmp` is
its footprint-free projection (the integer rows' post, `blockC_lt`, …). -/
theorem blockC_strcmp_footprint (D : StrCmpOp) (C : D.Cert)
    (gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat) (st' st'' : Vsa.While.St) (sl sr : String)
    (sp r sret aExpr : BitVec 64) (v8 v9 v18 v19 : BitVec 64) (out0 : Array String)
    (m0 mret : Mem) :
    Triple
      (fun c =>
        TwoSubReturn gpre N A SL φf φc nf nc st' st'' (.str sl) (.str sr)
          sp r sret v8 v9 v18 m0 c ∧
        StrCmpResid D gpre N A SL sp r sret aExpr c ∧
        BinaryReturnData SL sp sret c ∧
        String.join out0.toList = st''.out ∧
        c.σ.sailOutput = out0 ∧
        g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
        g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧
        gpre Register.x19 = some v19 ∧ g Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x2 == R) = false →
          gpre R = g R) ∧
        c.σ.mem = mret)
      (fun c => ∃ (mpre : Mem) (φfm φcm φfe φce : Addr → Nat),
        PhiExtends φf φfm nf ∧
        PhiExtends φc φcm nc ∧
        PhiExtends φfm φfe st'.store.frames.size ∧
        PhiExtends φcm φce st'.store.closures.size ∧
        PreEpilogueVD g N A SL φfe φce st'' (.bool (D.bres sl sr))
          sp r sret v8 v9 v18 out0 m0 mpre c ∧
        MemFootprint (strCmpCellFoot sp.toNat sret.toNat) mret mpre) := by
  intro c hpre
  obtain ⟨hTS, R, hData, houtStr, hout0eq, hgv8, hgv9, hgv18, hgv2, hgprex19, hgx19, hbridge,
    hmret⟩ := hpre
  have parts := TwoSubReturn.destruct gpre N A SL φf φc nf nc st' st'' (.str sl) (.str sr)
    sp r sret v8 v9 v18 m0 c hTS
  have hsp1088 : 1088 ≤ sp.toNat := by have := R.geom.SLloSp; omega
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]
    have := sp.isLt
    omega
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- (1) dispatch
  obtain ⟨c1, hs1, hKind⟩ :=
    strCmpKindEntry_of_twoSubReturn D C gpre N A SL φf φc nf nc st' st'' sl sr
      sp r sret aExpr v8 v9 v18 m0 c hTS hData.toBinaryReturnLoads R.geom
  -- (2) the seam
  obtain ⟨c2, hs2, T⟩ := strCmpTailReady_of_kindEntry hKind (strCmpSeamGeom_of_resid D hTS R)
  -- the memory after the seam
  let mB := strCmpSeamMem c.σ.mem (sp - 1088#64) D.tokW
  have hmBdef : mB = strCmpSeamMem c.σ.mem (sp - 1088#64) D.tokW := rfl
  have hAgB : ∀ k, ¬ (sp.toNat - 1088 ≤ k ∧ k < sp.toNat - 1080) → mB[k]? = c.σ.mem[k]? := by
    intro k hk
    rw [hmBdef]
    exact strCmpSeamMem_agree c.σ.mem (sp - 1088#64) D.tokW k (by rw [hspsub]; omega)
  have himageB : StaticImageSupport mB SL A := by
    rw [hmBdef]
    exact R.image.writeMap8 (sp - 1088#64).toNat D.tokW
      (by rw [hspsub]; have := R.geom.SLloSp; omega)
      (by rw [hspsub]; have := R.geom.spSLhi; omega)
  have hcodeB : Eval_exprLoaded mB := himageB.text.Eval_exprLoaded
  have hVboolB : Value_boolLoaded mB := himageB.text.Value_boolLoaded
  have hMemExtB : MemExtends c.σ.mem mB := by
    rw [hmBdef]; exact memExtends_writeMap8 _ _ _
  -- (3) the sign tail
  obtain ⟨x, hx11_2, hsignx⟩ := T.sign
  obtain ⟨vm2, hvm2⟩ := T.minstret
  have hL2 : GHolds c2.σ (D.tailL x sret) := by
    simp only [StrCmpOp.tailL, GHolds, gprGet]
    exact ⟨hx11_2, T.tok, T.sret, True.intro⟩
  have hcode2 : Eval_exprLoaded c2.σ.mem := by rw [T.mem]; exact hcodeB
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hout3, hpc3, hmi3, hregs3, hframe3⟩ :=
    segEval_sound D.tailSeg c2.σ c2.tick c2.steps 0x800036a4#64 vm2 (D.tailL x sret) []
      T.good T.pc hvm2 hL2 (by change KeysOK [11, 12, 9]; decide)
      (C.tail_facts c2.σ x sret [] hcode2) C.tail_ok T.tick
  have hfr3 : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ n ∈ wrChain D.tailSeg, (gprReg n == R) = false) →
      σ3.regs.get? R = c2.σ.regs.get? R := hframe3
  have hwr3 : ∀ R : Register, AbiPreserved R = true →
      ∀ n ∈ wrChain D.tailSeg, (gprReg n == R) = false :=
    fun R hR n hn => abiPreserved_ne hR (C.tail_avoid n hn)
  have hmem3B : σ3.mem = mB := by rw [hmem3, C.tail_log, T.mem]
  have hpc3v : σ3.regs.get? Register.PC = some D.vbPC := by rw [hpc3, C.tail_end]
  have hx11_3 : σ3.regs.get? Register.x11 = some (sTailWord D.op x) :=
    gholds_lookup (n := 11) _ hregs3 (C.tail_x11 x sret)
  have hx10_3 : σ3.regs.get? Register.x10 = some sret := by
    have := gholds_lookup (n := 10) _ hregs3 (C.tail_x10 x sret)
    rw [sext_zero, BitVec.add_zero] at this
    exact this
  have hx9_3 : σ3.regs.get? Register.x9 = some sret :=
    (hfr3 Register.x9 (by decide) (hwr3 Register.x9 (by decide))).trans T.sret
  have hx2_3 : σ3.regs.get? Register.x2 = some (sp - 1088#64) :=
    (hfr3 Register.x2 (by decide) (hwr3 Register.x2 (by decide))).trans T.sp
  obtain ⟨vm3, hvm3⟩ := hmi3
  have hcode3 : Eval_exprLoaded σ3.mem := by rw [hmem3B]; exact hcodeB
  -- (4) `jal value_bool`
  obtain ⟨τ, j, hstepτ, hj, hGτ, hmemτ, hobs⟩ :=
    C.jal_site σ3 i3 (c2.steps + evalBlocksFuel D.tailSeg) D.vbPC vm3 hG3 hpc3v hvm3 hcode3 rfl hi3
  have hmemτB : τ.mem = mB := by rw [hmemτ, hmem3B]
  have hpcτ : τ.regs.get? Register.PC = some (0x800027f8#64) := by
    have := obs_jal_pc hobs
    rwa [C.jal_tgt] at this
  have hlinkτ : τ.regs.get? Register.x1 = some D.ldPC := by
    have := obs_jal_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [C.box_link] at this
  have hx10τ : τ.regs.get? Register.x10 = some sret :=
    obs_jal_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx10_3
  have hx11τ : τ.regs.get? Register.x11 = some (sTailWord D.op x) :=
    obs_jal_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx11_3
  have hx9τ : τ.regs.get? Register.x9 = some sret :=
    obs_jal_other hobs Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx9_3
  have hspτ : τ.regs.get? Register.x2 = some (sp - 1088#64) :=
    obs_jal_other hobs Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hx2_3
  obtain ⟨vmiτ, hmiτ⟩ := obs_jal_minstret hobs
  have houtτ : τ.sailOutput = out0 := by
    rw [hobs.out, sailOutput_sigmaPost_jal, hout3, T.out, hout0eq]
  have hcodeτ : Eval_exprLoaded τ.mem := by rw [hmemτB]; exact hcodeB
  have hVboolτ : Value_boolLoaded τ.mem := by rw [hmemτB]; exact hVboolB
  -- (5) the transport facts for the box at `τ`
  obtain ⟨φfm, φcm, hpfm, hpcm, _hR, _hL, φf', φc', hpf', hpc', _hstore, hSurv⟩ := parts.p11
  obtain ⟨w19, hgprex19', hs3slot⟩ := parts.p10
  have hw19 : w19 = v19 := by
    rw [hgprex19] at hgprex19'
    exact (Option.some.inj hgprex19').symm
  have hAgSlots : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat) c.σ.mem mB := by
    intro k hk
    exact (hAgB k (by omega)).symm
  have hs3τ : read64 τ.mem (sp.toNat - 40) = some w19.toNat := by
    rw [hmemτB, ← read64_agreeP hAgSlots (fun j hj => ⟨by omega, by omega⟩)]
    exact hs3slot
  have hslotRaτ : read64 τ.mem (sp.toNat - 8) = some r.toNat := by
    rw [hmemτB, ← read64_agreeP hAgSlots (fun j hj => ⟨by omega, by omega⟩)]
    exact parts.p13
  have hslotS0τ : read64 τ.mem (sp.toNat - 16) = some v8.toNat := by
    rw [hmemτB, ← read64_agreeP hAgSlots (fun j hj => ⟨by omega, by omega⟩)]
    exact parts.p14
  have hslotS1τ : read64 τ.mem (sp.toNat - 24) = some v9.toNat := by
    rw [hmemτB, ← read64_agreeP hAgSlots (fun j hj => ⟨by omega, by omega⟩)]
    exact parts.p15
  have hslotS2τ : read64 τ.mem (sp.toNat - 32) = some v18.toNat := by
    rw [hmemτB, ← read64_agreeP hAgSlots (fun j hj => ⟨by omega, by omega⟩)]
    exact parts.p16
  have hSurvτ : ∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → τ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st''.store := by
    intro m' hm'
    refine hSurv m' (fun k hk => ?_)
    have hkB : ¬ (sp.toNat - 1088 ≤ k ∧ k < sp.toNat - 1080) := by
      intro ⟨h1, h2⟩
      have := R.geom.SLloSp
      have := R.geom.spSLhi
      exact hk ⟨by omega, by omega⟩
    rw [← hm' k hk, hmemτB, hAgB k hkB]
  have hMemExtτ : MemExtends m0 τ.mem := by
    rw [hmemτB]; exact parts.p17.trans hMemExtB
  have hWordsτ : ValueWordsTotal τ.mem sret.toNat := by
    rw [hmemτB]; exact ValueWordsTotal.mono hMemExtB hData.sret_words
  have hmemframeτ : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ τ.mem[a]? = m0[a]? := by
    intro a ha hA
    right
    have haB : ¬ (sp.toNat - 1088 ≤ a ∧ a < sp.toNat - 1080) := by
      intro ⟨h1, h2⟩
      have := R.geom.SLloSp
      exact ha ⟨by omega, by omega⟩
    rw [hmemτB, hAgB a haB]
    exact parts.p18 a ha hA
  have hframeGτ : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      (Register.x19 == R) = false → τ.regs.get? R = g R := by
    intro R hR he8 he9 he18 he2 h19ne
    have hRk := hR
    obtain ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    have ne : ∀ {X : Register}, AbiPreserved X = false → (X == R) = false :=
      fun hX => abiPreserved_ne hab hX
    have f_τ : τ.regs.get? R = σ3.regs.get? R :=
      (hobs.1 R hmc' hmt' hmip').trans
        (get?_sigmaPost_jal _ _ _ _ _ _ R hmi' hpc' (ne (X := Register.x1) (by decide))
          hnpc' hmii')
    rw [f_τ, hfr3 R (abiNoise_noiseRegs hRk) (hwr3 R hab), T.frame R hRk he8 h19ne]
    exact hbridge R hRk he8 he9 he18 he2
  have hBoolRegion : BoolRegion sret :=
    ⟨R.geom.sretAl, R.geom.sretLo, R.geom.sretHi, R.geom.sretWin, R.geom.sretVi⟩
  have hval_bridge : (sTailWord D.op x != 0#64) = D.bres sl sr := hsignx D.op D.bres C.order
  have hspHtif : tohostAddr + 16 + 1088 ≤ sp.toNat := by
    have := R.geom.SLloSp; have := R.geom.SLwin; omega
  obtain ⟨hgeo1, hgeo2, hgeo3, hgeo4⟩ :=
    eqne_ld_geom sp hsp1088 R.geom.sphiRam hspHtif R.geom.sp8
  let cvb : Config := ⟨τ, j, c2.steps + evalBlocksFuel D.tailSeg + 1⟩
  obtain ⟨mpre, φfm2, φcm2, φfe, φce, cfin, hStepsFin, hp1, hp2, hp3, hp4, hPre, hBoxFoot⟩ :=
    boolBoxEpilogue_footprint g N A SL φf φc φfm φcm φf' φc' nf nc
      st'.store.frames.size st'.store.closures.size st' st''
      sp r sret v8 v9 v18 v19 w19 (sTailWord D.op x) (D.bres sl sr) out0 m0
      cvb D.ldPC D.ldPC D.jPC D.jImm
      (fun σ i u pc vminstret v2 b0 b1 b2 b3 b4 b5 b6 b7 =>
        C.ld_site σ i u pc vminstret v2 b0 b1 b2 b3 b4 b5 b6 b7)
      (fun σ i u pc vminstret => C.j_site σ i u pc vminstret)
      rfl C.ld_update C.ld_after C.j_tgt C.j_tgt_al (eqne_ldPCeq sp hsp1088)
      hGτ hVboolτ hpcτ hx10τ hx11τ hlinkτ hx9τ hspτ ⟨vmiτ, hmiτ⟩ hj
      houtτ hcodeτ hBoolRegion C.link_al hval_bridge
      hpfm hpcm hpf' hpc' houtStr hSurvτ hs3τ
      hslotRaτ hslotS0τ hslotS1τ hslotS2τ
      hgv8 hgv9 hgv18 hgv2 hgx19 hw19 hframeGτ
      hMemExtτ hWordsτ hmemframeτ
      R.geom.sretEvalCode R.geom.sretStk R.geom.sretInSL
      (by have := R.geom.SLloSp; omega) (by have := R.geom.SLloSp; omega)
      hsp1088 R.geom.sphiRam (by have := R.geom.SLloSp; have := R.geom.SLlo; omega)
      hspHtif R.geom.sp8 R.geom.raAl
      hgeo1 hgeo2 hgeo3 hgeo4
  refine ⟨cfin, ?_, mpre, φfm2, φcm2, φfe, φce, hp1, hp2, hp3, hp4, hPre, ?_⟩
  · have hchain : Steps c cvb :=
      ((hs1.trans hs2).trans hs3).trans (Steps.single hstepτ)
    exact hchain.trans hStepsFin
  · -- the footprint: `mret → mB` is the token spill, `mB = τ.mem → mpre` the box.
    have hSpill : MemFootprint (word8 (sp.toNat - 1088)) mret mB :=
      ⟨fun k hk => by
        rw [← hmret]
        exact hAgB k (by unfold word8 at hk; omega)⟩
    have hBox : MemFootprint (resultSlot sret.toNat) mB mpre := by
      rw [hmemτB] at hBoxFoot; exact hBoxFoot
    exact hSpill.trans hBox

/-- The footprint-free projection (the landed statement). -/
theorem blockC_strcmp (D : StrCmpOp) (C : D.Cert)
    (gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat) (st' st'' : Vsa.While.St) (sl sr : String)
    (sp r sret aExpr : BitVec 64) (v8 v9 v18 v19 : BitVec 64) (out0 : Array String)
    (m0 : Mem) :
    Triple
      (fun c =>
        TwoSubReturn gpre N A SL φf φc nf nc st' st'' (.str sl) (.str sr)
          sp r sret v8 v9 v18 m0 c ∧
        StrCmpResid D gpre N A SL sp r sret aExpr c ∧
        BinaryReturnData SL sp sret c ∧
        String.join out0.toList = st''.out ∧
        c.σ.sailOutput = out0 ∧
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
        PreEpilogueVD g N A SL φfe φce st'' (.bool (D.bres sl sr))
          sp r sret v8 v9 v18 out0 m0 mpre c) := by
  intro c hpre
  obtain ⟨hTS, R, hData, houtStr, hout0eq, hgv8, hgv9, hgv18, hgv2, hgprex19, hgx19, hbridge⟩ :=
    hpre
  obtain ⟨c', hs, mpre, φfm, φcm, φfe, φce, hp1, hp2, hp3, hp4, hPre, _⟩ :=
    blockC_strcmp_footprint D C gpre g N A SL φf φc nf nc st' st'' sl sr
      sp r sret aExpr v8 v9 v18 v19 out0 m0 c.σ.mem c
      ⟨hTS, R, hData, houtStr, hout0eq, hgv8, hgv9, hgv18, hgv2, hgprex19, hgx19, hbridge, rfl⟩
  exact ⟨c', hs, mpre, φfm, φcm, φfe, φce, hp1, hp2, hp3, hp4, hPre⟩

/-! ## The recursive case from the arm entry and from the node entry -/

/-- The left string survives the right child: the `hVlSurv` premise of
`blockB_binary_data` at a string operand.  Its universal memory quantification
holds only for payloads outside the arena; see the obstruction recorded in
`PROOF_CLOSURE_PLAN.md`. -/
def StrLeftSurvives (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (sp : BitVec 64) (sl : String) : Prop :=
  ∀ (φ : Addr → Nat) (mm mm' : Mem),
    ValueRepr mm N φ (sp.toNat - 968) (.str sl) →
    (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat - 1080) → ¬ (A.lo ≤ k ∧ k < A.hi) →
      ¬ ((sp.toNat - 944) ≤ k ∧ k < (sp.toNat - 944) + 24) → mm[k]? = mm'[k]?) →
    ValueRepr mm' N φ (sp.toNat - 968) (.str sl)

/-- **`evalStrCmpSim`** — the `EvalE.binary op` recursive case at two string
operands, from the arm entry: `blockB_binary_data ≫ blockC_strcmp ≫ blockD_v_rec`
(the shape of `evalLtSim`). -/
theorem evalStrCmpSim (D : StrCmpOp) (C : D.Cert)
    (gouter gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (sl sr : String)
    (sp r sret aExpr aEnv aLOp aROp aEnvReg : BitVec 64) (v8 v9 v18 v19 : BitVec 64)
    (out0 : Array String) (m0 : Mem)
    (hLeft : EvalE st d env el st' (.str sl))
    (hIHl : EvalIH st d env el st' (.str sl))
    (hIHr : EvalIH st' d env er st'' (.str sr))
    (hEvalE : EvalE st d env (.binary D.op el er) st'' (.bool (D.bres sl sr)))
    (hVlSurv : StrLeftSurvives N A SL sp sl)
    (hResid : ∀ c2 : Config,
      TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
        st' st'' (.str sl) (.str sr) sp r sret v8 v9 v18 m0 c2 →
      StrCmpResid D gpre N A SL sp r sret aExpr c2) :
    Triple
      (fun c => ∃ ment,
        ArmEntryK gouter N A SL φf φc st (0x800034e8#64) UnaryArmCallee (.binary D.op el er)
          sp r sret aExpr aEnv v8 v9 v18 out0 m0 ment c ∧
        BinExtras N A SL el er ment sp sret aExpr aLOp aROp ∧
        BinaryRecContext gpre φf st env aEnvReg ∧
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
        MemExtends m0 ment ∧
        EvalGround ment SL A sp sret aExpr.toNat (.binary D.op el er) ∧
        StackOK SL (sp - 1088#64)
          (el.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget el = true ∧
        Vsa.While.StoreBodiesBound st.store Vsa.While.perCallBudget ∧
        StackOK SL (sp - 1088#64)
          (er.stackNeed + (Vsa.While.maxCallDepth - d) * Vsa.While.perCallBudget + 1088) ∧
        Expr.bodiesBound Vsa.While.perCallBudget er = true ∧
        Vsa.While.StoreBodiesBound st'.store Vsa.While.perCallBudget ∧
        g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
        g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧ g Register.x19 = some v19 ∧
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x2 == R) = false →
          gpre R = g R))
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st'' (.bool (D.bres sl sr)) sp r sret m0) := by
  intro c hpre
  obtain ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
    hpayL, hexprL, hpayR, hexprR, hMemExtM0, hGmt47,
    hstackBudgetL, hexprBodiesL, hstoreBodiesL,
    hstackBudgetR, hexprBodiesR, hstoreBodiesR,
    hgv8, hgv9, hgv18, hgv2, hgvx19, hbridge⟩ := hpre
  obtain ⟨c2, hs2, hReturned⟩ :=
    blockB_binary_data gouter gpre N A SL φf φc st st' st'' d env D.op el er (.str sl) (.str sr)
      sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 out0 m0 hLeft hIHl hIHr hVlSurv
      c ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
        hpayL, hexprL, hpayR, hexprR, hMemExtM0, hGmt47,
        hstackBudgetL, hexprBodiesL, hstoreBodiesL,
        hstackBudgetR, hexprBodiesR, hstoreBodiesR⟩
  have hTS := hReturned.result
  have hData := hReturned.extra
  have hR : StrCmpResid D gpre N A SL sp r sret aExpr c2 := hResid c2 hTS
  have hOutC2 : String.join c2.σ.sailOutput.toList = st''.out :=
    (TwoSubReturn.destruct gpre N A SL φf φc st.store.frames.size st.store.closures.size
      st' st'' (.str sl) (.str sr) sp r sret v8 v9 v18 m0 c2 hTS).p8
  obtain ⟨c3, hs3, mpre, φfm, φcm, φfe, φce, hpfm, hpcm, hpfe, hpce, hPreD⟩ :=
    blockC_strcmp D C gpre g N A SL φf φc st.store.frames.size st.store.closures.size
      st' st'' sl sr sp r sret aExpr v8 v9 v18 v19 c2.σ.sailOutput m0
      c2 ⟨hTS, hR, hData, hOutC2, rfl, hgv8, hgv9, hgv18, hgv2, hgx19, hgvx19, hbridge⟩
  obtain ⟨c4, hs4, hExitDe⟩ :=
    blockD_v_rec g N A SL φfe φce st'' (.bool (D.bres sl sr)) sp r sret v8 v9 v18
      c2.σ.sailOutput m0 c3 ⟨mpre, hPreD⟩
  obtain ⟨hExitE, hMemExt, hWords, φf', φc', hpf', hpc', hSurv⟩ := hExitDe
  have hmono := evalE_store_mono hEvalE
  have hleftMono := evalE_store_mono hLeft
  have hleF' : st.store.frames.size ≤ st'.store.frames.size := hleftMono.1
  have hleC' : st.store.closures.size ≤ st'.store.closures.size := hleftMono.2
  have hpfF : PhiExtends φf φfe st.store.frames.size := hpfm.trans (PhiExtends.mono hleF' hpfe)
  have hpcF : PhiExtends φc φce st.store.closures.size :=
    hpcm.trans (PhiExtends.mono hleC' hpce)
  have hExit : EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st'' (.bool (D.bres sl sr)) sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfF hpcF hExitE hmono.1 hmono.2
  exact ⟨c4, ((hs2.trans hs3).trans hs4), hExit, hMemExt, hWords,
    φf', φc', hpfF.trans (PhiExtends.mono hmono.1 hpf'),
    hpcF.trans (PhiExtends.mono hmono.2 hpc'), hSurv⟩

/-- **`binRow_strcmp`** — the string-comparison cell from the node entry (the
shape of `binRow_eq`): `blockA_binaryArm_budgeted ≫ evalStrCmpSim`. -/
theorem binRow_strcmp (D : StrCmpOp) (C : D.Cert)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (sl sr : String)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    (hLeft : EvalE st d env el st' (.str sl))
    (hIHl : EvalIH st d env el st' (.str sl))
    (hIHr : EvalIH st' d env er st'' (.str sr))
    (hEvalE : EvalE st d env (.binary D.op el er) st'' (.bool (D.bres sl sr)))
    (hVlSurv : ∀ c : Config,
      EvalEntry g N A SL φf φc st d env (.binary D.op el er) sp r sret aEnv aExpr m0 c →
      StrLeftSurvives N A SL sp sl)
    (hResid : ∀ c : Config,
      EvalEntry g N A SL φf φc st d env (.binary D.op el er) sp r sret aEnv aExpr m0 c →
      ∀ (gpre : (R : Register) → Option (RegisterType R)) (v8 v9 v18 v19 : BitVec 64),
      BinaryArmFrame g gpre sp aExpr v8 v9 v18 v19 →
      ∀ c2 : Config,
      TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
        st' st'' (.str sl) (.str sr) sp r sret v8 v9 v18 m0 c2 →
      StrCmpResid D gpre N A SL sp r sret aExpr c2) :
    Triple
      (fun c => EvalEntry g N A SL φf φc st d env (.binary D.op el er) sp r sret aEnv aExpr m0 c)
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st'' (.bool (D.bres sl sr)) sp r sret m0) := by
  intro c hc
  obtain ⟨aLOp, aROp, hX⟩ := hc.binaryExtras
  have hstoreBodiesR := StoreBodiesBound.afterEvalE hLeft
    (Expr.bodiesBound_binary hc.expr_bodies).1 hc.store_bodies
  obtain ⟨c1, hs1, gpre', aEnvReg', v8', v9', v18', v19', ment, hArm, hBE, hRec, hx11, hx13, hx19,
    hgframe, hg8w, hg18w, hgx8, hgx18, hgx19, hpayL, hexprL, hpayR, hexprR, hMemExt, hGmt,
    hsbL, hebL, hstbL, hsbR, hebR, hstbR⟩ :=
    blockA_binaryArm_budgeted g N A SL φf φc st st' d env D.op el er sp r sret aEnv aExpr
      aLOp aROp m0 hX hstoreBodiesR c hc
  have hArmFrame := BinaryArmFrame.of_entry hArm hgframe hgx19
  obtain ⟨c2, hs2, hExit⟩ :=
    evalStrCmpSim D C g gpre' g N A SL φf φc st st' st'' d env el er sl sr
      sp r sret aExpr aEnv aLOp aROp aEnvReg' v8' v9' v18' v19' c1.σ.sailOutput m0
      hLeft hIHl hIHr hEvalE (hVlSurv c hc) (hResid c hc gpre' v8' v9' v18' v19' hArmFrame)
      c1 ⟨ment, hArm, hBE, hRec, hx11, hx13, hx19, hgframe, hg8w, hg18w, hgx8, hgx18, hgx19,
        hpayL, hexprL, hpayR, hexprR, hMemExt, hGmt,
        hsbL, hebL, hstbL, hsbR, hebR, hstbR,
        hArmFrame.saved8, hArmFrame.saved9, hArmFrame.saved18, hArmFrame.savedSp,
        hArmFrame.saved19, hArmFrame.bridge⟩
  exact ⟨c2, hs1.trans hs2, hExit⟩

/-! ## The field supplier -/

/-- The reached data from the entry: geometry and image from the landed entry
suppliers, the operand regions from the named premise. -/
theorem strCmpResid_of_entry (D : StrCmpOp) (C : D.Cert)
    {g gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' st'' : Vsa.While.St} {d env : Nat} {el er : Expr} {sl sr : String}
    {sp r sret aEnv aExpr v8 v9 v18 v19 : BitVec 64} {m0 : Mem} {c c' : Config}
    (he : EvalEntry g N A SL φf φc st d env (.binary D.op el er) sp r sret aEnv aExpr m0 c)
    (hf : BinaryArmFrame g gpre sp aExpr v8 v9 v18 v19)
    (hret : TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
      st' st'' (.str sl) (.str sr) sp r sret v8 v9 v18 m0 c')
    (hops : StrCmpOperandsAt sp c'.σ.mem) :
    StrCmpResid D gpre N A SL sp r sret aExpr c' :=
  { geom := C.tok_eq ▸ he.binaryPostGeom hf hret C.slot_of_rodata
      (fun _ h => FixedTextLoaded.Value_boolLoaded h) (by decide) (by decide) (by decide)
    image := he.binaryReturnImage hret
    ops := hops }

/-- **Residual 1 (shared by the four cells)** — at every actual return of both
children under a represented string-comparison entry, both payloads are
`strcmp`-admissible regions.  Supplier: the ownership layer's payload location
(arena or AST region) plus the arena/stack and static-image geometry of
`EvalGround`. -/
def StrCmpOperandsSupply : Prop :=
  ∀ (g gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d env : Nat) (op : BinOp) (el er : Expr) (sl sr : String)
    (sp r sret aEnv aExpr v8 v9 v18 v19 : BitVec 64) (m0 : Mem) (c c' : Config),
    EvalEntry g N A SL φf φc st d env (.binary op el er) sp r sret aEnv aExpr m0 c →
    BinaryArmFrame g gpre sp aExpr v8 v9 v18 v19 →
    TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
      st' st'' (.str sl) (.str sr) sp r sret v8 v9 v18 m0 c' →
    StrCmpOperandsAt sp c'.σ.mem

/-- **Residual 2 (shared by the four cells)** — the left string survives the
right child, at every represented string-comparison entry.  This is the
`hVlSurv` premise of `blockB_binary_data`; it is an OBSTRUCTION for arena
payloads (see `PROOF_CLOSURE_PLAN.md`), cured by amending `blockB_binary_data`
to retain the left temporary through the right child's actual exit. -/
def StrLeftSurvivesSupply : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d env : Nat) (op : BinOp) (el er : Expr) (sl : String)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config),
    EvalEntry g N A SL φf φc st d env (.binary op el er) sp r sret aEnv aExpr m0 c →
    EvalE st d env el st' (.str sl) →
    StrLeftSurvives N A SL sp sl

/-- **The cell supplier.**  Any string-comparison cell from its descriptor, its
certificate, and the two shared residuals. -/
theorem binStrCmpCell_of (D : StrCmpOp) (C : D.Cert)
    (hOps : StrCmpOperandsSupply) (hSurv : StrLeftSurvivesSupply) :
    BinStrCmpCell D.op D.bres := by
  intro st d env el er st' st'' sl sr hEl hEr ihL ihR
  intro g N A SL φf φc sp r sret aEnv aExpr m0
  exact binRow_strcmp D C g N A SL φf φc st st' st'' d env el er sl sr sp r sret aEnv aExpr m0
    hEl ihL ihR
    (EvalE.binary st d env D.op el er st' st'' (.str sl) (.str sr) _ hEl hEr (C.sem _ _ _))
    (fun c hc => hSurv g N A SL φf φc st st' d env D.op el er sl sp r sret aEnv aExpr m0 c hc hEl)
    (fun c hc gpre v8 v9 v18 v19 hf c2 hTS =>
      strCmpResid_of_entry D C hc hf hTS
        (hOps g gpre N A SL φf φc st st' st'' d env D.op el er sl sr
          sp r sret aEnv aExpr v8 v9 v18 v19 m0 c c2 hc hf hTS))

#print axioms strCmpKindEntry_of_twoSubReturn
#print axioms strCmpSeamGeom_of_resid
#print axioms blockC_strcmp_footprint
#print axioms blockC_strcmp
#print axioms evalStrCmpSim
#print axioms binRow_strcmp
#print axioms strCmpResid_of_entry
#print axioms binStrCmpCell_of

end Vsa.Sim
