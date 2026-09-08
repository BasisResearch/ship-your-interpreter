import Vsa.Sim.StrCmpCell
import Vsa.Sim.rows.StrCmpSignTail
import Vsa.Sim.CmpArmSeg
import Vsa.Sim.CmpTailSitesGen
import Vsa.Sim.rows.StrCmpOrderClose
import Vsa.Sim.FixedOperatorTable

/-!
# `StrCmpCellInstances` — the four string-comparison cells

One descriptor and one certificate per operator on the `StrCmpCell` layer; the
field suppliers `field_hStrLt_of` … take the two shared residuals
(`StrCmpOperandsSupply`, `StrLeftSurvivesSupply`).

| op | token | slot | sign tail | `jal value_bool` | `ld s3` | `j` |
|----|-------|------|-----------|------------------|---------|-----|
| lt | 20 | 0x80019fa8 | `sTailLt` | 0x800036c8 | 0x800036cc | 0x800036d0 |
| le | 21 | 0x80019fac | `sTailLe` | 0x80003b00 | 0x80003b04 | 0x80003b08 |
| gt | 22 | 0x80019fb0 | `sTailGt` | 0x80003aec | 0x80003af0 | 0x80003af4 |
| ge | 23 | 0x80019fb4 | `cmpFixupTail` | 0x800036c8 | 0x800036cc | 0x800036d0 |

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

/-! ## `<` -/

def strCmpLt : StrCmpOp :=
  { op := .lt, bres := fun sl sr => sl < sr, tok := 20, idx := 9#64, slotAddr := 0x80019fa8#64,
    slotDef := LtSlotPinned, tailSeg := sTailLt, vbPC := 0x800036c8#64, ldPC := 0x800036cc#64,
    jPC := 0x800036d0#64, jalImm := 0x1ff130#21, jImm := 0x1ffd1c#21 }

theorem strCmpLt_cert : strCmpLt.Cert :=
  { tok_eq := rfl
    tok_lt := by decide
    sem := fun _ _ _ => rfl
    order := strCmpOrderBridge_lt
    slot_of_rodata := fun _ h => FixedRodataLoaded.ltSlot h
    slot_pinned := fun _ h => h
    index := by decide
    slot_addr := by decide
    bltu := by decide
    slot_lo := by decide
    slot_hi := by decide
    slot_ht := by decide
    slot_al := by decide
    tail_ok := by show ChainOK 0x800036a4#64 [11, 12, 9] sTailLt; decide
    tail_avoid := by decide
    tail_facts := fun σ x sret lds h => sTailLt_facts σ x sret lds h
    tail_end := by
      intro x sret
      show chainEndPC 0x800036a4#64 (strCmpLt.tailL x sret) [] sTailLt = _
      rw [chainEndPC_eq_bt sTailLt _ _ _ (by decide)]
      rfl
    tail_log := fun _ _ _ => rfl
    tail_x11 := fun _ _ => rfl
    tail_x10 := fun _ _ => rfl
    jal_site := site_800036c8
    ld_site := site_800036cc
    j_site := site_800036d0
    jal_tgt := by apply BitVec.eq_of_toNat_eq; decide
    box_link := by decide
    ld_update := by decide
    ld_after := by decide
    j_tgt := by apply BitVec.eq_of_toNat_eq; decide
    j_tgt_al := by decide
    link_al := by decide }

/-! ## `≤` -/

def strCmpLe : StrCmpOp :=
  { op := .le, bres := fun sl sr => sl < sr || sl == sr, tok := 21, idx := 10#64,
    slotAddr := 0x80019fac#64, slotDef := LeSlotPinned, tailSeg := sTailLe,
    vbPC := 0x80003b00#64, ldPC := 0x80003b04#64, jPC := 0x80003b08#64,
    jalImm := 0x1fecf8#21, jImm := 0x1ff8e4#21 }

theorem strCmpLe_cert : strCmpLe.Cert :=
  { tok_eq := rfl
    tok_lt := by decide
    sem := fun _ _ _ => rfl
    order := strCmpOrderBridge_le
    slot_of_rodata := fun _ h => FixedRodataLoaded.leSlot h
    slot_pinned := fun _ h => h
    index := by decide
    slot_addr := by decide
    bltu := by decide
    slot_lo := by decide
    slot_hi := by decide
    slot_ht := by decide
    slot_al := by decide
    tail_ok := by show ChainOK 0x800036a4#64 [11, 12, 9] sTailLe; decide
    tail_avoid := by decide
    tail_facts := fun σ x sret lds h => sTailLe_facts σ x sret lds h
    tail_end := by
      intro x sret
      show chainEndPC 0x800036a4#64 (strCmpLe.tailL x sret) [] sTailLe = _
      rw [chainEndPC_eq_bt sTailLe _ _ _ (by decide)]
      rfl
    tail_log := fun _ _ _ => rfl
    tail_x11 := fun _ _ => rfl
    tail_x10 := fun _ _ => rfl
    jal_site := site_80003b00
    ld_site := site_80003b04
    j_site := site_80003b08
    jal_tgt := by apply BitVec.eq_of_toNat_eq; decide
    box_link := by decide
    ld_update := by decide
    ld_after := by decide
    j_tgt := by apply BitVec.eq_of_toNat_eq; decide
    j_tgt_al := by decide
    link_al := by decide }

/-! ## `>` -/

def strCmpGt : StrCmpOp :=
  { op := .gt, bres := fun sl sr => sr < sl, tok := 22, idx := 11#64, slotAddr := 0x80019fb0#64,
    slotDef := GtSlotPinned, tailSeg := sTailGt, vbPC := 0x80003aec#64, ldPC := 0x80003af0#64,
    jPC := 0x80003af4#64, jalImm := 0x1fed0c#21, jImm := 0x1ff8f8#21 }

theorem strCmpGt_cert : strCmpGt.Cert :=
  { tok_eq := rfl
    tok_lt := by decide
    sem := fun _ _ _ => rfl
    order := strCmpOrderBridge_gt
    slot_of_rodata := fun _ h => FixedRodataLoaded.gtSlot h
    slot_pinned := fun _ h => h
    index := by decide
    slot_addr := by decide
    bltu := by decide
    slot_lo := by decide
    slot_hi := by decide
    slot_ht := by decide
    slot_al := by decide
    tail_ok := by show ChainOK 0x800036a4#64 [11, 12, 9] sTailGt; decide
    tail_avoid := by decide
    tail_facts := fun σ x sret lds h => sTailGt_facts σ x sret lds h
    tail_end := by
      intro x sret
      show chainEndPC 0x800036a4#64 (strCmpGt.tailL x sret) [] sTailGt = _
      rw [chainEndPC_eq_bt sTailGt _ _ _ (by decide)]
      rfl
    tail_log := fun _ _ _ => rfl
    tail_x11 := fun _ _ => rfl
    tail_x10 := fun _ _ => rfl
    jal_site := site_80003aec
    ld_site := site_80003af0
    j_site := site_80003af4
    jal_tgt := by apply BitVec.eq_of_toNat_eq; decide
    box_link := by decide
    ld_update := by decide
    ld_after := by decide
    j_tgt := by apply BitVec.eq_of_toNat_eq; decide
    j_tgt_al := by decide
    link_al := by decide }

/-! ## `≥` -/

def strCmpGe : StrCmpOp :=
  { op := .ge, bres := fun sl sr => sr < sl || sl == sr, tok := 23, idx := 12#64,
    slotAddr := 0x80019fb4#64, slotDef := GeSlotPinned, tailSeg := cmpFixupTail,
    vbPC := 0x800036c8#64, ldPC := 0x800036cc#64, jPC := 0x800036d0#64,
    jalImm := 0x1ff130#21, jImm := 0x1ffd1c#21 }

theorem strCmpGe_cert : strCmpGe.Cert :=
  { tok_eq := rfl
    tok_lt := by decide
    sem := fun _ _ _ => rfl
    order := strCmpOrderBridge_ge
    slot_of_rodata := fun _ h => FixedRodataLoaded.geSlot h
    slot_pinned := fun _ h => h
    index := by decide
    slot_addr := by decide
    bltu := by decide
    slot_lo := by decide
    slot_hi := by decide
    slot_ht := by decide
    slot_al := by decide
    tail_ok := by show ChainOK 0x800036a4#64 [11, 12, 9] cmpFixupTail; decide
    tail_avoid := by decide
    tail_facts := fun σ x sret lds h => cmpFixupTail_facts σ x sret lds h
    tail_end := by
      intro x sret
      show chainEndPC 0x800036a4#64 (strCmpGe.tailL x sret) [] cmpFixupTail = _
      rw [chainEndPC_eq_bt cmpFixupTail _ _ _ (by decide)]
      rfl
    tail_log := fun _ _ _ => rfl
    tail_x11 := fun _ _ => rfl
    tail_x10 := fun _ _ => rfl
    jal_site := site_800036c8
    ld_site := site_800036cc
    j_site := site_800036d0
    jal_tgt := by apply BitVec.eq_of_toNat_eq; decide
    box_link := by decide
    ld_update := by decide
    ld_after := by decide
    j_tgt := by apply BitVec.eq_of_toNat_eq; decide
    j_tgt_al := by decide
    link_al := by decide }

/-! ## The four field suppliers -/

theorem ScaffoldRows.field_hStrLt_of (hOps : StrCmpOperandsSupply) (hSurv : StrLeftSurvivesSupply) :
    BinStrCmpCell .lt (fun sl sr => sl < sr) :=
  binStrCmpCell_of strCmpLt strCmpLt_cert hOps hSurv

theorem ScaffoldRows.field_hStrLe_of (hOps : StrCmpOperandsSupply) (hSurv : StrLeftSurvivesSupply) :
    BinStrCmpCell .le (fun sl sr => sl < sr || sl == sr) :=
  binStrCmpCell_of strCmpLe strCmpLe_cert hOps hSurv

theorem ScaffoldRows.field_hStrGt_of (hOps : StrCmpOperandsSupply) (hSurv : StrLeftSurvivesSupply) :
    BinStrCmpCell .gt (fun sl sr => sr < sl) :=
  binStrCmpCell_of strCmpGt strCmpGt_cert hOps hSurv

theorem ScaffoldRows.field_hStrGe_of (hOps : StrCmpOperandsSupply) (hSurv : StrLeftSurvivesSupply) :
    BinStrCmpCell .ge (fun sl sr => sr < sl || sl == sr) :=
  binStrCmpCell_of strCmpGe strCmpGe_cert hOps hSurv

#print axioms strCmpLt_cert
#print axioms strCmpLe_cert
#print axioms strCmpGt_cert
#print axioms strCmpGe_cert
#print axioms ScaffoldRows.field_hStrLt_of
#print axioms ScaffoldRows.field_hStrLe_of
#print axioms ScaffoldRows.field_hStrGt_of
#print axioms ScaffoldRows.field_hStrGe_of

end Vsa.Sim
