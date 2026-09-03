import Vsa
open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Halts Diverges)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Refine (Layout Loaded InterpSim)
open Vsa.Sim.Rows
open Vsa.Sim

/-!
# Certified falsity battery (current tree, wave 48k+)

Machine-checked refutations of the 11 int/eq `TermResidualsCore` fields, one
per field, all axiom-clean.  Nothing opaque: each is a KERNEL proof — the
wrapper (`BinIntCellResid`/`BinEqCellResid`) unfolds, its `∃`-body's
`BinArmExtras.slot6` demands a jump-table word absent from `∅`, contradiction.

This is stronger than an SMT countermodel and needs no solver: the falsity is a
term the kernel checks.  The cure for every one of these is identical — carry
`EvalEntry` as a hypothesis so the entry supplies the static pins (`slot6`,
`sproom`, `gx19_pres`); the 6 unary/logic siblings (`NegResid` …) already carry
it and are therefore NOT in this battery (their `∅`-instantiation is vacuously
true, not false).

**WAVE 49 — the cure LANDED.**  The 11 `TermResidualsCore` fields are no longer
stated in the bare form refuted below: they are `Vsa.Sim.BinIntCell` /
`Vsa.Sim.BinEqCell`, which carry the arm's `EvalEntry`.  The theorems here stay
as the historical record — each still proves exactly what it says, namely that
the BARE statement is false, which is why the amendment was needed.  The landed
shape's slot-verify + its vacuity at this very `∅` witness are in
`experiments/fleet/obstructions/B2CarryLanded.lean`, and `#sweep_refute` now
reports REFUTED=0 over all 58 fields (was 11).
-/

def witSt : Vsa.While.St := ⟨⟨#[], #[]⟩, ""⟩

/-- `KindSlotPinned 6 armPC ∅` is false: the four table bytes are absent. -/
theorem kindSlot6_empty_false (armPC : BitVec 64) :
    ¬ KindSlotPinned 6 armPC (∅ : Mem) := by
  rintro ⟨t0, _, _, _, hb0, _, _, _, _⟩
  simp at hb0

section
variable (L : Layout)

/-- Shared refuter for a `BinIntCellResid` field instantiated at `m0 = ∅`. -/
private theorem binInt_refuted (op : BinOp) (Resid) :
    ¬ (∀ g N A SL φf φc st st' st'' el er (a b : Int) sp r sret aExpr m0,
        BinIntCellResid op Resid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0) := by
  intro H
  obtain ⟨_, _, _, _, _, _, hX, _⟩ := H (fun _ => none) ⟨0,0,0⟩ ⟨0,0⟩ ⟨0,0⟩
    (fun _ => 0) (fun _ => 0) witSt witSt witSt .null .null 0 0
    (0#64) (0#64) (0#64) (0#64) (∅ : Mem)
  exact kindSlot6_empty_false _ hX.slot6

/-- Shared refuter for a `BinEqCellResid` field instantiated at `m0 = ∅`. -/
private theorem binEq_refuted (op : Vsa.Sim.EqNeOp) (opTok : BinOp)
    (link jalPC : BitVec 64) (jImm : BitVec 21) :
    ¬ (∀ g N A SL φf φc st st' st'' el er (vl vr : Value) sp r sret aExpr m0,
        BinEqCellResid op opTok link jalPC jImm g N A SL φf φc st st' st'' el er vl vr sp r sret aExpr m0) := by
  intro H
  obtain ⟨_, _, _, _, _, _, hX, _⟩ := H (fun _ => none) ⟨0,0,0⟩ ⟨0,0⟩ ⟨0,0⟩
    (fun _ => 0) (fun _ => 0) witSt witSt witSt .null .null .null .null
    (0#64) (0#64) (0#64) (0#64) (∅ : Mem)
  exact kindSlot6_empty_false _ hX.slot6

theorem field_hIAdd_refuted : ¬ (∀ g N A SL φf φc st st' st'' el er (a b : Int) sp r sret aExpr m0,
    BinIntCellResid .add Vsa.Sim.AddResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0) :=
  binInt_refuted _ _

theorem field_hISub_refuted : ¬ (∀ g N A SL φf φc st st' st'' el er (a b : Int) sp r sret aExpr m0,
    BinIntCellResid .sub Vsa.Sim.SubResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0) :=
  binInt_refuted _ _

theorem field_hIMul_refuted : ¬ (∀ g N A SL φf φc st st' st'' el er (a b : Int) sp r sret aExpr m0,
    BinIntCellResid .mul Vsa.Sim.MulResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0) :=
  binInt_refuted _ _

theorem field_hIMod_refuted : ¬ (∀ g N A SL φf φc st st' st'' el er (a b : Int) sp r sret aExpr m0,
    BinIntCellResid .mod Vsa.Sim.ModResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0) :=
  binInt_refuted _ _

theorem field_hILt_refuted : ¬ (∀ g N A SL φf φc st st' st'' el er (a b : Int) sp r sret aExpr m0,
    BinIntCellResid .lt Vsa.Sim.LtResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0) :=
  binInt_refuted _ _

theorem field_hILe_refuted : ¬ (∀ g N A SL φf φc st st' st'' el er (a b : Int) sp r sret aExpr m0,
    BinIntCellResid .le Vsa.Sim.LeResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0) :=
  binInt_refuted _ _

theorem field_hIGt_refuted : ¬ (∀ g N A SL φf φc st st' st'' el er (a b : Int) sp r sret aExpr m0,
    BinIntCellResid .gt Vsa.Sim.GtResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0) :=
  binInt_refuted _ _

theorem field_hIGe_refuted : ¬ (∀ g N A SL φf φc st st' st'' el er (a b : Int) sp r sret aExpr m0,
    BinIntCellResid .ge Vsa.Sim.GeResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0) :=
  binInt_refuted _ _

/-- `hIDiv` carries an extra guard `¬(a = -2^63 ∧ b = -1)`, discharged at `a=b=0`. -/
theorem field_hIDiv_refuted : ¬ (∀ g N A SL φf φc st st' st'' el er (a b : Int),
    ¬(a = -2^63 ∧ b = -1) → ∀ sp r sret aExpr m0,
    BinIntCellResid .div Vsa.Sim.DivResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0) := by
  intro H
  obtain ⟨_, _, _, _, _, _, hX, _⟩ := H (fun _ => none) ⟨0,0,0⟩ ⟨0,0⟩ ⟨0,0⟩
    (fun _ => 0) (fun _ => 0) witSt witSt witSt .null .null 0 0 (by decide)
    (0#64) (0#64) (0#64) (0#64) (∅ : Mem)
  exact kindSlot6_empty_false _ hX.slot6

theorem field_hEq_refuted : ¬ (∀ g N A SL φf φc st st' st'' el er (vl vr : Value) sp r sret aExpr m0,
    BinEqCellResid .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21)
      g N A SL φf φc st st' st'' el er vl vr sp r sret aExpr m0) :=
  binEq_refuted _ _ _ _ _

theorem field_hNe_refuted : ¬ (∀ g N A SL φf φc st st' st'' el er (vl vr : Value) sp r sret aExpr m0,
    BinEqCellResid .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21)
      g N A SL φf φc st st' st'' el er vl vr sp r sret aExpr m0) :=
  binEq_refuted _ _ _ _ _

end
