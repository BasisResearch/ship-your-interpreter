import experiments.fleet.obstructions.RefutBatteryCur
open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Halts Diverges)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim

/-!
# Cure validation for the 11 int/eq falsities

`RefutBatteryCur.lean` proves the 11 fields FALSE via the `∅` countermodel; the
failing atom (the CTI) is `KindSlotPinned 6 0x800034e8 m0` — the EX_BINARY
jump-table slot, absent from `∅`.  The cure is the hypothesis `EvalEntry`, and
this file VALIDATES it the CEGIS way:

* `evalEntry_supplies_slot6` — `EvalEntry … m0 …` ENTAILS the exact failing atom
  (its `ground.table.slot6` is `KindSlotPinned 6 0x800034e8 c.σ.mem`, and
  `mem : c.σ.mem = m0`).  So carrying `EvalEntry` discharges the CTI.
* `evalEntry_empty_false` — `EvalEntry … ∅ …` is itself UNINHABITED, so the
  amended field `∀ …, EvalEntry … → BinIntCellResid …` is NOT refutable at the
  `∅` witness that killed the bare statement.  This is exactly why the 6
  unary/logic siblings (which already carry `EvalEntry`) are not false.

Kernel-certified, axiom-clean.  The failing atom is SMT-shaped (an array-lookup
`m[jumpTableBase+24]? = some _`); the repairing hypothesis is the semantic
`EvalEntry`, whose entailment of that atom the kernel projects directly.
-/

variable {g : (R : Register) → Option (RegisterType R)}
  {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
  {st : While.St} {d : Nat} {a : Addr} {e : Expr}
  {sp r sret aEnv aExpr : BitVec 64} {m0 : Mem} {c : Config}

/-- The cure hypothesis supplies the CTI: `EvalEntry` entails the slot-6 pin. -/
theorem evalEntry_supplies_slot6
    (he : EvalEntry g N A SL φf φc st d a e sp r sret aEnv aExpr m0 c) :
    KindSlotPinned 6 (0x800034e8#64) m0 :=
  he.mem ▸ he.ground.table.slot6

/-- `EvalEntry` is uninhabited at the `∅` witness — so the amended statement is
not refutable there (the countermodel that killed the bare field is gone). -/
theorem evalEntry_empty_false :
    ¬ EvalEntry g N A SL φf φc st d a e sp r sret aEnv aExpr (∅ : Mem) c := by
  intro he
  exact kindSlot6_empty_false _ (evalEntry_supplies_slot6 he)

#print axioms evalEntry_supplies_slot6
#print axioms evalEntry_empty_false
