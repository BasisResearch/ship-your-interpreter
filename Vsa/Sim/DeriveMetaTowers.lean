import Vsa.Sim.DeriveMeta
import Vsa.Sim.EvalSimCommon
import Vsa.Sim.EvalBinSim

/-!
# `DeriveMetaTowers` — `#derive_destructurer` on the two REAL towers

CLAUDE.md task #32 ("consuming a LANDED ∃/∧ tower ⇒ ONE named destructuring
lemma beside the tower, never positional projection chains") mechanized.
-- discipline: allow(R6-anon-projection-tower) the flagged text is the RULE QUOTE in this doc header, not code

The two towers picked by the task:

* `ArmEntryK` (`EvalSimCommon.lean`) — the recursive-arm entry package (~48
  top-level conjuncts, some `∃`-leaves).  Consumers today `obtain ⟨…48 idents…⟩`
  (see `rows/BinArmBridge.lean:221`).
* `TwoSubReturn` (`EvalBinSim.lean`) — the post-second-call package (16
  top-level conjuncts, nested `∃`-tower).  Consumers today `obtain` positionally
  (see `rows/BinIntReadback.lean:96`).

`#derive_destructurer` emits `<D>.Parts`/`<D>.destruct`/`<D>.mk'` for each; the
`example`s below consume through the named fields — no positional chains.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

#derive_destructurer ArmEntryK
#derive_destructurer TwoSubReturn

/-! ## Named-field consumers — no positional chains

Before: consumers `obtain ⟨…16/48 idents…⟩ := hTSR` (see the doc header).
After: `<Def>.destruct … h` yields a `<Def>.Parts` whose fields are named
`p1 … pN` (the generator's default; pass `fields …` to name them).  A consumer
extracts a specific conjunct by its field name — reorders of the tower no longer
shift a positional index. -/

open Vsa.Machine (Config)

-- `TwoSubReturn`'s 3rd conjunct is the dispatch-PC register fact; extract it by
-- NAME through the generated `.destruct` (no `.2.2` chain).
example
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat) (st' st'' : Vsa.While.St) (vl vr : Value)
    (sp r sret : BitVec 64) (v8 v9 v18 : BitVec 64) (m0 : Mem) (c : Config)
    (h : TwoSubReturn gpre N A SL φf φc nf nc st' st'' vl vr sp r sret v8 v9 v18 m0 c) :
    c.σ.regs.get? Register.PC = some (0x8000351c#64) :=
  (TwoSubReturn.destruct gpre N A SL φf φc nf nc st' st'' vl vr
    sp r sret v8 v9 v18 m0 c h).p3

-- `ArmEntryK`'s 3rd conjunct is its arm-PC register fact; same, by NAME.
example
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (armPC : BitVec 64) (calleeLoaded : Mem → Prop) (e : Expr)
    (sp r sret aExpr aEnv : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (m0 ment : Mem) (c : Config)
    (h : ArmEntryK g N A SL φf φc st armPC calleeLoaded e sp r sret aExpr aEnv
      v8 v9 v18 out0 m0 ment c) :
    c.σ.regs.get? Register.PC = some armPC :=
  (ArmEntryK.destruct g N A SL φf φc st armPC calleeLoaded e sp r sret aExpr aEnv
    v8 v9 v18 out0 m0 ment c h).p3

#print axioms ArmEntryK.destruct
#print axioms ArmEntryK.mk'
#print axioms TwoSubReturn.destruct
#print axioms TwoSubReturn.mk'

end Vsa.Sim
