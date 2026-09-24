import VsaIris.Interp.SeqLoopClosure

/-!
# The loop lemmas' statements (lane E6): `while`, `for`, the call arguments

INTERP_DESIGN.md §4.3. The statement only (xv6iris `spec-modules.md`): the
arms that enter these loops (E5's `while`/`for` arms, E4's call arm) take the
motives below as hypotheses; the proofs are `Interp/LoopWhile.lean`,
`Interp/LoopFor.lean` and `Interp/LoopArgs.lean`.

Every loop is stated at its loop HEAD inside the enclosing function's frame,
in the continuation form of G's `seqLoop` motives (`blockSeqT_body`): the
machine state `ms` at the head PC, the stack below the lowered `sp`, the AST,
the world; the continuation receives the machine state at the loop's exit.

* **`exec_stmt`'s `while` arm** (`0x8000403c`..`0x80004090`): the condition
  into the slot `sp+80`, copied to `sp+16` for `value_truthy`, the body
  through `exec_stmt` with the arm's own `ret` slot, `bne a0,1` then
  `beq a0,3`, back edge to the head.
* **`exec_stmt`'s `for` arm** after `env_new` (`0x8000423c`): the init
  statement (`ExecInit`, status discarded), then the loop head `0x8000426c`:
  the condition (if any) into `sp+104`, copied to `sp+16`, `value_truthy`
  (`ForCond`); the body; `beq a0,3`; the step (if any) into `sp+16`
  (`ExecStep`); back edge.
* **`eval_expr`'s call arm, the argument loop** (`0x800031dc`..`0x80003250`):
  argument `i` into the slot `sp+64`, its three words copied to
  `args[i] = sp+240+24*i`; the index spilled at `sp+16`, the count at
  `sp+24`.

The two statement loops leave at `loopExit status`: `0x8000409c` (the shared
epilogue, `a0 = 0`) on a normal end, `0x80004150` (the `ret` epilogue) on a
returned value. Each loop writes only the frame's scratch words (`W`); every
other byte of the frame is `Untouched`, which is how the arm's epilogue finds
its saved registers.

Total mode: the motives are D-free predicates over the cost relation's
indices; the case lemmas (one per constructor of `ExecSCost`'s `while*`, of
`ForLoopCost`, `ForCondCost`, `ExecStepCost`, `ExecInitCost`, `EvalArgsCost`)
take the children's specs and the motive of the recursive premise as
hypotheses, so A's recursor instantiates them. For `ExecSCost` the motive is
the conjunction `execSpecT_body D ∧ ∀ c b, sm = .whileStmt c b → whileT_body …`.

Partial mode: `whileP_body`/`forLoopP_body` are proved outright by Löb (the
back edge's `jal eval_expr` pays the later); `execInitP_body` and
`evalArgsP_body` by structure. The abort branch hands back the stack below
the lowered `sp`, the `ret` slot and the frame bytes (`blockSeqP_body`'s
shape).
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While

/-! ## Pure shapes -/

/-- An `exec_stmt` arm's registers inside its frame: the lowered `sp`, the
statement node (`s0`), the interpreter (`s1`), the `ret` slot (`s2`), the
frame pointer (`s3`). -/
structure StmtHead (R : Nat → BitVec 64) (s aS inp aRet aEnv : BitVec 64) : Prop where
  sp : R 2 = s + 18446744073709551440#64
  s0 : R 8 = aS
  s1 : R 9 = inp
  s2 : R 18 = aRet
  s3 : R 19 = aEnv

/-- The bytes of the frame `S` outside the written words `W` are unchanged. -/
def Untouched (S W : Nat → Prop) (Mt Mt' : Mem) : Prop :=
  ∀ a, S a → ¬ W a → imgM Mt' a = imgM Mt a

theorem Untouched.refl (S W : Nat → Prop) (Mt : Mem) : Untouched S W Mt Mt := fun _ _ _ => rfl

theorem Untouched.trans {S W : Nat → Prop} {M1 M2 M3 : Mem} (h1 : Untouched S W M1 M2)
    (h2 : Untouched S W M2 M3) : Untouched S W M1 M3 :=
  fun a hs hw => (h2 a hs hw).trans (h1 a hs hw)

/-- `exec_stmt`'s frame bytes `[s - 176, s)`. -/
abbrev execS (s : BitVec 64) : Nat → Prop := InExt (s.toNat - 176, 176)

/-- The scratch words the `while`/`for` loops write: `[sp+16, sp+128)` (the
`value_truthy` copy and step slot `sp+16`, the condition slots `sp+80` and
`sp+104`). The saved registers at `sp+136..` are outside. -/
abbrev execW (s : BitVec 64) : Nat → Prop := InExt (s.toNat - 176 + 16, 112)

/-- Where a `while`/`for` loop leaves `exec_stmt`: the `ret` epilogue on a
returned value, the shared epilogue (with `a0 = 0`) otherwise. -/
def loopExit : Status → BitVec 64
  | .ret _ => 0x80004150#64
  | _ => 0x8000409c#64

theorem loopExit_ret (v : Value) : loopExit (.ret v) = 0x80004150#64 := rfl
theorem loopExit_normal : loopExit .normal = 0x8000409c#64 := rfl

/-- What a `for` loop needs of its lowered stack `m'`: each present part fits
and bounds its closure bodies. -/
structure ForFits (d : Nat) (cnd step : Option Expr) (b : Stmt) (m' : Nat) : Prop where
  cond : ∀ c, cnd = some c → evalNeed c d ≤ m' ∧ c.bodiesBound perCallBudget = true
  step : ∀ e, step = some e → evalNeed e d ≤ m' ∧ e.bodiesBound perCallBudget = true
  body : execNeed b d ≤ m'
  bodyB : b.bodiesBound perCallBudget = true

/-- What a `while` loop needs of its lowered stack `m'`. -/
structure WhileFits (d : Nat) (c : Expr) (b : Stmt) (m' : Nat) : Prop where
  cond : evalNeed c d ≤ m'
  condB : c.bodiesBound perCallBudget = true
  body : execNeed b d ≤ m'
  bodyB : b.bodiesBound perCallBudget = true

/-- The `for` arm's registers after `env_new` returned the loop scope `a0`
(`0x8000423c`): the arm's registers, `s3` still the enclosing frame. -/
structure InitHead (R : Nat → BitVec 64) (s aS inp aRet aOuter : BitVec 64) : Prop where
  sp : R 2 = s + 18446744073709551440#64
  s0 : R 8 = aS
  s1 : R 9 = inp
  s2 : R 18 = aRet
  a0 : R 10 = aOuter

/-- What the `for` arm's init keeps: the callee-saved registers but `s3`,
which becomes the loop scope. -/
abbrev initKeep : List Nat := [2, 8, 9, 18, 20, 21, 22, 23, 24, 25, 26, 27]

/-- The argument loop's registers at its head `0x800031dc`: the lowered `sp`,
the call node (`s0`), the interpreter (`s2`), the frame pointer (`a3`), the
index (`a6`) and the count (`a5`, the `lw` of `argc`). -/
structure ArgsHead (R : Nat → BitVec 64) (s aX inp aE : BitVec 64) (idx argc : Nat) : Prop where
  sp : R 2 = s + 18446744073709550528#64
  s0 : R 8 = aX
  s2 : R 18 = inp
  a3 : R 13 = aE
  a6 : R 16 = BitVec.ofNat 64 idx
  a5 : R 15 = BitVec.ofNat 64 argc

/-- The argument array `args[32]` of the call arm: `sp + 240`. -/
abbrev argsBase (s : BitVec 64) : Nat := s.toNat - 1088 + 240

/-- The words the argument loop writes: the spills `[sp, sp+32)`, the
argument slot `[sp+64, sp+88)` and the array `[sp+240, sp+1008)`. The callee
value at `sp+96` and the saved registers at `sp+1016..` are outside. -/
def argsW (s : BitVec 64) (a : Nat) : Prop :=
  InExt (s.toNat - 1088, 32) a ∨ InExt (s.toNat - 1088 + 64, 24) a ∨
    InExt (argsBase s, 768) a

/-- What the argument loop keeps: the callee-saved registers and the count. -/
abbrev argsKeep : List Nat := [15, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

section Motive

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr
variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- The argument values already in `args[]`: `vs[j]` in the three words at
`base + 24 * (i + j)` of the image, persistent. -/
def argVals (N : NativeAddrs) (img : Nat → BitVec 8) (base : Nat) : Nat → List Value → IProp GF
  | _, [] => iprop(emp)
  | i, v :: vs => iprop(valImg N img (base + 24 * i) v ∗ argVals N img base (i + 1) vs)

instance (N : NativeAddrs) (img : Nat → BitVec 8) (base i : Nat) (vs : List Value) :
    Persistent (argVals (GF := GF) N img base i vs) := by
  induction vs generalizing i with
  | nil => unfold argVals; infer_instance
  | cons v vs ih => unfold argVals; infer_instance

variable (live : Nat → Prop) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)

/-! ### `while` -/

/-- **The `while` loop, total mode**: the motive of `ExecSCost` at a `while`
statement, stated at the loop head `0x8000403c` (the condition's `ld`). From
the head with `k + n` credits the loop runs against the derivation and leaves
at `loopExit status` with `a0` the status, the `ret` slot as `statusRet`, the
callee-saved registers kept and the frame outside the scratch words
unchanged. Cases: `whileT_false`, `whileT_break`, `whileT_ret`,
`whileT_loop`. -/
def whileT_body (st : St) (d env : Nat) (c : Expr) (b : Stmt) (st' : St) (status : Status)
    (n : Nat) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (k : Nat) (aS aEnv aRet s : BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) (m' : Nat),
    StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv → ExecFrameGeom s →
    StackGeom (s + 18446744073709551440#64) m' → WhileFits d c b m' → SlotGeom aRet →
    (ms 0x8000403c#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.whileStmt c b) ∗
      □ frameAt env aEnv.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 aRet.toNat ∗ world N L Room inp (.counted (k + n)) st d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms (loopExit status) R' (execS s) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ statusRet N aRet.toNat status -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)
      ⊢ (twpW (vsaModel live)).W Φ)

/-- **The `while` loop, partial mode** (proved outright by Löb, `whileP_all`):
from the loop head, the loop leaves with SOME outcome and its `ExecS`
derivation, or aborts, handing back the stack below the lowered `sp`, the
`ret` slot and the frame bytes. The two continuations are an additive pair
(INTERP_DESIGN.md §10.1). -/
def whileP_body (Core : IProp GF) (d env : Nat) (c : Expr) (b : Stmt) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (st : St) (aS aEnv aRet s : BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) (m' : Nat),
    StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv → ExecFrameGeom s →
    StackGeom (s + 18446744073709551440#64) m' → WhileFits d c b m' → SlotGeom aRet →
    (ms 0x8000403c#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.whileStmt c b) ∗
      □ frameAt env aEnv.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 aRet.toNat ∗ world N L Room inp .uncounted st d ∗
      evalSpecsP (vsaModel live) N L Room inp Core ∗ execSpecsP (vsaModel live) N L Room inp Core ∗
      ((∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st' : St) (status : Status),
        ⌜ExecS st d env (.whileStmt c b) st' status⌝ -∗
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms (loopExit status) R' (execS s) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ statusRet N aRet.toNat status -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ) ∧
       (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
          ownSet (execS s) byteAny) -∗ (wpW (vsaModel live)).W Φ))
      ⊢ (wpW (vsaModel live)).W Φ)

/-! ### `for` -/

/-- **The `for` loop, total mode**: the motive of `ForLoopCost`, stated at the
loop head `0x8000426c` (the condition field's `ld`) with the loop scope in
`s3`. Cases: `forLoopT_condFalse`, `forLoopT_bodyBreak`, `forLoopT_bodyRet`,
`forLoopT_loop`. -/
def forLoopT_body (st : St) (d env : Nat) (cnd step : Option Expr) (b : Stmt) (st' : St)
    (status : Status) (n : Nat) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (k : Nat) (init : Option Stmt) (aS aEnv aRet s : BitVec 64)
    (R : Nat → BitVec 64) (Mt : Mem) (m' : Nat),
    StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv → ExecFrameGeom s →
    StackGeom (s + 18446744073709551440#64) m' → ForFits d cnd step b m' → SlotGeom aRet →
    (ms 0x8000426c#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.forStmt init cnd step b) ∗
      □ frameAt env aEnv.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 aRet.toNat ∗ world N L Room inp (.counted (k + n)) st d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms (loopExit status) R' (execS s) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ statusRet N aRet.toNat status -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)
      ⊢ (twpW (vsaModel live)).W Φ)

/-- **The `for` condition, total mode**: the motive of `ForCondCost` (the
condition is absent or holds). From the loop head `0x8000426c` to the body's
call staging `0x800042a8`. Cases: `forCondT_none`, `forCondT_some`. -/
def forCondT_body (st : St) (d env : Nat) (cnd : Option Expr) (st' : St) (n : Nat) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (k : Nat) (init : Option Stmt) (step : Option Expr) (b : Stmt)
    (aS aEnv aRet s : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) (m' : Nat),
    StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv → ExecFrameGeom s →
    StackGeom (s + 18446744073709551440#64) m' → ForFits d cnd step b m' →
    (ms 0x8000426c#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.forStmt init cnd step b) ∗
      □ frameAt env aEnv.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      world N L Room inp (.counted (k + n)) st d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs calleeSaved R R' ∧ Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms 0x800042a8#64 R' (execS s) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)
      ⊢ (twpW (vsaModel live)).W Φ)

/-- **The `for` step, total mode**: the motive of `ExecStepCost`. From the
step field's `ld` `0x80004264` (after the body's status test) back to the
loop head `0x8000426c`. Cases: `execStepT_none`, `execStepT_some`. -/
def execStepT_body (st : St) (d env : Nat) (step : Option Expr) (st' : St) (n : Nat) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (k : Nat) (init : Option Stmt) (cnd : Option Expr) (b : Stmt)
    (aS aEnv aRet s : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) (m' : Nat),
    StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv → ExecFrameGeom s →
    StackGeom (s + 18446744073709551440#64) m' → ForFits d cnd step b m' →
    (ms 0x80004264#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.forStmt init cnd step b) ∗
      □ frameAt env aEnv.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      world N L Room inp (.counted (k + n)) st d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs calleeSaved R R' ∧ Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms 0x8000426c#64 R' (execS s) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)
      ⊢ (twpW (vsaModel live)).W Φ)

/-- **The `for` init, total mode**: the motive of `ExecInitCost`. From the
return of `env_new` (`0x8000423c`, the loop scope in `a0`) to the loop head
`0x8000426c` with the scope in `s3`; the init's status is discarded (C
ignores it), its `ret` slot contents too. The loop scope is `outer`.
Cases: `execInitT_none`, `execInitT_some`. -/
def execInitT_body (st : St) (d outer : Nat) (init : Option Stmt) (st' : St) (n : Nat) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (k : Nat) (cnd step : Option Expr) (b : Stmt)
    (aS aOuter aRet s : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) (m' : Nat),
    InitHead R s aS (BitVec.ofNat 64 inp) aRet aOuter → ExecFrameGeom s →
    StackGeom (s + 18446744073709551440#64) m' →
    (∀ i, init = some i → execNeed i d ≤ m' ∧ i.bodiesBound perCallBudget = true) →
    SlotGeom aRet →
    (ms 0x8000423c#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.forStmt init cnd step b) ∗
      □ frameAt outer aOuter.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 aRet.toNat ∗ world N L Room inp (.counted (k + n)) st d ∗
      (∀ (R' : Nat → BitVec 64),
        ⌜KeepRegs initKeep R R' ∧ R' 19 = aOuter⌝ -∗
        ms 0x8000426c#64 R' (execS s) Mt -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ slot24 aRet.toNat -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)
      ⊢ (twpW (vsaModel live)).W Φ)

/-- **The `for` loop, partial mode** (proved outright by Löb, `forLoopP_all`),
as `whileP_body`, with the `ForLoop` derivation. -/
def forLoopP_body (Core : IProp GF) (d env : Nat) (cnd step : Option Expr) (b : Stmt) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (st : St) (init : Option Stmt) (aS aEnv aRet s : BitVec 64)
    (R : Nat → BitVec 64) (Mt : Mem) (m' : Nat),
    StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv → ExecFrameGeom s →
    StackGeom (s + 18446744073709551440#64) m' → ForFits d cnd step b m' → SlotGeom aRet →
    (ms 0x8000426c#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.forStmt init cnd step b) ∗
      □ frameAt env aEnv.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 aRet.toNat ∗ world N L Room inp .uncounted st d ∗
      evalSpecsP (vsaModel live) N L Room inp Core ∗ execSpecsP (vsaModel live) N L Room inp Core ∗
      ((∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st' : St) (status : Status),
        ⌜ForLoop st d env cnd step b st' status⌝ -∗
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms (loopExit status) R' (execS s) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ statusRet N aRet.toNat status -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ) ∧
       (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
          ownSet (execS s) byteAny) -∗ (wpW (vsaModel live)).W Φ))
      ⊢ (wpW (vsaModel live)).W Φ)

/-- **The `for` init, partial mode** (proved outright, `execInitP_all`), as
`execInitT_body`, with the `ExecInit` derivation, or the abort. -/
def execInitP_body (Core : IProp GF) (d outer : Nat) (init : Option Stmt) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (st : St) (cnd step : Option Expr) (b : Stmt)
    (aS aOuter aRet s : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) (m' : Nat),
    InitHead R s aS (BitVec.ofNat 64 inp) aRet aOuter → ExecFrameGeom s →
    StackGeom (s + 18446744073709551440#64) m' →
    (∀ i, init = some i → execNeed i d ≤ m' ∧ i.bodiesBound perCallBudget = true) →
    SlotGeom aRet →
    (ms 0x8000423c#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.forStmt init cnd step b) ∗
      □ frameAt outer aOuter.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 aRet.toNat ∗ world N L Room inp .uncounted st d ∗
      execSpecsP (vsaModel live) N L Room inp Core ∗
      ((∀ (R' : Nat → BitVec 64) (st' : St),
        ⌜ExecInit st d outer init st'⌝ -∗ ⌜KeepRegs initKeep R R' ∧ R' 19 = aOuter⌝ -∗
        ms 0x8000426c#64 R' (execS s) Mt -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ slot24 aRet.toNat -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ) ∧
       (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
          ownSet (execS s) byteAny) -∗ (wpW (vsaModel live)).W Φ))
      ⊢ (wpW (vsaModel live)).W Φ)

/-! ### The call arguments -/

/-- **The argument loop, total mode**: the motive of `EvalArgsCost`, stated
at the loop head `0x800031dc` for a nonempty suffix `es = all.drop idx` of
the call's arguments `all` (the empty list never reaches the head: the arm's
`blez` skips the loop). `args[0..idx)` already hold `pre`; the loop leaves at
`0x80003254` with `args[0..argc)` holding `pre ++ vs`, the callee-saved
registers and the count kept, and the frame outside `argsW` unchanged.
Cases: `evalArgsT_cons` (`evalArgsT_nil` is vacuous). -/
def evalArgsT_body (st : St) (d env : Nat) (es : List Expr) (st' : St) (vs : List Value)
    (n : Nat) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (k idx : Nat) (f : Expr) (all : List Expr) (pre : List Value)
    (aX aE s : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) (m' : Nat),
    es ≠ [] → es = all.drop idx → pre.length = idx → all.length ≤ 32 →
    ArgsHead R s aX (BitVec.ofNat 64 inp) aE idx all.length → EvalFrameG s →
    StackGeom (s + 18446744073709550528#64) m' →
    (∀ x ∈ all, evalNeed x d ≤ m' ∧ x.bodiesBound perCallBudget = true) →
    (ms 0x800031dc#64 R (InExt (s.toNat - 1088, 1088)) Mt ∗ codeRes ∗
      □ astEG aX.toNat (.call f all) ∗ □ frameAt env aE.toNat ∗
      stackScratch (s + 18446744073709550528#64) m' ∗ argVals N (imgM Mt) (argsBase s) 0 pre ∗
      world N L Room inp (.counted (k + n)) st d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs argsKeep R R' ∧ R' 16 = BitVec.ofNat 64 all.length ∧
          Untouched (InExt (s.toNat - 1088, 1088)) (argsW s) Mt Mt'⌝ -∗
        ms 0x80003254#64 R' (InExt (s.toNat - 1088, 1088)) Mt' -∗
        argVals N (imgM Mt') (argsBase s) 0 (pre ++ vs) -∗
        stackScratch (s + 18446744073709550528#64) m' -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)
      ⊢ (twpW (vsaModel live)).W Φ)

/-- **The argument loop, partial mode** (proved outright by structure,
`evalArgsP_all`): each argument through the Löb hypothesis; the loop leaves
with SOME values and their `EvalArgs` derivation, or aborts as `eval_expr`
does (`ms_callEvalP`): the whole stack below `s` and the arm's result slot
`sret0` (owned as `Out`). -/
def evalArgsP_body (Core : IProp GF) (d env : Nat) (es : List Expr) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (st : St) (idx : Nat) (f : Expr) (all : List Expr)
    (pre : List Value) (aX aE s sret0 : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) (m' n0 : Nat)
    (Out : IProp GF),
    es ≠ [] → es = all.drop idx → pre.length = idx → all.length ≤ 32 →
    ArgsHead R s aX (BitVec.ofNat 64 inp) aE idx all.length → EvalFrameG s →
    StackGeom (s + 18446744073709550528#64) m' → m' + 1088 = n0 →
    (∀ x ∈ all, evalNeed x d ≤ m' ∧ x.bodiesBound perCallBudget = true) →
    (Out ⊢ slot24 sret0.toNat) →
    (ms 0x800031dc#64 R (InExt (s.toNat - 1088, 1088)) Mt ∗ codeRes ∗
      □ astEG aX.toNat (.call f all) ∗ □ frameAt env aE.toNat ∗
      stackScratch (s + 18446744073709550528#64) m' ∗ argVals N (imgM Mt) (argsBase s) 0 pre ∗
      world N L Room inp .uncounted st d ∗ Out ∗ evalSpecsP (vsaModel live) N L Room inp Core ∗
      ((∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st' : St) (vs : List Value),
        ⌜EvalArgs st d env es st' vs⌝ -∗
        ⌜KeepRegs argsKeep R R' ∧ R' 16 = BitVec.ofNat 64 all.length ∧
          Untouched (InExt (s.toNat - 1088, 1088)) (argsW s) Mt Mt'⌝ -∗
        ms 0x80003254#64 R' (InExt (s.toNat - 1088, 1088)) Mt' -∗
        argVals N (imgM Mt') (argsBase s) 0 (pre ++ vs) -∗
        stackScratch (s + 18446744073709550528#64) m' -∗
        world N L Room inp .uncounted st' d -∗ Out -∗ (wpW (vsaModel live)).W Φ) ∧
       (iprop(abortAt Core s n0 ∗ slot24 sret0.toNat) -∗ (wpW (vsaModel live)).W Φ))
      ⊢ (wpW (vsaModel live)).W Φ)

theorem evalArgsT_nil (st : St) (d env : Nat) :
    evalArgsT_body (GF := GF) live N L Room inp st d env [] st [] 0 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ h => absurd rfl h

theorem evalArgsP_nil (Core : IProp GF) (d env : Nat) :
    evalArgsP_body (GF := GF) live N L Room inp Core d env [] :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd rfl h

end Motive

end VsaIris.Interp
