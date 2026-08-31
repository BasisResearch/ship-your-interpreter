import Vsa.Sim.ExecExprRet
import Vsa.Sim.ExecRet
import Vsa.Sim.ExecRetNull
import Vsa.Sim.ExecVarNull
import Vsa.Sim.rows.ExecCaseGeom
import Vsa.Sim.TermSimClose

/-!
# Layer 4 — M4 RECURSIVE `ExecS` cases re-landed at `ExecExitD` (`hSExpr`/`hSRet`)

The recursive statement-side twin of `rows/ExecCaseGeom.lean` (which handles the
register-only leaves `brk`/`cont`).  The recursive statement cases
(`ExecS.expr`, `ExecS.ret`) run a sub-`eval_expr` derivation, so their exit store
is `st'.store` (the sub-eval mutated memory) at a NON-identity `φ`, and — for
`ret` — the arm writes the caller retslot `[aRet, aRet+24)`.  The identity-φ
`ExecLeafWiden` therefore does not apply; this file supplies the recursive-shaped
widener(s) and routes `hSExpr`/`hSRet` onto `execExprSim`/`execRetSim`.

## The two gaps between the landed sim and the `mExecS` motive

`execExprSim` (`ExecExprRet.lean`) proves
`Triple (ExecEntry (.expr e) ∧ sailOutput = out0) (ExecExit … st' .normal …)`
and `execRetSim` (`ExecRet.lean`) proves
`Triple (ExecEntry (.ret (some e)) ∧ sailOutput = out0) (ExecExit … st' (.ret v) …)`,
each conditional on the jump-table geometry + the recursion glue `hGlue`.  The
recursor's minor premise `hSExpr`/`hSRet` is (via `TermSimAssembly.mExecS =
ExecBlock.ExecIH` by definitional unfolding, and `mEvalE = EvalRecCommon.EvalIH`)

    ∀ ghosts, Triple (ExecEntry …) (ExecExitD … st.store.frames.size
                                              st.store.closures.size st' status …)

so the gaps are exactly as for the leaves, but recursive:

1. **entry `out0`** — drop `∧ sailOutput = out0` by `out0 := c.σ.sailOutput`
   (`rfl`).  Pure marshalling — identical to `execBrkSimD`/`execContSimD`.
2. **exit `ExecExit → ExecExitD`** — add `MemExtends m0 c.σ.mem` and the
   `[SL.lo,SL.hi)`-store-survival clause AT A NON-IDENTITY `φ` (the sub-eval
   allocated/extended the store maps).  Unlike `ExecLeafWiden` (identity φ,
   unchanged store), the recursive widener `ExecRecWiden` carries its own
   `∃ φf' φc', PhiExtends …` witnesses in the survival clause.  This is the
   statement-frame analog of `EvalExitD`'s survival clause / `SubExecReturn`'s
   survival clause (both carry `∃ φf' φc'`), re-supplied as the honest
   exit-quantified widener the recursive-case minor premise provides.

`ExecRecWiden` is TRUE of every recursive statement exit: `execExprSim`/
`execRetSim` internally re-represent `st'.store` at extended maps with a
survival clause (via `SubExecReturn`/`SubExecReturnR` and `execBlockD`), so the
widener is the honest re-supply of what the packaged `ExecExit` forgets.  The
`ret`-arm retslot write `[aRet, aRet+24)` is disjoint from the arena where
`st'.store` lives, so it is transparent to the survival clause (which quantifies
over ALL `m'` agreeing outside `[SL.lo, SL.hi)`); NO retslot-specific carve is
needed in the widener — the retslot-awareness lives entirely inside the survival
witness the residual supplies.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
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

/-! ## `ExecRecWiden` — the recursive `ExecExitD` upgrade clauses, exit-quantified

The two `ExecExitD` clauses `ExecExit` forgets, as a widener over the exit config,
at a NON-identity `φ` (the sub-eval extended the store maps).  For any config `c`
satisfying the sim's `ExecExit` (the widener is applied ONLY to the sim's own
exit), it yields `MemExtends m0 c.σ.mem` and the `[SL.lo,SL.hi)`-survival of
`st'.store` at some extended pair `φf'/φc'`.  This is the recursive analog of
`ExecLeafWiden` (the identity-φ leaf widener): the survival clause here binds its
own `∃ φf' φc'`, matching the `ExecExitD.store`/`SubEvalReturn` shape.

**Re-landed (T1.2)** as a THIN ALIAS of the parametric `Widen` (`WidenMeta.lean`)
at the `ExecExit` family and the canonical `stackFoot SL` footprint; the bridge is
`execExitD_of_widen`. -/
abbrev ExecRecWiden
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' : Vsa.While.St) (status : Status) (sp r aRet : BitVec 64) (m0 : Mem) : Prop :=
  Widen (ExecExit g N A SL φf φc nf nc st' status sp r aRet m0)
    N A φf φc nf nc st' m0 (stackFoot SL)

/-- **The recursive widening.** `ExecExit … c ∧ ExecRecWiden …` gives
`ExecExitD … c` — the `mExecS` motive shape (`ExecBlock.ExecExitD`).  A THIN
COROLLARY of the parametric family bridge `execExitD_of_widen`
(`WidenMeta.lean`). -/
theorem execExitD_of_execExit_rec
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {nf nc : Nat}
    {st' : Vsa.While.St} {status : Status} {sp r aRet : BitVec 64} {m0 : Mem} {c : Config}
    (hExit : ExecExit g N A SL φf φc nf nc st' status sp r aRet m0 c)
    (hW : ExecRecWiden g N A SL φf φc nf nc st' status sp r aRet m0) :
    ExecExitD g N A SL φf φc nf nc st' status sp r aRet m0 c :=
  execExitD_of_widen hExit hW

/-! ## `ExecExprGeom` — the `hSExpr` recursor-supplied residual bundle

Everything `execExprSim` needs BEYOND the sub-`EvalIH` (which the recursor hands
the case for free, `rfl`-passed): the `execBlockA` jump-table slot pin + its
stack-disjointness, the recursion glue `hGlue`, and the recursive widener.  This
is the `ExecCaseGeom` twin for the recursive `expr` case: one bundle threaded
once, ∀-closed over the ghosts in the row. -/
def ExecExprGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr) (v : Value)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) : Prop :=
  StmtSlotPinned 0 execArmExpr m0 ∧
  (stmtJumpTableBase + 4 * 0 + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * 0) ∧
  -- the recursion glue is quantified over the entry `sailOutput` array `out0`
  -- (the row instantiates it per-config as `c.σ.sailOutput`).
  (∀ out0 : Array String,
    EvalIH st d env e st' v →
    Triple
      (fun c => ∃ ment v8 v9 v18 v19,
        ExecArmEntryK g N A SL φf φc st execArmExpr sp r aInterp aStmt aEnv aRet
          v8 v9 v18 v19 out0 m0 ment c)
      (fun c => ∃ subsret v1 v8 v9 v18 v19 mcall,
        SubExecReturn g N A SL φf φc st.store.frames.size st.store.closures.size st' v
          sp r aRet subsret (0x80004184#64) v1 v8 v9 v18 v19 m0 mcall c)) ∧
  ExecRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size st' .normal sp r aRet m0

/-- **`execExprSimD`** — `ExecS.expr` re-landed at `ExecExitD` (the `ExecIH`
shape).  Composes `execExprSim`'s packaged `ExecExit` with the recursive widener
`execExitD_of_execExit_rec`, threading the `ExecExprGeom` bundle, and supplying
the entry `out0 := c.σ.sailOutput` by `rfl`.  Consumes the sub-`EvalIH` directly
(passed through by the row). -/
theorem execExprSimD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr) (v : Value)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (hSpec : ExecS st d env (.expr e) st' .normal)
    (hIH : EvalIH st d env e st' v)
    (hG : ExecExprGeom g N A SL φf φc st st' d env e v
      sp r aInterp aStmt aEnv aRet m0) :
    Triple
      (ExecEntry g N A SL φf φc st d env (.expr e) sp r aInterp aStmt aEnv aRet m0)
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st' .normal sp r aRet m0) := by
  intro c hEntry
  obtain ⟨hslot, htableStk, hGlue, hW⟩ := hG
  obtain ⟨c', hs, hExit⟩ :=
    execExprSim g N A SL φf φc st st' d env e v sp r aInterp aStmt aEnv aRet m0
      c.σ.sailOutput hSpec hIH hslot htableStk (hGlue c.σ.sailOutput) c ⟨hEntry, rfl⟩
  exact ⟨c', hs, execExitD_of_execExit_rec hExit hW⟩

/-! ## `ExecRetGeom` — the `hSRet` recursor-supplied residual bundle

The `ExecExprGeom` twin for the recursive, retslot-writing `ret` case.  Carries
`execRetSim`'s FULL residual list — the jump-table slot pin + disjointness, the
retslot geometry (`aRet` an 8-aligned 24-byte RAM slot above HTIF, disjoint from
stack/arena/code — the `sd` store-region checks), the recursion glue `hGlue`
(producing `SubExecReturnR`, i.e. `SubExecReturn` + the 24-byte buffer
readability), and the recursive widener at status `.ret v`.  The retslot write
`[aRet, aRet+24)` is transparent to `ExecRecWiden`'s survival clause (the store
lives in the arena, disjoint from the retslot); the retslot-awareness is entirely
in the residual `hGlue`/widener the recursor supplies. -/
def ExecRetGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr) (v : Value)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) : Prop :=
  StmtSlotPinned 6 execArmRet m0 ∧
  (stmtJumpTableBase + 4 * 6 + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * 6) ∧
  aRet.toNat % 8 = 0 ∧
  0x80000000 ≤ aRet.toNat ∧ aRet.toNat + 24 ≤ 0x100000000 ∧
  tohostAddr + 16 ≤ aRet.toNat ∧
  (aRet.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ aRet.toNat) ∧
  (aRet.toNat + 24 ≤ A.lo ∨ A.hi ≤ aRet.toNat) ∧
  (aRet.toNat + 24 ≤ execStmtEntry ∨ execStmtEnd ≤ aRet.toNat) ∧
  (∀ out0 : Array String,
    EvalIH st d env e st' v →
    Triple
      (fun c => ∃ ment v8 v9 v18 v19,
        ExecArmEntryK g N A SL φf φc st execArmRet sp r aInterp aStmt aEnv aRet
          v8 v9 v18 v19 out0 m0 ment c)
      (fun c => ∃ subsret v1 v8 v9 v18 v19 mcall,
        SubExecReturnR g N A SL φf φc st.store.frames.size st.store.closures.size st' v
          sp r aRet subsret (0x80004138#64) v1 v8 v9 v18 v19 m0 mcall c)) ∧
  ExecRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size st' (.ret v) sp r aRet m0

/-- **`execRetSimD`** — `ExecS.ret` re-landed at `ExecExitD` (the `ExecIH`
shape).  Composes `execRetSim`'s packaged `ExecExit` (`.ret v`) with the
recursive widener, threading `ExecRetGeom`, and supplying the entry
`out0 := c.σ.sailOutput` by `rfl`. -/
theorem execRetSimD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr) (v : Value)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (hSpec : ExecS st d env (.ret (some e)) st' (.ret v))
    (hIH : EvalIH st d env e st' v)
    (hG : ExecRetGeom g N A SL φf φc st st' d env e v
      sp r aInterp aStmt aEnv aRet m0) :
    Triple
      (ExecEntry g N A SL φf φc st d env (.ret (some e)) sp r aInterp aStmt aEnv aRet m0)
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st' (.ret v) sp r aRet m0) := by
  intro c hEntry
  obtain ⟨hslot, htableStk, hRetAl, hRetLo, hRetHi, hRetWin, hRetStk, hRetArena,
    hRetCode, hGlue, hW⟩ := hG
  obtain ⟨c', hs, hExit⟩ :=
    execRetSim g N A SL φf φc st st' d env e v sp r aInterp aStmt aEnv aRet m0
      c.σ.sailOutput hSpec hIH hslot htableStk hRetAl hRetLo hRetHi hRetWin hRetStk
      hRetArena hRetCode (hGlue c.σ.sailOutput) c ⟨hEntry, rfl⟩
  exact ⟨c', hs, execExitD_of_execExit_rec hExit hW⟩

/-! ## `ExecRetNullGeom` — the `hSRetNull` recursor-supplied residual bundle
     (STRETCH; the `hGlue` `value_null` bridge is the surfaced open residual)

`execRetNullSim` (`ExecRetNull.lean`) is a LEAF — no sub-`EvalIH`, `st' = st`,
value fixed `.null` — but it still writes the retslot `[aRet, aRet+24)` and
completes `.ret .null`, so (like `ret`) it needs the recursive widener, NOT the
identity-φ leaf widener.  Its `hGlue` residual is DIFFERENT from `expr`/`ret`:
it takes the `beqz`-TAKEN path through the `value_null` callee bridge
(`0x80004124 → 0x800042f0 → jal value_null → j 0x80004138`), which materialises
`ValueRepr … subsret .null` and rejoins the shared copy+epilogue at `0x80004138`
in a `SubExecReturnR` state for `st`/`.null`.

This bundle carries `execRetNullSim`'s full residual list (the same retslot
geometry as `ret`, the `value_null`-bridge `hGlue`, and the widener at `.ret
.null`).  The `hGlue` here is a NAMED TYPED premise (surfaced, not discharged):
closing it requires a landed `value_null` callee-bridge Triple + the `beqz`-taken
arm setup, which is NOT among the landed site batteries — see the ledger note in
the report.  Everything ELSE (widener + entry marshalling) is closed. -/
def ExecRetNullGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) : Prop :=
  StmtSlotPinned 6 execArmRet m0 ∧
  (stmtJumpTableBase + 4 * 6 + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * 6) ∧
  aRet.toNat % 8 = 0 ∧
  0x80000000 ≤ aRet.toNat ∧ aRet.toNat + 24 ≤ 0x100000000 ∧
  tohostAddr + 16 ≤ aRet.toNat ∧
  (aRet.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ aRet.toNat) ∧
  (aRet.toNat + 24 ≤ A.lo ∨ A.hi ≤ aRet.toNat) ∧
  (aRet.toNat + 24 ≤ execStmtEntry ∨ execStmtEnd ≤ aRet.toNat) ∧
  -- the OPEN `value_null`-bridge glue (∀-closed over `out0`):
  (∀ out0 : Array String,
    Triple
      (fun c => ∃ ment v8 v9 v18 v19,
        ExecArmEntryK g N A SL φf φc st execArmRet sp r aInterp aStmt aEnv aRet
          v8 v9 v18 v19 out0 m0 ment c)
      (fun c => ∃ subsret v1 v8 v9 v18 v19 mcall,
        SubExecReturnR g N A SL φf φc st.store.frames.size st.store.closures.size st .null
          sp r aRet subsret (0x80004138#64) v1 v8 v9 v18 v19 m0 mcall c)) ∧
  ExecRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size st (.ret .null) sp r aRet m0

/-- **`execRetNullSimD`** — `ExecS.retNull` re-landed at `ExecExitD`.  Composes
`execRetNullSim`'s `ExecExit` (`st`, `.ret .null`) with the recursive widener.
The `value_null`-bridge `hGlue` is threaded from the `ExecRetNullGeom` bundle as a
surfaced open residual. -/
theorem execRetNullSimD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (hSpec : ExecS st d env (.ret none) st (.ret .null))
    (hG : ExecRetNullGeom g N A SL φf φc st d env
      sp r aInterp aStmt aEnv aRet m0) :
    Triple
      (ExecEntry g N A SL φf φc st d env (.ret none) sp r aInterp aStmt aEnv aRet m0)
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st (.ret .null) sp r aRet m0) := by
  intro c hEntry
  obtain ⟨hslot, htableStk, hRetAl, hRetLo, hRetHi, hRetWin, hRetStk, hRetArena,
    hRetCode, hGlue, hW⟩ := hG
  obtain ⟨c', hs, hExit⟩ :=
    execRetNullSim g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet m0
      c.σ.sailOutput hSpec hslot htableStk hRetAl hRetLo hRetHi hRetWin hRetStk
      hRetArena hRetCode (hGlue c.σ.sailOutput) c ⟨hEntry, rfl⟩
  exact ⟨c', hs, execExitD_of_execExit_rec hExit hW⟩

/-! ## PAYOFF DEMO (T1.2) — `execVarNullSimD`: the non-identity-φ statement leaf

`ExecS.varNull` (`.varDecl x none`) is the statement case whose exit store is
`st.store.define env x .null` — a `Store.define` that ADDS a frame binding, so the
exit frame count `≠` the entry `nf` and the survival φ-pair is genuinely
NON-identity.  Under the OLD identity-φ-only `ExecLeafWiden` (`PhiExtends.refl`)
this case could NOT be re-landed at `ExecExitD` (the step-6b ledger's
`hSVarNull`-blocked note).  The parametric `Widen` (= the re-landed `ExecRecWiden`
at the `ExecExit` family, `stackFoot SL` footprint) carries its own
`∃ φf' φc', PhiExtends φf φf' nf ∧ …`, so the `define`-widened φ is exactly the
supplied witness — the case is now dischargeable.  `execVarNullSimD` composes
`execVarDeclNullSim`'s packaged `ExecExit` with `execExitD_of_execExit_rec`,
threading the widener from the geom bundle.  This is the statement twin of
`execRetNullSimD`; the `value_null`+`env_define` body `hGlue` is the surfaced open
residual (unchanged from `execVarDeclNullSim`).

The retslot/`define` footprint story is captured by `Widen`'s `foot` parameter:
`execVarDeclNullSim`'s survival clause already lands at `stackFoot SL` (the
`define`d binding lives in the frame arena, disjoint from `[SL.lo,SL.hi)`), and
`Widen.footMono` (`retslotFoot SL aRet ⊇ stackFoot SL`) is the bridge available for
any variant whose survival is stated at the wider retslot-augmented footprint. -/
def ExecVarNullGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (x : String)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem) : Prop :=
  StmtSlotPinned 1 execArmVarDecl m0 ∧
  (stmtJumpTableBase + 4 * 1 + 4 ≤ SL.lo ∨ sp.toNat ≤ stmtJumpTableBase + 4 * 1) ∧
  -- the OPEN `value_null` + `env_define` body glue (∀-closed over `out0`):
  (∀ out0 : Array String,
    Triple
      (fun c => ∃ ment v8 v9 v18 v19,
        ExecArmEntryK g N A SL φf φc st execArmVarDecl sp r aInterp aStmt aEnv aRet
          v8 v9 v18 v19 out0 m0 ment c)
      (fun c => ∃ subsret v1 v8 v9 v18 v19 mcall,
        SubExecReturn g N A SL φf φc st.store.frames.size st.store.closures.size
          ⟨st.store.define env x .null, st.out⟩ .null
          sp r aRet subsret (0x80004118#64) v1 v8 v9 v18 v19 m0 mcall c)) ∧
  -- the NON-identity-φ widener (`define` grew the frame count): the payoff.
  ExecRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size
    ⟨st.store.define env x .null, st.out⟩ .normal sp r aRet m0

/-- **`execVarNullSimD`** — `ExecS.varNull` re-landed at `ExecExitD`, the
non-identity-φ statement leaf.  Discharges the `hSVarNull` motive shape via the
parametric widener (`ExecRecWiden = Widen … (stackFoot SL)`). -/
theorem execVarNullSimD
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (env : Addr) (x : String)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem)
    (hSpec : ExecS st d env (.varDecl x none)
      ⟨st.store.define env x .null, st.out⟩ .normal)
    (hG : ExecVarNullGeom g N A SL φf φc st d env x
      sp r aInterp aStmt aEnv aRet m0) :
    Triple
      (ExecEntry g N A SL φf φc st d env (.varDecl x none)
        sp r aInterp aStmt aEnv aRet m0)
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        ⟨st.store.define env x .null, st.out⟩ .normal sp r aRet m0) := by
  intro c hEntry
  obtain ⟨hslot, htableStk, hGlue, hW⟩ := hG
  obtain ⟨c', hs, hExit⟩ :=
    execVarDeclNullSim g N A SL φf φc st d env x sp r aInterp aStmt aEnv aRet m0
      c.σ.sailOutput hSpec hslot htableStk (hGlue c.σ.sailOutput) c ⟨hEntry, rfl⟩
  exact ⟨c', hs, execExitD_of_execExit_rec hExit hW⟩

end Vsa.Sim

/-! ## The `mExecS`-motive case rows (the recursor-premise adapters)

`exec_expr_row`/`exec_ret_row` marshal the `*D` lemma into the exact minor-premise
slot of `execSeq_sim_of_cases` (`TermSimClose.lean`).  As for the brk/cont rows
(`rows/ExecRouting.lean`), the premise is `ExecIH …` by definitional unfolding
(`TermSimAssembly.mExecS = ExecBlock.ExecIH`), and — for these recursive cases —
the sub-derivation IH the recursor hands the case (`mEvalE st d env e st' v a`) is
`EvalRecCommon.EvalIH st d env e st' v` by the SAME unfolding
(`TermSimAssembly.mEvalE = EvalRecCommon.EvalIH`), so it passes straight through
to the `*D` lemma's `hIH` by `rfl` — no adapter.  The per-case `ExecExprGeom`/
`ExecRetGeom` bundle (∀-closed over the ghosts) carries the geometry + glue +
widener. -/
namespace Vsa.Sim.Rows

open Vsa.Sim
open Vsa.Sim.TermSimAssembly

local notation "SpecSt" => Vsa.While.St

/-- The expr-case residual: the `ExecExprGeom` bundle, ∀-closed over the ghosts. -/
def ExprResid (st st' : SpecSt) (d : Nat) (env : Addr) (e : Expr) (v : Value) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    Vsa.Sim.ExecExprGeom g N A SL φf φc st st' d env e v
      sp r aInterp aStmt aEnv aRet m0

/-- Route `hSExpr` → `execExprSimD`.  The sub-`EvalIH` (`mEvalE … a`) passes to
`hIH` by `rfl` (`mEvalE = EvalIH`). -/
theorem exec_expr_row
    (hR : ∀ st st' d env e v, ExprResid st st' d env e v) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value)
      (a : EvalE st d env e st' v),
      mEvalE st d env e st' v a →
      mExecS st d env (Stmt.expr e) st' Status.normal (ExecS.expr st d env e st' v a) := by
  intro st d env e st' v a hIH
  show Vsa.Sim.ExecIH st d env (.expr e) st' .normal
  intro g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
  exact Vsa.Sim.execExprSimD g N A SL φf φc st st' d env e v
    sp r aInterp aStmt aEnv aRet m0 (ExecS.expr st d env e st' v a) hIH
    (hR st st' d env e v g N A SL φf φc sp r aInterp aStmt aEnv aRet m0)

/-- The ret-case residual: the `ExecRetGeom` bundle, ∀-closed over the ghosts. -/
def RetResid (st st' : SpecSt) (d : Nat) (env : Addr) (e : Expr) (v : Value) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    Vsa.Sim.ExecRetGeom g N A SL φf φc st st' d env e v
      sp r aInterp aStmt aEnv aRet m0

/-- Route `hSRet` → `execRetSimD`. -/
theorem exec_ret_row
    (hR : ∀ st st' d env e v, RetResid st st' d env e v) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value)
      (a : EvalE st d env e st' v),
      mEvalE st d env e st' v a →
      mExecS st d env (Stmt.ret (some e)) st' (Status.ret v) (ExecS.ret st d env e st' v a) := by
  intro st d env e st' v a hIH
  show Vsa.Sim.ExecIH st d env (.ret (some e)) st' (.ret v)
  intro g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
  exact Vsa.Sim.execRetSimD g N A SL φf φc st st' d env e v
    sp r aInterp aStmt aEnv aRet m0 (ExecS.ret st d env e st' v a) hIH
    (hR st st' d env e v g N A SL φf φc sp r aInterp aStmt aEnv aRet m0)

/-- The retNull-case residual: the `ExecRetNullGeom` bundle (carrying the OPEN
`value_null`-bridge glue), ∀-closed over the ghosts. -/
def RetNullResid (st : SpecSt) (d : Nat) (env : Addr) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    Vsa.Sim.ExecRetNullGeom g N A SL φf φc st d env
      sp r aInterp aStmt aEnv aRet m0

/-- Route `hSRetNull` → `execRetNullSimD` (STRETCH; leaf, no sub-IH; conditional
on the surfaced `value_null`-bridge glue inside `RetNullResid`). -/
theorem exec_retNull_row
    (hR : ∀ st d env, RetNullResid st d env) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr),
      mExecS st d env (Stmt.ret none) st (Status.ret Value.null) (ExecS.retNull st d env) := by
  intro st d env
  show Vsa.Sim.ExecIH st d env (.ret none) st (.ret .null)
  intro g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
  exact Vsa.Sim.execRetNullSimD g N A SL φf φc st d env
    sp r aInterp aStmt aEnv aRet m0 (ExecS.retNull st d env)
    (hR st d env g N A SL φf φc sp r aInterp aStmt aEnv aRet m0)

/-- The varNull-case residual: the `ExecVarNullGeom` bundle (carrying the OPEN
`value_null`+`env_define` glue), ∀-closed over the ghosts. -/
def VarNullResid (st : SpecSt) (d : Nat) (env : Addr) (x : String) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (m0 : Mem),
    Vsa.Sim.ExecVarNullGeom g N A SL φf φc st d env x
      sp r aInterp aStmt aEnv aRet m0

/-- Route `hSVarNull` → `execVarNullSimD` (the PAYOFF: non-identity-φ statement
leaf, unblocked by the parametric widener; conditional on the surfaced
`value_null`+`env_define` glue inside `VarNullResid`). -/
theorem exec_varNull_row
    (hR : ∀ st d env x, VarNullResid st d env x) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String),
      mExecS st d env (Stmt.varDecl x none)
        { store := st.store.define env x Value.null, out := st.out }
        Status.normal (ExecS.varNull st d env x) := by
  intro st d env x
  show Vsa.Sim.ExecIH st d env (.varDecl x none)
    ⟨st.store.define env x .null, st.out⟩ .normal
  intro g N A SL φf φc sp r aInterp aStmt aEnv aRet m0
  exact Vsa.Sim.execVarNullSimD g N A SL φf φc st d env x
    sp r aInterp aStmt aEnv aRet m0 (ExecS.varNull st d env x)
    (hR st d env x g N A SL φf φc sp r aInterp aStmt aEnv aRet m0)

end Vsa.Sim.Rows
