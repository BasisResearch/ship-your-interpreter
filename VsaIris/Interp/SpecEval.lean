import VsaIris.Interp.Code
import VsaIris.Interp.Repr
import VsaIris.Interp.Need
import VsaIris.Stack
import Vsa.While.Cost

/-!
# `eval_expr`'s specs: the statement (lane G)

INTERP_DESIGN.md §4 and §6. The statement only: no code proof is imported
(`Proof*`/`Case*` files take these as hypotheses, xv6iris `spec-modules.md`).
It supersedes `Specs.lean` §D for `eval_expr`; the changes and their reasons
are recorded in INTERP_DESIGN.md §10 ("STATEMENT CHANGES (G)"):

* **ABI.** `a0 = sret`, `a1 = in`, `a2 = e`, `a3 = env` (the C signature
  `eval_expr(Interp *in, Expr *e, Env *env)` with an `sret` result; the
  prologue keeps `a1` in `s2` and passes it to both children and to
  `runtime_error`, and the binary arm spills `a3` for the right child).
* **Registers are one valuation.** A body spills `s0`-`s3` and clobbers the
  temporaries whatever its caller passed, so the precondition owns every
  register but `PC`/`ra` (handled by `fnSpecW`) and `gp`/`tp` as ONE valuation
  `regFile rv` with named argument pins (`EvalRegs`); the postcondition hands
  back some `rv'` that agrees with `rv` on the callee-saved registers and
  `sp` (`KeepRegs`). A symbolic run (`SWP`) consumes exactly this shape.
* **The code image and `gp`** are persistent resources in the precondition
  (`codeRes`): a segment fetches its instructions, and the runs pin `gp`.
* **AST geometry.** `astEG` is `astE` plus the read set's address facts
  (RAM, off the HTIF words), which every load side condition needs; A0 supplies
  them from `ast_readable`, and `astEG_astE` forgets them.
* **Stack and slot geometry** are named structures (`StackGeom`, `SlotGeom`).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

section Regs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The registers a function body owns besides `PC` and `ra`: every GPR but
`x0`, `gp`, `tp`. -/
abbrev fRegs : List Nat :=
  [2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
    29, 30, 31]

/-- The callee-saved registers and `sp`: what a returning call keeps. -/
abbrev calleeSaved : List Nat := [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- The body's registers at the valuation `rv`. -/
def regFile (rv : Nat → BitVec 64) : IProp GF := sepL fRegs (fun r => r ↦ᵣ rv r)

/-- `rv'` keeps `rv`'s values on the registers `keep`. -/
def KeepRegs (keep : List Nat) (rv rv' : Nat → BitVec 64) : Prop := ∀ x ∈ keep, rv' x = rv x

/-- The interpreter's code and jump tables, and `gp`, persistent. -/
def codeRes : IProp GF := roOwn roR interpText

instance : Persistent (codeRes (GF := GF)) := by unfold codeRes; infer_instance

end Regs

/-! ## Pure geometry -/

/-- A byte a load may read: RAM, off the HTIF words. `win` is the string
routines' over-read window from the byte (H1's `SharedWin`): `strlen` and
`strcmp` load whole aligned words, so every string of an AST view needs its
8-byte window (E1, INTERP_DESIGN.md §10 "STATEMENT CHANGES (E1)"). -/
structure ReadOK (k : Nat) : Prop where
  lo : 0x80000000 ≤ k
  hi : k < 0x100000000
  off : k < Vsa.Sim.tohostAddr ∨ Vsa.Sim.tohostAddr + 16 ≤ k
  win : k + 8 ≤ 0x100000000 ∧ (k + 8 ≤ Vsa.Sim.tohostAddr ∨ Vsa.Sim.tohostAddr + 16 ≤ k)

/-- A stack pointer `s` with `n` owned bytes below it, inside the stack
segment (`stackSL`), 16-aligned. -/
structure StackGeom (s : BitVec 64) (n : Nat) : Prop where
  le : n ≤ s.toNat
  lo : Vsa.Sim.LayoutInstance.stackSL.lo ≤ s.toNat - n
  hi : s.toNat ≤ Vsa.Sim.LayoutInstance.stackSL.hi
  al : s.toNat % 16 = 0

/-- A 24-byte value slot the callee may store to: 8-aligned, RAM, off HTIF. -/
structure SlotGeom (a : BitVec 64) : Prop where
  al : a.toNat % 8 = 0
  lo : Vsa.Sim.tohostAddr + 16 ≤ a.toNat
  hi : a.toNat + 24 ≤ 0x100000000

/-- `eval_expr`'s argument registers. -/
structure EvalRegs (rv : Nat → BitVec 64) (sret inp aX aE s : BitVec 64) : Prop where
  a0 : rv 10 = sret
  a1 : rv 11 = inp
  a2 : rv 12 = aX
  a3 : rv 13 = aE
  sp : rv 2 = s

/-- `exec_stmt`'s argument registers (`a0 = in`, `a1 = s`, `a2 = env`,
`a3 = ret`; INTERP_DESIGN.md §4). -/
structure ExecRegs (rv : Nat → BitVec 64) (inp aS aE aRet s : BitVec 64) : Prop where
  a0 : rv 10 = inp
  a1 : rv 11 = aS
  a2 : rv 12 = aE
  a3 : rv 13 = aRet
  sp : rv 2 = s

/-- The binary's `ExecStatus` (`Vsa.Sim.StatusCode`). -/
def statusCode : Status → BitVec 64
  | .normal => 0#64
  | .brk => 1#64
  | .cont => 2#64
  | .ret _ => 3#64

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- Persistent AST ownership with its read set's address facts. -/
def astEG (a : Nat) (e : Expr) : IProp GF :=
  iprop(∃ (P : Nat → Prop) (m : Mem), ⌜ExprReprWithin m P a e ∧ ∀ k, P k → ReadOK k⌝ ∗ roOn P m)

instance (a : Nat) (e : Expr) : Persistent (astEG (GF := GF) a e) := by
  unfold astEG; infer_instance

theorem astEG_astE (a : Nat) (e : Expr) : astEG (GF := GF) a e ⊢ astE a e := by
  unfold astEG astE
  iintro ⟨%P, %m, %⟨h, _⟩, H⟩
  iexists P, m
  iframe H
  ipureintro; exact h

/-- Persistent statement ownership with its read set's address facts. -/
def astSG (a : Nat) (s : Stmt) : IProp GF :=
  iprop(∃ (P : Nat → Prop) (m : Mem), ⌜StmtReprWithin m P a s ∧ ∀ k, P k → ReadOK k⌝ ∗ roOn P m)

instance (a : Nat) (s : Stmt) : Persistent (astSG (GF := GF) a s) := by
  unfold astSG; infer_instance

theorem astSG_astS (a : Nat) (s : Stmt) : astSG (GF := GF) a s ⊢ astS a s := by
  unfold astSG astS
  iintro ⟨%P, %m, %⟨h, _⟩, H⟩
  iexists P, m
  iframe H
  ipureintro; exact h

/-- The `ret` slot: the returned value when the status is `.ret v`, any
contents otherwise. -/
def statusRet (N : NativeAddrs) (aRet : Nat) : Status → IProp GF
  | .ret v => valAt N aRet v
  | _ => slot24 aRet

omit I in
theorem statusRet_normal [InterpGS GF] (N : NativeAddrs) (a : Nat) :
    statusRet (GF := GF) N a .normal = slot24 a := rfl

variable (M : MachineModel) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)

def evalEntryPC : BitVec 64 := 0x80003164#64
def execEntryPC : BitVec 64 := 0x80003fe0#64

/-- `eval_expr`'s entry resources: the registers (`sret`, `in`, the node, the
frame pointer, `sp`), the code, the AST, the frame binding, the stack below
`s`, the result slot and the world. -/
def evalPre (ρ : Regime) (st : St) (d env : Nat) (e : Expr) (sret aE aX s : BitVec 64)
    (rv : Nat → BitVec 64) : IProp GF :=
  iprop(regFile rv ∗ ⌜EvalRegs rv sret (BitVec.ofNat 64 inp) aX aE s⌝ ∗ codeRes ∗
    □ astEG aX.toNat e ∗ □ frameAt env aE.toNat ∗
    stackScratch s (evalNeed e d) ∗ ⌜StackGeom s (evalNeed e d)⌝ ∗
    slot24 sret.toNat ∗ ⌜SlotGeom sret⌝ ∗ ⌜e.bodiesBound perCallBudget = true⌝ ∗
    world N L Room inp ρ st d)

/-- `eval_expr`'s exit resources: the callee-saved registers and `sp` kept,
the stack returned, the value in the slot, the world advanced. -/
def evalPost (ρ : Regime) (st' : St) (d : Nat) (e : Expr) (v : Value) (sret s : BitVec 64)
    (rv : Nat → BitVec 64) : IProp GF :=
  iprop(∃ rv', regFile rv' ∗ ⌜KeepRegs calleeSaved rv rv'⌝ ∗
    stackScratch s (evalNeed e d) ∗ valAt N sret.toNat v ∗ world N L Room inp ρ st' d)

/-- **`eval_expr`, total, derivation-indexed** (INTERP_DESIGN.md §4.1). -/
def evalSpecT_body (st : St) (d env : Nat) (e : Expr) (st' : St) (v : Value) (n : Nat)
    (_D : EvalECost st d env e st' v n) : IProp GF :=
  iprop(∀ (k : Nat) (sret aE aX s : BitVec 64) (rv : Nat → BitVec 64),
    fnSpecW (twpW M) evalEntryPC
      (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗
        evalPre N L Room inp (.counted (k + n)) st d env e sret aE aX s rv))
      (fun _ => evalPost N L Room inp (.counted k) st' d e v sret s rv))

/-- **`eval_expr`, partial, outcome-quantified** (INTERP_DESIGN.md §4.2). The
return branch gets SOME outcome with its derivation; an error aborts. The abort
resource over the landing core `Core` (H5) hands back the stack below `s` AND
the result slot: the slot sits in the caller's frame, which the caller must
rebuild to rebase its own abort. -/
def evalSpecP_body (Core : IProp GF) (st : St) (d env : Nat) (e : Expr) : IProp GF :=
  iprop(∀ (sret aE aX s : BitVec 64) (rv : Nat → BitVec 64),
    fnSpecAbort (wpW M) evalEntryPC
      (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗
        evalPre N L Room inp .uncounted st d env e sret aE aX s rv))
      (fun _ => iprop(∃ st' v, ⌜EvalE st d env e st' v⌝ ∗
        evalPost N L Room inp .uncounted st' d e v sret s rv))
      iprop(abortAt Core s (evalNeed e d) ∗ slot24 sret.toNat))

/-- The Löb hypothesis of the partial proof: every `eval_expr` call, later. -/
def evalSpecsP (Core : IProp GF) : IProp GF :=
  iprop(□ ▷ ∀ st d env e, evalSpecP_body M N L Room inp Core st d env e)

instance (Core : IProp GF) : Persistent (evalSpecsP (GF := GF) M N L Room inp Core) := by
  unfold evalSpecsP; infer_instance

/-- `exec_stmt`'s entry resources (the statement form of `evalPre`). -/
def execPre (ρ : Regime) (st : St) (d env : Nat) (sm : Stmt) (aS aE aRet s : BitVec 64)
    (rv : Nat → BitVec 64) : IProp GF :=
  iprop(regFile rv ∗ ⌜ExecRegs rv (BitVec.ofNat 64 inp) aS aE aRet s⌝ ∗ codeRes ∗
    □ astSG aS.toNat sm ∗ □ frameAt env aE.toNat ∗
    stackScratch s (execNeed sm d) ∗ ⌜StackGeom s (execNeed sm d)⌝ ∗
    slot24 aRet.toNat ∗ ⌜SlotGeom aRet⌝ ∗ ⌜sm.bodiesBound perCallBudget = true⌝ ∗
    world N L Room inp ρ st d)

/-- `exec_stmt`'s exit resources: the status in `a0`, the `ret` slot holding
the returned value exactly when the status is `.ret v`. -/
def execPost (ρ : Regime) (st' : St) (d : Nat) (sm : Stmt) (status : Status)
    (aRet s : BitVec 64) (rv : Nat → BitVec 64) : IProp GF :=
  iprop(∃ rv', regFile rv' ∗ ⌜KeepRegs calleeSaved rv rv' ∧ rv' 10 = statusCode status⌝ ∗
    stackScratch s (execNeed sm d) ∗ statusRet N aRet.toNat status ∗ world N L Room inp ρ st' d)

/-- **`exec_stmt`, total, derivation-indexed** (INTERP_DESIGN.md §4.1). -/
def execSpecT_body (st : St) (d env : Nat) (sm : Stmt) (st' : St) (status : Status) (n : Nat)
    (_D : ExecSCost st d env sm st' status n) : IProp GF :=
  iprop(∀ (k : Nat) (aS aE aRet s : BitVec 64) (rv : Nat → BitVec 64),
    fnSpecW (twpW M) execEntryPC
      (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗
        execPre N L Room inp (.counted (k + n)) st d env sm aS aE aRet s rv))
      (fun _ => execPost N L Room inp (.counted k) st' d sm status aRet s rv))

/-- **`exec_stmt`, partial, outcome-quantified** (INTERP_DESIGN.md §4.2); the
abort hands back the stack and the `ret` slot (as `evalSpecP_body`). -/
def execSpecP_body (Core : IProp GF) (st : St) (d env : Nat) (sm : Stmt) : IProp GF :=
  iprop(∀ (aS aE aRet s : BitVec 64) (rv : Nat → BitVec 64),
    fnSpecAbort (wpW M) execEntryPC
      (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗
        execPre N L Room inp .uncounted st d env sm aS aE aRet s rv))
      (fun _ => iprop(∃ st' status, ⌜ExecS st d env sm st' status⌝ ∗
        execPost N L Room inp .uncounted st' d sm status aRet s rv))
      iprop(abortAt Core s (execNeed sm d) ∗ slot24 aRet.toNat))

/-- The Löb hypothesis for `exec_stmt` calls. -/
def execSpecsP (Core : IProp GF) : IProp GF :=
  iprop(□ ▷ ∀ st d env sm, execSpecP_body M N L Room inp Core st d env sm)

instance (Core : IProp GF) : Persistent (execSpecsP (GF := GF) M N L Room inp Core) := by
  unfold execSpecsP; infer_instance

/-- **A runtime helper that always returns**, for either WP: entered with the
body's registers at `rv` (argument facts `pins`) and `Pre`, it returns some
`rv'` that changes only the registers `clob`, and `Post rv'`. The return
address is word-aligned (the helper's `ret` needs it; H2, INTERP_DESIGN.md
§10 "STATEMENT CHANGES (H2)"). -/
def helperSpec (Wp : MachWP (GF := GF) M) (entry : BitVec 64) (clob : List Nat)
    (pins : (Nat → BitVec 64) → Prop) (Pre : IProp GF)
    (Post : (Nat → BitVec 64) → IProp GF) : IProp GF :=
  iprop(∀ rv : Nat → BitVec 64, fnSpecW Wp entry
    (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗ regFile rv ∗ ⌜pins rv⌝ ∗ codeRes ∗ Pre))
    (fun _ => iprop(∃ rv', regFile rv' ∗ ⌜∀ x ∈ fRegs, x ∉ clob → rv' x = rv x⌝ ∗ Post rv')))

/-- `value_int` (`0x8000280c`: `li a5,2; sd a1,8(a0); sw a5,0(a0); ret`): the
slot at `a0` holds the integer `a1`; clobbers `a5`. Stub statement for H2. -/
def valueIntSpec (Wp : MachWP (GF := GF) M) (p n : BitVec 64) : IProp GF :=
  helperSpec M Wp 0x8000280c#64 [15] (fun rv => rv 10 = p ∧ rv 11 = n)
    iprop(slot24 p.toNat ∗ ⌜SlotGeom p⌝) (fun _ => valAt N p.toNat (.int n.toInt))

/-- `value_null` (`0x800027ec`: `sw zero,0(a0); sd zero,8(a0); ret`): the
slot at `a0` holds `null`; clobbers nothing. Stub statement for H2. -/
def valueNullSpec (Wp : MachWP (GF := GF) M) (p : BitVec 64) : IProp GF :=
  helperSpec M Wp 0x800027ec#64 [] (fun rv => rv 10 = p)
    iprop(slot24 p.toNat ∗ ⌜SlotGeom p⌝) (fun _ => valAt N p.toNat .null)

end Specs

end VsaIris.Interp
