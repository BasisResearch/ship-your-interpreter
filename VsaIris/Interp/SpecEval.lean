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

/-- A byte a load may read: RAM, off the HTIF words. -/
structure ReadOK (k : Nat) : Prop where
  lo : 0x80000000 ≤ k
  hi : k < 0x100000000
  off : k < Vsa.Sim.tohostAddr ∨ Vsa.Sim.tohostAddr + 16 ≤ k

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

variable (M : MachineModel) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)

def evalEntryPC : BitVec 64 := 0x80003164#64

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

/-- **A runtime helper that always returns**, for either WP: entered with the
body's registers at `rv` (argument facts `pins`) and `Pre`, it returns some
`rv'` that changes only the registers `clob`, and `Post rv'`. -/
def helperSpec (Wp : MachWP (GF := GF) M) (entry : BitVec 64) (clob : List Nat)
    (pins : (Nat → BitVec 64) → Prop) (Pre : IProp GF)
    (Post : (Nat → BitVec 64) → IProp GF) : IProp GF :=
  iprop(∀ rv : Nat → BitVec 64, fnSpecW Wp entry
    (fun _ => iprop(regFile rv ∗ ⌜pins rv⌝ ∗ codeRes ∗ Pre))
    (fun _ => iprop(∃ rv', regFile rv' ∗ ⌜∀ x ∈ fRegs, x ∉ clob → rv' x = rv x⌝ ∗ Post rv')))

/-- `value_int` (`0x8000280c`: `li a5,2; sd a1,8(a0); sw a5,0(a0); ret`): the
slot at `a0` holds the integer `a1`; clobbers `a5`. Stub statement for H2. -/
def valueIntSpec (Wp : MachWP (GF := GF) M) (p n : BitVec 64) : IProp GF :=
  helperSpec M Wp 0x8000280c#64 [15] (fun rv => rv 10 = p ∧ rv 11 = n)
    iprop(slot24 p.toNat ∗ ⌜SlotGeom p⌝) (fun _ => valAt N p.toNat (.int n.toInt))

end Specs

end VsaIris.Interp
