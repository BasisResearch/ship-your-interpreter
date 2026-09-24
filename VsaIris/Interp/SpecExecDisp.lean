import VsaIris.Interp.Arm

/-!
# `exec_stmt` from its dispatch point: the recursor motive (lane E5)

INTERP_DESIGN.md §10 "STATEMENT CHANGES (E5)". gcc compiled the `if` arm's
`return exec_stmt(in, branch, env, ret)` as a tail call INSIDE the frame: the
arm loads the branch into `s0`, reloads the dispatch registers and jumps back
to the kind dispatch (`0x80004230 j 0x80004014`, `0x800042d0 bnez s0,
0x80004014`). The branch therefore never runs from `exec_stmt`'s entry, and the
entry-shaped `execSpecT_body` (a `fnSpecW`) cannot be applied to it. The
statement every exec arm proves, and the recursor motive of `ExecSCost`, is the
spec at the DISPATCH point:

* the PC at `0x80004014`, the 176-byte frame spilled (`ExecSaved`: the return
  address and the caller's `s0`-`s3`), the dispatch registers (`DispRegs`:
  `s0 = s`, `s1 = in`, `s2 = ret`, `s3 = env`, `a6 = 8`, `a4` = the jump
  table), the frame bytes owned as a tracking memory (`ms`), the stack below the
  frame;
* the continuation receives the state after the epilogue's `ret`: the PC and
  `ra` at the return address, `sp` and `s0`-`s3` restored, `s4`-`s11` kept,
  the status in `a0` (`ExecRet`), the whole stack back, the `ret` slot as
  `statusRet`.

`execSpecT_body`/`execSpecP_body` follow by running the prologue
(`ExecDisp.lean`: `execSpecT_of_disp`, `execSpecP_of_disp`).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

/-- `exec_stmt`'s stack pointer after its prologue (`addi sp,sp,-176`). -/
abbrev execSP (s : BitVec 64) : BitVec 64 := s + 18446744073709551440#64

/-- The dispatch point of `exec_stmt` (`lw a5,0(s0)`). -/
def execDispPC : BitVec 64 := 0x80004014#64

/-- The registers at the dispatch point. -/
structure DispRegs (R : Nat → BitVec 64) (inp aS aE aRet s : BitVec 64) : Prop where
  sp : R 2 = execSP s
  s0 : R 8 = aS
  s1 : R 9 = inp
  s2 : R 18 = aRet
  s3 : R 19 = aE
  a6 : R 16 = 8#64
  a4 : R 14 = 0x80019fb8#64

/-- **`exec_stmt`'s prologue spills**, the seam invariant of every exec arm:
the return address and `s0`-`s3` at the top of the 176-byte frame. -/
structure ExecSaved (Mt : Mem) (s ret v8 v9 v18 v19 : BitVec 64) : Prop where
  ra : ldv .ld Mt (s.toNat - 176 + 168) = ret
  s0 : ldv .ld Mt (s.toNat - 176 + 160) = v8
  s1 : ldv .ld Mt (s.toNat - 176 + 152) = v9
  s2 : ldv .ld Mt (s.toNat - 176 + 144) = v18
  s3 : ldv .ld Mt (s.toNat - 176 + 136) = v19

/-- The registers after `exec_stmt` returns, against those at the dispatch
point `R`: `sp` and `s0`-`s3` restored from the spills, `s4`-`s11` kept, the
status in `a0`. -/
structure ExecRet (R R' : Nat → BitVec 64) (s v8 v9 v18 v19 : BitVec 64) (status : Status) :
    Prop where
  sp : R' 2 = s
  s0 : R' 8 = v8
  s1 : R' 9 = v9
  s2 : R' 18 = v18
  s3 : R' 19 = v19
  hi : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R R'
  a0 : R' 10 = statusCode status

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable (M : MachineModel) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)

/-- The pure side of the dispatch-point entry. -/
structure DispFacts (st : St) (d : Nat) (sm : Stmt) (R : Nat → BitVec 64) (Mt : Mem)
    (aS aE aRet s ret v8 v9 v18 v19 : BitVec 64) : Prop where
  regs : DispRegs R (BitVec.ofNat 64 inp) aS aE aRet s
  saved : ExecSaved Mt s ret v8 v9 v18 v19
  ral : ret.toNat % 4 = 0
  stack : StackGeom s (execNeed sm d)
  slot : SlotGeom aRet
  bodies : sm.bodiesBound perCallBudget = true

/-- **`exec_stmt`'s resources at the dispatch point**: the machine state (PC,
`ra`, registers, the frame bytes at `Mt`), the code, the statement, the frame
binding, the stack below the frame, the `ret` slot and the world. -/
def execDispPre (ρ : Regime) (st : St) (d env : Nat) (sm : Stmt) (aS aE aRet s : BitVec 64)
    (R : Nat → BitVec 64) (Mt : Mem) (ret v8 v9 v18 v19 : BitVec 64) : IProp GF :=
  iprop(ms execDispPC R (InExt (s.toNat - 176, 176)) Mt ∗
    ⌜DispFacts inp st d sm R Mt aS aE aRet s ret v8 v9 v18 v19⌝ ∗ codeRes ∗
    □ astSG aS.toNat sm ∗ □ frameAt env aE.toNat ∗
    stackScratch (execSP s) (execNeed sm d - 176) ∗ slot24 aRet.toNat ∗
    world N L Room inp ρ st d)

/-- **The return continuation**: after the epilogue's `ret`, at the return
address, with `ExecRet`, the whole stack, the `ret` slot and the world. -/
def execDispK (Wp : MachWP (GF := GF) M) (Φ : Nat × String → IProp GF) (ρ : Regime) (st' : St)
    (d : Nat) (sm : Stmt) (status : Status) (aRet s : BitVec 64) (R : Nat → BitVec 64)
    (ret v8 v9 v18 v19 : BitVec 64) : IProp GF :=
  iprop(∀ R' : Nat → BitVec 64, ⌜ExecRet R R' s v8 v9 v18 v19 status⌝ -∗
    PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗ regFile R' -∗ stackScratch s (execNeed sm d) -∗
    statusRet N aRet.toNat status -∗ world N L Room inp ρ st' d -∗ Wp.W Φ)

/-- **`exec_stmt` from the dispatch point, total, derivation-indexed**: the
recursor motive of `ExecSCost` (INTERP_DESIGN.md §4.1, §10 "STATEMENT CHANGES
(E5)"). -/
def execDispT_body (st : St) (d env : Nat) (sm : Stmt) (st' : St) (status : Status) (n : Nat)
    (_D : ExecSCost st d env sm st' status n) : IProp GF :=
  iprop(□ ∀ (Φ : Nat × String → IProp GF) (k : Nat) (aS aE aRet s : BitVec 64)
    (R : Nat → BitVec 64) (Mt : Mem) (ret v8 v9 v18 v19 : BitVec 64),
    execDispPre N L Room inp (.counted (k + n)) st d env sm aS aE aRet s R Mt ret v8 v9 v18 v19 -∗
    execDispK M N L Room inp (twpW M) Φ (.counted k) st' d sm status aRet s R ret v8 v9 v18 v19 -∗
    (twpW M).W Φ)

/-- **`exec_stmt` from the dispatch point, partial, outcome-quantified**: the
return branch gets SOME outcome with its derivation; the abort branch the
stack below the entry `sp` (frame included) and the `ret` slot. The two are an
additive pair (INTERP_DESIGN.md §10.1). -/
def execDispP_body (Core : IProp GF) (st : St) (d env : Nat) (sm : Stmt) : IProp GF :=
  iprop(□ ∀ (Φ : Nat × String → IProp GF) (aS aE aRet s : BitVec 64)
    (R : Nat → BitVec 64) (Mt : Mem) (ret v8 v9 v18 v19 : BitVec 64),
    execDispPre N L Room inp .uncounted st d env sm aS aE aRet s R Mt ret v8 v9 v18 v19 -∗
    ((∀ (st' : St) (status : Status), ⌜ExecS st d env sm st' status⌝ -∗
        execDispK M N L Room inp (wpW M) Φ .uncounted st' d sm status aRet s R ret v8 v9 v18 v19) ∧
      (iprop(abortAt Core s (execNeed sm d) ∗ slot24 aRet.toNat) -∗ (wpW M).W Φ)) -∗
    (wpW M).W Φ)

instance (st : St) (d env : Nat) (sm : Stmt) (st' : St) (status : Status) (n : Nat)
    (D : ExecSCost st d env sm st' status n) :
    Persistent (execDispT_body (GF := GF) M N L Room inp st d env sm st' status n D) := by
  unfold execDispT_body; infer_instance

instance (Core : IProp GF) (st : St) (d env : Nat) (sm : Stmt) :
    Persistent (execDispP_body (GF := GF) M N L Room inp Core st d env sm) := by
  unfold execDispP_body; infer_instance

/-- The Löb hypothesis of the partial proof at the dispatch point: every
`exec_stmt` statement, later. `execSpecsP` follows (`execSpecsP_of_disp`). -/
def execDispsP (Core : IProp GF) : IProp GF :=
  iprop(□ ▷ ∀ st d env sm, execDispP_body M N L Room inp Core st d env sm)

instance (Core : IProp GF) : Persistent (execDispsP (GF := GF) M N L Room inp Core) := by
  unfold execDispsP; infer_instance

end Specs

end VsaIris.Interp
