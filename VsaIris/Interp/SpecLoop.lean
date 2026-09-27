import VsaIris.Interp.SeqLoopClosure

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While

structure StmtHead (R : Nat → BitVec 64) (s aS inp aRet aEnv : BitVec 64) : Prop where
  sp : R 2 = s + 18446744073709551440#64
  s0 : R 8 = aS
  s1 : R 9 = inp
  s2 : R 18 = aRet
  s3 : R 19 = aEnv

def Untouched (S W : Nat → Prop) (Mt Mt' : Mem) : Prop :=
  ∀ a, S a → ¬ W a → imgM Mt' a = imgM Mt a

theorem Untouched.refl (S W : Nat → Prop) (Mt : Mem) : Untouched S W Mt Mt := fun _ _ _ => rfl

theorem Untouched.trans {S W : Nat → Prop} {M1 M2 M3 : Mem} (h1 : Untouched S W M1 M2)
    (h2 : Untouched S W M2 M3) : Untouched S W M1 M3 :=
  fun a hs hw => (h2 a hs hw).trans (h1 a hs hw)

abbrev execS (s : BitVec 64) : Nat → Prop := InExt (s.toNat - 176, 176)

abbrev execW (s : BitVec 64) : Nat → Prop := InExt (s.toNat - 176 + 16, 112)

def loopExit : Status → BitVec 64
  | .ret _ => 0x80004150#64
  | _ => 0x8000409c#64

theorem loopExit_ret (v : Value) : loopExit (.ret v) = 0x80004150#64 := rfl
theorem loopExit_normal : loopExit .normal = 0x8000409c#64 := rfl

structure ForFits (d : Nat) (cnd step : Option Expr) (b : Stmt) (m' : Nat) : Prop where
  cond : ∀ c, cnd = some c → evalNeed c d ≤ m' ∧ c.bodiesBound perCallBudget = true
  step : ∀ e, step = some e → evalNeed e d ≤ m' ∧ e.bodiesBound perCallBudget = true
  body : execNeed b d ≤ m'
  bodyB : b.bodiesBound perCallBudget = true

structure WhileFits (d : Nat) (c : Expr) (b : Stmt) (m' : Nat) : Prop where
  cond : evalNeed c d ≤ m'
  condB : c.bodiesBound perCallBudget = true
  body : execNeed b d ≤ m'
  bodyB : b.bodiesBound perCallBudget = true

structure InitHead (R : Nat → BitVec 64) (s aS inp aRet aOuter : BitVec 64) : Prop where
  sp : R 2 = s + 18446744073709551440#64
  s0 : R 8 = aS
  s1 : R 9 = inp
  s2 : R 18 = aRet
  a0 : R 10 = aOuter

abbrev initKeep : List Nat := [2, 8, 9, 18, 20, 21, 22, 23, 24, 25, 26, 27]

structure ArgsHead (R : Nat → BitVec 64) (s aX inp aE : BitVec 64) (idx argc : Nat) : Prop where
  sp : R 2 = s + 18446744073709550528#64
  s0 : R 8 = aX
  s2 : R 18 = inp
  a3 : R 13 = aE
  a6 : R 16 = BitVec.ofNat 64 idx
  a5 : R 15 = BitVec.ofNat 64 argc

abbrev argsBase (s : BitVec 64) : Nat := s.toNat - 1088 + 240

def argsW (s : BitVec 64) (a : Nat) : Prop :=
  InExt (s.toNat - 1088, 32) a ∨ InExt (s.toNat - 1088 + 64, 24) a ∨
    InExt (argsBase s, 768) a

abbrev argsKeep : List Nat := [15, 2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

section Motive

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr
variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

def argVals (N : NativeAddrs) (img : Nat → BitVec 8) (base : Nat) : Nat → List Value → IProp GF
  | _, [] => iprop(emp)
  | i, v :: vs => iprop(valImg N img (base + 24 * i) v ∗ argVals N img base (i + 1) vs)

instance (N : NativeAddrs) (img : Nat → BitVec 8) (base i : Nat) (vs : List Value) :
    Persistent (argVals (GF := GF) N img base i vs) := by
  induction vs generalizing i with
  | nil => unfold argVals; infer_instance
  | cons v vs ih => unfold argVals; infer_instance

variable (live : Nat → Prop) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)

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
