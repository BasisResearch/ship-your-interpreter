import Vsa.Sim.ExecWhileIndexed

namespace Vsa.Sim

open Vsa.While

local notation "SpecSt" => Vsa.While.St

/-- The semantic facts that every recursive child must return to its parent.

`ReprDelta` deliberately contains no machine memory.  It records the
append-only semantic-store change and the agreement required to transport
existing frame and closure addresses through freshly chosen representation
maps. -/
structure ReprDelta (st0 st1 : SpecSt) (env : Addr)
    (phiF0 phiF1 phiC0 phiC1 : Addr -> Nat) : Prop where
  storeLe : StoreLe st0.store st1.store
  envValid : EnvValid st1 env
  frames : PhiExtends phiF0 phiF1 st0.store.frames.size
  closures : PhiExtends phiC0 phiC1 st0.store.closures.size

namespace ReprDelta

theorem refl {st : SpecSt} {env : Addr} {phiF phiC : Addr -> Nat}
    (henv : EnvValid st env) :
    ReprDelta st st env phiF phiF phiC phiC :=
  { storeLe := StoreLe.refl _
    envValid := henv
    frames := PhiExtends.refl _ _
    closures := PhiExtends.refl _ _ }

theorem trans {st0 st1 st2 : SpecSt} {env : Addr}
    {phiF0 phiF1 phiF2 phiC0 phiC1 phiC2 : Addr -> Nat}
    (h01 : ReprDelta st0 st1 env phiF0 phiF1 phiC0 phiC1)
    (h12 : ReprDelta st1 st2 env phiF1 phiF2 phiC1 phiC2) :
    ReprDelta st0 st2 env phiF0 phiF2 phiC0 phiC2 :=
  { storeLe := h01.storeLe.trans h12.storeLe
    envValid := h12.envValid
    frames := h01.frames.trans (PhiExtends.mono h01.storeLe.1 h12.frames)
    closures := h01.closures.trans (PhiExtends.mono h01.storeLe.2 h12.closures) }

theorem ofStoreLe {st0 st1 : SpecSt} {env : Addr}
    {phiF0 phiF1 phiC0 phiC1 : Addr -> Nat}
    (henv : EnvValid st0 env) (hstore : StoreLe st0.store st1.store)
    (hframes : PhiExtends phiF0 phiF1 st0.store.frames.size)
    (hclosures : PhiExtends phiC0 phiC1 st0.store.closures.size) :
    ReprDelta st0 st1 env phiF0 phiF1 phiC0 phiC1 :=
  { storeLe := hstore
    envValid := henv.afterStoreLe hstore
    frames := hframes
    closures := hclosures }

theorem ofEvalE {st0 st1 : SpecSt} {d : Nat} {env : Addr}
    {e : Expr} {v : Value} {phiF0 phiF1 phiC0 phiC1 : Addr -> Nat}
    (henv : EnvValid st0 env) (hsem : EvalE st0 d env e st1 v)
    (hframes : PhiExtends phiF0 phiF1 st0.store.frames.size)
    (hclosures : PhiExtends phiC0 phiC1 st0.store.closures.size) :
    ReprDelta st0 st1 env phiF0 phiF1 phiC0 phiC1 :=
  ofStoreLe henv (Vsa.While.evalE_store_mono hsem) hframes hclosures

theorem ofExecS {st0 st1 : SpecSt} {d : Nat} {env : Addr}
    {stmt : Stmt} {status : Status}
    {phiF0 phiF1 phiC0 phiC1 : Addr -> Nat}
    (henv : EnvValid st0 env) (hsem : ExecS st0 d env stmt st1 status)
    (hframes : PhiExtends phiF0 phiF1 st0.store.frames.size)
    (hclosures : PhiExtends phiC0 phiC1 st0.store.closures.size) :
    ReprDelta st0 st1 env phiF0 phiF1 phiC0 phiC1 :=
  ofStoreLe henv (Vsa.While.execS_store_mono hsem) hframes hclosures

theorem ofExecSeq {st0 st1 : SpecSt} {d : Nat} {env : Addr}
    {stmts : List Stmt} {status : Status}
    {phiF0 phiF1 phiC0 phiC1 : Addr -> Nat}
    (henv : EnvValid st0 env) (hsem : ExecSeq st0 d env stmts st1 status)
    (hframes : PhiExtends phiF0 phiF1 st0.store.frames.size)
    (hclosures : PhiExtends phiC0 phiC1 st0.store.closures.size) :
    ReprDelta st0 st1 env phiF0 phiF1 phiC0 phiC1 :=
  ofStoreLe henv (Vsa.While.execSeq_store_mono hsem) hframes hclosures

theorem ofForCond {st0 st1 : SpecSt} {d : Nat} {env : Addr}
    {cond : Option Expr} {phiF0 phiF1 phiC0 phiC1 : Addr -> Nat}
    (henv : EnvValid st0 env) (hsem : ForCond st0 d env cond st1)
    (hframes : PhiExtends phiF0 phiF1 st0.store.frames.size)
    (hclosures : PhiExtends phiC0 phiC1 st0.store.closures.size) :
    ReprDelta st0 st1 env phiF0 phiF1 phiC0 phiC1 :=
  ofStoreLe henv (Vsa.While.forCond_store_mono hsem) hframes hclosures

theorem ofExecStep {st0 st1 : SpecSt} {d : Nat} {env : Addr}
    {step : Option Expr} {phiF0 phiF1 phiC0 phiC1 : Addr -> Nat}
    (henv : EnvValid st0 env) (hsem : ExecStep st0 d env step st1)
    (hframes : PhiExtends phiF0 phiF1 st0.store.frames.size)
    (hclosures : PhiExtends phiC0 phiC1 st0.store.closures.size) :
    ReprDelta st0 st1 env phiF0 phiF1 phiC0 phiC1 :=
  ofStoreLe henv (Vsa.While.execStep_store_mono hsem) hframes hclosures

theorem ofForLoop {st0 st1 : SpecSt} {d : Nat} {env : Addr}
    {cond step : Option Expr} {body : Stmt} {status : Status}
    {phiF0 phiF1 phiC0 phiC1 : Addr -> Nat}
    (henv : EnvValid st0 env)
    (hsem : ForLoop st0 d env cond step body st1 status)
    (hframes : PhiExtends phiF0 phiF1 st0.store.frames.size)
    (hclosures : PhiExtends phiC0 phiC1 st0.store.closures.size) :
    ReprDelta st0 st1 env phiF0 phiF1 phiC0 phiC1 :=
  ofStoreLe henv (Vsa.While.forLoop_store_mono hsem) hframes hclosures

end ReprDelta

/-- A compositional description of the semantic output appended by a child.
This is the source-level counterpart of a machine output effect. -/
structure OutputDelta (before after suffix : String) : Prop where
  append_eq : after = before ++ suffix

namespace OutputDelta

theorem refl (out : String) : OutputDelta out out "" := by
  constructor
  simp

theorem append (before suffix : String) :
    OutputDelta before (before ++ suffix) suffix :=
  ⟨rfl⟩

theorem trans {out0 out1 out2 suffix01 suffix12 : String}
    (h01 : OutputDelta out0 out1 suffix01)
    (h12 : OutputDelta out1 out2 suffix12) :
    OutputDelta out0 out2 (suffix01 ++ suffix12) := by
  constructor
  rw [h12.append_eq, h01.append_eq, String.append_assoc]

theorem unchanged {out0 out1 : String} (h : OutputDelta out0 out1 "") :
    out1 = out0 := by
  simpa using h.append_eq

end OutputDelta

end Vsa.Sim
