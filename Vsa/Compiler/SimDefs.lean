import Vsa.Compiler.SimFn

/-!
# Forward simulation statements for arguments, calls and statements

`ASpec`: argument lists leave their values in consecutive temporaries.
`CSpec`: calling a value from the call code. `SSpec`/`QSpec`: statements and
statement lists reach the exit of their completion status (`SPost`): the end
of their code, or the `break`/`continue`/`return` target of the context with
the frame that many levels up the chain (`ExitAt`).
-/

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

/-- The values `vs` are in the temporaries from `k` on. -/
def InTmps (H : CloMap) (m : Mem) (h sp k : Nat) (vs : List Value) : Prop :=
  ∀ j (hj : j < vs.length), InTmp H m h sp (k + j) (vs[j]'hj)

/-- After evaluating arguments into temporaries from `k`. -/
structure APost (code : List Ins) (T : List String) (V : View) (st : St) (d : Nat) (env : Addr)
    (Γ : List (List String)) (sp fs k : Nat) (A : AM) (n : Nat) (st' : St) (vs : List Value) (V' : View)
    (B : AM) : Prop where
  ms : MS code T V' st' d env Γ sp fs B
  tmps : InTmps V'.H B.mem V'.h sp k vs
  grow : VGrow V st.store V' st'.store
  within : Within V V' n
  stack : StackKeep A.mem B.mem sp fs k
  obj : ObjAgree A.mem B.mem V.h

/-- Forward simulation of an argument list evaluation of cost `n`. -/
def ASpec (code : List Ins) (T : List String) (st : St) (d : Nat) (env : Addr) (es : List Expr) (st' : St)
    (vs : List Value) (n : Nat) : Prop :=
  ∀ (V : View) (Γ : List (List String)) (sp fs k pos : Nat) (A : AM),
    MS code T V st d env Γ sp fs A → A.pc = pcOf pos → WfArgs T Γ es →
    Seg code pos (gargs T Γ k pos es) → PosOK (pos + (gargs T Γ k pos es).length) →
    16 + 16 * tArgs k es ≤ fs → 16 + 16 * (k + es.length) ≤ fs →
    Reaches code A (fun B => (B.pc = pcOf errPos ∧ ¬ Room V n) ∨
      (B.pc = pcOf (pos + (gargs T Γ k pos es).length) ∧
        ∃ V', APost code T V st d env Γ sp fs k A n st' vs V' B))

/-- Forward simulation of calling `fv` on `vs`: from the call code with `fv` in
temporary `k` and the arguments above it. -/
def CSpec (code : List Ins) (T : List String) (st : St) (d : Nat) (fv : Value) (vs : List Value) (st' : St)
    (v : Value) (n : Nat) : Prop :=
  ∀ (V : View) (env : Addr) (Γ : List (List String)) (sp fs k pos : Nat) (A : AM),
    MS code T V st d env Γ sp fs A → A.pc = pcOf pos → InTmp V.H A.mem V.h sp k fv →
    InTmps V.H A.mem V.h sp (k + 1) vs → vs.length ≤ maxArgs →
    Seg code pos (callCode k vs.length pos) → PosOK (pos + (callCode k vs.length pos).length) →
    16 + 16 * (k + 1 + vs.length) ≤ fs →
    Reaches code A (fun B => (B.pc = pcOf errPos ∧ ¬ Room V n) ∨
      (B.pc = pcOf (pos + (callCode k vs.length pos).length) ∧
        ∃ V', EPost code T V st d env Γ sp fs (k + 1 + vs.length) A n st' v V' B))

/-- The context's exits are well formed. -/
structure CtxOK (C : GCtx) : Prop where
  blk : C.blk < C.Γ.length
  brk : ∀ p dt, C.brk = some (p, dt) → dt ≤ C.blk ∧ PosOK p
  cont : ∀ p dt, C.cont = some (p, dt) → dt ≤ C.blk ∧ PosOK p
  ret : ∀ p dt, C.ret = some (p, dt) → dt ≤ C.blk ∧ PosOK p

/-- Arrival at an exit target with the invariant in the frame `blk - dt` levels up. -/
def ExitAt (code : List Ins) (T : List String) (V' : View) (st' : St) (d : Nat) (env : Addr) (C : GCtx)
    (sp fs : Nat) (tgt : Option (Nat × Nat)) (B : AM) : Prop :=
  match tgt with
  | none => B.pc = pcOf errPos
  | some (p, dt) => B.pc = pcOf p ∧
      MS code T V' st' d (anc st'.store env (C.blk - dt)) (C.Γ.drop (C.blk - dt)) sp fs B

/-- Where a statement with completion `t` ends up. -/
def StOut (code : List Ins) (T : List String) (V' : View) (st' : St) (d : Nat) (env : Addr) (C : GCtx)
    (sp fs fin : Nat) (B : AM) : Status → Prop
  | .normal => B.pc = pcOf fin ∧ MS code T V' st' d env C.Γ sp fs B
  | .brk => ExitAt code T V' st' d env C sp fs C.brk B
  | .cont => ExitAt code T V' st' d env C sp fs C.cont B
  | .ret v => ExitAt code T V' st' d env C sp fs C.ret B ∧ InA V'.H B.mem V'.h B.regs v

/-- After a statement (list) with completion `t`. -/
structure SPost (code : List Ins) (T : List String) (V : View) (st : St) (d : Nat) (env : Addr) (C : GCtx)
    (sp fs fin : Nat) (A : AM) (n : Nat) (st' : St) (t : Status) (V' : View) (B : AM) : Prop where
  out : StOut code T V' st' d env C sp fs fin B t
  grow : VGrow V st.store V' st'.store
  within : Within V V' n
  stack : StackKeep A.mem B.mem sp fs 0
  obj : ObjAgree A.mem B.mem V.h

/-- Forward simulation of a statement execution of cost `n`. -/
def SSpec (code : List Ins) (T : List String) (st : St) (d : Nat) (env : Addr) (s : Stmt) (st' : St)
    (t : Status) (n : Nat) : Prop :=
  ∀ (V : View) (C : GCtx) (sp fs pos : Nat) (A : AM),
    MS code T V st d env C.Γ sp fs A → A.pc = pcOf pos → WfS T C.Γ s → CtxOK C →
    Seg code pos (gstmt T C pos s) → PosOK (pos + (gstmt T C pos s).length) → 16 + 16 * tS s ≤ fs →
    Reaches code A (fun B => (B.pc = pcOf errPos ∧ ¬ Room V n) ∨
      ∃ V', SPost code T V st d env C sp fs (pos + (gstmt T C pos s).length) A n st' t V' B)

/-- Forward simulation of a statement-list execution of cost `n`. -/
def QSpec (code : List Ins) (T : List String) (st : St) (d : Nat) (env : Addr) (ss : List Stmt) (st' : St)
    (t : Status) (n : Nat) : Prop :=
  ∀ (V : View) (C : GCtx) (sp fs pos : Nat) (A : AM),
    MS code T V st d env C.Γ sp fs A → A.pc = pcOf pos → WfSeq T C.Γ ss → CtxOK C →
    Seg code pos (gseq T C pos ss) → PosOK (pos + (gseq T C pos ss).length) → 16 + 16 * tSeq ss ≤ fs →
    Reaches code A (fun B => (B.pc = pcOf errPos ∧ ¬ Room V n) ∨
      ∃ V', SPost code T V st d env C sp fs (pos + (gseq T C pos ss).length) A n st' t V' B)

end Vsa.Compiler
