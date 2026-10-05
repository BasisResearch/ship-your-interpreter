import Vsa.CT.Leak

namespace Vsa.CT

open Vsa.While

mutual

def SL.st : SL → Status
  | .block ls => stSs ls
  | .ifT _ s => s.st
  | .ifF _ s => s.st
  | .whileLoop _ _ r => r.st
  | .forS _ lp => lp.st
  | .brk => .brk
  | .cont => .cont
  | _ => .normal

def stSs : List SL → Status
  | [] => .normal
  | [l] => l.st
  | _ :: l :: ls => stSs (l :: ls)

def FL.st : FL → Status
  | .loop _ _ _ r => r.st
  | _ => .normal

end

theorem stSs_cons (l : SL) (ls : List SL) (h : ls ≠ []) : stSs (l :: ls) = stSs ls := by
  cases ls with
  | nil => exact absurd rfl h
  | cons l' ls => rfl

mutual

theorem execL_st : ∀ {st d env s st' t l}, ExecL st d env s st' t l → (∀ v, t ≠ .ret v) → t = l.st
  | _, _, _, _, _, _, _, .expr .., _ => rfl
  | _, _, _, _, _, _, _, .varInit .., _ => rfl
  | _, _, _, _, _, _, _, .varNull .., _ => rfl
  | _, _, _, _, _, _, _, .block _ _ _ _ _ _ _ _ _ _ h, hr => (execSeqL_st h hr).trans rfl
  | _, _, _, _, _, _, _, .ifTrue _ _ _ _ _ _ _ _ _ _ _ _ _ _ h, hr => (execL_st h hr).trans rfl
  | _, _, _, _, _, _, _, .ifFalse _ _ _ _ _ _ _ _ _ _ _ _ _ _ h, hr => (execL_st h hr).trans rfl
  | _, _, _, _, _, _, _, .ifNone .., _ => rfl
  | _, _, _, _, _, _, _, .whileFalse .., _ => rfl
  | _, _, _, _, _, _, _, .whileBreak .., _ => rfl
  | _, _, _, _, _, _, _, .whileRet _ _ _ _ _ _ _ _ rv _ _ _ _ _, hr => absurd rfl (hr rv)
  | _, _, _, _, _, _, _, .whileLoop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h, hr => (execL_st h hr).trans rfl
  | _, _, _, _, _, _, _, .forStart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h, hr => (forL_st h hr).trans rfl
  | _, _, _, _, _, _, _, .ret _ _ _ _ _ v _ _, hr => absurd rfl (hr v)
  | _, _, _, _, _, _, _, .retNull .., hr => absurd rfl (hr _)
  | _, _, _, _, _, _, _, .brk .., _ => rfl
  | _, _, _, _, _, _, _, .cont .., _ => rfl

theorem execSeqL_st : ∀ {st d env ss st' t l}, ExecSeqL st d env ss st' t l → (∀ v, t ≠ .ret v) →
    t = stSs l
  | _, _, _, _, _, _, _, .nil .., _ => rfl
  | _, _, _, _, _, _, _, .consNormal _ _ _ _ _ _ _ _ l ls h1 h2, hr => by
    cases h2 with
    | nil => exact execL_st h1 hr
    | consNormal _ _ _ _ _ _ _ _ l' ls' h3 h4 =>
      rw [stSs_cons _ _ (by simp)]; exact execSeqL_st (.consNormal _ _ _ _ _ _ _ _ _ _ h3 h4) hr
    | consAbrupt _ _ _ _ _ _ _ l' h3 hne =>
      rw [stSs_cons _ _ (by simp)]; exact (execL_st h3 hr).trans rfl
  | _, _, _, _, _, _, _, .consAbrupt _ _ _ _ _ _ _ l h1 _, hr => execL_st h1 hr

theorem forL_st : ∀ {st d env c step b st' t l}, ForLoopL st d env c step b st' t l →
    (∀ v, t ≠ .ret v) → t = l.st
  | _, _, _, _, _, _, _, _, _, .condFalse .., _ => rfl
  | _, _, _, _, _, _, _, _, _, .bodyBreak .., _ => rfl
  | _, _, _, _, _, _, _, _, _, .bodyRet _ _ _ _ _ _ _ _ rv _ _ _ _, hr => absurd rfl (hr rv)
  | _, _, _, _, _, _, _, _, _, .loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h, hr => (forL_st h hr).trans rfl

end

end Vsa.CT
