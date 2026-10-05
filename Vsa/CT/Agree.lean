import Vsa.CT.Leak

namespace Vsa.CT

open Vsa.While

mutual

theorem EvalL.sem : ∀ {st d env e st' v l}, EvalL st d env e st' v l → EvalE st d env e st' v
  | _, _, _, _, _, _, _, .int .. => .int ..
  | _, _, _, _, _, _, _, .str .. => .str ..
  | _, _, _, _, _, _, _, .bool .. => .bool ..
  | _, _, _, _, _, _, _, .null .. => .null ..
  | _, _, _, _, _, _, _, .var _ _ _ _ _ h => .var _ _ _ _ _ h
  | _, _, _, _, _, _, _, .assign _ _ _ _ _ _ _ _ _ h1 h2 => .assign _ _ _ _ _ _ _ _ h1.sem h2
  | _, _, _, _, _, _, _, .binary _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    .binary _ _ _ _ _ _ _ _ _ _ _ h1.sem h2.sem h3
  | _, _, _, _, _, _, _, .orTrue _ _ _ _ _ _ _ _ h1 h2 => .orTrue _ _ _ _ _ _ _ h1.sem h2
  | _, _, _, _, _, _, _, .orFalse _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    .orFalse _ _ _ _ _ _ _ _ _ h1.sem h2 h3.sem
  | _, _, _, _, _, _, _, .andFalse _ _ _ _ _ _ _ _ h1 h2 => .andFalse _ _ _ _ _ _ _ h1.sem h2
  | _, _, _, _, _, _, _, .andTrue _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    .andTrue _ _ _ _ _ _ _ _ _ h1.sem h2 h3.sem
  | _, _, _, _, _, _, _, .neg _ _ _ _ _ _ _ h => .neg _ _ _ _ _ _ h.sem
  | _, _, _, _, _, _, _, .not _ _ _ _ _ _ _ h => .not _ _ _ _ _ _ h.sem
  | _, _, _, _, _, _, _, .call _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 =>
    .call _ _ _ _ _ _ _ _ _ _ _ h1.sem h2 h3.sem h4.sem
  | _, _, _, _, _, _, _, .fn _ _ _ _ _ _ _ _ h => .fn _ _ _ _ _ _ _ _ h

theorem EvalArgsL.sem : ∀ {st d env es st' vs ls}, EvalArgsL st d env es st' vs ls →
    EvalArgs st d env es st' vs
  | _, _, _, _, _, _, _, .nil .. => .nil ..
  | _, _, _, _, _, _, _, .cons _ _ _ _ _ _ _ _ _ _ _ h1 h2 => .cons _ _ _ _ _ _ _ _ _ h1.sem h2.sem

theorem CallL.sem : ∀ {st d fv vs st' v l}, CallL st d fv vs st' v l → Call st d fv vs st' v
  | _, _, _, _, _, _, _, .closure _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    .closure _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5.sem h6
  | _, _, _, _, _, _, _, .print .. => .print ..
  | _, _, _, _, _, _, _, .println .. => .println ..
  | _, _, _, _, _, _, _, .assertOk _ _ _ _ _ h1 h2 => .assertOk _ _ _ _ _ h1 h2

theorem ExecL.sem : ∀ {st d env s st' t l}, ExecL st d env s st' t l → ExecS st d env s st' t
  | _, _, _, _, _, _, _, .expr _ _ _ _ _ _ _ h => .expr _ _ _ _ _ _ h.sem
  | _, _, _, _, _, _, _, .varInit _ _ _ _ _ _ _ _ h => .varInit _ _ _ _ _ _ _ h.sem
  | _, _, _, _, _, _, _, .varNull .. => .varNull ..
  | _, _, _, _, _, _, _, .block _ _ _ _ _ _ _ _ _ h1 h2 => .block _ _ _ _ _ _ _ _ h1 h2.sem
  | _, _, _, _, _, _, _, .ifTrue _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    .ifTrue _ _ _ _ _ _ _ _ _ _ h1.sem h2 h3.sem
  | _, _, _, _, _, _, _, .ifFalse _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    .ifFalse _ _ _ _ _ _ _ _ _ _ h1.sem h2 h3.sem
  | _, _, _, _, _, _, _, .ifNone _ _ _ _ _ _ _ _ h1 h2 => .ifNone _ _ _ _ _ _ _ h1.sem h2
  | _, _, _, _, _, _, _, .whileFalse _ _ _ _ _ _ _ _ h1 h2 => .whileFalse _ _ _ _ _ _ _ h1.sem h2
  | _, _, _, _, _, _, _, .whileBreak _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    .whileBreak _ _ _ _ _ _ _ _ h1.sem h2 h3.sem
  | _, _, _, _, _, _, _, .whileRet _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    .whileRet _ _ _ _ _ _ _ _ _ h1.sem h2 h3.sem
  | _, _, _, _, _, _, _, .whileLoop _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    .whileLoop _ _ _ _ _ _ _ _ _ _ _ h1.sem h2 h3.sem h4 h5.sem
  | _, _, _, _, _, _, _, .forStart _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    .forStart _ _ _ _ _ _ _ _ _ _ _ _ h1 h2.sem h3.sem
  | _, _, _, _, _, _, _, .ret _ _ _ _ _ _ _ h => .ret _ _ _ _ _ _ h.sem
  | _, _, _, _, _, _, _, .retNull .. => .retNull ..
  | _, _, _, _, _, _, _, .brk .. => .brk ..
  | _, _, _, _, _, _, _, .cont .. => .cont ..

theorem ExecInitL.sem : ∀ {st d env s st' l}, ExecInitL st d env s st' l → ExecInit st d env s st'
  | _, _, _, _, _, _, .none .. => .none ..
  | _, _, _, _, _, _, .some _ _ _ _ _ _ _ h => .some _ _ _ _ _ _ h.sem

theorem ForLoopL.sem : ∀ {st d env c step b st' t l}, ForLoopL st d env c step b st' t l →
    ForLoop st d env c step b st' t
  | _, _, _, _, _, _, _, _, _, .condFalse _ _ _ _ _ _ _ _ _ h1 h2 => .condFalse _ _ _ _ _ _ _ _ h1.sem h2
  | _, _, _, _, _, _, _, _, _, .bodyBreak _ _ _ _ _ _ _ _ _ _ h1 h2 =>
    .bodyBreak _ _ _ _ _ _ _ _ h1.sem h2.sem
  | _, _, _, _, _, _, _, _, _, .bodyRet _ _ _ _ _ _ _ _ _ _ _ h1 h2 =>
    .bodyRet _ _ _ _ _ _ _ _ _ h1.sem h2.sem
  | _, _, _, _, _, _, _, _, _, .loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    .loop _ _ _ _ _ _ _ _ _ _ _ _ h1.sem h2.sem h3 h4.sem h5.sem

theorem ForCondL.sem : ∀ {st d env c st' l}, ForCondL st d env c st' l → ForCond st d env c st'
  | _, _, _, _, _, _, .none .. => .none ..
  | _, _, _, _, _, _, .some _ _ _ _ _ _ _ h1 h2 => .some _ _ _ _ _ _ h1.sem h2

theorem ExecStepL.sem : ∀ {st d env c st' l}, ExecStepL st d env c st' l → ExecStep st d env c st'
  | _, _, _, _, _, _, .none .. => .none ..
  | _, _, _, _, _, _, .some _ _ _ _ _ _ _ h => .some _ _ _ _ _ _ h.sem

theorem ExecSeqL.sem : ∀ {st d env ss st' t l}, ExecSeqL st d env ss st' t l →
    ExecSeq st d env ss st' t
  | _, _, _, _, _, _, _, .nil .. => .nil ..
  | _, _, _, _, _, _, _, .consNormal _ _ _ _ _ _ _ _ _ _ h1 h2 => .consNormal _ _ _ _ _ _ _ _ h1.sem h2.sem
  | _, _, _, _, _, _, _, .consAbrupt _ _ _ _ _ _ _ _ h1 h2 => .consAbrupt _ _ _ _ _ _ _ h1.sem h2

end

mutual

theorem _root_.Vsa.While.EvalE.leak : ∀ {st d env e st' v}, EvalE st d env e st' v → ∃ l, EvalL st d env e st' v l
  | _, _, _, _, _, _, .int .. => ⟨_, .int ..⟩
  | _, _, _, _, _, _, .str .. => ⟨_, .str ..⟩
  | _, _, _, _, _, _, .bool .. => ⟨_, .bool ..⟩
  | _, _, _, _, _, _, .null .. => ⟨_, .null ..⟩
  | _, _, _, _, _, _, .var _ _ _ _ _ h => ⟨_, .var _ _ _ _ _ h⟩
  | _, _, _, _, _, _, .assign _ _ _ _ _ _ _ _ h1 h2 =>
    let ⟨_, h1⟩ := h1.leak; ⟨_, .assign _ _ _ _ _ _ _ _ _ h1 h2⟩
  | _, _, _, _, _, _, .binary _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    let ⟨_, h1⟩ := h1.leak; let ⟨_, h2⟩ := h2.leak; ⟨_, .binary _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3⟩
  | _, _, _, _, _, _, .orTrue _ _ _ _ _ _ _ h1 h2 =>
    let ⟨_, h1⟩ := h1.leak; ⟨_, .orTrue _ _ _ _ _ _ _ _ h1 h2⟩
  | _, _, _, _, _, _, .orFalse _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    let ⟨_, h1⟩ := h1.leak; let ⟨_, h3⟩ := h3.leak; ⟨_, .orFalse _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3⟩
  | _, _, _, _, _, _, .andFalse _ _ _ _ _ _ _ h1 h2 =>
    let ⟨_, h1⟩ := h1.leak; ⟨_, .andFalse _ _ _ _ _ _ _ _ h1 h2⟩
  | _, _, _, _, _, _, .andTrue _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    let ⟨_, h1⟩ := h1.leak; let ⟨_, h3⟩ := h3.leak; ⟨_, .andTrue _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3⟩
  | _, _, _, _, _, _, .neg _ _ _ _ _ _ h => let ⟨_, h⟩ := h.leak; ⟨_, .neg _ _ _ _ _ _ _ h⟩
  | _, _, _, _, _, _, .not _ _ _ _ _ _ h => let ⟨_, h⟩ := h.leak; ⟨_, .not _ _ _ _ _ _ _ h⟩
  | _, _, _, _, _, _, .call _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 =>
    let ⟨_, h1⟩ := h1.leak; let ⟨_, h3⟩ := h3.leak; let ⟨_, h4⟩ := h4.leak
    ⟨_, .call _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4⟩
  | _, _, _, _, _, _, .fn _ _ _ _ _ _ _ _ h => ⟨_, .fn _ _ _ _ _ _ _ _ h⟩

theorem _root_.Vsa.While.EvalArgs.leak : ∀ {st d env es st' vs}, EvalArgs st d env es st' vs →
    ∃ ls, EvalArgsL st d env es st' vs ls
  | _, _, _, _, _, _, .nil .. => ⟨_, .nil ..⟩
  | _, _, _, _, _, _, .cons _ _ _ _ _ _ _ _ _ h1 h2 =>
    let ⟨_, h1⟩ := h1.leak; let ⟨_, h2⟩ := h2.leak; ⟨_, .cons _ _ _ _ _ _ _ _ _ _ _ h1 h2⟩

theorem _root_.Vsa.While.Call.leak : ∀ {st d fv vs st' v}, Call st d fv vs st' v → ∃ l, CallL st d fv vs st' v l
  | _, _, _, _, _, _, .closure _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 =>
    let ⟨_, h5⟩ := h5.leak; ⟨_, .closure _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6⟩
  | _, _, _, _, _, _, .print .. => ⟨_, .print ..⟩
  | _, _, _, _, _, _, .println .. => ⟨_, .println ..⟩
  | _, _, _, _, _, _, .assertOk _ _ _ _ _ h1 h2 => ⟨_, .assertOk _ _ _ _ _ h1 h2⟩

theorem _root_.Vsa.While.ExecS.leak : ∀ {st d env s st' t}, ExecS st d env s st' t → ∃ l, ExecL st d env s st' t l
  | _, _, _, _, _, _, .expr _ _ _ _ _ _ h => let ⟨_, h⟩ := h.leak; ⟨_, .expr _ _ _ _ _ _ _ h⟩
  | _, _, _, _, _, _, .varInit _ _ _ _ _ _ _ h =>
    let ⟨_, h⟩ := h.leak; ⟨_, .varInit _ _ _ _ _ _ _ _ h⟩
  | _, _, _, _, _, _, .varNull .. => ⟨_, .varNull ..⟩
  | _, _, _, _, _, _, .block _ _ _ _ _ _ _ _ h1 h2 =>
    let ⟨_, h2⟩ := h2.leak; ⟨_, .block _ _ _ _ _ _ _ _ _ h1 h2⟩
  | _, _, _, _, _, _, .ifTrue _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    let ⟨_, h1⟩ := h1.leak; let ⟨_, h3⟩ := h3.leak; ⟨_, .ifTrue _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3⟩
  | _, _, _, _, _, _, .ifFalse _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    let ⟨_, h1⟩ := h1.leak; let ⟨_, h3⟩ := h3.leak; ⟨_, .ifFalse _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3⟩
  | _, _, _, _, _, _, .ifNone _ _ _ _ _ _ _ h1 h2 =>
    let ⟨_, h1⟩ := h1.leak; ⟨_, .ifNone _ _ _ _ _ _ _ _ h1 h2⟩
  | _, _, _, _, _, _, .whileFalse _ _ _ _ _ _ _ h1 h2 =>
    let ⟨_, h1⟩ := h1.leak; ⟨_, .whileFalse _ _ _ _ _ _ _ _ h1 h2⟩
  | _, _, _, _, _, _, .whileBreak _ _ _ _ _ _ _ _ h1 h2 h3 =>
    let ⟨_, h1⟩ := h1.leak; let ⟨_, h3⟩ := h3.leak; ⟨_, .whileBreak _ _ _ _ _ _ _ _ _ _ h1 h2 h3⟩
  | _, _, _, _, _, _, .whileRet _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    let ⟨_, h1⟩ := h1.leak; let ⟨_, h3⟩ := h3.leak; ⟨_, .whileRet _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3⟩
  | _, _, _, _, _, _, .whileLoop _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    let ⟨_, h1⟩ := h1.leak; let ⟨_, h3⟩ := h3.leak; let ⟨_, h5⟩ := h5.leak
    ⟨_, .whileLoop _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5⟩
  | _, _, _, _, _, _, .forStart _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    let ⟨_, h2⟩ := h2.leak; let ⟨_, h3⟩ := h3.leak; ⟨_, .forStart _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3⟩
  | _, _, _, _, _, _, .ret _ _ _ _ _ _ h => let ⟨_, h⟩ := h.leak; ⟨_, .ret _ _ _ _ _ _ _ h⟩
  | _, _, _, _, _, _, .retNull .. => ⟨_, .retNull ..⟩
  | _, _, _, _, _, _, .brk .. => ⟨_, .brk ..⟩
  | _, _, _, _, _, _, .cont .. => ⟨_, .cont ..⟩

theorem _root_.Vsa.While.ExecInit.leak : ∀ {st d env s st'}, ExecInit st d env s st' → ∃ l, ExecInitL st d env s st' l
  | _, _, _, _, _, .none .. => ⟨_, .none ..⟩
  | _, _, _, _, _, .some _ _ _ _ _ _ h => let ⟨_, h⟩ := h.leak; ⟨_, .some _ _ _ _ _ _ _ h⟩

theorem _root_.Vsa.While.ForLoop.leak : ∀ {st d env c step b st' t}, ForLoop st d env c step b st' t →
    ∃ l, ForLoopL st d env c step b st' t l
  | _, _, _, _, _, _, _, _, .condFalse _ _ _ _ _ _ _ _ h1 h2 =>
    let ⟨_, h1⟩ := h1.leak; ⟨_, .condFalse _ _ _ _ _ _ _ _ _ h1 h2⟩
  | _, _, _, _, _, _, _, _, .bodyBreak _ _ _ _ _ _ _ _ h1 h2 =>
    let ⟨_, h1⟩ := h1.leak; let ⟨_, h2⟩ := h2.leak; ⟨_, .bodyBreak _ _ _ _ _ _ _ _ _ _ h1 h2⟩
  | _, _, _, _, _, _, _, _, .bodyRet _ _ _ _ _ _ _ _ _ h1 h2 =>
    let ⟨_, h1⟩ := h1.leak; let ⟨_, h2⟩ := h2.leak; ⟨_, .bodyRet _ _ _ _ _ _ _ _ _ _ _ h1 h2⟩
  | _, _, _, _, _, _, _, _, .loop _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    let ⟨_, h1⟩ := h1.leak; let ⟨_, h2⟩ := h2.leak; let ⟨_, h4⟩ := h4.leak; let ⟨_, h5⟩ := h5.leak
    ⟨_, .loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5⟩

theorem _root_.Vsa.While.ForCond.leak : ∀ {st d env c st'}, ForCond st d env c st' → ∃ l, ForCondL st d env c st' l
  | _, _, _, _, _, .none .. => ⟨_, .none ..⟩
  | _, _, _, _, _, .some _ _ _ _ _ _ h1 h2 => let ⟨_, h1⟩ := h1.leak; ⟨_, .some _ _ _ _ _ _ _ h1 h2⟩

theorem _root_.Vsa.While.ExecStep.leak : ∀ {st d env c st'}, ExecStep st d env c st' → ∃ l, ExecStepL st d env c st' l
  | _, _, _, _, _, .none .. => ⟨_, .none ..⟩
  | _, _, _, _, _, .some _ _ _ _ _ _ h => let ⟨_, h⟩ := h.leak; ⟨_, .some _ _ _ _ _ _ _ h⟩

theorem _root_.Vsa.While.ExecSeq.leak : ∀ {st d env ss st' t}, ExecSeq st d env ss st' t →
    ∃ l, ExecSeqL st d env ss st' t l
  | _, _, _, _, _, _, .nil .. => ⟨_, .nil ..⟩
  | _, _, _, _, _, _, .consNormal _ _ _ _ _ _ _ _ h1 h2 =>
    let ⟨_, h1⟩ := h1.leak; let ⟨_, h2⟩ := h2.leak; ⟨_, .consNormal _ _ _ _ _ _ _ _ _ _ h1 h2⟩
  | _, _, _, _, _, _, .consAbrupt _ _ _ _ _ _ _ h1 h2 =>
    let ⟨_, h1⟩ := h1.leak; ⟨_, .consAbrupt _ _ _ _ _ _ _ _ h1 h2⟩

end

theorem bigStep_iff_L (p : Program) (out : String) : BigStep p out ↔ ∃ ℓ, BigStepL p out ℓ := by
  constructor
  · rintro ⟨st', h, rfl⟩
    obtain ⟨ℓ, h⟩ := h.leak
    exact ⟨ℓ, st', h, rfl⟩
  · rintro ⟨ℓ, st', h, rfl⟩
    exact ⟨st', h.sem, rfl⟩

end Vsa.CT
