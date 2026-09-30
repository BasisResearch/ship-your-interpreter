import VsaIris.WhileLogic.Adequacy

namespace Vsa.While.Logic.ClosureExample

open Iris BI Vsa.While Vsa.While.Logic

abbrev fnBody : List Stmt := [.ret (some (.binary .add (.var "x") (.int 1)))]

abbrev cd : ClosureData := ⟨0, some "f", ["x"], fnBody⟩

def prog : Program := [
  .varDecl "f" (some (.fn (some "f") ["x"] fnBody)),
  .expr (.call (.var "println") [.call (.var "f") [.int 41]])]

theorem closure_spec : initOwn ⊢ wpSeq 0 0 prog (PostOut (· = "42\n")) := by
  unfold prog initOwn
  iintro ⟨H0, Ho⟩

  iapply wp_seq_cons
  iapply wp_varInit
  iapply wp_fn
  iintro %c Hc
  iapply wp_def
  isplitl [H0]
  · iexact H0
  iintro H0
  simp only [seqK]

  iapply wp_seq_cons
  iapply wp_expr
  iapply (wp_call _ _ (by decide))
  iapply wp_var
  iapply (wp_get_here (F := globalFrame.defVar "f" (.closure c)) (v := .native .println) rfl)
  isplit
  · iexact H0
  iapply wp_args_cons
  iapply (wp_call _ _ (by decide))
  iapply wp_var
  iapply (wp_get_here (F := globalFrame.defVar "f" (.closure c)) rfl)
  isplit
  · iexact H0
  iapply wp_args_cons
  iapply wp_int
  iapply wp_args_nil
  iapply (wp_call_closure (cd := cd) rfl (by decide))
  isplitl [Hc]
  · iexact Hc
  iintro %fr Hfr _

  iapply wp_seq_cons
  iapply wp_ret
  iapply wp_binary
  iapply wp_var
  iapply (wp_get_here (F := Frame.bindAll ⟨some cd.env, []⟩ (cd.params.zip [.int 41])) rfl)
  isplit
  · iexact Hfr
  iapply wp_int
  iapply (wp_bin (v := .int (wrap64 (41 + 1))) (fun _ => rfl))
  simp only [seqK, retK]
  iapply wp_args_nil
  iapply (wp_println (by simp [NoClosure]))
  isplitl [Ho]
  · iexact Ho
  iintro Ho
  have hs : "" ++ printArgs₀ [.int (wrap64 (41 + 1))] ++ "\n" = "42\n" := by decide
  rw [hs]
  iapply wp_seq_nil
  unfold PostOut
  isplit
  · ipureintro; rfl
  · iexists "42\n"
    isplit
    · ipureintro; rfl
    · iexact Ho

theorem closure_bigStep : BigStep prog "42\n" := by
  obtain ⟨out, h, rfl⟩ := adequacy_bigStep closure_spec
  exact h

end Vsa.While.Logic.ClosureExample
