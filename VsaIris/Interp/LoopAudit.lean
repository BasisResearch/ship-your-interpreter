import VsaIris.Interp.LoopWhile
import VsaIris.Interp.LoopFor
import VsaIris.Interp.LoopArgs

/-! Axiom audit of lane E6's loop lemmas (a separate module, so the lanes do
not edit `VsaIris/Audit.lean` concurrently; A folds it in). -/

#print axioms VsaIris.Interp.whileT_false
#print axioms VsaIris.Interp.whileT_break
#print axioms VsaIris.Interp.whileT_ret
#print axioms VsaIris.Interp.whileT_loop
#print axioms VsaIris.Interp.whileP_all
#print axioms VsaIris.Interp.forLoopT_condFalse
#print axioms VsaIris.Interp.forLoopT_bodyBreak
#print axioms VsaIris.Interp.forLoopT_bodyRet
#print axioms VsaIris.Interp.forLoopT_loop
#print axioms VsaIris.Interp.forCondT_none
#print axioms VsaIris.Interp.forCondT_some
#print axioms VsaIris.Interp.execStepT_none
#print axioms VsaIris.Interp.execStepT_some
#print axioms VsaIris.Interp.execInitT_none
#print axioms VsaIris.Interp.execInitT_some
#print axioms VsaIris.Interp.forLoopP_all
#print axioms VsaIris.Interp.execInitP_all
#print axioms VsaIris.Interp.evalArgsT_nil
#print axioms VsaIris.Interp.evalArgsT_cons
#print axioms VsaIris.Interp.evalArgsP_all
