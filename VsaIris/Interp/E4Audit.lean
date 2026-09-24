import VsaIris.Interp.Case.CallPrintT
import VsaIris.Interp.Case.CallPrintlnT
import VsaIris.Interp.Case.CallAssertT
import VsaIris.Interp.Case.CallClosureT
import VsaIris.Interp.Case.CallArmP
import VsaIris.Interp.CallNotCallable

/-! Lane E4's axiom audit: the call family's cases and its layer. -/

#print axioms VsaIris.Interp.caseT_CallPrint
#print axioms VsaIris.Interp.caseT_CallPrintln
#print axioms VsaIris.Interp.caseT_CallAssert
#print axioms VsaIris.Interp.caseT_CallClosure
#print axioms VsaIris.Interp.caseP_CallArm
#print axioms VsaIris.Interp.callPrefixT
#print axioms VsaIris.Interp.callPrefixP
#print axioms VsaIris.Interp.callNativeOut
#print axioms VsaIris.Interp.callNativeAssert
#print axioms VsaIris.Interp.callNotCallable
#print axioms VsaIris.Interp.callCloHead
#print axioms VsaIris.Interp.cloBind
#print axioms VsaIris.Interp.cloBodyEntry
#print axioms VsaIris.Interp.cloExitN
#print axioms VsaIris.Interp.cloExitR
#print axioms VsaIris.Interp.cloCallT
#print axioms VsaIris.Interp.callClosureT
