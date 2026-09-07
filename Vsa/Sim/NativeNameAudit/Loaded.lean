import Vsa.Sim.NativeNameAudit.Admission
import Vsa.Sim.NativeNameAudit.Ast

/-! Initial admission of the mutable binding-name candidate under the historical
AST-only boundary. This is independent of the untrusted sparse replay. -/

namespace Vsa.Sim.NativeNameAudit

open Vsa.Sim.OutputAliasLoaded Vsa.Sim.LayoutInstance

theorem nativeName_readyFacts :
    BeforeRuntimeOwnership.InterpRunReadyFacts nativeNameConfig 0x82000000 2 fixedInp
      Nfixed arena phif phic 0 where
  toInterpRunOwnedFacts := {
    toInterpRunPhysicalFacts := nativeName_physicalFacts
    ast_owned := nativeName_ast_owned }
  ast_readable := nativeName_ast_readable

theorem nativeName_loaded :
    Vsa.Refine.Loaded BeforeRuntimeOwnership.interpRunLayout nativeNameProgram nativeNameConfig :=
  ⟨0x82000000, 2, programWithin.erase,
    fixedInp, Nfixed, arena, phif, phic, 0, nativeName_readyFacts⟩

#print axioms nativeName_readyFacts
#print axioms nativeName_loaded
#print axioms nativeName_bigStep

end Vsa.Sim.NativeNameAudit
