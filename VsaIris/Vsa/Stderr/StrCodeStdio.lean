import VsaIris.Vsa.Fprintf.Strlen

namespace VsaIris.Sym

open VsaIris.Interp

theorem strCode_stdio : ∀ p ∈ strCode, p ∈ stdioText := fun p hp =>
  List.mem_append_left _ (Vsa.Sim.mem_piecesText (List.all_eq_true.1
    (by decide +kernel : strCode.all (fun p => Vsa.Sim.piecesHasB stdioPieces p.1 p.2) = true) p hp))

end VsaIris.Sym
