import Vsa.Sim.AstAccessAudit.AccessUnit000
import Vsa.Sim.AstAccessAudit.AccessUnit001
import Vsa.Sim.AstAccessAudit.AccessUnit002
import Vsa.Sim.AstAccessAudit.AccessUnit003
import Vsa.Sim.AstAccessAudit.AccessUnit004
import Vsa.Sim.AstAccessAudit.AccessUnit005
import Vsa.Sim.AstAccessAudit.AccessUnit006
import Vsa.Sim.AstAccessAudit.AccessUnit007
import Vsa.Sim.AstAccessAudit.AccessUnit008

open Vsa.Machine
namespace Vsa.Sim.AstAccessAudit
theorem access_prefix : ∃ c, Steps accessConfig c ∧ AccessHolds traceD009 c := by
  have h := access_initial_trace
  obtain ⟨c0, hs0, h⟩ := run000 h
  obtain ⟨c1, hs1, h⟩ := run001 h
  obtain ⟨c2, hs2, h⟩ := run002 h
  obtain ⟨c3, hs3, h⟩ := run003 h
  obtain ⟨c4, hs4, h⟩ := run004 h
  obtain ⟨c5, hs5, h⟩ := run005 h
  obtain ⟨c6, hs6, h⟩ := run006 h
  obtain ⟨c7, hs7, h⟩ := run007 h
  obtain ⟨c8, hs8, h⟩ := run008 h
  exact ⟨c8, ((((((((hs0.trans hs1).trans hs2).trans hs3).trans hs4).trans hs5).trans hs6).trans hs7).trans hs8), h⟩

#print axioms access_prefix
end Vsa.Sim.AstAccessAudit
