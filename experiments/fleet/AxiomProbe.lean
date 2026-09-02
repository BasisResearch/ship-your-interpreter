import Vsa.Sim.EndToEnd
import Vsa.Sim.rows.AssemblySkeleton
import Vsa.Sim.rows.SeqForRows
import Vsa.Sim.rows.CallClosureRow

-- ITEM ZERO post-amendment axiom audit (task c gate).
#print axioms Vsa.Sim.TermAssembly.termCases_of_residuals
#print axioms Vsa.Sim.TermAssembly.interpSim_of_residuals
#print axioms Vsa.Sim.TermAssembly.Skel.termResidualsCore_of_skeleton
#print axioms Vsa.Sim.Rows.hFlCondFalse_row
#print axioms Vsa.Sim.Rows.hFlBodyBreak_row
#print axioms Vsa.Sim.Rows.hFlBodyRet_row
#print axioms Vsa.Sim.Rows.hFlLoop_row
#print axioms Vsa.Sim.TermSimAssembly.seqSpanGround_of
#print axioms Vsa.Sim.TermSimAssembly.term_sim_of_cases
#print axioms Vsa.Sim.EndToEnd.endToEnd
#print axioms Vsa.Sim.hEntryHalts_closed'
#print axioms Vsa.Sim.Rows.eval_callClosure_row
