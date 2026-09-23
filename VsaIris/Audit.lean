import VsaIris.DlHeap
import VsaIris.Adequacy
import VsaIris.Example
import VsaIris.Vsa.Instance
import VsaIris.Vsa.EnvNewPilot
import VsaIris.LocalRun

/-! Axiom audit: every headline result, printed. -/

#print axioms VsaIris.wp_exec_step
#print axioms VsaIris.wp_exec_halt
#print axioms VsaIris.wp_local_step
#print axioms VsaIris.wp_run
#print axioms VsaIris.mach_adequacy
#print axioms VsaIris.wp_ret
#print axioms VsaIris.wp_jal
#print axioms VsaIris.wp_call
#print axioms VsaIris.heapFoot_carve
#print axioms VsaIris.heapFoot_return
#print axioms VsaIris.owned_off_heap
#print axioms VsaIris.wp_call_malloc
#print axioms VsaIris.wp_call_malloc_keeps
#print axioms VsaIris.no_fixed_privFoot
#print axioms VsaIris.eb73d8c_witness
#print axioms VsaIris.Example.countdown_halts
#print axioms VsaIris.Inst.vsa_adequacy
#print axioms VsaIris.Inst.seg_runFact
#print axioms VsaIris.Inst.wp_seg
#print axioms VsaIris.Inst.jalExec_of_site
#print axioms VsaIris.Inst.EnvNew.envNew_spec
#print axioms VsaIris.Inst.EnvNew.envNew_spec_vsa
#print axioms VsaIris.lag_run
#print axioms VsaIris.twpW
#print axioms VsaIris.wpW
#print axioms VsaIris.MachWP.run
#print axioms VsaIris.wp_run_later
#print axioms VsaIris.wpP_exec_halt
#print axioms VsaIris.twp_wp
#print axioms VsaIris.wp_callW
#print axioms VsaIris.wp_call_later
#print axioms VsaIris.wp_localRunW
#print axioms VsaIris.mach_adequacyP
#print axioms VsaIris.Inst.wp_segW
#print axioms VsaIris.Inst.vsa_adequacyP
#print axioms VsaIris.Inst.vsa_adequacyP_nonzero
