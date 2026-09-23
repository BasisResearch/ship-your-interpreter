import VsaIris.DlHeap
import VsaIris.Adequacy
import VsaIris.Example

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
