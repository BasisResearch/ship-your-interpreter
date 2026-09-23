import VsaIris.DlHeap
import VsaIris.Adequacy
import VsaIris.Example
import VsaIris.Vsa.Instance
import VsaIris.Vsa.EnvNewPilot
import VsaIris.Vsa.Console
import VsaIris.LocalRun
import VsaIris.Loop
import VsaIris.Interp.Need
import VsaIris.Vsa.MainErr

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
#print axioms VsaIris.consoleOwn_excl
#print axioms VsaIris.MachWP.runOut
#print axioms VsaIris.MachWP.haltConsole
#print axioms VsaIris.wp_runOut
#print axioms VsaIris.wp_halt_console
#print axioms VsaIris.Inst.putc_runFact
#print axioms VsaIris.Inst.exit_haltFact
#print axioms VsaIris.Inst.wp_putcW
#print axioms VsaIris.Inst.wp_putc
#print axioms VsaIris.Inst.wp_exitW
#print axioms VsaIris.Inst.wp_exit
#print axioms VsaIris.Inst.vsa_adequacy_exit
#print axioms VsaIris.Inst.putcSite_cert
#print axioms VsaIris.Inst.exitSite_cert
#print axioms VsaIris.MachWP.loop
#print axioms VsaIris.MachWP.loopI
#print axioms VsaIris.MachWP.loopSeg
#print axioms VsaIris.wp_loop
#print axioms VsaIris.wpP_loop
#print axioms VsaIris.fnSpecAbort
#print axioms VsaIris.wp_callAbort
#print axioms VsaIris.wp_callAbort_later
#print axioms VsaIris.fnSpecAbort_of_fnSpecW
#print axioms VsaIris.fnSpecAbort_mono
#print axioms VsaIris.fnSpecAbort_rebase
#print axioms VsaIris.blockOwn_split
#print axioms VsaIris.blockOwn_join
#print axioms VsaIris.stackScratch_carve
#print axioms VsaIris.stackScratch_join
#print axioms VsaIris.abort_rebase
#print axioms VsaIris.stackScratch_frame
#print axioms VsaIris.stackScratch_unframe
#print axioms VsaIris.wp_callArmW
#print axioms VsaIris.wp_callArmAbort
#print axioms VsaIris.Interp.stackBudget_child
#print axioms VsaIris.Interp.stackBudget_call
#print axioms VsaIris.Interp.execNeed_callBody
#print axioms VsaIris.Interp.execNeed_of_stackFits
#print axioms VsaIris.Interp.stackScratch_boundary
#print axioms VsaIris.Newlib.NewlibHoles.at
#print axioms VsaIris.Newlib.Exit.wp_exitCall
#print axioms VsaIris.Newlib.MainErr.wp_mainErrTail
