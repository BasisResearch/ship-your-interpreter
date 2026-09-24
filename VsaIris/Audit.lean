import VsaIris.DlHeap
import VsaIris.Adequacy
import VsaIris.Example
import VsaIris.Vsa.Instance
import VsaIris.Vsa.EnvNewPilot
import VsaIris.Vsa.Console
import VsaIris.LocalRun
import VsaIris.Loop
import VsaIris.Interp.Need
import VsaIris.Vsa.RuntimeError
import VsaIris.Vsa.OomSites
import VsaIris.Vsa.Setjmp
import VsaIris.Vsa.TopAbrupt
import VsaIris.Interp.WorldVacuity
import VsaIris.Interp.ProofValueCons
import VsaIris.Interp.ProofValueTruthy
import VsaIris.Interp.ProofValueEqual
import VsaIris.Interp.ProofValuePrint
import VsaIris.Interp.ProofNativePrint
import VsaIris.Interp.ProofNativePrintln
import VsaIris.Interp.ProofNativeAssert
import VsaIris.Vsa.StrlenOwned
import VsaIris.Interp.ProofStringify
import VsaIris.Interp.E5Audit
import VsaIris.Vsa.AllocHoles
import VsaIris.Interp.ProofEnvNew
import VsaIris.Interp.ProofEnvGet
import VsaIris.Interp.ProofEnvSet
import VsaIris.Interp.ProofEnvDefine
import VsaIris.Interp.Case.LeafNullT
import VsaIris.Interp.Case.LeafNullP
import VsaIris.Interp.Case.LeafIntT
import VsaIris.Interp.Case.LeafIntP
import VsaIris.Interp.Case.LeafStrT
import VsaIris.Interp.Case.LeafStrP
import VsaIris.Interp.Case.LeafBoolT
import VsaIris.Interp.Case.LeafBoolP
-- E4/E5 (errCtx clash E1 LeafErr vs E2 SpecErr, LANE.md): import VsaIris.Interp.Case.VarT
-- E4/E5 (errCtx clash E1 LeafErr vs E2 SpecErr, LANE.md): import VsaIris.Interp.Case.VarP
-- E4/E5 (errCtx clash E1 LeafErr vs E2 SpecErr, LANE.md): import VsaIris.Interp.Case.AssignT
-- E4/E5 (errCtx clash E1 LeafErr vs E2 SpecErr, LANE.md): import VsaIris.Interp.Case.AssignP

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
#print axioms VsaIris.Newlib.Landing.wp_landing
#print axioms VsaIris.Interp.abortRes_widen
#print axioms VsaIris.Interp.wp_abortOom
#print axioms VsaIris.Interp.wp_abortLanding
#print axioms VsaIris.Interp.wp_abort
#print axioms VsaIris.Inst.aluA0_runFact
#print axioms VsaIris.Newlib.RtErr.rtErr_spec
#print axioms VsaIris.Inst.seg_runFactR
#print axioms VsaIris.Newlib.Oom.wp_oomBlock
#print axioms VsaIris.Newlib.OomSites.oom80002a38_ok
#print axioms VsaIris.Newlib.OomSites.oom80002bd0_ok
#print axioms VsaIris.Newlib.OomSites.oom80003140_ok
#print axioms VsaIris.Newlib.Setjmp.setjmp_spec
#print axioms VsaIris.Newlib.Landing.wp_interpRet1
#print axioms VsaIris.Newlib.TopAbrupt.wp_topAbrupt
#print axioms VsaIris.Newlib.TopAbrupt.topRet_ok
#print axioms VsaIris.Newlib.TopAbrupt.topBrk_ok
#print axioms VsaIris.Newlib.OomSites.oom80003e28_ok
#print axioms VsaIris.Interp.stdioOK_of_mem
#print axioms VsaIris.Interp.textOwn_of_roOn
#print axioms VsaIris.Interp.boot_of_bytes
#print axioms VsaIris.Interp.world_of_boundary
#print axioms VsaIris.Interp.Boot.gap
#print axioms Vsa.Sim.NativeNameAudit.Control.bootHeap
#print axioms VsaIris.Interp.ctl_bootGap
#print axioms VsaIris.Interp.ctl_world_counted
#print axioms VsaIris.Interp.ctl_world_uncounted
#print axioms VsaIris.Sym.swp_alu
#print axioms VsaIris.Interp.helper_leaf
#print axioms VsaIris.Interp.valueNull_spec
#print axioms VsaIris.Interp.valueBool_spec
#print axioms VsaIris.Interp.valueInt_spec
#print axioms VsaIris.Interp.valueStr_spec
#print axioms VsaIris.Interp.valueTruthy_spec
#print axioms VsaIris.Interp.valueEqual_spec
#print axioms VsaIris.Interp.ms_tailNewlib
#print axioms VsaIris.Interp.valuePrint_spec
#print axioms VsaIris.Interp.nativePrint_spec
#print axioms VsaIris.Interp.nativePrintln_spec
#print axioms VsaIris.Interp.nativeAssert_spec
#print axioms VsaIris.Interp.stringify_spec
#print axioms VsaIris.Interp.ms_callNewlibAbort
#print axioms VsaIris.LocalRun.promote
#print axioms VsaIris.Inst.Strlen.strlen_specOwnedW
#print axioms VsaIris.VsaHeap.mallocChgRun_proved
#print axioms VsaIris.VsaHeap.mallocLocalRun_proved
#print axioms VsaIris.VsaHeap.freeChgRun_proved
#print axioms VsaIris.VsaHeap.freeLocalRun_proved
#print axioms VsaIris.VsaHeap.reallocChgRun_proved
#print axioms VsaIris.VsaHeap.reallocLocalRun_proved
#print axioms VsaIris.VsaHeap.allocSpecs
#print axioms VsaIris.Interp.envNew_spec
#print axioms VsaIris.Interp.envGet_spec
#print axioms VsaIris.Interp.envSet_spec
#print axioms VsaIris.Interp.envDefine_spec
#print axioms VsaIris.Interp.reallocRho_spec
#print axioms Vsa.Sim.NativeNameAudit.Control.sharedGeom

-- lane E1: eval_expr's leaf, var, assign and fn arms
#print axioms VsaIris.Interp.caseT_LeafNull
#print axioms VsaIris.Interp.caseP_LeafNull
#print axioms VsaIris.Interp.caseT_LeafInt
#print axioms VsaIris.Interp.caseP_LeafInt
#print axioms VsaIris.Interp.caseT_LeafStr
#print axioms VsaIris.Interp.caseP_LeafStr
#print axioms VsaIris.Interp.caseT_LeafBool
#print axioms VsaIris.Interp.caseP_LeafBool
-- E4/E5 (errCtx clash E1 LeafErr vs E2 SpecErr, LANE.md): #print axioms VsaIris.Interp.caseT_Var
-- E4/E5 (errCtx clash E1 LeafErr vs E2 SpecErr, LANE.md): #print axioms VsaIris.Interp.caseP_Var
-- E4/E5 (errCtx clash E1 LeafErr vs E2 SpecErr, LANE.md): #print axioms VsaIris.Interp.caseT_Assign
-- E4/E5 (errCtx clash E1 LeafErr vs E2 SpecErr, LANE.md): #print axioms VsaIris.Interp.caseP_Assign
-- E4/E5 (errCtx clash E1 LeafErr vs E2 SpecErr, LANE.md): #print axioms VsaIris.Interp.ev_rtErr
#print axioms VsaIris.Interp.ms_callEnv3
#print axioms VsaIris.Interp.reallocNullChgRun_proved
#print axioms VsaIris.Interp.reallocNullLocalRun_proved
#print axioms VsaIris.Interp.reallocNullHoles_proved
