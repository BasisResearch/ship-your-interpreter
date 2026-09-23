import VsaIris.Vsa.H5Sites
import VsaIris.Vsa.Newlib
import VsaIris.Stack
import VsaIris.Vsa.EnvNewPilot
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.Code.Exit
import Vsa.Sim.Code._exit

/-!
# `exit(e)` ends the run with code `e` (H5)

From `exit`'s entry (`0x80004764`) with `a0 = e`, the machine runs `exit`'s
prologue, its newlib interior (`IrisHoles.newlib.exitHandlers`), `mv a0,s0`,
`jal _exit`, `_exit`'s `slli/srli/ori/auipc`, and the `tohost` store, which
halts with code `e` (F2's `Inst.wp_exitW`). The continuation is only the
postcondition at every output extending the console: this is the last step
of every run, for either WP. The normal exit (`exit(0)`, `term_sim`), the
error exit (`exit(70)`, the landing) and the out-of-memory exit (`exit(1)`)
are all this lemma.

```
80004764: addi sp,sp,-16; li a1,0; sd s0,0(sp); sd ra,8(sp); mv s0,a0
80004778: jal __call_exitprocs … 80004784: jalr a5      (newlib: exitHandlers)
80004788: mv a0,s0
8000478c: jal _exit
80000180: slli a4,a0,32; srli a5,a4,31; ori a5,a5,1; auipc a4,0x1b
80000190: sd a5,-1164(a4)                                (tohost: halt e)
```
-/

namespace VsaIris.Newlib.Exit

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Sim VsaIris.Inst VsaIris.Interp VsaIris.Stdio VsaIris.Newlib.Sites

/-! ## The three segments -/

#derive_case exitProSeg chain
  [(0x80004764#64, 0xff010113#32),
   (0x80004768#64, 0x00000593#32),
   (0x8000476c#64, 0x00813023#32),
   (0x80004770#64, 0x00113423#32),
   (0x80004774#64, 0x00050413#32)]

#derive_case exitMvSeg chain [(0x80004788#64, 0x00040513#32)]

#derive_case exitESeg chain
  [(0x80000180#64, 0x02051713#32),
   (0x80000184#64, 0x01f75793#32),
   (0x80000188#64, 0x0017e793#32),
   (0x8000018c#64, 0x0001b717#32)]

abbrev proL (s a1v s0v r e : BitVec 64) : GRegs := [(2, s), (11, a1v), (8, s0v), (1, r), (10, e)]
abbrev mvL (a0v e : BitVec 64) : GRegs := [(10, a0v), (8, e)]
abbrev eL (e a4v a5v : BitVec 64) : GRegs := [(10, e), (14, a4v), (15, a5v)]

/-- `exit`'s code bytes give `Code.ExitLoaded`. -/
theorem exitLoaded_of_code {m : Std.ExtHashMap Nat (BitVec 8)}
    (h : ∀ p ∈ codeFoot exitCodeBase exitCode, m[p.1]? = some p.2.2) : Code.ExitLoaded m := by
  have h' : ∀ a b, (a, b) ∈ exitCode.zipIdx.map (fun p => (exitCodeBase + p.2, p.1)) →
      m[a]? = some b := by
    intro a b hab
    obtain ⟨q, hq, e⟩ := List.mem_map.mp hab
    cases e
    exact h _ (List.mem_map_of_mem (f := fun p => (exitCodeBase + p.2, Iris.DFrac.discard, p.1)) hq)
  unfold Code.ExitLoaded Code.exitChunk0
  repeat' apply And.intro
  all_goals (apply h'; decide)

theorem exitELoaded_of_code {m : Std.ExtHashMap Nat (BitVec 8)}
    (h : ∀ p ∈ codeFoot exitCodeEBase exitCodeE, m[p.1]? = some p.2.2) : Code._exitLoaded m := by
  have h' : ∀ a b, (a, b) ∈ exitCodeE.zipIdx.map (fun p => (exitCodeEBase + p.2, p.1)) →
      m[a]? = some b := by
    intro a b hab
    obtain ⟨q, hq, e⟩ := List.mem_map.mp hab
    cases e
    exact h _ (List.mem_map_of_mem (f := fun p => (exitCodeEBase + p.2, Iris.DFrac.discard, p.1)) hq)
  unfold Code._exitLoaded Code._exitChunk0
  repeat' apply And.intro
  all_goals (apply h'; decide)

/-- The 16-byte frame below `s`, in RAM above the HTIF words. -/
structure Frame16 (s : BitVec 64) : Prop where
  lo : 0x80000000 ≤ (s - 16#64).toNat
  hi : (s - 16#64).toNat + 16 ≤ 0x100000000
  win : tohostAddr + 16 ≤ (s - 16#64).toNat
  align : (s - 16#64).toNat % 8 = 0

theorem pro_facts {m : Std.ExtHashMap Nat (BitVec 8)} {s a1v s0v r e : BitVec 64}
    (hcode : Code.ExitLoaded m) (hg : Frame16 s) :
    ChainFacts m m (proL s a1v s0v r e) [] exitProSeg := by
  unfold exitProSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exit_at_"
  · exact EnvNew.storeFact (s - 16#64) 0 16 hg.lo hg.hi hg.win hg.align (by decide)
      (by rw [← sp_sub16]; rfl) (by decide) (by decide) (by decide)
  · exact EnvNew.storeFact (s - 16#64) 8 16 hg.lo hg.hi hg.win hg.align (by decide)
      (by rw [← sp_sub16]; rfl) (by decide) (by decide) (by decide)

theorem pro_log (s a1v s0v r e : BitVec 64) :
    (segOut exitProSeg (proL s a1v s0v r e) []).log =
      [((s + sign_extend (m := 64) (0xff0#12) + sign_extend (m := 64) (0x000#12)).toNat, 8, s0v),
       ((s + sign_extend (m := 64) (0xff0#12) + sign_extend (m := 64) (0x008#12)).toNat, 8, r)] :=
  rfl

theorem pro_fin (s a1v s0v r e : BitVec 64) :
    finReg exitProSeg (proL s a1v s0v r e) [] 2 = s - 16#64 ∧
    finReg exitProSeg (proL s a1v s0v r e) [] 11 = 0#64 ∧
    finReg exitProSeg (proL s a1v s0v r e) [] 8 = e ∧
    finReg exitProSeg (proL s a1v s0v r e) [] 1 = r ∧
    finReg exitProSeg (proL s a1v s0v r e) [] 10 = e := by
  refine ⟨(show s + sign_extend (m := 64) (0xff0#12) = _ from sp_sub16 s),
    (show 0#64 + sign_extend (m := 64) (0x000#12) = _ by decide),
    (show e + sign_extend (m := 64) (0x000#12) = _ from addi0_env e), rfl, rfl⟩

theorem pro_pc (s a1v s0v r e : BitVec 64) :
    evalBlocksPC 0x80004764#64 (SegEvalState.init (proL s a1v s0v r e) []) exitProSeg =
      0x80004778#64 := rfl

theorem mv_facts {m : Std.ExtHashMap Nat (BitVec 8)} {a0v e : BitVec 64}
    (hcode : Code.ExitLoaded m) : ChainFacts m m (mvL a0v e) [] exitMvSeg := by
  unfold exitMvSeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exit_at_"

theorem mv_fin (a0v e : BitVec 64) :
    finReg exitMvSeg (mvL a0v e) [] 10 = e ∧ finReg exitMvSeg (mvL a0v e) [] 8 = e :=
  ⟨(show e + sign_extend (m := 64) (0x000#12) = _ from addi0_env e), rfl⟩

theorem mv_pc (a0v e : BitVec 64) :
    evalBlocksPC 0x80004788#64 (SegEvalState.init (mvL a0v e) []) exitMvSeg = 0x8000478c#64 :=
  rfl

theorem e_facts {m : Std.ExtHashMap Nat (BitVec 8)} {e a4v a5v : BitVec 64}
    (hcode : Code._exitLoaded m) : ChainFacts m m (eL e a4v a5v) [] exitESeg := by
  unfold exitESeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code._exit_at_"

/-- `(e << 32) >> 31 | 1` is the HTIF exit word for `e < 2^31`. -/
theorem exitWord_of_shifts (e : BitVec 64) (he : e.toNat < 2 ^ 31) :
    shift_bits_right (shift_bits_left e (Sail.BitVec.extractLsb (0x020#6) 5 0))
        (Sail.BitVec.extractLsb (0x01f#6) 5 0) ||| sign_extend (m := 64) (0x001#12) =
      exitWord e := by
  have h1 : shift_bits_right (shift_bits_left e (Sail.BitVec.extractLsb (0x020#6) 5 0))
      (Sail.BitVec.extractLsb (0x01f#6) 5 0) = e <<< 1 := by
    apply BitVec.eq_of_toNat_eq
    simp [shift_bits_right, shift_bits_left, Sail.BitVec.extractLsb, BitVec.toNat_shiftLeft,
      BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h1]
  rfl

theorem e_fin (e a4v a5v : BitVec 64) (he : e.toNat < 2 ^ 31) :
    finReg exitESeg (eL e a4v a5v) [] 10 = e ∧
    finReg exitESeg (eL e a4v a5v) [] 14 = exitSite.base ∧
    finReg exitESeg (eL e a4v a5v) [] 15 = exitWord e :=
  ⟨rfl, (show 0x8000018c#64 + sign_extend (m := 64) ((0x0001b#20) +++ (0x000#12)) = _ by decide),
    exitWord_of_shifts e he⟩

theorem e_pc (e a4v a5v : BitVec 64) :
    evalBlocksPC 0x80000180#64 (SegEvalState.init (eL e a4v a5v) []) exitESeg = 0x80000190#64 :=
  rfl

/-! ## The rule -/

/-- `exit`'s entry. -/
abbrev exitEntry : BitVec 64 := 0x80004764#64

/-- The stack `exit` needs: its 16-byte frame and the newlib interior's. -/
def exitNeed : Nat := 16 + exitHandlersNeed

section Wp

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- Take one register out of a clobbered list. -/
theorem clobbered_take {r : Nat} {rs : List Nat} (h : r ∈ rs) :
    clobbered (GF := GF) rs ⊢ (∃ v, r ↦ᵣ v) ∗ clobbered (rs.erase r) := by
  unfold clobbered
  iintro H
  ihave H := (sepL_perm _ (List.perm_cons_erase h)).1 $$ H
  rw [sepL_cons]
  iexact H

/-- Put one register back. -/
theorem clobbered_put {r : Nat} {rs : List Nat} (h : r ∈ rs) :
    (∃ v, r ↦ᵣ v) ∗ clobbered (GF := GF) (rs.erase r) ⊢ clobbered rs := by
  unfold clobbered
  iintro H
  iapply (sepL_perm _ (List.perm_cons_erase h)).2
  rw [sepL_cons]
  iexact H

/-- **`exit(e)`**, for either WP. Entered at `0x80004764` with `a0 = e`
(`e < 2^31`), the callee-saved `s0` and the rest of the ABI frame, newlib's
data at its boundary state or after a `stderr` write, and the console at
`o`, the run halts with code `e` and the console at some extension of `o`. -/
theorem wp_exitCall {Ierr : (Nat → BitVec 8) → Prop} (H : NewlibHolesAt Ierr)
    (live : Nat → Prop) (hlive : CodeLive live) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} (s r e s0v : BitVec 64) (cs : Nat → BitVec 64) (o : String)
    (he : e.toNat < 2 ^ 31) (hs : SpIn s exitNeed) :
    PC ↦ᵣ exitEntry ∗ ra ↦ᵣ r ∗ (8 : Nat) ↦ᵣ s0v ∗ argsAt [e] ∗
      callFrame s exitNeed (calleeSaved.drop 1) cs ∗
      stdioAt (fun img => StdioOK img ∨ Ierr img) ∗ consoleOwn o ∗
      (∀ o', Φ (e.toNat, o ++ o'))
    ⊢ Wp.W Φ := by
  have hlo := hs.lo
  have hhi := hs.hi
  have hal := hs.align
  unfold exitNeed exitHandlersNeed tohostAddr at hlo
  have hs16 : 16 ≤ s.toNat := by omega
  have hb : (s - 16#64).toNat = s.toNat - 16 := sp_sub16_toNat s hs16
  have hg : Frame16 s := ⟨by rw [hb]; omega, by rw [hb]; omega,
    by rw [hb]; unfold tohostAddr; omega, by rw [hb]; omega⟩
  have hsp' : SpIn (s - 16#64) exitHandlersNeed :=
    ⟨by rw [hb]; unfold tohostAddr exitHandlersNeed; omega, by rw [hb]; omega, by rw [hb]; omega⟩
  have hcodeL := exitCode_text.live hlive
  have hcodeEL := exitCodeE_text.live hlive
  unfold callFrame argsAt
  simp only [List.zipIdx_cons, List.zipIdx_nil, sepL_cons, sepL_nil, Nat.add_zero,
    List.length_singleton]
  iintro ⟨Hpc, Hra, Hs0, ⟨⟨Ha0, -⟩, Hargs⟩, ⟨Hsp, Hscr, Hsaved, Htmp, #Hgp, #Himg⟩, Hstdio, Hcon,
    HΦ⟩
  ihave #Hcode := instrAt_of_binImg exitCode_text $$ Himg
  ihave #HcodeE := instrAt_of_binImg exitCodeE_text $$ Himg
  -- `exit`'s frame
  ihave ⟨Hscr, Hfr⟩ := stackScratch_frame (s := s) (f := 16#64) (n := exitNeed)
    (by unfold exitNeed exitHandlersNeed; omega) (by decide) $$ Hscr
  ihave Hfr := blockOwn_range _ _ $$ Hfr
  ihave ⟨%Wstk, %hWstk, Hfr⟩ := sepL_byteAny_exists _ $$ Hfr
  rw [show (16#64 : BitVec 64).toNat = 16 from rfl] at hWstk
  have hWmem : ∀ a, (∃ q ∈ Wstk, q.1 = a) ↔ a ∈ List.range' (s - 16#64).toNat 16 := by
    intro a; rw [← hWstk]; simp
  ihave ⟨⟨%a1v, Ha1⟩, Hargs⟩ := clobbered_take (r := 11) (by decide) $$ Hargs
  -- the prologue
  iapply wp_segW live Wp exitProSeg (proL s a1v s0v r e) [] 0x80004764#64
    (codeFoot exitCodeBase exitCode) Wstk 4 (by decide)
    (by change ChainOK _ [2, 11, 8, 1, 10] _; decide) (by change KeysOK [2, 11, 8, 1, 10]; decide)
    (by change ∀ k ∈ wrChain exitProSeg, k ∈ [2, 11, 8, 1, 10]; decide)
    (fun a ha => by
      rw [pro_log, sp_sub16, off0_addr, off8_addr _ (by have := hg.hi; omega)]
      have : ¬ a ∈ List.range' (s - 16#64).toNat 16 := fun h => by
        obtain ⟨q, hq, e⟩ := (hWmem a).2 h
        exact ha q hq e
      rw [List.mem_range'] at this
      simp only [OutL]
      refine ⟨?_, ?_, trivial⟩ <;>
      · apply Classical.byContradiction; intro hc
        exact this ⟨a - (s - 16#64).toNat, by omega, by omega⟩)
    (fun c hok ⟨_, hMR, _, _⟩ => pro_facts (exitLoaded_of_code (code_present hok _ hMR hcodeL)) hg)
  have hpc := pro_pc s a1v s0v r e
  obtain ⟨f2, f11, f8, f1, f10⟩ := pro_fin s a1v s0v r e
  simp only [proL] at hpc f2 f11 f8 f1 f10
  simp only [proL, sepL_cons, sepL_nil, hpc, f2, f11, f8, f1, f10]
  rw [← instrAt_eq]
  unfold VsaIris.sp VsaIris.ra
  iframe Hpc Hsp Ha1 Hs0 Hra Ha0 Hfr Hcode
  iintro Hpc ⟨Hsp, Ha1, Hs0, Hra, Ha0, -⟩ Hfr -
  -- `exit`'s newlib interior
  have hh := H.exitHandlers live Wp (s - 16#64) e r cs o Φ hlive hsp'
  unfold exitHandlersSpec exitHandlersPC exitHandlersEnd callFrame argsAt at hh
  simp only [List.zipIdx_cons, List.zipIdx_nil, sepL_cons, sepL_nil, Nat.add_zero,
    List.length_cons, List.length_nil] at hh
  iapply hh
  unfold VsaIris.sp VsaIris.ra
  iframe Hpc Hra Hs0 Ha0 Ha1 Hstdio Hcon Hsp Hsaved Htmp Hgp Himg
  isplitl [Hargs]
  · rw [show List.drop (0 + 1 + 1) argRegs = (List.drop 1 argRegs).erase 11 from rfl]
    iexact Hargs
  isplitl [Hscr]
  · rw [show exitHandlersNeed = exitNeed - (16#64 : BitVec 64).toNat from rfl]
    iexact Hscr
  iintro Hpc ⟨%rv, Hra⟩ Hs0 Hargs Hstdio ⟨%o', Hcon⟩ ⟨Hsp, Hscr, Hsaved, Htmp, -, -⟩
  -- `mv a0,s0`
  ihave ⟨⟨%a0v, Ha0⟩, Hargs⟩ := clobbered_take (r := 10) (by decide) $$ Hargs
  iapply wp_segW live Wp exitMvSeg (mvL a0v e) [] 0x80004788#64
    (codeFoot exitCodeBase exitCode) [] 0 (by decide)
    (by change ChainOK _ [10, 8] _; decide) (by change KeysOK [10, 8]; decide)
    (by change ∀ k ∈ wrChain exitMvSeg, k ∈ [10, 8]; decide)
    (fun a _ => trivial)
    (fun c hok ⟨_, hMR, _, _⟩ => mv_facts (exitLoaded_of_code (code_present hok _ hMR hcodeL)))
  have hpc := mv_pc a0v e
  obtain ⟨g10, g8⟩ := mv_fin a0v e
  simp only [mvL] at hpc g10 g8
  simp only [mvL, sepL_cons, sepL_nil, hpc, g10, g8]
  rw [← instrAt_eq]
  iframe Hpc Ha0 Hs0 Hcode
  iintro Hpc ⟨Ha0, Hs0, -⟩ - -
  -- `jal _exit`
  have hjt : TextAt exitJalExitE.pc exitJalExitE.code := by decide
  ihave #Hjal := instrAt_of_binImg hjt $$ Himg
  iapply wp_jalW Wp (JalSite.exec exitJalExitE_cert live (hjt.live hlive))
  unfold VsaIris.ra
  iframe Hjal Hra
  isplitl [Hpc]
  · rw [show BitVec.ofNat 64 exitJalExitE.pc = 0x8000478c#64 from rfl]
    iexact Hpc
  rw [show exitJalExitE.tgt = 0x80000180#64 from rfl]
  iintro Hpc -
  iapply Wp.lat_intro
  -- `_exit`'s word
  ihave ⟨⟨%a4v, Ha4⟩, Hargs⟩ := clobbered_take (r := 14) (by decide) $$ Hargs
  ihave ⟨⟨%a5v, Ha5⟩, Hargs⟩ := clobbered_take (r := 15) (by decide) $$ Hargs
  iapply wp_segW live Wp exitESeg (eL e a4v a5v) [] 0x80000180#64
    (codeFoot exitCodeEBase exitCodeE) [] 3 (by decide)
    (by change ChainOK _ [10, 14, 15] _; decide) (by change KeysOK [10, 14, 15]; decide)
    (by change ∀ k ∈ wrChain exitESeg, k ∈ [10, 14, 15]; decide)
    (fun a _ => trivial)
    (fun c hok ⟨_, hMR, _, _⟩ => e_facts (exitELoaded_of_code (code_present hok _ hMR hcodeEL)))
  have hpc := e_pc e a4v a5v
  obtain ⟨h10, h14, h15⟩ := e_fin e a4v a5v he
  simp only [eL] at hpc h10 h14 h15
  simp only [eL, sepL_cons, sepL_nil, hpc, h10, h14, h15]
  rw [← instrAt_eq]
  iframe Hpc Ha0 Ha4 Ha5 HcodeE
  iintro Hpc ⟨Ha0, Ha4, Ha5, -⟩ - -
  -- the `tohost` store
  have hxt : TextAt exitSite.pc exitSite.code := by decide
  ihave #Hx := instrAt_of_binImg hxt $$ Himg
  iapply wp_exitW Wp exitSite exitSite_cert e (by omega) (DFrac.own 1) (DFrac.own 1)
    (DFrac.own 1) (o ++ o') (hxt.live hlive)
  rw [show exitSite.rs1 = 14 from rfl, show exitSite.rs2 = 15 from rfl,
    show BitVec.ofNat 64 exitSite.pc = 0x80000190#64 from rfl]
  iframe Hx Ha4 Ha5 Hcon Hpc
  iapply HΦ

end Wp

end VsaIris.Newlib.Exit
