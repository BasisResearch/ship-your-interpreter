import VsaIris.Vsa.Stdout.Fputc
import VsaIris.Vsa.Stdout.StdioAfter
import VsaIris.Interp.NewlibCall
import VsaIris.Vsa.NewlibOut

/-!
# From a stdout run to `NewlibOut.outSpec` (lane N1)

`outSpec` is H5's calling convention: argument registers (`argsAt`), the
call frame (`sp`, the stack below it, the callee-saved registers, the
temporaries, `gp`, the binary's image), newlib's data and `errno`
(`stdioW`) and the console. A stdout run (`fputc_run`, …) is a printing
symbolic run over one register file and the owned bytes `outS s need`. This
module packages the one into the other.
-/

namespace VsaIris.Sym

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open Vsa.MemRepr Vsa.Sim VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio VsaIris.Newlib
open VsaIris.Inst

section Regs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem argRegs_nodup (k : Nat) : (argRegs.drop k).Nodup :=
  List.Nodup.sublist (List.drop_sublist _ _) (by decide)

/-- `argsAt` as one register function. -/
theorem argsAt_fn : ∀ (k : Nat) (ws : List (BitVec 64)), k + ws.length ≤ 8 →
    iprop(sepL (GF := GF) (ws.zipIdx k) (fun p => (10 + p.2) ↦ᵣ p.1) ∗
      clobbered (argRegs.drop (k + ws.length))) ⊢
      ∃ fa : Nat → BitVec 64, sepL (argRegs.drop k) (fun r => r ↦ᵣ fa r) ∗
        ⌜∀ i (h : i < ws.length), fa (10 + k + i) = ws[i]⌝
  | k, [], _ => by
    simp only [List.zipIdx_nil, sepL_nil, List.length_nil, Nat.add_zero]
    iintro ⟨-, H⟩
    ihave ⟨%f, H⟩ := clobbered_fn _ (argRegs_nodup k) $$ H
    iexists f
    iframe H
    ipureintro; intro i h; simp at h
  | k, w :: ws, hk => by
    have hk8 : k < 8 := by simp at hk; omega
    have hdrop : argRegs.drop k = (10 + k) :: argRegs.drop (k + 1) := by
      revert hk8; generalize k = j; intro hj
      rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega
    have hnot : 10 + k ∉ argRegs.drop (k + 1) := by
      have := argRegs_nodup k; rw [hdrop] at this; exact (List.nodup_cons.mp this).1
    rw [List.zipIdx_cons, sepL_cons]
    iintro ⟨⟨H0, H⟩, Hc⟩
    ihave ⟨%fa, Hs, %hfa⟩ := argsAt_fn (k + 1) ws (by simp at hk; omega) $$ [H Hc]
    · simp only [List.length_cons, show k + (ws.length + 1) = k + 1 + ws.length by omega]
      iframe H Hc
    iexists fun r => if r = 10 + k then w else fa r
    rw [hdrop, sepL_cons]
    isplitl
    · isplitl [H0]
      · simp only [ite_true]; iexact H0
      rw [sepL_congr (Φ := fun r => iprop(r ↦ᵣ (if r = 10 + k then w else fa r)))
        (Ψ := fun r => iprop(r ↦ᵣ fa r)) (fun r hr => by
        simp [show r ≠ 10 + k from fun e => hnot (e ▸ hr)])]
      iexact Hs
    · ipureintro
      intro i h
      rcases i with _ | i
      · simp
      · have := hfa i (by simp at h; omega)
        simp only [List.getElem_cons_succ]
        rw [if_neg (by omega), ← this]; congr 1; omega

theorem argsAt_fn0 (vs : List (BitVec 64)) (hlen : vs.length ≤ 8) :
    argsAt (GF := GF) vs ⊢ ∃ fa : Nat → BitVec 64, sepL argRegs (fun r => r ↦ᵣ fa r) ∗
      ⌜∀ i (h : i < vs.length), fa (10 + i) = vs[i]⌝ := by
  have h := argsAt_fn (GF := GF) 0 vs (by omega)
  simp only [Nat.zero_add, List.drop_zero] at h
  unfold argsAt; exact h

/-- **A call's registers as one register file.** -/
theorem call_regs (entry r s : BitVec 64) (vs : List (BitVec 64)) (cs : Nat → BitVec 64)
    (hlen : vs.length ≤ 8) :
    iprop(VsaIris.PC ↦ᵣ entry ∗ VsaIris.ra ↦ᵣ r ∗ argsAt (GF := GF) vs ∗ sp ↦ᵣ s ∗
      sepL Newlib.calleeSaved (fun x => x ↦ᵣ cs x) ∗ clobbered tmpRegs) ⊢
      ∃ rv : Nat → BitVec 64, sepL iRegs (fun x => x ↦ᵣ rv x) ∗
        ⌜rv 32 = entry ∧ rv 1 = r ∧ rv 2 = s ∧ (∀ i (h : i < vs.length), rv (10 + i) = vs[i]) ∧
          ∀ x ∈ Newlib.calleeSaved, rv x = cs x⌝ := by
  classical
  iintro ⟨Hpc, Hra, Ha, Hsp, Hcs, Ht⟩
  ihave ⟨%fa, Ha, %hfa⟩ := argsAt_fn0 vs hlen $$ Ha
  ihave ⟨%ft, Ht⟩ := clobbered_fn tmpRegs (by decide) $$ Ht
  let rv : Nat → BitVec 64 := fun x =>
    if x = 32 then entry else if x = 1 then r else if x = 2 then s else
      if x ∈ argRegs then fa x else if x ∈ tmpRegs then ft x else cs x
  iexists rv
  isplitl
  · iapply (sepL_iRegs rv).2
    have e32 : rv 32 = entry := by simp [rv]
    have e1 : rv 1 = r := by simp [rv]
    rw [e32, e1]
    iframe Hpc Hra
    iapply (regFile_newlib rv).2
    have e2 : rv 2 = s := by simp [rv]
    rw [e2]
    iframe Hsp
    rw [sepL_congr (Φ := fun x => iprop(x ↦ᵣ rv x)) (Ψ := fun x => iprop(x ↦ᵣ cs x))
      (l := Newlib.calleeSaved) (fun x hx => by
        simp only [Newlib.calleeSaved, argRegs, tmpRegs, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [rv, argRegs, tmpRegs])]
    rw [sepL_congr (Φ := fun x => iprop(x ↦ᵣ rv x)) (Ψ := fun x => iprop(x ↦ᵣ ft x))
      (l := tmpRegs) (fun x hx => by
        simp only [tmpRegs, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rv, argRegs, tmpRegs])]
    rw [sepL_congr (Φ := fun x => iprop(x ↦ᵣ rv x)) (Ψ := fun x => iprop(x ↦ᵣ fa x))
      (l := argRegs) (fun x hx => by
        simp only [argRegs, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rv, argRegs])]
    iframe Hcs Ht Ha
  · ipureintro
    refine ⟨by simp [rv], by simp [rv], by simp [rv], fun i h => ?_, fun x hx => ?_⟩
    · have := hfa i h
      have hi : 10 + i ∈ argRegs := by
        simp only [argRegs, List.mem_cons, List.not_mem_nil, _root_.or_false]; omega
      simp only [rv, hi, if_true]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simpa using this
    · simp only [Newlib.calleeSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [rv, argRegs, tmpRegs]

/-- **A returned register file as a call's post registers.** -/
theorem ret_regs (r s : BitVec 64) (cs rv : Nat → BitVec 64) (h32 : rv 32 = r) (h1 : rv 1 = r)
    (h2 : rv 2 = s) (hcs : ∀ x ∈ Newlib.calleeSaved, rv x = cs x) :
    sepL (GF := GF) iRegs (fun x => x ↦ᵣ rv x) ⊢
      iprop(VsaIris.PC ↦ᵣ r ∗ VsaIris.ra ↦ᵣ r ∗ clobbered argRegs ∗ sp ↦ᵣ s ∗
        sepL Newlib.calleeSaved (fun x => x ↦ᵣ cs x) ∗ clobbered tmpRegs) := by
  iintro H
  ihave ⟨Hpc, Hra, Hr⟩ := (sepL_iRegs rv).1 $$ H
  rw [h32, h1]
  iframe Hpc Hra
  ihave ⟨Hsp, Hcs, Ht, Ha⟩ := (regFile_newlib rv).1 $$ Hr
  rw [h2]
  iframe Hsp
  isplitl [Ha]
  · iapply clobbered_of_fn _ rv $$ Ha
  isplitl [Hcs]
  · rw [sepL_congr (Φ := fun x => iprop(x ↦ᵣ rv x)) (Ψ := fun x => iprop(x ↦ᵣ cs x))
      (l := Newlib.calleeSaved) (fun x hx => by rw [hcs x hx])] at *
    iexact Hcs
  · iapply clobbered_of_fn _ rv $$ Ht

end Regs

end VsaIris.Sym
