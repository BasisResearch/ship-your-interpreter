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
      simp only [rv, hi, ite_true]
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

/-! ## The run's read-only cells and owned bytes -/

/-- Every byte of `stdioText` is the fixed binary's `.text` byte. -/
theorem stdioText_img :
    stdioText.all (fun p => decide (textDom p.1) && textByte p.1 == p.2) = true := by
  decide +kernel

theorem stdioText_img_mem : ∀ p ∈ stdioText, textDom p.1 ∧ textByte p.1 = p.2 := by
  intro p hp
  have h := List.all_eq_true.1 stdioText_img p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h

theorem stdioText_live {live : Nat → Prop} (h : CodeLive live) : ∀ p ∈ stdioText, live p.1 :=
  fun p hp => h _ (stdioText_img_mem p hp).1

theorem imgM_impDt {k : Nat} (h : impureW k) : imgM impDt k = impureByte k := by
  unfold imgM impDt
  rw [fillMem_get impureByte (List.mem_range'.mpr ⟨k - 0x8001b970, by unfold impureW at h; omega,
    by unfold impureW at h; omega⟩)]
  rfl

section Own

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **The read-only cells of a stdout run**: `gp`, the stdio code from the
binary's image, `_impure_ptr` as the data view. -/
theorem roOwn_stdio :
    iprop(gp ↦ᵣ□ Newlib.gpV ∗ binImg ∗ impureRO) ⊢@{IProp GF}
      roOwn roR (stdioText ++ dataOf impDt (accAddrs 0x8001b970 8)) := by
  unfold roOwn
  iintro ⟨#Hgp, #Himg, #Hr⟩
  isplitl []
  · simp only [roR, sepL_cons, sepL_nil]
    rw [show Newlib.gpV = MallocFast.gpV from rfl]
    iframe Hgp
  iapply (sepL_append _ _ _).2
  isplitl []
  · iapply binImg_sepL stdioText (fun p hp => .inl (stdioText_img_mem p hp)) $$ Himg
  unfold dataOf
  rw [sepL_map]
  unfold impureRO
  ihave #Hr := roImg_restrict (T := impureW) (g := imgM impDt) (fun _ h => h)
    (fun k hk => (imgM_impDt hk).symm) $$ Hr
  iapply roImg_list impureW (imgM impDt) _ (fun a ha => by
    rw [mem_accAddrs_iff] at ha; unfold impureW; omega) $$ Hr

/-- **The owned bytes of a stdout call**, at one tracking memory: newlib's
exclusive data at its image, `errno` and the stack at any values. -/
theorem outBytes (img : Nat → BitVec 8) (s : BitVec 64) (need : Nat) (hs : need ≤ s.toNat) :
    iprop(ownSet (GF := GF) stdioExcl (fun a => a ↦ₘ img a) ∗ errnoOwn ∗ stackScratch s need) ⊢
      ∃ Mt : Mem, ownSet (outS s need) (fun a => a ↦ₘ imgM Mt a) ∗
        ⌜∀ a, stdioExcl a → imgM Mt a = img a⌝ := by
  classical
  iintro ⟨Hx, He, Hst⟩
  unfold errnoOwn stackScratch blockOwn
  ihave ⟨%fe, He⟩ := ownSet_fn _ $$ He
  ihave ⟨%fs, Hst⟩ := ownSet_fn _ $$ Hst
  ihave %hd1 := ownSet_disj _ _ _ _ $$ [Hx He]
  · iframe Hx He
  ihave %hd2 := ownSet_disj _ _ _ _ $$ [Hx Hst]
  · iframe Hx Hst
  ihave %hd3 := ownSet_disj _ _ _ _ $$ [He Hst]
  · iframe He Hst
  let f : Nat → BitVec 8 := fun a => if stdioExcl a then img a else if errnoFoot a then fe a else fs a
  ihave Hx := ownSet_congr (Ψ := fun a => iprop(a ↦ₘ f a)) (fun a ha => by simp [f, ha]) $$ Hx
  ihave He := ownSet_congr (Ψ := fun a => iprop(a ↦ₘ f a))
    (fun a ha => by simp [f, ha, show ¬ stdioExcl a from fun h => hd1 a h ha]) $$ He
  ihave Hst := ownSet_congr (Ψ := fun a => iprop(a ↦ₘ f a))
    (fun a ha => by simp [f, show ¬ stdioExcl a from fun h => hd2 a h ha,
      show ¬ errnoFoot a from fun h => hd3 a h ha]) $$ Hst
  ihave H := ownSet_join _ _ _ (fun a h1 h2 => hd3 a h1 h2) $$ [He Hst]
  · iframe He Hst
  ihave H := ownSet_join stdioExcl (fun a => errnoFoot a ∨ InExt (s.toNat - need, need) a) _
    (fun a (h1 : stdioExcl a) (h2 : errnoFoot a ∨ InExt (s.toNat - need, need) a) => by
      rcases h2 with h2 | h2
      · exact hd1 a h1 h2
      · exact hd2 a h1 h2) $$ [Hx H]
  · iframe Hx H
  ihave H := ownSet_iff (T := outS s need) _ (fun a => by
    unfold outS stdioExcl errnoFoot Stdio.InRange InExt
    constructor
    · rintro (h | h | ⟨h1, h2⟩)
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr ⟨h1, by simp at h2; omega⟩)
    · rintro (h | h | ⟨h1, h2⟩)
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr ⟨h1, by simp; omega⟩)) $$ H
  ihave ⟨%M, H, %hM⟩ := ownSet_trackedAt _ f $$ H
  iexists M
  iframe H
  ipureintro
  intro a ha
  rw [hM a (by unfold outS; exact .inl ha)]
  simp [f, ha]

/-- **The owned bytes back** as newlib's data, `errno` and the stack. -/
theorem outBytes_back (mv : Nat → BitVec 8) (s : BitVec 64) (need : Nat) (hs : need ≤ s.toNat)
    (hs4 : 0x8001c168 ≤ s.toNat - need) :
    ownSet (GF := GF) (outS s need) (fun a => a ↦ₘ mv a) ⊢
      ownSet stdioExcl (fun a => a ↦ₘ mv a) ∗ errnoOwn ∗ stackScratch s need := by
  iintro H
  ihave ⟨Hx, H⟩ := ownSet_split _ stdioExcl _ $$ H
  ihave ⟨He, Hs⟩ := ownSet_split _ errnoFoot _ $$ H
  isplitl [Hx]
  · iapply ownSet_iff _ (fun a => ⟨fun h => h.2, fun h => ⟨.inl h, h⟩⟩) $$ Hx
  isplitl [He]
  · unfold errnoOwn
    ihave He := ownSet_forget _ mv $$ He
    iapply ownSet_iff _ (fun a => ⟨fun h => h.2, fun h => ⟨⟨by
      unfold outS errnoFoot Stdio.InRange at *; omega, by
      unfold stdioExcl stdioFoot errnoFoot Stdio.InRange at *; omega⟩, h⟩⟩) $$ He
  · unfold stackScratch blockOwn
    ihave Hs := ownSet_forget _ mv $$ Hs
    iapply ownSet_iff _ (fun a => ⟨fun ⟨⟨h1, h2⟩, h3⟩ => by
      unfold outS stdioExcl stdioFoot errnoFoot impureW Stdio.InRange InExt at *; simp at *; omega,
      fun h => ⟨⟨by unfold outS InExt at *; simp at h; omega, by
        unfold stdioExcl stdioFoot InExt Stdio.InRange at *; simp at h; omega⟩, by
        unfold errnoFoot InExt Stdio.InRange at *; simp at h; omega⟩⟩) $$ Hs

/-- A persistent byte is not in an owned list. -/
theorem sepL_ro_ne (y : Nat) (b : BitVec 8) (f : Nat → BitVec 8) :
    ∀ l : List Nat, sepL (GF := GF) l (fun a => a ↦ₘ f a) ∗ (y ↦ₘ□ b) ⊢ ⌜y ∉ l⌝
  | [] => by iintro _; ipureintro; simp
  | x :: xs => by
    rw [sepL_cons]
    iintro ⟨⟨Hx, Hxs⟩, #Hy⟩
    ihave %h1 := memRO_excl_ne y x b (f x) $$ [Hx]
    · iframe Hy Hx
    ihave %h2 := sepL_ro_ne y b f xs $$ [Hxs]
    · iframe Hxs Hy
    ipureintro
    simp only [List.mem_cons, not_or]
    exact ⟨h1, h2⟩

/-- Persistent bytes are off an owned byte set. -/
theorem ownSet_ro_off (S : Nat → Prop) (f : Nat → BitVec 8) :
    ∀ text : List (Nat × BitVec 8), ownSet (GF := GF) S (fun a => a ↦ₘ f a) ∗
      sepL text (fun p => p.1 ↦ₘ□ p.2) ⊢ ⌜∀ p ∈ text, ¬ S p.1⌝
  | [] => by iintro _; ipureintro; simp
  | q :: qs => by
    rw [sepL_cons]
    iintro ⟨HS, #Hq, #Hqs⟩
    ihave %h2 := ownSet_ro_off S f qs $$ [HS]
    · iframe HS Hqs
    rw [show ownSet S (fun a => a ↦ₘ f a) = iprop(∃ l : List Nat,
        ⌜l.Nodup ∧ ∀ a, a ∈ l ↔ S a⌝ ∗ sepL l (fun a => a ↦ₘ f a)) from rfl]
    icases HS with ⟨%l, %⟨_, hmem⟩, Hl⟩
    ihave %h1 := sepL_ro_ne q.1 q.2 f l $$ [Hl]
    · iframe Hl Hq
    ipureintro
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact fun h => h1 ((hmem _).2 h)
    · exact h2 p hp

/-- The data part of a run's read-only resources. -/
theorem roOwn_data {ro : List (Nat × BitVec 64)} {T D : List (Nat × BitVec 8)} :
    roOwn (GF := GF) ro (T ++ D) ⊢ sepL D (fun p => p.1 ↦ₘ□ p.2) := by
  unfold roOwn
  iintro ⟨-, #H⟩
  ihave ⟨-, #H⟩ := (sepL_append _ _ _).1 $$ H
  iexact H

end Own

/-- The end of a stdout call's run: the console grew by `frag`, the PC and
`ra` are the return address, `sp` and the callee-saved registers are back,
and newlib's data (with `_impure_ptr`) is in its boundary state again. -/
def OutEnd (o frag : String) (r s : BitVec 64) (cs : Nat → BitVec 64) :
    String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop :=
  fun t rv mv => t = o ++ frag ∧ rv 32 = r ∧ rv 1 = r ∧ rv 2 = s ∧
    (∀ x ∈ Newlib.calleeSaved, rv x = cs x) ∧
    StdioOK (fun a => if impureW a then impureByte a else mv a)

/-- **The end of a stdout run from its summary.** A callee returning with
`RetOK`, a memory keeping everything but its stack window, `errno` and
stdout's pointer/count/flags/buffer byte (`outKeep`), and stdout idle again
(`_p` at the one-byte buffer, `_w = 0`, the flags), ends in `OutEnd`. -/
theorem outEnd_of {o frag t : String} {r s a0 : BitVec 64} {cs R R' rv : Nat → BitVec 64}
    {Mt M' : Mem} {img mv : Nat → BitVec 8} {k need : Nat}
    (hok : StdioOK img) (himp : ImpureImg img) (hMt : ∀ a, stdioExcl a → imgM Mt a = img a)
    (hR : RetOK R R' a0) (h1 : R 1 = r) (h2 : R 2 = s)
    (hcs : ∀ x ∈ Newlib.calleeSaved, R x = cs x) (hs4 : 0x8001c168 ≤ s.toNat - k)
    (hK : MemKeep Mt M' (outKeep s k))
    (hp : ldv .ld M' 0x8001bb20 = 0x8001bb97#64) (hw : ldv .lw M' 0x8001bb2c = 0#64)
    (hf : ldv .lhu M' 0x8001bb30 = 0x200a#64)
    (hm : Matches iRegs (outS s need) r R' M' rv mv) (ht : t = o ++ frag) :
    OutEnd o frag r s cs t rv mv := by
  have hk : ∀ x ∈ iRegs, x ≠ 32 → x ≠ 10 → x ∉ callClob → rv x = R x := fun x hx h32 h10 hc => by
    rw [hm.regs x hx h32, hR.keep x hx h32 h10 hc]
  have hmv : ∀ a, outS s need a → mv a = imgM M' a := hm.img
  have hW : ∀ a, outW a → mv a = imgM M' a := fun a ha => hmv a (.inl ⟨by
    unfold outW at ha; unfold stdioFoot Stdio.InRange; omega, by unfold outW at ha; unfold impureW; omega⟩)
  have hsv : ∀ x ∈ Newlib.calleeSaved, x ∈ iRegs ∧ x ≠ 32 ∧ x ≠ 10 ∧ x ∉ callClob := by decide
  refine ⟨ht, hm.pc, by rw [hk 1 (by decide) (by decide) (by decide) (by decide), h1],
    by rw [hk 2 (by decide) (by decide) (by decide) (by decide), h2],
    fun x hx => by
      obtain ⟨a, b, c, d⟩ := hsv x hx
      rw [hk x a b c d, hcs x hx], ?_⟩
  refine StdioOK.written hok (fun a ha hn => ?_) ?_ ?_ ?_
  · by_cases hi : impureW a
    · simp only [hi, ite_true]; exact (himp a hi).symm
    · simp only [hi, ite_false]
      rw [hmv a (.inl ⟨ha, hi⟩), hK.keep a ?_, hMt a ⟨ha, hi⟩]
      unfold outKeep; unfold stdioFoot Stdio.InRange at ha; unfold outW at hn; omega
  · rw [imgLE_congr (img' := imgM M') (fun i hi => by
      rw [if_neg (show ¬ impureW _ by unfold impureW; omega), hW _ (by unfold outW; omega)])]
    rw [ldv_ld_imgW] at hp
    have := congrArg BitVec.toNat hp
    rw [imgW_toNat] at this
    exact this
  · rw [imgLE_congr (img' := imgM M') (fun i hi => by
      rw [if_neg (show ¬ impureW _ by unfold impureW; omega), hW _ (by unfold outW; omega)])]
    rw [ldv_lw_img] at hw
    have hl := imgLE_lt (imgM M') 0x8001bb2c 4
    have := congrArg BitVec.toNat (sext32_eq_zero hw)
    simp at this
    omega
  · rw [imgLE_congr (img' := imgM M') (fun i hi => by
      rw [if_neg (show ¬ impureW _ by unfold impureW; omega), hW _ (by unfold outW; omega)])]
    rw [ldv_lhu_img] at hf
    have hl := imgLE_lt (imgM M') 0x8001bb30 2
    have := congrArg BitVec.toNat hf
    simp at this
    omega

section Spec

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **A stdout call from its run.** The run, from the call's registers and
owned bytes (newlib's data at a `StdioOK` image), ends in `OutEnd`; the
persistent input `Rr` supplies the run's data view and its pure facts. -/
theorem outSpec_of_run {live : Nat → Prop} (Wp : MachWP (GF := GF) (vsaModel live))
    {entry : BitVec 64} {args : List (BitVec 64)} {Rr : IProp GF} {s : BitVec 64} {need : Nat}
    {cs : Nat → BitVec 64} {o frag : String} {X : Type} {Dt : X → Mem} {DA : X → List Nat}
    {Pf : X → Prop}
    (hlen : args.length ≤ 8) (hneed : need ≤ s.toNat) (hs4 : 0x8001c168 ≤ s.toNat - need)
    (hdata : iprop(Rr ∗ gp ↦ᵣ□ Newlib.gpV ∗ binImg ∗ impureRO) ⊢
      ∃ x, roOwn roR (stdioText ++ dataOf (Dt x) (DA x)) ∗ ⌜Pf x⌝)
    (hrun : ∀ (x : X) (R : Nat → BitVec 64) (Mt : Mem) (r : BitVec 64) (img : Nat → BitVec 8),
      r.toNat % 4 = 0 → R 1 = r → R 2 = s → (∀ i (h : i < args.length), R (10 + i) = args[i]) →
      (∀ x ∈ Newlib.calleeSaved, R x = cs x) → StdioOK img → ImpureImg img →
      (∀ a, stdioExcl a → imgM Mt a = img a) → Pf x →
      (∀ q ∈ dataOf (Dt x) (DA x), ¬ outS s need q.1) →
      SWPO live (stdioText ++ dataOf (Dt x) (DA x)) iRegs (outS s need) (OutEnd o frag r s cs) o
        entry R Mt) :
    ⊢ outSpec live Wp entry args Rr s need cs o frag := by
  classical
  unfold outSpec fnSpecW
  iintro !> %r %Φ Hpc Hra ⟨%hal, Hargs, HR, Hw, Hcon, Hcf⟩ Hk
  unfold callFrame
  icases Hcf with ⟨Hsp, Hst, Hcs, Ht, #Hgp, #Himg⟩
  ihave ⟨%R, Hregs, %⟨h32, h1, h2, hargs, hcs⟩⟩ := call_regs entry r s args cs hlen $$
    [Hpc Hra Hargs Hsp Hcs Ht]
  · iframe Hpc Hra Hargs Hsp Hcs Ht
  unfold stdioW stdioOwn stdioAt
  icases Hw with ⟨⟨%img, %⟨hok, himp⟩, Hx, #Himp⟩, He⟩
  ihave ⟨%x, #Hro, %hPf⟩ := hdata $$ [HR Himp]
  · iframe HR Hgp Himg Himp
  ihave ⟨%Mt, HS, %hMt⟩ := outBytes img s need hneed $$ [Hx He Hst]
  · iframe Hx He Hst
  ihave ⟨⟨HS, -⟩, %hoff⟩ := keep_pure (ownSet_ro_off (outS s need) (imgM Mt) (dataOf (Dt x) (DA x))) $$ [HS]
  · ihave #Hd := roOwn_data $$ Hro
    iframe HS Hd
  have hl := hrun x R Mt r img hal h1 h2 hargs hcs hok himp hMt hPf hoff
  have hlro := swpo_run hl (rv := R) (mv := imgM Mt) ⟨h32, fun _ _ _ => rfl, fun _ _ => rfl⟩
  iapply wp_lroW Wp hlro
  iframe Hro Hregs HS Hcon
  unfold runKontO
  iintro %t' %rv' %mv' %⟨ht, e32, e1, e2, ecs, hok'⟩ Hregs HS Hcon
  ihave ⟨Hpc, Hra, Ha, Hsp, Hcs, Ht⟩ := ret_regs r s cs rv' e32 e1 e2 ecs $$ Hregs
  ihave ⟨Hx, He, Hst⟩ := outBytes_back mv' s need hneed hs4 $$ HS
  iapply Hk $$ Hpc Hra
  rw [← ht]
  simp only []
  iframe Ha Hcon
  isplitl [Hx He]
  · iframe He
    iexists fun a => if impureW a then impureByte a else mv' a
    isplitr
    · ipureintro; exact ⟨hok', fun a ha => by simp [ha]⟩
    iframe Himp
    iapply ownSet_congr (fun a (ha : stdioExcl a) => by simp [ha.2]) $$ Hx
  · iframe Hsp Hst Hcs Ht Hgp Himg

/-- The interpreter's stack lies above `.bss`. -/
theorem bss_of_stackGeom {s : BitVec 64} {n need : Nat} (h : StackGeom s n) (hle : need ≤ n) :
    0x8001c168 ≤ s.toNat - need := by
  have h1 := h.le; have h2 := h.lo
  unfold Vsa.Sim.LayoutInstance.stackSL at h2
  simp only at h2
  omega

/-- **`fputc(c, stdout)`** prints the character (`OutHoles.fputc`, with the
stack above `.bss`). -/
theorem fputc_out (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live)) (c : BitVec 8)
    (s : BitVec 64) (cs : Nat → BitVec 64) (o : String) (hcl : CodeLive live)
    (hsp : SpIn s outNeed) (hbss : 0x8001c168 ≤ s.toNat - outNeed) :
    ⊢ outSpec live Wp fputcEntry [BitVec.zeroExtend 64 c, stdoutFile] iprop(emp) s outNeed cs o
        (toString (Char.ofNat c.toNat)) := by
  have hlo := hsp.lo
  have hhi := hsp.hi
  unfold tohostAddr outNeed at hlo; unfold outNeed at hbss
  refine outSpec_of_run (X := Unit) (Pf := fun _ => True) (Dt := fun _ => impDt)
    (DA := fun _ => accAddrs 0x8001b970 8) Wp (by simp) (by unfold outNeed; omega) hbss ?_
    (fun _ R Mt r img hal h1 h2 hargs hcs hok himp hMt _ _ => ?_)
  · iintro ⟨-, H⟩
    iexists ()
    isplitl
    · iapply roOwn_stdio $$ H
    · ipureintro; trivial
  · have hs1 : s.toNat - outNeed + 512 ≤ s.toNat := by unfold outNeed; omega
    have hs5 : 0x8001c168 ≤ s.toNat - 512 := Nat.le_trans hbss (Nat.sub_le_sub_left (by decide) _)
    obtain ⟨_, hokA⟩ := id hok
    refine fputc_run (stdioText_live hcl) hs1 hhi hbss hsp.align hal h1
      (hargs 0 (by simp)) (hargs 1 (by simp)) h2
      (consoleMt_of hokA fun a ha hi => hMt a ⟨ha, hi⟩)
      (fun R' M' hR hK hD => swpo_done fun rv mv hm => ?_)
    refine outEnd_of (k := 512) hok himp hMt hR h1 h2 hcs hs5 hK hD.p hD.w hD.flagsU hm ?_
    simp [putcs, putcStr]

end Spec

end VsaIris.Sym
