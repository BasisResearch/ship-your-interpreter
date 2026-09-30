import Vsa.Compiler.SetupStr

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

structure SetupOK (p : Program) : Prop where
  lat : ∀ s ∈ strTab p, Latin1 s
  tab : strOff (strTab p) (strTab p).length ≤ 0x100000
  glob : (globalNames p).length ≤ 120
  tmp : tSeq p ≤ 120

def view0 (p : Program) : View :=
  ⟨[(frameBase, globalNames p)], [], frameBase + 8 + 16 * (globalNames p).length,
    objBase + strOff (strTab p) (strTab p).length⟩

def store0 : Store := ⟨#[], #[]⟩

theorem addNames_prefix : ∀ (xs l : List String), ∃ r, addNames l xs = l ++ r
  | [], l => ⟨[], by simp [addNames]⟩
  | x :: xs, l => by
    obtain ⟨r, hr⟩ := addNames_prefix xs (addName l x)
    have e : addNames l (x :: xs) = addNames (addName l x) xs := rfl
    rw [e, hr]
    unfold addName
    split
    · exact ⟨r, rfl⟩
    · exact ⟨[x] ++ r, by simp⟩

theorem strOff_append : ∀ (l r : List String) (i : Nat), i ≤ l.length → strOff (l ++ r) i = strOff l i
  | [], _, i, h => by simp at h; subst h; cases ‹List String› <;> rfl
  | s :: l, r, 0, _ => rfl
  | s :: l, r, i + 1, h => by
    simp only [List.cons_append, strOff]
    rw [strOff_append l r i (by simpa using h)]

theorem globalNames_eq (p : Program) : ∃ r, globalNames p = ["print", "println", "assert"] ++ r := by
  obtain ⟨r, hr⟩ := addNames_prefix (p.flatMap declsS) ["print", "println", "assert"]
  refine ⟨r, ?_⟩
  unfold globalNames frameNames
  rw [List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  simpa [addNames, addName] using hr

theorem strTab_eq (p : Program) : ∃ r, strTab p = fixedStrs ++ r := addNames_prefix _ _

theorem objImg0 {p : Program} (hok : SetupOK p) {m : Mem}
    (hstr : ∀ i < (strTab p).length, StrW m (objBase + strOff (strTab p) i) ((strTab p).getD i "").toList) :
    ObjImg (strTab p) m (view0 p).h := by
  obtain ⟨r, hr⟩ := strTab_eq p
  have hob : objBase = 0x90000000 := rfl
  have hoe : objEnd = 0xE0000000 := rfl
  have hlen : fixedStrs.length ≤ (strTab p).length := by rw [hr]; simp
  have hf8 : fixedStrs.length = 8 := rfl
  have htab := hok.tab
  simp only [view0]
  refine ⟨fun i hi => ?_, ?_, fun s hs => ?_, ⟨by omega, by omega, ?_⟩⟩
  · have := hstr i (by omega)
    have e1 : strOff (strTab p) i = strOff fixedStrs i := by rw [hr]; exact strOff_append _ _ _ (by omega)
    have e2 : (strTab p).getD i "" = fixedStrs[i] := by
      rw [hr, List.getD_eq_getElem?_getD, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]; rfl
    rw [e1, e2] at this
    exact this
  · have e1 : strOff (strTab p) 8 = strOff fixedStrs 8 := by rw [hr]; exact strOff_append _ _ _ (by omega)
    have e2 := strOff_mono (strTab p) (show 8 ≤ (strTab p).length by omega)
    have e3 : strOff fixedStrs 8 = strOff fixedStrs 7 + 40 := by decide
    unfold fixedAddr
    omega
  · have hi : (strTab p).idxOf s < (strTab p).length := List.idxOf_lt_length_of_mem hs
    have hget : (strTab p).getD ((strTab p).idxOf s) "" = s := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, List.getElem_idxOf]
    have hsucc := strOff_succ (strTab p) _ hi
    have hmono := strOff_mono (strTab p) (show (strTab p).idxOf s + 1 ≤ (strTab p).length by omega)
    have := hstr _ hi
    rw [hget] at this hsucc
    unfold strSize at hsucc
    exact ⟨this, by unfold strAddr; omega, by unfold strAddr; rw [String.length_toList]; omega⟩
  · have := strOff_al (strTab p) (strTab p).length
    omega

theorem setupCode_eq (p : Program) : setupCode p =
    strTabCode (strTab p) ++
      (liN spR (stackHi - frameSize p) ++ [mvi depR 0] ++ liN hpF frameBase ++
        liN hpO (objBase + strOff (strTab p) (strTab p).length) ++
        [mvi a5 (globalNames p).length, mvi a6 0, Call (mainPos + (strTabCode (strTab p) ++
          liN spR (stackHi - frameSize p) ++ [mvi depR 0] ++ liN hpF frameBase ++
          liN hpO (objBase + strOff (strTab p) (strTab p).length)).length + 2) nfPos]) ++
      ([mv envR a4] ++ natCode 0 ++ natCode 1 ++ natCode 2) := by
  simp only [setupCode, nativeCode, List.append_assoc, List.cons_append, List.nil_append]

theorem stackOK0 (p : Program) (h : tSeq p ≤ 120) : StackOK 0 (stackHi - frameSize p) (frameSize p) := by
  have hmc : maxCallDepth = 1000 := rfl
  have hM : maxFS = 2048 := rfl
  have hsH : stackHi = 0x100000000 := rfl
  have hsL : stackLo = 0xE0000000 := rfl
  have hfs : frameSize p = 16 + 16 * tSeq p := rfl
  exact ⟨Nat.zero_le _, by rw [hmc, hM]; omega, by omega, by omega, by omega⟩

theorem storeRel0 {m : Mem} {h : Nat} : StoreRel [] [] store0 m frameBase h where
  len := rfl
  frame := fun _ _ _ _ h => by simp [store0] at h
  region := fun _ _ _ h => by simp at h
  nodup := fun _ _ _ h => by simp at h
  disjoint := fun _ _ _ _ _ _ _ h => by simp at h
  parents := fun _ _ _ h => by simp [store0] at h
  clo := ⟨rfl, fun _ _ _ h => by simp [store0] at h⟩
  inj := fun _ _ _ h => by simp at h
  top := by decide
  lo := Nat.le_refl _

theorem initSt_eq : ⟨(((store0.allocFrame none).1.define 0 "print" (.native .print)).define 0 "println"
    (.native .println)).define 0 "assert" (.native .assert), ""⟩ = initSt := by
  simp [store0, Store.allocFrame, Store.define, initSt]

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem run_nat {V : View} {st : St} {d : Nat} {env : Addr} {Γ : List (List String)} {sp fs pos : Nat} {A : AM}
    (hm : MS code T V st d env Γ sp fs A) (hA : A.pc = pcOf pos) {x : String} {f : NativeFn} {i : Nat}
    (hx : slotOf (Γ.headD []) x = some i) (hfi : natId f = BitVec.ofNat 64 i) (hi : i < 3)
    (hseg : Seg code pos (natCode i)) :
    Reaches code A (fun B => B.pc = pcOf (pos + 6) ∧
      MS code T V ⟨st.store.define env x (.native f), st.out⟩ d env Γ sp fs B) := by
  obtain ⟨pc, L, m, o⟩ := A
  simp only at hA; subst hA
  unfold natCode at hseg
  obtain ⟨s1, s2⟩ := hseg.append
  have hxm : x ∈ Γ.headD [] := List.mem_of_getElem? (slotOf_some hx)
  have s2' : Seg code (pos + 2) (storeSlot ((slotOf (Γ.headD []) x).getD 0)) := by rw [hx]; exact s2
  apply run_whole hR.fits s1
  wp_simp [BitVec.ofInt_natCast]
  have hmq := hm.transport (B := ⟨pcOf (pos + 2), gset (gset L 10 5#64) 11 (BitVec.ofNat 64 i), m, o⟩)
    (S := [a0, a1]) (by decide) (by reg_simp []; exact Keep.refl _ _) (Agree.refl _ _ _) (ObjAgree.refl _ _) rfl
  refine reaches_mono (run_storeSlot hR hmq rfl hxm s2' (v := .native f) (t := 5#64) (p := BitVec.ofNat 64 i)
    (by reg_simp []) (by reg_simp []) ⟨rfl, hfi.symm⟩) ?_
  rintro B ⟨hpc, hmB, -⟩
  exact ⟨by rw [hpc], hmB⟩

theorem run_setup (p : Program) (hok : SetupOK p) (hseg : Seg code mainPos (setupCode p))
    (hP : PosOK (mainPos + (setupCode p).length)) {L : GRegs} {m : Mem} {o : Array String}
    (ho : String.join o.toList = "") :
    Reaches code ⟨pcOf mainPos, L, m, o⟩ (fun B => B.pc = pcOf (mainPos + (setupCode p).length) ∧
      MS code (strTab p) (view0 p) initSt 0 0 [globalNames p] (stackHi - frameSize p) (frameSize p) B) := by
  have hob : objBase = 0x90000000 := rfl
  have hoe : objEnd = 0xE0000000 := rfl
  have hfb : frameBase = 0x80100000 := rfl
  have hfe : frameEnd = 0x90000000 := rfl
  have hsH : stackHi = 0x100000000 := rfl
  have hsL : stackLo = 0xE0000000 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hG := hok.glob
  have htab := hok.tab
  have htmp := hok.tmp
  have hfs : frameSize p = 16 + 16 * tSeq p := rfl
  obtain ⟨rG, hGe⟩ := globalNames_eq p
  rw [setupCode_eq] at hseg hP ⊢
  obtain ⟨s12, s3⟩ := hseg.append
  obtain ⟨s1, s2⟩ := s12.append
  simp only [List.length_append] at s2 s3 hP ⊢
  have hnf : PosOK nfPos := by unfold PosOK; decide
  refine ex_bind (run_strTab hR.fits (strTab p) hok.lat (by omega) (strTab p).length (Nat.le_refl _) mainPos L m o
    s1 (posOK_le hP (by unfold strTabCode; omega))) ?_
  rintro ⟨pc1, L1, m1, o1⟩ ⟨hpc1, ho1, -, hstr1, -⟩
  simp only at hpc1 ho1 hstr1; subst hpc1 ho1
  have himg1 := objImg0 hok hstr1

  have e11 : (liN hpF frameBase).length = 11 := rfl
  have e2 : (liN spR (stackHi - frameSize p)).length = (li 2 (BitVec.ofNat 64 (stackHi - frameSize p))).length := rfl
  have e8 : (liN hpO (objBase + strOff (strTab p) (strTab p).length)).length =
    (li 8 (BitVec.ofNat 64 (objBase + strOff (strTab p) (strTab p).length))).length := rfl
  have en0 : (natCode 0).length = 6 := rfl
  have en1 : (natCode 1).length = 6 := rfl
  have en2 : (natCode 2).length = 6 := rfl
  generalize hQ : mainPos + (strTabCode (strTab p)).length + (li 2 (BitVec.ofNat 64 (stackHi - frameSize p))).length
      + 1 + 11 + (li 8 (BitVec.ofNat 64 (objBase + strOff (strTab p) (strTab p).length))).length + 1 + 1 = Q
  have hlen : mainPos + ((strTabCode (strTab p)).length + ((liN spR (stackHi - frameSize p)).length + 1 +
      (liN hpF frameBase).length + (liN hpO (objBase + strOff (strTab p) (strTab p).length)).length + 3)) = Q + 1 := by
    omega
  simp only [List.length_cons, List.length_nil, List.length_append] at hP s3 ⊢
  have hQ1 : PosOK (Q + 1) := posOK_le hP (by omega)
  have hcall : PosOK Q := posOK_le hQ1 (by omega)
  obtain ⟨s4, s7⟩ := s3.append
  obtain ⟨s4, s6⟩ := s4.append
  obtain ⟨s4, s5⟩ := s4.append
  simp only [List.length_append, List.length_singleton] at s5 s6 s7
  have s4 := s4.cast (pos' := Q + 1) (by omega)
  have s5 := s5.cast (pos' := Q + 1 + 1) (by omega)
  have s6 := s6.cast (pos' := Q + 1 + 1 + 6) (by omega)
  have s7 := s7.cast (pos' := Q + 1 + 1 + 6 + 6) (by omega)
  apply run_jumps hR.fits s2
  wp_simp [liN, BitVec.ofInt_natCast, hcall]
  rw [hQ]
  refine ex_bind (run_nf hR.fits hR.nf (n := (globalNames p).length) (f := frameBase) (par := 0)
    (r := pcOf (Q + 1)) (by reg_simp []) (by reg_simp []) (by reg_simp []) (by reg_simp [])
    (pcOf_aligned hQ1) ⟨Nat.le_refl _, by decide, by decide⟩ (by omega)) ?_
  rintro ⟨pc2, L2, m2, o2⟩ (⟨hpc2, -, hm2, ho2, g14, g23, hk2⟩ | ⟨-, hov⟩)
  rotate_left
  · omega
  simp only at hpc2 hm2 ho2 g14 g23 hk2; subst hpc2
  have k14 := has_mem g14 (by decide); have e14 := srcVal_of_has g14
  simp only [a4] at k14 e14
  apply run_whole hR.fits s4
  wp_simp [k14, e14]

  obtain ⟨hs1, -, -, -, hout1, -⟩ := (storeRel0 (m := m1) (h := (view0 p).h)).alloc_frame (par := none)
    (L := globalNames p) (fun b hb => by cases hb) (by decide) (Nat.le_refl _) (by omega)
    (frameNames_nodup _ _) hG
  have hobj := hout1.obj (h := (view0 p).h) (by omega)
  have hkeep : ∀ r, r ∈ [2, 8, 24] → ∀ v, Has (gset (gset (gset (gset (gset (gset (gset L1 2
      (BitVec.ofNat 64 (stackHi - frameSize p))) 24 0) 23 (BitVec.ofNat 64 frameBase)) 8
      (BitVec.ofNat 64 (objBase + strOff (strTab p) (strTab p).length))) 15 (BitVec.ofNat 64 (globalNames p).length))
      16 0) 1 (pcOf (Q + 1))) r v → Has (gset L2 9 (BitVec.ofNat 64 frameBase)) r v := by
    intro r hr v hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    have hn : r ∉ nfClob := by rcases hr with rfl | rfl | rfl <;> decide
    exact (hk2.has hn hv).set_other (by omega)
  have hms : MS code (strTab p) (view0 p) ⟨(store0.allocFrame none).1, ""⟩ 0 0 [globalNames p]
      (stackHi - frameSize p) (frameSize p) ⟨pcOf (Q + 1 + 1), gset L2 9 (BitVec.ofNat 64 frameBase), m2, o2⟩ := {
    rel := by rw [hm2]; exact hs1
    img := by rw [hm2]; exact himg1.transport hobj (Nat.le_refl _) himg1.ptr
    clo := fun a cd q h _ => by simp [Store.allocFrame, store0] at h
    chn := .top rfl rfl rfl
    out := by rw [ho2]; exact ho
    ho := hkeep 8 (by decide) _ (by simp only [view0]; reg_simp [])
    hf := by simp only [view0]; exact g23.set_other (by decide)
    henv := by rw [show (view0 p).fa 0 = frameBase from rfl]; reg_simp []
    hsp := hkeep 2 (by decide) _ (by reg_simp [])
    hdep := hkeep 24 (by decide) _ (by reg_simp [])
    stk := stackOK0 p hok.tmp
    hfal := by simp only [view0]; omega }

  refine ex_bind (run_nat hR hms rfl (x := "print") (f := .print) (i := 0) (by rw [hGe]; simp [slotOf]) rfl
    (by decide) s5) ?_
  rintro B4 ⟨hpc4, hm4⟩
  refine ex_bind (run_nat hR hm4 hpc4 (x := "println") (f := .println) (i := 1) (by rw [hGe]; simp [slotOf]) rfl
    (by decide) s6) ?_
  rintro B5 ⟨hpc5, hm5⟩
  refine reaches_mono (run_nat hR hm5 hpc5 (x := "assert") (f := .assert) (i := 2) (by rw [hGe]; simp [slotOf])
    rfl (by decide) s7) ?_
  rintro B6 ⟨hpc6, hm6⟩
  refine ⟨by rw [hpc6]; congr 1; omega, ?_⟩
  rw [← initSt_eq]
  exact hm6

end

end Vsa.Compiler
