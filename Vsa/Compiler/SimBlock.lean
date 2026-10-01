import Vsa.Compiler.SimSeq
import Vsa.Compiler.R6Keys

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

theorem ExitAt.leave {code : List Ins} {T : List String} {V' : View} {st' : St} {d : Nat} {env inner : Addr}
    {C : GCtx} {L : List String} {sp fs : Nat} {tgt : Option (Nat × Nat)} {B : AM}
    (h : ExitAt code T V' st' d inner (C.enter L) sp fs tgt B) (htgt : ∀ p dt, tgt = some (p, dt) → dt ≤ C.blk)
    {fr : Frame} (hfr : st'.store.frames[inner]? = some fr) (hpar : fr.parent = some env) :
    ExitAt code T V' st' d env C sp fs tgt B := by
  cases tgt with
  | none => exact h
  | some pt =>
    obtain ⟨p, dt⟩ := pt
    have hdt := htgt p dt rfl
    obtain ⟨h1, h2⟩ := h
    refine ⟨h1, ?_⟩
    have e1 : (C.enter L).blk - dt = C.blk - dt + 1 := by simp [GCtx.enter]; omega
    rw [e1, anc_succ_of hfr hpar] at h2
    simpa [GCtx.enter] using h2

theorem StOut.leave {code : List Ins} {T : List String} {V' : View} {st' : St} {d : Nat} {env inner : Addr}
    {C : GCtx} {L : List String} {sp fs fin fin' : Nat} {B : AM} {t : Status} (hC : CtxOK C)
    (h : StOut code T V' st' d inner (C.enter L) sp fs fin B t) (ht : t ≠ .normal)
    {fr : Frame} (hfr : st'.store.frames[inner]? = some fr) (hpar : fr.parent = some env) :
    StOut code T V' st' d env C sp fs fin' B t := by
  cases t with
  | normal => exact absurd rfl ht
  | brk => exact ExitAt.leave h (fun p dt e => (hC.brk p dt e).1) hfr hpar
  | cont => exact ExitAt.leave h (fun p dt e => (hC.cont p dt e).1) hfr hpar
  | ret v => exact ⟨ExitAt.leave h.1 (fun p dt e => (hC.ret p dt e).1) hfr hpar, h.2⟩

theorem CtxOK.enter {C : GCtx} (h : CtxOK C) (L : List String) : CtxOK (C.enter L) where
  blk := by have := h.blk; simp [GCtx.enter]; omega
  brk p dt e := by have := h.brk p dt e; simp only [GCtx.enter]; omega
  cont p dt e := by have := h.cont p dt e; simp only [GCtx.enter]; omega
  ret p dt e := by have := h.ret p dt e; simp only [GCtx.enter]; omega

structure Entered' (code : List Ins) (T : List String) (V : View) (st : St) (d : Nat) (env : Addr)
    (Γ : List (List String)) (sp fs : Nat) (L : List String) (A B : AM) : Prop where
  ms : MS code T (V.enter L) ⟨(st.store.allocFrame (some env)).1, st.out⟩ d st.store.frames.size (L :: Γ) sp fs B
  out : OutFrames A.mem B.mem (V.hF + 8 + 16 * L.length)
  grow : VGrow V st.store (V.enter L) (st.store.allocFrame (some env)).1
  par : ((st.store.allocFrame (some env)).1).frames[st.store.frames.size]? = some ⟨some env, []⟩

theorem OutFrames.stackKeep {m m' : Mem} {hF : Nat} (ho : OutFrames m m' hF) (hF' : hF ≤ frameEnd) {sp fs k : Nat}
    (hsp : stackLo ≤ sp) : StackKeep m m' sp fs k := ho.stack hF' hsp

section
variable {code : List Ins} (hR : RTLoaded code)
include hR

theorem run_enterFrame {T : List String} {V : View} {st : St} {d : Nat} {env : Addr} {Γ : List (List String)}
    {sp fs pos : Nat} {A : AM} (hm : MS code T V st d env Γ sp fs A) (hA : A.pc = pcOf pos) {L : List String}
    (hL : L.length ≤ 120) (hnd : L.Nodup) (hseg : Seg code pos (enterFrame L pos)) (hP : PosOK (pos + 4)) :
    Reaches code A (fun B => (B.pc = pcOf errPos ∧ frameEnd < V.hF + 8 + 16 * L.length) ∨
      (B.pc = pcOf (pos + 4) ∧ Entered' code T V st d env Γ sp fs L A B)) := by
  obtain ⟨pc0, L0, m, o⟩ := A
  simp only at hA; subst hA
  have k9 := has_mem hm.henv (by decide); have e9 := srcVal_of_has hm.henv
  simp only [envR] at k9 e9
  have hLl : L.length < 2048 := by omega
  have hp3 : PosOK (pos + 3) := posOK_le hP (by omega)
  apply run_jumps hR.fits hseg
  wp_simp [enterFrame, k9, e9, hp3]
  have hlo := hm.rel.lo
  have htopF := hm.rel.top
  have hfe : frameEnd = 0x90000000 := rfl
  have hfb : frameBase = 0x80100000 := rfl
  have hfal := hm.hfal
  refine ex_bind (run_nf hR.fits hR.nf (n := L.length) (by reg_simp []) (by reg_simp []; rfl)
    (by reg_simp []; exact hm.hf) (by reg_simp []) (pcOf_aligned hp3) ⟨hlo, hfal, htopF⟩ (by omega)) ?_
  rintro ⟨pc3, L3, m3, o3⟩ (⟨hpc3, hroomF, hm3, ho3, g14, g23, hk3⟩ | ⟨hpc3, hov⟩)
  rotate_left
  · exact reach_here (.inl ⟨hpc3, hov⟩)
  simp only at hpc3 hroomF hm3 ho3 g14 g23 hk3
  subst hpc3 hm3 ho3
  obtain ⟨fr0, hfr0⟩ := hm.chn.frame
  have henvlt : env < st.store.frames.size := (Array.getElem?_eq_some_iff.mp hfr0).1
  obtain ⟨hs3, hg3, -, hF3, hout3, -⟩ := hm.rel.alloc_frame (par := some env) (L := L)
    (fun b hb => by cases hb; exact henvlt) hfal hlo hroomF hnd hL
  have k14 := has_mem g14 (by decide); have e14 := srcVal_of_has g14
  simp only [a4] at k14 e14
  apply run_whole hR.fits (hseg.drop 3 |>.cast rfl)
  wp_simp [enterFrame, k14, e14]
  have hobj3 := hout3.obj (h := V.h) hroomF
  have hlen' : st.store.frames.size = V.F.length := hm.rel.len.symm
  have hfaE : (V.enter L).fa st.store.frames.size = V.hF := View.fa_eq (V := V.enter L) hF3
  refine reach_here (.inr ⟨by simp, ?_, hout3, ⟨hg3, List.prefix_refl _, by simp only [View.enter]; omega,
    by simp only [View.enter]; omega⟩, by simp [Store.allocFrame]⟩)
  exact {
    rel := hs3
    img := hm.img.transport hobj3 (Nat.le_refl _) hm.img.ptr
    clo := hm.clo.grow hm.rel.clo hobj3 hg3 rfl rfl (fun b ⟨fr, hb'⟩ =>
      View.fa_append (by rw [← hlen']; exact (Array.getElem?_eq_some_iff.mp hb').1))
    chn := ChainL.push (hm.chn.grow hg3) (by simp [Store.allocFrame] : _ = some ⟨some env, []⟩) rfl hF3
    out := hm.out
    ho := by reg_simp []; exact hk3.has (by decide) (by reg_simp []; exact hm.ho)
    hf := by reg_simp []; exact g23
    henv := by rw [hfaE]; reg_simp []
    hsp := by reg_simp []; exact hk3.has (by decide) (by reg_simp []; exact hm.hsp)
    hdep := by reg_simp []; exact hk3.has (by decide) (by reg_simp []; exact hm.hdep)
    stk := hm.stk
    hfal := by simp only [View.enter]; omega }

theorem run_leave {T : List String} {V : View} {st : St} {d : Nat} {env inner : Addr} {Γ : List (List String)}
    {L : List String} {sp fs pos : Nat} {A : AM} (hm : MS code T V st d inner (L :: Γ) sp fs A)
    (hA : A.pc = pcOf pos) {fr : Frame} (hfr : st.store.frames[inner]? = some fr) (hpar : fr.parent = some env)
    (hseg : Seg code pos [.ld envR envR]) :
    Reaches code A (fun B => B.pc = pcOf (pos + 1) ∧ MS code T V st d env Γ sp fs B ∧ B.mem = A.mem ∧
      B.out = A.out) := by
  obtain ⟨pc0, L0, m, o⟩ := A
  simp only at hA; subst hA
  obtain ⟨f, P⟩ := hm.popScope hfr hpar
  apply run_whole hR.fits hseg
  wp_simp [hm.keys.row.wp, P.fa, P.nat]
  refine ⟨P.ld, reach_here ⟨by simp, ?_, rfl, rfl⟩⟩
  rw [P.word]
  exact hm.reseat rfl rfl P.chn (hm.keys.setEnv _)

theorem sBlock {T : List String} {st : St} {d : Nat} {env : Addr} {ss : List Stmt} {store' : Store}
    {inner : Addr} {st' : St} {status : Status} {n : Nat}
    (halloc : st.store.allocFrame (some env) = (store', inner))
    (hQ : QSpec code T ⟨store', st.out⟩ d inner ss st' status n) :
    SSpec code T st d env (.block ss) st' status (envBytes + n) := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp
  obtain ⟨hL, hwss⟩ := hwf
  have hst' : store' = (st.store.allocFrame (some env)).1 := by rw [halloc]
  have hin : inner = st.store.frames.size := by
    have : inner = (st.store.allocFrame (some env)).2 := by rw [halloc]
    rw [this]; rfl
  subst hst' hin
  simp only [gstmt] at hseg hP ⊢
  obtain ⟨s12, s3⟩ := hseg.append
  obtain ⟨s1, s2⟩ := s12.append
  have e4 : (enterFrame (frameNames [] ss) pos).length = 4 := rfl
  simp only [List.length_append, e4, List.length_singleton] at hP s2 s3 ⊢
  refine ex_bind (run_enterFrame hR hm hA hL (frameNames_nodup _ _) s1 (posOK_le hP (by omega))) ?_
  rintro B (⟨h1, h2⟩ | ⟨hpcB, hE⟩)
  · refine reach_here (.inl ⟨h1, fun hr => ?_⟩)
    have h1 := hr.1; have he : envBytes = 32 := rfl; omega
  refine ex_bind (hQ _ (C.enter (frameNames [] ss)) sp fs _ B hE.ms hpcB hwss (hctx.enter _) s2
    (posOK_le hP (by omega)) (by simpa [tS] using htmp)) ?_
  rintro B' (⟨h1, h2⟩ | ⟨Ve, hp⟩)
  · refine reach_here (.inl ⟨h1, fun hr => h2 ⟨?_, ?_⟩⟩)
    · have h1 := hr.1; have he : envBytes = 32 := rfl; simp only [View.enter]; omega
    · have := hr.2; simp only [View.enter]; omega
  obtain ⟨frI, hfrI, hparI⟩ := hp.grow.grows.frames _ _ hE.par
  have hparI' : frI.parent = some env := hparI
  have hwith : Within V Ve (envBytes + n) := by
    have h1 := hp.within.1; have h2 := hp.within.2
    simp only [View.enter] at h1 h2; unfold envBytes
    exact ⟨by omega, by omega⟩
  have hgrow : VGrow V st.store Ve st'.store := hE.grow.trans hp.grow
  have hb := hm.stk.bounds
  have hstk : StackKeep A.mem B'.mem sp fs 0 := (hE.out.stackKeep hE.ms.rel.top hb.1).trans hp.stack
  have hobj : ObjAgree A.mem B'.mem V.h := (hE.out.obj hE.ms.rel.top).trans hp.obj (Nat.le_refl _)
  by_cases ht : status = .normal
  · subst ht
    obtain ⟨hpc', hm'⟩ := hp.out
    refine reaches_mono (run_leave hR hm' hpc' hfrI hparI' (s3.cast (by rw [← Nat.add_assoc]))) ?_
    rintro B'' ⟨g1, g2, g3, g4⟩
    refine .inr ⟨Ve, ⟨by rw [g1]; congr 1 <;> omega, g2⟩, hgrow, hwith, by rw [g3]; exact hstk,
      by rw [g3]; exact hobj⟩
  · exact reach_here (.inr ⟨Ve, hp.out.leave hctx ht hfrI hparI', hgrow, hwith, hstk, hobj⟩)

end

end Vsa.Compiler
