import Vsa.Compiler.SimFnExit
import Vsa.Compiler.GenLen
import Vsa.Compiler.R6Expr

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

theorem anc_zero (s : Store) (a : Addr) : anc s a 0 = a := rfl

theorem Grows.fa {V V' : View} {s s' : Store} (hg : Grows V.F s V'.F s') {a : Addr} {q : Nat × List String}
    (hq : V.F[a]? = some q) : V'.fa a = V.fa a := by
  simp [View.fa, parOf, hq, hg.objs a q hq]

theorem fnCtx_ok (L : List String) (Γ : List (List String)) {epi : Nat} (h : PosOK epi) :
    CtxOK (fnCtx (L :: Γ) epi) where
  blk := by simp [fnCtx]
  brk _ _ e := by cases e
  cont _ _ e := by cases e
  ret p dt e := by
    have e' : some (epi, 0) = some (p, dt) := e
    cases e'
    exact ⟨Nat.le_refl _, h⟩

structure CloJumped (A J : AM) (q P sp k nv : Nat) (r : BitVec 64) : Prop where
  pc : J.pc = pcOf q
  mem : J.mem = A.mem
  out : J.out = A.out
  keep : Keep [a2, a3, a4, t3, ra, t0, t1, t2, t6] A.regs J.regs
  hra : Has J.regs ra r
  h12 : Has J.regs a2 (BitVec.ofNat 64 P)
  h13 : Has J.regs a3 (BitVec.ofNat 64 (sp + 16 + 16 * (k + 1)))
  h14 : Has J.regs a4 (BitVec.ofNat 64 nv)

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem run_cloJump {V : View} {st : St} {d : Nat} {env : Addr} {Γ : List (List String)} {sp fs k pos nv : Nat}
    {A : AM} (hm : MS code T V st d env Γ sp fs A) (hA : A.pc = pcOf pos) {P q : Nat}
    (ht : rdW A.mem (sp + 16 + 16 * k) = 4) (hp : rdW A.mem (sp + 16 + 16 * k + 8) = BitVec.ofNat 64 P)
    (hn8 : (BitVec.ofNat 64 (P + 8)).toNat = P + 8) (hl8 : LdOK (P + 8)) (hq : rdW A.mem (P + 8) = pcOf q)
    (hqq : PosOK q) (hseg : Seg code pos (callCode k nv pos)) (hP : PosOK (pos + (callCode k nv pos).length))
    (htmp : 16 + 16 * (k + 1 + nv) ≤ fs) :
    Reaches code A (fun J => CloJumped A J q P sp k nv (pcOf (ccCL k nv pos + 6))) := by
  have hs := CCSegs.of hseg
  have hfin := ccFin_eq k nv pos
  obtain ⟨pc0, L0, m0, o0⟩ := A
  simp only at hA ht hp hq; subst hA
  refine ex_bind (run_dispatch hR hs hP hm.hsp hm.stk (by omega)) ?_
  rintro ⟨pc1, L1, m1, o1⟩ ⟨hm1, ho1, hk1, g6, hpc1⟩
  simp only at hm1 ho1 hk1 g6 hpc1; subst hm1 ho1 hpc1
  rw [ht, hp] at *
  simp only [dispTgt, if_true] at *
  have hcl := hs.clo
  simp only [ccClo] at hcl
  have hfinL : ccCL k nv pos + 8 ≤ pos + (callCode k nv pos).length := by
    rw [hfin]; simp only [ccFin]; omega
  have hb := hm.stk.bounds
  have hfs := hm.stk.fsz
  have hL : stackLo = 0xE0000000 := rfl
  have hH : stackHi = 0x100000000 := rfl
  have ht' : tohostAddr = 0x8001ad00 := rfl
  apply run_jumps hR.fits hcl
  wp_simp [g6.wp, (hk1.has (by decide) hm.hsp).wp, hn8, hl8, hq, BitVec.ofInt_natCast]
  apply run_jumps hR.fits ((hcl.drop 7).cast (pos' := ccCL k nv pos + 7) rfl)
  wp_simp [pcOf_aligned hqq]
  refine reach_here ⟨rfl, rfl, rfl, by reg_simp []; exact hk1.mono (by decide), by reg_simp [] <;> rfl,
    by reg_simp [], ?_, by reg_simp []⟩
  reg_simp []
  rw [show sp + (16 + 16 * (k + 1)) = sp + 16 + 16 * (k + 1) by omega]

theorem cClosure {st : St} {d : Nat} {a : Addr} {cd : ClosureData} {vs : List Value} {st' : St}
    {status : Status} {v : Value} {nb : Nat} (hcd : st.store.closures[a]? = some cd)
    (hlen : vs.length = cd.params.length) (hd : d < maxCallDepth)
    (hB : QSpec code T ⟨entryStore st.store cd vs, st.out⟩ (d + 1) st.store.frames.size cd.body st' status nb)
    (hst : status = .normal ∧ v = .null ∨ status = .ret v) {n : Nat} (hn : envBytes + nb ≤ n) :
    CSpec code T st d (.closure a) vs st' v n := by
  intro V env Γ sp fs k pos A hm hA hf hvs hmax hseg hP htmp
  have hs := CCSegs.of hseg
  have hfin := ccFin_eq k vs.length pos
  obtain ⟨pc0, L0, m0, o0⟩ := A
  simp only at hA; subst hA
  obtain ⟨ht4, hpa⟩ : rdW m0 (sp + 16 + 16 * k) = 4 ∧ V.H[a]? = some (rdW m0 (sp + 16 + 16 * k + 8)).toNat := hf
  generalize hPw : rdW m0 (sp + 16 + 16 * k + 8) = pw at hpa
  obtain ⟨q, Γc, hc1, hc2, hc3, hc4, hc5, hc6⟩ := hm.clo a cd pw.toNat hcd hpa
  obtain ⟨dA, cA, hco⟩ := hm.rel.clo.obj a cd pw.toNat hcd hpa
  have hco1 := hco.lo; have hco2 := hco.hi; have hco3 := hco.al; have hptr := hm.img.ptr.hi
  obtain ⟨hob, hoe, ht⟩ := obj_consts
  have hpw : pw = BitVec.ofNat 64 pw.toNat := by simp
  generalize hP' : pw.toNat = P at hpw hpa hc1 hc2 hco hco1 hco2 hco3
  subst hpw
  have hcl := hs.clo
  simp only [ccClo] at hcl
  have hfinL : ccCL k vs.length pos + 8 ≤ pos + (callCode k vs.length pos).length := by
    rw [hfin]; simp only [ccFin]; omega
  have hq8 : PosOK (ccCL k vs.length pos + 8) := posOK_le hP hfinL
  have hqq : PosOK q := posOK_le hc5 (by omega)
  have hb := hm.stk.bounds
  have hfs := hm.stk.fsz
  have hL : stackLo = 0xE0000000 := rfl
  have hH : stackHi = 0x100000000 := rfl
  have hma : maxArgs = 32 := rfl
  refine ex_bind (run_cloJump hR hm (A := ⟨pcOf pos, L0, m0, o0⟩) rfl ht4 hPw (toNat_ofNat_lt (by omega))
    (by unfold LdOK; omega) hc2 hqq hseg hP htmp) fun J hJ => ?_
  obtain ⟨pcJ, LJ, mJ, oJ⟩ := J
  obtain ⟨hpcJ, hmJ, hoJ, hkJ, g1, g12, g13, g14⟩ := hJ
  simp only at hpcJ hmJ hoJ hkJ g1 g12 g13 g14; subst mJ oJ

  have hmq := hm.keep hkJ (pc := pcJ)
  refine ex_bind (run_entry hR (k := k) hmq hcd hpa hc1 hc3 hc4 hc5 hc6 hlen hd hpcJ g1 g12 g13 g14 hvs htmp
    hmax) ?_
  rintro E (⟨h1, h2⟩ | hE)
  · refine reach_here (.inl ⟨h1, fun hr => ?_⟩)
    have := hr.1; have hLl := hc6.2.1; unfold envBytes at hn; omega

  have h := And.intro hc4 hc5
  rw [fnCode_eq, List.append_assoc, List.append_assoc] at h
  simp only [↓segP_app, fnPost, fnHead_length, paramCopies_length, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.reduceAdd] at h
  obtain ⟨-, -, -, ⟨sBody, pB⟩, sPost, pPost⟩ := h
  rw [show q + 14 + 8 * cd.params.length + 1 = fnBody cd.params q from rfl] at sBody pB sPost pPost
  have hSh : (fnCtx (frameNames cd.params cd.body :: Γc) (fnBody cd.params q +
      (gseq T (fnCtx (frameNames cd.params cd.body :: Γc) 0) (fnBody cd.params q) cd.body).length + 2)).Sh
      (fnCtx (frameNames cd.params cd.body :: Γc) 0) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hlb := gseq_len T hSh (fnBody cd.params q) cd.body
  rw [hlb] at sPost pPost
  have hctx := fnCtx_ok (frameNames cd.params cd.body) Γc (posOK_le pPost (by omega) : PosOK (fnBody cd.params q +
    (gseq T (fnCtx (frameNames cd.params cd.body :: Γc) 0) (fnBody cd.params q) cd.body).length + 2))
  refine ex_bind (hB _ _ (sp - frameSize cd.body) (frameSize cd.body) _ E hE.ms hE.pc hc6.2.2.2 hctx sBody
    pB (by simp [frameSize])) ?_
  rintro B (⟨h1, h2⟩ | ⟨Ve, hpost⟩)
  · refine reach_here (.inl ⟨h1, fun hr => h2 ⟨?_, ?_⟩⟩)
    · have := hr.1; have hLl := hc6.2.1; simp only [View.enter]; unfold envBytes at hn; omega
    · have := hr.2; simp only [View.enter]; omega

  have hEst := hE.stack
  have hbsp : stackLo ≤ sp - frameSize cd.body := by
    have := hm.stk.room
    have : maxFS ≤ (maxCallDepth - d) * maxFS := Nat.le_mul_of_pos_left _ (by omega)
    have hM : maxFS = 2048 := rfl
    have := hc6.2.2.1; simp only [frameSize]; omega
  have hfs' : frameSize cd.body ≤ sp := by
    have := hm.stk.room
    have : maxFS ≤ (maxCallDepth - d) * maxFS := Nat.le_mul_of_pos_left _ (by omega)
    have hM : maxFS = 2048 := rfl
    have := hc6.2.2.1; simp only [frameSize]; omega
  have hfsz : frameSize cd.body ≤ 1936 := by have := hc6.2.2.1; simp only [frameSize]; omega
  have hfs16 : 16 ≤ frameSize cd.body := by simp only [frameSize]; omega
  have hspal : (sp - frameSize cd.body) % 16 = 0 := by simp only [frameSize]; omega
  have hsv : rdW B.mem (sp - frameSize cd.body) = pcOf (ccCL k vs.length pos + 6) := by
    rw [hpost.stack.low _ (Nat.le_refl _) (by omega) (by omega)]; exact hE.ra
  have hse : rdW B.mem (sp - frameSize cd.body + 8) = BitVec.ofNat 64 (V.fa env) := by
    rw [hpost.stack.low _ (by omega) (by omega) (by omega)]; exact hE.env
  have hmB : Agree m0 B.mem sp stackHi := hE.stack.trans (by
    have := hpost.stack.high; rwa [show sp - frameSize cd.body + frameSize cd.body = sp by omega] at this)
  have hvgrow : VGrow V st.store Ve st'.store := hE.grow.trans hpost.grow
  have hraa : (rdW B.mem (sp - frameSize cd.body)).toNat % 4 = 0 := by
    rw [hsv]; exact pcOf_aligned (posOK_le hq8 (by omega))

  have finish : ∀ (R : AM) (MB : MS code T Ve st' (d + 1) st.store.frames.size
      (frameNames cd.params cd.body :: Γc) (sp - frameSize cd.body) (frameSize cd.body) B),
      R.pc = pcOf (ccCL k vs.length pos + 6) → R.mem = B.mem → R.out = B.out →
      Has R.regs envR (BitVec.ofNat 64 (V.fa env)) → Has R.regs spR (BitVec.ofNat 64 sp) →
      Has R.regs depR (BitVec.ofNat 64 d) → Keep [a0, a1, ra, t6, envR, spR, depR] B.regs R.regs →
      InA Ve.H B.mem Ve.h R.regs v →
      Reaches code R (fun B => B.pc = pcOf errPos ∧ ¬Room V n ∨
        B.pc = pcOf (pos + (callCode k vs.length pos).length) ∧
        ∃ V', EPost code T V st d env Γ sp fs (k + 1 + vs.length) ⟨pcOf pos, L0, m0, o0⟩ n st' v V' B) := by
    intro R MB hpcR hmR hoR g9 g2 g24 hkR hvR
    obtain ⟨pcR, LR, mR, oR⟩ := R
    simp only at hpcR hmR hoR g9 g2 g24 hkR hvR; subst hpcR hmR hoR
    have hF : PosOK (ccFin k vs.length pos) := posOK_le hP (by omega)
    apply run_jumps hR.fits ((hcl.drop 6).cast (pos' := ccCL k vs.length pos + 6) rfl)
    wp_simp [hF]
    obtain ⟨fq, hfq⟩ := hm.chn.head'
    have hfa := hvgrow.grows.fa hfq
    have hw : Within V Ve n := by
      have h1 := hpost.within.1; have h2 := hpost.within.2; have hLl := hc6.2.1
      simp only [View.enter] at h1 h2; unfold envBytes at hn
      exact ⟨by omega, by omega⟩
    refine reach_here (.inr ⟨by rw [hfin], Ve, ?_⟩)
    exact {
      ms := {
        rel := MB.rel
        img := MB.img
        clo := MB.clo
        chn := hm.chn.grow hvgrow.grows
        out := MB.out
        ho := hkR.has (by decide) MB.ho
        hf := hkR.has (by decide) MB.hf
        henv := by rw [hfa]; exact g9
        hsp := g2
        hdep := g24
        stk := hm.stk
        hfal := MB.hfal }
      val := hvR
      grow := hvgrow
      within := hw
      stack := ⟨hmB.mono (Nat.le_refl _) (by have := hm.stk.top; omega), hmB.mono (by omega) (Nat.le_refl _)⟩
      obj := hE.obj.trans hpost.obj (Nat.le_refl _) }
  have hstop : sp - frameSize cd.body + frameSize cd.body ≤ stackHi := by have := hm.stk.top; omega
  rcases hst with ⟨rfl, rfl⟩ | rfl
  · obtain ⟨hpcB, MB⟩ := hpost.out
    obtain ⟨pcB, LB, mB, oB⟩ := B
    simp only at hpcB MB hsv hse hmB hraa; subst hpcB
    rw [hlb]
    refine ex_bind (run_fnNull hR sPost MB.hsp MB.hdep hbsp hstop hspal hfsz hfs16 hraa) ?_
    rintro R ⟨hpcR, hmR, hoR, g9, g2, g24, hkR, g10, g11⟩
    exact finish R MB (hpcR.trans hsv) hmR hoR (by rw [← hse]; exact g9)
      (by rw [show sp - frameSize cd.body + frameSize cd.body = sp by omega] at g2; exact g2) g24 hkR
      ⟨0, 0, g10, g11, rfl, rfl⟩
  · obtain ⟨⟨hpcB, MB⟩, hvB⟩ := hpost.out
    obtain ⟨pcB, LB, mB, oB⟩ := B
    simp only at hpcB MB hvB hsv hse hmB hraa; subst hpcB
    refine reaches_pc (q' := fnBody cd.params q + (gseq T (fnCtx (frameNames cd.params cd.body :: Γc) 0)
      (fnBody cd.params q) cd.body).length + 2) rfl ?_
    refine ex_bind (run_fnRet hR sPost MB.hsp MB.hdep hbsp hstop hspal hfsz hfs16 hraa) ?_
    rintro R ⟨hpcR, hmR, hoR, g9, g2, g24, hkR⟩
    obtain ⟨tv, pv, g10, g11, hvv⟩ := hvB
    exact finish R MB (hpcR.trans hsv) hmR hoR (by rw [← hse]; exact g9)
      (by rw [show sp - frameSize cd.body + frameSize cd.body = sp by omega] at g2; exact g2) g24
      ((hkR.mono (by decide)))
      ⟨tv, pv, hkR.has (by decide) g10, hkR.has (by decide) g11, hvv⟩

end

end Vsa.Compiler
