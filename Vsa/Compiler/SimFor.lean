import Vsa.Compiler.SimForDefs

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

def tOS : Option Stmt → Nat
  | some s => tS s
  | none => 0

def tOE : Option Expr → Nat
  | some e => tE e
  | none => 0

theorem tS_for (i : Option Stmt) (c st : Option Expr) (b : Stmt) :
    tS (.forStmt i c st b) = max (tOS i) (max (tOE c) (max (tOE st) (tS b))) := by
  cases i <;> cases c <;> cases st <;> rfl

theorem fHd_none (T : List String) (C : GCtx) (pos : Nat) (b : Stmt) : fHd T C pos none b = pos + 4 := rfl

theorem fPb_none (T : List String) (C : GCtx) (pos : Nat) (init : Option Stmt) (b : Stmt) :
    fPb T C pos init none b = fHd T C pos init b := rfl

theorem CtxOK.swallow {C : GCtx} (h : CtxOK C) {x : Nat} (hx : PosOK x) : CtxOK (C.swallow x) where
  blk := h.blk
  brk p dt e := by
    have e' : some (x, C.blk) = some (p, dt) := e
    cases e'; exact ⟨Nat.le_refl _, hx⟩
  cont p dt e := by
    have e' : some (x, C.blk) = some (p, dt) := e
    cases e'; exact ⟨Nat.le_refl _, hx⟩
  ret p dt e := by
    have e' : some (x, C.blk) = some (p, dt) := e
    cases e'; exact ⟨Nat.le_refl _, hx⟩

theorem StOut.swallow {code : List Ins} {T : List String} {V' : View} {st' : St} {d : Nat} {env : Addr} {C : GCtx}
    {sp fs x : Nat} {B : AM} {t : Status} (h : StOut code T V' st' d env (C.swallow x) sp fs x B t) :
    B.pc = pcOf x ∧ MS code T V' st' d env C.Γ sp fs B := by
  cases t with
  | normal => exact h
  | brk => exact ExitAt.here h
  | cont => exact ExitAt.here h
  | ret v => exact ExitAt.here h.1

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem xiNone (st : St) (d : Nat) (env : Addr) : XISpec code T st d env none st 0 := by
  intro V C pos cnd step b sp fs A hok hm hA
  exact reach_here (.inr ⟨V, ⟨by rw [hA, fHd_none], hm⟩, VGrow.refl _ _, Within.refl _ _, StackKeep.refl _ _ _ _,
    ObjAgree.refl _ _⟩)

theorem xiSome {st : St} {d : Nat} {env : Addr} {s : Stmt} {st' : St} {t : Status} {n : Nat}
    (hS : SSpec code T st d env s st' t n) : XISpec code T st d env (some s) st' n := by
  intro V C pos cnd step b sp fs A hok hm hA
  have ho := for_order T C pos (some s) cnd step b
  have hci := hok.segs.ci
  have hl := fCi_length T C pos (some s) b
  simp only [fCi] at hci hl
  have hPh : PosOK (fHd T C pos (some s) b) := posOK_le hok.pend (by omega)
  have htmp := hok.tmp
  simp only [tS] at htmp
  have hctx : CtxOK ((fC1 C (some s) b).swallow (fHd T C pos (some s) b)) := (hok.ctx.enter _).swallow hPh
  refine reaches_mono (hS V ((fC1 C (some s) b).swallow (fHd T C pos (some s) b)) sp fs (pos + 4) A hm hA hok.wi
    hctx hci (by rw [hl]; exact hPh) (by omega)) ?_
  rintro B (⟨h1, h2⟩ | ⟨V', hp⟩)
  · exact .inl ⟨h1, h2⟩
  · have hout : StOut code T V' st' d env ((fC1 C (some s) b).swallow (fHd T C pos (some s) b)) sp fs
        (fHd T C pos (some s) b) B t := by
      have := hp.out
      rw [hl] at this
      cases t with
      | normal => exact this
      | brk => exact this
      | cont => exact this
      | ret v => exact this
    exact .inr ⟨V', ⟨hout.swallow.1, hout.swallow.2⟩, hp.grow, hp.within, hp.stack, hp.obj⟩

theorem fcNone (st : St) (d : Nat) (env : Addr) : FCSpec code T st d env none st 0 := by
  intro V C pos init step b sp fs A hok hm hA
  exact reach_here (.inr ⟨V, ⟨by rw [hA, fPb_none], hm⟩, VGrow.refl _ _, Within.refl _ _, StackKeep.refl _ _ _ _,
    ObjAgree.refl _ _⟩)

theorem fcSome {st : St} {d : Nat} {env : Addr} {c : Expr} {st' : St} {v : Value} {n : Nat}
    (hE : ESpec code T st d env c st' v n) (htr : v.truthy = true) : FCSpec code T st d env (some c) st' n := by
  intro V C pos init step b sp fs A hok hm hA
  have ho := for_order T C pos init (some c) step b
  have hcc := hok.segs.cc
  simp only [fCc] at hcc
  have htmp := hok.tmp
  rw [tS_for] at htmp
  simp only [tOE] at htmp
  have hpb : fPb T C pos init (some c) b = fHd T C pos init b +
      (gexpr T (fC1 C init b).Γ 0 (fHd T C pos init b) c).length + 3 := by simp [fPb, fLc]; omega
  have hPe := hok.pend
  refine reaches_mono (run_cond hR hE (C := fC1 C init b) hm hA hok.wc hcc (by rw [← hpb]; exact posOK_le hPe (by omega))
    (posOK_le hPe (by omega)) (by omega)) ?_
  rintro B (⟨h1, h2⟩ | ⟨V1, hp⟩)
  · exact .inl ⟨h1, h2⟩
  · rw [htr, if_pos rfl, ← hpb] at hp
    exact .inr ⟨V1, hp⟩

omit hR in
theorem xsNone (st : St) (d : Nat) (env : Addr) : XSSpec code T st d env none st 0 := by
  intro V C pos init cnd b sp fs A hok hm hA
  have ho := for_order T C pos init cnd none b
  exact reach_here (.inr ⟨V, ⟨by rw [hA]; simp only [fCs, List.length_nil] at ho; congr 1 <;> omega, hm⟩,
    VGrow.refl _ _, Within.refl _ _, StackKeep.refl _ _ _ _, ObjAgree.refl _ _⟩)

omit hR in
theorem xsSome {st : St} {d : Nat} {env : Addr} {e : Expr} {st' : St} {v : Value} {n : Nat}
    (hE : ESpec code T st d env e st' v n) : XSSpec code T st d env (some e) st' n := by
  intro V C pos init cnd b sp fs A hok hm hA
  have ho := for_order T C pos init cnd (some e) b
  have hcs := hok.segs.cs
  simp only [fCs] at hcs ho
  have htmp := hok.tmp
  rw [tS_for] at htmp
  simp only [tOE] at htmp
  refine reaches_mono (hE V (fC1 C init b).Γ sp fs 0 _ A hm hA hok.ws hcs (posOK_le hok.pend (by omega))
    (by omega)) ?_
  rintro B (⟨h1, h2⟩ | ⟨h1, V1, hp⟩)
  · exact .inl ⟨h1, h2⟩
  · exact .inr ⟨V1, SPost.of_epost hp (by rw [h1]; congr 1 <;> omega) (Nat.le_refl _)⟩

theorem flCondFalse {st : St} {d : Nat} {env : Addr} {c : Expr} {step : Option Expr} {b : Stmt} {st' : St}
    {v : Value} {nc : Nat} (hE : ESpec code T st d env c st' v nc) (hfa : v.truthy = false) :
    FLSpec code T st d env (some c) step b st' .normal nc := by
  intro V C pos init sp fs A hok hm hA
  have ho := for_order T C pos init (some c) step b
  have hcc := hok.segs.cc
  simp only [fCc] at hcc
  have htmp := hok.tmp
  rw [tS_for] at htmp
  simp only [tOE] at htmp
  have hpb : fPb T C pos init (some c) b = fHd T C pos init b +
      (gexpr T (fC1 C init b).Γ 0 (fHd T C pos init b) c).length + 3 := by simp [fPb, fLc]; omega
  have hPe := hok.pend
  refine reaches_mono (run_cond hR hE (C := fC1 C init b) hm hA hok.wc hcc (by rw [← hpb]; exact posOK_le hPe (by omega))
    (posOK_le hPe (by omega)) (by omega)) ?_
  rintro B (⟨h1, h2⟩ | ⟨V1, hp⟩)
  · exact .inl ⟨h1, h2⟩
  · rw [hfa] at hp
    simp only [Bool.false_eq_true, if_false] at hp
    exact .inr ⟨V1, hp⟩

theorem for_body {st st1 st2 : St} {d : Nat} {env : Addr} {cnd step : Option Expr} {b : Stmt} {t : Status}
    {nb : Nat} (hB : SSpec code T st1 d env b st2 t nb) {V V1 : View} {C : GCtx} {pos : Nat} {init : Option Stmt}
    {sp fs : Nat} {A B : AM} {nc : Nat} (hok : ForOK code T C pos init cnd step b fs)
    (hp1 : SPost code T V st d env (fC1 C init b) sp fs (fPb T C pos init cnd b) A nc st1 .normal V1 B) :
    Reaches code B (fun B' => (B'.pc = pcOf errPos ∧ ¬ Room V (nc + nb)) ∨ ∃ V2,
      SPost code T V st d env ((fC1 C init b).loop (fEx T C pos init cnd step b) (fPs T C pos init cnd b)) sp fs
        (fPs T C pos init cnd b) A (nc + nb) st2 t V2 B') := by
  have ho := for_order T C pos init cnd step b
  have htmp := hok.tmp
  rw [tS_for] at htmp
  obtain ⟨hpc1, hm1⟩ := hp1.out
  have hPe := hok.pend
  have hbl := fBody_length T C pos init cnd step b
  refine reaches_mono (hB V1 ((fC1 C init b).loop (fEx T C pos init cnd step b) (fPs T C pos init cnd b)) sp fs
    (fPb T C pos init cnd b) B hm1 hpc1 hok.wb ((hok.ctx.enter _).loop (posOK_le hPe (by omega))
    (posOK_le hPe (by omega))) hok.segs.body (by rw [hbl]; exact posOK_le hPe (by omega)) (by omega)) ?_
  rintro B' (⟨h1, h2⟩ | ⟨V2, hp2⟩)
  · exact .inl ⟨h1, Room.not_within h2 hp1.within (by omega)⟩
  · refine .inr ⟨V2, ?_⟩
    rw [hbl, show fPb T C pos init cnd b + (fPs T C pos init cnd b - fPb T C pos init cnd b) =
      fPs T C pos init cnd b by omega] at hp2
    exact ⟨hp2.out, hp1.grow.trans hp2.grow, hp1.within.add hp2.within, hp1.stack.trans hp2.stack,
      hp1.obj.trans hp2.obj hp1.grow.le⟩

theorem flBodyBreak {st st1 st2 : St} {d : Nat} {env : Addr} {cnd step : Option Expr} {b : Stmt} {nc nb : Nat}
    (hC : FCSpec code T st d env cnd st1 nc) (hB : SSpec code T st1 d env b st2 .brk nb) :
    FLSpec code T st d env cnd step b st2 .normal (nc + nb) := by
  intro V C pos init sp fs A hok hm hA
  refine ex_bind (hC V C pos init step b sp fs A hok hm hA) ?_
  rintro B (⟨h1, h2⟩ | ⟨V1, hp1⟩)
  · exact reach_here (.inl ⟨h1, Room.not_mono h2 (by omega)⟩)
  refine reaches_mono (for_body hR hB hok hp1) ?_
  rintro B' (⟨h1, h2⟩ | ⟨V2, hp2⟩)
  · exact .inl ⟨h1, h2⟩
  · obtain ⟨hpc2, hm2⟩ := ExitAt.here hp2.out
    exact .inr ⟨V2, ⟨⟨hpc2, hm2⟩, hp2.grow, hp2.within, hp2.stack, hp2.obj⟩⟩

theorem flBodyRet {st st1 st2 : St} {d : Nat} {env : Addr} {cnd step : Option Expr} {b : Stmt} {rv : Value}
    {nc nb : Nat} (hC : FCSpec code T st d env cnd st1 nc) (hB : SSpec code T st1 d env b st2 (.ret rv) nb) :
    FLSpec code T st d env cnd step b st2 (.ret rv) (nc + nb) := by
  intro V C pos init sp fs A hok hm hA
  refine ex_bind (hC V C pos init step b sp fs A hok hm hA) ?_
  rintro B (⟨h1, h2⟩ | ⟨V1, hp1⟩)
  · exact reach_here (.inl ⟨h1, Room.not_mono h2 (by omega)⟩)
  refine reaches_mono (for_body hR hB hok hp1) ?_
  rintro B' (⟨h1, h2⟩ | ⟨V2, hp2⟩)
  · exact .inl ⟨h1, h2⟩
  · exact .inr ⟨V2, ⟨hp2.out.loop_ret, hp2.grow, hp2.within, hp2.stack, hp2.obj⟩⟩

theorem flLoop {st st1 st2 st3 st4 : St} {d : Nat} {env : Addr} {cnd step : Option Expr} {b : Stmt}
    {status status' : Status} {nc nb ns nr : Nat} (hC : FCSpec code T st d env cnd st1 nc)
    (hB : SSpec code T st1 d env b st2 status nb) (hst : status = .normal ∨ status = .cont)
    (hX : XSSpec code T st2 d env step st3 ns) (hL : FLSpec code T st3 d env cnd step b st4 status' nr) :
    FLSpec code T st d env cnd step b st4 status' (nc + nb + ns + nr) := by
  intro V C pos init sp fs A hok hm hA
  have ho := for_order T C pos init cnd step b
  refine ex_bind (hC V C pos init step b sp fs A hok hm hA) ?_
  rintro B (⟨h1, h2⟩ | ⟨V1, hp1⟩)
  · exact reach_here (.inl ⟨h1, Room.not_mono h2 (by omega)⟩)
  refine ex_bind (for_body hR hB hok hp1) ?_
  rintro B' (⟨h1, h2⟩ | ⟨V2, hp2⟩)
  · exact reach_here (.inl ⟨h1, Room.not_mono h2 (by omega)⟩)
  have hps : B'.pc = pcOf (fPs T C pos init cnd b) ∧ MS code T V2 st2 d env (fC1 C init b).Γ sp fs B' := by
    rcases hst with rfl | rfl
    · exact hp2.out
    · exact ExitAt.here hp2.out
  refine ex_bind (hX V2 C pos init cnd b sp fs B' hok hps.2 hps.1) ?_
  rintro B'' (⟨h1, h2⟩ | ⟨V3, hp3⟩)
  · exact reach_here (.inl ⟨h1, Room.not_within h2 hp2.within (by omega)⟩)
  obtain ⟨hpc3, hm3⟩ := hp3.out
  obtain ⟨pc3, L3, m3, o3⟩ := B''
  simp only at hpc3 hm3; subst hpc3
  have hPe := hok.pend
  apply run_jumps hR.fits hok.segs.jmp
  wp_simp [posOK_le hPe (by omega : fEx T C pos init cnd step b - 1 ≤ _),
    posOK_le hPe (by omega : fHd T C pos init b ≤ _)]
  refine reaches_mono (hL V3 C pos init sp fs _ hok (hm3.setpc _) rfl) ?_
  rintro B3 (⟨h1, h2⟩ | ⟨V4, hp4⟩)
  · exact .inl ⟨h1, Room.not_within h2 (hp2.within.add hp3.within) (by omega)⟩
  · exact .inr ⟨V4, ⟨hp4.out, hp2.grow.trans (hp3.grow.trans hp4.grow), (hp2.within.add hp3.within).add hp4.within,
      hp2.stack.trans (hp3.stack.trans hp4.stack), hp2.obj.trans (hp3.obj.trans hp4.obj hp3.grow.le) hp2.grow.le⟩⟩

theorem sForStart {st : St} {d : Nat} {env : Addr} {init : Option Stmt} {cnd step : Option Expr} {b : Stmt}
    {store' : Store} {outer : Addr} {st1 st2 : St} {status : Status} {ni nl : Nat}
    (halloc : st.store.allocFrame (some env) = (store', outer))
    (hI : XISpec code T ⟨store', st.out⟩ d outer init st1 ni)
    (hL : FLSpec code T st1 d outer cnd step b st2 status nl) :
    SSpec code T st d env (.forStmt init cnd step b) st2 status (envBytes + ni + nl) := by
  intro V C sp fs pos A hm hA hwf hctx hseg hP htmp
  obtain ⟨hL120, hwi, hwc, hws, hwb⟩ := hwf
  have hst' : store' = (st.store.allocFrame (some env)).1 := by rw [halloc]
  have hin : outer = st.store.frames.size := by
    have : outer = (st.store.allocFrame (some env)).2 := by rw [halloc]
    rw [this]; rfl
  subst hst' hin
  have hsegs := ForSegs.of hseg
  have hlen := for_len T C pos init cnd step b
  rw [hlen] at hP ⊢
  have ho := for_order T C pos init cnd step b
  have hok : ForOK code T C pos init cnd step b fs := ⟨hsegs, hP, hwi, hwc, hws, hwb, hctx, htmp⟩
  refine ex_bind (run_enterFrame hR hm hA hL120 (addNames_nodup _ List.nodup_nil) hsegs.ent
    (posOK_le hP (by omega))) ?_
  rintro B (⟨h1, h2⟩ | ⟨hpcB, hE⟩)
  · refine reach_here (.inl ⟨h1, fun hr => ?_⟩)
    have h1 := hr.1; have he : envBytes = 32 := rfl; omega
  refine ex_bind (hI _ C pos cnd step b sp fs B hok hE.ms hpcB) ?_
  rintro B' (⟨h1, h2⟩ | ⟨V1, hp1⟩)
  · refine reach_here (.inl ⟨h1, fun hr => h2 ⟨?_, ?_⟩⟩)
    · have h1 := hr.1; have he : envBytes = 32 := rfl; simp only [View.enter]; omega
    · have := hr.2; simp only [View.enter]; omega
  obtain ⟨hpc1, hm1⟩ := hp1.out
  refine ex_bind (hL V1 C pos init sp fs B' hok hm1 hpc1) ?_
  rintro B'' (⟨h1, h2⟩ | ⟨V2, hp2⟩)
  · refine reach_here (.inl ⟨h1, fun hr => h2 ⟨?_, ?_⟩⟩)
    · have h1 := hr.1; have h3 := hp1.within.1; have he : envBytes = 32 := rfl; simp only [View.enter] at h3; omega
    · have h1 := hr.2; have h3 := hp1.within.2; simp only [View.enter] at h3; omega
  have hp12 := hp1.seq hp2 rfl
  obtain ⟨frO, hfrO, hparO⟩ := hp12.grow.grows.frames _ _ hE.par
  have hparO' : frO.parent = some env := hparO
  have hwith : Within V V2 (envBytes + ni + nl) := by
    have h1 := hp12.within.1; have h2 := hp12.within.2
    simp only [View.enter] at h1 h2; unfold envBytes
    exact ⟨by omega, by omega⟩
  have hgrow : VGrow V st.store V2 st2.store := hE.grow.trans hp12.grow
  have hb := hm.stk.bounds
  have hstk : StackKeep A.mem B''.mem sp fs 0 := (hE.out.stackKeep hE.ms.rel.top hb.1).trans hp12.stack
  have hobj : ObjAgree A.mem B''.mem V.h := (hE.out.obj hE.ms.rel.top).trans hp12.obj (Nat.le_refl _)
  by_cases ht : status = .normal
  · subst ht
    obtain ⟨hpc', hm'⟩ := hp2.out
    refine reaches_mono (run_leave hR hm' hpc' hfrO hparO' hsegs.lv) ?_
    rintro B3 ⟨g1, g2, g3, g4⟩
    exact .inr ⟨V2, ⟨g1, g2⟩, hgrow, hwith, by rw [g3]; exact hstk, by rw [g3]; exact hobj⟩
  · exact reach_here (.inr ⟨V2, hp2.out.leave hctx ht hfrO hparO', hgrow, hwith, hstk, hobj⟩)

end

end Vsa.Compiler
