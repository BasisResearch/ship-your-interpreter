import Vsa.Compiler.SimLogic
import Vsa.Compiler.R6Reg

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

theorem OutFrames.obj {m m' : Mem} {hF h : Nat} (ho : OutFrames m m' hF) (hF' : hF ≤ frameEnd) :
    ObjAgree m m' h := by
  have he : frameEnd = objBase := rfl
  exact fun a ha h1 _ => ho a ha (.inr (by omega))

theorem OutFrames.stack {m m' : Mem} {hF : Nat} (ho : OutFrames m m' hF) (hF' : hF ≤ frameEnd) {sp fs k : Nat}
    (hsp : stackLo ≤ sp) : StackKeep m m' sp fs k := by
  have he : frameEnd = 0x90000000 := rfl
  have hl : stackLo = 0xE0000000 := rfl
  exact ⟨fun a h1 _ h3 => ho a h3 (.inr (by omega)), fun a h1 _ h3 => ho a h3 (.inr (by omega))⟩

theorem CloCode.shape {code : List Ins} {T : List String} {V : View} {s s' : Store} {m m' : Mem}
    (hc : CloCode code T V s m) (hok : CloOK V.H s m V.h) (hag : ObjAgree m m' V.h)
    (hsh : SameShape s s') (hcl : s'.closures = s.closures) : CloCode code T V s' m' := by
  intro a cd p ha hp
  rw [hcl] at ha
  obtain ⟨q, Γc, h1, h2, h3, h4, h5, h6⟩ := hc.transport hok hag a cd p ha hp
  exact ⟨q, Γc, h1, h2, h3.transport hsh, h4, h5, h6⟩

theorem VGrow.shape {V : View} {s s' : Store} (hsh : SameShape s s') : VGrow V s V s' :=
  ⟨Grows.of_shape hsh, List.prefix_refl _, Nat.le_refl _, Nat.le_refl _⟩

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem sAssign {st : St} {d : Nat} {env : Addr} {x : String} {e : Expr} {st' : St} {v : Value}
    {store'' : Store} {n : Nat} (hE : ESpec code T st d env e st' v n) (hset : st'.store.set? env x v = some store'') :
    ESpec code T st d env (.assign x e) ⟨store'', st'.out⟩ v n := by
  intro V Γ sp fs k pos A hm hA hwf hseg hP htmp
  simp only [tE] at htmp
  have hwl : (walkCode (fun l p => writeHere x l p (pos + (gexpr T Γ k pos e).length + 1 +
      walkLen (hereLen 8 x) Γ)) (pos + (gexpr T Γ k pos e).length + 1) Γ).length = walkLen (hereLen 8 x) Γ :=
    walkCode_length x _ 8 writeHere (fun l p => writeHere_length x l p _) Γ _
  have h := And.intro hseg hP
  simp only [gexpr, setCode, ↓segP_app, List.length_cons, List.length_nil, Nat.zero_add] at h
  obtain ⟨⟨s1, p1⟩, ⟨s2, -⟩, s3, p3⟩ := h
  simp only [gexpr, setCode, List.length_append, List.length_singleton, hwl] at p3 ⊢
  refine hE.bind hm hA hwf s1 p1 htmp
    (fun B h1 h2 => .inl ⟨h1, h2⟩) fun V1 B hpc hp => ?_
  obtain ⟨t, p, h10, h11, hv⟩ := hp.val
  obtain ⟨pc1, L1, m1, o1⟩ := B
  simp only at hpc h10 h11 hv; subst hpc
  have hms := hp.ms
  obtain ⟨f, hFa⟩ := hms.chn.head'
  obtain ⟨fr, hfr⟩ := hms.chn.frame
  have hlt : env < st'.store.frames.size := (Array.getElem?_eq_some_iff.mp hfr).1
  apply run_whole hR.fits s2
  wp_simp [hms.henv.wp, View.fa_eq hFa]
  refine reaches_mono (walk_write hR.fits hms.rel x _ p3 hv hms.chn
    _ f _ o1 hFa s3 (by reg_simp []) (by reg_simp []; exact h10) (by reg_simp []; exact h11)) ?_
  rintro ⟨pc2, L2, m2, o2⟩ ⟨ho2, hk2, hB⟩
  simp only at ho2 hk2 hB; subst ho2
  have hset' := hset
  unfold Store.set? at hset'
  rw [set_gas hms.rel.parents x v env _ hlt, ] at hset'
  rw [hset'] at hB
  obtain ⟨hpc2, sp'⟩ := hB
  have hk : Keep (t0 :: writeClob) L1 L2 :=
    (Keep.gset (Keep.refl _ L1) (by decide)).trans (hk2.mono (by decide))
  have hobj := sp'.out.obj (h := V1.h) hms.rel.top
  refine .inr ⟨?_, V1, ?_⟩
  · show pc2 = _; rw [hpc2]; congr 1 <;> omega
  exact {
    ms := {
      rel := sp'.rel
      img := hms.img.transport hobj (Nat.le_refl _) hms.img.ptr
      clo := hms.clo.shape hms.rel.clo hobj sp'.shape sp'.clo
      chn := hms.chn.transport sp'.shape
      out := hms.out
      ho := hk.has (by decide) hms.ho
      hf := hk.has (by decide) hms.hf
      henv := hk.has (by decide) hms.henv
      hsp := hk.has (by decide) hms.hsp
      hdep := hk.has (by decide) hms.hdep
      stk := hms.stk
      hfal := hms.hfal }
    val := ⟨t, p, hk.has (by decide) h10, hk.has (by decide) h11, hv.mono hobj (Nat.le_refl _)⟩
    grow := hp.grow.trans (VGrow.shape sp'.shape)
    within := hp.within
    stack := hp.stack.trans (sp'.out.stack hms.rel.top hms.stk.bounds.1)
    obj := hp.obj.trans hobj hp.grow.le }

end

end Vsa.Compiler
