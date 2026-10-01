import Vsa.Compiler.SimCallNat
import Vsa.Compiler.R6Reg

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

def defFrame (x : String) (v : Value) (f : Frame) : Frame :=
  { f with vars := (if f.vars.any (·.1 == x) then f.vars.map (rebind x v) else f.vars ++ [(x, v)]) }

theorem define_eq (s : Store) (c : Addr) (x : String) (v : Value) :
    s.define c x v = { s with frames := s.frames.modify c (defFrame x v) } := rfl

theorem OutFrames.trans {m1 m2 m3 : Mem} {hF : Nat} (h1 : OutFrames m1 m2 hF) (h2 : OutFrames m2 m3 hF) :
    OutFrames m1 m3 hF := fun b hb ho => (h2 b hb ho).trans (h1 b hb ho)

theorem SameShape.trans {s1 s2 s3 : Store} (h1 : SameShape s1 s2) (h2 : SameShape s2 s3) : SameShape s1 s3 := by
  refine ⟨h2.1.trans h1.1, fun b fr h => ?_⟩
  obtain ⟨fr1, h1', e1⟩ := h1.2 b fr h
  obtain ⟨fr2, h2', e2⟩ := h2.2 b fr1 h1'
  exact ⟨fr2, h2', e2.trans e1⟩

theorem SameShape.refl (s : Store) : SameShape s s := ⟨rfl, fun _ fr h => ⟨fr, h, rfl⟩⟩

theorem define_shape (s : Store) (c : Addr) (x : String) (v : Value) : SameShape s (s.define c x v) := by
  refine ⟨by simp [Store.define], fun b fr h => ?_⟩
  rw [define_eq]
  simp only [Array.getElem?_modify]
  split
  · next e => subst e; rw [h]; exact ⟨_, rfl, rfl⟩
  · exact ⟨fr, h, rfl⟩

theorem define_frame {s : Store} {c : Addr} {fr : Frame} (h : s.frames[c]? = some fr) (x : String) (v : Value) :
    (s.define c x v).frames[c]? = some (defFrame x v fr) := by
  rw [define_eq]; simp only [Array.getElem?_modify, if_pos rfl, h]; rfl

structure ParamPost (F : FrMap) (H : CloMap) (s : Store) (m : Mem) (hF h : Nat) (s' : Store) (m' : Mem) :
    Prop where
  rel : StoreRel F H s' m' hF h
  shape : SameShape s s'
  clo : s'.closures = s.closures
  out : OutFrames m m' hF

section
variable {code : List Ins} (hR : RTLoaded code)
include hR

theorem run_params {F : FrMap} {H : CloMap} {hF h : Nat} {c : Addr} {fa : Nat} {Lay : List String}
    {argp : Nat} (hFc : F[c]? = some (fa, Lay)) (hal : argp % 8 = 0) (hlo : stackLo ≤ argp) :
    ∀ (ps : List String) (vs : List Value) (j : Nat) (s : Store) (m : Mem) (L : GRegs) (o : Array String)
      (q : Nat), ps.length = vs.length → j + ps.length ≤ 32 → argp + 16 * (j + ps.length) ≤ stackHi →
      Seg code q (paramCopies Lay j ps) → Has L a3 (BitVec.ofNat 64 argp) → Has L a4 (BitVec.ofNat 64 fa) →
      StoreRel F H s m hF h → (∃ fr, s.frames[c]? = some fr) → (∀ x ∈ ps, x ∈ Lay) →
      (∀ i (hi : i < vs.length), VRepr H m h (vs[i]'hi) (rdW m (argp + 16 * (j + i)))
        (rdW m (argp + 16 * (j + i) + 8))) →
      Reaches code ⟨pcOf q, L, m, o⟩ (fun B => B.pc = pcOf (q + 8 * ps.length) ∧ B.out = o ∧
        Keep [t4, t5, t6] L B.regs ∧
        ParamPost F H s m hF h ((ps.zip vs).foldl (fun s p => s.define c p.1 p.2) s) B.mem)
  | [], vs, j, s, m, L, o, q, hl, _, _, _, _, _, hs, _, _, _ => by
    cases vs with
    | cons _ _ => simp at hl
    | nil =>
      exact reach_here ⟨by simp, rfl, Keep.refl _ _, hs, SameShape.refl _, rfl, OutFrames.refl _ _⟩
  | x :: xs, vs, j, s, m, L, o, q, hl, hj, htop, hseg, h13, h14, hs, ⟨fr, hfr⟩, hx, hv => by
    cases vs with
    | nil => simp at hl
    | cons v vs =>
    simp only [List.length_cons] at hl hj htop
    obtain ⟨hb, he, ht⟩ := frame_consts
    have hL : stackLo = 0xE0000000 := rfl
    have hH : stackHi = 0x100000000 := rfl
    obtain ⟨i, hsl⟩ : ∃ i, slotOf Lay x = some i := by
      cases h' : slotOf Lay x with
      | none => exact absurd (hx x (by simp)) (slotOf_none h')
      | some i => exact ⟨i, rfl⟩
    have hi := slotOf_lt hsl
    obtain ⟨hf1, hf2, hf3, hf4⟩ := hs.region c fa Lay hFc
    have htop' := hs.top
    unfold frSize at hf2
    simp only [paramCopies, paramCopy, seg_app_iff, List.length_cons, List.length_nil] at hseg
    obtain ⟨s1, s2⟩ := hseg
    have hv0 := hv 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at hv0
    have n1 : (BitVec.ofNat 64 (argp + 16 * j)).toNat = argp + 16 * j := toNat_ofNat_lt (by omega)
    have n2 : (BitVec.ofNat 64 (argp + 16 * j + 8)).toNat = argp + 16 * j + 8 := toNat_ofNat_lt (by omega)
    have n3 : (BitVec.ofNat 64 (fa + (8 + 16 * i))).toNat = fa + (8 + 16 * i) := toNat_ofNat_lt (by omega)
    have n4 : (BitVec.ofNat 64 (fa + (8 + 16 * i) + 8)).toNat = fa + (8 + 16 * i) + 8 :=
      toNat_ofNat_lt (by omega)
    have t1 : fa + (8 + 16 * i) ≠ tohostAddr := by omega
    have t2 : fa + (8 + 16 * i) + 8 ≠ tohostAddr := by omega
    have o1 : StOK (fa + (8 + 16 * i)) := by unfold StOK; omega
    have o2 : StOK (fa + (8 + 16 * i) + 8) := by unfold StOK; omega
    have l1 : LdOK (argp + 16 * j) := by unfold LdOK; omega
    have l2 : LdOK (argp + 16 * j + 8) := by unfold LdOK; omega
    apply run_whole hR.fits s1
    wp_simp [hsl, Option.getD_some, h13.wp, h14.wp, n1, n2, n3, n4, t1, t2, o1, o2, l1, l2]
    have r2 : rdW (applyW m (fa + (8 + 16 * i), 8, rdW m (argp + 16 * j))) (argp + 16 * j + 8) =
        rdW m (argp + 16 * j + 8) := by rw [rdW_upd (by omega) (by omega), if_neg (by omega)]
    have ea : fa + (8 + 16 * i) = fa + 8 + 16 * i := by omega
    rw [r2, ea]
    have hs1 := hs.write_slot hfr hFc hsl hv0 (defFrame x v) binds_define
    rw [← define_eq] at hs1
    have hout1 : OutFrames m (applyW (applyW m (fa + 8 + 16 * i, 8, rdW m (argp + 16 * j)))
        (fa + 8 + 16 * i + 8, 8, rdW m (argp + 16 * j + 8))) hF := fun b hb hb' => by
      rw [rdW_two (by omega) hb, if_neg (by omega), if_neg (by omega)]
    have hobj1 := hout1.obj (h := h) htop'
    refine reaches_mono (run_params hFc hal hlo xs vs (j + 1) _ _ _ o (q + 8) (by omega) (by omega) (by omega) s2
      (by reg_simp []; exact h13) (by reg_simp []; exact h14) hs1
      ⟨_, define_frame hfr x v⟩
      (fun y hy => hx y (by simp [hy])) (fun i' hi' => ?_)) ?_
    · have := hv (i' + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [hout1 _ (by omega) (.inr (by omega)), hout1 _ (by omega) (.inr (by omega))]
      rw [show j + 1 + i' = j + (i' + 1) by omega]
      exact this.mono hobj1 (Nat.le_refl _)
    · rintro B ⟨hpc, ho, hk, pp⟩
      refine ⟨by rw [hpc]; congr 1 <;> omega, ho, ?_, ?_⟩
      · exact Keep.trans (by reg_simp []; exact Keep.refl _ _) hk
      · simp only [List.zip_cons_cons, List.foldl_cons]
        exact ⟨pp.rel, (define_shape s c x v).trans pp.shape, pp.clo, hout1.trans pp.out⟩

end

end Vsa.Compiler
