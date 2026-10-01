import Vsa.Compiler.Wf
import Vsa.Compiler.SimVar

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

def maxFS : Nat := 2048

structure View where
  F : FrMap
  H : CloMap
  hF : Nat
  h : Nat

def View.fa (V : View) (a : Addr) : Nat := parOf V.F (some a)

structure ObjImg (T : List String) (m : Mem) (h : Nat) : Prop where
  fixed : FixedOK m
  fixedHi : fixedAddr 7 + 40 ≤ h
  strs : ∀ s ∈ T, StrBelow m h (strAddr T s) s.toList
  ptr : ObjPtr h

def fnCode (T : List String) (Γ : List (List String)) (params : List String) (body : List Stmt)
    (q : Nat) : List Ins :=
  let L := frameNames params body
  let fs := frameSize body
  let fp := fnPre L params fs q
  let pb := q + fp.length
  let lb := (gseq T (fnCtx (L :: Γ) 0) pb body).length
  fp ++ gseq T (fnCtx (L :: Γ) (pb + lb + 2)) pb body ++ fnPost fs

def WfFn (T : List String) (Γ : List (List String)) (params : List String) (body : List Stmt) : Prop :=
  params.length ≤ 120 ∧ (frameNames params body).length ≤ 120 ∧ tSeq body ≤ 120 ∧ WfSeq T (frameNames params body :: Γ) body

def CloCode (code : List Ins) (T : List String) (V : View) (s : Store) (m : Mem) : Prop :=
  ∀ (a : Nat) (cd : ClosureData) (p : Nat), s.closures[a]? = some cd → V.H[a]? = some p →
    ∃ q Γc, rdW m p = BitVec.ofNat 64 (V.fa cd.env) ∧ rdW m (p + 8) = pcOf q ∧
      ChainL V.F s cd.env Γc ∧ Seg code q (fnCode T Γc cd.params cd.body q) ∧
      PosOK (q + (fnCode T Γc cd.params cd.body q).length) ∧ WfFn T Γc cd.params cd.body

structure StackOK (d sp fs : Nat) : Prop where
  depth : d ≤ maxCallDepth
  room : stackLo + (maxCallDepth - d) * maxFS ≤ sp
  top : sp + fs ≤ stackHi
  al : sp % 16 = 0
  fsz : fs ≤ 1936

structure MS (code : List Ins) (T : List String) (V : View) (st : St) (d : Nat) (env : Addr)
    (Γ : List (List String)) (sp fs : Nat) (A : AM) : Prop where
  rel : StoreRel V.F V.H st.store A.mem V.hF V.h
  img : ObjImg T A.mem V.h
  clo : CloCode code T V st.store A.mem
  chn : ChainL V.F st.store env Γ
  out : String.join A.out.toList = st.out
  ho : Has A.regs hpO (BitVec.ofNat 64 V.h)
  hf : Has A.regs hpF (BitVec.ofNat 64 V.hF)
  henv : Has A.regs envR (BitVec.ofNat 64 (V.fa env))
  hsp : Has A.regs spR (BitVec.ofNat 64 sp)
  hdep : Has A.regs depR (BitVec.ofNat 64 d)
  stk : StackOK d sp fs
  hfal : V.hF % 8 = 0

def Room (V : View) (n : Nat) : Prop := V.hF + 64 * n ≤ frameEnd ∧ V.h + 64 * n ≤ objEnd

structure VGrow (V : View) (s : Store) (V' : View) (s' : Store) : Prop where
  grows : Grows V.F s V'.F s'
  hpre : V.H <+: V'.H
  hle : V.hF ≤ V'.hF
  le : V.h ≤ V'.h

def Within (V V' : View) (n : Nat) : Prop := V'.hF ≤ V.hF + 64 * n ∧ V'.h ≤ V.h + 64 * n

def anc (s : Store) (a : Addr) : Nat → Addr
  | 0 => a
  | i + 1 => match s.frames[a]? with
    | some fr => match fr.parent with
      | some b => anc s b i
      | none => a
    | none => a

structure StackKeep (m m' : Mem) (sp fs k : Nat) : Prop where
  low : Agree m m' sp (sp + 16 + 16 * k)
  high : Agree m m' (sp + fs) stackHi

structure EPost (code : List Ins) (T : List String) (V : View) (st : St) (d : Nat) (env : Addr)
    (Γ : List (List String)) (sp fs k : Nat) (A : AM) (n : Nat) (st' : St) (v : Value) (V' : View)
    (B : AM) : Prop where
  ms : MS code T V' st' d env Γ sp fs B
  val : InA V'.H B.mem V'.h B.regs v
  grow : VGrow V st.store V' st'.store
  within : Within V V' n
  stack : StackKeep A.mem B.mem sp fs k
  obj : ObjAgree A.mem B.mem V.h

def keyRegs : List Nat := [hpO, hpF, envR, spR, depR]

def Scratch (S : List Nat) : Prop := ∀ r ∈ keyRegs, r ∉ S

instance (S : List Nat) : Decidable (Scratch S) := by unfold Scratch; infer_instance

theorem ObjImg.transport {T : List String} {m m' : Mem} {h h' : Nat} (hi : ObjImg T m h)
    (hag : ObjAgree m m' h) (hh : h ≤ h') (hp : ObjPtr h') : ObjImg T m' h' where
  fixed := hi.fixed.mono hag hi.fixedHi
  fixedHi := by have := hi.fixedHi; omega
  strs s hs := (hi.strs s hs).mono hag hh
  ptr := hp

theorem CloCode.transport {code : List Ins} {T : List String} {V : View} {s : Store} {m m' : Mem}
    (hc : CloCode code T V s m) (hok : CloOK V.H s m V.h) (hag : ObjAgree m m' V.h) :
    CloCode code T V s m' := by
  intro a cd p ha hp
  obtain ⟨q, Γc, h1, h2, h3, h4, h5, h6⟩ := hc a cd p ha hp
  obtain ⟨dd, cc, ho⟩ := hok.obj a cd p ha hp
  have := ho.lo; have := ho.hi; have := ho.al
  refine ⟨q, Γc, ?_, ?_, h3, h4, h5, h6⟩
  · rw [hag p ho.al ho.lo (by omega)]; exact h1
  · rw [hag (p + 8) (by omega) (by omega) (by omega)]; exact h2

theorem MS.transport {code : List Ins} {T : List String} {V : View} {st : St} {d : Nat} {env : Addr}
    {Γ : List (List String)} {sp fs : Nat} {A B : AM} (hm : MS code T V st d env Γ sp fs A)
    {S : List Nat} (hS : Scratch S) (hk : Keep S A.regs B.regs) (hag : Agree A.mem B.mem frameBase V.hF)
    (hobj : ObjAgree A.mem B.mem V.h) (ho : B.out = A.out) : MS code T V st d env Γ sp fs B where
  rel := hm.rel.transport hag hobj (Nat.le_refl _)
  img := hm.img.transport hobj (Nat.le_refl _) hm.img.ptr
  clo := hm.clo.transport hm.rel.clo hobj
  chn := hm.chn
  out := by rw [ho]; exact hm.out
  ho := hk.has (hS hpO (by decide)) hm.ho
  hf := hk.has (hS hpF (by decide)) hm.hf
  henv := hk.has (hS envR (by decide)) hm.henv
  hsp := hk.has (hS spR (by decide)) hm.hsp
  hdep := hk.has (hS depR (by decide)) hm.hdep
  stk := hm.stk
  hfal := hm.hfal

theorem VGrow.refl (V : View) (s : Store) : VGrow V s V s :=
  ⟨Grows.refl _ _, List.prefix_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem Within.refl (V : View) (n : Nat) : Within V V n := ⟨by omega, by omega⟩

theorem StackKeep.refl (m : Mem) (sp fs k : Nat) : StackKeep m m sp fs k := ⟨Agree.refl _ _ _, Agree.refl _ _ _⟩

theorem ObjAgree.refl (m : Mem) (h : Nat) : ObjAgree m m h := fun _ _ _ _ => rfl

theorem epost_regs {code : List Ins} {T : List String} {V : View} {st : St} {d : Nat} {env : Addr}
    {Γ : List (List String)} {sp fs k : Nat} {A B : AM} {n : Nat} {v : Value}
    (hm : MS code T V st d env Γ sp fs A) {S : List Nat} (hS : Scratch S) (hk : Keep S A.regs B.regs)
    (hmem : B.mem = A.mem) (ho : B.out = A.out) (hv : InA V.H A.mem V.h B.regs v) :
    EPost code T V st d env Γ sp fs k A n st v V B where
  ms := hm.transport hS hk (by rw [hmem]; exact Agree.refl _ _ _) (by rw [hmem]; exact ObjAgree.refl _ _) ho
  val := by rw [hmem]; exact hv
  grow := VGrow.refl _ _
  within := Within.refl _ _
  stack := by rw [hmem]; exact StackKeep.refl _ _ _ _
  obj := by rw [hmem]; exact ObjAgree.refl _ _

end Vsa.Compiler
