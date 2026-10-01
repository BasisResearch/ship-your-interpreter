import Vsa.Compiler.SimOp
import Vsa.Compiler.R6Reg

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

def tmpW (m : Mem) (sp k : Nat) (t p : BitVec 64) : Mem :=
  applyW (applyW m (sp + 16 + 16 * k, 8, t)) (sp + 16 + 16 * k + 8, 8, p)

theorem StackOK.bounds {d sp fs : Nat} (h : StackOK d sp fs) : stackLo ≤ sp ∧ sp + fs ≤ stackHi ∧ sp % 16 = 0 :=
  ⟨by have := h.room; omega, h.top, h.al⟩

theorem rdW_tmpW {m : Mem} {sp k : Nat} {t p : BitVec 64} (hal : sp % 16 = 0) {a : Nat} (ha : a % 8 = 0) :
    rdW (tmpW m sp k t p) a =
      if a = sp + 16 + 16 * k + 8 then p else if a = sp + 16 + 16 * k then t else rdW m a := by
  unfold tmpW; rw [rdW_upd (by omega) ha, rdW_upd (by omega) ha]

theorem tmpW_outside {m : Mem} {sp k : Nat} {t p : BitVec 64} (hal : sp % 16 = 0) {lo hi : Nat}
    (h : hi ≤ sp + 16 + 16 * k ∨ sp + 16 + 16 * k + 16 ≤ lo) : Agree m (tmpW m sp k t p) lo hi :=
  fun a h1 h2 h3 => by rw [rdW_tmpW hal h3, if_neg (by omega), if_neg (by omega)]

theorem StackKeep.stored {m : Mem} {sp fs k j : Nat} {t p : BitVec 64} (hal : sp % 16 = 0) (hj : k ≤ j)
    (hfs : 16 + 16 * (j + 1) ≤ fs) : StackKeep m (tmpW m sp j t p) sp fs k :=
  ⟨tmpW_outside hal (.inl (by omega)), tmpW_outside hal (.inr (by omega))⟩

theorem InTmp.stored {H : CloMap} {m : Mem} {h sp k : Nat} {v : Value} {t p : BitVec 64}
    (hv : VRepr H m h v t p) (hal : sp % 16 = 0) (hag : ObjAgree m (tmpW m sp k t p) h) :
    InTmp H (tmpW m sp k t p) h sp k v := by
  unfold InTmp
  rw [rdW_tmpW hal (by omega), if_neg (by omega), if_pos rfl, rdW_tmpW hal (by omega), if_pos rfl]
  exact hv.mono hag (Nat.le_refl _)

theorem MS.stored {code : List Ins} {T : List String} {V : View} {st : St} {d : Nat} {env : Addr}
    {Γ : List (List String)} {sp fs : Nat} {A : AM} (hm : MS code T V st d env Γ sp fs A) {j : Nat}
    (hj : 16 + 16 * (j + 1) ≤ fs) {t p : BitVec 64} {pc : BitVec 64} {L : GRegs} {S : List Nat}
    (hS : Scratch S) (hk : Keep S A.regs L) :
    MS code T V st d env Γ sp fs ⟨pc, L, tmpW A.mem sp j t p, A.out⟩ ∧
      ObjAgree A.mem (tmpW A.mem sp j t p) V.h := by
  have hb := hm.stk.bounds
  have hl : stackLo = 0xE0000000 := rfl
  have he : frameEnd = 0x90000000 := rfl
  have hoe : objEnd = 0xE0000000 := rfl
  have := hm.rel.top; have := hm.img.ptr.hi
  have hobj : ObjAgree A.mem (tmpW A.mem sp j t p) V.h := fun a ha h1 h2 => by
    rw [rdW_tmpW hb.2.2 ha, if_neg (by omega), if_neg (by omega)]
  exact ⟨hm.transport (B := ⟨pc, L, tmpW A.mem sp j t p, A.out⟩) hS hk
    (tmpW_outside hb.2.2 (.inl (by omega))) hobj rfl, hobj⟩

structure HeapStep (m m' : Mem) (h h' : Nat) : Prop where
  grow : h ≤ h'
  ptr : ObjPtr h'
  frame : ∀ a, a % 8 = 0 → (a + 8 ≤ h ∨ h' ≤ a) → (a + 8 ≤ bufBase ∨ bufBase + 160 ≤ a) →
    rdW m' a = rdW m a

theorem HeapStep.obj {m m' : Mem} {h h' : Nat} (hs : HeapStep m m' h h') : ObjAgree m m' h := by
  have hb : bufBase = 0x80080000 := rfl
  have hob : objBase = 0x90000000 := rfl
  exact fun a ha h1 h2 => hs.frame a ha (.inl h2) (.inr (by omega))

theorem HeapStep.low {m m' : Mem} {h h' : Nat} (hs : HeapStep m m' h h') (hh : objBase ≤ h) {hi : Nat}
    (hhi : hi ≤ objBase) : Agree m m' frameBase hi := by
  have hb : bufBase = 0x80080000 := rfl
  have hf : frameBase = 0x80100000 := rfl
  exact fun a h1 h2 h3 => hs.frame a h3 (.inl (by omega)) (.inr (by omega))

theorem HeapStep.stack {m m' : Mem} {h h' : Nat} (hs : HeapStep m m' h h') {lo hi : Nat}
    (hlo : objEnd ≤ lo) : Agree m m' lo hi := by
  have hb : bufBase = 0x80080000 := rfl
  have hoe : objEnd = 0xE0000000 := rfl
  have := hs.ptr.hi
  exact fun a h1 h2 h3 => hs.frame a h3 (.inr (by omega)) (.inr (by omega))

def View.withH (V : View) (h' : Nat) : View := { V with h := h' }

theorem MS.heap {code : List Ins} {T : List String} {V : View} {st : St} {d : Nat} {env : Addr}
    {Γ : List (List String)} {sp fs : Nat} {A : AM} (hm : MS code T V st d env Γ sp fs A) {h' : Nat}
    {m' : Mem} (hs : HeapStep A.mem m' V.h h') {pc : BitVec 64} {L : GRegs} {S : List Nat}
    (hS : ∀ r ∈ keyRegs, r ≠ hpO → r ∉ S) (hk : Keep S A.regs L) (h8 : Has L hpO (BitVec.ofNat 64 h')) :
    MS code T (V.withH h') st d env Γ sp fs ⟨pc, L, m', A.out⟩ where
  rel := hm.rel.transport (hs.low hm.img.ptr.lo (Nat.le_trans hm.rel.top (by decide))) hs.obj hs.grow
  img := hm.img.transport hs.obj hs.grow hs.ptr
  clo := hm.clo.transport hm.rel.clo hs.obj
  chn := hm.chn
  out := hm.out
  ho := h8
  hf := hk.has (hS hpF (by decide) (by decide)) hm.hf
  henv := hk.has (hS envR (by decide) (by decide)) hm.henv
  hsp := hk.has (hS spR (by decide) (by decide)) hm.hsp
  hdep := hk.has (hS depR (by decide) (by decide)) hm.hdep
  stk := hm.stk
  hfal := hm.hfal

section
variable {code : List Ins} (hfit : Fits code)
include hfit

theorem run_storeTmp {q k sp d fs : Nat} (hseg : Seg code q (storeTmp k)) {L : GRegs} {m : Mem}
    {o : Array String} {t p : BitVec 64} (hsp : Has L spR (BitVec.ofNat 64 sp)) (hst : StackOK d sp fs)
    (hk : 16 + 16 * (k + 1) ≤ fs) (h10 : Has L a0 t) (h11 : Has L a1 p) {Q : AM → Prop}
    (hQ : ∀ L', Keep [t6] L L' → Reaches code ⟨pcOf (q + 4), L', tmpW m sp k t p, o⟩ Q) :
    Reaches code ⟨pcOf q, L, m, o⟩ Q := by
  have hb := hst.bounds
  have hfs := hst.fsz
  have hl : stackLo = 0xE0000000 := rfl
  have hh : stackHi = 0x100000000 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hM : maxFS = 2048 := rfl
  have hn1 : (BitVec.ofNat 64 (sp + (16 + 16 * k))).toNat = sp + (16 + 16 * k) := toNat_ofNat_lt (by omega)
  have hn2 : (BitVec.ofNat 64 (sp + (16 + 16 * k) + 8)).toNat = sp + (16 + 16 * k) + 8 :=
    toNat_ofNat_lt (by omega)
  apply run_whole hfit hseg
  wp_simp [storeTmp, hsp.wp, h10.wp, h11.wp, hn1, hn2]
  rw [if_neg (by omega), if_neg (by omega)]
  refine ⟨by unfold StOK; omega, by unfold StOK; omega, ?_⟩
  have e1 : sp + (16 + 16 * k) = sp + 16 + 16 * k := by omega
  simp only [e1]
  exact hQ _ (by reg_simp []; exact Keep.refl _ _)

theorem run_loadTmp {q k sp d fs : Nat} (hseg : Seg code q (loadTmp k)) {L : GRegs} {m : Mem}
    {o : Array String} (hsp : Has L spR (BitVec.ofNat 64 sp)) (hst : StackOK d sp fs)
    (hk : 16 + 16 * (k + 1) ≤ fs) {Q : AM → Prop}
    (hQ : ∀ L', Keep [t6, a0, a1] L L' → Has L' a0 (rdW m (sp + 16 + 16 * k)) →
      Has L' a1 (rdW m (sp + 16 + 16 * k + 8)) → Reaches code ⟨pcOf (q + 4), L', m, o⟩ Q) :
    Reaches code ⟨pcOf q, L, m, o⟩ Q := by
  have hb := hst.bounds
  have hfs := hst.fsz
  have hl : stackLo = 0xE0000000 := rfl
  have hh : stackHi = 0x100000000 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hM : maxFS = 2048 := rfl
  have hn1 : (BitVec.ofNat 64 (sp + (16 + 16 * k))).toNat = sp + (16 + 16 * k) := toNat_ofNat_lt (by omega)
  have hn2 : (BitVec.ofNat 64 (sp + (16 + 16 * k) + 8)).toNat = sp + (16 + 16 * k) + 8 :=
    toNat_ofNat_lt (by omega)
  apply run_whole hfit hseg
  wp_simp [loadTmp, hsp.wp, hn1, hn2]
  refine ⟨by unfold LdOK; omega, by unfold LdOK; omega, ?_⟩
  have e1 : sp + (16 + 16 * k) = sp + 16 + 16 * k := by omega
  simp only [e1]
  exact hQ _ (by reg_simp []; exact Keep.refl _ _) (by reg_simp []) (by reg_simp [])

end

end Vsa.Compiler
