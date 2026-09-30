import VsaIris.Interp.ITac
import VsaIris.Interp.Arm

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open Vsa.MemRepr Vsa.Sim

section Leaf

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]
variable {live : Nat → Prop}

def HelperEnd (r : BitVec 64) (rv : Nat → BitVec 64) (clob : List Nat)
    (Good : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (rv' : Nat → BitVec 64)
    (mv : Nat → BitVec 8) : Prop :=
  rv' 32 = r ∧ rv' 1 = r ∧ (∀ x ∈ fRegs, x ∉ clob → rv' x = rv x) ∧ Good rv' mv

theorem helper_leaf (Wp : MachWP (GF := GF) (vsaModel live))
    {entry : BitVec 64} {clob : List Nat} {pins : (Nat → BitVec 64) → Prop} {Pre : IProp GF}
    {Post : (Nat → BitVec 64) → IProp GF} (S : Nat → Prop) (E : Mem → IProp GF)
    (P : (Nat → BitVec 64) → Mem → Prop)
    (Good : Mem → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (hin : ∀ rv, pins rv → Pre ⊢ ∃ Mt, ownSet S (fun a => a ↦ₘ imgM Mt a) ∗ E Mt ∗ ⌜P rv Mt⌝)
    (hrun : ∀ (rv : Nat → BitVec 64) (Mt : Mem) (r : BitVec 64), pins rv → P rv Mt →
      r.toNat % 4 = 0 → IW live ∅ [] S (HelperEnd r rv clob (Good Mt)) entry (upd rv 1 r) Mt)
    (hout : ∀ Mt rv' mv, Good Mt rv' mv → E Mt ∗ ownSet S (fun a => a ↦ₘ mv a) ⊢ Post rv') :
    ⊢ helperSpec (vsaModel live) Wp entry clob pins Pre Post := by
  unfold helperSpec fnSpecW
  iintro %rv !> %r %Φ Hpc Hra ⟨%hal, Hregs, %hp, #Hcode, HPre⟩ Hk
  ihave ⟨%Mt, HS, HE, %hP⟩ := hin rv hp $$ HPre
  obtain ⟨n, hn⟩ := hrun rv Mt r hp hP hal
  let rv0 : Nat → BitVec 64 := fun x => if x = 32 then entry else upd rv 1 r x
  have hrun0 := hn rv0 (imgM Mt) ⟨by simp [rv0, VsaIris.PC],
    fun x _ hne => by simp only [rv0, show x ≠ 32 from by simpa [VsaIris.PC] using hne, ite_false],
    fun _ _ => rfl⟩
  iapply wp_localRunW Wp n rv0 (imgM Mt) hrun0
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  rw [hro]
  iframe Hcode HS
  isplitl [Hpc Hra Hregs]
  · iapply (sepL_iRegs rv0).2
    have e1 : rv0 32 = entry := by simp [rv0]
    have e2 : rv0 1 = r := by simp [rv0]
    have e3 : regFile (GF := GF) rv0 = regFile rv := by
      unfold regFile
      exact sepL_congr fun x hx => by
        have h32 : x ≠ 32 := fun e => by subst e; revert hx; decide
        have h1 : x ≠ 1 := fun e => by subst e; revert hx; decide
        simp only [rv0, h32, ite_false, upd_other _ _ h1]
    rw [e1, e2, e3]
    iframe Hpc Hra Hregs
  iintro %rv' %mv' %⟨h32, h1, hkeep, hgood⟩ Hrs HS
  ihave ⟨Hpc, Hra, Hregs⟩ := (sepL_iRegs rv').1 $$ Hrs
  rw [h32, h1]
  iapply Hk $$ Hpc Hra
  iexists rv'
  iframe Hregs
  isplitr
  · ipureintro; exact hkeep
  iapply hout Mt rv' mv' hgood $$ [$]

theorem swp_helperEnd {S : Nat → Prop} {r : BitVec 64} {rv R : Nat → BitVec 64} {Mt : Mem}
    {clob : List Nat} {Good : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (h1 : R 1 = r) (hkeep : ∀ x ∈ fRegs, x ∉ clob → R x = rv x)
    (hgood : ∀ rv' mv, (∀ x ∈ fRegs, rv' x = R x) → (∀ a, S a → mv a = imgM Mt a) → Good rv' mv) :
    IW live ∅ [] S (HelperEnd r rv clob Good) r R Mt := by
  refine swp_done fun rv' mv hm => ⟨hm.pc, ?_, fun x hx hc => ?_, hgood rv' mv (fun x hx => ?_) hm.img⟩
  · rw [hm.regs 1 (by decide) (by decide), h1]
  · rw [hm.regs x (by rw [iRegs_eq]; exact .tail _ (.tail _ hx))
      (fun e => by subst e; revert hx; decide), hkeep x hx hc]
  · exact hm.regs x (by rw [iRegs_eq]; exact .tail _ (.tail _ hx))
      (fun e => by subst e; revert hx; decide)

end Leaf

macro "helper_keep" : tactic =>
  `(tactic| (intro x hx hc
             have h1 : x ≠ 1 := fun e => by subst e; revert hx; decide
             simp only [List.mem_cons, List.not_mem_nil, _root_.or_false, not_or] at hc
             simp only [upd]
             simp_all))

theorem imgLE_store4_hit (Mt : Mem) (a : Nat) (v : BitVec 64) :
    imgLE (imgM (writeLog Mt [(a, 4, v)])) a 4 = v.toNat % 2 ^ 32 := by
  refine readLE_memImg (m := writeLog Mt [(a, 4, v)]) ?_
  show read32 (Vsa.Sim.writeMap4 Mt a (Vsa.Sim.swData v)) a = _
  rw [Vsa.Sim.read32_writeMap4, Vsa.Sim.swData_toNat]

theorem imgLE_store_miss (Mt : Mem) {a b w n : Nat} (v : BitVec 64) (h : a + n ≤ b ∨ b + w ≤ a) :
    imgLE (imgM (writeLog Mt [(b, w, v)])) a n = imgLE (imgM Mt) a n :=
  imgLE_congr fun i hi => imgM_store_miss _ _ (by omega)

theorem imgLE_agree {f g : Nat → BitVec 8} {a n : Nat} (h : ∀ i, i < n → f (a + i) = g (a + i)) :
    imgLE f a n = imgLE g a n := imgLE_congr h

section Vals

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

theorem valAt_of_img (N : Vsa.RuntimeRepr.NativeAddrs) {a : Nat} {v : Vsa.While.Value}
    {mv : Nat → BitVec 8} :
    valImg (GF := GF) N mv a v ∗ ownSet (InExt (a, 24)) (fun b => b ↦ₘ mv b) ⊢ valAt N a v := by
  unfold valAt
  iintro ⟨Hv, HS⟩
  iexists mv
  iframe Hv HS

omit I in

theorem slot24_tracked (a : Nat) :
    slot24 (GF := GF) a ⊢ ∃ Mt : Mem, ownSet (InExt (a, 24)) (fun b => b ↦ₘ imgM Mt b) := by
  unfold slot24 blockOwn
  iintro H
  ihave ⟨%f, H⟩ := ownSet_fn _ $$ H
  iapply ownSet_mem _ f $$ H

theorem valAt_tracked (N : Vsa.RuntimeRepr.NativeAddrs) (a : Nat) (v : Vsa.While.Value) :
    valAt (GF := GF) N a v ⊢ ∃ Mt : Mem, ownSet (InExt (a, 24)) (fun b => b ↦ₘ imgM Mt b) ∗
      valImg N (imgM Mt) a v := by
  unfold valAt
  iintro ⟨%img, H, #Hv⟩
  obtain ⟨Mt, hMt⟩ := exists_mem_img img (List.range' a 24)
  have hag : ∀ b, InExt (a, 24) b → imgM Mt b = img b := fun b hb =>
    hMt b (List.mem_range'.2 ⟨b - a, by simp [InExt] at hb; omega, by simp [InExt] at hb; omega⟩)
  iexists Mt
  isplitl [H]
  · iapply ownSet_congr (fun b hb => by rw [hag b hb]) $$ H
  have e : ∀ k, k < 24 → imgM Mt (a + k) = img (a + k) := fun k hk =>
    hag (a + k) (by simp [InExt]; omega)
  have e0 : imgW (imgM Mt) a = imgW img a := by
    unfold imgW; rw [imgLE_congr (fun i hi => e i (by omega))]
  have e8 : imgW (imgM Mt) (a + 8) = imgW img (a + 8) := by
    have h : imgLE (imgM Mt) (a + 8) 8 = imgLE img (a + 8) 8 :=
      imgLE_congr (fun i hi => by have := e (8 + i) (by omega); rwa [← Nat.add_assoc] at this)
    unfold imgW; rw [h]
  have e16 : imgW (imgM Mt) (a + 16) = imgW img (a + 16) := by
    have h : imgLE (imgM Mt) (a + 16) 8 = imgLE img (a + 16) 8 :=
      imgLE_congr (fun i hi => by have := e (16 + i) (by omega); rwa [← Nat.add_assoc] at this)
    unfold imgW; rw [h]
  unfold valImg; rw [e0, e8, e16]
  iexact Hv

omit I in

theorem ownSet_trackedAt (S : Nat → Prop) (f : Nat → BitVec 8) :
    ownSet (GF := GF) S (fun a => a ↦ₘ f a) ⊢
      ∃ M : Mem, ownSet S (fun a => a ↦ₘ imgM M a) ∗ ⌜∀ a, S a → imgM M a = f a⌝ := by
  unfold ownSet
  iintro ⟨%l, %⟨hnd, hmem⟩, Hl⟩
  obtain ⟨M, hM⟩ := exists_mem_img f l
  iexists M
  isplitl
  · iexists l
    isplitr
    · ipureintro; exact ⟨hnd, hmem⟩
    rw [sepL_congr (Ψ := fun a => iprop(a ↦ₘ imgM M a)) (fun a ha => by rw [hM a ha])] at *
    iexact Hl
  · ipureintro; exact fun a ha => hM a ((hmem a).2 ha)

omit I in

theorem ownSet_join_tracked (S T : Nat → Prop) (Ms Mt : Mem) :
    ownSet (GF := GF) S (fun a => a ↦ₘ imgM Ms a) ∗ ownSet T (fun a => a ↦ₘ imgM Mt a) ⊢
      ∃ M : Mem, ownSet (fun a => S a ∨ T a) (fun a => a ↦ₘ imgM M a) ∗
        ⌜(∀ a, S a → imgM M a = imgM Ms a) ∧ (∀ a, T a → imgM M a = imgM Mt a) ∧
          ∀ a, S a → ¬ T a⌝ := by
  classical
  iintro ⟨HS, HT⟩
  ihave %hd := ownSet_disj S T _ _ $$ [$]
  let f : Nat → BitVec 8 := fun a => if S a then imgM Ms a else imgM Mt a
  ihave HS := ownSet_congr (Ψ := fun a => iprop(a ↦ₘ f a)) (fun a ha => by simp [f, ha]) $$ HS
  ihave HT := ownSet_congr (Ψ := fun a => iprop(a ↦ₘ f a))
    (fun a ha => by simp [f, show ¬ S a from fun h => hd a h ha]) $$ HT
  ihave H := ownSet_join S T _ hd $$ [$]
  ihave ⟨%M, H, %hM⟩ := ownSet_trackedAt _ f $$ H
  iexists M
  iframe H
  ipureintro
  refine ⟨fun a ha => ?_, fun a ha => ?_, hd⟩
  · rw [hM a (.inl ha)]; simp [f, ha]
  · rw [hM a (.inr ha)]; simp [f, show ¬ S a from fun h => hd a h ha]

omit I in

theorem ownSet_split_tracked (S T : Nat → Prop) (M : Mem) (hd : ∀ a, S a → ¬ T a) :
    ownSet (GF := GF) (fun a => S a ∨ T a) (fun a => a ↦ₘ imgM M a) ⊢
      ownSet S (fun a => a ↦ₘ imgM M a) ∗ ownSet T (fun a => a ↦ₘ imgM M a) := by
  iintro H
  ihave ⟨H1, H2⟩ := ownSet_split _ S _ $$ H
  isplitl [H1]
  · iapply ownSet_iff _ (fun a => ⟨fun h => h.2, fun h => ⟨.inl h, h⟩⟩) $$ H1
  · iapply ownSet_iff _ (fun a => ⟨fun h => h.1.resolve_left h.2, fun h => ⟨.inr h, fun h' => hd a h' h⟩⟩) $$ H2

def ValPure (N : Vsa.RuntimeRepr.NativeAddrs) : Vsa.While.Value → BitVec 64 → BitVec 64 → BitVec 64 → Prop
  | .null, w0, _, _ => w0.toNat % 2 ^ 32 = 0
  | .bool b, w0, w1, _ => w0.toNat % 2 ^ 32 = 1 ∧ w1.toNat % 2 ^ 32 = cond b 1 0
  | .int n, w0, w1, _ => w0.toNat % 2 ^ 32 = 2 ∧ w1.toInt = n
  | .str _, w0, w1, _ => w0.toNat % 2 ^ 32 = 3 ∧ w1.toNat ≠ 0
  | .closure _, w0, w1, _ => w0.toNat % 2 ^ 32 = 4 ∧ w1.toNat ≠ 0
  | .native f, w0, _, w2 => w0.toNat % 2 ^ 32 = 5 ∧ w2.toNat = N.addr f

theorem valOf_pure (N : Vsa.RuntimeRepr.NativeAddrs) (v : Vsa.While.Value) (w0 w1 w2 : BitVec 64) :
    valOf (GF := GF) N v w0 w1 w2 ⊢ ⌜ValPure N v w0 w1 w2⌝ := by
  cases v <;> unfold valOf ValPure
  · iintro %h; ipureintro; exact h
  · iintro %h; ipureintro; exact h
  · iintro %h; ipureintro; exact h
  · iintro ⟨%h, -⟩; ipureintro; exact h
  · iintro ⟨%h, -⟩; ipureintro; exact h
  · iintro ⟨%h, -⟩; ipureintro; exact h

theorem ValPure.kind {N : Vsa.RuntimeRepr.NativeAddrs} {v : Vsa.While.Value} {w0 w1 w2 : BitVec 64}
    (h : ValPure N v w0 w1 w2) : w0.toNat % 2 ^ 32 = Vsa.RuntimeRepr.kindTag v := by
  cases v <;> simp only [ValPure] at h <;> first | exact h | exact h.1

theorem ldv_lw_kind {Mt : Mem} {a k : Nat} (h : (imgW (imgM Mt) a).toNat % 2 ^ 32 = k)
    (hk : k < 2 ^ 31) : ldv .lw Mt a = BitVec.ofNat 64 k :=
  ldvf_lw_imgLE (by rw [← imgW_lo32]; exact h) hk

theorem ldv_ld_imgW (Mt : Mem) (a : Nat) : ldv .ld Mt a = imgW (imgM Mt) a := by
  refine BitVec.eq_of_toNat_eq ?_
  rw [show ldv .ld Mt a = ldvf .ld (imgM Mt) a from rfl, ldvf_ld_imgLE rfl, imgW_toNat]
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have := imgLE_lt (imgM Mt) a 8; omega)

theorem valImg_str {N : Vsa.RuntimeRepr.NativeAddrs} {f : Nat → BitVec 8} {a : Nat} {x : String} :
    valImg (GF := GF) N f a (.str x) ⊢ strAt (imgW f (a + 8)).toNat x := by
  unfold valImg valOf
  iintro ⟨-, #H⟩
  iexact H

theorem valImg_words {N : Vsa.RuntimeRepr.NativeAddrs} {f g : Nat → BitVec 8} {a b : Nat}
    {v : Vsa.While.Value} (h0 : imgW f a = imgW g b) (h8 : imgW f (a + 8) = imgW g (b + 8))
    (h16 : imgW f (a + 16) = imgW g (b + 16)) : valImg (GF := GF) N f a v = valImg N g b v := by
  unfold valImg; rw [h0, h8, h16]

theorem valImg_agreeOn {N : Vsa.RuntimeRepr.NativeAddrs} {f g : Nat → BitVec 8} {a : Nat}
    {v : Vsa.While.Value} (h : ∀ k, InExt (a, 24) k → f k = g k) :
    valImg (GF := GF) N f a v = valImg N g a v := by
  have e : ∀ o, o ≤ 16 → imgW f (a + o) = imgW g (a + o) := fun o ho => by
    unfold imgW
    rw [imgLE_congr (n := 8) (img' := g) (fun i hi => h _ (by simp [InExt]; omega))]
  exact valImg_words (by simpa using e 0 (by omega)) (e 8 (by omega)) (e 16 (by omega))

end Vals

end VsaIris.Interp
