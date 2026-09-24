import VsaIris.Interp.ITac
import VsaIris.Interp.Arm

/-!
# A helper as one symbolic run (lane H2)

A runtime helper stated with `SpecEval.helperSpec` whose body has no calls
(or tail-calls, see `helper_runK`) is one symbolic run from its entry: the
owned bytes `S` it is handed, the body's registers, the code. `helper_leaf`
reduces its spec to

* `hin`: the precondition as the owned bytes at a tracking memory, a kept
  resource `E`, and pure facts `P` the run uses;
* `hrun`: the run (`IW`, driven by `ix_run`) from the entry, ending at the
  return address with the registers outside `clob` kept and a pure end
  condition `Good`;
* `hout`: `Good` and the end bytes give the postcondition.

The data view is empty: a leaf's loads read owned bytes or the code's tables.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open Vsa.MemRepr Vsa.Sim

section Leaf

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]
variable {live : Nat → Prop}

/-- The end condition of a helper's run: back at the return address `r` with
`ra = r`, the registers outside `clob` kept, and `Good`. -/
def HelperEnd (r : BitVec 64) (rv : Nat → BitVec 64) (clob : List Nat)
    (Good : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (rv' : Nat → BitVec 64)
    (mv : Nat → BitVec 8) : Prop :=
  rv' 32 = r ∧ rv' 1 = r ∧ (∀ x ∈ fRegs, x ∉ clob → rv' x = rv x) ∧ Good rv' mv

/-- **A helper whose body is one symbolic run**, for either WP. -/
theorem helper_leaf (Wp : MachWP (GF := GF) (vsaModel live))
    {entry : BitVec 64} {clob : List Nat} {pins : (Nat → BitVec 64) → Prop} {Pre : IProp GF}
    {Post : (Nat → BitVec 64) → IProp GF} (S : Nat → Prop) (E : IProp GF)
    (P : (Nat → BitVec 64) → Mem → Prop) (Good : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)
    (hin : ∀ rv, pins rv → Pre ⊢ ∃ Mt, ownSet S (fun a => a ↦ₘ imgM Mt a) ∗ E ∗ ⌜P rv Mt⌝)
    (hrun : ∀ (rv : Nat → BitVec 64) (Mt : Mem) (r : BitVec 64), pins rv → P rv Mt →
      r.toNat % 4 = 0 → IW live ∅ [] S (HelperEnd r rv clob Good) entry (upd rv 1 r) Mt)
    (hout : ∀ rv' mv, Good rv' mv → E ∗ ownSet S (fun a => a ↦ₘ mv a) ⊢ Post rv') :
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
  iapply hout rv' mv' hgood $$ [HE HS]
  iframe HE HS

/-- **Closing a helper's run** at its return address: the end condition from
the symbolic state (every concrete end state matching it satisfies it). -/
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

/-! ## Reading stored words back -/

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

/-- A slot's bytes and their meaning are a represented value. -/
theorem valAt_of_img (N : Vsa.RuntimeRepr.NativeAddrs) {a : Nat} {v : Vsa.While.Value}
    {mv : Nat → BitVec 8} :
    valImg (GF := GF) N mv a v ∗ ownSet (InExt (a, 24)) (fun b => b ↦ₘ mv b) ⊢ valAt N a v := by
  unfold valAt
  iintro ⟨Hv, HS⟩
  iexists mv
  iframe Hv HS

omit I in
/-- A value slot at any contents, at a tracking memory. -/
theorem slot24_tracked (a : Nat) :
    slot24 (GF := GF) a ⊢ ∃ Mt : Mem, ownSet (InExt (a, 24)) (fun b => b ↦ₘ imgM Mt b) := by
  unfold slot24 blockOwn
  iintro H
  ihave ⟨%f, H⟩ := ownSet_fn _ $$ H
  iapply ownSet_mem _ f $$ H

/-- A represented value at a tracking memory holding its bytes. -/
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

end Vals

end VsaIris.Interp
