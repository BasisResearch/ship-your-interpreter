import Vsa.CT.TProg
import Vsa.Sim.RunT
import Vsa.Sim.StepCount

namespace Vsa.Compiler

open Vsa.While Vsa.CT Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config Step Steps StepsN Halted Halts RunT pcOfC output)

def LibOK (L : Nat → BitVec 64 → BitVec 64 → BitVec 64 → List (BitVec 64)) : Prop :=
  ∀ (t : Nat) (x y r res : BitVec 64) (A : AM) (c : Config), libRes t x y = some res →
    r.toNat % 4 = 0 → Corr c A → A.pc = BitVec.ofNat 64 t → lookupG 1 A.regs = some r →
    lookupG 10 A.regs = some x → lookupG 11 A.regs = some y → 12 ∈ keysG A.regs →
    13 ∈ keysG A.regs → LibLoaded A.mem →
    ∃ c', RunT c (L t x y r) c' ∧ Corr c' ⟨r, (10, res) :: eraseAll clobbered A.regs, A.mem, A.out⟩

def sailObs (L : Nat → BitVec 64 → BitVec 64 → BitVec 64 → List (BitVec 64)) (o : Obs) :
    List (BitVec 64) :=
  match o.lib with
  | some (t, x, y) => o.pc :: L t x y (BitVec.addInt o.pc 4)
  | none => [o.pc]

def sailTr (L : Nat → BitVec 64 → BitVec 64 → BitVec 64 → List (BitVec 64)) (τ : List Obs) :
    List (BitVec 64) := τ.flatMap (sailObs L)

theorem step1_runT {c : Config} {A A' : AM} (hc : Corr c A) (h : Step1Corr c A') :
    ∃ c', RunT c [A.pc] c' ∧ Corr c' A' := by
  obtain ⟨c', hs, he, hc'⟩ := h
  have hn := Vsa.Machine.Steps.toN_of_stepsEq hs he
  cases hn with
  | succ s h0 =>
    cases h0
    exact ⟨_, RunT.single s hc.pc, hc'⟩

theorem obsOf_nonlib {code : List Ins} {A : AM}
    (hnl : ∀ off, fetch code A.pc = some (.jal 1 off) →
      ¬ ((A.pc + sign_extend (m := 64) (evenJ off)).toNat = mulPC ∨
        (A.pc + sign_extend (m := 64) (evenJ off)).toNat = divPC ∨
        (A.pc + sign_extend (m := 64) (evenJ off)).toNat = modPC)) :
    (obsOf code A).lib = none ∧ (obsOf code A).pc = A.pc := by
  unfold obsOf
  split
  · rename_i i hf
    cases i with
    | jal rd off =>
      simp only [insObs]
      split
      · rename_i h
        obtain ⟨rfl, hl⟩ := h
        exact absurd hl (hnl off hf)
      · exact ⟨rfl, rfl⟩
    | ld => exact ⟨rfl, rfl⟩
    | sd => exact ⟨rfl, rfl⟩
    | _ => exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem sim_libcallT {L : Nat → BitVec 64 → BitVec 64 → BitVec 64 → List (BitVec 64)} (hL : LibOK L)
    (off : BitVec 21) {A A' : AM} {c : Config} (hc : Corr c A)
    (hb : ∀ j < 4, A.mem[A.pc.toNat + j]? = some (byte (Ins.jal 1 off).encode j))
    (hlo : 0x80000000 ≤ A.pc.toNat) (hhi : A.pc.toNat + 4 ≤ tohostAddr)
    (hal : A.pc.toNat % 4 = 0)
    (htgt : (A.pc + sign_extend (m := 64) (evenJ off)).toNat % 4 = 0)
    (hlib : LibLoaded A.mem)
    (h : libCall (A.pc + sign_extend (m := 64) (evenJ off)).toNat A = some (.run A')) :
    ∃ c', RunT c (A.pc :: L (A.pc + sign_extend (m := 64) (evenJ off)).toNat (srcVal 10 A.regs)
      (srcVal 11 A.regs) (BitVec.addInt A.pc 4)) c' ∧ Corr c' A' := by
  obtain ⟨c1, r1, hc1⟩ := step1_runT hc (sim_jal_link off hc hb hlo hhi hal htgt)
  have hret : (BitVec.addInt A.pc 4).toNat % 4 = 0 := by
    rw [addInt4_toNat _ (by simp only [tohostAddr] at hhi; omega)]; omega
  have hr : lookupG 1 ((1, BitVec.addInt A.pc 4) :: eraseG 1 A.regs) = some (BitVec.addInt A.pc 4) := by
    simp [lookupG]
  have hlk : ∀ n, n ≠ 1 → lookupG n ((1, BitVec.addInt A.pc 4) :: eraseG 1 A.regs) = lookupG n A.regs := by
    intro n hn
    simp only [lookupG, if_neg (Ne.symm hn)]
    exact lookupG_eraseG_ne hn A.regs
  have hkey : ∀ n, n ≠ 1 → n ∈ keysG A.regs → n ∈ keysG ((1, BitVec.addInt A.pc 4) :: eraseG 1 A.regs) :=
    fun n hn hk => List.mem_cons_of_mem _ (mem_keysG_eraseG hn _ hk)
  have hsub : ∀ res : BitVec 64, ∀ p ∈ (10, res) :: eraseAll clobbered A.regs,
      p ∈ (10, res) :: eraseAll clobbered ((1, BitVec.addInt A.pc 4) :: eraseG 1 A.regs) := by
    intro res p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact List.mem_cons_self ..
    · obtain ⟨hpL, hpS⟩ := mem_eraseAll hp
      refine List.mem_cons_of_mem _ (mem_eraseAll_of (List.mem_cons_of_mem _ (mem_eraseG_of hpL ?_)) hpS)
      intro h1; exact hpS (by rw [h1]; simp [clobbered])
  have hlib1 : LibLoaded (AM.mk (A.pc + sign_extend (m := 64) (evenJ off))
      ((1, BitVec.addInt A.pc 4) :: eraseG 1 A.regs) A.mem A.out).mem := hlib
  have hpcT : (A.pc + sign_extend (m := 64) (evenJ off)) =
      BitVec.ofNat 64 (A.pc + sign_extend (m := 64) (evenJ off)).toNat := by
    apply BitVec.eq_of_toNat_eq; simp
  unfold libCall at h
  split at h
  · rename_i x y hx hy
    split at h
    · rename_i hk
      have h12 := hkey 12 (by decide) hk.1
      have h13 := hkey 13 (by decide) hk.2
      have hx' := (hlk 10 (by decide)).trans hx
      have hy' := (hlk 11 (by decide)).trans hy
      have hsx : srcVal 10 A.regs = x := (show Has A.regs 10 x from ⟨by decide, .inr ⟨by decide, hx⟩⟩).src.2
      have hsy : srcVal 11 A.regs = y := (show Has A.regs 11 y from ⟨by decide, .inr ⟨by decide, hy⟩⟩).src.2
      rw [hsx, hsy]
      have go : ∀ res, libRes (A.pc + sign_extend (m := 64) (evenJ off)).toNat x y = some res →
          A' = ⟨BitVec.addInt A.pc 4, (10, res) :: eraseAll clobbered A.regs, A.mem, A.out⟩ →
          ∃ c', RunT c (A.pc :: L (A.pc + sign_extend (m := 64) (evenJ off)).toNat x y
            (BitVec.addInt A.pc 4)) c' ∧ Corr c' A' := by
        intro res hres hA'
        obtain ⟨c', r2, hc'⟩ := hL _ x y _ res _ c1 hres hret hc1 hpcT hr hx' hy' h12 h13 hlib1
        exact ⟨c', by simpa using r1.trans r2, hA' ▸ hc'.sub (hsub res)⟩
      split at h
      · rename_i hm; cases h
        exact go _ (by simp [libRes, hm]) rfl
      · split at h
        · rename_i hd; cases h
          exact go _ (by simp [libRes, hd, show divPC ≠ mulPC by decide]) rfl
        · split at h
          · rename_i hd; cases h
            exact go _ (by simp [libRes, hd, show modPC ≠ mulPC by decide,
              show modPC ≠ divPC by decide]) rfl
          · cases h
    · cases h
  · cases h

theorem step_simT {L : Nat → BitVec 64 → BitVec 64 → BitVec 64 → List (BitVec 64)} (hL : LibOK L)
    {code : List Ins} {A A' : AM} {c : Config} (hc : Corr c A)
    (hcode : CodeAt A.mem code) (hlib : LibLoaded A.mem)
    (h : astep code A = some (.run A')) :
    ∃ c', RunT c (sailObs L (obsOf code A)) c' ∧ Corr c' A' := by
  by_cases hnl : ∀ off, fetch code A.pc = some (.jal 1 off) →
      ¬ ((A.pc + sign_extend (m := 64) (evenJ off)).toNat = mulPC ∨
        (A.pc + sign_extend (m := 64) (evenJ off)).toNat = divPC ∨
        (A.pc + sign_extend (m := 64) (evenJ off)).toNat = modPC)
  · obtain ⟨hl, hp⟩ := obsOf_nonlib hnl
    obtain ⟨c', r, hc'⟩ := step1_runT hc (step_sim1 hc hcode hnl h)
    refine ⟨c', ?_, hc'⟩
    simp only [sailObs, hl, hp]; exact r
  · obtain ⟨off, hf, hlt⟩ : ∃ off, fetch code A.pc = some (.jal 1 off) ∧
        ((A.pc + sign_extend (m := 64) (evenJ off)).toNat = mulPC ∨
          (A.pc + sign_extend (m := 64) (evenJ off)).toNat = divPC ∨
          (A.pc + sign_extend (m := 64) (evenJ off)).toNat = modPC) :=
      Classical.byContradiction fun hno => hnl fun off hf hlt => hno ⟨off, hf, hlt⟩
    obtain ⟨hcb, hal, hhi, _⟩ := fetch_spec hf
    have hb := fetch_bytes hcode hf
    have hlo : 0x80000000 ≤ A.pc.toNat := by simp only [codeBase] at hcb; omega
    unfold astep at h
    rw [hf] at h
    simp only [exec] at h
    split at h
    · rename_i htgt
      simp only [show (1 : Nat) ≠ 0 by decide, if_false, if_true] at h
      try rw [if_pos hlt] at h
      have hobs : obsOf code A = ⟨A.pc, none, some ((A.pc + sign_extend (m := 64) (evenJ off)).toNat,
          srcVal 10 A.regs, srcVal 11 A.regs)⟩ := by
        unfold obsOf; rw [hf]; simp only [insObs]; rw [if_pos ⟨by trivial, hlt⟩]
      rw [hobs]
      exact sim_libcallT hL off hc hb hlo hhi hal htgt hlib h
    · cases h

theorem run_simT {L : Nat → BitVec 64 → BitVec 64 → BitVec 64 → List (BitVec 64)} (hL : LibOK L)
    {code : List Ins} (hfit : Fits code) : ∀ {τ : List Obs} {A B : AM}, StarT code τ A B →
    ∀ {c : Config}, Corr c A → CodeAt A.mem code → LibLoaded A.mem →
    ∃ c', RunT c (sailTr L τ) c' ∧ Corr c' B ∧ CodeAt B.mem code ∧ LibLoaded B.mem
  | _, _, _, .refl _, c, hc, hcode, hlib => ⟨c, .refl c, hc, hcode, hlib⟩
  | _, _, _, .step hs rest, c, hc, hcode, hlib => by
    obtain ⟨c1, r1, hc1⟩ := step_simT hL hc hcode hlib hs
    have hag := astep_mem_low hs
    obtain ⟨c2, r2, hc2, hcode2, hlib2⟩ := run_simT hL hfit rest hc1 (CodeAt.of_low hfit hag hcode)
      (LibLoaded.of_low hag hlib)
    exact ⟨c2, by simpa [sailTr] using r1.trans r2, hc2, hcode2, hlib2⟩

theorem halts_of_abstractT {L : Nat → BitVec 64 → BitVec 64 → BitVec 64 → List (BitVec 64)} (hL : LibOK L)
    {code : List Ins} (hfit : Fits code) {A B : AM} {c : Config} {τ : List Obs} {e : Nat}
    (hc : Corr c A) (hcode : CodeAt A.mem code) (hlib : LibLoaded A.mem) (r : StarT code τ A B)
    (hh : astep code B = some (.halt e)) :
    ∃ c' σf, RunT c (sailTr L τ) c' ∧ Halted c' e σf ∧ output σf = String.join B.out.toList := by
  obtain ⟨c', hs, hc', hcode', -⟩ := run_simT hL hfit r hc hcode hlib
  obtain ⟨σf, hH, ho⟩ := halt_sim hc' hcode' hh
  exact ⟨c', σf, hs, hH, ho⟩

end Vsa.Compiler

