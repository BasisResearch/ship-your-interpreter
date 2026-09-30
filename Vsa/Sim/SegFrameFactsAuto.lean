import Vsa.Sim.EqNeDispatchSeg

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic

namespace Vsa.Sim

theorem frame_ld_read (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (a : MInstr)
    (base : BitVec 64) (fb : FrameBundle m base) (hk : a.kind = .ld)
    (hsrc : srcVal a.rs1 L = base)
    (hoff : (sign_extend (m := 64) a.imm : BitVec 64).toNat + 8 ≤ 0x108)
    (hoff8 : (sign_extend (m := 64) a.imm : BitVec 64).toNat % 8 = 0) :
    MemFacts m L
      (let o := base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat
       [bytesT1 m o, bytesT1 m (o + 1), bytesT1 m (o + 2),
        bytesT1 m (o + 3), bytesT1 m (o + 4), bytesT1 m (o + 5),
        bytesT1 m (o + 6), bytesT1 m (o + 7)]) a := by
  have hea : (eaddrM a L).toNat
      = base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat :=
    frame_ea a L base _ hsrc rfl (by omega) fb
  refine memFacts_ld_frame m L a _ _ _ _ _ _ _ _ hk
    (by rw [hea]; have := fb.lo; omega) (by rw [hea]; have := fb.hi; omega)
    (by rw [hea]; have := fb.htif; right; omega)
    (by rw [hea]) (by rw [hea])
    (by rw [hea]) (by rw [hea])
    (by rw [hea]) (by rw [hea])
    (by rw [hea]) (by rw [hea])

theorem wlogM_widths : ∀ (body : List MInstr) (L : GRegs) (lds : List (List (BitVec 8)))
    (e : WEntry), e ∈ wlogM body L lds → e.2.1 = 1 ∨ e.2.1 = 2 ∨ e.2.1 = 4 ∨ e.2.1 = 8 := by
  intro body
  induction body with
  | nil => intro L lds e he; simp only [wlogM, List.not_mem_nil] at he
  | cons a rest ih =>
    intro L lds e he
    rw [wlogM] at he

    cases hk : a.kind <;> rw [hk] at he <;>
      first
        | exact ih _ _ e he
        | (rcases List.mem_cons.mp he with rfl | he
           · rw [show (wentryM a L).2.1 = widthOfM a.kind from rfl, hk]; decide
           · exact ih _ _ e he)

theorem lookupG_eraseG_ne (n rd : Nat) (h : n ≠ rd) :
    ∀ L : GRegs, lookupG n (eraseG rd L) = lookupG n L := by
  intro L
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    simp only [eraseG]
    split
    · next hkrd => rw [ih, lookupG, if_neg (by omega)]
    · next hkrd => rw [lookupG, lookupG, ih]

theorem srcVal_stepGM_ne (a : MInstr) (L : GRegs) (bs : List (BitVec 8)) (n : Nat)
    (h : n ≠ a.rd) : srcVal n (stepGM a L bs) = srcVal n L := by
  unfold stepGM
  cases n with
  | zero => split <;> rfl
  | succ m =>
    split <;>
      first
        | rfl
        | (show (lookupG (m+1) ((a.rd, wvalM a L bs) :: eraseG a.rd L)).getD 0#64
              = (lookupG (m+1) L).getD 0#64
           rw [lookupG, if_neg (by omega), lookupG_eraseG_ne (m+1) a.rd (by omega) L])

theorem srcVal_runGM_ne (n : Nat) : ∀ (body : List MInstr),
    (∀ a ∈ body, a.rd ≠ n) → ∀ (L : GRegs) (lds : List (List (BitVec 8))),
      srcVal n (runGM body L lds) = srcVal n L := by
  intro body
  induction body with
  | nil => intro _ L lds; rfl
  | cons a rest ih =>
    intro h L lds
    rw [runGM, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    exact srcVal_stepGM_ne a L (lds.headD []) n (h a (List.mem_cons_self ..)).symm

theorem wlogM_store_offsets :
    ∀ (body : List MInstr) (L : GRegs) (lds : List (List (BitVec 8)))
      (base : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) (fb : FrameBundle m base),
      srcVal 2 L = base →
      (∀ a ∈ body, a.rd ≠ 2) →
      (∀ a ∈ body, (a.kind = .sw ∨ a.kind = .sd ∨ a.kind = .sb ∨ a.kind = .sh) →
        a.rs1 = 2 ∧ (sign_extend (m := 64) a.imm : BitVec 64).toNat ≤ 0x108) →
      ∀ e ∈ wlogM body L lds,
        ∃ a, a ∈ body ∧ (a.kind = .sw ∨ a.kind = .sd ∨ a.kind = .sb ∨ a.kind = .sh) ∧
          e.1 = base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat := by
  intro body
  induction body with
  | nil => intro L lds base m fb _ _ _ e he; simp only [wlogM, List.not_mem_nil] at he
  | cons a rest ih =>
    intro L lds base m fb h2 hrd hst e he
    rw [wlogM] at he
    cases hk : a.kind <;> rw [hk] at he <;> dsimp only [] at he <;> (try rw [← hk] at he) <;>
      first
        | (rcases List.mem_cons.mp he with rfl | he
           · obtain ⟨hrs1, hoff⟩ := hst a (List.mem_cons_self ..) (by rw [hk]; decide)
             refine ⟨a, List.mem_cons_self .., by rw [hk]; decide, ?_⟩
             show (eaddrM a L).toNat = _
             rw [frame_ea a L base _ (by rw [hrs1]; exact h2) rfl hoff fb]
           · obtain ⟨a', ha', hk', he'⟩ :=
               ih L lds base m fb h2 (fun x hx => hrd x (List.mem_cons_of_mem _ hx))
                 (fun x hx => hst x (List.mem_cons_of_mem _ hx)) e he
             exact ⟨a', List.mem_cons_of_mem _ ha', hk', he'⟩)
        | (obtain ⟨a', ha', hk', he'⟩ :=
            ih (stepGM a L (lds.headD [])) (stepLdsM a.kind lds) base m fb
              (by rw [srcVal_stepGM_ne a L (lds.headD []) 2 (hrd a (List.mem_cons_self ..)).symm]
                  exact h2)
              (fun x hx => hrd x (List.mem_cons_of_mem _ hx))
              (fun x hx => hst x (List.mem_cons_of_mem _ hx)) e he
           exact ⟨a', List.mem_cons_of_mem _ ha', hk', he'⟩)

theorem wlogM_below (body : List MInstr) (L : GRegs) (lds : List (List (BitVec 8)))
    (base : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) (fb : FrameBundle m base) (off : Nat)
    (h2 : srcVal 2 L = base)
    (hrd : ∀ a ∈ body, a.rd ≠ 2)
    (hst : ∀ a ∈ body, (a.kind = .sw ∨ a.kind = .sd ∨ a.kind = .sb ∨ a.kind = .sh) →
      a.rs1 = 2 ∧ (sign_extend (m := 64) a.imm : BitVec 64).toNat ≤ 0x108)
    (hgap : ∀ a ∈ body, (a.kind = .sw ∨ a.kind = .sd ∨ a.kind = .sb ∨ a.kind = .sh) →
      off + 8 ≤ (sign_extend (m := 64) a.imm : BitVec 64).toNat) :
    ∀ e ∈ wlogM body L lds, base.toNat + off + 8 ≤ e.1 := by
  intro e he
  obtain ⟨a, ha, hk, haddr⟩ := wlogM_store_offsets body L lds base m fb h2 hrd hst e he
  rw [haddr]; have := hgap a ha hk; omega

theorem frame_ea_rw {m : Std.ExtHashMap Nat (BitVec 8)} {a : MInstr} {L : GRegs}
    {base : BitVec 64} (fb : FrameBundle m base)
    (hsrc : srcVal a.rs1 L = base := by rfl)
    (hoff : (sign_extend (m := 64) a.imm : BitVec 64).toNat ≤ 0x108 := by decide) :
    (eaddrM a L).toNat = base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat :=
  frame_ea a L base _ hsrc rfl hoff fb

theorem frame_ld_read_thru (m0 : Std.ExtHashMap Nat (BitVec 8)) (log : List WEntry)
    (L : GRegs) (a : MInstr) (base : BitVec 64) (fb : FrameBundle m0 base) (hk : a.kind = .ld)
    (hsrc : srcVal a.rs1 L = base)
    (hoff : (sign_extend (m := 64) a.imm : BitVec 64).toNat + 8 ≤ 0x108)
    (hoff8 : (sign_extend (m := 64) a.imm : BitVec 64).toNat % 8 = 0)
    (hw : ∀ e ∈ log, e.2.1 = 1 ∨ e.2.1 = 2 ∨ e.2.1 = 4 ∨ e.2.1 = 8)
    (hbelow : ∀ e ∈ log,
      base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat + 8 ≤ e.1) :
    MemFacts (writeLog m0 log) L
      (let o := base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat
       [bytesT1 m0 o, bytesT1 m0 (o + 1), bytesT1 m0 (o + 2),
        bytesT1 m0 (o + 3), bytesT1 m0 (o + 4), bytesT1 m0 (o + 5),
        bytesT1 m0 (o + 6), bytesT1 m0 (o + 7)]) a := by
  have hea : (eaddrM a L).toNat
      = base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat :=
    frame_ea a L base _ hsrc rfl (by omega) fb

  have thru : ∀ j : Nat, j < 8 →
      (writeLog m0 log)[base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat + j]?
        = m0[base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat + j]? := by
    intro j hj
    exact writeLog_getElem_disjoint _ log m0 hw
      (fun e he => Or.inl (by have := hbelow e he; omega))
  refine memFacts_ld_frame (writeLog m0 log) L a _ _ _ _ _ _ _ _ hk
    (by rw [hea]; have := fb.lo; omega) (by rw [hea]; have := fb.hi; omega)
    (by rw [hea]; have := fb.htif; right; omega)
    (by rw [hea]; exact congrArg (fun b => b.getD 0) (thru 0 (by omega)))
    (by rw [hea]; exact congrArg (fun b => b.getD 0) (thru 1 (by omega)))
    (by rw [hea]; exact congrArg (fun b => b.getD 0) (thru 2 (by omega)))
    (by rw [hea]; exact congrArg (fun b => b.getD 0) (thru 3 (by omega)))
    (by rw [hea]; exact congrArg (fun b => b.getD 0) (thru 4 (by omega)))
    (by rw [hea]; exact congrArg (fun b => b.getD 0) (thru 5 (by omega)))
    (by rw [hea]; exact congrArg (fun b => b.getD 0) (thru 6 (by omega)))
    (by rw [hea]; exact congrArg (fun b => b.getD 0) (thru 7 (by omega)))

theorem frame_sd_auto (m base_mem : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (a : MInstr)
    (base : BitVec 64) (bs : List (BitVec 8)) (fb : FrameBundle base_mem base)
    (hk : a.kind = .sd) (hsrc : srcVal a.rs1 L = base)
    (hoff : (sign_extend (m := 64) a.imm : BitVec 64).toNat + 8 ≤ 0x108)
    (hoff8 : (sign_extend (m := 64) a.imm : BitVec 64).toNat % 8 = 0) :
    MemFacts m L bs a := by
  have hea : (eaddrM a L).toNat
      = base.toNat + (sign_extend (m := 64) a.imm : BitVec 64).toNat :=
    frame_ea a L base _ hsrc rfl (by omega) fb
  refine memFacts_sd_frame m L a bs hk ?_ ?_ ?_ ?_
  · rw [hea]; have := fb.lo; omega
  · rw [hea]; have := fb.hi; omega
  · rw [hea]; have := fb.htif; omega
  · rw [hea]; have := fb.al; omega

open Lean Elab Tactic Meta

set_option maxRecDepth 100000

end Vsa.Sim
