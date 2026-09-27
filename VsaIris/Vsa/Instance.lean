import VsaIris.Adequacy
import VsaIris.MachWP
import Vsa.Sim.SegToTripleFramed
import Vsa.Sim.StepCount
import Vsa.Sim.WriteLogNF

namespace VsaIris.Inst

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable
open Vsa.Machine (Config Step Steps StepsN Halted MState output)
open Vsa.Sim

def vsaStep (c : Config) : StepResult Config :=
  match (Vsa.stepOnce c.tick c.steps).run c.σ with
  | .ok (.inr (i', u')) σ' => .next ⟨σ', i', u'⟩
  | .ok (.inl (some e, _)) σ' => .halt e (output σ')
  | _ => .stuck

def pcVal (σ : MState) : BitVec 64 :=
  ((σ.regs.get? Register.PC : Option (BitVec 64))).getD 0

def vsaReg (c : Config) (k : Nat) : BitVec 64 :=
  if k = VsaIris.PC then pcVal c.σ else (gprGet c.σ k).getD 0

structure VsaOk (live : Nat → Prop) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  gpr : ∀ n, 1 ≤ n → n ≤ 31 → (gprGet c.σ n).isSome
  live : ∀ a, live a → (c.σ.mem[a]?).isSome
  htifIdle : c.σ.regs.get? Register.htif_payload_writes = some (0#4)

def vsaModel (live : Nat → Prop) : MachineModel where
  State := Config
  step := vsaStep
  reg := vsaReg
  mem c a := (c.σ.mem[a]?).getD 0
  out c := output c.σ
  ok := VsaOk live

theorem vsaStep_next {c c' : Config} (h : vsaStep c = .next c') : Step c c' := by
  obtain ⟨σ, i, u⟩ := c
  unfold vsaStep at h
  split at h
  · next i' u' σ' e => cases h; exact .mk e
  · cases h
  · cases h

theorem vsaStep_of_step {c c' : Config} (h : Step c c') : vsaStep c = .next c' := by
  cases h with
  | mk e => simp only [vsaStep, e]

theorem vsaStep_halt {c : Config} {e : Nat} {out : String} (h : vsaStep c = .halt e out) :
    ∃ σf, Halted c e σf ∧ output σf = out := by
  obtain ⟨σ, i, u⟩ := c
  unfold vsaStep at h
  split at h
  · cases h
  · next e' n σ' he => cases h; exact ⟨σ', .mk he, rfl⟩
  · cases h

theorem reachesN_of_stepsN {live : Nat → Prop} {n : Nat} {c c' : Config}
    (h : StepsN n c c') : ReachesN (vsaModel live) n c c' := by
  induction h with
  | zero c => exact ReachesN.zero (M := vsaModel live) c
  | succ s _ ih => exact ReachesN.succ (M := vsaModel live) (vsaStep_of_step s) ih

theorem steps_of_reaches {live : Nat → Prop} {c c' : (vsaModel live).State}
    (h : Reaches (vsaModel live) c c') : Steps c c' := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .head (vsaStep_next s) ih

theorem stepsN_of_reachesN {live : Nat → Prop} {n : Nat} {c c' : (vsaModel live).State}
    (h : ReachesN (vsaModel live) n c c') : StepsN n c c' := by
  induction h with
  | zero c => exact .zero c
  | succ s _ ih => exact .succ (vsaStep_next s) ih

theorem vsa_adequacyP {GF : BundledGFunctors} [MachGpreS GF] (live : Nat → Prop) (c : Config)
    (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8))
    (hr : RegAgree (vsaModel live) mr c) (hm : MemAgree (vsaModel live) mm c)
    (hok : VsaOk live c) (φ : Nat × String → Prop)
    (H : AdequacyHypP GF (vsaModel live) mr mm (output c.σ) φ) :
    Vsa.Machine.Diverges c ∨ ∃ out e, Vsa.Machine.Halts c out e ∧ φ (e, out) := by
  rcases mach_adequacyP (GF := GF) (M := vsaModel live) c mr mm hr hm hok φ H with
    hd | ⟨e, out, ⟨cf, hre, hh⟩, hφ⟩
  · exact .inl fun n => (hd n).imp fun _ h => stepsN_of_reachesN h
  · obtain ⟨σf, hhalt, hout⟩ := vsaStep_halt hh
    exact .inr ⟨out, e, ⟨cf, σf, steps_of_reaches hre, hhalt, hout⟩, hφ⟩

theorem vsa_adequacyP_nonzero {GF : BundledGFunctors} [MachGpreS GF] (live : Nat → Prop)
    (c : Config) (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8))
    (hr : RegAgree (vsaModel live) mr c) (hm : MemAgree (vsaModel live) mm c)
    (hok : VsaOk live c) (H : AdequacyHypP GF (vsaModel live) mr mm (output c.σ) (fun v => v.1 ≠ 0)) :
    Vsa.Machine.Diverges c ∨ ∃ out e, Vsa.Machine.Halts c out e ∧ e ≠ 0 :=
  vsa_adequacyP live c mr mm hr hm hok _ H

theorem mem_keysG_eraseG {n r : Nat} (hne : n ≠ r) :
    ∀ {L : GRegs}, n ∈ keysG L → n ∈ keysG (eraseG r L)
  | [], h => h
  | (m, v) :: L, h => by
    simp only [keysG, List.mem_cons] at h
    simp only [eraseG]
    split
    · next hm =>
      rcases h with rfl | h
      · exact absurd hm hne
      · exact mem_keysG_eraseG hne h
    · simp only [keysG, List.mem_cons]
      rcases h with rfl | h
      · exact .inl rfl
      · exact .inr (mem_keysG_eraseG hne h)

theorem mem_keysG_stepGM {n : Nat} (a : MInstr) (L : GRegs) (bs : List (BitVec 8))
    (h : n ∈ keysG L) : n ∈ keysG (stepGM a L bs) := by
  unfold stepGM
  split
  · exact h
  · exact h
  · exact h
  · exact h
  · simp only [keysG, List.mem_cons]
    by_cases hn : n = a.rd
    · exact .inl hn
    · exact .inr (mem_keysG_eraseG hn h)

theorem mem_keysG_runGM {n : Nat} :
    ∀ (is : List MInstr) (L : GRegs) (lds : List (List (BitVec 8))),
      n ∈ keysG L → n ∈ keysG (runGM is L lds)
  | [], _, _, h => h
  | a :: r, L, _, h => mem_keysG_runGM r _ _ (mem_keysG_stepGM a L _ h)

theorem mem_keysG_runChain {n : Nat} :
    ∀ (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8))),
      n ∈ keysG L → n ∈ keysG (runChain bs L lds)
  | [], _, _, h => h
  | b :: bs, L, lds, h => mem_keysG_runChain bs _ _ (mem_keysG_runGM b.body L lds h)

theorem lookupG_of_mem {n : Nat} : ∀ {L : GRegs}, n ∈ keysG L → ∃ v, lookupG n L = some v
  | [], h => nomatch h
  | (m, v) :: L, h => by
    simp only [lookupG]
    split
    · exact ⟨v, rfl⟩
    · next hm =>
      simp only [keysG, List.mem_cons] at h
      rcases h with rfl | h
      · exact absurd rfl hm
      · exact lookupG_of_mem h

theorem mem_keysG_of_mem {p : Nat × BitVec 64} : ∀ {L : GRegs}, p ∈ L → p.1 ∈ keysG L
  | q :: L, h => by
    simp only [keysG, List.mem_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact .inl rfl
    · exact .inr (mem_keysG_of_mem h)

theorem exists_of_mem_keysG {k : Nat} : ∀ {L : GRegs}, k ∈ keysG L → ∃ v, (k, v) ∈ L
  | (m, v) :: L, h => by
    simp only [keysG, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨v, List.mem_cons_self⟩
    · obtain ⟨w, hw⟩ := exists_of_mem_keysG h
      exact ⟨w, .tail _ hw⟩

theorem gholds_of_forall {σ : MState} :
    ∀ (L : GRegs), (∀ p ∈ L, gprGet σ p.1 = some p.2) → GHolds σ L
  | [], _ => trivial
  | p :: L, h => ⟨h p List.mem_cons_self, gholds_of_forall L fun q hq => h q (.tail _ hq)⟩

theorem gprGet_none {σ : MState} {k : Nat} (h : k = 0 ∨ 32 ≤ k) : gprGet σ k = none := by
  rcases h with rfl | h
  · rfl
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 32 := ⟨k - 32, by omega⟩
    rfl

private theorem gpr_avoids_noise : ∀ n, n < 32 → 1 ≤ n →
    ∀ R ∈ noiseRegs, (R == gprReg n) = false := by decide

theorem vsaReg_gpr {c : Config} {n : Nat} (h : n ≠ VsaIris.PC) :
    vsaReg c n = (gprGet c.σ n).getD 0 := ite_eq_right h

theorem gprGet_eq_of_vsaReg {live : Nat → Prop} {c : Config} (hok : VsaOk live c) {n : Nat}
    {v : BitVec 64} (h1 : 1 ≤ n) (h31 : n ≤ 31) (h : vsaReg c n = v) : gprGet c.σ n = some v := by
  rw [vsaReg_gpr (by unfold VsaIris.PC; omega)] at h
  have hs := hok.gpr n h1 h31
  cases hg : gprGet c.σ n with
  | none => rw [hg] at hs; cases hs
  | some w => rw [hg] at h; exact congrArg some h

def Pointwise (f : Std.ExtHashMap Nat (BitVec 8) → Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ a : Nat, (∀ m, (f m)[a]? = m[a]?) ∨ ∃ v, ∀ m, (f m)[a]? = some v

theorem pointwise_id : Pointwise id := fun _ => .inl fun _ => rfl

theorem pointwise_insert (k : Nat) (v : BitVec 8) : Pointwise (fun m => m.insert k v) := by
  intro a
  by_cases h : k = a
  · exact .inr ⟨v, fun m => by rw [Std.ExtHashMap.getElem?_insert, ite_eq_left (by simp [h])]⟩
  · exact .inl fun m => by rw [Std.ExtHashMap.getElem?_insert, ite_eq_right (by simp [h])]

theorem pointwise_comp {f g : Std.ExtHashMap Nat (BitVec 8) → Std.ExtHashMap Nat (BitVec 8)}
    (hf : Pointwise f) (hg : Pointwise g) : Pointwise (fun m => g (f m)) := by
  intro a
  rcases hg a with hg | ⟨v, hg⟩
  · rcases hf a with hf | ⟨w, hf⟩
    · exact .inl fun m => (hg _).trans (hf m)
    · exact .inr ⟨w, fun m => (hg _).trans (hf m)⟩
  · exact .inr ⟨v, fun m => hg _⟩

theorem pointwise_applyW (e : WEntry) : Pointwise (fun m => applyW m e) := by
  obtain ⟨A, w, d⟩ := e
  by_cases h1 : w = 1
  · subst h1; exact pointwise_insert _ _
  by_cases h2 : w = 2
  · subst h2; exact pointwise_comp (pointwise_insert _ _) (pointwise_insert _ _)
  by_cases h4 : w = 4
  · subst h4
    exact pointwise_comp (pointwise_comp (pointwise_comp (pointwise_insert _ _)
      (pointwise_insert _ _)) (pointwise_insert _ _)) (pointwise_insert _ _)
  by_cases h8 : w = 8
  · subst h8
    exact pointwise_comp (pointwise_comp (pointwise_comp (pointwise_comp (pointwise_comp
      (pointwise_comp (pointwise_comp (pointwise_insert _ _) (pointwise_insert _ _))
      (pointwise_insert _ _)) (pointwise_insert _ _)) (pointwise_insert _ _))
      (pointwise_insert _ _)) (pointwise_insert _ _)) (pointwise_insert _ _)
  have : (fun m => applyW m (A, w, d)) = id :=
    funext fun m => applyW_eq_of_ne m A w d h1 h2 h4 h8
  rw [this]; exact pointwise_id

theorem pointwise_writeLog : ∀ log : List WEntry, Pointwise (fun m => writeLog m log)
  | [] => pointwise_id
  | e :: log => pointwise_comp (pointwise_applyW e) (pointwise_writeLog log)

theorem writeLog_present (m : Std.ExtHashMap Nat (BitVec 8)) (log : List WEntry) (a : Nat)
    (h : (m[a]?).isSome) : ((writeLog m log)[a]?).isSome := by
  rcases pointwise_writeLog log a with hp | ⟨v, hp⟩
  · rw [hp]; exact h
  · rw [hp]; rfl

theorem writeLog_getD_congr (m m' : Std.ExtHashMap Nat (BitVec 8)) (log : List WEntry) (a : Nat)
    (h : (m[a]?).getD 0 = (m'[a]?).getD 0) :
    ((writeLog m log)[a]?).getD 0 = ((writeLog m' log)[a]?).getD 0 := by
  rcases pointwise_writeLog log a with hp | ⟨v, hp⟩
  · rw [hp, hp]; exact h
  · rw [hp, hp]

theorem gprReg_htif_payload (n : Nat) : (gprReg n == Register.htif_payload_writes) = false := by
  unfold gprReg
  split <;> rfl

abbrev segOut (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8))) : SegEvalState :=
  evalBlocks bs (SegEvalState.init L lds)

def finReg (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8))) (n : Nat) :
    BitVec 64 :=
  (lookupG n (segOut bs L lds).regs).getD 0

def segRW (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8))) (pc0 : BitVec 64) :
    List (Nat × BitVec 64 × BitVec 64) :=
  (VsaIris.PC, pc0, evalBlocksPC pc0 (SegEvalState.init L lds) bs) ::
    L.map fun p => (p.1, p.2, finReg bs L lds p.1)

def wbase : List (Nat × BitVec 8) → Std.ExtHashMap Nat (BitVec 8)
  | [] => ∅
  | p :: W => (wbase W).insert p.1 p.2

def segMW (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (W : List (Nat × BitVec 8)) : List (Nat × BitVec 8 × BitVec 8) :=
  W.map fun p => (p.1, p.2, ((writeLog (wbase W) (segOut bs L lds).log)[p.1]?).getD 0)

theorem wbase_get {a : Nat} : ∀ {W : List (Nat × BitVec 8)} {o : BitVec 8}, (a, o) ∈ W →
    ∃ o', (a, o') ∈ W ∧ (wbase W)[a]? = some o'
  | p :: W, o, h => by
    simp only [wbase]
    rw [Std.ExtHashMap.getElem?_insert]
    by_cases hp : p.1 = a
    · exact ⟨p.2, by rw [← hp]; exact List.mem_cons_self, by simp [hp]⟩
    · rw [ite_eq_right (by simp [hp])]
      rcases List.mem_cons.mp h with rfl | h
      · exact absurd rfl hp
      · obtain ⟨o', ho, hg⟩ := wbase_get h
        exact ⟨o', .tail _ ho, hg⟩

theorem seg_runFact (live : Nat → Prop) (bs : List BBlock) (L : GRegs)
    (lds : List (List (BitVec 8))) (pc0 : BitVec 64) (MR : List (Nat × DFrac × BitVec 8))
    (W : List (Nat × BitVec 8)) (n : Nat) (hlen : evalBlocksFuel bs = n + 1)
    (hwf : ChainOK pc0 (keysG L) bs) (hkeys : KeysOK (keysG L))
    (hwr : ∀ k ∈ wrChain bs, k ∈ keysG L)
    (hcover : ∀ a, (∀ p ∈ W, p.1 ≠ a) → OutL (segOut bs L lds).log a)
    (hfacts : ∀ c : Config, VsaOk live c →
      FootHolds (M := vsaModel live) c [] MR (segRW bs L lds pc0) (segMW bs L lds W) →
      ChainFacts c.σ.mem c.σ.mem L lds bs) :
    RunFact (vsaModel live) n [] MR (segRW bs L lds pc0) (segMW bs L lds W) := by
  intro c hok hfoot
  have hok : VsaOk live c := hok
  obtain ⟨_, hMR, hRW, hMW⟩ := hfoot
  have hfacts' := hfacts c hok ⟨(fun _ h => nomatch h), hMR, hRW, hMW⟩

  have hpc : c.σ.regs.get? Register.PC = some pc0 := by
    have h := hRW _ List.mem_cons_self
    change pcVal c.σ = pc0 at h
    obtain ⟨v, hv⟩ := hok.good.PC
    unfold pcVal at h
    rw [hv] at h ⊢
    exact congrArg some h
  obtain ⟨vm, hmi⟩ := hok.good.minstret
  have hkeyL : ∀ p ∈ L, 1 ≤ p.1 ∧ p.1 ≤ 31 := fun p hp => hkeys p.1 (mem_keysG_of_mem hp)
  have hL : GHolds c.σ L := gholds_of_forall L fun p hp =>
    gprGet_eq_of_vsaReg hok (hkeyL p hp).1 (hkeyL p hp).2
      (hRW (p.1, p.2, finReg bs L lds p.1)
        (.tail _ (List.mem_map_of_mem (f := fun p => (p.1, p.2, finReg bs L lds p.1)) hp)))

  obtain ⟨σ', i', hs, hi', hG', hmem', hout', hpc', _, hregs, hframe⟩ :=
    segEval_sound bs c.σ c.tick c.steps pc0 vm L lds hok.good hpc hmi hL hkeys hfacts' hwf
      hok.tick
  have hN : StepsN (n + 1) c ⟨σ', i', c.steps + evalBlocksFuel bs⟩ := by
    have h := Vsa.Machine.Steps.toN_of_stepsEq (k := evalBlocksFuel bs) hs rfl
    rw [show n + 1 = evalBlocksFuel bs from hlen.symm]
    exact h
  have hkout : ∀ k ∈ keysG L, k ∈ keysG (segOut bs L lds).regs := fun k hk => by
    rw [evalBlocks_regs]; exact mem_keysG_runChain bs L lds hk
  have hwrne : ∀ k, k ∉ wrChain bs → 1 ≤ k → k ≤ 31 →
      ∀ m ∈ wrChain bs, (gprReg m == gprReg k) = false := fun k hk h1 h31 m hm => by
    have hm' := hkeys m (hwr m hm)
    exact gprReg_beq_false m (by omega) k (by omega) hm'.1 h1 (fun e => hk (e ▸ hm))
  have hframeK : ∀ k, k ∉ wrChain bs → 1 ≤ k → k ≤ 31 → gprGet σ' k = gprGet c.σ k :=
    fun k hk h1 h31 =>
      gprGet_of_frame k h1 h31 (gpr_avoids_noise k (by omega) h1) (hwrne k hk h1 h31) hframe
  have hfin : ∀ k ∈ keysG L, gprGet σ' k = some (finReg bs L lds k) := fun k hk => by
    obtain ⟨w, hw⟩ := lookupG_of_mem (hkout k hk)
    unfold finReg
    rw [hw]
    exact gholds_lookup _ hregs hw
  refine ⟨⟨σ', i', c.steps + evalBlocksFuel bs⟩, reachesN_of_stepsN hN, ?_, ?_,
    show output σ' = output c.σ by unfold output; rw [hout']⟩
  ·
    refine ⟨hG', hi', fun k h1 h31 => ?_, fun a ha => ?_, ?_⟩
    · by_cases hk : k ∈ wrChain bs
      · rw [hfin k (hwr k hk)]; rfl
      · rw [hframeK k hk h1 h31]; exact hok.gpr k h1 h31
    · show ((σ'.mem)[a]?).isSome
      rw [hmem']
      exact writeLog_present _ _ _ (hok.live a ha)
    · rw [hframe _ (by decide) (fun m _ => gprReg_htif_payload m)]
      exact hok.htifIdle
  ·
    constructor
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · change vsaReg _ VsaIris.PC = _
        unfold vsaReg pcVal
        rw [ite_eq_left rfl]
        simp only [hpc']
        rfl
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        have hq' := hkeyL q hq
        change vsaReg _ q.1 = finReg bs L lds q.1
        rw [vsaReg_gpr (by unfold VsaIris.PC; omega)]
        simp only [hfin q.1 (mem_keysG_of_mem hq)]
        rfl
    · intro k hk
      have hkpc : k ≠ VsaIris.PC := fun e => hk _ List.mem_cons_self e.symm
      have hkL : k ∉ keysG L := fun hkL => by
        obtain ⟨v, hv⟩ := exists_of_mem_keysG hkL
        exact hk (k, v, finReg bs L lds k)
          (.tail _ (List.mem_map_of_mem (f := fun p => (p.1, p.2, finReg bs L lds p.1)) hv)) rfl
      change vsaReg _ k = vsaReg c k
      rw [vsaReg_gpr hkpc, vsaReg_gpr (c := c) hkpc]
      by_cases hr : 1 ≤ k ∧ k ≤ 31
      · rw [hframeK k (fun hw => hkL (hwr k hw)) hr.1 hr.2]
      · rw [gprGet_none (by omega), gprGet_none (by omega)]
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      change ((σ'.mem)[q.1]?).getD 0 = ((writeLog (wbase W) (segOut bs L lds).log)[q.1]?).getD 0
      rw [hmem']
      apply writeLog_getD_congr
      obtain ⟨o', ho', hg⟩ := wbase_get hq
      rw [hg]
      exact hMW (q.1, o', _) (List.mem_map_of_mem ho')
    · intro k hk
      change ((σ'.mem)[k]?).getD 0 = ((c.σ.mem)[k]?).getD 0
      rw [hmem', writeLog_out _ _ _ (hcover k fun p hp e =>
        hk (p.1, p.2, _) (List.mem_map_of_mem hp) e)]

theorem sepL_map {GF : BundledGFunctors} {α β : Type _} (f : α → β) (P : β → IProp GF) :
    ∀ l : List α, sepL (l.map f) P = sepL l (fun x => P (f x))
  | [] => rfl
  | x :: xs => by simp only [List.map_cons, sepL_cons, sepL_map f P xs]

abbrev newByte (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (W : List (Nat × BitVec 8)) (a : Nat) : BitVec 8 :=
  ((writeLog (wbase W) (segOut bs L lds).log)[a]?).getD 0

section Wp

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem wp_segW {Φ : Nat × String → IProp GF} (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8))) (pc0 : BitVec 64)
    (MR : List (Nat × DFrac × BitVec 8)) (W : List (Nat × BitVec 8)) (n : Nat)
    (hlen : evalBlocksFuel bs = n + 1)
    (hwf : ChainOK pc0 (keysG L) bs) (hkeys : KeysOK (keysG L))
    (hwr : ∀ k ∈ wrChain bs, k ∈ keysG L)
    (hcover : ∀ a, (∀ p ∈ W, p.1 ≠ a) → OutL (segOut bs L lds).log a)
    (hfacts : ∀ c : Config, VsaOk live c →
      FootHolds (M := vsaModel live) c [] MR (segRW bs L lds pc0) (segMW bs L lds W) →
      ChainFacts c.σ.mem c.σ.mem L lds bs) :
    VsaIris.PC ↦ᵣ pc0 ∗ sepL L (fun p => p.1 ↦ᵣ p.2) ∗ sepL W (fun p => p.1 ↦ₘ p.2) ∗
      sepL MR (fun p => p.1 ↦ₘ{p.2.1} p.2.2) ∗
      (VsaIris.PC ↦ᵣ evalBlocksPC pc0 (SegEvalState.init L lds) bs -∗
        sepL L (fun p => p.1 ↦ᵣ finReg bs L lds p.1) -∗
        sepL W (fun p => p.1 ↦ₘ newByte bs L lds W p.1) -∗
        sepL MR (fun p => p.1 ↦ₘ{p.2.1} p.2.2) -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hpc, HL, HW, HMR, Hk⟩
  iapply Wp.run n [] MR (segRW bs L lds pc0) (segMW bs L lds W)
    (seg_runFact live bs L lds pc0 MR W n hlen hwf hkeys hwr hcover hfacts)
  unfold footPre footPost segRW segMW
  simp only [sepL_cons, sepL_nil, sepL_map]
  iframe HMR Hpc HL HW
  iintro ⟨-, HMR, ⟨Hpc, HL⟩, HW⟩
  iapply Hk $$ Hpc HL HW HMR

end Wp

end VsaIris.Inst
