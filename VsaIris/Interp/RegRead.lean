import VsaIris.Interp.Arm

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast Vsa.MemRepr Vsa.Sim

theorem ldv_win (k : MKind) {M M' : Mem} {S : Nat → Prop} {a : Nat}
    (h : ∀ b, S b → imgM M' b = imgM M b) (hs : ∀ j, j < widthOfM k → S (a + j)) :
    ldv k M' a = ldv k M a := by
  unfold ldv bytesAt
  congr 1
  apply List.map_congr_left
  intro j hj
  exact h _ (hs j (List.mem_range.1 hj))

theorem rk_ite_neg {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

syntax "rd_disch" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rd_disch) => `(tactic| rd_disch [])
  | `(tactic| rd_disch [$ds,*]) =>
    `(tactic| ((try intro _ _); first | decide | omega |
      ((try simp only [widthOfM, InExt, $ds,*] at *); first | omega | sx_addr)))

syntax "rd_back" (" [" Lean.Parser.Tactic.simpLemma,* "]")?
  (" using " "[" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| rd_back $[[$hs?,*]]? $[using [$ds?,*]]? $[$loc]?) => do
    let hs := hs?.map (·.getElems) |>.getD #[]
    let ds := ds?.map (·.getElems) |>.getD #[]
    `(tactic| simp (disch := rd_disch [$ds,*]) only [imgM_store_miss, ldv_store_miss, $hs,*] $[$loc]?)

syntax "reg_keep" " [" term,* "]" : tactic
macro_rules
  | `(tactic| reg_keep [$hs,*]) => do
    let mut t ← `(tactic| fail "reg_keep")
    for h in hs.getElems.reverse do
      t ← `(tactic| first | (apply $h <;> assumption) | ($t:tactic))
    `(tactic| (intro y _; intros
               simp (disch := (revert y; decide +kernel)) only [upd_apply, rk_ite_neg]
               $t:tactic))

end VsaIris.Interp
