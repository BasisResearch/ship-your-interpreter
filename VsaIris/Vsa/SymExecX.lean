import VsaIris.Vsa.SymExec
import VsaIris.Vsa.StepRules

/-!
# Extensions of the reflective executor

`symRunX C sub n s pf` runs the executor of `SymExec.lean` with four additions, proved sound once by
`symRunX_swp` (and its segment form `symRunX_cont`):

* **path facts** `pf : List PF` (`x = c`, `x ≠ c`, `x <u n`, `n ≤u x`): a fork records the facts
  its outcome implies; an `x = c` fact also rewrites `x` to `c` in the registers and the store
  list of that side;
* **branch decisions** (`brDecide`): a branch is decided by the constants of its operands, the
  known entry registers (`Cfg.known`, also for a register the run has not written), the path
  facts, or the syntactic equality of its operands; the untaken side is not in the tree
  (`XTree.brD`);
* **jump-table dispatch** (`splitStep`): a load whose address is constant in the image for every
  value `j < n` of an atom `x` with a path fact `x <u n` splits the run over the values
  (`XTree.sel`); each side reads its table entry from the image, so the indirect jump that
  follows has a constant target;
* **width-exact store forwarding** (`subHit`): a load inside an earlier store of the same base
  reads its bytes (`fwdV`), e.g. a 16-bit `lhu` of a field written by `sh` or by `sd`.
-/

namespace VsaIris.SymExec

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-! ## Substitution and constant folding -/

/-- Replace every occurrence of `e` by `v`. -/
def SE.subst (x e v : SE) : SE :=
  if x = e then v else
  match x with
  | .add a b => .add (SE.subst a e v) (SE.subst b e v)
  | .sub a b => .sub (SE.subst a e v) (SE.subst b e v)
  | .ld k a => .ld k (SE.subst a e v)
  | .ldD k a => .ldD k (SE.subst a e v)
  | .alu i a b => .alu i (SE.subst a e v) (SE.subst b e v)
  | .ltu a b => .ltu (SE.subst a e v) (SE.subst b e v)
  | x => x

theorem SE.subst_den (ρ : Env) {e v : SE} (h : e.den ρ = v.den ρ) :
    ∀ x : SE, (x.subst e v).den ρ = x.den ρ := by
  intro x
  induction x with
  | add a b iha ihb =>
    unfold SE.subst; split
    · rename_i hx; rw [hx]; exact h.symm
    · simp only [SE.den, iha, ihb]
  | sub a b iha ihb =>
    unfold SE.subst; split
    · rename_i hx; rw [hx]; exact h.symm
    · simp only [SE.den, iha, ihb]
  | ld k a iha =>
    unfold SE.subst; split
    · rename_i hx; rw [hx]; exact h.symm
    · simp only [SE.den, iha]
  | ldD k a iha =>
    unfold SE.subst; split
    · rename_i hx; rw [hx]; exact h.symm
    · simp only [SE.den, iha]
  | alu i a b iha ihb =>
    unfold SE.subst; split
    · rename_i hx; rw [hx]; exact h.symm
    · simp only [SE.den, iha, ihb]
  | ltu a b iha ihb =>
    unfold SE.subst; split
    · rename_i hx; rw [hx]; exact h.symm
    · simp only [SE.den, iha, ihb]
  | c _ =>
    unfold SE.subst; split
    · rename_i hx; rw [hx]; exact h.symm
    · rfl
  | r _ =>
    unfold SE.subst; split
    · rename_i hx; rw [hx]; exact h.symm
    · rfl
  | h _ =>
    unfold SE.subst; split
    · rename_i hx; rw [hx]; exact h.symm
    · rfl
  | raw _ =>
    unfold SE.subst; split
    · rename_i hx; rw [hx]; exact h.symm
    · rfl

def subC (x y : SE) : SE :=
  match x, y with
  | .c a, .c b => .c (a - b)
  | x, y => .sub x y

def aluC (i : MInstr) (x y : SE) : SE :=
  match x, y with
  | .c a, .c b => .c (aluVal i a b)
  | x, y => .alu i x y

def ltuC (x y : SE) : SE :=
  match x, y with
  | .c a, .c b => .c (zero_extend (m := 64) (bool_to_bit (zopz0zI_u a b)))
  | x, y => .ltu x y

/-- Fold constant subterms (the address arithmetic of a jump-table access after a split). -/
def SE.fold : SE → SE
  | .add a b => addS a.fold b.fold
  | .sub a b => subC a.fold b.fold
  | .alu i a b => aluC i a.fold b.fold
  | .ltu a b => ltuC a.fold b.fold
  | .ld k a => .ld k a.fold
  | .ldD k a => .ldD k a.fold
  | x => x

theorem SE.fold_den (ρ : Env) : ∀ x : SE, x.fold.den ρ = x.den ρ
  | .add a b => by
    show (addS a.fold b.fold).den ρ = _
    rw [addS_den, SE.fold_den ρ a, SE.fold_den ρ b]; rfl
  | .sub a b => by
    show (subC a.fold b.fold).den ρ = _
    have ha := SE.fold_den ρ a; have hb := SE.fold_den ρ b
    unfold subC; split
    · rename_i x y hx hy; rw [hx] at ha; rw [hy] at hb
      show x - y = a.den ρ - b.den ρ
      rw [← ha, ← hb]; rfl
    · show a.fold.den ρ - b.fold.den ρ = _; rw [ha, hb]; rfl
  | .alu i a b => by
    show (aluC i a.fold b.fold).den ρ = _
    have ha := SE.fold_den ρ a; have hb := SE.fold_den ρ b
    unfold aluC; split
    · rename_i x y hx hy; rw [hx] at ha; rw [hy] at hb
      show aluVal i x y = aluVal i (a.den ρ) (b.den ρ)
      rw [← ha, ← hb]; rfl
    · show aluVal i (a.fold.den ρ) (b.fold.den ρ) = _; rw [ha, hb]; rfl
  | .ltu a b => by
    show (ltuC a.fold b.fold).den ρ = _
    have ha := SE.fold_den ρ a; have hb := SE.fold_den ρ b
    unfold ltuC; split
    · rename_i x y hx hy; rw [hx] at ha; rw [hy] at hb
      show zero_extend (m := 64) (bool_to_bit (zopz0zI_u x y)) =
        zero_extend (m := 64) (bool_to_bit (zopz0zI_u (a.den ρ) (b.den ρ)))
      rw [← ha, ← hb]; rfl
    · show zero_extend (m := 64) (bool_to_bit (zopz0zI_u (a.fold.den ρ) (b.fold.den ρ))) = _
      rw [ha, hb]; rfl
  | .ld k a => by
    show ldv k ρ.M0 (a.fold.den ρ).toNat = _; rw [SE.fold_den ρ a]; rfl
  | .ldD k a => by
    show ldv k ρ.D0 (a.fold.den ρ).toNat = _; rw [SE.fold_den ρ a]; rfl
  | .c _ => rfl
  | .r _ => rfl
  | .h _ => rfl
  | .raw _ => rfl

/-- Substitute, then fold. -/
def SE.sf (x e v : SE) : SE := (x.subst e v).fold

theorem SE.sf_den (ρ : Env) {e v : SE} (h : e.den ρ = v.den ρ) (x : SE) :
    (x.sf e v).den ρ = x.den ρ := by
  unfold SE.sf; rw [SE.fold_den, SE.subst_den ρ h]

def regsSF (e v : SE) (L : List (Nat × SE)) : List (Nat × SE) := L.map fun p => (p.1, p.2.sf e v)

def memSF (e v : SE) (M : SMem) : SMem := M.map fun p => (p.1.sf e v, p.2.1, p.2.2.sf e v)

theorem regsSF_den (ρ : Env) {e v : SE} (h : e.den ρ = v.den ρ) :
    ∀ L : List (Nat × SE), regsDen ρ (regsSF e v L) = regsDen ρ L
  | [] => rfl
  | (k, x) :: L => by
    show upd (regsDen ρ (regsSF e v L)) k ((x.sf e v).den ρ) = upd (regsDen ρ L) k (x.den ρ)
    rw [regsSF_den ρ h L, SE.sf_den ρ h]

theorem memSF_den (ρ : Env) {e v : SE} (h : e.den ρ = v.den ρ) :
    ∀ M : SMem, memDen ρ (memSF e v M) = memDen ρ M
  | [] => rfl
  | (a, w, x) :: M => by
    show writeLog (memDen ρ (memSF e v M)) [(((a.sf e v).den ρ).toNat, w, (x.sf e v).den ρ)] = _
    rw [memSF_den ρ h M, SE.sf_den ρ h, SE.sf_den ρ h]; rfl

theorem regsSF_keys (e v : SE) (L : List (Nat × SE)) (r : Nat) :
    (regsSF e v L).any (fun p => decide (p.1 = r)) = L.any (fun p => decide (p.1 = r)) := by
  induction L with
  | nil => rfl
  | cons p L ih => simp only [regsSF, List.map_cons, List.any_cons] at ih ⊢; rw [ih]

/-- The state with `e` replaced by `v` (registers and stores; obligations stay). -/
def SS.sf (s : SS) (e v : SE) : SS := ⟨s.pc, regsSF e v s.regs, memSF e v s.mem, s.obs⟩

/-! ## Path facts -/

inductive PF where
  | eq (e : SE) (v : BitVec 64)
  | ne (e : SE) (v : BitVec 64)
  | ult (e : SE) (n : Nat)
  | uge (e : SE) (n : Nat)
deriving DecidableEq

def PF.den (ρ : Env) : PF → Prop
  | .eq e v => e.den ρ = v
  | .ne e v => e.den ρ ≠ v
  | .ult e n => (e.den ρ).toNat < n
  | .uge e n => n ≤ (e.den ρ).toNat

def PFOK (ρ : Env) (pf : List PF) : Prop := ∀ p ∈ pf, p.den ρ

theorem pfok_nil (ρ : Env) : PFOK ρ [] := fun _ h => nomatch h

theorem pfok_append {ρ : Env} {a b : List PF} (ha : PFOK ρ a) (hb : PFOK ρ b) : PFOK ρ (a ++ b) :=
  fun p hp => (List.mem_append.1 hp).elim (ha p) (hb p)

def PF.hasH (i : Nat) : PF → Bool
  | .eq e _ => e.hasH i
  | .ne e _ => e.hasH i
  | .ult e _ => e.hasH i
  | .uge e _ => e.hasH i

def PF.maxH : PF → Nat
  | .eq e _ => e.maxH
  | .ne e _ => e.maxH
  | .ult e _ => e.maxH
  | .uge e _ => e.maxH

def pfHasH (i : Nat) (pf : List PF) : Bool := pf.any fun p => p.hasH i

theorem PF.den_withH (ρ : Env) (i : Nat) (v : BitVec 64) (p : PF) (h : p.hasH i = false) :
    p.den (ρ.withH i v) ↔ p.den ρ := by
  cases p <;> simp only [PF.hasH] at h <;> simp only [PF.den, SE.den_withH ρ i v _ h]

theorem pfok_withH {ρ : Env} {i : Nat} {v : BitVec 64} {pf : List PF} (h : pfHasH i pf = false)
    (hp : PFOK ρ pf) : PFOK (ρ.withH i v) pf := fun p hm =>
  (PF.den_withH ρ i v p (by simp only [pfHasH, List.any_eq_false] at h; simpa using h p hm)).2 (hp p hm)

/-- Branch operand: a known entry register is its constant, a fact `x = c` makes `x` the
constant. -/
def unraw (K : List (Nat × BitVec 64)) : SE → SE
  | .raw r => lookupK K r
  | x => x

theorem unraw_den {ρ : Env} {K : List (Nat × BitVec 64)} (hK : KnownOK ρ K) (x : SE) :
    (unraw K x).den ρ = x.den ρ := by
  cases x <;> try rfl
  exact lookupK_den hK _

def pfFind (pf : List PF) (x : SE) : Option (BitVec 64) :=
  pf.findSome? fun p => match p with
    | .eq e v => if e = x then some v else none
    | _ => none

theorem pfFind_den {ρ : Env} {pf : List PF} (hp : PFOK ρ pf) {x : SE} {v : BitVec 64}
    (h : pfFind pf x = some v) : x.den ρ = v := by
  unfold pfFind at h
  obtain ⟨p, hm, hp'⟩ := List.exists_of_findSome?_eq_some h
  have hd := hp p hm
  cases p with
  | eq e w =>
    simp only at hp'
    split at hp'
    · rename_i he; cases hp'; subst he; exact hd
    · cases hp'
  | ne e w => simp at hp'
  | ult e n => simp at hp'
  | uge e n => simp at hp'

def opnd (K : List (Nat × BitVec 64)) (pf : List PF) (x : SE) : SE :=
  match pfFind pf (unraw K x) with
  | some v => .c v
  | none => unraw K x

theorem opnd_den {ρ : Env} {K : List (Nat × BitVec 64)} (hK : KnownOK ρ K) {pf : List PF}
    (hp : PFOK ρ pf) (x : SE) : (opnd K pf x).den ρ = x.den ρ := by
  unfold opnd
  split
  · rename_i v hv; exact (pfFind_den hp hv).symm.trans (unraw_den hK x)
  · exact unraw_den hK x

def ultB (pf : List PF) (x : SE) (n : Nat) : Bool :=
  pf.any fun p => match p with | .ult e m => decide (e = x ∧ m ≤ n) | _ => false

def ugeB (pf : List PF) (x : SE) (n : Nat) : Bool :=
  pf.any fun p => match p with | .uge e m => decide (e = x ∧ n ≤ m) | _ => false

def neB (pf : List PF) (x : SE) (v : BitVec 64) : Bool :=
  pf.any fun p => match p with | .ne e w => decide (e = x ∧ w = v) | _ => false

theorem ultB_sound {ρ : Env} {pf : List PF} (hp : PFOK ρ pf) {x : SE} {n : Nat}
    (h : ultB pf x n = true) : (x.den ρ).toNat < n := by
  obtain ⟨p, hm, hb⟩ := List.any_eq_true.1 h
  have hd := hp p hm
  cases p with
  | ult e m =>
    simp only [decide_eq_true_eq] at hb
    obtain ⟨rfl, hle⟩ := hb
    exact Nat.lt_of_lt_of_le hd hle
  | eq _ _ => simp at hb
  | ne _ _ => simp at hb
  | uge _ _ => simp at hb

theorem ugeB_sound {ρ : Env} {pf : List PF} (hp : PFOK ρ pf) {x : SE} {n : Nat}
    (h : ugeB pf x n = true) : n ≤ (x.den ρ).toNat := by
  obtain ⟨p, hm, hb⟩ := List.any_eq_true.1 h
  have hd := hp p hm
  cases p with
  | uge e m =>
    simp only [decide_eq_true_eq] at hb
    obtain ⟨rfl, hle⟩ := hb
    exact Nat.le_trans hle hd
  | eq _ _ => simp at hb
  | ne _ _ => simp at hb
  | ult _ _ => simp at hb

theorem neB_sound {ρ : Env} {pf : List PF} (hp : PFOK ρ pf) {x : SE} {v : BitVec 64}
    (h : neB pf x v = true) : x.den ρ ≠ v := by
  obtain ⟨p, hm, hb⟩ := List.any_eq_true.1 h
  have hd := hp p hm
  cases p with
  | ne e w =>
    simp only [decide_eq_true_eq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact hd
  | eq _ _ => simp at hb
  | ult _ _ => simp at hb
  | uge _ _ => simp at hb

/-- `x <u c`, from facts. -/
def ltuR (pf : List PF) (x : SE) (w : BitVec 64) : Option Bool :=
  if ultB pf x w.toNat then some true else if ugeB pf x w.toNat then some false else none

/-- `c <u y`, from facts. -/
def ltuL (pf : List PF) (u : BitVec 64) (y : SE) : Option Bool :=
  if ugeB pf y (u.toNat + 1) then some true else if ultB pf y (u.toNat + 1) then some false else none

/-- `x <u y`, decided from constants and facts. -/
def ltuDec (pf : List PF) (x y : SE) : Option Bool :=
  match x, y with
  | .c u, .c w => some (decide (u.toNat < w.toNat))
  | x, .c w => ltuR pf x w
  | .c u, y => ltuL pf u y
  | _, _ => none

def eqR (pf : List PF) (x : SE) (w : BitVec 64) : Option Bool :=
  if neB pf x w then some false else none

def eqL (pf : List PF) (u : BitVec 64) (y : SE) : Option Bool :=
  if neB pf y u then some false else none

def eqS (x y : SE) : Option Bool := if x = y then some true else none

/-- `x = y`, decided from constants, facts and syntactic equality. -/
def eqDec (pf : List PF) (x y : SE) : Option Bool :=
  match x, y with
  | .c u, .c w => some (decide (u = w))
  | x, .c w => eqR pf x w
  | .c u, y => eqL pf u y
  | x, y => eqS x y

theorem ltuR_sound {ρ : Env} {pf : List PF} (hp : PFOK ρ pf) {x : SE} {w : BitVec 64} {b : Bool}
    (h : ltuR pf x w = some b) : decide ((x.den ρ).toNat < w.toNat) = b := by
  unfold ltuR at h
  by_cases h1 : ultB pf x w.toNat = true
  · rw [if_pos h1] at h; cases h; exact decide_eq_true (ultB_sound hp h1)
  · rw [if_neg h1] at h
    by_cases h2 : ugeB pf x w.toNat = true
    · rw [if_pos h2] at h; cases h; exact decide_eq_false (Nat.not_lt.2 (ugeB_sound hp h2))
    · rw [if_neg h2] at h; cases h

theorem ltuL_sound {ρ : Env} {pf : List PF} (hp : PFOK ρ pf) {u : BitVec 64} {y : SE} {b : Bool}
    (h : ltuL pf u y = some b) : decide (u.toNat < (y.den ρ).toNat) = b := by
  unfold ltuL at h
  by_cases h1 : ugeB pf y (u.toNat + 1) = true
  · rw [if_pos h1] at h; cases h
    have := ugeB_sound hp h1; exact decide_eq_true (by omega)
  · rw [if_neg h1] at h
    by_cases h2 : ultB pf y (u.toNat + 1) = true
    · rw [if_pos h2] at h; cases h
      have := ultB_sound hp h2; exact decide_eq_false (by omega)
    · rw [if_neg h2] at h; cases h

theorem ltuDec_sound {ρ : Env} {pf : List PF} (hp : PFOK ρ pf) {x y : SE} {b : Bool}
    (h : ltuDec pf x y = some b) : decide ((x.den ρ).toNat < (y.den ρ).toNat) = b := by
  unfold ltuDec at h
  split at h
  · cases h; rfl
  · exact ltuR_sound hp h
  · exact ltuL_sound hp h
  · cases h

theorem eqDec_sound {ρ : Env} {pf : List PF} (hp : PFOK ρ pf) {x y : SE} {b : Bool}
    (h : eqDec pf x y = some b) : decide (x.den ρ = y.den ρ) = b := by
  unfold eqDec at h
  split at h
  · cases h; rfl
  · unfold eqR at h
    split at h
    · cases h; rename_i hu; exact decide_eq_false (neB_sound hp hu)
    · cases h
  · unfold eqL at h
    split at h
    · cases h; rename_i hu; exact decide_eq_false (fun e => neB_sound hp hu e.symm)
    · cases h
  · unfold eqS at h
    split at h
    · cases h; rename_i he; subst he; exact decide_eq_true rfl
    · cases h

theorem guardB_beq_dec (a b : BitVec 64) : guardB .BEQ a b = decide (a = b) := by
  by_cases h : a = b
  · rw [decide_eq_true h]; exact (guard_beq a b).2 h
  · rw [decide_eq_false h]
    cases hg : guardB .BEQ a b
    · rfl
    · exact absurd ((guard_beq a b).1 hg) h

theorem guardB_bltu_dec (a b : BitVec 64) : guardB .BLTU a b = decide (a.toNat < b.toNat) := by
  by_cases h : a.toNat < b.toNat
  · rw [decide_eq_true h]; exact (guard_bltu a b).2 h
  · rw [decide_eq_false h]
    cases hg : guardB .BLTU a b
    · rfl
    · exact absurd ((guard_bltu a b).1 hg) h

theorem guardB_bgeu_dec (a b : BitVec 64) : guardB .BGEU a b = decide (b.toNat ≤ a.toNat) := by
  by_cases h : b.toNat ≤ a.toNat
  · rw [decide_eq_true h]; exact (guard_bgeu a b).2 h
  · rw [decide_eq_false h]
    cases hg : guardB .BGEU a b
    · rfl
    · exact absurd ((guard_bgeu a b).1 hg) h

theorem guardB_bne_dec (a b : BitVec 64) : guardB .BNE a b = !decide (a = b) := by
  by_cases h : a = b
  · rw [decide_eq_true h]
    cases hg : guardB .BNE a b
    · rfl
    · exact absurd h ((guard_bne a b).1 hg)
  · rw [decide_eq_false h]; exact (guard_bne a b).2 h

theorem guardB_bgeu (a b : BitVec 64) : guardB .BGEU a b = !guardB .BLTU a b := by
  rw [guardB_bgeu_dec, guardB_bltu_dec]
  by_cases h : a.toNat < b.toNat
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl

/-- The outcome of a branch, when constants, known registers, facts or syntax decide it. -/
def brDecide (pf : List PF) (op : bop) (x y : SE) : Option Bool :=
  match op with
  | .BEQ => eqDec pf x y
  | .BNE => (eqDec pf x y).map (!·)
  | .BLTU => ltuDec pf x y
  | .BGEU => (ltuDec pf x y).map (!·)
  | op => match x, y with
    | .c u, .c w => some (guardB op u w)
    | _, _ => none

theorem brDecide_sound {ρ : Env} {pf : List PF} (hp : PFOK ρ pf) {op : bop} {x y : SE} {b : Bool}
    (h : brDecide pf op x y = some b) : guardB op (x.den ρ) (y.den ρ) = b := by
  unfold brDecide at h
  split at h
  · rw [guardB_beq_dec]; exact eqDec_sound hp h
  · obtain ⟨b', h', rfl⟩ := Option.map_eq_some_iff.1 h
    rw [guardB_bne_dec, eqDec_sound hp h']
  · rw [guardB_bltu_dec]; exact ltuDec_sound hp h
  · obtain ⟨b', h', rfl⟩ := Option.map_eq_some_iff.1 h
    rw [guardB_bgeu, guardB_bltu_dec, ltuDec_sound hp h']
  · split at h
    · cases h; rfl
    · cases h

/-- Facts of `x = y` (or `x ≠ y`). -/
def eqFacts (isEq : Bool) (x y : SE) : List PF :=
  match x, y with
  | .c _, .c _ => []
  | x, .c w => [if isEq then .eq x w else .ne x w]
  | .c u, y => [if isEq then .eq y u else .ne y u]
  | _, _ => []

/-- Facts of `x <u y` (or `¬ x <u y`). -/
def ltFacts (isLt : Bool) (x y : SE) : List PF :=
  match x, y with
  | .c _, .c _ => []
  | x, .c w => [if isLt then .ult x w.toNat else .uge x w.toNat]
  | .c u, y => [if isLt then .uge y (u.toNat + 1) else .ult y (u.toNat + 1)]
  | _, _ => []

def brFacts (op : bop) (x y : SE) (g : Bool) : List PF :=
  match op with
  | .BEQ => eqFacts g x y
  | .BNE => eqFacts (!g) x y
  | .BLTU => ltFacts g x y
  | .BGEU => ltFacts (!g) x y
  | _ => []

theorem pfok_single {ρ : Env} {p : PF} (h : p.den ρ) : PFOK ρ [p] := by
  intro q hq; rw [List.mem_singleton] at hq; subst hq; exact h

theorem eqFact1 {ρ : Env} {x : SE} {w : BitVec 64} {g : Bool} (h : decide (x.den ρ = w) = g) :
    PFOK ρ [if g then .eq x w else .ne x w] := by
  refine pfok_single ?_
  cases g
  · exact (show x.den ρ ≠ w from of_decide_eq_false h)
  · exact (show x.den ρ = w from of_decide_eq_true h)

theorem ltFact1 {ρ : Env} {x : SE} {w : BitVec 64} {g : Bool}
    (h : decide ((x.den ρ).toNat < w.toNat) = g) :
    PFOK ρ [if g then .ult x w.toNat else .uge x w.toNat] := by
  refine pfok_single ?_
  cases g
  · exact (show w.toNat ≤ (x.den ρ).toNat from Nat.not_lt.1 (of_decide_eq_false h))
  · exact (show (x.den ρ).toNat < w.toNat from of_decide_eq_true h)

theorem ltFact2 {ρ : Env} {u : BitVec 64} {y : SE} {g : Bool}
    (h : decide (u.toNat < (y.den ρ).toNat) = g) :
    PFOK ρ [if g then .uge y (u.toNat + 1) else .ult y (u.toNat + 1)] := by
  refine pfok_single ?_
  cases g
  · have : ¬ u.toNat < (y.den ρ).toNat := of_decide_eq_false h
    exact (show (y.den ρ).toNat < u.toNat + 1 by omega)
  · have : u.toNat < (y.den ρ).toNat := of_decide_eq_true h
    exact (show u.toNat + 1 ≤ (y.den ρ).toNat by omega)

theorem eqFacts_sound {ρ : Env} {x y : SE} {g : Bool} (h : decide (x.den ρ = y.den ρ) = g) :
    PFOK ρ (eqFacts g x y) := by
  unfold eqFacts
  split
  · exact pfok_nil ρ
  · exact eqFact1 h
  · exact eqFact1 (by rw [← h]; exact decide_eq_decide.2 eq_comm)
  · exact pfok_nil ρ

theorem ltFacts_sound {ρ : Env} {x y : SE} {g : Bool}
    (h : decide ((x.den ρ).toNat < (y.den ρ).toNat) = g) : PFOK ρ (ltFacts g x y) := by
  unfold ltFacts
  split
  · exact pfok_nil ρ
  · exact ltFact1 h
  · exact ltFact2 h
  · exact pfok_nil ρ

theorem brFacts_sound {ρ : Env} {op : bop} {x y : SE} {g : Bool}
    (h : guardB op (x.den ρ) (y.den ρ) = g) : PFOK ρ (brFacts op x y g) := by
  unfold brFacts
  split
  · rw [guardB_beq_dec] at h; exact eqFacts_sound h
  · rw [guardB_bne_dec] at h
    exact eqFacts_sound (by rw [← h]; simp)
  · rw [guardB_bltu_dec] at h; exact ltFacts_sound h
  · rw [guardB_bgeu, guardB_bltu_dec] at h
    exact ltFacts_sound (by rw [← h]; simp)
  · exact pfok_nil ρ

theorem zext_lt_of_sext {x : BitVec 32} {n : Nat} (hn : n ≤ 2 ^ 31)
    (h : (sign_extend (m := 64) x).toNat < n) : (zero_extend (m := 64) x).toNat < n := by
  simp only [sign_extend, zero_extend, Sail.BitVec.signExtend, Sail.BitVec.zeroExtend] at *
  rw [BitVec.toNat_signExtend] at h
  have := x.isLt
  split at h
  · simp only [BitVec.toNat_setWidth] at h; omega
  · simpa using h

theorem lwu_lt_of_lw {M : Mem} {a n : Nat} (hn : n ≤ 2 ^ 31) (h : (ldv .lw M a).toNat < n) :
    (ldv .lwu M a).toNat < n := by
  simp only [ldv, bytesVal] at h ⊢
  exact zext_lt_of_sext hn h

/-- A bound on a sign-extended word bounds its zero-extended load too (`lw`, then `lwu` of the
same word). -/
def lwOne (p : PF) : List PF :=
  match p with
  | .ult (.ldD .lw a) n => if n ≤ 2 ^ 31 then [.ult (.ldD .lwu a) n] else []
  | .ult (.ld .lw a) n => if n ≤ 2 ^ 31 then [.ult (.ld .lwu a) n] else []
  | _ => []

def lwFacts (fs : List PF) : List PF := fs.flatMap lwOne

theorem lwOne_sound {ρ : Env} {p : PF} (h : p.den ρ) : PFOK ρ (lwOne p) := by
  unfold lwOne
  split
  · split
    · rename_i a n hn; exact pfok_single (lwu_lt_of_lw hn h)
    · exact pfok_nil ρ
  · split
    · rename_i a n hn; exact pfok_single (lwu_lt_of_lw hn h)
    · exact pfok_nil ρ
  · exact pfok_nil ρ

theorem lwFacts_sound {ρ : Env} {fs : List PF} (hp : PFOK ρ fs) : PFOK ρ (lwFacts fs) := by
  intro q hq
  obtain ⟨p, hm, hq⟩ := List.mem_flatMap.1 hq
  exact lwOne_sound (hp p hm) q hq

/-- A side of a fork with its `x = c` facts applied to the registers and stores; an entry
register the run has not written gets the constant as its value. -/
def applyEq (s : SS) (e : SE) (v : BitVec 64) : SS :=
  let s1 := s.sf e (.c v)
  match e with
  | .r r => if s.regs.any (fun p => decide (p.1 = r)) then s1 else ⟨s1.pc, (r, .c v) :: s1.regs, s1.mem, s1.obs⟩
  | _ => s1

def applyFacts (s : SS) : List PF → SS
  | [] => s
  | .eq e v :: fs => applyFacts (applyEq s e v) fs
  | _ :: fs => applyFacts s fs

theorem regsDen_fresh (ρ : Env) {r : Nat} :
    ∀ {L : List (Nat × SE)}, L.any (fun p => decide (p.1 = r)) = false → regsDen ρ L r = ρ.R0 r
  | [], _ => rfl
  | (k, e) :: L, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    show upd (regsDen ρ L) k (e.den ρ) r = _
    rw [upd_other _ _ (Ne.symm h.1)]; exact regsDen_fresh ρ h.2

/-- Applying true facts keeps the denotation and the rest of the state. -/
theorem applyEq_den {ρ : Env} {s : SS} {e : SE} {v : BitVec 64} (h : e.den ρ = v) :
    (applyEq s e v).pc = s.pc ∧ (applyEq s e v).obs = s.obs ∧
    regsDen ρ (applyEq s e v).regs = regsDen ρ s.regs ∧
    memDen ρ (applyEq s e v).mem = memDen ρ s.mem := by
  have h' : e.den ρ = (SE.c v).den ρ := h
  have hr := regsSF_den ρ h' s.regs
  have hm := memSF_den ρ h' s.mem
  unfold applyEq
  split
  · rename_i r
    split
    · exact ⟨rfl, rfl, hr, hm⟩
    · rename_i hn
      refine ⟨rfl, rfl, ?_, hm⟩
      show upd (regsDen ρ (regsSF (.r r) (.c v) s.regs)) r v = _
      rw [hr]
      apply upd_self_eq
      rw [regsDen_fresh ρ (by cases hh : s.regs.any (fun p => decide (p.1 = r)) <;> simp_all [regsSF_keys])]; exact h
  · exact ⟨rfl, rfl, hr, hm⟩

theorem applyFacts_den {ρ : Env} :
    ∀ (fs : List PF) (s : SS), PFOK ρ fs → (applyFacts s fs).pc = s.pc ∧
      (applyFacts s fs).obs = s.obs ∧ regsDen ρ (applyFacts s fs).regs = regsDen ρ s.regs ∧
      memDen ρ (applyFacts s fs).mem = memDen ρ s.mem
  | [], s, _ => ⟨rfl, rfl, rfl, rfl⟩
  | .eq e v :: fs, s, hp => by
    have h1 := applyEq_den (s := s) (hp _ List.mem_cons_self)
    have h2 := applyFacts_den fs (applyEq s e v) (fun p hm => hp p (List.mem_cons_of_mem _ hm))
    exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩
  | .ne _ _ :: fs, s, hp => applyFacts_den fs s (fun p hm => hp p (List.mem_cons_of_mem _ hm))
  | .ult _ _ :: fs, s, hp => applyFacts_den fs s (fun p hm => hp p (List.mem_cons_of_mem _ hm))
  | .uge _ _ :: fs, s, hp => applyFacts_den fs s (fun p hm => hp p (List.mem_cons_of_mem _ hm))

/-! ## Width-exact forwarding -/

/-- The bytes `[o, o + n)` of a stored word. -/
def fwdBytes (o n : Nat) (v : BitVec 64) : List (BitVec 8) :=
  (List.range n).map fun j => v.extractLsb' (8 * (o + j)) 8

/-- The value of a load of kind `k` at offset `o` inside a store of `v`. -/
def fwdV (k : MKind) (o : Nat) (v : BitVec 64) : BitVec 64 := bytesVal k (fwdBytes o (widthOfM k) v)

theorem byte_of_ext {w : Nat} (x : BitVec w) (v : BitVec 64) (j : Nat)
    (hx : x.toNat = v.toNat % 2 ^ w) (hj : 8 * j + 8 ≤ w) :
    x.extractLsb' (8 * j) 8 = v.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, hx]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have e : 2 ^ w = 2 ^ (8 * j) * 2 ^ (w - 8 * j) := by rw [← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact Nat.pow_dvd_pow 2 (by omega)

theorem getElem?_ins (m : Std.ExtHashMap Nat (BitVec 8)) (k a : Nat) (b : BitVec 8) :
    (m.insert k b)[a]? = if k = a then some b else m[a]? := by
  rw [Std.ExtHashMap.getElem?_insert]; simp only [beq_iff_eq]

theorem sx_toNat {n : Nat} (v : BitVec 64) (hn : n ≤ 64) (h1 : 1 ≤ n) :
    (Sail.BitVec.extractLsb v (n - 1) 0).toNat = v.toNat % 2 ^ (n - 1 - 0 + 1) := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat, Nat.shiftRight_zero]

theorem ins_eq (m : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (b : BitVec 8) :
    (m.insert k b)[k]? = some b := Std.ExtHashMap.getElem?_insert_self

theorem ins_ne (m : Std.ExtHashMap Nat (BitVec 8)) {k a : Nat} (b : BitVec 8) (h : k ≠ a) :
    (m.insert k b)[a]? = m[a]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simpa using h)]

theorem sb_byte (v : BitVec 64) : sbData v = v.extractLsb' (8 * 0) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [sbData, Sail.BitVec.extractLsb, BitVec.extractLsb_toNat, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, Nat.mul_zero]
  rfl

/-- A byte of a single store. -/
theorem imgM_store_byte (M : Mem) (A sw : Nat) (v : BitVec 64)
    (hw : sw = 1 ∨ sw = 2 ∨ sw = 4 ∨ sw = 8) {j : Nat} (hj : j < sw) :
    imgM (writeLog M [(A, sw, v)]) (A + j) = v.extractLsb' (8 * j) 8 := by
  unfold imgM writeLog
  simp only [List.foldl_cons, List.foldl_nil]
  rcases hw with rfl | rfl | rfl | rfl
  · obtain rfl : j = 0 := by omega
    simp only [applyW, Nat.add_zero, ins_eq, Option.getD_some]
    exact sb_byte v
  · simp only [applyW]
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · simp only [Nat.add_zero]; rw [ins_ne _ _ (by omega), ins_eq, Option.getD_some]
      exact byte_of_ext (w := 16) _ v 0 (sx_toNat (n := 16) v (by omega) (by omega)) (by omega)
    · rw [ins_eq, Option.getD_some]
      exact byte_of_ext (w := 16) _ v 1 (sx_toNat (n := 16) v (by omega) (by omega)) (by omega)
  · simp only [applyW, writeMap4]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
      (try simp only [Nat.add_zero]) <;>
      repeat (first | rw [ins_eq] | rw [ins_ne _ _ (by omega)])
    all_goals rw [Option.getD_some]
    · exact byte_of_ext (w := 32) _ v 0 (sx_toNat (n := 32) v (by omega) (by omega)) (by omega)
    · exact byte_of_ext (w := 32) _ v 1 (sx_toNat (n := 32) v (by omega) (by omega)) (by omega)
    · exact byte_of_ext (w := 32) _ v 2 (sx_toNat (n := 32) v (by omega) (by omega)) (by omega)
    · exact byte_of_ext (w := 32) _ v 3 (sx_toNat (n := 32) v (by omega) (by omega)) (by omega)
  · simp only [applyW, writeMap8]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (try simp only [Nat.add_zero]) <;>
      repeat (first | rw [ins_eq] | rw [ins_ne _ _ (by omega)])
    all_goals rw [Option.getD_some]
    · exact byte_of_ext (w := 64) _ v 0 (sx_toNat (n := 64) v (by omega) (by omega)) (by omega)
    · exact byte_of_ext (w := 64) _ v 1 (sx_toNat (n := 64) v (by omega) (by omega)) (by omega)
    · exact byte_of_ext (w := 64) _ v 2 (sx_toNat (n := 64) v (by omega) (by omega)) (by omega)
    · exact byte_of_ext (w := 64) _ v 3 (sx_toNat (n := 64) v (by omega) (by omega)) (by omega)
    · exact byte_of_ext (w := 64) _ v 4 (sx_toNat (n := 64) v (by omega) (by omega)) (by omega)
    · exact byte_of_ext (w := 64) _ v 5 (sx_toNat (n := 64) v (by omega) (by omega)) (by omega)
    · exact byte_of_ext (w := 64) _ v 6 (sx_toNat (n := 64) v (by omega) (by omega)) (by omega)
    · exact byte_of_ext (w := 64) _ v 7 (sx_toNat (n := 64) v (by omega) (by omega)) (by omega)

/-- A load inside one store reads the stored bytes. -/
theorem ldv_store_sub (k : MKind) (M : Mem) (A sw o : Nat) (v : BitVec 64)
    (hw : sw = 1 ∨ sw = 2 ∨ sw = 4 ∨ sw = 8) (ho : o + widthOfM k ≤ sw) :
    ldv k (writeLog M [(A, sw, v)]) (A + o) = fwdV k o v := by
  unfold ldv fwdV fwdBytes bytesAt
  congr 1
  refine List.map_congr_left fun j hj => ?_
  have := List.mem_range.mp hj
  rw [Nat.add_assoc]
  exact imgM_store_byte M A sw v hw (by omega)

def okW (sw : Nat) : Bool := sw == 1 || sw == 2 || sw == 4 || sw == 8

theorem okW_sound {sw : Nat} (h : okW sw = true) : sw = 1 ∨ sw = 2 ∨ sw = 4 ∨ sw = 8 := by
  simp only [okW, Bool.or_eq_true, beq_iff_eq] at h; omega

/-- The newest store a load of kind `k` at `a` overlaps, when the load lies inside it:
`(store address, offset, stored value, obligations)`. -/
def subHit (k : MKind) (a : SE) : SMem → Option (SE × Nat × SE × List SOb)
  | [] => none
  | (sa, sw, sv) :: t =>
    if (base a).1 = (base sa).1 then
      if ((base a).2 - (base sa).2).toNat + widthOfM k ≤ sw ∧ okW sw = true then
        some (sa, ((base a).2 - (base sa).2).toNat, sv,
          [.ldH sa (((base a).2 - (base sa).2).toNat + widthOfM k)])
      else if sepC (base a).2 (widthOfM k) (base sa).2 sw then subHit k a t else none
    else (subHit k a t).map fun r => (r.1, r.2.1, r.2.2.1, .disj a (widthOfM k) sa sw :: r.2.2.2)

theorem subHit_sound (ρ : Env) (S : Nat → Prop) (DA : List Nat) (k : MKind) (a : SE) :
    ∀ (M : SMem) (sa : SE) (o : Nat) (sv : SE) (obs : List SOb),
      subHit k a M = some (sa, o, sv, obs) → ObsOK ρ S DA obs →
      ldv k (memDen ρ M) (a.den ρ).toNat = fwdV k o (sv.den ρ)
  | [], _, _, _, _, h, _ => by cases h
  | (sa', sw, sv') :: t, sa, o, sv, obs, h, hob => by
    unfold subHit at h
    by_cases h1 : (base a).1 = (base sa').1
    · rw [if_pos h1] at h
      by_cases h2 : ((base a).2 - (base sa').2).toNat + widthOfM k ≤ sw ∧ okW sw = true
      · rw [if_pos h2] at h
        cases h
        have hl := hob _ List.mem_cons_self
        simp only [SOb.den, LdOK] at hl
        show ldv k (writeLog (memDen ρ t) [((sa'.den ρ).toNat, sw, sv'.den ρ)]) _ = _
        have e : (a.den ρ).toNat = (sa'.den ρ).toNat + ((base a).2 - (base sa').2).toNat := by
          rw [base_den ρ a, base_den ρ sa', h1]
          have e2 : (base sa').1.den ρ + (base a).2 =
              ((base sa').1.den ρ + (base sa').2) + ((base a).2 - (base sa').2) := by
            rw [BitVec.add_assoc, BitVec.add_comm (base sa').2, BitVec.sub_add_cancel]
          rw [e2, BitVec.toNat_add]
          rw [base_den ρ sa'] at hl
          exact Nat.mod_eq_of_lt (by omega)
        rw [e]
        exact ldv_store_sub k _ _ sw _ _ (okW_sound h2.2) h2.1
      · rw [if_neg h2] at h
        by_cases h3 : sepC (base a).2 (widthOfM k) (base sa').2 sw = true
        · rw [if_pos h3] at h
          rw [← subHit_sound ρ S DA k a t sa o sv obs h hob]
          show ldv k (writeLog (memDen ρ t) [((sa'.den ρ).toNat, sw, sv'.den ρ)]) _ = _
          rw [ldv_store_miss]
          have := sepC_sound (b := (base a).1.den ρ) h3
          rw [base_den ρ a, base_den ρ sa', ← h1]
          exact this
        · rw [if_neg h3] at h; cases h
    · rw [if_neg h1] at h
      cases hl : subHit k a t with
      | none => rw [hl] at h; cases h
      | some p =>
        rw [hl] at h
        obtain ⟨sa1, o1, sv1, obs1⟩ := p
        cases h
        rw [← subHit_sound ρ S DA k a t sa1 o1 sv1 obs1 hl (fun o ho => hob o (List.mem_cons_of_mem _ ho))]
        show ldv k (writeLog (memDen ρ t) [((sa'.den ρ).toNat, sw, sv'.den ρ)]) _ = _
        rw [ldv_store_miss]
        exact hob _ List.mem_cons_self

/-! ## The extended tree and executor -/

/-- Decode obligation of `jal ra, imm`. -/
def JalDec (w : BitVec 32) (imm : BitVec 21) : Prop :=
  ∀ σ, decodeN w σ = .ok (instruction.JAL (imm, regidx.Regidx 0x01#5)) σ

/-- `jal ra, imm21`. -/
def decJal (w : BitVec 32) : Option (BitVec 21) :=
  if (w.extractLsb' 0 7).toNat = 0x6f ∧ (w.extractLsb' 7 5).toNat = 1 then
    some ((((w.extractLsb' 31 1).append (w.extractLsb' 12 8)).append (w.extractLsb' 20 1)).append
      ((w.extractLsb' 21 10).append (0#1)))
  else none

inductive XTree where
  | leaf (s : SS) (pf : List PF)
  | br (pc : BitVec 64) (op : bop) (a b : SE) (obs : List SOb) (t f : XTree)
  /-- A decided branch: only the side taken. -/
  | brD (pc : BitVec 64) (obs : List SOb) (t : XTree)
  | jr (s : SS) (tgt : SE)
  | hv (i : Nat) (t : XTree)
  | raw (i : Nat) (k : MKind) (a : SE) (M : SMem) (t : XTree)
  /-- Slot `i` holds the bytes `[o, o + width k)` of `v`. -/
  | fwd (i : Nat) (k : MKind) (o : Nat) (v : SE) (t : XTree)
  /-- Case split: `e = j` continues with `t`, otherwise with `f`. -/
  | sel (e : SE) (j : Nat) (t f : XTree)
  /-- Unreachable by the path facts. -/
  | dead
  /-- A call `jal ra, imm` (word `w`): the run continues at the callee. -/
  | jal (w : BitVec 32) (imm : BitVec 21) (t : XTree)

/-- The residual weakest precondition; a leaf may assume its path facts. -/
def XTree.WP (ρ : Env) (S : Nat → Prop) (DA : List Nat)
    (K : BitVec 64 → (Nat → BitVec 64) → Mem → Prop) : XTree → Prop
  | .leaf s pf => ObsOK ρ S DA s.obs ∧ (PFOK ρ pf → K s.pc (regsDen ρ s.regs) (memDen ρ s.mem))
  | .br _ op a b obs t f => ObsOK ρ S DA obs ∧
      (guardB op (a.den ρ) (b.den ρ) = true → t.WP ρ S DA K) ∧
      (guardB op (a.den ρ) (b.den ρ) = false → f.WP ρ S DA K)
  | .brD _ obs t => ObsOK ρ S DA obs ∧ t.WP ρ S DA K
  | .jr s x => ObsOK ρ S DA s.obs ∧ K (x.den ρ) (regsDen ρ s.regs) (memDen ρ s.mem)
  | .hv i t => ∀ v, t.WP (ρ.withH i v) S DA K
  | .raw i k a M t => t.WP (ρ.withH i (ldv k (memDen ρ M) (a.den ρ).toNat)) S DA K
  | .fwd i k o v t => t.WP (ρ.withH i (fwdV k o (v.den ρ))) S DA K
  | .sel e j t f => ((e.den ρ).toNat = j → t.WP ρ S DA K) ∧ ((e.den ρ).toNat ≠ j → f.WP ρ S DA K)
  | .dead => True
  | .jal w imm t => JalDec w imm ∧ t.WP ρ S DA K

/-- The cases `j₀, j₀ + 1, …, j₀ + c - 1` of `e`. -/
def selChain (e : SE) (go : Nat → XTree) : Nat → Nat → XTree
  | _, 0 => .dead
  | j, c + 1 => .sel e j (go j) (selChain e go (j + 1) c)

theorem selChain_WP {ρ : Env} {S : Nat → Prop} {DA : List Nat}
    {K : BitVec 64 → (Nat → BitVec 64) → Mem → Prop} {e : SE} {go : Nat → XTree} :
    ∀ (c j : Nat), (selChain e go j c).WP ρ S DA K → j ≤ (e.den ρ).toNat →
      (e.den ρ).toNat < j + c → (go (e.den ρ).toNat).WP ρ S DA K
  | 0, _, _, h1, h2 => by omega
  | c + 1, j, h, h1, h2 => by
    by_cases hj : (e.den ρ).toNat = j
    · have := h.1 hj; rw [hj]; exact this
    · exact selChain_WP c (j + 1) (h.2 hj) (by omega) (by omega)

/-- Result of the extended step. -/
inductive XStepR where
  | base (r : StepR)
  /-- A load inside an earlier store of a constant: the next state. -/
  | fwdC (s : SS)
  /-- A load inside an earlier store of a symbolic value: slot `i`. -/
  | fwdS (i : Nat) (k : MKind) (o : Nat) (v : SE) (s : SS)
  /-- Split over the values `j < n` of `e`. -/
  | split (e : SE) (n : Nat)
  /-- A call `jal ra, imm`. -/
  | jal (w : BitVec 32) (imm : BitVec 21) (s : SS)

def pfMaxH (pf : List PF) : Nat := (pf.map PF.maxH).foldl max 0

def freshX (s : SS) (pf : List PF) : Nat := max (freshH s) (pfMaxH pf)

/-- Width-exact forwarding of a load that no other rule reads. -/
def fwdStep (C : Cfg) (s : SS) (pf : List PF) : Option XStepR :=
  let a := havocA C s
  let ea := eaS C.known a s.regs
  if (decodeM (wordAt C.img s.pc.toNat)).isSome = true ∧ isLoadK a.kind = true ∧ s.pc ∉ C.hv ∧
      s.pc ∉ C.rawpcs ∧ (symBody C a s.regs s.mem).isNone = true ∧
      lineChk C.img C.rT C.rs a = true then
    match subHit a.kind ea s.mem with
    | some (_, o, sv, obs) =>
      let obs' := .ld ea (widthOfM a.kind) :: obs ++ .decM s.pc (wordAt C.img s.pc.toNat) :: s.obs
      match sv with
      | .c v => some (.fwdC ⟨BitVec.addInt s.pc 4, (a.rd, .c (fwdV a.kind o v)) :: s.regs, s.mem, obs'⟩)
      | _ =>
        let i := freshX s pf
        if !regsHasH i s.regs && !memHasH i s.mem && !obsHasH i obs' && !ea.hasH i && !pfHasH i pf
        then some (.fwdS i a.kind o sv ⟨BitVec.addInt s.pc 4, (a.rd, .h i) :: s.regs, s.mem, obs'⟩)
        else none
    | none => none
  else none

/-- The values `j < n` of an atom with a fact `e <u n` for which the load address is constant
inside the code ranges. -/
def splitStep (C : Cfg) (s : SS) (pf : List PF) : Option XStepR :=
  let a := havocA C s
  let ea := eaS C.known a s.regs
  if (decodeM (wordAt C.img s.pc.toNat)).isSome = true ∧ isLoadK a.kind = true ∧ s.pc ∉ C.hv then
    match ea with
    | .c _ => none
    | _ => pf.findSome? fun p => match p with
      | .ult e n =>
        if 0 < n ∧ n ≤ 64 ∧ ((List.range n).all fun j =>
            match ea.sf e (.c (BitVec.ofNat 64 j)) with
            | .c v => imgOK C v (widthOfM a.kind)
            | _ => false) = true then some (.split e n) else none
      | _ => none
  else none

/-- The target of a call. -/
def jalTgt (pc : BitVec 64) (imm : BitVec 21) : BitVec 64 :=
  BitVec.ofNat 64 pc.toNat + sign_extend (m := 64) imm

def jalStep (C : Cfg) (s : SS) : Option XStepR :=
  match decJal (wordAt C.img s.pc.toNat) with
  | some imm =>
    if (jalChk s.pc.toNat (wordAt C.img s.pc.toNat) imm (jalTgt s.pc imm) &&
        C.hasB s.pc.toNat (wbytes (wordAt C.img s.pc.toNat)) && decide (VsaIris.ra ∈ C.rs)) = true then
      some (.jal (wordAt C.img s.pc.toNat) imm ⟨jalTgt s.pc imm,
        (VsaIris.ra, .c (BitVec.ofNat 64 (s.pc.toNat + 4))) :: s.regs, s.mem, s.obs⟩)
    else none
  | none => none

def symStepX (C : Cfg) (s : SS) (pf : List PF) : XStepR :=
  match havocStep C s with
  | some r => .base r
  | none =>
    match splitStep C s pf with
    | some r => r
    | none =>
      match fwdStep C s pf with
      | some r => r
      | none =>
        match jalStep C s with
        | some r => r
        | none => .base (symStep C s)

/-- A branch: decided sides continue with `go`; an undecided one forks, each side with the facts
its outcome implies. -/
def brRunX (K : List (Nat × BitVec 64)) (sub : Bool) (go fork : SS → List PF → XTree) (pc : BitVec 64)
    (op : bop) (a b : SE) (t f : SS) (pf : List PF) : XTree :=
  let x := opnd K pf a
  let y := opnd K pf b
  let t' : SS := { t with obs := [] }
  let f' : SS := { f with obs := [] }
  match brDecide pf op x y with
  | some true => .brD pc t.obs (go t' pf)
  | some false => .brD pc t.obs (go f' pf)
  | none =>
    .br pc op a b t.obs
      (fork (if sub then applyFacts t' (brFacts op x y true) else t')
        (brFacts op x y true ++ (lwFacts (brFacts op x y true) ++ pf)))
      (fork (if sub then applyFacts f' (brFacts op x y false) else f')
        (brFacts op x y false ++ (lwFacts (brFacts op x y false) ++ pf)))

def symRunX (C : Cfg) (sub : Bool) : Nat → SS → List PF → XTree
  | 0, s, pf => .leaf s pf
  | n + 1, s, pf =>
    if s.pc ∈ C.stops then .leaf s pf else
    match symStepX C s pf with
    | .fwdC s' => symRunX C sub n s' pf
    | .fwdS i k o v s' => .fwd i k o v (symRunX C sub n s' pf)
    | .split e m => selChain e (fun j => symRunX C sub n (s.sf e (.c (BitVec.ofNat 64 j))) pf) 0 m
    | .jal w imm s' => .jal w imm (symRunX C sub n s' pf)
    | .base r =>
      match r with
      | .next s' => symRunX C sub n s' pf
      | .br op a b t f =>
        brRunX C.known sub (symRunX C sub n)
          (fun s' pf' => if C.forkStop then .leaf s' pf' else symRunX C sub n s' pf') s.pc op a b t f pf
      | .jr s' x => .jr s' x
      | .hv i s' => if pfHasH i pf then .leaf s pf else .hv i (symRunX C sub n s' pf)
      | .raw i k a M s' => if pfHasH i pf then .leaf s pf else .raw i k a M (symRunX C sub n s' pf)
      | .stop => .leaf s pf

/-! ## Soundness -/

theorem splitStep_cases {C : Cfg} {s : SS} {pf : List PF} {r : XStepR}
    (h : splitStep C s pf = some r) : ∃ e n, r = .split e n ∧ PF.ult e n ∈ pf := by
  unfold splitStep at h
  simp only at h
  split at h
  · split at h
    · cases h
    · obtain ⟨p, hm, hp⟩ := List.exists_of_findSome?_eq_some h
      cases p with
      | ult e n =>
        simp only at hp
        split at hp
        · cases hp; exact ⟨e, n, rfl, hm⟩
        · cases hp
      | eq _ _ => simp at hp
      | ne _ _ => simp at hp
      | uge _ _ => simp at hp
  · cases h

/-- What a forwarding step established. -/
structure FwdFacts (C : Cfg) (s : SS) (o : Nat) (sv : SE) (obs' : List SOb) : Prop where
  dec : (decodeM (wordAt C.img s.pc.toNat)).isSome = true
  load : isLoadK (havocA C s).kind = true
  chk : lineChk C.img C.rT C.rs (havocA C s) = true
  hit : ∃ sa obs, subHit (havocA C s).kind (eaS C.known (havocA C s) s.regs) s.mem = some (sa, o, sv, obs) ∧
    obs' = .ld (eaS C.known (havocA C s) s.regs) (widthOfM (havocA C s).kind) :: obs ++
      .decM s.pc (wordAt C.img s.pc.toNat) :: s.obs

theorem fwdStep_cases {C : Cfg} {s : SS} {pf : List PF} {r : XStepR}
    (h : fwdStep C s pf = some r) :
    (∃ o v obs', FwdFacts C s o (.c v) obs' ∧
      r = .fwdC ⟨BitVec.addInt s.pc 4, ((havocA C s).rd, .c (fwdV (havocA C s).kind o v)) :: s.regs,
        s.mem, obs'⟩) ∨
    (∃ o sv obs', FwdFacts C s o sv obs' ∧ regsHasH (freshX s pf) s.regs = false ∧
      memHasH (freshX s pf) s.mem = false ∧ obsHasH (freshX s pf) obs' = false ∧
      (eaS C.known (havocA C s) s.regs).hasH (freshX s pf) = false ∧ pfHasH (freshX s pf) pf = false ∧
      r = .fwdS (freshX s pf) (havocA C s).kind o sv
        ⟨BitVec.addInt s.pc 4, ((havocA C s).rd, .h (freshX s pf)) :: s.regs, s.mem, obs'⟩) := by
  unfold fwdStep at h
  simp only at h
  split at h
  · rename_i hc
    obtain ⟨hd, hl, -, -, -, hchk⟩ := hc
    split at h
    · rename_i sa o sv obs hs
      split at h
      · rename_i v
        cases h
        exact .inl ⟨o, v, _, ⟨hd, hl, hchk, sa, obs, hs, rfl⟩, rfl⟩
      · split at h
        · rename_i hf
          cases h
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
          obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hf
          exact .inr ⟨o, sv, _, ⟨hd, hl, hchk, sa, obs, hs, rfl⟩, h1, h2, h3, h4, h5, rfl⟩
        · cases h
    · cases h
  · cases h

theorem jalStep_cases {C : Cfg} {s : SS} {r : XStepR} (h : jalStep C s = some r) :
    ∃ imm, decJal (wordAt C.img s.pc.toNat) = some imm ∧
      (jalChk s.pc.toNat (wordAt C.img s.pc.toNat) imm (jalTgt s.pc imm) &&
        C.hasB s.pc.toNat (wbytes (wordAt C.img s.pc.toNat)) && decide (VsaIris.ra ∈ C.rs)) = true ∧
      r = .jal (wordAt C.img s.pc.toNat) imm ⟨jalTgt s.pc imm,
        (VsaIris.ra, .c (BitVec.ofNat 64 (s.pc.toNat + 4))) :: s.regs, s.mem, s.obs⟩ := by
  unfold jalStep at h
  split at h
  · rename_i imm hd
    split at h
    · rename_i hc; cases h; exact ⟨imm, hd, hc, rfl⟩
    · cases h
  · cases h

theorem symStepX_base {C : Cfg} {s : SS} {pf : List PF} {r : StepR}
    (h : symStepX C s pf = .base r) : symStep C s = r := by
  unfold symStepX at h
  cases hh : havocStep C s with
  | some r0 => rw [hh] at h; cases h; unfold symStep; rw [hh]
  | none =>
    rw [hh] at h
    cases hs : splitStep C s pf with
    | some r1 =>
      rw [hs] at h; subst h
      obtain ⟨_, _, he, _⟩ := splitStep_cases hs; cases he
    | none =>
      rw [hs] at h
      cases hf : fwdStep C s pf with
      | some r1 =>
        rw [hf] at h; subst h
        rcases fwdStep_cases hf with ⟨_, _, _, _, he⟩ | ⟨_, _, _, _, _, _, _, _, _, he⟩ <;> cases he
      | none =>
        rw [hf] at h
        cases hj : jalStep C s with
        | some r1 =>
          rw [hj] at h; subst h
          obtain ⟨_, _, _, he⟩ := jalStep_cases hj; cases he
        | none => rw [hj] at h; injection h

theorem symStepX_cases {C : Cfg} {s : SS} {pf : List PF} {r : XStepR} (h : symStepX C s pf = r) :
    (∃ r0, r = .base r0 ∧ symStep C s = r0) ∨ splitStep C s pf = some r ∨ fwdStep C s pf = some r ∨
      jalStep C s = some r := by
  cases r with
  | base r0 => exact .inl ⟨r0, rfl, symStepX_base h⟩
  | _ =>
    unfold symStepX at h
    cases hh : havocStep C s with
    | some r0 => rw [hh] at h; cases h
    | none =>
      rw [hh] at h
      cases hs : splitStep C s pf with
      | some r1 => rw [hs] at h; subst h; exact .inr (.inl rfl)
      | none =>
        rw [hs] at h
        cases hf : fwdStep C s pf with
        | some r1 => rw [hf] at h; subst h; exact .inr (.inr (.inl rfl))
        | none =>
          rw [hf] at h
          cases hj : jalStep C s with
          | some r1 => rw [hj] at h; subst h; exact .inr (.inr (.inr rfl))
          | none => rw [hj] at h; cases h

theorem brRunX_WP {K : List (Nat × BitVec 64)} {sub : Bool} {go fork : SS → List PF → XTree} {pc : BitVec 64}
    {op : bop} {a b : SE} {t f : SS} {pf : List PF} {ρ : Env} {S : Nat → Prop} {DA : List Nat}
    {Kc : BitVec 64 → (Nat → BitVec 64) → Mem → Prop} {X : SS → Prop}
    (hK : KnownOK ρ K) (hp : PFOK ρ pf)
    (hgo : ∀ s pf', PFOK ρ pf' → (go s pf').WP ρ S DA Kc → X s)
    (hfork : ∀ s pf', PFOK ρ pf' → (fork s pf').WP ρ S DA Kc → X s)
    (hX : ∀ s fs, PFOK ρ fs → X (applyFacts s fs) → X s)
    (h : (brRunX K sub go fork pc op a b t f pf).WP ρ S DA Kc) :
    ObsOK ρ S DA t.obs ∧
    (guardB op (a.den ρ) (b.den ρ) = true → X { t with obs := [] }) ∧
    (guardB op (a.den ρ) (b.den ρ) = false → X { f with obs := [] }) := by
  have hx := opnd_den hK hp a
  have hy := opnd_den hK hp b
  unfold brRunX at h
  simp only at h
  split at h
  · rename_i hd
    have hg := brDecide_sound hp hd
    rw [hx, hy] at hg
    exact ⟨h.1, fun _ => hgo _ _ hp h.2, fun e => absurd (hg.symm.trans e) (by simp)⟩
  · rename_i hd
    have hg := brDecide_sound hp hd
    rw [hx, hy] at hg
    exact ⟨h.1, fun e => absurd (hg.symm.trans e) (by simp), fun _ => hgo _ _ hp h.2⟩
  · refine ⟨h.1, fun hg => ?_, fun hg => ?_⟩
    · have hf := brFacts_sound (x := opnd K pf a) (y := opnd K pf b) (op := op) (g := true)
        (by rw [hx, hy]; exact hg)
      have := hfork _ _ (pfok_append hf (pfok_append (lwFacts_sound hf) hp)) (h.2.1 hg)
      cases sub
      · exact this
      · exact hX _ _ hf this
    · have hf := brFacts_sound (x := opnd K pf a) (y := opnd K pf b) (op := op) (g := false)
        (by rw [hx, hy]; exact hg)
      have := hfork _ _ (pfok_append hf (pfok_append (lwFacts_sound hf) hp)) (h.2.2 hg)
      cases sub
      · exact this
      · exact hX _ _ hf this

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt x.isLt

theorem sf_split_den {ρ : Env} {e : SE} {j : Nat} (hj : (e.den ρ).toNat = j) (s : SS) :
    regsDen ρ (s.sf e (.c (BitVec.ofNat 64 j))).regs = regsDen ρ s.regs ∧
    memDen ρ (s.sf e (.c (BitVec.ofNat 64 j))).mem = memDen ρ s.mem := by
  have h : e.den ρ = (SE.c (BitVec.ofNat 64 j)).den ρ := by
    show e.den ρ = BitVec.ofNat 64 j; rw [← hj, ofNat_toNat64]
  exact ⟨regsSF_den ρ h s.regs, memSF_den ρ h s.mem⟩

theorem symRunX_obs (C : Cfg) (sub : Bool) (S : Nat → Prop) (DA : List Nat) (Kc) :
    ∀ (ρ : Env) (n : Nat) (s : SS) (pf : List PF), KnownOK ρ C.known → PFOK ρ pf →
      (symRunX C sub n s pf).WP ρ S DA Kc → ObsOK ρ S DA s.obs
  | _, 0, s, _, _, _, h => h.1
  | ρ, n + 1, s, pf, hK, hp, h => by
    unfold symRunX at h
    by_cases hs : s.pc ∈ C.stops
    · rw [if_pos hs] at h; exact h.1
    · rw [if_neg hs] at h
      cases hst : symStepX C s pf with
      | fwdC s' =>
        rw [hst] at h
        rcases symStepX_cases hst with ⟨_, h', _⟩ | h' | h' | h'
        · cases h'
        · obtain ⟨_, _, h'', _⟩ := splitStep_cases h'; cases h''
        · rcases fwdStep_cases h' with ⟨o, v, obs', F, he⟩ | ⟨_, _, _, _, _, _, _, _, _, he⟩
          · cases he
            obtain ⟨_, _, _, rfl⟩ := F.hit
            intro x hx
            exact symRunX_obs C sub S DA Kc ρ n _ pf hK hp h x
              (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hx)))
          · cases he
        · obtain ⟨_, _, _, he⟩ := jalStep_cases h'; cases he
      | fwdS i k o v s' =>
        rw [hst] at h
        rcases symStepX_cases hst with ⟨_, h', _⟩ | h' | h' | h'
        · cases h'
        · obtain ⟨_, _, h'', _⟩ := splitStep_cases h'; cases h''
        · rcases fwdStep_cases h' with ⟨_, _, _, _, he⟩ | ⟨o', sv, obs', F, hR, hM, hO, hE, hP, he⟩
          · cases he
          · cases he
            obtain ⟨_, _, _, rfl⟩ := F.hit
            have h0 := symRunX_obs C sub S DA Kc
              (ρ.withH (freshX s pf) (fwdV (havocA C s).kind o (v.den ρ))) n _ pf
              (fun p hp' => hK p hp') (pfok_withH hP hp) h
            have h1 := obsOK_withH hO h0
            intro x hx
            exact h1 x (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hx)))
        · obtain ⟨_, _, _, he⟩ := jalStep_cases h'; cases he
      | split e m =>
        rw [hst] at h
        rcases symStepX_cases hst with ⟨_, h', _⟩ | h' | h' | h'
        · cases h'
        · obtain ⟨e', m', he, hm⟩ := splitStep_cases h'
          cases he
          have hb : (e.den ρ).toNat < m := hp _ hm
          have hc := selChain_WP m 0 h (Nat.zero_le _) (by omega)
          exact symRunX_obs C sub S DA Kc ρ n (s.sf e (.c (BitVec.ofNat 64 (e.den ρ).toNat))) pf hK hp hc
        · rcases fwdStep_cases h' with ⟨_, _, _, _, he⟩ | ⟨_, _, _, _, _, _, _, _, _, he⟩ <;> cases he
        · obtain ⟨_, _, _, he⟩ := jalStep_cases h'; cases he
      | jal w imm s' =>
        rw [hst] at h
        rcases symStepX_cases hst with ⟨_, h', _⟩ | h' | h' | h'
        · cases h'
        · obtain ⟨_, _, h'', _⟩ := splitStep_cases h'; cases h''
        · rcases fwdStep_cases h' with ⟨_, _, _, _, he⟩ | ⟨_, _, _, _, _, _, _, _, _, he⟩ <;> cases he
        · obtain ⟨imm', -, -, he⟩ := jalStep_cases h'
          cases he
          exact symRunX_obs C sub S DA Kc ρ n ⟨jalTgt s.pc imm,
            (VsaIris.ra, .c (BitVec.ofNat 64 (s.pc.toNat + 4))) :: s.regs, s.mem, s.obs⟩ pf hK hp h.2
      | base r =>
        rw [hst] at h
        have hs0 := symStepX_base hst
        cases r with
        | stop => exact h.1
        | next s' =>
          intro o ho
          exact symRunX_obs C sub S DA Kc ρ n s' pf hK hp h o (symStep_obs C s hs0 o ho)
        | jr s' x =>
          intro o ho
          exact h.1 o (symStep_jr_obs C s hs0 o ho)
        | br op a b t f =>
          replace h := brRunX_WP (X := fun _ => True) hK hp (fun _ _ _ _ => trivial)
            (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) h
          obtain ⟨ht, -⟩ := symStep_br_obs C s hs0
          exact fun o ho => h.1 o (ht o ho)
        | hv i s' =>
          obtain ⟨-, hok, rfl, rfl⟩ := symStep_hv hs0
          simp only at h
          split at h
          · exact h.1
          · rename_i hP
            obtain ⟨hf, hsub⟩ := havoc_obs hok
            have h0 := symRunX_obs C sub S DA Kc (ρ.withH (freshH s) 0) n _ pf (fun p hp' => hK p hp')
              (pfok_withH (by simpa using hP) hp) (h 0)
            exact obsOK_withH hf (fun o ho => h0 o (hsub o ho))
        | raw i k a M s' =>
          obtain ⟨-, hok, rfl, rfl, rfl, rfl, rfl⟩ := symStep_raw hs0
          simp only at h
          split at h
          · exact h.1
          · rename_i hP
            obtain ⟨hf, hsub⟩ := raw_obs hok
            have h0 := symRunX_obs C sub S DA Kc
              (ρ.withH (freshH s) (ldv (havocA C s).kind (memDen ρ s.mem)
                ((eaS C.known (havocA C s) s.regs).den ρ).toNat)) n _ pf (fun p hp' => hK p hp')
              (pfok_withH (by simpa using hP) hp) h
            exact obsOK_withH hf (fun o ho => h0 o (hsub o ho))

section runX
variable {live : Nat → Prop} {T : List (Nat × BitVec 8)} {S : Nat → Prop} {Dt : Mem}
  {DA : List Nat} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- An owned load whose value is given: the ordinary owned-load rule. -/
theorem load_sound (C : Cfg) (hc : CodeAt T C.img C.rT) (hlive : ∀ p ∈ T, live p.1)
    (hPC : VsaIris.PC ∈ C.rs) (hgprs : gp ∉ C.rs) (ρ : Env) (hK : KnownOK ρ C.known) (s : SS)
    (hchk : lineChk C.img C.rT C.rs (havocA C s) = true) (hl : isLoadK (havocA C s).kind = true)
    (hea : (SOb.ld (eaS C.known (havocA C s) s.regs) (widthOfM (havocA C s).kind)).den ρ S DA)
    (hdec : DecM (havocA C s)) (v : BitVec 64)
    (hv : v = ldv (havocA C s).kind (memDen ρ s.mem) ((eaS C.known (havocA C s) s.regs).den ρ).toNat)
    (hk : SWP live (T ++ dataOf Dt DA) C.rs S Q (BitVec.addInt s.pc 4)
      (upd (regsDen ρ s.regs) (havocA C s).rd v) (memDen ρ s.mem)) :
    SWP live (T ++ dataOf Dt DA) C.rs S Q s.pc (regsDen ρ s.regs) (memDen ρ s.mem) := by
  have hline := LineOK.of_chk hchk
  have hst := not_store_of_load hl
  have hp : (havocA C s).pc = s.pc := (mkLine_fields s.pc (wordAt C.img s.pc.toNat)).1
  have hea0 := hea
  simp only [SOb.den] at hea0
  have he := eaddrM_eq ρ hK (L := s.regs) (rs1_mem (havocA C s))
  rw [← he] at hea0
  have := swpx_line (T := T) (D := dataOf Dt DA) (rs := C.rs) (S := S) (Q := Q) C.img C.rT hc
    (havocA C s) (R := regsDen ρ s.regs) (Mt := memDen ρ s.mem) (lineKs (havocA C s))
    [bytesAt (imgM (memDen ρ s.mem))
      (eaddrM (havocA C s) (pinsOf (lineKs (havocA C s)) (regsDen ρ s.regs))).toNat
      (widthOfM (havocA C s).kind)]
    (accAddrs (eaddrM (havocA C s) (pinsOf (lineKs (havocA C s)) (regsDen ρ s.regs))).toNat
      (widthOfM (havocA C s).kind)) []
    hline.wf hline.keys hline.wr (fun b _ => by rw [hst]; trivial) hlive hline.pins hdec
    (fun m _ _ hp => memFacts_load hl hea0.1 hp) hPC hline.regs hline.nogp hgprs hea0.2
    (fun _ h => by cases h)
    (fun x _ _ hx => by
      rw [lineR_nonstore hst]
      refine upd_other _ _ (fun e => hx ?_)
      exact e ▸ hline.wr _ (by rw [wrChain_nonstore hst]; exact List.mem_singleton_self _))
    (by
      rw [lineR_nonstore hst, wvalM_load hl, hst, he, hp]
      show SWP _ _ _ _ _ _ (upd _ _ (ldv (havocA C s).kind (memDen ρ s.mem)
        ((eaS C.known (havocA C s) s.regs).den ρ).toNat)) (writeLog (memDen ρ s.mem) [])
      rw [← hv]; exact hk)
  rwa [hp] at this

/-- **Soundness of the extended executor.** -/
theorem symRunX_swp (C : Cfg) (sub : Bool) (hc : CodeAt T C.img C.rT)
    (hmem : ∀ i code, C.hasB i code = true → ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ T)
    (hlive : ∀ p ∈ T, live p.1)
    (hPC : VsaIris.PC ∈ C.rs) (hgprs : gp ∉ C.rs) (R0 : Nat → BitVec 64) (M0 : Mem)
    (hkv : ∀ H, ∀ e ∈ C.kv, ldv e.1 Dt (e.2.1.den ⟨R0, M0, Dt, H⟩).toNat = e.2.2)
    (hkm : ∀ H, ∀ e ∈ C.kvM, ldv e.1 M0 (e.2.1.den ⟨R0, M0, Dt, H⟩).toNat = e.2.2)
    (hK : ∀ p ∈ C.known, R0 p.1 = p.2) :
    ∀ (H : Nat → BitVec 64) (n : Nat) (s : SS) (pf : List PF), PFOK ⟨R0, M0, Dt, H⟩ pf →
      (symRunX C sub n s pf).WP ⟨R0, M0, Dt, H⟩ S DA
        (fun pc R M => SWP live (T ++ dataOf Dt DA) C.rs S Q pc R M) →
      SWP live (T ++ dataOf Dt DA) C.rs S Q s.pc (regsDen ⟨R0, M0, Dt, H⟩ s.regs)
        (memDen ⟨R0, M0, Dt, H⟩ s.mem)
  | _, 0, s, _, hp, h => h.2 hp
  | H, n + 1, s, pf, hp, h => by
    have hKo : KnownOK ⟨R0, M0, Dt, H⟩ C.known := hK
    have hsnd := symStep0_sound (S := S) (DA := DA) (Q := Q) C hc hlive hPC hgprs
      ⟨R0, M0, Dt, H⟩ rfl (hkv H) (hkm H) hK s
    have hobs := symRunX_obs C sub S DA _ ⟨R0, M0, Dt, H⟩ (n + 1) s pf hKo hp h
    unfold symRunX at h
    by_cases hs : s.pc ∈ C.stops
    · rw [if_pos hs] at h; exact h.2 hp
    · rw [if_neg hs] at h
      cases hst : symStepX C s pf with
      | fwdC s' =>
        rw [hst] at h
        rcases symStepX_cases hst with ⟨_, h', _⟩ | h' | h' | h'
        · cases h'
        · obtain ⟨_, _, h'', _⟩ := splitStep_cases h'; cases h''
        · rcases fwdStep_cases h' with ⟨o, v, obs', F, he⟩ | ⟨_, _, _, _, _, _, _, _, _, he⟩
          · cases he
            obtain ⟨sa, obs, hsh, rfl⟩ := F.hit
            have hob := symRunX_obs C sub S DA _ _ n _ pf hKo hp h
            have hsw := symRunX_swp C sub hc hmem hlive hPC hgprs R0 M0 hkv hkm hK H n _ pf hp h
            refine load_sound C hc hlive hPC hgprs _ hKo s F.chk F.load (hob _ List.mem_cons_self)
              (hob _ (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)))
              (fwdV (havocA C s).kind o v) ?_ hsw
            exact (subHit_sound _ S DA _ _ s.mem sa o (.c v) obs hsh
              (fun x hx => hob x (List.mem_cons_of_mem _ (List.mem_append_left _ hx)))).symm
          · cases he
        · obtain ⟨_, _, _, he⟩ := jalStep_cases h'; cases he
      | fwdS i k o v s' =>
        rw [hst] at h
        rcases symStepX_cases hst with ⟨_, h', _⟩ | h' | h' | h'
        · cases h'
        · obtain ⟨_, _, h'', _⟩ := splitStep_cases h'; cases h''
        · rcases fwdStep_cases h' with ⟨_, _, _, _, he⟩ | ⟨o', sv, obs', F, hR, hM, hO, hE, hP, he⟩
          · cases he
          · cases he
            obtain ⟨sa, obs, hsh, rfl⟩ := F.hit
            have hp' := pfok_withH (v := fwdV (havocA C s).kind o (v.den ⟨R0, M0, Dt, H⟩)) hP hp
            have hob0 := symRunX_obs C sub S DA _ _ n _ pf (fun p hp'' => hK p hp'') hp' h
            have hob := obsOK_withH hO hob0
            have hsw := symRunX_swp C sub hc hmem hlive hPC hgprs R0 M0 hkv hkm hK _ n _ pf hp' h
            refine load_sound C hc hlive hPC hgprs _ hKo s F.chk F.load (hob _ List.mem_cons_self)
              (hob _ (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)))
              (fwdV (havocA C s).kind o (v.den ⟨R0, M0, Dt, H⟩)) ?_ ?_
            · exact (subHit_sound _ S DA _ _ s.mem sa o v obs hsh
                (fun x hx => hob x (List.mem_cons_of_mem _ (List.mem_append_left _ hx)))).symm
            · have e1 : regsDen ⟨R0, M0, Dt, hset H (freshX s pf)
                  (fwdV (havocA C s).kind o (v.den ⟨R0, M0, Dt, H⟩))⟩
                  (((havocA C s).rd, SE.h (freshX s pf)) :: s.regs) =
                  upd (regsDen ⟨R0, M0, Dt, H⟩ s.regs) (havocA C s).rd
                    (fwdV (havocA C s).kind o (v.den ⟨R0, M0, Dt, H⟩)) := by
                show upd (regsDen ⟨R0, M0, Dt, hset H (freshX s pf) _⟩ s.regs) _
                  (hset H (freshX s pf) _ (freshX s pf)) = _
                rw [hset_self]
                congr 1
                exact regsDen_withH ⟨R0, M0, Dt, H⟩ _ _ _ hR
              have e2 : memDen ⟨R0, M0, Dt, hset H (freshX s pf)
                  (fwdV (havocA C s).kind o (v.den ⟨R0, M0, Dt, H⟩))⟩ s.mem = memDen ⟨R0, M0, Dt, H⟩ s.mem :=
                memDen_withH ⟨R0, M0, Dt, H⟩ _ _ s.mem hM
              rw [e1, e2] at hsw
              exact hsw
        · obtain ⟨_, _, _, he⟩ := jalStep_cases h'; cases he
      | split e m =>
        rw [hst] at h
        rcases symStepX_cases hst with ⟨_, h', _⟩ | h' | h' | h'
        · cases h'
        · obtain ⟨e', m', he, hm⟩ := splitStep_cases h'
          cases he
          have hb : (e.den ⟨R0, M0, Dt, H⟩).toNat < m := hp _ hm
          have hc' := selChain_WP m 0 h (Nat.zero_le _) (by omega)
          have hsw := symRunX_swp C sub hc hmem hlive hPC hgprs R0 M0 hkv hkm hK H n _ pf hp hc'
          obtain ⟨e1, e2⟩ := sf_split_den (ρ := ⟨R0, M0, Dt, H⟩) (e := e) rfl s
          rw [e1, e2] at hsw
          exact hsw
        · rcases fwdStep_cases h' with ⟨_, _, _, _, he⟩ | ⟨_, _, _, _, _, _, _, _, _, he⟩ <;> cases he
        · obtain ⟨_, _, _, he⟩ := jalStep_cases h'; cases he
      | jal w imm s' =>
        rw [hst] at h
        rcases symStepX_cases hst with ⟨_, h', _⟩ | h' | h' | h'
        · cases h'
        · obtain ⟨_, _, h'', _⟩ := splitStep_cases h'; cases h''
        · rcases fwdStep_cases h' with ⟨_, _, _, _, he⟩ | ⟨_, _, _, _, _, _, _, _, _, he⟩ <;> cases he
        · obtain ⟨imm', hd, hc', he⟩ := jalStep_cases h'
          cases he
          have hsw := symRunX_swp C sub hc hmem hlive hPC hgprs R0 M0 hkv hkm hK H n _ pf hp h.2
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
          obtain ⟨⟨hj, hb⟩, hra⟩ := hc'
          have hfoot := hmem _ _ hb
          refine swp_jal s.pc.toNat (wbytes (wordAt C.img s.pc.toNat)) (jalTgt s.pc imm)
            (jalExec_word s.pc.toNat _ imm _ hj h.1 live (fun p hp' => hlive _ (hfoot p hp')))
            (fun p hp' => List.mem_append_left _ (hfoot p hp')) hPC hra (ofNat_toNat64 s.pc).symm ?_
          exact hsw
      | base r =>
        rw [hst] at h
        have hs0 := symStepX_base hst
        cases r with
        | stop => exact h.2 hp
        | next s' =>
          have hob := symRunX_obs C sub S DA _ _ n s' pf hKo hp h
          have hsw := symRunX_swp C sub hc hmem hlive hPC hgprs R0 M0 hkv hkm hK H n s' pf hp h
          rcases symStep_next hs0 with ⟨sltu, rd, rs1, rs2, imm, hok, rfl⟩ | hst0
          · exact obs_sound C hmem hlive hPC hgprs ⟨R0, M0, Dt, H⟩ hK s sltu rd rs1 rs2 imm hok
              (hob _ List.mem_cons_self) hsw
          · exact hsnd.1 s' hst0 hob hsw
        | jr s' x =>
          exact hsnd.2.2 s' x (symStep_not_havoc hs0 (fun _ _ => nofun) (fun _ _ _ _ _ => nofun)
            (fun _ => nofun) nofun) h.1 h.2
        | br op a b t f =>
          obtain ⟨hob, h1, h2⟩ := brRunX_WP
            (X := fun s' => SWP live (T ++ dataOf Dt DA) C.rs S Q s'.pc
              (regsDen ⟨R0, M0, Dt, H⟩ s'.regs) (memDen ⟨R0, M0, Dt, H⟩ s'.mem)) hKo hp
            (fun s' pf' hp' hs' => symRunX_swp C sub hc hmem hlive hPC hgprs R0 M0 hkv hkm hK H n s' pf'
              hp' hs')
            (fun s' pf' hp' hs' => by
              by_cases hfs : C.forkStop = true
              · rw [if_pos hfs] at hs'; exact hs'.2 hp'
              · rw [if_neg hfs] at hs'
                exact symRunX_swp C sub hc hmem hlive hPC hgprs R0 M0 hkv hkm hK H n s' pf' hp' hs')
            (fun s' fs hf hX' => by
              obtain ⟨e1, -, e3, e4⟩ := applyFacts_den fs s' hf
              rw [e1, e3, e4] at hX'; exact hX') h
          have hsame := symStep_br_same C s hs0
          exact hsnd.2.1 op a b t f (symStep_not_havoc hs0 (fun _ _ => nofun)
            (fun _ _ _ _ _ => nofun) (fun _ => nofun) nofun)
            (fun hg => ⟨hob, h1 hg⟩) (fun hg => ⟨hsame ▸ hob, h2 hg⟩)
        | hv i s' =>
          obtain ⟨hl, hok, rfl, rfl⟩ := symStep_hv hs0
          simp only at h
          split at h
          · exact h.2 hp
          · rename_i hP
            have hP' : pfHasH (freshH s) pf = false := by simpa using hP
            exact havoc_sound C hc hlive hPC hgprs ⟨R0, M0, Dt, H⟩ hK s hok hl
              (symRunX_obs C sub S DA _ _ n _ pf (fun p hp'' => hK p hp'') (pfok_withH hP' hp) (h 0))
              (fun v => symRunX_swp C sub hc hmem hlive hPC hgprs R0 M0 hkv hkm hK (hset H (freshH s) v) n _ pf
                (pfok_withH hP' hp) (h v))
        | raw i k a M s' =>
          obtain ⟨hl, hok, rfl, rfl, rfl, rfl, rfl⟩ := symStep_raw hs0
          simp only at h
          split at h
          · exact h.2 hp
          · rename_i hP
            have hP' : pfHasH (freshH s) pf = false := by simpa using hP
            exact raw_sound C hc hlive hPC hgprs ⟨R0, M0, Dt, H⟩ hK s hok hl
              (symRunX_obs C sub S DA _ _ n _ pf (fun p hp'' => hK p hp'') (pfok_withH hP' hp) h)
              (symRunX_swp C sub hc hmem hlive hPC hgprs R0 M0 hkv hkm hK _ n _ pf (pfok_withH hP' hp) h)

end runX

/-! ## Pruning and the segment form -/

def XTree.prune (Γ : Geom) : XTree → XTree
  | .leaf s pf => .leaf { s with obs := s.obs.filter fun o => !obCheck Γ o } pf
  | .br pc op a b obs t f =>
    .br pc op a b (obs.filter fun o => !obCheck Γ o) (t.prune Γ) (f.prune Γ)
  | .brD pc obs t => .brD pc (obs.filter fun o => !obCheck Γ o) (t.prune Γ)
  | .jr s x => .jr { s with obs := s.obs.filter fun o => !obCheck Γ o } x
  | .hv i t => .hv i (t.prune Γ)
  | .raw i k a M t => .raw i k a M (t.prune Γ)
  | .fwd i k o v t => .fwd i k o v (t.prune Γ)
  | .sel e j t f => .sel e j (t.prune Γ) (f.prune Γ)
  | .dead => .dead
  | .jal w imm t => .jal w imm (t.prune Γ)

theorem obsOK_of_filter {ρ : Env} {S : Nat → Prop} {DA : List Nat} {Γ : Geom}
    (hΓ : Γ.holds ρ S DA) {obs : List SOb} (h : ObsOK ρ S DA (obs.filter fun o => !obCheck Γ o)) :
    ObsOK ρ S DA obs := by
  intro o ho
  cases hc : obCheck Γ o
  · exact h o (List.mem_filter.2 ⟨ho, by simp [hc]⟩)
  · exact obCheck_sound hΓ o hc

theorem XTree.WP_of_prune {R0 : Nat → BitVec 64} {M0 D0 : Mem} {S : Nat → Prop} {DA : List Nat}
    {Γ : Geom} (hΓ : ∀ H, Γ.holds ⟨R0, M0, D0, H⟩ S DA)
    {K : BitVec 64 → (Nat → BitVec 64) → Mem → Prop} :
    ∀ (T : XTree) (H : Nat → BitVec 64), (T.prune Γ).WP ⟨R0, M0, D0, H⟩ S DA K →
      T.WP ⟨R0, M0, D0, H⟩ S DA K
  | .leaf _ _, H, h => ⟨obsOK_of_filter (hΓ H) h.1, h.2⟩
  | .br _ _ _ _ _ t f, H, h => ⟨obsOK_of_filter (hΓ H) h.1,
      fun hg => XTree.WP_of_prune hΓ t H (h.2.1 hg), fun hg => XTree.WP_of_prune hΓ f H (h.2.2 hg)⟩
  | .brD _ _ t, H, h => ⟨obsOK_of_filter (hΓ H) h.1, XTree.WP_of_prune hΓ t H h.2⟩
  | .jr _ _, H, h => ⟨obsOK_of_filter (hΓ H) h.1, h.2⟩
  | .hv i t, H, h => fun v => XTree.WP_of_prune hΓ t (hset H i v) (h v)
  | .raw _ _ _ _ t, H, h => XTree.WP_of_prune hΓ t (hset H _ _) h
  | .fwd _ _ _ _ t, H, h => XTree.WP_of_prune hΓ t (hset H _ _) h
  | .sel _ _ t f, H, h =>
    ⟨fun hj => XTree.WP_of_prune hΓ t H (h.1 hj), fun hj => XTree.WP_of_prune hΓ f H (h.2 hj)⟩
  | .dead, _, _ => trivial
  | .jal _ _ t, H, h => ⟨h.1, XTree.WP_of_prune hΓ t H h.2⟩

section contX
variable {live : Nat → Prop} {T : List (Nat × BitVec 8)} {S : Nat → Prop} {Dt : Mem}
  {DA : List Nat} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- One segment of an extended run from any symbolic state with true path facts. -/
theorem symRunX_cont {C : Cfg} (sub : Bool) {R0 : Nat → BitVec 64} {M0 : Mem}
    (hX : RunCtx live T Dt C R0 M0) (Γ : Geom)
    (hΓn : Γ.all (fun f => f.atom.noHv) = true)
    (hΓ : Γ.holds ⟨R0, M0, Dt, fun _ => 0⟩ S DA) (n : Nat) (ρ : Env)
    (hR : ρ.R0 = R0) (hM : ρ.M0 = M0) (hD : ρ.D0 = Dt) (s : SS) (pf : List PF)
    (hp : PFOK ρ pf)
    (h : ((symRunX C sub n s pf).prune Γ).WP ρ S DA
      (fun pc R M => SWP live (T ++ dataOf Dt DA) C.rs S Q pc R M)) :
    SWP live (T ++ dataOf Dt DA) C.rs S Q s.pc (regsDen ρ s.regs) (memDen ρ s.mem) := by
  obtain ⟨R, M, D, H⟩ := ρ
  cases hR; cases hM; cases hD
  exact symRunX_swp C sub hX.code hX.text hX.live hX.pc hX.gp R M
    (fun H e he => by
      rw [SE.den_noHv R M D H (fun _ => 0) e.2.1
        (List.all_eq_true.1 hX.kvn e (List.mem_append_left _ he))]
      exact hX.kv e he)
    (fun H e he => by
      rw [SE.den_noHv R M D H (fun _ => 0) e.2.1
        (List.all_eq_true.1 hX.kvn e (List.mem_append_right _ he))]
      exact hX.kvM e he)
    hX.known H n s pf hp (XTree.WP_of_prune (fun _ => Geom.holds_noHv hΓn hΓ) _ _ h)

/-- A run of a text without a data view, as a run with the empty one. -/
theorem swp_noData {rs : List Nat} {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (h : SWP live (T ++ dataOf ∅ []) rs S Q pc R Mt) : SWP live T rs S Q pc R Mt := by
  simpa [dataOf] using h

theorem swp_ofNoData {rs : List Nat} {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (h : SWP live T rs S Q pc R Mt) : SWP live (T ++ dataOf ∅ []) rs S Q pc R Mt := by
  simpa [dataOf] using h

end contX

theorem XTree.WP_leaf {ρ : Env} {S : Nat → Prop} {DA : List Nat}
    {K : BitVec 64 → (Nat → BitVec 64) → Mem → Prop} {s : SS} {pf : List PF}
    (h1 : ObsOK ρ S DA s.obs) (h2 : PFOK ρ pf → K s.pc (regsDen ρ s.regs) (memDen ρ s.mem)) :
    (XTree.leaf s pf).WP ρ S DA K := ⟨h1, h2⟩

theorem XTree.WP_br {ρ : Env} {S : Nat → Prop} {DA : List Nat}
    {K : BitVec 64 → (Nat → BitVec 64) → Mem → Prop} {pc : BitVec 64} {op : bop} {a b : SE}
    {t f : XTree} {obs : List SOb} (h0 : ObsOK ρ S DA obs)
    (h1 : guardB op (a.den ρ) (b.den ρ) = true → t.WP ρ S DA K)
    (h2 : guardB op (a.den ρ) (b.den ρ) = false → f.WP ρ S DA K) :
    (XTree.br pc op a b obs t f).WP ρ S DA K := ⟨h0, h1, h2⟩

theorem XTree.WP_brD {ρ : Env} {S : Nat → Prop} {DA : List Nat}
    {K : BitVec 64 → (Nat → BitVec 64) → Mem → Prop} {pc : BitVec 64} {t : XTree}
    {obs : List SOb} (h0 : ObsOK ρ S DA obs) (h1 : t.WP ρ S DA K) :
    (XTree.brD pc obs t).WP ρ S DA K := ⟨h0, h1⟩

theorem XTree.WP_jr {ρ : Env} {S : Nat → Prop} {DA : List Nat}
    {K : BitVec 64 → (Nat → BitVec 64) → Mem → Prop} {s : SS} {x : SE} (h1 : ObsOK ρ S DA s.obs)
    (h2 : K (x.den ρ) (regsDen ρ s.regs) (memDen ρ s.mem)) : (XTree.jr s x).WP ρ S DA K := ⟨h1, h2⟩

theorem XTree.WP_hv {ρ : Env} {S : Nat → Prop} {DA : List Nat}
    {K : BitVec 64 → (Nat → BitVec 64) → Mem → Prop} {i : Nat} {t : XTree}
    (h : ∀ v, t.WP (ρ.withH i v) S DA K) : (XTree.hv i t).WP ρ S DA K := h

theorem XTree.WP_raw {ρ : Env} {S : Nat → Prop} {DA : List Nat}
    {K : BitVec 64 → (Nat → BitVec 64) → Mem → Prop} {i : Nat} {k : MKind} {a : SE} {M : SMem}
    {t : XTree} (h : t.WP (ρ.withH i (ldv k (memDen ρ M) (a.den ρ).toNat)) S DA K) :
    (XTree.raw i k a M t).WP ρ S DA K := h

theorem XTree.WP_fwd {ρ : Env} {S : Nat → Prop} {DA : List Nat}
    {K : BitVec 64 → (Nat → BitVec 64) → Mem → Prop} {i : Nat} {k : MKind} {o : Nat} {v : SE}
    {t : XTree} (h : t.WP (ρ.withH i (fwdV k o (v.den ρ))) S DA K) :
    (XTree.fwd i k o v t).WP ρ S DA K := h

theorem XTree.WP_sel {ρ : Env} {S : Nat → Prop} {DA : List Nat}
    {K : BitVec 64 → (Nat → BitVec 64) → Mem → Prop} {e : SE} {j : Nat} {t f : XTree}
    (h1 : (e.den ρ).toNat = j → t.WP ρ S DA K) (h2 : (e.den ρ).toNat ≠ j → f.WP ρ S DA K) :
    (XTree.sel e j t f).WP ρ S DA K := ⟨h1, h2⟩

theorem XTree.WP_dead {ρ : Env} {S : Nat → Prop} {DA : List Nat}
    {K : BitVec 64 → (Nat → BitVec 64) → Mem → Prop} : XTree.dead.WP ρ S DA K := trivial

theorem XTree.WP_jal {ρ : Env} {S : Nat → Prop} {DA : List Nat}
    {K : BitVec 64 → (Nat → BitVec 64) → Mem → Prop} {w : BitVec 32} {imm : BitVec 21} {t : XTree}
    (h1 : JalDec w imm) (h2 : t.WP ρ S DA K) : (XTree.jal w imm t).WP ρ S DA K := ⟨h1, h2⟩

open Lean Meta Elab Tactic in
/-- `symx_dec` closes a goal `JalDec w imm` by reflexivity on the partially evaluated decoder. -/
elab "symx_dec" : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``JalDec 2 do throwError "symx_dec: not a `JalDec` goal"
  let some ty' ← unfoldDefinition? ty | throwError "symx_dec"
  let v ← forallTelescope ty' fun xs body => do
    let some (_, _, rhs) := body.eq? | throwError "symx_dec: unexpected goal"
    mkLambdaFVars xs (← mkEqRefl rhs)
  g.assign v
  replaceMainGoal []

deriving instance Lean.ToExpr for PF
deriving instance Lean.ToExpr for XTree

open Lean Meta Elab Tactic in
/-- `symx_eval`: replace the closed `XTree.prune Γ (symRunX C sub n s pf)` of the goal by its value
(compiled evaluation; the kernel re-checks it as one definitional unfolding). -/
elab "symx_eval" : tactic => do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let closed (e : Expr) := !e.hasFVar && !e.hasMVar
  let some e := tgt.find? (fun e => e.isAppOfArity ``XTree.prune 2 && closed e)
    | throwError "symx_eval: no closed `XTree.prune` in the goal"
  let v ← unsafe evalExpr XTree (mkConst ``XTree) e
  let te := toExpr v
  let tgt' := tgt.replace fun x => if x == e then some te else none
  replaceMainGoal [← g.replaceTargetDefEq tgt']

end VsaIris.SymExec
