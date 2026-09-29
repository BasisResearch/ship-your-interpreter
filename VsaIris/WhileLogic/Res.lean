import Iris.Instances.UPred
import VsaIris.WhileLogic.Store

/-!
# Resources of the WHILE program logic

The logic's assertions are iris-lean uniform predicates `UPred Res` over the
camera `Res` of *partial stores*:

* a frame heap `Nat → Option (Excl Frame)` (one exclusive cell per scope,
  holding its parent pointer and full binding list),
* a closure heap `Nat → Option (Excl ClosureData)`,
* the console output `Option (Excl Out)`.

Every component is discrete with Leibniz equality, so `≡{n}≡` on `Res` is
`=` (`dist_eq`). A big-step state `σ` is abstracted to the full resource
`abs σ`; a resource `r` describes part of `σ` in the presence of a frame `rf`
when `abs σ = r • rf`. The lemmas below read owned cells off that equation
and re-establish it after the store operations of the semantics.
-/

namespace Vsa.While.Logic

open Iris OFE CMRA Vsa.While

instance : OFE Frame := OFE.ofDiscrete Frame
instance : OFE.Discrete Frame := ⟨id⟩
instance : OFE ClosureData := OFE.ofDiscrete ClosureData
instance : OFE.Discrete ClosureData := ⟨id⟩

/-- The console contents, as a resource value. -/
structure Out where
  s : String

instance : OFE Out := OFE.ofDiscrete Out
instance : OFE.Discrete Out := ⟨id⟩

abbrev FHeap := Nat → Option (Excl Frame)
abbrev CHeap := Nat → Option (Excl ClosureData)
/-- The camera of partial WHILE states. -/
abbrev Res := FHeap × CHeap × Option (Excl Out)
/-- Assertions of the WHILE program logic. -/
abbrev vProp := UPred Res

theorem dist_eq {n : Nat} {x y : Res} (h : x ≡{n}≡ y) : x = y := OFE.Discrete.discrete h

theorem incN_iff {n : Nat} {x y : Res} : x ≼{n} y ↔ ∃ z, y = x • z :=
  ⟨fun ⟨z, h⟩ => ⟨z, dist_eq h⟩, fun ⟨z, h⟩ => ⟨z, h ▸ .rfl⟩⟩

@[simp] theorem op_fst (x y : Res) (a : Nat) : (x • y).1 a = x.1 a • y.1 a := rfl
@[simp] theorem op_snd_fst (x y : Res) (a : Nat) : (x • y).2.1 a = x.2.1 a • y.2.1 a := rfl
@[simp] theorem op_snd_snd (x y : Res) : (x • y).2.2 = x.2.2 • y.2.2 := rfl

theorem opt_op_none {α} [OFE α] (x : Option (Excl α)) : x • none = x := by
  cases x <;> rfl
theorem opt_none_op {α} [OFE α] (x : Option (Excl α)) : none • x = x := by
  cases x <;> rfl

@[simp] theorem excl_op_none {α} [OFE α] (a : α) :
    (some (Excl.excl a) : Option (Excl α)) • none = some (Excl.excl a) := rfl
@[simp] theorem excl_op_some {α} [OFE α] (a : α) (w : Excl α) :
    (some (Excl.excl a) : Option (Excl α)) • some w = some Excl.invalid := rfl

/-- An exclusive cell composed with a frame: the frame is empty there. -/
theorem excl_op_eq {α} [OFE α] {a b : α} {y : Option (Excl α)}
    (h : some (Excl.excl b) = (some (Excl.excl a) : Option (Excl α)) • y) :
    y = none ∧ b = a := by
  cases y with
  | none => exact ⟨rfl, Excl.excl.inj (Option.some.inj h)⟩
  | some y => cases h

theorem op_eq_none {α} [OFE α] {x y : Option (Excl α)} (h : (none : Option (Excl α)) = x • y) :
    x = none ∧ y = none := by
  cases x <;> cases y <;> first | exact ⟨rfl, rfl⟩ | cases h

/-! ## Abstraction of states -/

def absF (s : Store) : FHeap := fun a => s.frames[a]?.map .excl
def absC (s : Store) : CHeap := fun c => s.closures[c]?.map .excl

/-- The full resource of a big-step state. -/
def abs (σ : St) : Res := (absF σ.store, absC σ.store, some (.excl ⟨σ.out⟩))

theorem abs_validN (σ : St) (n : Nat) : ✓{n} abs σ := by
  refine ⟨fun a => ?_, fun c => ?_, trivial⟩
  · show optionValidN n (σ.store.frames[a]?.map Excl.excl)
    cases σ.store.frames[a]? <;> trivial
  · show optionValidN n (σ.store.closures[c]?.map Excl.excl)
    cases σ.store.closures[c]? <;> trivial

theorem validN_of_rep {σ : St} {r rf : Res} {n : Nat} (h : abs σ = r • rf) : ✓{n} r :=
  validN_op_left (h ▸ abs_validN σ n)

/-! ## Reading owned cells -/

theorem rep_frame {σ : St} {r rf : Res} {a : Nat} {F : Frame}
    (h : abs σ = r • rf) (hr : r.1 a = some (.excl F)) :
    σ.store.frames[a]? = some F ∧ rf.1 a = none := by
  have := congrArg (fun x : Res => x.1 a) h
  simp only [op_fst, hr, abs, absF] at this
  cases hy : rf.1 a with
  | some w =>
    rw [hy, excl_op_some] at this
    cases hF : σ.store.frames[a]? <;> rw [hF] at this <;> cases this
  | none =>
    rw [hy, excl_op_none] at this
    cases hF : σ.store.frames[a]? <;> rw [hF] at this <;> cases this
    exact ⟨rfl, rfl⟩

theorem rep_closure {σ : St} {r rf : Res} {c : Nat} {cd : ClosureData}
    (h : abs σ = r • rf) (hr : r.2.1 c = some (.excl cd)) :
    σ.store.closures[c]? = some cd ∧ rf.2.1 c = none := by
  have := congrArg (fun x : Res => x.2.1 c) h
  simp only [op_snd_fst, hr, abs, absC] at this
  cases hy : rf.2.1 c with
  | some w =>
    rw [hy, excl_op_some] at this
    cases hF : σ.store.closures[c]? <;> rw [hF] at this <;> cases this
  | none =>
    rw [hy, excl_op_none] at this
    cases hF : σ.store.closures[c]? <;> rw [hF] at this <;> cases this
    exact ⟨rfl, rfl⟩

theorem rep_out {σ : St} {r rf : Res} {o : String}
    (h : abs σ = r • rf) (hr : r.2.2 = some (.excl ⟨o⟩)) :
    σ.out = o ∧ rf.2.2 = none := by
  have := congrArg (fun x : Res => x.2.2) h
  simp only [op_snd_snd, hr, abs] at this
  obtain ⟨h1, h2⟩ := excl_op_eq this
  exact ⟨congrArg Out.s h2, h1⟩

theorem rep_fresh {σ : St} {r rf : Res} {a : Nat}
    (h : abs σ = r • rf) (ha : σ.store.frames[a]? = none) : r.1 a = none ∧ rf.1 a = none := by
  have := congrArg (fun x : Res => x.1 a) h
  simp only [op_fst, abs, absF, ha, Option.map_none] at this
  exact op_eq_none this

theorem rep_freshC {σ : St} {r rf : Res} {c : Nat}
    (h : abs σ = r • rf) (hc : σ.store.closures[c]? = none) :
    r.2.1 c = none ∧ rf.2.1 c = none := by
  have := congrArg (fun x : Res => x.2.1 c) h
  simp only [op_snd_fst, abs, absC, hc, Option.map_none] at this
  exact op_eq_none this

/-! ## Re-establishing the representation after a store operation -/

/-- Overwrite (or create) the frame cell at `a`. -/
def Res.setF (r : Res) (a : Nat) (F : Frame) : Res :=
  (fun b => if b = a then some (.excl F) else r.1 b, r.2)

/-- Overwrite (or create) the closure cell at `c`. -/
def Res.setC (r : Res) (c : Nat) (cd : ClosureData) : Res :=
  (r.1, fun b => if b = c then some (.excl cd) else r.2.1 b, r.2.2)

/-- Overwrite the output cell. -/
def Res.setO (r : Res) (o : String) : Res := (r.1, r.2.1, some (.excl ⟨o⟩))

theorem rep_setF {σ σ' : St} {r rf : Res} {a : Nat} {F : Frame}
    (h : abs σ = r • rf) (hrf : rf.1 a = none)
    (hb : ∀ b, b ≠ a → σ'.store.frames[b]? = σ.store.frames[b]?)
    (ha : σ'.store.frames[a]? = some F)
    (hc : σ'.store.closures = σ.store.closures) (ho : σ'.out = σ.out) :
    abs σ' = r.setF a F • rf := by
  have h1 := congrArg (fun x : Res => x.1) h
  have h2 := congrArg (fun x : Res => x.2) h
  simp only [abs] at h1 h2
  refine Prod.ext (funext fun b => ?_) ?_
  · change σ'.store.frames[b]?.map Excl.excl =
      (if b = a then some (Excl.excl F) else r.1 b) • rf.1 b
    by_cases hba : b = a
    · subst hba; simp only [ha, ↓reduceIte, hrf]; rfl
    · simp only [hb b hba, hba, ↓reduceIte]
      exact congrFun h1 b
  · show (absC σ'.store, some (Excl.excl (⟨σ'.out⟩ : Out))) = r.2 • rf.2
    rw [ho, show absC σ'.store = absC σ.store by unfold absC; rw [hc]]
    exact h2

theorem rep_setC {σ σ' : St} {r rf : Res} {c : Nat} {cd : ClosureData}
    (h : abs σ = r • rf) (hrf : rf.2.1 c = none)
    (hb : ∀ b, b ≠ c → σ'.store.closures[b]? = σ.store.closures[b]?)
    (hcd : σ'.store.closures[c]? = some cd)
    (hf : σ'.store.frames = σ.store.frames) (ho : σ'.out = σ.out) :
    abs σ' = r.setC c cd • rf := by
  have h1 := congrArg (fun x : Res => x.1) h
  have h2 := congrArg (fun x : Res => x.2.1) h
  have h3 := congrArg (fun x : Res => x.2.2) h
  simp only [abs] at h1 h2 h3
  refine Prod.ext ?_ (Prod.ext (funext fun b => ?_) ?_)
  · show absF σ'.store = r.1 • rf.1
    rw [show absF σ'.store = absF σ.store by unfold absF; rw [hf]]; exact h1
  · change σ'.store.closures[b]?.map Excl.excl =
      (if b = c then some (Excl.excl cd) else r.2.1 b) • rf.2.1 b
    by_cases hbc : b = c
    · subst hbc; simp only [hcd, ↓reduceIte, hrf]; rfl
    · simp only [hb b hbc, hbc, ↓reduceIte]
      exact congrFun h2 b
  · show some (Excl.excl (⟨σ'.out⟩ : Out)) = r.2.2 • rf.2.2
    rw [ho]; exact h3

theorem rep_setO {σ σ' : St} {r rf : Res}
    (h : abs σ = r • rf) (hrf : rf.2.2 = none) (hs : σ'.store = σ.store) :
    abs σ' = r.setO σ'.out • rf := by
  have h1 := congrArg (fun x : Res => x.1) h
  have h2 := congrArg (fun x : Res => x.2.1) h
  simp only [abs] at h1 h2
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show absF σ'.store = r.1 • rf.1; rw [hs]; exact h1
  · show absC σ'.store = r.2.1 • rf.2.1; rw [hs]; exact h2
  · show some (Excl.excl (⟨σ'.out⟩ : Out)) = some (Excl.excl (⟨σ'.out⟩ : Out)) • rf.2.2
    rw [hrf]; rfl

theorem setF_op (r z : Res) (a : Nat) (F : Frame) (hz : z.1 a = none) :
    (r • z).setF a F = r.setF a F • z := by
  refine Prod.ext (funext fun b => ?_) rfl
  change (if b = a then some (Excl.excl F) else r.1 b • z.1 b) =
    (if b = a then some (Excl.excl F) else r.1 b) • z.1 b
  by_cases hb : b = a
  · subst hb; simp only [↓reduceIte, hz]; rfl
  · simp only [hb, ↓reduceIte]

/-! ## Points-to assertions -/

/-- The single frame cell `a ↦ F`. -/
def singF (a : Nat) (F : Frame) : Res :=
  (fun b => if b = a then some (.excl F) else none, fun _ => none, none)

def singC (c : Nat) (cd : ClosureData) : Res :=
  (fun _ => none, fun b => if b = c then some (.excl cd) else none, none)

def singO (o : String) : Res := (fun _ => none, fun _ => none, some (.excl ⟨o⟩))

/-- `a ↦f F`: exclusive ownership of scope `a`, whose parent pointer and full
binding list are `F`. -/
def ptsF (a : Nat) (F : Frame) : vProp := UPred.ownM (singF a F)
/-- `c ↦c cd`: exclusive ownership of closure `c`. -/
def ptsC (c : Nat) (cd : ClosureData) : vProp := UPred.ownM (singC c cd)
/-- `out o`: exclusive ownership of the console, whose contents are `o`. -/
def outIs (o : String) : vProp := UPred.ownM (singO o)

scoped infix:60 " ↦f " => ptsF
scoped infix:60 " ↦c " => ptsC

theorem ownM_holds {m : Res} {n : Nat} {x : Iris.ValidAt Res n} :
    (UPred.ownM m).holds n x ↔ ∃ z, x.val = m • z := incN_iff

@[simp] theorem singF_at (a : Nat) (F : Frame) : (singF a F).1 a = some (.excl F) := by
  simp [singF]

@[simp] theorem singC_at (c : Nat) (cd : ClosureData) :
    (singC c cd).2.1 c = some (.excl cd) := by
  simp [singC]

@[simp] theorem singO_out (o : String) : (singO o).2.2 = some (.excl ⟨o⟩) := rfl

theorem singF_setF (a : Nat) (F F' : Frame) : (singF a F).setF a F' = singF a F' := by
  refine Prod.ext (funext fun b => ?_) rfl
  change (if b = a then some (Excl.excl F') else (if b = a then _ else none)) =
    (if b = a then some (Excl.excl F') else none)
  by_cases hb : b = a <;> simp [hb]

theorem singO_setO (o o' : String) : (singO o).setO o' = singO o' := rfl

/-- Creating a frame cell in a resource that has none there. -/
theorem setF_eq_sing_op (x : Res) (a : Nat) (F : Frame) (hx : x.1 a = none) :
    x.setF a F = singF a F • x := by
  refine Prod.ext (funext fun b => ?_) ?_
  · change (if b = a then some (Excl.excl F) else x.1 b) =
      (if b = a then some (Excl.excl F) else none) • x.1 b
    by_cases hb : b = a
    · subst hb; simp only [↓reduceIte, hx]; rfl
    · simp only [hb, ↓reduceIte]; exact (opt_none_op _).symm
  · change x.2 = ((fun _ => none, none) : CHeap × Option (Excl Out)) • x.2
    refine Prod.ext (funext fun c => ?_) ?_
    · exact (opt_none_op _).symm
    · exact (opt_none_op _).symm

/-- Creating a closure cell in a resource that has none there. -/
theorem setC_eq_sing_op (x : Res) (c : Nat) (cd : ClosureData) (hx : x.2.1 c = none) :
    x.setC c cd = singC c cd • x := by
  refine Prod.ext (funext fun b => (opt_none_op _).symm) (Prod.ext (funext fun b => ?_) ?_)
  · change (if b = c then some (Excl.excl cd) else x.2.1 b) =
      (if b = c then some (Excl.excl cd) else none) • x.2.1 b
    by_cases hb : b = c
    · subst hb; simp only [↓reduceIte, hx]; rfl
    · simp only [hb, ↓reduceIte]; exact (opt_none_op _).symm
  · exact (opt_none_op _).symm

theorem ownM_self (m : Res) (n : Nat) (h : ✓{n} m) : (UPred.ownM m).holds n ⟨m, h⟩ :=
  ownM_holds.mpr ⟨UCMRA.unit, unit_right_id.symm⟩

end Vsa.While.Logic
