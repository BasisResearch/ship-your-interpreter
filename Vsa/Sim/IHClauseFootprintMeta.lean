import Vsa.Sim.ExitFootprint
import Vsa.Sim.RuntimeOwnership

/-!
# `IHClauseFootprintMeta` — clause shapes derived from a footprint (IH tower, Level 2)

Every clause the string cells need is a consequence of ONE footprint fact
`MemFootprint F m0 m` (`ExitFootprint.lean`).  This file states the two derived
clause shapes once, over `MemFootprint`, and lifts them to the child contract
`EvalIHF F`:

* **region preservation** — bytes of any region disjoint from the footprint
  agree between the entry memory and the reached memory
  (`MemFootprint.agreeP_of_disjoint`, `.region`, `EvalIHF.regionPreserved`);
* **payload survival** — a C string, a `ValueRepr`, a `SharedCString`, or a
  `ValueOwned` whose byte range is disjoint from the footprint survives
  (`MemFootprint.cstring`, `.valueRepr`, `.sharedCString`, `.valueOwned`,
  `EvalIHF.cstringSurvives`);
* **the binary-arm left survival** — the left temporary at `sp - 968` survives
  a non-allocating right child (`strLeftSurvives_of_footprint`): its header lies
  above the right child's frame and its payload, covered outside the whole stack
  (`ValuePayloadCovered`, the `EvalPayloadIH` shape), is untouched by a footprint
  inside `[SL.lo, sp - 1088) ∪ [sp - 944, sp - 920)`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Sail Vsa
open Vsa.Machine (Config)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.RuntimeOwnership (SharedCString ValueOwned)

namespace Vsa.Sim

namespace MemFootprint

variable {F : Nat → Prop} {m0 m : Mem}

/-- (a) Region preservation: agreement on any predicate disjoint from the footprint. -/
theorem agreeP_of_disjoint (h : MemFootprint F m0 m) {R : Nat → Prop}
    (hd : ∀ k, R k → ¬ F k) : AgreeP R m0 m :=
  fun k hk => (h.agree k (hd k hk)).symm

/-- (a) Region preservation on a byte interval `[lo, hi)`. -/
theorem region (h : MemFootprint F m0 m) {lo hi : Nat}
    (hd : ∀ k, lo ≤ k → k < hi → ¬ F k) :
    ∀ k, lo ≤ k → k < hi → m[k]? = m0[k]? :=
  fun k h1 h2 => h.agree k (hd k h1 h2)

/-- (b) A C string whose bytes (through the NUL) avoid the footprint survives. -/
theorem cstring (h : MemFootprint F m0 m) {p : Nat} {s : String}
    (hcs : CString m0 p s) (hd : ∀ k, k ≤ s.length → ¬ F (p + k)) : CString m p s :=
  cstring_agreeP h.toAgreeP hcs hd

/-- (b) A represented value whose header and payload avoid the footprint survives. -/
theorem valueRepr (h : MemFootprint F m0 m) {N : NativeAddrs} {φc : Addr → Nat}
    {a : Nat} {v : Value} (hv : ValueRepr m0 N φc a v)
    (hhdr : ∀ k, valHeader a k → ¬ F k)
    (hpay : ValuePayloadCovered (fun k => ¬ F k) m0 a v) : ValueRepr m N φc a v :=
  valueRepr_agreeP h.toAgreeP hhdr hpay hv

/-- (b) A shared C string survives a footprint disjoint from the shared set. -/
theorem sharedCString (h : MemFootprint F m0 m) {shared : Nat → Prop} {p : Nat} {s : String}
    (hs : SharedCString m0 shared p s) (hd : ∀ k, shared k → ¬ F k) :
    SharedCString m shared p s :=
  hs.transport (h.agreeP_of_disjoint hd)

/-- (b) An owned value survives a footprint disjoint from its header and the shared set. -/
theorem valueOwned (h : MemFootprint F m0 m) {shared : Nat → Prop} {a : Nat} {v : Value}
    (ho : ValueOwned m0 shared a v) (hhdr : ∀ k, valHeader a k → ¬ F k)
    (hd : ∀ k, shared k → ¬ F k) : ValueOwned m shared a v := by
  cases v <;> simp only [ValueOwned] at ho ⊢
  all_goals first
    | exact True.intro
    | (obtain ⟨p, hp, hs⟩ := ho
       exact ⟨p, by rw [← read64_agreeP h.toAgreeP (valHeader_read64_off8 hhdr)]; exact hp,
         hs.transport (h.agreeP_of_disjoint hd)⟩)

end MemFootprint

/-- A byte outside the stack window and the result slot is outside `noArenaFoot`. -/
theorem noArenaFoot_not {SL : StackLayout} {A : Arena} {sp sret k : Nat}
    (h1 : ¬ (SL.lo ≤ k ∧ k < sp)) (h2 : ¬ (sret ≤ k ∧ k < sret + 24)) :
    ¬ noArenaFoot SL A sp sret k := by
  unfold noArenaFoot stackWin resultSlot; omega

/-! ## The clause shapes at the child contract -/

/-- Clause (a) at the child contract: a region family disjoint from the footprint
family is preserved between the child's entry memory and its actual return. -/
theorem EvalIHF.regionPreserved {F : FootFam} {st st' : Vsa.While.St} {d env : Nat}
    {e : Expr} {v : Value} (h : EvalIHF F st d env e st' v)
    (R : StackLayout → Arena → Nat → Nat → Nat → Prop)
    (hd : ∀ SL A sp sret k, R SL A sp sret k → ¬ F SL A sp sret k) :
    EvalIHWithM (fun _ A SL _ _ sp sret m0 c => AgreeP (R SL A sp.toNat sret.toNat) m0 c.σ.mem)
      st d env e st' v :=
  EvalIHWithM.mono
    (fun _ A SL _ _ sp sret _ _ hf =>
      hf.agreeP_of_disjoint (fun k hk => hd SL A sp.toNat sret.toNat k hk)) h

/-- Clause (b) at the child contract: a C string whose bytes avoid the footprint
family at every geometry survives the child. -/
theorem EvalIHF.cstringSurvives {F : FootFam} {st st' : Vsa.While.St} {d env : Nat}
    {e : Expr} {v : Value} (h : EvalIHF F st d env e st' v) (p : Nat) (s : String)
    (hd : ∀ SL A sp sret k, k ≤ s.length → ¬ F SL A sp sret (p + k)) :
    EvalIHWithM (fun _ _ _ _ _ _ _ m0 c => CString m0 p s → CString c.σ.mem p s)
      st d env e st' v :=
  EvalIHWithM.mono
    (fun _ A SL _ _ sp sret _ _ hf hcs =>
      hf.cstring hcs (fun k hk => hd SL A sp.toNat sret.toNat k hk)) h

/-! ## The binary arm's left survival from the right child's footprint -/

/-- **`strLeftSurvives_of_footprint`** — the left temporary at `sp - 968` (a string
value whose payload is covered outside the whole stack, the `EvalPayloadIH`
shape) survives ANY memory change with the footprint of a non-allocating right
child at its geometry `sp' = sp - 1088`, `sret' = sp - 944`.  This is the
memory-level cure of the `hVlSurv` obstruction (`PROOF_CLOSURE_PLAN.md`, task 1):
the head consumes it at the actual left-return and right-return memories. -/
theorem strLeftSurvives_of_footprint {N : NativeAddrs} {SL : StackLayout} {A : Arena}
    {sp : Nat} {φ : Addr → Nat} {mm mm' : Mem} {sl : String}
    (hsp : SL.lo + 1088 ≤ sp) (hspHi : sp ≤ SL.hi)
    (hv : ValueRepr mm N φ (sp - 968) (.str sl))
    (hcov : ValuePayloadCovered (fun k => ¬ (SL.lo ≤ k ∧ k < SL.hi)) mm (sp - 968) (.str sl))
    (hfoot : MemFootprint (noArenaFoot SL A (sp - 1088) (sp - 944)) mm mm') :
    ValueRepr mm' N φ (sp - 968) (.str sl) := by
  refine hfoot.valueRepr hv ?_ ?_
  · intro k hk hF
    unfold valHeader at hk
    unfold noArenaFoot stackWin resultSlot at hF
    omega
  · simp only [ValuePayloadCovered] at hcov ⊢
    intro p hp k hk hF
    have := hcov p hp k hk
    unfold noArenaFoot stackWin resultSlot at hF
    omega

#print axioms MemFootprint.agreeP_of_disjoint
#print axioms MemFootprint.cstring
#print axioms MemFootprint.valueRepr
#print axioms MemFootprint.valueOwned
#print axioms EvalIHF.regionPreserved
#print axioms EvalIHF.cstringSurvives
#print axioms strLeftSurvives_of_footprint

end Vsa.Sim
