import Vsa.Sim.IHClauseFootprintMeta
import Vsa.Sim.EntryGround
import Vsa.Sim.EnvGetSpec9
import Vsa.Sim.EvalReturn

/-!
# `OwnedPayloadClause` — the payload-ownership clause (IH tower, Level 2)

The string-comparison cells (`StrCmpCell.lean`, residual `StrCmpOperandsSupply`)
need to know WHERE a returned string's payload lives: `ValueRepr` gives a
`CString` at some pointer and no geometry at all.  This file states that
knowledge once, as an induction-hypothesis clause over the recursor
(`scripts/ih_clauses.tsv` clause `OwnedPayload`), at the shape the allocator
ledger (`PROOF_CLOSURE_PLAN.md` task 2) fills:

* **`SharedFam` / `OwnedIndex`** — the shared byte set, indexed by the call
  geometry `SL A` exactly like a `FootFam` (so it is entry-independent and no
  stability question arises when a parent scribbles its stack before calling a
  child).  `OwnedIndex` is the named-field bundle of its properties: the three
  `SharedGeom`-shaped geometry fields (`ram`, `htif`, `stack`), the IMMUTABLE
  AST-region part `ast` (derived concretely from `EvalGround`'s
  `AstRegionSpec`), and the ALLOCATOR part `arena` (a field: task 2's ledger
  supplies the live immutable payload extents through `ArenaShared`).
  `stdShared` is the canonical index — the geometric envelope above the HTIF
  window and outside the stack — and `ownedIndex_std` proves `OwnedIndex` for
  it unconditionally, so the clause is never stated at an uninhabited index.
* **`OwnedSlot`** — the clause's retained fact at a 24-byte value slot,
  stated WITHOUT naming the semantic value (the generator's `pred` is one
  fixed `EvalExtraM` term, so it cannot mention `v`): a slot whose tag is
  `.str` (3) or `.native` (5) points at a SHARED C string.  Non-string,
  non-native results satisfy it definitionally (`OwnedSlot.of_payloadFree`),
  which is what closes eleven of the fifteen recursor steps.
* **transport** — `OwnedSlot.transport` moves the fact across any
  `MemFootprint` disjoint from the slot header and from the shared set (the
  `MemFootprint.valueOwned` shape of `IHClauseFootprintMeta.lean`).
* **the consumer side** — `valueOwned_of_ownedSlot` turns the clause fact plus
  the actual `ValueRepr` into `RuntimeOwnership.ValueOwned` (what
  `strCmpOperandsAt_of_owned` consumes), and `ownedGeom_of_index` produces the
  three `SharedGeom` fields from the index and ONE named premise
  `SharedTopSlack` (the `strcmp` word loop's 8-byte slack below the RAM top,
  which an entry's `AstRegionSpec` alone does not give).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Sail Vsa
open Vsa.Machine (Config)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.RuntimeOwnership (SharedCString ValueOwned)

namespace Vsa.Sim

/-! ## 1. The shared byte set and its index -/

/-- An entry-independent shared byte set, indexed by the call geometry
(`SL`, `A`) exactly like a `FootFam`. -/
abbrev SharedFam := StackLayout → Arena → Nat → Prop

/-- Geometry of an arena holding immutable payloads: above the HTIF window,
below the RAM top, and outside the stack.  Supplier (task 2): the allocator
ledger's `HeapArena`/`Reserved` bounds at the concrete Layout. -/
structure ArenaShared (SL : StackLayout) (A : Arena) : Prop where
  htif : tohostAddr + 16 ≤ A.lo
  top : A.hi ≤ 0x100000000
  stack : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo

/-- **The ownership index.**  `S` is the byte set a returned payload may live
in; the fields are everything producers and consumers of the clause need.

* `ram`/`htif`/`stack` — the consumer-side geometry (`SharedGeom`'s shape minus
  the RAM-top slack, which is the separate named premise `SharedTopSlack`);
* `ast` — the immutable part: every byte of ANY entry's pinned AST/rodata
  region is shared (`EvalGround.ast`, `AstRegionSpec`);
* `arena` — the ALLOCATOR part, a field the ledger supplies (task 2:
  `HeapOwned`/`Reserved` place the live immutable payload extents inside a
  well-placed arena). -/
structure OwnedIndex (S : SharedFam) : Prop where
  ram : ∀ (SL : StackLayout) (A : Arena) (k : Nat), S SL A k →
    0x8001acf0 ≤ k ∧ k < 0x100000000
  htif : ∀ (SL : StackLayout) (A : Arena) (k : Nat), S SL A k → tohostAddr + 16 ≤ k
  stack : ∀ (SL : StackLayout) (A : Arena) (k : Nat), S SL A k → k < SL.lo ∨ SL.hi ≤ k
  ast : ∀ (SL : StackLayout) (A : Arena) (m : Mem) (sret aExpr : Nat) (e : Expr)
    (lo hi : Nat), AstRegionSpec m SL A sret aExpr e lo hi →
    ∀ k, lo ≤ k → k < hi → S SL A k
  arena : ∀ (SL : StackLayout) (A : Arena), ArenaShared SL A →
    ∀ k, A.lo ≤ k → k < A.hi → S SL A k

/-- The canonical index: the geometric envelope above the HTIF window, below
the RAM top, outside the stack.  Both the pinned AST region and a well-placed
arena lie inside it, so `OwnedIndex stdShared` needs no premise. -/
def stdShared : SharedFam := fun SL _ k =>
  tohostAddr + 16 ≤ k ∧ k < 0x100000000 ∧ (k < SL.lo ∨ SL.hi ≤ k)

theorem ownedIndex_std : OwnedIndex stdShared where
  ram := by
    intro _ _ k hk
    simp only [stdShared] at hk
    have ht : tohostAddr = 0x8001ad00 := rfl
    obtain ⟨h1, h2, _⟩ := hk
    omega
  htif := by
    intro _ _ k hk
    simp only [stdShared] at hk
    exact hk.1
  stack := by
    intro _ _ k hk
    simp only [stdShared] at hk
    exact hk.2.2
  ast := by
    intro SL _ _ _ _ _ lo hi spec k hlo hhi
    have hw := spec.win
    have hr := spec.hi_ram
    simp only [stdShared]
    refine ⟨by omega, by omega, ?_⟩
    rcases spec.stack_disjoint with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  arena := by
    intro SL A hA k hlo hhi
    have hht := hA.htif
    have htp := hA.top
    simp only [stdShared]
    refine ⟨by omega, by omega, ?_⟩
    rcases hA.stack with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-- The three `SharedGeom` fields (`StrCmpCellClauses.lean`) of one index
instance: `SharedGeom.mk hG.ram hG.htif hG.stack`. -/
structure OwnedGeom (shared : Nat → Prop) (SL : StackLayout) : Prop where
  ram : ∀ k, shared k → 0x8001acf0 ≤ k ∧ k + 8 ≤ 0x100000000
  htif : ∀ k, shared k → tohostAddr + 16 ≤ k
  stack : ∀ k, shared k → k < SL.lo ∨ SL.hi ≤ k

/-- **NAMED PREMISE** — the `strcmp` word loop reads 8 bytes at a time, so the
shared set must stay 8 bytes below the RAM top.  An entry's `AstRegionSpec`
gives only `hi ≤ 2^32`, so this is a Layout fact.  Supplier (task 2): the
concrete image/arena bounds — the AST region and the arena both end far below
`0x100000000`. -/
def SharedTopSlack (S : SharedFam) (SL : StackLayout) (A : Arena) : Prop :=
  ∀ k, S SL A k → k + 8 ≤ 0x100000000

theorem ownedGeom_of_index {S : SharedFam} {SL : StackLayout} {A : Arena}
    (h : OwnedIndex S) (htop : SharedTopSlack S SL A) : OwnedGeom (S SL A) SL where
  ram := fun k hk => ⟨(h.ram SL A k hk).1, htop k hk⟩
  htif := fun k hk => h.htif SL A k hk
  stack := fun k hk => h.stack SL A k hk

/-! ## 2. `OwnedSlot` — the retained fact, stated without the semantic value -/

/-- **The clause's retained fact.**  A 24-byte value slot at `a` whose tag word
is `.str` (3) or `.native` (5) points at a SHARED C string.  The generator's
clause predicate is one fixed `EvalExtraM` term and therefore cannot mention
the returned value `v`, so the payload-carrying variants are selected by their
tag instead. -/
def OwnedSlot (m : Mem) (shared : Nat → Prop) (a : Nat) : Prop :=
  ∀ tag : Nat, read32 m a = some tag → tag = 3 ∨ tag = 5 →
    ∃ p s, read64 m (a + 8) = some p ∧ SharedCString m shared p s

/-- Values with no indirect payload: everything but `.str` and `.native`
(the variants `RuntimeOwnership.ValueOwned` constrains). -/
def PayloadFree : Value → Prop
  | .str _ => False
  | .native _ => False
  | _ => True

/-- **The definitional discharge.**  A represented non-string, non-native result
satisfies the clause at EVERY shared set: its tag word is `0`, `1`, `2` or `4`.
This is what closes the eleven recursor steps whose result cannot carry a
payload. -/
theorem OwnedSlot.of_payloadFree {m : Mem} {shared : Nat → Prop} {N : NativeAddrs}
    {φc : Addr → Nat} {a : Nat} {v : Value}
    (hv : ValueRepr m N φc a v) (hpf : PayloadFree v) : OwnedSlot m shared a := by
  intro tag htag hts
  have hinj : ∀ n : Nat, read32 m a = some n → tag = n :=
    fun n hn => Option.some.inj (htag.symm.trans hn)
  exfalso
  cases v <;>
    first
      | exact False.elim hpf
      | (rcases hts with rfl | rfl) <;>
          first
            | exact absurd (hinj 0 hv) (by decide)
            | exact absurd (hinj 1 hv.1) (by decide)
            | exact absurd (hinj 2 hv.1) (by decide)
            | exact absurd (hinj 4 hv.1) (by decide)

/-- **Transport** — the fact survives any `MemFootprint` disjoint from the slot
header and from the shared set (`MemFootprint.valueOwned`'s shape). -/
theorem OwnedSlot.transport {F shared : Nat → Prop} {m0 m : Mem} {a : Nat}
    (h : OwnedSlot m0 shared a) (hf : MemFootprint F m0 m)
    (hhdr : ∀ k, valHeader a k → ¬ F k) (hd : ∀ k, shared k → ¬ F k) :
    OwnedSlot m shared a := by
  intro tag htag hts
  have hag := hf.toAgreeP
  have h32 : read32 m0 a = read32 m a := read32_agreeP hag (valHeader_read32 hhdr)
  have h64 : read64 m0 (a + 8) = read64 m (a + 8) :=
    read64_agreeP hag (valHeader_read64_off8 hhdr)
  obtain ⟨p, s, hp, hs⟩ := h tag (h32.trans htag) hts
  exact ⟨p, s, h64.symm.trans hp, hf.sharedCString hs hd⟩

/-- **The consumer side** — the clause fact plus the ACTUAL represented string
value give `RuntimeOwnership.ValueOwned`, the hypothesis of
`strCmpOperandsAt_of_owned` (`StrCmpCellClauses.lean`). -/
theorem valueOwned_of_ownedSlot {m : Mem} {shared : Nat → Prop} {N : NativeAddrs}
    {φc : Addr → Nat} {a : Nat} {s : String}
    (h : OwnedSlot m shared a) (hv : ValueRepr m N φc a (.str s)) :
    ValueOwned m shared a (.str s) := by
  obtain ⟨htag, p, hp, _hnz, hcs⟩ := hv
  obtain ⟨q, t, hq, hst⟩ := h 3 htag (Or.inl rfl)
  have hpq : p = q := Option.some.inj (hp.symm.trans hq)
  subst hpq
  obtain ⟨cs, hcstr, hseq⟩ := hcs
  obtain ⟨cs', hcstr', hteq⟩ := hst.repr
  have hcc : cs = cs' := cstr_unique_eg9 m p cs cs' hcstr hcstr'
  have hts : t = s := by rw [hteq, hseq, hcc]
  subst hts
  exact ⟨p, hp, hst⟩

/-! ## 3. The clause as an `EvalExtraM` and its trivial producer -/

/-- The clause predicate at the index `S`: the value the call left in its
result slot is owned at `S`. -/
abbrev ownedExtra (S : SharedFam) : EvalExtraM :=
  fun _ A SL _ _ _ sret _ c => OwnedSlot c.σ.mem (S SL A) sret.toNat

/-- The ∀-closed child contract at the index `S` (the clause's `mEvalE`). -/
abbrev EvalIHO (S : SharedFam) (st : Vsa.While.St) (d : Nat) (env : Addr) (e : Expr)
    (st' : Vsa.While.St) (v : Value) : Prop :=
  EvalIHWithM (ownedExtra S) st d env e st' v

theorem EvalIHO.forget {S : SharedFam} {st st' : Vsa.While.St} {d env : Nat}
    {e : Expr} {v : Value} (h : EvalIHO S st d env e st' v) : EvalIH st d env e st' v :=
  EvalIHWithM.forget h

/-- **The clause from the OLD motive alone**, whenever the produced value cannot
carry a payload: the same execution, with the extra read off the exit's own
`ValueRepr`.  No re-derivation of any row. -/
theorem evalIHO_of_return {S : SharedFam} {st st' : Vsa.While.St} {d env : Nat}
    {e : Expr} {v : Value} (hpf : PayloadFree v)
    (h : EvalReturnIH TrivialOwned st d env e st' v) : EvalIHO S st d env e st' v where
  run := fun g N A SL φf φc sp r sret aEnv aExpr m0 =>
    (h.forget g N A SL φf φc sp r sret aEnv aExpr m0).conseq (fun _ hp => hp)
      (fun _ hp => ⟨hp, by
        obtain ⟨φc', _, hval⟩ := hp.1.result
        exact OwnedSlot.of_payloadFree hval hpf⟩)

#print axioms ownedIndex_std
#print axioms ownedGeom_of_index
#print axioms OwnedSlot.of_payloadFree
#print axioms OwnedSlot.transport
#print axioms valueOwned_of_ownedSlot
#print axioms evalIHO_of_return

end Vsa.Sim
