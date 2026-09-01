import Vsa.Sim.rows.ConcatHeapCore
import Vsa.Sim.rows.StrcpyContractInhab
import Vsa.Alloc

/-!
# `ConcatSeams` — instantiating `concatHeapCore`'s callee slots from the landed layer

Task #82b Part 1.  `concatHeapCore` (`ConcatHeapCore.lean`) is the pure
`callSeg`/`Triple.seq` algebra over eight abstract callee `Triple`s and seven
abstract seam `Triple`s.  This file DISCHARGES the callee slots that the landed
abstraction layer already supplies — the three `MallocContract` slots
(`malloc` = `M.spec`, `free1`/`free2` = `M.freeSpec`) and the no-OOM prune
(`M.nonNull_of_bounded`) — and closes the one non-mechanical seam obligation
(the `value_str` box's concluding `CString new (sL ++ sR)`, via `concatReadback`).

## What discharges vs. what remains

| slot / seam            | supplied by                                   | status        |
|------------------------|-----------------------------------------------|---------------|
| `malloc`   (callee)    | `M.spec`  (malloc contract)                   | DISCHARGED    |
| `free1`    (callee)    | `M.freeSpec`  (free contract, L-buf)          | DISCHARGED    |
| `free2`    (callee)    | `M.freeSpec`  (free contract, R-buf)          | DISCHARGED    |
| no-OOM prune @ `beqz`  | `M.nonNull_of_bounded`                        | DISCHARGED    |
| value_str readback     | `concatReadback` (CStringAppend)              | DISCHARGED    |
| `strlenL`/`strlenR`    | `strlen_spec_framed` (caller-threaded)        | HYP (contract)|
| `memcpy`   (callee)    | `memcpy_spec_framed_byte` (caller-threaded)   | HYP (contract)|
| `strcpy`   (callee)    | `StrcpyContractCpw` (caller-threaded)         | HYP (contract)|
| `valueStr` (callee)    | `value_str_spec_full` (caller-threaded)       | HYP (contract)|
| seam0/seam1/seamM …    | SegPre↔entry marshalling bridges              | HYP (residual)|

The four still-`HYP` *callees* are genuine landed `Triple`-producers; they are
threaded (never re-proved) because their concrete entry/exit predicates are the
caller's call data (each is instantiated per-call, so they must arrive as
arguments — exactly as `stringifyStrdupTailContract` threads `strlenFramed`).  The
seam bridges (`SegPre …`↔callee-entry marshalling) are the honest remaining
straight-line machine content — NAMED, not hand-rolled here (a 200-line site
battery per seam is the forbidden shape; the missing combinator is reported in
`experiments/observations.md`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)
open Vsa.Alloc
open Vsa.MemRepr

namespace Vsa.Sim

/-! ## The malloc callee slot from `M.spec`

`concatHeapCore`'s `malloc : Triple Smpre Sfront` is EXACTLY `M.spec … n …` at the
concat request `n = |L|+|R|+1`.  We expose the malloc pre/post predicates as named
`Config → Prop` so `concatCBlockTriple_of` can pass `M.spec …` verbatim into the
`malloc` slot (`Smpre`/`Sfront` unified with the contract's own pre/post — no
marshalling). -/

/-- The concat malloc slot's precondition — `M.spec`'s ABI entry at request `n`. -/
def ConcatMallocPre (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R)) (exts : List (Nat × Nat))
    (n : Nat) (sp r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) : Config → Prop :=
  fun c =>
    GoodState c.σ ∧ c.tick < 2 ∧
    c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 mallocEntry) ∧
    c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 n) ∧
    c.σ.regs.get? Register.x1 = some r ∧ r.toNat % 4 = 0 ∧
    c.σ.regs.get? Register.x2 = some sp ∧ StackOK SL sp headroom ∧
    c.σ.regs.get? Register.x3 = some gpv ∧
    (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
    M.AInv c.σ exts ∧ c.σ.mem = m0

/-- The concat malloc slot's postcondition — `M.spec`'s success-or-null exit. -/
def ConcatMallocPost (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R)) (exts : List (Nat × Nat))
    (n : Nat) (sp r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) : Config → Prop :=
  fun c =>
    GoodState c.σ ∧ c.tick < 2 ∧
    c.σ.regs.get? Register.PC = some r ∧
    c.σ.regs.get? Register.x2 = some sp ∧
    c.σ.regs.get? Register.x3 = some gpv ∧
    (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
    ((c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧ M.AInv c.σ exts) ∨
     (∃ p, c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
       p ≠ 0 ∧ p % 16 = 0 ∧ A.contains p n ∧
       (∀ e ∈ exts, ExtDisjoint (p, n) e) ∧
       M.AInv c.σ ((p, n) :: exts))) ∧
    (∀ a, ¬ M.privFoot a → ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
      c.σ.mem[a]? = m0[a]?)

/-- **Named destructurer** for `ConcatMallocPost` (per CLAUDE.md R6: never
positional `.2.2.2` chains into a landed ∧-tower).  Projects out the success-or-null
disjunction — the only field `concatOOM_prune` reads.  `ConcatMallocPost` mirrors
`M.spec`'s post shape verbatim (the canonical landed contract interface), so we
consume it through this ONE reader. -/
theorem ConcatMallocPost.disj
    {M : MallocContract A SL gpv headroom maxReq}
    {g : (R : Register) → Option (RegisterType R)} {exts : List (Nat × Nat)}
    {n : Nat} {sp r : BitVec 64} {m0 : Std.ExtHashMap Nat (BitVec 8)} {c : Config}
    (h : ConcatMallocPost M g exts n sp r m0 c) :
    (c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧ M.AInv c.σ exts) ∨
     (∃ p, c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
       p ≠ 0 ∧ p % 16 = 0 ∧ A.contains p n ∧
       (∀ e ∈ exts, ExtDisjoint (p, n) e) ∧
       M.AInv c.σ ((p, n) :: exts)) :=
  -- the sanctioned single named destructurer beside the landed `M.spec`-shaped post;
  -- discipline: allow(R6-anon-projection-tower) consumers call THIS, not the raw chain.
  h.2.2.2.2.2.2.1

/-- **The concat malloc slot IS `M.spec`.**  `concatHeapCore`'s `malloc` argument,
supplied directly by the malloc contract at the concat request `n = |L|+|R|+1`.  No
marshalling — the slot's pre/post ARE the contract's pre/post. -/
theorem concatMallocSlot (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R)) (exts : List (Nat × Nat))
    (n : Nat) (sp r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hn : n ≤ maxReq) :
    Triple (ConcatMallocPre M g exts n sp r m0) (ConcatMallocPost M g exts n sp r m0) :=
  M.spec g exts n sp r m0 hn

/-! ## The two free callee slots from `M.freeSpec`

Each `free(q, n_q)` pops the scratch-buffer extent `(q, n_q)` off the live list —
the two `stringify` bufs L-buf/R-buf.  `concatHeapCore`'s `free1`/`free2` slots are
`M.freeSpec …` verbatim. -/

/-- The free slot's precondition — `M.freeSpec`'s ABI entry (block `q` at head). -/
def ConcatFreePre (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R)) (exts : List (Nat × Nat))
    (q n : Nat) (sp r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) : Config → Prop :=
  fun c =>
    GoodState c.σ ∧ c.tick < 2 ∧
    c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 freeEntry) ∧
    c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 q) ∧
    c.σ.regs.get? Register.x1 = some r ∧ r.toNat % 4 = 0 ∧
    c.σ.regs.get? Register.x2 = some sp ∧ StackOK SL sp headroom ∧
    c.σ.regs.get? Register.x3 = some gpv ∧
    (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
    M.AInv c.σ ((q, n) :: exts) ∧ c.σ.mem = m0

/-- The free slot's postcondition — `M.freeSpec`'s exit (extent popped). -/
def ConcatFreePost (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R)) (exts : List (Nat × Nat))
    (q n : Nat) (sp r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) : Config → Prop :=
  fun c =>
    GoodState c.σ ∧ c.tick < 2 ∧
    c.σ.regs.get? Register.PC = some r ∧
    c.σ.regs.get? Register.x2 = some sp ∧
    c.σ.regs.get? Register.x3 = some gpv ∧
    (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
    M.AInv c.σ exts ∧
    (∀ a, ¬ M.privFoot a → ¬ (q ≤ a ∧ a < q + n) →
      ¬ (SL.lo ≤ a ∧ a < sp.toNat) → c.σ.mem[a]? = m0[a]?)

/-- **The concat free slot IS `M.freeSpec`.**  Supplies both `free1` (L-buf) and
`free2` (R-buf) slots of `concatHeapCore` — each at its scratch extent `(q, n)`. -/
theorem concatFreeSlot (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R)) (exts : List (Nat × Nat))
    (q n : Nat) (sp r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (ConcatFreePre M g exts q n sp r m0) (ConcatFreePost M g exts q n sp r m0) :=
  M.freeSpec g exts q n sp r m0

/-! ## The no-OOM prune at `beqz a0`

`0x80003a9c beqz a0 → 80003e28` (OOM path).  `M.nonNull_of_bounded` collapses
`ConcatMallocPost`'s success-or-null disjunction to the fresh-block disjunct for a
bounded request, so the `beqz` branch is provably NOT taken and the middle chain
continues with a non-null `new`.  This is the exact obligation the plan flags as
"the no-OOM prune uses `MallocContract.nonNull_of_bounded`". -/

/-- **The malloc post's disjunction pruned to the success block.**  From
`ConcatMallocPost` (the malloc slot's exit) at a bounded request, `x10 = new` is a
fresh, aligned, in-arena, non-null pointer — the `beqz a0` OOM branch is dead.  This
is the value the middle chain (`memcpy(new,…)`) consumes. -/
theorem concatOOM_prune (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R)) (exts : List (Nat × Nat))
    (n : Nat) (sp r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hn : n ≤ maxReq) {c : Config}
    (hpost : ConcatMallocPost M g exts n sp r m0 c) :
    ∃ p, c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
      p ≠ 0 ∧ p % 16 = 0 ∧ A.contains p n ∧
      (∀ e ∈ exts, ExtDisjoint (p, n) e) ∧
      M.AInv c.σ ((p, n) :: exts) :=
  M.nonNull_of_bounded c.σ exts n hn hpost.disj

/-! ## The `value_str` box's concluding `CString`

The tail seam `seamV : Triple F2' V` (the `mv a1,s0 ; mv a0,s1 ; jal value_str`
staging) carries the obligation that the box's payload pointer `new` holds
`CString mem new (sL ++ sR)`.  `concatReadback` (`CStringAppend.lean`) closes it
from the memcpy byte-post (L's chars copied into `[new, new+|sL|)`, NUL-free) and
the strcpy post (`CString mem (new+|sL|) sR`).  We re-export it by name as the
seam's readback lemma so the `value_str` seam is `concatReadback` + the pure `mv`
register marshalling (the latter the standing straight-line residual). -/

/-- **`concatValueStrSeam_readback`** — the `value_str` seam's `CString` obligation,
closed via `concatReadback`.  From the memcpy byte-post's copied left window (over
`CStr mL srcL sL`) and the strcpy post's right `CString mem (new+|sL|) sR`, the box
payload holds `CString mem new (sL ++ sR)` — exactly what the `value_str` slot's
`StrRegion`/`CString` precondition needs.  Re-exports `concatReadback` at the concat
boundary; the residue of `seamV` is then only the `mv a1,s0 ; mv a0,s1` register
staging (straight-line). -/
theorem concatValueStrSeam_readback {mL mem : Mem} {new srcL : Nat} {sL sR : String}
    (hLsrc : CStr mL srcL sL.toList)
    (hLcopy : ∀ k, k < sL.toList.length → mem[(new + k)]? = mL[(srcL + k)]?)
    (hR : CString mem (new + sL.toList.length) sR) :
    CString mem new (sL ++ sR) :=
  concatReadback hLsrc hLcopy hR

/-! ## `concatCBlockTriple_of` — `concatHeapCore` with the landed slots discharged

The whole concat C-block `Triple P Q`, with the three `MallocContract` slots
(`malloc`, `free1`, `free2`) DISCHARGED from `M`, and the remaining four callees
(two `strlen`, `memcpy`, `strcpy`, `value_str`) + the seven marshalling seams
threaded as arguments.  This is `concatHeapCore` with its most reusable callee
slots pre-plugged — the caller supplies only the call-specific contract
instantiations (whose entry/exit predicates are call data) and the straight-line
seam bridges. -/
theorem concatCBlockTriple_of
    (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R))
    -- malloc call data
    (exts : List (Nat × Nat)) (nMal : Nat) (spM rM : BitVec 64)
    (mMal : Std.ExtHashMap Nat (BitVec 8)) (hnMal : nMal ≤ maxReq)
    -- free call data (two scratch extents, at their own live-lists/geometry)
    (exts1 : List (Nat × Nat)) (q1 n1 : Nat) (sp1 r1 : BitVec 64)
    (m1 : Std.ExtHashMap Nat (BitVec 8))
    (exts2 : List (Nat × Nat)) (q2 n2 : Nat) (sp2 r2 : BitVec 64)
    (m2 : Std.ExtHashMap Nat (BitVec 8))
    -- the four call-threaded callee contracts (entry/exit are call data ⇒ arguments)
    {P S1 S1' S2 S2' M1 M1' M2 M2' Smid V V' Q : Config → Prop}
    (strlenL : Triple S1 S1') (strlenR : Triple S2 S2')
    (memcpy : Triple M1 M1') (strcpy : Triple M2 M2') (valueStr : Triple V V')
    -- the seven marshalling seam bridges (SegPre↔entry straight-line, NAMED residuals)
    (seam0 : Triple P S1) (seam1 : Triple S1' S2)
    (seamM : Triple S2' (ConcatMallocPre M g exts nMal spM rM mMal))
    (seamMc : Triple (ConcatMallocPost M g exts nMal spM rM mMal) M1)
    (seamSc : Triple M1' M2) (seamEnd : Triple M2' Smid)
    (seamF1 : Triple Smid (ConcatFreePre M g exts1 q1 n1 sp1 r1 m1))
    (seamF2 : Triple (ConcatFreePost M g exts1 q1 n1 sp1 r1 m1)
      (ConcatFreePre M g exts2 q2 n2 sp2 r2 m2))
    (seamV : Triple (ConcatFreePost M g exts2 q2 n2 sp2 r2 m2) V)
    (seamQ : Triple V' Q) :
    Triple P Q :=
  concatHeapCore
    (strlenL := strlenL) (strlenR := strlenR)
    (malloc := concatMallocSlot M g exts nMal spM rM mMal hnMal)
    (seam0 := seam0) (seam1 := seam1) (seamM := seamM)
    (memcpy := memcpy) (strcpy := strcpy)
    (seamMc := seamMc) (seamSc := seamSc) (seamEnd := seamEnd)
    (free1 := concatFreeSlot M g exts1 q1 n1 sp1 r1 m1)
    (free2 := concatFreeSlot M g exts2 q2 n2 sp2 r2 m2)
    (valueStr := valueStr)
    (seamF1 := seamF1) (seamF2 := seamF2) (seamV := seamV) (seamQ := seamQ)

#print axioms concatMallocSlot
#print axioms concatFreeSlot
#print axioms concatOOM_prune
#print axioms concatValueStrSeam_readback
#print axioms concatCBlockTriple_of

end Vsa.Sim
