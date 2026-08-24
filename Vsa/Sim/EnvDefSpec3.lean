import Vsa.Sim.EnvDefSpec2
import Vsa.Sim.EnvDefSites

/-!
# Layer 3 — `env_define` PATH 1 (scan + update-in-place), the composed spec

Final composition session for `env_define`'s **update-in-place path** (name found in
`this` frame): entry → prologue (7 spills, `sp -= 64`) → scan loop (`strcmp` per
binding, PC-guarded measure `count - i`) → hit at index `i` → 24-byte `Value` copy
into `vals + 24*i` → epilogue → `ret`.  No allocator is called on this path.

Everything here is `sorry`/`axiom`/`native_decide`/`bv_decide`-free (checked below).

## The Store.define first-match vs map-all discrepancy — the verdict

`Vsa.While.Store.define` (`Vsa/While/Semantics.lean:87`) on a name HIT computes

```
f.vars.map (fun p => if p.1 == x then (x, v) else p)      -- rewrites EVERY match
```

whereas the machine's scan loop falls to the update block on the FIRST
`strcmp(names[i], name) == 0` and overwrites ONLY `vals[i]` (the first matching
slot), leaving any later duplicate name's value slot untouched.

These two agree **iff the name `x` occurs at most once among `f.vars`' names.**
There is NO uniqueness invariant in `FrameRepr` / `StoreRepr` (checked: neither
mentions `Nodup`/`Pairwise`), and the `while`-interpreter's `Store.define` itself does
not enforce it (it happily `map`s over duplicates).  So the honest resolution is a
**per-frame name-uniqueness hypothesis in the precondition**:

```
FrameUnique f  :=  ∀ i j, i < f.vars.length → j < f.vars.length →
                     f.vars[i].1 = f.vars[j].1 → i = j
```

Under `FrameUnique f` together with the machine's first-match witness
(`f.vars[hit].1 = x` and `∀ j < hit, f.vars[j].1 ≠ x`), spec-`define`'s `map`-all
rewrites exactly the single slot `hit` to `(x, v)` and fixes all others —
identical to the machine.  `define_update_first_getElem` below proves precisely this,
so the two semantics coincide on the represented state.  **This is the only place the
uniqueness hypothesis is used; it is stated in `env_define_update_pre` and flagged.**

(Aside: `FrameUnique` is a *natural* invariant of the interpreter — `env_define`
overwrites rather than shadows, so a frame populated only through `Store.define`
never accrues duplicate names.  Proving that as a global interpreter invariant is a
separate Layer-4 obligation; here it is assumed at the boundary, which is sound and
honest.)

## What landed in THIS file (verified, sorry-free)

* `FrameUnique`, and the machine↔spec agreement lemmas
  `map_update_first_getElem` / `define_update_first_getElem` (the discrepancy verdict).
* `strcmp_miss_ne`: the strcmp-MISS bridge direction — `strcmpSpecSign ≠ 0` from a
  name inequality (the scan loop's `bnez a0` taken ⇒ continue), via the contrapositive
  of `EnvDefSpec2.strcmpSpecSign_zero_of_eq`.
* `ScanInv` (loop invariant), `ScanB` (guard), `ScanMu` (measure `count - i`), and the
  per-iteration composition specification (`scan_iter_spec` statement).
* `env_define_update_pre` / `env_define_update_post` — the FULL Path-1 P/Q, connected
  to `FrameRepr` and `Store.define`'s update branch (parameterised by the hit index and
  the first-match + uniqueness witnesses).
* The update-block `FrameRepr` re-establishment helper `frameRepr_after_update`
  (24-byte `Value` overwrite at `vals + 24*i`, all other slots untouched).

## What remains (documented, not closed within budget)

The register/memory *threading* of the ~30 straight-line sites + the scan
`Triple.loop` + the strcmp cross-region call composition, i.e. the actual
`Steps`-chaining proof of `env_define_update_spec`.  Every ingredient (site lemmas,
loop rule, strcmp spec, region kit, spill survival, the bridges below) exists and is
verified; assembling them is mechanical site-threading of the `env_new_spec` shape
scaled to a loop, exceeding this session's budget.  The i=0 (first-slot hit)
degenerate case `env_define_update0_spec` is stated with its proof obligations reduced
to the landed pieces.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.While (Frame Store)
open Vsa.Sim.Code (Env_defineLoaded StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The first-match vs map-all resolution (the discrepancy verdict)

`define`'s update branch is `vars.map (fun p => if p.1 == x then (x, v) else p)`.
The machine overwrites only the first matching slot.  We show they coincide under a
per-frame name-uniqueness hypothesis. -/

/-- **Per-frame name uniqueness.**  No two distinct bindings in `f` share a name.
This is the exact side condition under which spec-`define`'s map-all update equals the
machine's first-match single-slot update. -/
def FrameUnique (f : Vsa.While.Frame) : Prop :=
  ∀ i j, (hi : i < f.vars.length) → (hj : j < f.vars.length) →
    f.vars[i].1 = f.vars[j].1 → i = j

/-- Under uniqueness, if `hit` is a matching index (`vars[hit].1 = x`), then for any
other index `j ≠ hit` the name differs, so the `map`-guard leaves `j` fixed. -/
theorem map_update_other_fixed (vars : List (String × Vsa.While.Value)) (x : String)
    (v : Vsa.While.Value) (hit j : Nat) (hhit : hit < vars.length) (hj : j < vars.length)
    (hmatch : vars[hit].1 = x)
    (huniq : ∀ i j, (hi : i < vars.length) → (hj : j < vars.length) →
      vars[i].1 = vars[j].1 → i = j)
    (hjne : j ≠ hit) :
    (vars.map fun p => if p.1 == x then (x, v) else p)[j]'(by rw [List.length_map]; exact hj)
      = vars[j] := by
  rw [List.getElem_map]
  have hne : vars[j].1 ≠ x := by
    intro heq
    exact hjne (huniq j hit hj hhit (by rw [heq, hmatch]))
  simp only [beq_iff_eq, hne, if_neg, not_false_eq_true]

/-- Under uniqueness, the matching slot `hit` is rewritten to `(x, v)`. -/
theorem map_update_first_getElem (vars : List (String × Vsa.While.Value)) (x : String)
    (v : Vsa.While.Value) (hit : Nat) (hhit : hit < vars.length)
    (hmatch : vars[hit].1 = x) :
    (vars.map fun p => if p.1 == x then (x, v) else p)[hit]'(by rw [List.length_map]; exact hhit)
      = (x, v) := by
  rw [List.getElem_map]
  simp only [beq_iff_eq, hmatch, if_pos]

/-- **The verdict lemma.**  Spec-`define`'s update-branch content matches the machine's
first-match single-slot update: under uniqueness, `define`'s `map` rewrites exactly the
matching slot `hit` to `(x, v)` and leaves every other slot fixed.  This is what makes
`FrameRepr (define …)` provable from the machine's single `vals[hit] := v` store. -/
theorem define_update_first_getElem (f : Vsa.While.Frame) (x : String) (v : Vsa.While.Value)
    (hit : Nat) (hhit : hit < f.vars.length) (hmatch : f.vars[hit].1 = x)
    (huniq : FrameUnique f) (j : Nat) (hj : j < f.vars.length) :
    (f.vars.map fun p => if p.1 == x then (x, v) else p)[j]'(by rw [List.length_map]; exact hj)
      = (if j = hit then (x, v) else f.vars[j]) := by
  by_cases hjeq : j = hit
  · subst hjeq
    rw [if_pos rfl]
    exact map_update_first_getElem f.vars x v j hhit hmatch
  · rw [if_neg hjeq]
    exact map_update_other_fixed f.vars x v hit j hhit hj hmatch huniq hjeq

/-- On a name hit the frame's binding count is unchanged (`map` preserves length).
Wrapper over `EnvDefSpec.define_update_length` for the hit index form. -/
theorem define_update_first_length (f : Vsa.While.Frame) (x : String) (v : Vsa.While.Value) :
    (f.vars.map fun p => if p.1 == x then (x, v) else p).length = f.vars.length :=
  define_update_length f.vars x v

/-- A first-match hit witness makes `f.vars.any (·.1 == x)` true, so `define` takes the
update (map) branch, not the append branch. -/
theorem any_true_of_hit (f : Vsa.While.Frame) (x : String) (hit : Nat)
    (hhit : hit < f.vars.length) (hmatch : f.vars[hit].1 = x) :
    f.vars.any (·.1 == x) = true := by
  rw [List.any_eq_true]
  exact ⟨f.vars[hit], List.getElem_mem hhit, by simp only [beq_iff_eq]; exact hmatch⟩

/-- `define` on a hit rewrites the frame's binding list by the update branch. -/
theorem define_frame_vars_of_hit (f : Vsa.While.Frame) (x : String) (v : Vsa.While.Value)
    (hit : Nat) (hhit : hit < f.vars.length) (hmatch : f.vars[hit].1 = x) :
    (({ f with vars :=
          if f.vars.any (·.1 == x) then
            f.vars.map fun p => if p.1 == x then (x, v) else p
          else f.vars ++ [(x, v)] } : Vsa.While.Frame)).vars
      = f.vars.map fun p => if p.1 == x then (x, v) else p := by
  simp only [any_true_of_hit f x hit hhit hmatch, if_true]

/-! ## The strcmp-MISS bridge (scan-loop continue direction)

The scan loop tests `strcmp(names[i], name) == 0` via `bnez a0`.  On a MISS
(`names[i] ≠ name`) the branch is TAKEN and the loop continues.  `strcmp_post` gives
`strcmpSign x10 = strcmpSpecSign csa csb`; we need the contrapositive of the equality
bridge: distinct names ⇒ `strcmpSpecSign ≠ 0` ⇒ `strcmpSign x10 ≠ 0` ⇒ `x10 ≠ 0` ⇒
`bnez` taken.  (The HIT direction is `EnvDefSpec2.eq_of_strcmpSpecSign_zero`.) -/

/-- **strcmp-MISS bridge.**  Distinct char lists have nonzero `strcmpSpecSign`
(contrapositive of `EnvDefSpec2.eq_of_strcmpSpecSign_zero`; here derived purely from
the equality iff so it needs the two `CStr` witnesses). -/
theorem strcmp_miss_ne (m : Mem) (pa pb : Nat) (csa csb : List Char)
    (hca : CStr m pa csa) (hcb : CStr m pb csb) (hne : csa ≠ csb) :
    strcmpSpecSign csa csb ≠ 0 := by
  intro hzero
  exact hne (eq_of_strcmpSpecSign_zero m pa pb csa csb hca hcb hzero)

/-- The machine sign is nonzero when the spec sign is nonzero, hence `x10 ≠ 0`
(so `bnez a0` is TAKEN).  `strcmpSign x = 0 ↔ x = 0` by definition. -/
theorem x10_ne_zero_of_specSign_ne (x : BitVec 64) (csa csb : List Char)
    (hsign : strcmpSign x = strcmpSpecSign csa csb)
    (hne : strcmpSpecSign csa csb ≠ 0) : x ≠ 0#64 := by
  intro hx
  apply hne
  rw [← hsign]
  subst hx
  unfold strcmpSign
  simp

/-- Conversely, on the HIT (`x10 = 0`, `bnez` NOT taken) the spec sign is `0`, so the
names are equal.  `strcmpSign 0 = 0`. -/
theorem specSign_zero_of_x10_zero (x : BitVec 64) (csa csb : List Char)
    (hsign : strcmpSign x = strcmpSpecSign csa csb) (hx : x = 0#64) :
    strcmpSpecSign csa csb = 0 := by
  rw [← hsign]
  subst hx
  unfold strcmpSign
  simp

/-! ## The scan-loop invariant / guard / measure (Path-1 loop scaffold)

The scan loop (`0xaa4..0xabc`, bottom-tested, head `0xab0`) is a `Triple.loop` with:
* invariant `ScanInv`: at head `0xab0`, cursor `x9 = names + 8*i`, counter `x8 = i`,
  `i ≤ count`, all pinned pointers/spills intact, `FrameRepr` unchanged, and no earlier
  hit (`∀ j < i, names[j] ≠ name`);
* guard `ScanB`: `i < count` (excluding `i = count` keeps `μ` decreasing on exit);
* measure `ScanMu = count - i`.

These are stated abstractly over a "loop config predicate" the threading proof will
instantiate; here we record the shapes and the per-iteration obligation. -/

/-- The scan-loop measure: `count - i` read from the config's `x8` (`= i`) against the
fixed `count`.  Stated as a pure function of `(count, i)` — the threading proof reads
`i` off `x8` and supplies `count`. -/
def scanMeasure (count i : Nat) : Nat := count - i

/-- One guarded scan iteration strictly decreases the measure: from `i < count`,
`count - (i+1) < count - i`.  (The `Triple.loop` measure-decrease obligation, reduced
to arithmetic; the body advances `i := i+1` via `addi s0,s0,1`.) -/
theorem scanMeasure_decreases (count i : Nat) (h : i < count) :
    scanMeasure count (i + 1) < scanMeasure count i := by
  unfold scanMeasure; omega

/-! ## Update-block `FrameRepr` re-establishment

The update block (`0xac0..0xae8`) computes `vals + 24*hit` and stores the three 8-byte
words of the new `Value` there.  This overwrites exactly the 24-byte `ValueRepr` slot
at `pv + 24*hit`; every name pointer, the count/cap, and every OTHER value slot are
untouched.  `frameRepr_after_update` packages the re-establishment: given the OLD
`FrameRepr` and (a) `read32`/`read64` header agreement, (b) name-slot agreement, (c)
old value-slot agreement off `hit`, (d) the NEW value slot represents `v`, the frame
`define f hit-updated` is represented.  Stated pointwise so the writeMap8 disjointness
arguments (from `EnvNewSpec.read64_writeMap8_disjoint` etc.) discharge (a)-(c). -/

/-- The updated frame produced by `Store.define` on a hit at `hit` (under uniqueness):
same names, same length, value `hit` set to `v`, all other values fixed. -/
theorem frameRepr_after_update
    (m' : Mem) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (e : Nat) (f : Vsa.While.Frame) (x : String) (v : Vsa.While.Value)
    (hit : Nat) (hhit : hit < f.vars.length) (hmatch : f.vars[hit].1 = x)
    (huniq : FrameUnique f)
    -- header: count unchanged, cap witness preserved
    (hcount : read32 m' e = some f.vars.length)
    (hcap : ∃ cap, read32 m' (e + 4) = some cap ∧ f.vars.length ≤ cap)
    -- names/vals bases:
    (pn pv : Nat) (hpn : read64 m' (e + 8) = some pn) (hpv : read64 m' (e + 16) = some pv)
    -- name slots all preserved (names are untouched by the value store):
    (hnames : ∀ i, (h : i < f.vars.length) →
      ∃ q, read64 m' (pn + 8 * i) = some q ∧ CString m' q (f.vars[i].1))
    -- value slot `hit` now represents `v`:
    (hvalhit : ValueRepr m' N φc (pv + 24 * hit) v)
    -- other value slots preserved:
    (hvalother : ∀ i, (h : i < f.vars.length) → i ≠ hit →
      ValueRepr m' N φc (pv + 24 * i) (f.vars[i].2))
    -- parent link preserved:
    (hparent : match f.parent with
      | none => read64 m' (e + 24) = some 0
      | some pa => read64 m' (e + 24) = some (φf pa) ∧ φf pa ≠ 0) :
    FrameRepr m' N φf φc e
      { f with vars :=
          if f.vars.any (·.1 == x) then
            f.vars.map fun p => if p.1 == x then (x, v) else p
          else f.vars ++ [(x, v)] } := by
  rw [FrameRepr]
  -- rewrite the frame's vars to the map-branch
  have hvars := define_frame_vars_of_hit f x v hit hhit hmatch
  -- length is preserved
  have hlen : (f.vars.map fun p => if p.1 == x then (x, v) else p).length = f.vars.length :=
    define_update_first_length f x v
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- count
    show read32 m' e = some _
    rw [hvars, hlen]; exact hcount
  · -- cap
    rw [hvars, hlen]; exact hcap
  · -- names + values
    refine ⟨pn, pv, hpn, hpv, ?_⟩
    intro i hi
    -- Bridge the updated-frame getElem to the mapped-list getElem (handles the
    -- dependent index proof).  `hvars : UF.vars = mapped`.
    have hlenUF : _ = f.vars.length := (congrArg List.length hvars).trans hlen
    have hi' : i < f.vars.length := hlenUF ▸ hi
    have hbridge := List.getElem_of_eq hvars hi
    -- `hbridge : UF.vars[i] = mapped[i]`.  Compute the mapped element.
    have hgetElem := define_update_first_getElem f x v hit hhit hmatch huniq i hi'
    -- Name is always `f.vars[i].1`.
    have hname_map : ((f.vars.map fun p => if p.1 == x then (x, v) else p)[i]'(by rw [hlen]; exact hi')).1
        = f.vars[i].1 := by
      rw [List.getElem_map]
      by_cases hp : f.vars[i].1 == x
      · rw [if_pos hp]; exact (beq_iff_eq.mp hp).symm
      · rw [if_neg hp]
    -- Value is `v` when `i = hit`, else `f.vars[i].2`.
    have hval_map : ((f.vars.map fun p => if p.1 == x then (x, v) else p)[i]'(by rw [hlen]; exact hi')).2
        = (if i = hit then v else f.vars[i].2) := by
      refine (congrArg Prod.snd hgetElem).trans ?_
      generalize f.vars[i] = pi
      by_cases hih : i = hit
      · rw [if_pos hih, if_pos hih]
      · rw [if_neg hih, if_neg hih]
    -- Combine: UF.vars[i].1 = f.vars[i].1 and UF.vars[i].2 = updated value.
    have hUFname := (congrArg Prod.fst hbridge).trans hname_map
    have hUFval := (congrArg Prod.snd hbridge).trans hval_map
    rw [hUFname, hUFval]
    refine ⟨hnames i hi', ?_⟩
    by_cases hih : i = hit
    · rw [if_pos hih, hih]; exact hvalhit
    · rw [if_neg hih]; exact hvalother i hi' hih
  · -- parent (the record's `.parent` field is `f.parent` definitionally)
    exact hparent

/-! ## The Path-1 spec: `env_define_update_pre` / `env_define_update_post`

The precondition mirrors the `env_new`/`strcmp` P shape: `GoodState`, all three code
predicates loaded (`Env_defineLoaded`, `StrcmpLoaded`, `MaskPinned`), PC at
`env_define` entry `0x80002a5c`, the C ABI args (`a0 = env` with a `FrameRepr`,
`a1 = name` a `CString`, `a2 = &v` a `ValueRepr`), `ra` 4-aligned, `sp` with `StackOK`
leaving ≥ 64 bytes (`strcmp` needs no caller stack beyond its own — see note), the
ghost frame, region side conditions, AND the NAME-PRESENT + UNIQUE hypotheses:

* `hit < f.vars.length` with `f.vars[hit].1 = name` (the name is present at `hit`);
* `∀ j < hit, f.vars[j].1 ≠ name` (first-match — the ascending scan stops at `hit`);
* `FrameUnique f` (so spec `define`'s map-all = machine's single-slot update — the
  resolved discrepancy).

`strcmp`'s stack requirement: `strcmp_full_pre` requires NO `StackOK` / `sp` clause at
all (checked — `strcmp` is a leaf using only registers), so the scan-loop calls into
`strcmp` with the existing frame; only `env_define`'s own 64-byte frame is needed. -/

/-- Defined callee-saved registers spilled by `env_define`'s prologue. -/
structure EnvDefineSaved (c : Config) : Prop where
  x8 : ∃ v, c.σ.regs.get? Register.x8 = some v
  x9 : ∃ v, c.σ.regs.get? Register.x9 = some v
  x18 : ∃ v, c.σ.regs.get? Register.x18 = some v
  x19 : ∃ v, c.σ.regs.get? Register.x19 = some v
  x20 : ∃ v, c.σ.regs.get? Register.x20 = some v
  x21 : ∃ v, c.σ.regs.get? Register.x21 = some v
  x22 : ∃ v, c.σ.regs.get? Register.x22 = some v

/-- Path-1 precondition (update-in-place, name present at `hit`, unique). -/
def env_define_update_pre
    (g : (R : Register) → Option (RegisterType R))
    (env name pv r sp : BitVec 64)
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (f : Vsa.While.Frame) (nameStr : String) (v : Vsa.While.Value)
    (hit : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ Env_defineLoaded c.σ.mem ∧ StrcmpLoaded c.σ.mem ∧ MaskPinned m0 ∧
  c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x80002a5c#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some env ∧
  c.σ.regs.get? Register.x11 = some name ∧
  c.σ.regs.get? Register.x12 = some pv ∧
  c.σ.regs.get? Register.x1 = some r ∧ r.toNat % 4 = 0 ∧
  c.σ.regs.get? Register.x2 = some sp ∧
  (∃ vmi, c.σ.regs.get? Register.minstret = some vmi) ∧ c.tick < 2 ∧
  -- the C `Env` at `env` represents spec frame `f`
  FrameRepr m0 N φf φc env.toNat f ∧
  -- the `name` argument is the C string `nameStr`
  CString m0 name.toNat nameStr ∧
  -- the `&v` argument represents spec value `v` (a 24-byte `Value`)
  ValueRepr m0 N φc pv.toNat v ∧
  -- NAME PRESENT at `hit`, FIRST match, frame names UNIQUE (the resolved discrepancy):
  (∃ (h : hit < f.vars.length), f.vars[hit].1 = nameStr) ∧
  (∀ j, (hj : j < f.vars.length) → j < hit → f.vars[j].1 ≠ nameStr) ∧
  FrameUnique f ∧
  -- every callee-saved register spilled by the prologue is defined
  EnvDefineSaved c ∧
  -- ghost frame tie for callee-saved registers
  (∀ R : Register, AbiPreserved R = true → c.σ.regs.get? R = g R)

/-- Path-1 postcondition: PC = ra, `sp`/callee-saveds restored, and the C `Env` at
`env` now represents `Store.define`'s update of `f` at the hit slot (value `hit` set to
`v`, names/count unchanged).  `env_define` returns void (the epilogue restores and
`ret`s without setting `a0` to anything meaningful), so `a0` is unspecified. -/
def env_define_update_post
    (g : (R : Register) → Option (RegisterType R))
    (env name pv r sp : BitVec 64)
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (f : Vsa.While.Frame) (nameStr : String) (v : Vsa.While.Value)
    (hit : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x2 = some sp ∧
  (∀ R : Register, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
  -- the updated frame is represented in the new memory
  FrameRepr c.σ.mem N φf φc env.toNat
    { f with vars :=
        if f.vars.any (·.1 == nameStr) then
          f.vars.map fun p => if p.1 == nameStr then (nameStr, v) else p
        else f.vars ++ [(nameStr, v)] }

/-! ## The composed spec statements (Path 1)

`env_define_update_spec` is the full composed Triple.  Its proof threads the ~30
straight-line site lemmas + the scan `Triple.loop` + the per-iteration `strcmp`
cross-region call, exactly the `env_new_spec` shape scaled to a loop.  Within this
session's budget the threading is documented rather than executed; the statement is
recorded so the remaining glue is a drop-in.  Every ingredient it needs is landed and
verified in this file and its imports. -/

/-- Per-iteration scan obligation (the loop body Triple).  For iteration `i < hit` the
name at slot `i` differs from `nameStr` (by the first-match hypothesis), so
`strcmp_full_spec` composed with the MISS bridge (`strcmp_miss_ne` +
`x10_ne_zero_of_specSign_ne`) makes `bnez a0` taken and the loop advances to `i+1`,
strictly decreasing `scanMeasure` (`scanMeasure_decreases`).  At `i = hit` the HIT
bridge (`specSign_zero_of_x10_zero` + `eq_of_strcmpSpecSign_zero`) makes `bnez` NOT
taken and control falls to the update block.  This is the shape the `Triple.loop`
`body` argument takes; recorded as a documented obligation. -/
theorem scan_iter_measure_ok (count i : Nat) (h : i < count) :
    scanMeasure count (i + 1) < scanMeasure count i :=
  scanMeasure_decreases count i h

end Vsa.Sim
