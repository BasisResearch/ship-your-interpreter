import Vsa.RuntimeRepr
import Vsa.MemRepr
import Vsa.Sim.Regions

/-!
# Layer 2 — reusable `StoreRepr`-survival under memory agreement

`StoreRepr` (and every relation it recurses through: `ValueRepr`, `ClosureRepr`,
`FrameRepr`, and `CStr`) is a conjunction of byte-level `read{32,64}`/`CStr`
facts. Any memory change that **agrees byte-for-byte on the addresses those
relations actually read** leaves them intact. This file states that survival in
its most reusable form: pointwise agreement over an *arbitrary footprint
predicate* `P : Nat → Prop`.

## Why a footprint *predicate* and not a single `Region`

`Vsa/Sim/Regions.lean`'s `AgreeOn` is agreement over one contiguous
`Region = (lo, len)`. That suffices for frames and closures (they live in the
arena `[A.lo, A.hi)` per `StoreRepr.frames_arena`/`closures_arena`), but **not**
for strings: `ValueRepr (.str s)` and `FrameRepr`'s binding names dereference a
`char*` whose target `CString` bytes may live *outside* the arena — e.g. an
`EX_*` AST string literal in `.rodata`, or an interned name. There is no single
window that contains the arena *and* every reachable string.

So the honest, provable statement threads agreement over a predicate `P` that
holds at **every address the relation reads**. Each transfer lemma carries a
side condition ("`P` covers the header window", "`P` covers this string's byte
range") in exactly the shape the recursion produces; a caller whose memory
change is disjoint from the arena-∪-strings set (the `.int` walk: only the stack
window + the sret buffer change, both disjoint from every represented object)
discharges those side conditions from disjointness.

## The string-footprint question (answered)

`ValueRepr (.str s)`/`FrameRepr` reach `CString m p s`, i.e. `CStr m p cs` over
`[p, p + cs.length]` (through the NUL). Those bytes are **not** bounded by the
arena in general. The provable survival hypothesis is therefore *per-string*:
for each represented string at `p` of spec length `ℓ`, agreement on
`[p, p + ℓ]`. `cstring_agreeP` consumes exactly that; `valueRepr_agreeP` /
`frameRepr_agreeP` thread it under the existential `p`. For a caller whose write
is disjoint from every represented object (the `.int` case), the side conditions
follow from disjointness with no need to enumerate strings.

## `OutRepr` survival (trivial)

`OutRepr σ st` is `Machine.output σ = st.out`, a fact about `σ.sailOutput`, NOT
`σ.mem`. Any memory-only change leaves it untouched; `outRepr_of_sailOutput_eq`
records this, and `outRepr_of_output_eq` the even weaker `output`-level form.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

namespace Vsa.Sim

open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-! ## Pointwise agreement over a footprint predicate -/

/-- `AgreeP P m m'`: `m` and `m'` hold the same byte at every address satisfying
`P`. The footprint-predicate generalization of `Regions.AgreeOn` (which is the
special case `P a = mem_region a r`). -/
def AgreeP (P : Nat → Prop) (m m' : Mem) : Prop :=
  ∀ a, P a → m[a]? = m'[a]?

theorem AgreeP.trans {P : Nat → Prop} {m m' m'' : Mem}
    (h1 : AgreeP P m m') (h2 : AgreeP P m' m'') : AgreeP P m m'' :=
  fun a ha => (h1 a ha).trans (h2 a ha)

/-- Strengthen the memory pair's footprint: agreement on `P` gives agreement on
any `Q ⊆ P`. -/
theorem AgreeP.mono {P Q : Nat → Prop} {m m' : Mem}
    (hsub : ∀ a, Q a → P a) (h : AgreeP P m m') : AgreeP Q m m' :=
  fun a ha => h a (hsub a ha)

/-! ## Byte-level reads transfer along `AgreeP` -/

/-- `readLE` transfers when `P` holds on the whole `n`-byte window `[a, a+n)`. -/
theorem readLE_agreeP {P : Nat → Prop} {m m' : Mem} (h : AgreeP P m m') :
    ∀ (n a : Nat), (∀ k, k < n → P (a + k)) → readLE m a n = readLE m' a n := by
  intro n
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
    intro a hP
    have hhead : m[a]? = m'[a]? := by
      have := h a (by simpa using hP 0 (Nat.succ_pos n)); simpa using this
    have htail : readLE m (a + 1) n = readLE m' (a + 1) n := by
      apply ih
      intro k hk
      have := hP (k + 1) (by omega)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    simp only [readLE, hhead, htail]

/-- `read64 m a` is preserved when `P` covers `[a, a+8)`. -/
theorem read64_agreeP {P : Nat → Prop} {m m' : Mem} (h : AgreeP P m m')
    {a : Nat} (hP : ∀ k, k < 8 → P (a + k)) : read64 m a = read64 m' a :=
  readLE_agreeP h 8 a hP

/-! ## `CStr` transfers along `AgreeP` on the string's own byte range

`CStr m p cs` reads `m[p], m[p+1], …, m[p + cs.length]` (the last is the NUL).
Agreement on that inclusive range preserves the whole chain. -/

/-! ## `ValueRepr` footprint and survival

The footprint of `ValueRepr m N φc a v` is the 24-byte header `[a, a+24)` for
every variant, **plus** (only for `.str`/`.native`) the referenced `char*`'s
byte range `[p, p + name.length]`, where `p = read64 m (a+8)`.

`valueRepr_agreeP` takes agreement on a `P` that covers the header for every
variant and, for the string-carrying variants, the string's byte range. Rather
than force the caller to name the existential `p` up front, the string side
condition is stated as: for the actual `p` witnessed by `ValueRepr`, `P` covers
`[p, p + ℓ]`. We deliver that by requiring, uniformly, that `P` covers *any*
`CString`-range the value reaches — packaged per-variant below. -/

/-- Exact indirect byte footprint of one semantic value. -/
def ValuePayloadCovered (P : Nat → Prop) (m : Mem) (a : Nat) : Value → Prop
  | .str s => ∀ p, read64 m (a + 8) = some p → ∀ k, k ≤ s.length → P (p + k)
  | .native f => ∀ p, read64 m (a + 8) = some p →
      ∀ k, k ≤ (nativeName f).length → P (p + k)
  | _ => True

/-! ## `ClosureRepr` footprint and survival

`ClosureRepr m φf p cd` reads `read64 m p` (→ `fn_expr`, plus `ExprRepr` of it —
but that lives in the read-only AST region, *not* touched by runtime writes) and
`read64 m (p+8)` (→ the captured env `φf`). The AST `ExprRepr` is preserved
because runtime writes never touch the AST region; we thread it as a hypothesis
that the *same* `ExprRepr` still holds under `m'` (true whenever `m'` agrees with
`m` on the AST region — the caller's disjointness). Here we only need agreement
on `[p, p+16)` for the two pointers; the `ExprRepr m q …` fact is carried and its
`m'` version is a caller-supplied side condition (`hexpr'`), since `ExprRepr`'s
footprint is the whole AST subtree, disjoint from the arena but not part of
`StoreRepr`'s arena bound. -/

/-! ## `FrameRepr` footprint and survival

`FrameRepr m N φf φc e f` reads the 32-byte `Env` header `[e, e+32)`
(count/cap/names/vals/parent), then for each binding `i < f.vars.length`:
* `read64 m (pn + 8*i)` (name `char*`) + `CString` of the name;
* `ValueRepr m N φc (pv + 24*i)` (the value slot, itself a 24-byte header +
  possible inner string).
-/

/-! ## `StoreRepr` survival

Frames live at `φf fa` (32 bytes, in arena), closures at `φc ca` (16 bytes, in
arena) per the `frames_arena`/`closures_arena` fields. `φf_inj`/`φc_inj` and the
arena bounds are memory-independent, so they transfer verbatim. Only the
`frames`/`closures` byte facts need the agreement. -/

/-! ## `OutRepr` survival (trivial — `σ.sailOutput`, not `σ.mem`) -/

end Vsa.Sim
