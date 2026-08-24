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

theorem AgreeP.refl (P : Nat → Prop) (m : Mem) : AgreeP P m m := fun _ _ => rfl

theorem AgreeP.symm {P : Nat → Prop} {m m' : Mem} (h : AgreeP P m m') :
    AgreeP P m' m := fun a ha => (h a ha).symm

theorem AgreeP.trans {P : Nat → Prop} {m m' m'' : Mem}
    (h1 : AgreeP P m m') (h2 : AgreeP P m' m'') : AgreeP P m m'' :=
  fun a ha => (h1 a ha).trans (h2 a ha)

/-- Strengthen the memory pair's footprint: agreement on `P` gives agreement on
any `Q ⊆ P`. -/
theorem AgreeP.mono {P Q : Nat → Prop} {m m' : Mem}
    (hsub : ∀ a, Q a → P a) (h : AgreeP P m m') : AgreeP Q m m' :=
  fun a ha => h a (hsub a ha)

/-- Bridge from `Regions.AgreeOn r` to `AgreeP` over that region's membership. -/
theorem AgreeP.of_agreeOn {r : Region} {m m' : Mem} (h : AgreeOn r m m') :
    AgreeP (fun a => mem_region a r) m m' := h

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

/-- `read32 m a` is preserved when `P` covers `[a, a+4)`. -/
theorem read32_agreeP {P : Nat → Prop} {m m' : Mem} (h : AgreeP P m m')
    {a : Nat} (hP : ∀ k, k < 4 → P (a + k)) : read32 m a = read32 m' a :=
  readLE_agreeP h 4 a hP

/-- `read64 m a` is preserved when `P` covers `[a, a+8)`. -/
theorem read64_agreeP {P : Nat → Prop} {m m' : Mem} (h : AgreeP P m m')
    {a : Nat} (hP : ∀ k, k < 8 → P (a + k)) : read64 m a = read64 m' a :=
  readLE_agreeP h 8 a hP

/-- `readI64 m a` is preserved when `P` covers `[a, a+8)`. -/
theorem readI64_agreeP {P : Nat → Prop} {m m' : Mem} (h : AgreeP P m m')
    {a : Nat} (hP : ∀ k, k < 8 → P (a + k)) : readI64 m a = readI64 m' a := by
  simp only [readI64, read64_agreeP h hP]

/-! ## `CStr` transfers along `AgreeP` on the string's own byte range

`CStr m p cs` reads `m[p], m[p+1], …, m[p + cs.length]` (the last is the NUL).
Agreement on that inclusive range preserves the whole chain. -/

theorem cstr_agreeP {P : Nat → Prop} {m m' : Mem} (h : AgreeP P m m') :
    ∀ {p : Nat} {cs : List Char}, CStr m p cs →
      (∀ k, k ≤ cs.length → P (p + k)) → CStr m' p cs := by
  intro p cs hcstr
  induction hcstr with
  | @nil a hnul =>
    intro hP
    refine CStr.nil ?_
    have := h a (by simpa using hP 0 (Nat.zero_le _))
    rw [← this]; exact hnul
  | @cons a b cs hb hbne hb128 hrest ih =>
    intro hP
    refine CStr.cons (b := b) ?_ hbne hb128 (ih ?_)
    · have := h a (by simpa using hP 0 (Nat.zero_le _))
      rw [← this]; exact hb
    · intro k hk
      have := hP (k + 1) (by simp only [List.length_cons]; omega)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

/-- `CString` version of `cstr_agreeP`: agreement on `[p, p + s.length]` (through
the NUL) transfers `CString m p s`. -/
theorem cstring_agreeP {P : Nat → Prop} {m m' : Mem} (h : AgreeP P m m')
    {p : Nat} {s : String} (hcs : CString m p s)
    (hP : ∀ k, k ≤ s.length → P (p + k)) : CString m' p s := by
  obtain ⟨cs, hcstr, hs⟩ := hcs
  have hlen : cs.length = s.length := by rw [hs, String.length_ofList]
  exact ⟨cs, cstr_agreeP h hcstr (fun k hk => hP k (by omega)), hs⟩

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

/-- Header window predicate for a 24-byte `Value` at `a`. -/
def valHeader (a : Nat) : Nat → Prop := fun k => a ≤ k ∧ k < a + 24

theorem valHeader_read32 {P : Nat → Prop} {a : Nat}
    (hhdr : ∀ k, valHeader a k → P k) : ∀ k, k < 4 → P (a + k) :=
  fun k hk => hhdr _ ⟨by omega, by omega⟩

theorem valHeader_read32_off8 {P : Nat → Prop} {a : Nat}
    (hhdr : ∀ k, valHeader a k → P k) : ∀ k, k < 4 → P (a + 8 + k) :=
  fun k hk => hhdr _ ⟨by omega, by omega⟩

theorem valHeader_read64_off8 {P : Nat → Prop} {a : Nat}
    (hhdr : ∀ k, valHeader a k → P k) : ∀ k, k < 8 → P (a + 8 + k) :=
  fun k hk => hhdr _ ⟨by omega, by omega⟩

theorem valHeader_readI64_off8 {P : Nat → Prop} {a : Nat}
    (hhdr : ∀ k, valHeader a k → P k) : ∀ k, k < 8 → P (a + 8 + k) :=
  fun k hk => hhdr _ ⟨by omega, by omega⟩

theorem valHeader_read64_off16 {P : Nat → Prop} {a : Nat}
    (hhdr : ∀ k, valHeader a k → P k) : ∀ k, k < 8 → P (a + 16 + k) :=
  fun k hk => hhdr _ ⟨by omega, by omega⟩

/-- **`ValueRepr` survives an `AgreeP`** whose footprint `P` covers the 24-byte
header and every string byte the value dereferences.

`hhdr` : `P` covers `[a, a+24)`.
`hstr` : for the *actual* dereferenced `char*` `p` and its string `s`
  (`.str`/`.native`), `P` covers `[p, p + s.length]`. Stated as a hypothesis on
  the value's own `read64 m (a+8)` witness so the caller need not guess `p`. For
  the non-string variants it is unused (pass `fun _ _ _ _ => by omega` — vacuous).
-/
theorem valueRepr_agreeP {P : Nat → Prop} {m m' : Mem} (h : AgreeP P m m')
    {N : NativeAddrs} {φc : Addr → Nat} {a : Nat} {v : Value}
    (hhdr : ∀ k, valHeader a k → P k)
    (hstr : ∀ (p : Nat) (s : String), read64 m (a + 8) = some p →
      (∀ k, k ≤ s.length → P (p + k)))
    (hv : ValueRepr m N φc a v) : ValueRepr m' N φc a v := by
  cases v with
  | null =>
    simp only [ValueRepr] at hv ⊢
    rw [← read32_agreeP h (valHeader_read32 hhdr)]; exact hv
  | bool b =>
    simp only [ValueRepr] at hv ⊢
    obtain ⟨h0, h8⟩ := hv
    exact ⟨by rw [← read32_agreeP h (valHeader_read32 hhdr)]; exact h0,
      by rw [← read32_agreeP h (valHeader_read32_off8 hhdr)]; exact h8⟩
  | int n =>
    simp only [ValueRepr] at hv ⊢
    obtain ⟨h0, h8⟩ := hv
    exact ⟨by rw [← read32_agreeP h (valHeader_read32 hhdr)]; exact h0,
      by rw [← readI64_agreeP h (valHeader_readI64_off8 hhdr)]; exact h8⟩
  | str s =>
    simp only [ValueRepr] at hv ⊢
    obtain ⟨h0, p, hp, hpne, hcstr⟩ := hv
    refine ⟨by rw [← read32_agreeP h (valHeader_read32 hhdr)]; exact h0,
      p, by rw [← read64_agreeP h (valHeader_read64_off8 hhdr)]; exact hp, hpne, ?_⟩
    exact cstring_agreeP h hcstr (hstr p s hp)
  | closure ca =>
    simp only [ValueRepr] at hv ⊢
    obtain ⟨h0, h8, hne⟩ := hv
    exact ⟨by rw [← read32_agreeP h (valHeader_read32 hhdr)]; exact h0,
      by rw [← read64_agreeP h (valHeader_read64_off8 hhdr)]; exact h8, hne⟩
  | native f =>
    simp only [ValueRepr] at hv ⊢
    obtain ⟨h0, ⟨p, hp, hcstr⟩, h16⟩ := hv
    refine ⟨by rw [← read32_agreeP h (valHeader_read32 hhdr)]; exact h0,
      ⟨p, by rw [← read64_agreeP h (valHeader_read64_off8 hhdr)]; exact hp, ?_⟩,
      by rw [← read64_agreeP h (valHeader_read64_off16 hhdr)]; exact h16⟩
    exact cstring_agreeP h hcstr (hstr p _ hp)

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

/-- Closure header window predicate: `[p, p+16)`. -/
def closHeader (p : Nat) : Nat → Prop := fun k => p ≤ k ∧ k < p + 16

/-- **`ClosureRepr` survives an `AgreeP`** covering the 16-byte header, given the
`fn_expr` `ExprRepr` still holds under `m'` (its AST footprint being disjoint
from the write, a caller-supplied fact keyed to the witnessed `q`). -/
theorem closureRepr_agreeP {P : Nat → Prop} {m m' : Mem} (h : AgreeP P m m')
    {φf : Addr → Nat} {p : Nat} {cd : ClosureData}
    (hhdr : ∀ k, closHeader p k → P k)
    (hexpr' : ∀ q, read64 m p = some q → ExprRepr m q (.fn cd.name cd.params cd.body) →
      ExprRepr m' q (.fn cd.name cd.params cd.body))
    (hc : ClosureRepr m φf p cd) : ClosureRepr m' φf p cd := by
  obtain ⟨⟨q, hq, hqexpr⟩, henv, hne⟩ := hc
  refine ⟨⟨q, ?_, ?_⟩, ?_, hne⟩
  · rw [← read64_agreeP h (fun k hk => hhdr _ ⟨by omega, by omega⟩)]; exact hq
  · exact hexpr' q hq hqexpr
  · rw [← read64_agreeP h (fun k hk => hhdr _ ⟨by omega, by omega⟩)]; exact henv

/-! ## `FrameRepr` footprint and survival

`FrameRepr m N φf φc e f` reads the 32-byte `Env` header `[e, e+32)`
(count/cap/names/vals/parent), then for each binding `i < f.vars.length`:
* `read64 m (pn + 8*i)` (name `char*`) + `CString` of the name;
* `ValueRepr m N φc (pv + 24*i)` (the value slot, itself a 24-byte header +
  possible inner string).
-/

/-- Env header window predicate: `[e, e+32)`. -/
def envHeader (e : Nat) : Nat → Prop := fun k => e ≤ k ∧ k < e + 32

/-- **`FrameRepr` survives an `AgreeP`** covering the 32-byte env header, every
name-pointer slot, every name string, and every value slot (header + inner
string). The per-binding footprints are supplied via the existential
`pn`/`pv` witnesses. -/
theorem frameRepr_agreeP {P : Nat → Prop} {m m' : Mem} (h : AgreeP P m m')
    {N : NativeAddrs} {φf φc : Addr → Nat} {e : Nat} {f : Frame}
    (hhdr : ∀ k, envHeader e k → P k)
    -- name-pointer slots `[pn+8i, pn+8i+8)` and value headers `[pv+24i, pv+24i+24)`
    (hslots : ∀ pn pv, read64 m (e + 8) = some pn → read64 m (e + 16) = some pv →
      ∀ i, i < f.vars.length →
        (∀ k, k < 8 → P (pn + 8 * i + k)) ∧ (∀ k, valHeader (pv + 24 * i) k → P k))
    -- name strings `[qn, qn + name.length]`
    (hnames : ∀ pn pv, read64 m (e + 8) = some pn → read64 m (e + 16) = some pv →
      ∀ i, (hi : i < f.vars.length) → ∀ qn, read64 m (pn + 8 * i) = some qn →
        (∀ k, k ≤ (f.vars[i].1).length → P (qn + k)))
    -- inner value strings `[pval, pval + name.length]` for each value slot
    (hvalstr : ∀ pn pv, read64 m (e + 8) = some pn → read64 m (e + 16) = some pv →
      ∀ i, (hi : i < f.vars.length) →
        ∀ (pval : Nat) (s : String), read64 m (pv + 24 * i + 8) = some pval →
          (∀ k, k ≤ s.length → P (pval + k)))
    (hf : FrameRepr m N φf φc e f) : FrameRepr m' N φf φc e f := by
  obtain ⟨hcount, ⟨cap, hcap, hcaple⟩, ⟨pn, pv, hpn, hpv, hbind⟩, hpar⟩ := hf
  refine ⟨?_, ⟨cap, ?_, hcaple⟩, ⟨pn, pv, ?_, ?_, ?_⟩, ?_⟩
  · rw [← read32_agreeP h (fun k hk => hhdr _ ⟨by omega, by omega⟩)]; exact hcount
  · rw [← read32_agreeP h (fun k hk => hhdr _ ⟨by omega, by omega⟩)]; exact hcap
  · rw [← read64_agreeP h (fun k hk => hhdr _ ⟨by omega, by omega⟩)]; exact hpn
  · rw [← read64_agreeP h (fun k hk => hhdr _ ⟨by omega, by omega⟩)]; exact hpv
  · intro i hi
    obtain ⟨⟨qn, hqn, hqnstr⟩, hval⟩ := hbind i hi
    obtain ⟨hnameslot, hvalhdr⟩ := hslots pn pv hpn hpv i hi
    refine ⟨⟨qn, ?_, ?_⟩, ?_⟩
    · rw [← read64_agreeP h hnameslot]; exact hqn
    · exact cstring_agreeP h hqnstr (hnames pn pv hpn hpv i hi qn hqn)
    · exact valueRepr_agreeP h hvalhdr (fun pval s hpval => hvalstr pn pv hpn hpv i hi pval s hpval) hval
  · cases hp : f.parent with
    | none =>
      simp only [hp] at hpar ⊢
      rw [← read64_agreeP h (fun k hk => hhdr _ ⟨by omega, by omega⟩)]; exact hpar
    | some pa =>
      simp only [hp] at hpar ⊢
      obtain ⟨hpar1, hpar2⟩ := hpar
      exact ⟨by rw [← read64_agreeP h (fun k hk => hhdr _ ⟨by omega, by omega⟩)]; exact hpar1, hpar2⟩

/-! ## `StoreRepr` survival

Frames live at `φf fa` (32 bytes, in arena), closures at `φc ca` (16 bytes, in
arena) per the `frames_arena`/`closures_arena` fields. `φf_inj`/`φc_inj` and the
arena bounds are memory-independent, so they transfer verbatim. Only the
`frames`/`closures` byte facts need the agreement. -/

/-- **`StoreRepr` survives an `AgreeP`** whose footprint `P` covers every byte
each represented frame and closure reads (their arena header windows, plus each
frame's binding slots/strings and each closure's env pointer; closure `fn_expr`
`ExprRepr` is preserved by the AST-region side conditions `hexpr'`).

This is deliberately stated with the same per-object footprint hypotheses the
recursion produces; a caller with a *contiguous* write disjoint from arena-∪-AST
∪-strings supplies each from a single disjointness fact. -/
theorem storeRepr_agreeP {P : Nat → Prop} {m m' : Mem} (h : AgreeP P m m')
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {s : Store}
    (hframehdr : ∀ fa, fa < s.frames.size → ∀ k, envHeader (φf fa) k → P k)
    (hframeslots : ∀ fa, (hfa : fa < s.frames.size) →
      ∀ pn pv, read64 m (φf fa + 8) = some pn → read64 m (φf fa + 16) = some pv →
        ∀ i, i < s.frames[fa].vars.length →
          (∀ k, k < 8 → P (pn + 8 * i + k)) ∧ (∀ k, valHeader (pv + 24 * i) k → P k))
    (hframenames : ∀ fa, (hfa : fa < s.frames.size) →
      ∀ pn pv, read64 m (φf fa + 8) = some pn → read64 m (φf fa + 16) = some pv →
        ∀ i, (hi : i < s.frames[fa].vars.length) → ∀ qn, read64 m (pn + 8 * i) = some qn →
          (∀ k, k ≤ (s.frames[fa].vars[i].1).length → P (qn + k)))
    (hframevalstr : ∀ fa, (hfa : fa < s.frames.size) →
      ∀ pn pv, read64 m (φf fa + 8) = some pn → read64 m (φf fa + 16) = some pv →
        ∀ i, (hi : i < s.frames[fa].vars.length) →
          ∀ (pval : Nat) (str : String), read64 m (pv + 24 * i + 8) = some pval →
            (∀ k, k ≤ str.length → P (pval + k)))
    (hclohdr : ∀ ca, ca < s.closures.size → ∀ k, closHeader (φc ca) k → P k)
    (hcloexpr : ∀ ca, (hca : ca < s.closures.size) → ∀ q, read64 m (φc ca) = some q →
      ExprRepr m q (.fn s.closures[ca].name s.closures[ca].params s.closures[ca].body) →
        ExprRepr m' q (.fn s.closures[ca].name s.closures[ca].params s.closures[ca].body))
    (hs : StoreRepr m N A φf φc s) : StoreRepr m' N A φf φc s where
  frames fa hfa := frameRepr_agreeP h (hframehdr fa hfa) (hframeslots fa hfa)
    (hframenames fa hfa) (hframevalstr fa hfa) (hs.frames fa hfa)
  closures ca hca := closureRepr_agreeP h (hclohdr ca hca) (hcloexpr ca hca) (hs.closures ca hca)
  φf_inj := hs.φf_inj
  φc_inj := hs.φc_inj
  frames_arena := hs.frames_arena
  closures_arena := hs.closures_arena

/-! ## `OutRepr` survival (trivial — `σ.sailOutput`, not `σ.mem`) -/

/-- `OutRepr` depends only on `σ.sailOutput`; if two states have equal
`sailOutput` (any memory-only change), `OutRepr` transfers. -/
theorem outRepr_of_sailOutput_eq {σ σ' : MState} {st : St}
    (heq : σ'.sailOutput = σ.sailOutput) (h : OutRepr σ st) : OutRepr σ' st := by
  simp only [OutRepr, Vsa.Machine.output] at h ⊢
  rw [heq]; exact h

/-- Even weaker: equal `Machine.output` transfers `OutRepr`. -/
theorem outRepr_of_output_eq {σ σ' : MState} {st : St}
    (heq : Vsa.Machine.output σ' = Vsa.Machine.output σ) (h : OutRepr σ st) : OutRepr σ' st := by
  simp only [OutRepr] at h ⊢; rw [heq]; exact h

end Vsa.Sim
