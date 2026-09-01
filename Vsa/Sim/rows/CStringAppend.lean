import Vsa.MemRepr

/-!
# `CStringAppend` — the general C-string concatenation lemma (Task #80 Half B stage 1)

The `.add` string-concat C-block (`Vsa/Sim/rows/StrConcatHeap.lean`) builds the
result buffer `new` byte-exactly as `memcpy(new, L, |L|)` (the left string's chars,
WITHOUT its NUL) followed by `strcpy(new+|L|, R)` (the right string's chars AND its
terminating NUL).  The concluding `CString new (L.display ++ R.display)` fact is
therefore the concatenation of a NUL-free left char run and a NUL-terminated right
`CStr` — a purely structural fact about `CStr`, stated here once, general over any
concat (it serves the two `.add` slots and any future string-append site).

We introduce `CStrChars m a cs` — the bytes of `cs` are present at `[a, a+|cs|)`,
each nonzero and ASCII, WITHOUT the terminating-NUL requirement `CStr` has (memcpy
copied exactly `|L|` bytes, so the byte at `a+|L|` is R's first char, NOT a NUL).
`cstr_append` then glues a `CStrChars` left run to a `CStr` right tail.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open Vsa.MemRepr

namespace Vsa.Sim

/-- `CStrChars m a cs` — the char bytes of `cs` are present at `[a, a+|cs|)`, each
nonzero and ASCII, with NO terminating-NUL requirement.  This is the "copied char
run" a `memcpy(dst, src, |src|)` produces (the source's chars without its NUL). -/
inductive CStrChars (m : Mem) : Nat → List Char → Prop where
  | nil {a : Nat} : CStrChars m a []
  | cons {a : Nat} {b : BitVec 8} {cs : List Char} :
    m[a]? = some b → b ≠ 0 → b.toNat < 128 →
    CStrChars m (a + 1) cs →
    CStrChars m a (Char.ofNat b.toNat :: cs)

/-- **`cstr_append`** — a NUL-free left char run `CStrChars m a csL` followed by a
NUL-terminated right `CStr m (a + |csL|) csR` is the concatenated `CStr m a (csL ++
csR)`.  Structural induction on the left run: each `cons` advances the base by one
and shrinks the left window; the `nil` base hands off to the right `CStr` at
`a + 0 = a`.  General over any concat. -/
theorem cstr_append {m : Mem} :
    ∀ {a : Nat} {csL csR : List Char}, CStrChars m a csL →
      CStr m (a + csL.length) csR → CStr m a (csL ++ csR) := by
  intro a csL csR hL
  induction hL with
  | @nil a =>
    intro hR
    simpa using (by simpa using hR : CStr m a csR)
  | @cons a b cs hb hbne hb128 hrest ih =>
    intro hR
    refine CStr.cons hb hbne hb128 ?_
    apply ih
    -- `(a+1) + cs.length = a + (b::cs).length` (list length shift)
    have : a + (Char.ofNat b.toNat :: cs).length = (a + 1) + cs.length := by
      simp only [List.length_cons]; omega
    rwa [this] at hR

/-- **`CStrChars` transports along a byte-equal copy** (the `memcpy` byte-post
shape): if `CStr m0 src cs` reads the source chars and `mem[dst+k]? = m0[src+k]?`
for every `k < cs.length` (the copied window, WITHOUT the NUL), then `CStrChars mem
dst cs`.  Structural induction with a shifting base, one step per `cons`. -/
theorem cStrChars_of_copy {m0 mem : Mem} :
    ∀ {src dst : Nat} {cs : List Char}, CStr m0 src cs →
      (∀ k, k < cs.length → mem[(dst + k)]? = m0[(src + k)]?) →
      CStrChars mem dst cs := by
  intro src dst cs hcstr
  induction hcstr generalizing dst with
  | @nil a hnul =>
    intro _hcopy; exact CStrChars.nil
  | @cons a b cs hb hbne hb128 hrest ih =>
    intro hcopy
    refine CStrChars.cons (b := b) ?_ hbne hb128 ?_
    · have := hcopy 0 (by simp only [List.length_cons]; omega)
      simpa using this.trans (by simpa using hb)
    · refine ih (dst := dst + 1) (fun k hk => ?_)
      have := hcopy (k + 1) (by simp only [List.length_cons]; omega)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

/-- **`cstring_append`** — the `CString`-level concatenation.  Given the left
string's char run copied at `[dst, dst+|L|)` (NUL-free, `CStrChars`) and the right
string's `CString` at `dst+|L|` (NUL-terminated), the buffer holds `CString mem dst
(sL ++ sR)`.  The `|L|`-offset for the right base is `sL.length` (the copied byte
count = the left char count, no NUL between). -/
theorem cstring_append {mem : Mem} {dst : Nat} {sL sR : String}
    (hL : CStrChars mem dst sL.toList)
    (hR : CString mem (dst + sL.toList.length) sR) :
    CString mem dst (sL ++ sR) := by
  obtain ⟨csR, hcsR, hsR⟩ := hR
  refine ⟨sL.toList ++ csR, cstr_append hL hcsR, ?_⟩
  -- `(sL ++ sR) = String.ofList (sL.toList ++ csR)`; `sR = ofList csR`.
  subst hsR
  apply String.toList_inj.mp
  simp [String.toList_ofList]

/-! ## The concat-C-block readback corollary

The concat C-block builds `new` as `memcpy(new, L, |L|)` (L's chars, no NUL) then
`strcpy(new+|L|, R)` (R's chars + NUL).  `concatReadback` packages the two callee
byte-posts into the concluding `CString new (sL ++ sR)` — the exact fact
`concatHeapCore`'s `value_str` box needs.  Suppliers: the memcpy byte-post's
copied-window clause (via `cStrChars_of_copy` from `CString mMem L sL`) and
`StrcpyContractCpw`'s `CString new+|L| sR` post. -/

/-- **`concatReadback`** — the concat C-block's concluding CString.  From (a) the
left chars copied into `[new, new+|sL|)` via a byte-equal window over `CString mL
srcL sL` (the memcpy byte-post shape, `|sL|` bytes, no NUL), and (b)
`CString mem (new + |sL|) sR` (the strcpy post, R + NUL already at `new+|sL|`),
concludes `CString mem new (sL ++ sR)`.  The `|sL|` offset is `sL.toList.length`
(the copied byte count). -/
theorem concatReadback {mL mem : Mem} {new srcL : Nat} {sL sR : String}
    (hLsrc : CStr mL srcL sL.toList)
    (hLcopy : ∀ k, k < sL.toList.length → mem[(new + k)]? = mL[(srcL + k)]?)
    (hR : CString mem (new + sL.toList.length) sR) :
    CString mem new (sL ++ sR) :=
  cstring_append (cStrChars_of_copy hLsrc hLcopy) hR

#print axioms cstr_append
#print axioms cStrChars_of_copy
#print axioms cstring_append
#print axioms concatReadback

end Vsa.Sim
