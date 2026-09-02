import Vsa.Sim.ReprSurvival

/-!
# Layer 2 — reusable `ValueRepr` TRANSLATION-COPY under a struct-byte copy

`Vsa/Sim/ReprSurvival.lean` proves *same-address* survival: `ValueRepr m N φc a v`
persists to `m'` when `m'` agrees with `m` byte-for-byte on the addresses the
relation reads (the 24-byte header `[a, a+24)` and any dereferenced string).

This file proves the *translation* variant used by the two `Value`-copy call
sites (`env_get`'s HIT tail and `EvalVarSim`'s `VarPostCall.hcopy`): a C `Value`
is **memcpy'd** from `srcAddr` to `dstAddr` — the 24 struct bytes are duplicated
verbatim (including any heap POINTER stored in the payload word), while the
pointed-to heap data (the `.str` string bytes / the closure) is **not** moved.
So `ValueRepr` re-holds at the *new* address `dstAddr` as long as:

1. the 24 struct bytes at `dstAddr` in `m'` equal the 24 at `srcAddr` in `m`
   (`∀ j < 24, m'[dstAddr+j]? = m[srcAddr+j]?`), and
2. `m'` preserves the value's heap payload target region (the `.str` string
   bytes at the payload pointer `p`; for `.closure`/`.native` the payload is a
   pointer whose target repr — `φc`/`N.addr`/native name string — must survive).

The mechanism, per kind:
* `.null`/`.bool`/`.int`: determined by the 24 struct bytes alone. The copied
  bytes give the same `read32`/`readI64` at `dstAddr` as at `srcAddr`.
* `.str`: struct bytes give the same payload pointer `p = read64 · (·+8)`; the
  `CString m p s` then transfers to `m'` by `cstring_agreeP` on `[p, p+s.length]`.
* `.closure`: struct bytes give the same `φc ca` at `dstAddr+8`; `φc ca ≠ 0` is
  memory-independent. (No further payload read — the `Closure*` target lives in
  `ClosureRepr`, part of `StoreRepr`, not `ValueRepr`.)
* `.native`: struct bytes give the same name pointer `p` (@+8) and `N.addr f`
  (@+16); the name `CString m p (nativeName f)` transfers by `cstring_agreeP`.

The heap-payload preservation is packaged, for `env_get`/`EvalVarSim`, as: `m'`
differs from `m` only inside the destination window `[dstAddr, dstAddr+24)`, and
that window is disjoint from the value's heap footprint (string bytes live
elsewhere in the arena / rodata). The convenience corollary
`valueRepr_copy_of_writeWindow` discharges the payload hypothesis from exactly
that disjointness.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

namespace Vsa.Sim

open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-! ## Byte-shifted `readLE` transfer

If the `n` bytes at `dstAddr` in `m'` equal the `n` bytes at `srcAddr` in `m`,
then any `readLE` of width `w ≤ n` reads the same value at the shifted address.
This is the byte-copy analogue of `readLE_agreeP` (which is the `srcAddr =
dstAddr` special case). -/

/-- `readLE` over a copied window: agreement `m'[dstAddr+k]? = m[srcAddr+k]?` for
all `k < n` transfers `readLE` of any width `w` with `off + w ≤ n` at the shifted
offset. Stated with an explicit offset `off` so the payload words at `+8`/`+16`
are covered directly. -/
theorem readLE_copy {m m' : Mem} {srcAddr dstAddr n : Nat}
    (hcopy : ∀ k, k < n → m'[dstAddr + k]? = m[srcAddr + k]?) :
    ∀ (w off : Nat), off + w ≤ n →
      readLE m' (dstAddr + off) w = readLE m (srcAddr + off) w := by
  intro w
  induction w with
  | zero => intro off _; rfl
  | succ w ih =>
    intro off hle
    have hhead : m'[dstAddr + off]? = m[srcAddr + off]? := by
      have := hcopy off (by omega)
      exact this
    have htail : readLE m' (dstAddr + off + 1) w = readLE m (srcAddr + off + 1) w := by
      have := ih (off + 1) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
    simp only [readLE, hhead]
    rw [show dstAddr + off + 1 = dstAddr + (off + 1) by omega,
        show srcAddr + off + 1 = srcAddr + (off + 1) by omega] at htail
    simp only [show dstAddr + off + 1 = dstAddr + (off + 1) by omega,
        show srcAddr + off + 1 = srcAddr + (off + 1) by omega, htail]

/-- `read32` at the copied destination equals `read32` at the source, for an
offset `off` with `off + 4 ≤ 24`. -/
theorem read32_copy {m m' : Mem} {srcAddr dstAddr : Nat}
    (hcopy : ∀ k, k < 24 → m'[dstAddr + k]? = m[srcAddr + k]?)
    {off : Nat} (hoff : off + 4 ≤ 24) :
    read32 m' (dstAddr + off) = read32 m (srcAddr + off) :=
  readLE_copy hcopy 4 off hoff

/-- `read64` at the copied destination equals `read64` at the source, for an
offset `off` with `off + 8 ≤ 24`. -/
theorem read64_copy {m m' : Mem} {srcAddr dstAddr : Nat}
    (hcopy : ∀ k, k < 24 → m'[dstAddr + k]? = m[srcAddr + k]?)
    {off : Nat} (hoff : off + 8 ≤ 24) :
    read64 m' (dstAddr + off) = read64 m (srcAddr + off) :=
  readLE_copy hcopy 8 off hoff

/-- `readI64` at the copied destination equals `readI64` at the source. -/
theorem readI64_copy {m m' : Mem} {srcAddr dstAddr : Nat}
    (hcopy : ∀ k, k < 24 → m'[dstAddr + k]? = m[srcAddr + k]?)
    {off : Nat} (hoff : off + 8 ≤ 24) :
    readI64 m' (dstAddr + off) = readI64 m (srcAddr + off) := by
  simp only [readI64, read64_copy hcopy hoff]

/-! ## The `ValueRepr` translation-copy lemma

The value struct at `srcAddr` in `m` reads:
* `read32 · srcAddr` (kind tag, @0) — always;
* `read64 · (srcAddr+8)` / `readI64 · (srcAddr+8)` (payload word, @8) — every
  non-null variant;
* `read64 · (srcAddr+16)` (@16) — only `.native`;
and, for `.str`/`.native`, a `CString` at the payload/name pointer `p`.

The `hpayload` hypothesis carries the payload-region agreement in the exact shape
`cstring_agreeP` consumes: for the payload pointer `p` witnessed by the *source*
`read64 m (srcAddr+8)`, `m'` and `m` agree on `[p, p + s.length]` (packaged via
`AgreeP` from `ReprSurvival`). -/

/-- **`ValueRepr` TRANSLATION-COPY (general form).**

Given `ValueRepr m N φc srcAddr v`, a struct-byte copy
`∀ j < 24, m'[dstAddr+j]? = m[srcAddr+j]?`, and payload-target agreement `hpay`
(`m'` agrees with `m` on the string byte range `[p, p+s.length]` for the payload
pointer `p` witnessed at the *source* `srcAddr+8`), conclude
`ValueRepr m' N φc dstAddr v`.

For `.null`/`.bool`/`.int`/`.closure` the `hpay` hypothesis is unused (there is
no string payload); pass `fun _ _ _ _ => rfl` or the vacuous witness. -/
theorem valueRepr_copy {m m' : Mem} {N : NativeAddrs} {φc : Addr → Nat}
    {srcAddr dstAddr : Nat} {v : Value}
    (hcopy : ∀ j, j < 24 → m'[dstAddr + j]? = m[srcAddr + j]?)
    (hpay : ∀ (p : Nat) (s : String), read64 m (srcAddr + 8) = some p →
      AgreeP (fun a => ∃ k, k ≤ s.length ∧ a = p + k) m m')
    (hv : ValueRepr m N φc srcAddr v) : ValueRepr m' N φc dstAddr v := by
  -- normalize `srcAddr` / `dstAddr` to `· + 0` so the offset lemmas apply at @0
  have h0dst : dstAddr = dstAddr + 0 := by omega
  have h0src : srcAddr = srcAddr + 0 := by omega
  cases v with
  | null =>
    simp only [ValueRepr] at hv ⊢
    rw [h0dst, read32_copy hcopy (by omega), ← h0src]; exact hv
  | bool b =>
    simp only [ValueRepr] at hv ⊢
    obtain ⟨hk, h8⟩ := hv
    refine ⟨?_, ?_⟩
    · rw [h0dst, read32_copy hcopy (by omega), ← h0src]; exact hk
    · rw [show dstAddr + 8 = dstAddr + 8 by rfl, read32_copy hcopy (off := 8) (by omega)]
      exact h8
  | int n =>
    simp only [ValueRepr] at hv ⊢
    obtain ⟨hk, h8⟩ := hv
    refine ⟨?_, ?_⟩
    · rw [h0dst, read32_copy hcopy (by omega), ← h0src]; exact hk
    · rw [readI64_copy hcopy (off := 8) (by omega)]; exact h8
  | str s =>
    simp only [ValueRepr] at hv ⊢
    obtain ⟨hk, p, hp, hpne, hcstr⟩ := hv
    refine ⟨?_, p, ?_, hpne, ?_⟩
    · rw [h0dst, read32_copy hcopy (by omega), ← h0src]; exact hk
    · rw [read64_copy hcopy (off := 8) (by omega)]; exact hp
    · exact cstring_agreeP (hpay p s hp) hcstr (fun k hk => ⟨k, hk, rfl⟩)
  | closure ca =>
    simp only [ValueRepr] at hv ⊢
    obtain ⟨hk, h8, hne⟩ := hv
    refine ⟨?_, ?_, hne⟩
    · rw [h0dst, read32_copy hcopy (by omega), ← h0src]; exact hk
    · rw [read64_copy hcopy (off := 8) (by omega)]; exact h8
  | native f =>
    simp only [ValueRepr] at hv ⊢
    obtain ⟨hk, ⟨p, hp, hcstr⟩, h16⟩ := hv
    refine ⟨?_, ⟨p, ?_, ?_⟩, ?_⟩
    · rw [h0dst, read32_copy hcopy (by omega), ← h0src]; exact hk
    · rw [read64_copy hcopy (off := 8) (by omega)]; exact hp
    · exact cstring_agreeP (hpay p _ hp) hcstr (fun k hk => ⟨k, hk, rfl⟩)
    · rw [read64_copy hcopy (off := 16) (by omega)]; exact h16

/-! ## Convenience corollary: copy realized as a write of the dst window

The two consumers realize the copy as "`m'` equals `m` outside the destination
window `[dstAddr, dstAddr+24)`, and inside that window the 24 bytes match the
source". The payload target (the `.str`/`.native` string) lives *outside* the
window (disjoint), so its bytes are untouched and `hpay` follows for free.

We phrase "the payload lives outside the window" abstractly as: every string the
value dereferences has its whole byte range disjoint from `[dstAddr, dstAddr+24)`.
For a caller that knows the string lives in a region disjoint from the write
(arena / rodata), this is a single `omega`-shaped disjointness fact. -/

/-- **`ValueRepr` TRANSLATION-COPY (write-window form).**

`m'` differs from `m` only inside `[dstAddr, dstAddr+24)`
(`houtside`: every byte outside the window is preserved), the 24 window bytes in
`m'` match the source 24 bytes in `m` (`hcopy`), and for the payload pointer `p`
witnessed at the source the string's byte range `[p, p+s.length]` is disjoint
from `[dstAddr, dstAddr+24)` (`hdisj`). Then `ValueRepr m' N φc dstAddr v`.

This is the form `env_get`'s HIT tail and `EvalVarSim`'s `hcopy` instantiate: the
three `sd` stores write exactly `[dstAddr, dstAddr+24)`, everything else
(including the heap string) is untouched, and the string's arena/rodata address
is disjoint from the sret/out buffer window. -/
theorem valueRepr_copy_of_writeWindow {m m' : Mem} {N : NativeAddrs} {φc : Addr → Nat}
    {srcAddr dstAddr : Nat} {v : Value}
    (hcopy : ∀ j, j < 24 → m'[dstAddr + j]? = m[srcAddr + j]?)
    (houtside : ∀ a, (a < dstAddr ∨ dstAddr + 24 ≤ a) → m'[a]? = m[a]?)
    (hdisj : ∀ (p : Nat) (s : String), read64 m (srcAddr + 8) = some p →
      ∀ k, k ≤ s.length → (p + k < dstAddr ∨ dstAddr + 24 ≤ p + k))
    (hv : ValueRepr m N φc srcAddr v) : ValueRepr m' N φc dstAddr v := by
  refine valueRepr_copy hcopy ?_ hv
  intro p s hp a ha
  obtain ⟨k, hk, rfl⟩ := ha
  exact (houtside (p + k) (hdisj p s hp k hk)).symm


/-! ## Total-read copy (wave 48k)

The Sail model copies memory TOTALLY: a `ld`/`sd` pair moves
`(m[a]?).getD 0`, so the destination window always holds `some` byte even where
the SOURCE byte is absent from the map.  Plain byte-for-byte agreement
(`hcopy` above) therefore does NOT hold for a total copy — but it is not what
`ValueRepr` needs.  `ValueRepr m … srcAddr v` already WITNESSES that every byte
it reads is present (a successful `readLE` forces each byte to be `some`), and
exactly there the total copy reproduces the source value.  That is the honest
form of the copy for a machine that never faults on absence: the value facts
come from the source `ValueRepr`, not from a blanket presence premise.

Bytes 4..7 of a `Value` struct (and 16..23 for the non-`.native` variants) are
never read by `ValueRepr`; under a total copy they hold `0`, and nothing
depends on them. -/

/-- `readLE` over a TOTALLY copied window: whenever the SOURCE read succeeds,
the destination reads the same value.  The source's success supplies the byte
presence that turns `getD 0` back into the byte itself. -/
theorem readLE_copy_total {m m' : Mem} {srcAddr dstAddr n : Nat}
    (hcopyT : ∀ k, k < n → m'[dstAddr + k]? = some ((m[srcAddr + k]?).getD 0)) :
    ∀ (w off : Nat), off + w ≤ n → ∀ {x : Nat},
      readLE m (srcAddr + off) w = some x → readLE m' (dstAddr + off) w = some x := by
  intro w
  induction w with
  | zero => intro off _ x hx; exact hx
  | succ w ih =>
    intro off hle x hx
    simp only [readLE, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
    obtain ⟨b, hb, rest, hrest, hval⟩ := hx
    have hhead : m'[dstAddr + off]? = some b := by
      rw [hcopyT off (by omega), hb]; rfl
    have htail : readLE m' (dstAddr + (off + 1)) w = some rest := by
      refine ih (off + 1) (by omega) ?_
      rw [show srcAddr + (off + 1) = srcAddr + off + 1 by omega]; exact hrest
    simp only [readLE, Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨b, hhead, rest, ?_, hval⟩
    rw [show dstAddr + off + 1 = dstAddr + (off + 1) by omega]; exact htail

/-- `read32` through a total copy, given the source read. -/
theorem read32_copy_total {m m' : Mem} {srcAddr dstAddr : Nat}
    (hcopyT : ∀ k, k < 24 → m'[dstAddr + k]? = some ((m[srcAddr + k]?).getD 0))
    {off x : Nat} (hoff : off + 4 ≤ 24) (h : read32 m (srcAddr + off) = some x) :
    read32 m' (dstAddr + off) = some x :=
  readLE_copy_total hcopyT 4 off hoff h

/-- `read64` through a total copy, given the source read. -/
theorem read64_copy_total {m m' : Mem} {srcAddr dstAddr : Nat}
    (hcopyT : ∀ k, k < 24 → m'[dstAddr + k]? = some ((m[srcAddr + k]?).getD 0))
    {off x : Nat} (hoff : off + 8 ≤ 24) (h : read64 m (srcAddr + off) = some x) :
    read64 m' (dstAddr + off) = some x :=
  readLE_copy_total hcopyT 8 off hoff h

/-- `readI64` through a total copy, given the source read. -/
theorem readI64_copy_total {m m' : Mem} {srcAddr dstAddr : Nat}
    (hcopyT : ∀ k, k < 24 → m'[dstAddr + k]? = some ((m[srcAddr + k]?).getD 0))
    {off : Nat} {x : Int} (hoff : off + 8 ≤ 24) (h : readI64 m (srcAddr + off) = some x) :
    readI64 m' (dstAddr + off) = some x := by
  simp only [readI64, Option.map_eq_some_iff] at h ⊢
  obtain ⟨n, hn, hx⟩ := h
  exact ⟨n, read64_copy_total hcopyT hoff hn, hx⟩

/-- **`ValueRepr` TRANSLATION-COPY, TOTAL form.**  Same conclusion as
`valueRepr_copy`, but the copy hypothesis is the one a real machine can supply:
the destination window holds the TOTAL reads of the source window.  No
byte-presence premise anywhere — the presence each read needs is already inside
`hv`. -/
theorem valueRepr_copy_total {m m' : Mem} {N : NativeAddrs} {φc : Addr → Nat}
    {srcAddr dstAddr : Nat} {v : Value}
    (hcopyT : ∀ j, j < 24 → m'[dstAddr + j]? = some ((m[srcAddr + j]?).getD 0))
    (hpay : ∀ (p : Nat) (s : String), read64 m (srcAddr + 8) = some p →
      AgreeP (fun a => ∃ k, k ≤ s.length ∧ a = p + k) m m')
    (hv : ValueRepr m N φc srcAddr v) : ValueRepr m' N φc dstAddr v := by
  have h0dst : dstAddr = dstAddr + 0 := by omega
  have h0src : srcAddr = srcAddr + 0 := by omega
  cases v with
  | null =>
    simp only [ValueRepr] at hv ⊢
    rw [h0dst]; exact read32_copy_total hcopyT (by omega) (by rw [← h0src]; exact hv)
  | bool b =>
    simp only [ValueRepr] at hv ⊢
    obtain ⟨hk, h8⟩ := hv
    exact ⟨by rw [h0dst]; exact read32_copy_total hcopyT (by omega) (by rw [← h0src]; exact hk),
      read32_copy_total hcopyT (off := 8) (by omega) h8⟩
  | int n =>
    simp only [ValueRepr] at hv ⊢
    obtain ⟨hk, h8⟩ := hv
    exact ⟨by rw [h0dst]; exact read32_copy_total hcopyT (by omega) (by rw [← h0src]; exact hk),
      readI64_copy_total hcopyT (off := 8) (by omega) h8⟩
  | str s =>
    simp only [ValueRepr] at hv ⊢
    obtain ⟨hk, p, hp, hpne, hcstr⟩ := hv
    exact ⟨by rw [h0dst]; exact read32_copy_total hcopyT (by omega) (by rw [← h0src]; exact hk),
      p, read64_copy_total hcopyT (off := 8) (by omega) hp, hpne,
      cstring_agreeP (hpay p s hp) hcstr (fun k hk => ⟨k, hk, rfl⟩)⟩
  | closure ca =>
    simp only [ValueRepr] at hv ⊢
    obtain ⟨hk, h8, hne⟩ := hv
    exact ⟨by rw [h0dst]; exact read32_copy_total hcopyT (by omega) (by rw [← h0src]; exact hk),
      read64_copy_total hcopyT (off := 8) (by omega) h8, hne⟩
  | native f =>
    simp only [ValueRepr] at hv ⊢
    obtain ⟨hk, ⟨p, hp, hcstr⟩, h16⟩ := hv
    exact ⟨by rw [h0dst]; exact read32_copy_total hcopyT (by omega) (by rw [← h0src]; exact hk),
      ⟨p, read64_copy_total hcopyT (off := 8) (by omega) hp,
        cstring_agreeP (hpay p _ hp) hcstr (fun k hk => ⟨k, hk, rfl⟩)⟩,
      read64_copy_total hcopyT (off := 16) (by omega) h16⟩

/-- **`ValueRepr` TRANSLATION-COPY, TOTAL write-window form.**  The total-read
sibling of `valueRepr_copy_of_writeWindow`. -/
theorem valueRepr_copy_total_of_writeWindow {m m' : Mem} {N : NativeAddrs} {φc : Addr → Nat}
    {srcAddr dstAddr : Nat} {v : Value}
    (hcopyT : ∀ j, j < 24 → m'[dstAddr + j]? = some ((m[srcAddr + j]?).getD 0))
    (houtside : ∀ a, (a < dstAddr ∨ dstAddr + 24 ≤ a) → m'[a]? = m[a]?)
    (hdisj : ∀ (p : Nat) (s : String), read64 m (srcAddr + 8) = some p →
      ∀ k, k ≤ s.length → (p + k < dstAddr ∨ dstAddr + 24 ≤ p + k))
    (hv : ValueRepr m N φc srcAddr v) : ValueRepr m' N φc dstAddr v := by
  refine valueRepr_copy_total hcopyT ?_ hv
  intro p s hp a ha
  obtain ⟨k, hk, rfl⟩ := ha
  exact (houtside (p + k) (hdisj p s hp k hk)).symm

/-! ## `#print axioms` sanity — main lemmas kernel-clean -/

section Sanity
example {m m' : Mem} {N : NativeAddrs} {φc : Addr → Nat}
    {srcAddr dstAddr : Nat} {v : Value}
    (hcopy : ∀ j, j < 24 → m'[dstAddr + j]? = m[srcAddr + j]?)
    (hpay : ∀ (p : Nat) (s : String), read64 m (srcAddr + 8) = some p →
      AgreeP (fun a => ∃ k, k ≤ s.length ∧ a = p + k) m m')
    (hv : ValueRepr m N φc srcAddr v) : ValueRepr m' N φc dstAddr v :=
  valueRepr_copy hcopy hpay hv
end Sanity

#print axioms valueRepr_copy
#print axioms valueRepr_copy_of_writeWindow
#print axioms valueRepr_copy_total
#print axioms valueRepr_copy_total_of_writeWindow

end Vsa.Sim
