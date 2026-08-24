import Vsa.Sim.EnvDefSpec
import Vsa.Sim.StrlenSpec
import Vsa.Sim.MemcpySpec

/-!
# Layer 3 — `env_define` spec, part 2: append/grow scaffolding + `ReallocContract`

Continuation of `Vsa/Sim/EnvDefSpec.lean` (the update-in-place foundations).  This
file owns the spec-side content for the **name-absent** (append) and **capacity==count**
(grow) paths of `env_define`, plus the `ReallocContract` interface the grow path needs,
and a precise composition map for the whole function.

Everything here is `sorry`/`axiom`/`native_decide`/`bv_decide`-free.

## Control-flow recap (append/grow, from `experiments/disasm.txt`)

```
APPEND/GROW ENTRY (name absent, from scan-loop exit at 0xaac beq)
  b14 lw   a5,4(s4)           ; a5 := env->cap
  b18 beq  a5,s3,0x80002b90    ; cap == count → GROW
APPEND (count < cap)  [0x80002b1c .. 0x80002b8c]
  b1c mv   a0,s2 ; b20 jal strlen         ; len := strlen(name)
  b24 addi s0,a0,1            ; s0 := len+1
  b28 mv a0,s0 ; b2c jal malloc          ; copy := malloc(len+1)
  b30 mv s1,a0 ; b34 beqz a0,0x80002bd0   ; NULL → OOM (exit, never returns)
  b38 mv a2,s0 ; b3c mv a1,s2 ; b40 jal memcpy   ; memcpy(copy, name, len+1)
  b44 lw   a5,0(s4)           ; a5 := env->count (= s3, but reloaded)
  b48 ld   a2,8(s4)           ; a2 := env->names base
  b4c ld   a4,16(s4)          ; a4 := env->vals  base
  b50 slli a3,a5,0x1          ; a3 := count*2
  b54 slli a7,a5,0x3          ; a7 := count*8        (name-slot stride)
  b58 add  a3,a3,a5           ; a3 := count*3
  b5c ld   a6,0(s5)           ; a6 := v.word0
  b60 ld   a0,8(s5)           ; a0 := v.word1
  b64 ld   a1,16(s5)          ; a1 := v.word2
  b68 add  a2,a2,a7           ; a2 := names + count*8
  b6c slli a3,a3,0x3          ; a3 := count*24       (vals stride)
  b70 sd   s1,0(a2)           ; names[count] := copy
  b74 add  a4,a4,a3           ; a4 := vals + count*24
  b78 addiw a5,a5,1           ; a5 := count+1
  b7c sd   a6,0(a4)           ; vals[count].word0 := v.word0
  b80 sd   a0,8(a4)           ; vals[count].word1 := v.word1
  b84 sd   a1,16(a4)          ; vals[count].word2 := v.word2
  b88 sw   a5,0(s4)           ; env->count := count+1
  b8c j    0x80002aec          ; → EPILOGUE
GROW (cap == count)  [0x80002b90 .. 0x80002bcc]
  b90 slliw a5,a5,0x1         ; a5 := cap*2   (new cap; cap*2 since cap≠0 here)
  b94 slli a1,a5,0x3          ; a1 := newcap*8
  b98 sw   a5,4(s4)           ; env->cap := newcap
  b9c mv   a0,s6 ; ba0 jal realloc      ; names := realloc(names, newcap*8)
  ba4 lw   a5,4(s4)           ; a5 := newcap (reload)
  ba8 sd   a0,8(s4)           ; env->names := new names ptr
  bac ld   a0,16(s4)          ; a0 := env->vals (old)
  bb0 slli a1,a5,0x1 ; bb4 add a1,a1,a5 ; bb8 slli a1,a1,0x3  ; a1 := newcap*24
  bbc jal  realloc            ; vals := realloc(vals, newcap*24)
  bc0 ld   a5,8(s4)           ; a5 := new names ptr (reload)
  bc4 sd   a0,16(s4)          ; env->vals := new vals ptr
  bc8 beqz a5,0x80002bd0       ; names NULL → OOM
  bcc bnez a0,0x80002b1c       ; vals ≠ NULL → back to APPEND head (0xb1c)
OOM  [0x80002bd0 .. 0x80002bf0]: _impure_ptr / fwrite / exit(1)  — never returns
CAP-INIT (count == 0 entry, from prologue blez at 0xa90)  [0x80002bf4 .. 0x80002c0c]
  bf4 lw   a5,4(a0)           ; a5 := cap
  bf8 bne  a5,s3,0x80002b1c    ; cap ≠ count(=0) → APPEND head
  bfc ld   s6,8(a0)           ; s6 := names
  c00 bnez a5,0x80002b90       ; cap ≠ 0 → GROW
  c04 li   a1,64 ; c08 li a5,8 ; c0c j 0x80002b98   ; cap := 8; go store cap + realloc
```

`realloc` entry is `0x8000527c` (newlib's real `realloc`, NOT a 3-instruction wrapper —
so `ReallocContract` is specified against dlmalloc's realloc semantics, exactly as
`MallocContract` is for malloc).

## The two realloc call sites (what `ReallocContract` must provide)

Both calls follow the RISC-V C ABI:
* `0xba0 realloc(a0 = old names ptr = s6, a1 = newcap*8)` → new names ptr in `a0`.
* `0xbbc realloc(a0 = old vals ptr, a1 = newcap*24)` → new vals ptr in `a0`.

`realloc(p, n)` (C semantics): returns a block of size `≥ n` whose first
`min(oldsize, n)` bytes equal the old block's; on failure returns NULL and leaves the
old block intact; `realloc(NULL, n) = malloc(n)`.  In the *grow* path here `n > oldsize`
always (newcap > cap), so the WHOLE old block's `oldsize` bytes are copied.

## Status of the four paths (see the report and the composition doc below)

* **Path 1 (scan+update)** — spec statement + composition documented; the per-iteration
  `strcmp_full_spec` ghost-at-call-site wiring is specified below (`ScanInv`, the loop
  measure, the strcmp P/Q instantiation).  The spec-side update characterization is
  landed in `EnvDefSpec` (`define_update_*`); this file adds the FrameRepr-update helper
  shape.
* **Path 3 (append, count < cap)** — spec-side append characterization landed here
  (`define_append_*`), append-path stride arithmetic landed here (`stride8`, `countw1`),
  strlen/malloc/memcpy composition documented.
* **Path 4 (grow, count == cap)** — `ReallocContract` landed here (TYPE-valued
  structure, matching the two call sites exactly), grow-path cap/stride arithmetic
  landed, realloc composition documented.
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
open Vsa.Sim.Code (Env_defineLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `realloc`'s entry address -/

/-- `realloc`'s entry address in the fixed binary (symbol table). -/
def reallocEntry : Nat := 0x8000527c

/-! ## Spec-side `define`: the append (name-absent) case characterization

When `x` is NOT bound in frame `f`, `Store.define` appends `(x, v)` to the binding
list, growing its length by one and leaving every prior entry fixed.  This is the
spec-side content the machine's append path (`0x80002b44..0x80002b88`,
`names[count] := copy; vals[count] := v; count++`) realises. -/

/-- The append branch grows the binding list length by one. -/
theorem define_append_length (vars : List (String × Vsa.While.Value)) (x : String)
    (v : Vsa.While.Value) :
    (vars ++ [(x, v)]).length = vars.length + 1 := by
  rw [List.length_append, List.length_singleton]

/-- On a name MISS, `Store.define` appends `(x, v)`; the frame's binding count grows
by one (the machine's append path stores `count+1` into `env->count`). -/
theorem define_append_count (f : Vsa.While.Frame) (x : String) (v : Vsa.While.Value)
    (hmiss : f.vars.any (·.1 == x) = false) :
    (({ f with vars :=
          if f.vars.any (·.1 == x) then
            f.vars.map fun p => if p.1 == x then (x, v) else p
          else f.vars ++ [(x, v)] } : Vsa.While.Frame)).vars.length = f.vars.length + 1 := by
  simp only [hmiss]
  exact define_append_length f.vars x v

/-- The appended entry at index `f.vars.length` is exactly `(x, v)`. -/
theorem define_append_getElem_new (vars : List (String × Vsa.While.Value)) (x : String)
    (v : Vsa.While.Value) :
    (vars ++ [(x, v)])[vars.length]'(by rw [define_append_length]; omega) = (x, v) := by
  rw [List.getElem_append_right (by omega)]
  simp

/-- Prior entries (index `j < f.vars.length`) are unchanged by the append. -/
theorem define_append_getElem_old (vars : List (String × Vsa.While.Value)) (x : String)
    (v : Vsa.While.Value) (j : Nat) (hj : j < vars.length) :
    (vars ++ [(x, v)])[j]'(by rw [define_append_length]; omega) = vars[j] := by
  rw [List.getElem_append_left hj]

/-! ## Append-path pointer / stride arithmetic

The append path computes two strides from `count`:
* name-slot offset `count*8` (`slli a7,a5,0x3`);
* value-slot offset `count*24` (`slli a3,a5,1; add a3,a3,a5; slli a3,a3,3` = `(2c+c)*8`).

`stride24` is already in `EnvDefSpec`; add the `count*8` fold and `count+1` (`addiw`). -/

/-- `slli` by 3 gives `8*count` (no wrap when `8*count < 2^64`). -/
theorem stride8 (n : Nat) (h : 8 * n < 2^64) : n * 8 % 2^64 = 8 * n := by
  omega

/-- `addiw count,1`: the count increment.  For `count < 2^31` (a valid `int` count),
`(count+1)` sign-extended from 32 bits is `count+1` at the `toNat` level. -/
theorem countw1 (n : Nat) (h : n < 2^31) :
    ((BitVec.ofNat 64 n) + sign_extend (m := 64) (0x001#12)).toNat = n + 1 := by
  have hs : (sign_extend (m := 64) (0x001#12) : BitVec 64).toNat = 1 := by decide
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

/-! ## Grow-path cap / stride arithmetic

The grow path doubles the capacity (`slliw a5,a5,1` = `cap*2`, since `cap ≠ 0` in the
grow block — the `cap == 0` case is handled by CAP-INIT which sets `cap := 8`), then
computes `newcap*8` (names realloc size) and `newcap*24` (vals realloc size). -/

/-- Cap doubling `cap*2` (no wrap when `2*cap < 2^32`, a valid `int` cap). -/
theorem cap_double (n : Nat) (h : 2 * n < 2^31) :
    ((BitVec.ofNat 64 n) <<< (1 : Nat)).toNat = 2 * n := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]

/-! ## `ReallocContract` — the realloc interface (TYPE-valued, `MallocContract` style)

Newlib's `realloc` (`0x8000527c`) is not verified; its behaviour is interface-specified
as a named hypothesis, exactly like `MallocContract`.  The contract is stated to be
EXACTLY what `env_define`'s two grow-path call sites need and no more:

* `realloc(a0 = p_old, a1 = n_new)` with `p_old ≠ 0` and `n_new > n_old` (a growth):
  returns `p_new` (fresh or moved), `n_new`-sized, in-arena, 16-aligned, whose first
  `n_old` bytes equal the old block `[p_old, p_old + n_old)`; the extent list drops
  `(p_old, n_old)` and gains `(p_new, n_new)`; on exhaustion returns NULL leaving the
  old block live (the OOM branch `exit`s, so callers rule it out with a non-exhaustion
  hypothesis just as for malloc).

The `oldExt` parameter is the `(p_old, n_old)` extent being resized; it must be in the
live `exts` list.  The ABI frame / stack-discipline / privFoot clauses mirror
`MallocContract` verbatim (realloc is a normal C function using the same allocator
state, gp-relative). -/
structure ReallocContract (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) where
  /-- Abstract allocator invariant: machine state × live allocations. -/
  AInv : MState → List (Nat × Nat) → Prop
  /-- Allocator-private addresses (metadata, reent state). -/
  privFoot : Nat → Prop
  /-- Private footprint is disjoint from every live allocation. -/
  privFoot_disjoint : ∀ σ exts, AInv σ exts →
    ∀ e ∈ exts, ∀ k < e.2, ¬ privFoot (e.1 + k)
  /-- The total-correctness triple for one growing `realloc(p_old, n_new)` call.
  `n_old`/`p_old` are the old extent (in `exts`); `n_new > n_old` (a growth). -/
  spec : ∀ (g : (R : Register) → Option (RegisterType R))
      (exts : List (Nat × Nat)) (p_old n_old n_new : Nat) (sp r : BitVec 64)
      (m0 : Std.ExtHashMap Nat (BitVec 8)),
    n_new ≤ maxReq → n_old < n_new → p_old ≠ 0 → (p_old, n_old) ∈ exts →
    Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 reallocEntry) ∧
        c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p_old) ∧
        c.σ.regs.get? Register.x11 = some (BitVec.ofNat 64 n_new) ∧
        c.σ.regs.get? Register.x1 = some r ∧ r.toNat % 4 = 0 ∧
        c.σ.regs.get? Register.x2 = some sp ∧ StackOK SL sp headroom ∧
        c.σ.regs.get? Register.x3 = some gpv ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        AInv c.σ exts ∧ c.σ.mem = m0)
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some r ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        c.σ.regs.get? Register.x3 = some gpv ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        -- NULL on exhaustion (old block still live), or a fresh/moved, aligned,
        -- in-arena block of size `n_new` whose first `n_old` bytes match the old:
        ((c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧ AInv c.σ exts) ∨
         (∃ p_new, c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p_new) ∧
           p_new ≠ 0 ∧ p_new % 16 = 0 ∧ A.contains p_new n_new ∧
           -- new extent disjoint from every OTHER live extent (the old one is dropped):
           (∀ e ∈ exts, e ≠ (p_old, n_old) → ExtDisjoint (p_new, n_new) e) ∧
           -- content preserved on the first `n_old` bytes:
           (∀ k, k < n_old → c.σ.mem[p_new + k]? = m0[p_old + k]?) ∧
           AInv c.σ ((p_new, n_new) :: (exts.erase (p_old, n_old))))) ∧
        -- memory outside the allocator-private footprint, the stack window, the old
        -- extent, and the new extent is untouched:
        (∀ a, ¬ privFoot a → ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
          (a < p_old ∨ p_old + n_old ≤ a) →
          c.σ.mem[a]? = m0[a]?))

/-! ## The strcmp result ↔ spec-name-equality bridge (load-bearing for path 1)

The scan loop tests `strcmp(names[i], name) == 0` via `bnez a0`.  `strcmp_full_spec`'s
post gives `strcmpSign x10 = strcmpSpecSign csa csb`; the env code branches on `x10 == 0`.
To correlate the C result with the SPEC-side `Store.define`'s `p.1 == x` name test we
need: for two proper C strings (`CStr` char lists), `strcmpSpecSign = 0 ↔ the char lists
are equal ↔ the `String`s are equal`.  This is missing from the `StrcmpSpec*` corpus (it
proves only the loop-local sign facts), so it is landed here. -/

/-- `byteVal` at an in-bounds index is the char's code. -/
theorem byteVal_getElem (cs : List Char) (k : Nat) (hk : k < cs.length) :
    byteVal cs k = cs[k].toNat := by
  unfold byteVal; rw [List.getElem?_eq_getElem hk]

/-- `byteVal` past the end (`k ≥ length`) is `0`. -/
theorem byteVal_zero_of_ge (cs : List Char) (k : Nat) (hk : cs.length ≤ k) :
    byteVal cs k = 0 := by
  unfold byteVal; rw [show cs[k]? = none from by rw [List.getElem?_eq_none]; exact hk]

/-- Interior bytes of a `CStr` list are nonzero: `byteVal cs i ≠ 0` for `i < length`. -/
theorem byteVal_ne_zero_of_lt (m : Mem) (p : Nat) (cs : List Char) (hc : CStr m p cs)
    (i : Nat) (hi : i < cs.length) : byteVal cs i ≠ 0 := by
  obtain ⟨b, hb, hbne⟩ := cstr_byte_ne m hc i hi
  rw [← cstr_byteVal m p cs hc i hi b hb hbne]
  exact fun h => hbne (BitVec.eq_of_toNat_eq (by rw [h]; rfl))

/-- Two char lists with equal lengths and agreeing `byteVal` streams are equal
(`Char.toNat` is injective). -/
theorem list_eq_of_byteVal_agree (csa csb : List Char)
    (hlen : csa.length = csb.length)
    (hagree : ∀ k, k < csa.length → byteVal csa k = byteVal csb k) :
    csa = csb := by
  apply List.ext_getElem hlen
  intro k hka hkb
  apply Char.ext
  apply UInt32.toNat_inj.mp
  have ha := byteVal_getElem csa k hka
  have hb := byteVal_getElem csb k hkb
  have := hagree k hka
  rw [ha, hb] at this
  -- byteVal · k = ·[k].toNat = ·[k].val.toNat (Char.toNat def)
  exact this

/-- **The strcmp equality bridge.**  For two proper C strings (`CStr` char lists),
`strcmpSpecSign = 0` forces the char lists equal.  Proof by cases on whether the lists
are already equal; if not, they differ at some in-bounds index or in length, and the
first-difference argument (`strcmpSpecSign_at`) yields a NONZERO sign, contradiction. -/
theorem eq_of_strcmpSpecSign_zero (m : Mem) (pa pb : Nat) (csa csb : List Char)
    (hca : CStr m pa csa) (hcb : CStr m pb csb)
    (hsign : strcmpSpecSign csa csb = 0) : csa = csb := by
  -- The bound and the first-difference index.
  let B := max csa.length csb.length + 1
  let k := firstDiff csa csb B
  obtain ⟨hagree, hdiffAt⟩ := firstDiff_is_least csa csb B
  -- Bytes agree strictly below k.
  have hagree_lt : ∀ i, i < k → byteVal csa i = byteVal csb i := hagree
  -- Show bytes ALSO agree at k, and k ≥ both lengths ⇒ full agreement ⇒ lists equal.
  -- strcmpSpecSign = isign (byteVal csa k) (byteVal csb k) definitionally.
  have hisign : isign (byteVal csa k) (byteVal csb k) = 0 := hsign
  have hbeqk : byteVal csa k = byteVal csb k := by
    -- if they differed, isign ≠ 0
    apply Decidable.byContradiction; intro hne
    unfold isign at hisign
    by_cases h1 : byteVal csa k < byteVal csb k
    · rw [if_pos h1] at hisign; exact absurd hisign (by decide)
    · rw [if_neg h1] at hisign; rw [if_neg hne] at hisign; exact absurd hisign (by decide)
  -- k ≥ csa.length: else byteVal csa k ≠ 0 (interior) and by agreement byteVal csb k ≠ 0,
  -- and k < B, so hdiffAt would need k < B ⇒ they differ — but they agree (hbeqk). So the
  -- only consistent possibility is k = length (terminator).  Precisely:
  have hka : csa.length ≤ k := by
    apply Decidable.byContradiction; intro h
    have hlt : k < csa.length := Nat.lt_of_not_le h
    -- k < la ≤ max < B ⇒ k < B ⇒ hdiffAt gives byteVal differ at k, contradicting hbeqk.
    have hkB : k < B := by
      have : csa.length ≤ max csa.length csb.length := Nat.le_max_left _ _
      show k < max csa.length csb.length + 1; omega
    exact hdiffAt hkB hbeqk
  have hkb : csb.length ≤ k := by
    apply Decidable.byContradiction; intro h
    have hlt : k < csb.length := Nat.lt_of_not_le h
    have hkB : k < B := by
      have : csb.length ≤ max csa.length csb.length := Nat.le_max_right _ _
      show k < max csa.length csb.length + 1; omega
    exact hdiffAt hkB hbeqk
  -- both lengths ≤ k; and agreement holds on [0,k) which covers [0, max) ⊇ both lengths.
  -- Lengths equal: byteVal csa la = 0 (terminator); if la < lb then byteVal csb la ≠ 0 but
  -- they agree (la < k) ⇒ contradiction; symmetric.
  have hlen : csa.length = csb.length := by
    rcases Nat.lt_trichotomy csa.length csb.length with h | h | h
    · exfalso
      have hla_lt_k : csa.length < k := by omega
      have hz : byteVal csa csa.length = 0 := byteVal_zero_of_ge csa csa.length (Nat.le_refl _)
      exact byteVal_ne_zero_of_lt m pb csb hcb csa.length h
        (by rw [← hagree_lt csa.length hla_lt_k]; exact hz)
    · exact h
    · exfalso
      have hlb_lt_k : csb.length < k := by omega
      have hz : byteVal csb csb.length = 0 := byteVal_zero_of_ge csb csb.length (Nat.le_refl _)
      exact byteVal_ne_zero_of_lt m pa csa hca csb.length h
        (by rw [hagree_lt csb.length hlb_lt_k]; exact hz)
  -- full agreement on [0, csa.length) (⊆ [0,k)) + equal lengths ⇒ lists equal.
  refine list_eq_of_byteVal_agree csa csb hlen (fun i hi => hagree_lt i (by omega))

/-- Trivial converse: equal char lists have `strcmpSpecSign = 0`. -/
theorem strcmpSpecSign_zero_of_eq (csa csb : List Char) (h : csa = csb) :
    strcmpSpecSign csa csb = 0 := by
  subst h
  unfold strcmpSpecSign isign
  simp

/-- **String-level bridge (the form path 1 consumes).**  For two `CString`s at `pa`/`pb`
representing spec strings `sa`/`sb`, `strcmpSpecSign csa csb = 0 ↔ sa = sb`, where
`csa`/`csb` are the underlying `CStr` char lists.  The scan loop uses the forward
direction on a `strcmp == 0` (hit) and the backward direction's contrapositive on
`strcmp != 0` (miss) to correlate with `Store.define`'s `String` name test. -/
theorem string_eq_iff_strcmpSpecSign_zero (m : Mem) (pa pb : Nat) (sa sb : String)
    (csa csb : List Char)
    (hca : CStr m pa csa) (hcb : CStr m pb csb)
    (hsa : sa = String.ofList csa) (hsb : sb = String.ofList csb) :
    strcmpSpecSign csa csb = 0 ↔ sa = sb := by
  constructor
  · intro h
    rw [hsa, hsb, eq_of_strcmpSpecSign_zero m pa pb csa csb hca hcb h]
  · intro h
    apply strcmpSpecSign_zero_of_eq
    rw [hsa, hsb] at h
    exact String.ofList_inj.mp h

/-! ## Composition documentation (paths 1, 3, 4)

The three remaining paths compose the landed callee specs + site lemmas by the exact
`env_new_spec` idiom (ghost-at-jal-successor, `hAInvFrame` transfer, ABI-frame register
threading, spill survival, `Env_defineLoaded` re-establishment via
`loaded_envdef_of_agree`).  What each path needs, precisely:

### Path 1 — scan loop + update (`env_define_update_spec`), NO allocator

The scan loop (`0xaa4..0xabc`, bottom-tested, head `0xab0`) is a `Triple.loop`:

* **Invariant `ScanInv`** (`AtHead i ∨ AtDone`): either at `0xab0` with `i < count`,
  `x8 = i`, `x9 = names + 8*i` (cursor), all the pinned pointers/spills intact, the
  frame's `FrameRepr` unchanged, and `∀ j < i, names[j] ≠ name` (no earlier hit); or
  `AtDone` at the update entry `0xac0` with the hit index `i` located
  (`names[i] = name`).
* **Guard `ScanB`** = "at `0xab0` with `i < count`".  Excluding `i = count` keeps the
  measure decreasing on the exiting iteration.
* **Measure** `ScanMu = count - i` (via `getD`).
* **Body** (`0xab0..0xabc + back-edge`): `ld a0,0(s1)` (load `names[i]`), `mv a1,s2`
  (name), then `jal strcmp` — the **cross-region call**.  Instantiate
  `strcmp_full_spec` with:
    - `g := fun R => σ_callsite.regs.get?` (ghost at the `jal`-successor `0xabc`, so the
      callee-entry `NotWrittenStrcmp` frame tie is `rfl`);
    - `pa := names[i]`, `pb := name`, `r := 0x80002abc`;
    - `sa/sb` the two `CString`s from `FrameRepr` (name-slot `i` gives
      `CString m q names[i].1`) and the caller's `name` argument's `CString`;
    - `P = strcmp_full_pre` needs: `StrcmpLoaded c.σ.mem` (a separate byte-pin,
      conjoined in `env_define_pre` alongside `Env_defineLoaded`); `MaskPinned m0`
      (rodata `0x8001ac80`, conjoined in P); the two `CString`s; the four
      `StrcmpRegion`/`StrcmpWRegion` region witnesses (from a layout-witness bundle in
      P asserting every represented string lives in RAM disjoint from code/HTIF); and
      the ghost tie (`rfl`).
    - env code tests `result == 0` via `bnez a0` at `0xabc`: `strcmp_post` gives
      `strcmpSign x10 = strcmpSpecSign csa csb`; `bnez` not-taken (`x10 = 0`) ⇔ the
      strings are equal ⇔ hit at `i`; taken ⇔ continue.  The equality bridge:
      `strcmpSpecSign csa csb = 0 ↔ csa = csb` (from `strcmpSpecSign`'s definition; the
      forward direction is `strcmpSpecSign_eq`'s converse — provable from `firstDiff`).
* On the hit (`AtDone i`): run the update path sites `0xac0..0xae8` (all landed in
  `EnvDefSites`: `ld a5,16(s4)` = vals base, the `slli;add;slli;add` stride to
  `vals+24*i` via `stride24`/`shl1_lit`/`shl3_lit`, the three `ld` of the `Value` from
  `s5`, the three `sd` into `vals+24*i`).  Then `FrameRepr` re-establishment: the three
  `sd`s overwrite exactly the 24-byte `ValueRepr` at `vals + 24*i`; every other slot,
  the name pointers, and the count are untouched (`getElem_writeMap8_disjoint` over the
  disjoint slots), so `FrameRepr m' N φf φc e (define …)` holds with the spec frame's
  binding `i` rewritten to `(x, v)` — exactly `define_update_getElem`.
* Epilogue `0xaec..0xb10` (landed): restore `ra/s0/s1/s2/s3/s4/s5/s6`, `addi sp,64`,
  `ret`.  Spill survival is identical to `env_new_spec` (the callee-saved values live
  at `sp+off`, disjoint from strcmp's footprint).

`Q = env_define_update_post` = `FrameRepr` for the updated frame `Store.define s a x v`
(update branch), memory framed to `[vals+24*i, +24) ∪ strcmp-footprint`, `sp`/callee-
saved restored, exact `ret`.  This path calls NO allocator — completable with the
landed pieces + the strcmp equality bridge.

### Path 3 — append (count < cap), calls strlen + malloc + memcpy

* `strlen_spec` (`StrlenSpec.strlen_spec`): CHECK its P alignment requirement.  The
  name pointer is `s2 = a1` (the caller's `name` arg).  strlen's aligned word path P
  requires `name % 8 = 0`.  **FLAG:** the name pointer's alignment is NOT provable in
  general — a `char *name` from `env_define`'s caller need not be 8-aligned.  If
  `strlen_spec` only covers the aligned path, path 3 needs either strlen's byte path or
  an alignment hypothesis in `env_define_pre`.  (`strcmp_full_spec` covers BOTH paths;
  if `strlen_spec` is aligned-only, the honest move is a P-level `name % 8 = 0`
  hypothesis, OR a `strlen_full_spec` extension mirroring `strcmp_full_spec`.)
* `malloc` via `MallocContract.spec` (env_new pattern): `n = len+1` (`addi s0,a0,1`),
  arena-non-exhaustion rules out the OOM `beqz` branch.
* `memcpy_spec` (`MemcpySpec`): `memcpy(copy, name, len+1)` — route disjunction P
  (copy is a fresh malloc block, disjoint from name).
* Then the append stores `0xb44..0xb88` (need sites: see EnvDefSites2 below —
  `lw/ld/ld/slli/slli/add/ld/ld/ld/add/slli/sd/add/addiw/sd/sd/sd/sw`), `count++`
  (`countw1`), and `FrameRepr` for the appended frame (`define_append_*`): a NEW
  name-slot `names[count] := copy` (with `CString copy name` from memcpy's post) and a
  NEW value-slot `vals[count] := v`, count `count+1`; prior slots untouched.

### Path 4 — grow (count == cap), calls realloc ×2 (+ then append)

Uses `ReallocContract` (above) twice: `realloc(names, newcap*8)` and
`realloc(vals, newcap*24)`, both growths (`newcap = 2*cap > cap`, and the byte sizes
grow proportionally).  The content-preservation clause (`first n_old bytes match`)
re-establishes `FrameRepr`'s name/value slots at their moved base; then control falls
back to the APPEND head `0xb1c` (`bnez a0` at `0xbcc`), so path 4 = grow + path 3.
The cap update `env->cap := newcap` (`sw a5,4(s4)` at `0xb98`) sets `FrameRepr`'s
existential `cap` witness to `newcap ≥ count+1`.  Non-exhaustion on both reallocs rules
out the OOM branches (`beqz a5`/`bnez a0` at `0xbc8`/`0xbcc`).

CAP-INIT (count == 0): `cap := 8` then jumps into the grow store+realloc; a
degenerate grow where the old extents may be NULL — realloc(NULL, n) = malloc(n), so
this sub-case additionally needs `realloc(NULL, ·)` = malloc in the contract (NOT added
above, since the count>0 grow path never passes NULL; CAP-INIT would need a
`ReallocContract` variant permitting `p_old = 0`).
-/

end Vsa.Sim
