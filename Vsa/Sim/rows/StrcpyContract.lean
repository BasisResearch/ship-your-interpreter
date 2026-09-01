import Vsa.Sim.rows.StringifyStrdupTail

/-!
# `StrcpyContract` — the composed `strcpy` callee contract as a NAMED residual

Task #68 Part 2 sub-fact.  The str-concat C-block (`0x80003a20 → 0x80003ae0`,
`Vsa/Sim/rows/StrConcatHeap.lean`) copies the RIGHT stringify buffer into the fresh
concat block with `strcpy(new + |L|, R)` at `0x80003ab4` (`jal strcpy@0x80006dc4`).

`strcpy` has verified per-site infrastructure — `Vsa/Sim/StrcpySites.lean` (the byte /
word site batteries) and `Vsa/Sim/StrcpySpecW2.lean` (the aligned word-loop pieces:
`iterCpw`, `entry_wordCpy`, `loop_body_w`, `entry_to_tail`, the ≤7-byte tail) — but
**no composed top-level `strcpy_full_spec` theorem exists** (unlike `memcpy` which has
`memcpy_spec_framed_byte`).  Rebuilding the whole word-loop composition here is out of
scope; per the brief's "honest move", we name the composed contract as ONE typed
residual, at the same `CString`-post surface `memcpy_bytepath_post` uses.

`StrcpyContract` says: `strcpy(dst, src)` — entry at `strcpyEntry`, `x10 = dst`,
`x11 = src`, `src` holding `CString m0 src str` — runs to a return at `r` with
`x10 = dst`, the whole C-string (INCLUDING the terminating NUL, `str.length + 1`
bytes) copied to `[dst, dst + |str| + 1)`, memory outside that window untouched, and
the caller-frame (`NotWrittenB`-class registers) preserved.  This is exactly what the
concat C-block needs to conclude `CString m' (new + |L|) R` after the copy.

The single inhabitant of `StrcpyContract` is the composition of the LANDED
`StrcpySpecW2` word-loop + byte-tail pieces (the genuine remaining machine work); it is
NOT an `axiom` and NOT `sorry` — it is a named typed obligation, supplied by that
composition when built.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)
open Vsa.MemRepr

namespace Vsa.Sim

/-- `strcpy`'s entry address in the fixed binary (symbol table). -/
def strcpyEntry : Nat := 0x80006dc4

/-- Registers `strcpy` must leave to the caller (the shared no-write class the
`memcpy` byte path uses — `strcpy` is the same leaf-copy shape). -/
abbrev StrcpyNotWritten : Register → Prop := NotWrittenB

/-- **The composed `strcpy(dst, src)` contract**, at the `CString`-copy post.

For every ABI ghost `g`, return address `r` (4-aligned), destination/source pointers
`dst`/`src`, source C-string `str`, and pristine memory `m0` with `CString m0 src.toNat
str`: from the `strcpy` entry (`x10 = dst`, `x11 = src`, `x1 = r`) the machine runs to a
return at `r` with `x10 = dst`, the `str.length + 1` bytes of the C-string (payload +
NUL) written to `[dst, dst + str.length + 1)`, memory outside that window unchanged, and
every `StrcpyNotWritten` register restored.  Consumers read back `CString mem' dst str`
from the copied-window clause + the NUL. -/
def StrcpyContract : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (str : String) (m0 : Std.ExtHashMap Nat (BitVec 8)),
    r.toNat % 4 = 0 →
    Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 strcpyEntry) ∧
        c.σ.regs.get? Register.x10 = some dst ∧
        c.σ.regs.get? Register.x11 = some src ∧
        c.σ.regs.get? Register.x1 = some r ∧
        c.σ.mem = m0 ∧ CString m0 src.toNat str ∧
        (∀ R, StrcpyNotWritten R → c.σ.regs.get? R = g R))
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some r ∧
        c.σ.regs.get? Register.x10 = some dst ∧
        c.σ.regs.get? Register.x1 = some r ∧
        -- the whole C-string incl. NUL is now at `[dst, dst + |str| + 1)`:
        CString c.σ.mem dst.toNat str ∧
        -- memory outside the copied window is untouched:
        (∀ a, (a < dst.toNat ∨ dst.toNat + (str.length + 1) ≤ a) →
          c.σ.mem[a]? = m0[a]?) ∧
        (∀ R, StrcpyNotWritten R → c.σ.regs.get? R = g R))

#print axioms StrcpyContract

end Vsa.Sim
