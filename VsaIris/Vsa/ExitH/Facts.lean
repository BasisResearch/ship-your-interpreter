import VsaIris.Vsa.Stdout.Tac
import VsaIris.Vsa.StdioErr

/-!
# `exit`'s newlib interior: the bytes it owns and the fields it reads (lane N4)

From `jal __call_exitprocs` (`0x80004778`) to `mv a0,s0` (`0x80004788`),
`exit` runs `__call_exitprocs(e, 0)` with an empty `__atexit`, then the
installed `stdio_exit_handler`, which is `_fwalk_sglue(_impure_data,
_fclose_r, &__sglue)`: `_fclose_r` on `stdin`, `stdout` and `stderr`
(`__sflush_r` with nothing pending, `__sclose` → `_close_r` → `_close`).

* The run owns `exitS s`: newlib's data but `_impure_ptr` (`stdioExcl`),
  `errno` (`_close_r` clears it) and the 256 bytes below `sp = s`.
* It reads the fields `CloseMt` (the common part: `__atexit`, the handler,
  `__sglue`, `stdin`, `stdout`) and `ErrIdleMt` or `ErrWrittenMt`
  (`stderr` at the boundary or after one write), as load values of the
  tracking memory (`Loads.lean`, generated).
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

/-- The bytes `exit`'s interior owns: newlib's data but `_impure_ptr`,
`errno`, and the 256 bytes below `s`. -/
def exitS (s : BitVec 64) (a : Nat) : Prop :=
  (stdioFoot a ∧ ¬ (0x8001b970 ≤ a ∧ a < 0x8001b978)) ∨ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c) ∨
    (s.toNat - 256 ≤ a ∧ a < s.toNat)

namespace XH
/-- Byte-set side goals over `exitS` (scoped: open `VsaIris.Sym.XH`). -/
scoped macro_rules | `(tactic| nx_addr) => `(tactic| (simp only [exitS, stdioFoot, InRange] at ⊢; (try simp (disch := omega) only [toNat_add_lit, toNat_add_neg, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); first | done | omega))
end XH

/-- Where the 256 bytes below `sp` may sit: RAM above the HTIF words, off
newlib's data (the Iris ownership of both makes them disjoint). -/
structure ExitSp (s : BitVec 64) : Prop where
  lo : 0x8001ad00 + 16 + 256 ≤ s.toNat
  hi : s.toNat ≤ 0x88000000
  align : s.toNat % 16 = 0
  place : s.toNat ≤ 0x8001b520 ∨ 0x8001c168 + 256 ≤ s.toNat

/-- The end of `exit`'s interior: `sp`, `s0` and `s1`–`s11` as at the entry. -/
structure ExitEnd (R : Nat → BitVec 64) (s e : BitVec 64) (R' : Nat → BitVec 64) : Prop where
  sp : R' 2 = s
  s0 : R' 8 = e
  saved : ∀ x ∈ [9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27], R' x = R x

end VsaIris.Sym
