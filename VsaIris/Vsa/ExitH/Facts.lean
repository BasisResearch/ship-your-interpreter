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
  tracking memory. `closeMt_of` and friends derive them from `StdioOK` /
  `StdioErrOK` (`VsaIris/Vsa/StdioErr.lean`, lane N3).
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

/-- The bytes `exit`'s interior owns: newlib's data but `_impure_ptr`,
`errno`, and the 256 bytes below `s`. -/
def exitS (s : BitVec 64) (a : Nat) : Prop :=
  (stdioFoot a ∧ ¬ (0x8001b970 ≤ a ∧ a < 0x8001b978)) ∨ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c) ∨
    (s.toNat - 256 ≤ a ∧ a < s.toNat)

macro_rules | `(tactic| nx_addr) => `(tactic| (simp only [exitS, stdioFoot, InRange] at ⊢; (try simp (disch := omega) only [toNat_add_lit, toNat_add_neg, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); first | done | omega))

/-- The fields the close path reads besides `stderr`'s `FILE`. -/
structure CloseMt (Mt : Mem) : Prop where
  atexit : ldv .ld Mt 0x8001b9f8 = 0#64
  handler : ldv .ld Mt 0x8001b9b0 = 0x80005d18#64
  glueNext : ldv .ld Mt 0x8001b520 = 0#64
  glueCount : ldv .lw Mt 0x8001b528 = 3#64
  glueFiles : ldv .ld Mt 0x8001b530 = 0x8001ba68#64
  sinit : ldv .ld Mt 0x8001b580 = 0x80005d2c#64
  in_flagsU : ldv .lhu Mt 0x8001ba78 = 4#64
  in_flags : ldv .lh Mt 0x8001ba78 = 4#64
  in_fd : ldv .lh Mt 0x8001ba7a = 0#64
  in_r : ldv .lw Mt 0x8001ba70 = 0#64
  in_ur : ldv .lw Mt 0x8001bad8 = 0#64
  in_cookie : ldv .ld Mt 0x8001ba98 = 0x8001ba68#64
  in_close : ldv .ld Mt 0x8001bab8 = 0x8000f0c0#64
  in_ub : ldv .ld Mt 0x8001bac0 = 0#64
  in_lb : ldv .ld Mt 0x8001bae0 = 0#64
  in_lock : ldv .ld Mt 0x8001bb08 = 0#64
  in_mode : ldv .lw Mt 0x8001bb18 = 0#64
  out_flagsU : ldv .lhu Mt 0x8001bb30 = 0x200a#64
  out_flags : ldv .lh Mt 0x8001bb30 = 0x200a#64
  out_fd : ldv .lh Mt 0x8001bb32 = 1#64
  out_base : ldv .ld Mt 0x8001bb38 = 0x8001bb97#64
  out_p : ldv .ld Mt 0x8001bb20 = 0x8001bb97#64
  out_cookie : ldv .ld Mt 0x8001bb50 = 0x8001bb20#64
  out_close : ldv .ld Mt 0x8001bb70 = 0x8000f0c0#64
  out_ub : ldv .ld Mt 0x8001bb78 = 0#64
  out_lb : ldv .ld Mt 0x8001bb98 = 0#64
  out_lock : ldv .ld Mt 0x8001bbc0 = 0#64
  out_mode : ldv .lw Mt 0x8001bbd0 = 0#64

/-- `stderr` at the boundary (`ExitIdleFile … 0x12 2`), as loads. -/
structure ErrIdleMt (Mt : Mem) : Prop where
  flagsU : ldv .lhu Mt 0x8001bbe8 = 0x12#64
  flags : ldv .lh Mt 0x8001bbe8 = 0x12#64
  fd : ldv .lh Mt 0x8001bbea = 2#64
  r : ldv .lw Mt 0x8001bbe0 = 0#64
  ur : ldv .lw Mt 0x8001bc48 = 0#64
  cookie : ldv .ld Mt 0x8001bc08 = 0x8001bbd8#64
  close : ldv .ld Mt 0x8001bc28 = 0x8000f0c0#64
  ub : ldv .ld Mt 0x8001bc30 = 0#64
  lb : ldv .ld Mt 0x8001bc50 = 0#64
  lock : ldv .ld Mt 0x8001bc78 = 0#64
  mode : ldv .lw Mt 0x8001bc88 = 0#64

/-- `stderr` after one write (`ErrWrittenFile`), as loads. -/
structure ErrWrittenMt (Mt : Mem) : Prop where
  flagsU : ldv .lhu Mt 0x8001bbe8 = 0x201a#64
  flags : ldv .lh Mt 0x8001bbe8 = 0x201a#64
  fd : ldv .lh Mt 0x8001bbea = 2#64
  base : ldv .ld Mt 0x8001bbf0 = 0x8001bc4f#64
  p : ldv .ld Mt 0x8001bbd8 = 0x8001bc4f#64
  cookie : ldv .ld Mt 0x8001bc08 = 0x8001bbd8#64
  close : ldv .ld Mt 0x8001bc28 = 0x8000f0c0#64
  ub : ldv .ld Mt 0x8001bc30 = 0#64
  lb : ldv .ld Mt 0x8001bc50 = 0#64
  lock : ldv .ld Mt 0x8001bc78 = 0#64
  mode : ldv .lw Mt 0x8001bc88 = 0#64

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
