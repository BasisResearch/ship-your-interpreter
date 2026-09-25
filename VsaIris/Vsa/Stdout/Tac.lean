import VsaIris.Vsa.Stdout.Console
import VsaIris.Vsa.Stdout.Write

/-!
# Driving stdout runs (lane N1)

A stdout call owns newlib's data, `errno` and its stack (`outS s need`: the
bytes below the call's `sp = s`). `ix_run` drives the stdio step table
(`Steps/*.lean`); this module extends its side-condition discharger with
`outS` (interval arithmetic) and its store forwarding with every load width
(`nx_mem`) and the boundary `stdout` fields (`ConsoleMt`).

A callee's summary is a transformer of printing symbolic runs whose
continuation is at the return address with `callRet R v a0`: `a0` the
result, the caller-saved temporaries and arguments at any values `v`, every
other register (`ra`, `sp`, the saved registers) as at the call.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio

/-- The bytes a stdout call owns: newlib's data, `errno`, and `need` bytes
of stack below `s`. -/
def outS (s : BitVec 64) (need : Nat) (a : Nat) : Prop :=
  stdioFoot a ∨ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c) ∨ (s.toNat - need ≤ a ∧ a < s.toNat)

macro_rules
  | `(tactic| sx_side) => `(tactic| (intro b hb; simp only [mem_accAddrs_iff, outS, stdioFoot, InRange] at *; sx_addr))

macro_rules
  | `(tactic| ix_mem) => `(tactic| ((try nx_mem) <;> (try simp (disch := assumption) only
      [ConsoleMt.impure, ConsoleMt.sinit, ConsoleMt.stdout, ConsoleMt.p, ConsoleMt.w,
       ConsoleMt.flagsU, ConsoleMt.flagsS, ConsoleMt.fd, ConsoleMt.base, ConsoleMt.bsize,
       ConsoleMt.lbf, ConsoleMt.cookie, ConsoleMt.writer, ConsoleMt.lock, ConsoleMt.lockMode] at *)))

/-- A branch refuted by a hypothesis of the run (a flag bit a summary assumes). -/
macro_rules
  | `(tactic| sx_side) => `(tactic| (intro hc; first | exact hc ‹_› | exact absurd hc ‹_›))

/-- The caller-saved registers other than `a0` and `ra`. -/
abbrev callClob : List Nat := [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

/-- Updating the registers `xs` to the values `v`. -/
def updAll (R : Nat → BitVec 64) (v : Nat → BitVec 64) : List Nat → Nat → BitVec 64
  | [] => R
  | x :: xs => upd (updAll R v xs) x (v x)

/-- The register file after a call returns `a0`: the caller-saved registers
(`callClob`) at `v`, everything else as at the call. -/
abbrev callRet (R v : Nat → BitVec 64) (a0 : BitVec 64) : Nat → BitVec 64 :=
  upd (updAll R v callClob) 10 a0

theorem updAll_apply (R v : Nat → BitVec 64) : ∀ (xs : List Nat) (x : Nat),
    updAll R v xs x = if x ∈ xs then v x else R x
  | [], x => by simp [updAll]
  | y :: ys, x => by
    simp only [updAll, upd_apply, updAll_apply R v ys x, List.mem_cons]
    by_cases h : x = y
    · subst h; simp
    · simp [h]

/-- Closing a callee's run: its end register file agrees with `callRet` at
the values it ends with. -/
theorem callRet_of {R Rf : Nat → BitVec 64} {a0 : BitVec 64} (h10 : Rf 10 = a0)
    (hkeep : ∀ x ∈ iRegs, x ≠ 32 → x ≠ 10 → x ∉ callClob → Rf x = R x) :
    ∀ r ∈ iRegs, r ≠ VsaIris.PC → callRet R Rf a0 r = Rf r := by
  intro r hr hne
  simp only [upd_apply, updAll_apply]
  by_cases e : r = 10
  · subst e; simp [h10]
  · rw [if_neg e]
    by_cases hc : r ∈ callClob
    · rw [if_pos hc]
    · rw [if_neg hc, hkeep r hr hne e hc]

end VsaIris.Sym
