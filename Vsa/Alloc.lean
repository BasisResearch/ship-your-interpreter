import Vsa.Triple
import Vsa.RuntimeRepr
import Vsa.Sim.GoodState

/-!
# The allocator interface: `MallocContract` (the plan's `MallocSpec`)

PLAN-InterpSim.md Layer 2, the CompCert-style-adapted decision: newlib's
allocator (`malloc` = 3-instruction wrapper → `_malloc_r`, 560 instructions
of dlmalloc) is *not verified*. Its behavior is interface-specified as a
**named hypothesis** on the final theorem — a Lean `structure` whose single
inhabitant would be a verified-malloc proof, never an `axiom`. A wrong
hypothesis makes theorems vacuous at worst, not `False`-derivable; and
`#print axioms` stays clean.

The contract says exactly what the plan lists: freshness, 16-byte
alignment, arena bounds, termination (it is a *total-correctness* Triple),
NULL on exhaustion, allocator-private footprint preserved — plus the RISC-V
ABI frame (callee-saved registers, `sp`/`gp`/`tp` restored) and the C-stack
discipline (the callee may scribble only strictly below the entry `sp`
within the stack region).

`AInv` is the abstract allocator-state invariant relating machine state to
the list of live allocations (`exts`, base/size pairs); `privFoot` is the
allocator-private address set (heap metadata, `_impure_ptr` reent state).
Both are existentially packaged by the structure — the final theorem takes
one `MallocContract …` argument and never inspects them further.
-/

namespace Vsa.Alloc

open Vsa.Machine Vsa.Logic Vsa.RuntimeRepr Vsa.Sim
open LeanRV64DExecutable

/-- `malloc`'s entry address in the fixed binary (symbol table). -/
def mallocEntry : Nat := 0x80004790

/-- The C stack region (concrete bounds from the linker script at M6). -/
structure StackLayout where
  lo : Nat
  hi : Nat

/-- `sp` is a plausible C stack pointer with `headroom` bytes available:
16-aligned (RISC-V psABI), inside the stack region with room to grow down. -/
def StackOK (SL : StackLayout) (sp : BitVec 64) (headroom : Nat) : Prop :=
  SL.lo + headroom ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0

/-- Extents `(base, size)` are disjoint. -/
def ExtDisjoint (a b : Nat × Nat) : Prop :=
  a.1 + a.2 ≤ b.1 ∨ b.1 + b.2 ≤ a.1

/-- Registers a call must preserve per the RISC-V ABI: `sp`, `gp`, `tp`,
`s0–s11` — plus the machine-control registers no C function touches. The
allocator contract's frame is stated over exactly these (caller-saved
registers are forfeit across the call). -/
def AbiPreserved : Register → Bool
  | .x2 | .x3 | .x4 | .x8 | .x9 => true
  | .x18 | .x19 | .x20 | .x21 | .x22 | .x23 | .x24 | .x25 | .x26 | .x27 => true
  | _ => false

/-- **The allocator contract** — the one named hypothesis of the final
theorem. `A` is the heap arena, `SL` the stack region, `gpv` the global
pointer value (pinned for the whole run; `_malloc_r` addresses its state
gp-relative), `headroom` the stack bytes malloc may use, `maxReq` the
largest request the interpreter ever makes (both concrete at M6). -/
structure MallocContract (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) where
  /-- Abstract allocator invariant: machine state × live allocations. -/
  AInv : MState → List (Nat × Nat) → Prop
  /-- Allocator-private addresses (metadata, reent state). -/
  privFoot : Nat → Prop
  /-- Private footprint is disjoint from every live allocation. -/
  privFoot_disjoint : ∀ σ exts, AInv σ exts →
    ∀ e ∈ exts, ∀ k < e.2, ¬ privFoot (e.1 + k)
  /-- The total-correctness triple for one `malloc(n)` call. -/
  spec : ∀ (g : (R : Register) → Option (RegisterType R))
      (exts : List (Nat × Nat)) (n : Nat) (sp r : BitVec 64)
      (m0 : Std.ExtHashMap Nat (BitVec 8)),
    n ≤ maxReq →
    Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 mallocEntry) ∧
        c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 n) ∧
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
        -- NULL on exhaustion, or a fresh, aligned, in-arena block:
        ((c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧ AInv c.σ exts) ∨
         (∃ p, c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
           p ≠ 0 ∧ p % 16 = 0 ∧ A.contains p n ∧
           (∀ e ∈ exts, ExtDisjoint (p, n) e) ∧
           AInv c.σ ((p, n) :: exts))) ∧
        -- memory outside the allocator-private footprint and the stack
        -- window strictly below the entry sp is untouched:
        (∀ a, ¬ privFoot a → ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
          c.σ.mem[a]? = m0[a]?))

end Vsa.Alloc
