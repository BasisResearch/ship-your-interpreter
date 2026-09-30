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

/-- `free`'s entry address in the fixed binary (symbol table): `<free>` is the
3-instruction reentrancy wrapper `mv a1,a0 ; ld a0,1120(gp) ; j _free_r`. -/
def freeEntry : Nat := 0x8000479c

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

end Vsa.Alloc
