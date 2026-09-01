import Vsa.Sim.JmpSpec
import Vsa.Sim.ReprSurvival

/-!
# Wave 45 — `SnprintfFrameContract` : the format-GENERIC snprintf footprint contract

The only landed `snprintf` spec, `snprintf_lld_spec` (`SnprintfSpec42`), is the
**byte-exact `"%lld"` capstone** (`x12` pinned to the `%lld` `.rodata`
`0x800192c0`, rendering `intToString`).  `runtime_error` (`0x80002da8`) makes two
`snprintf` calls whose formats are **not** `%lld`:

* call #1 `@0x80002dc8` uses the caller-inherited format (`a2` forwarded from
  `runtime_error(fmt, …)`, arbitrary) into a stack `body` scratch;
* call #2 `@0x80002de4` uses the fixed format `0x80019318 =
  "runtime error [line %d]: %s"` (`%d`+`%s` conversions, whose formatter paths are
  unverified) into `err_msg` at `s0+224`.

So neither call is the `%lld` specialization, and `snprintf_lld_spec` cannot be
instantiated for either.  What the error-transfer proof actually needs from each
call is *not* the byte-exact rendering but only the **footprint / frame**:

> `snprintf(dst, n, …)` terminates in `GoodState`, writes **only within
> `[dst.toNat, dst.toNat + n.toNat)`** (leaving all disjoint memory pointwise
> unchanged), keeps the console `output` unchanged (its buffer sink is RAM, not
> the `tohost` mailbox), restores the callee-saved ABI frame and `sp`, returns to
> its link `ra`, and preserves the blanket `NotWrittenJmp` ghost frame.

This is a **much weaker** property than `snprintf_lld_spec` proves, and it is
format-AGNOSTIC.  The pointwise frame is exactly the shape already present in
`snprintf_lld_spec`'s post (`SnprintfSpec42`, `∀ a, ¬win → mem'[a]? = mem[a]?`)
— but generalizing the *whole* `snprintf` body to an arbitrary format requires
verifying the unverified `%d`/`%s`/… conversion paths, out of scope here.  Per
CLAUDE.md Law 2, the format-generic frame is therefore a **NAMED typed premise**:
`SnprintfFrameContract`, a named-field `structure … : Prop`.  A future lane that
factors the footprint reasoning out of `snprintf_lld_spec`'s residual ledger (the
byte content is overkill — only the footprint bound is load-bearing) discharges
it; both the `%lld` capstone and the two `runtime_error` calls then consume the
SAME frame fact.

`AgreeP` (`Vsa/Sim/ReprSurvival.lean`) is the pointwise-agreement footprint
predicate: `AgreeP P m m' := ∀ a, P a → m[a]? = m'[a]?`.  We state the frame as
`AgreeP (outside dst n) c'.σ.mem c.σ.mem` where `outside dst n a := ¬(dst ≤ a <
dst+n)`.  `read64_agreeP` then transports any disjoint `read64` (e.g. the jmp_buf
slots) across the call.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine (MState Config Step Steps output)
open Vsa.Logic (Triple)
open Vsa.MemRepr (read64)
open Register

namespace Vsa.Sim

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-- The **complement of the write window** `[dst, dst+n)`: the addresses a
format-generic `snprintf(dst, n, …)` must leave unchanged. -/
def snprintfOutside (dst n : BitVec 64) (a : Nat) : Prop :=
  ¬(dst.toNat ≤ a ∧ a < dst.toNat + n.toNat)

/-- **The state at a `snprintf` ABI-call site.**  `PC` = the `snprintf` entry
`0x80005c44`, `a0 = dst` (the destination buffer), `a1 = n` (the size), and `ra =
link` (the caller's return address, 4-aligned so `ret` lands cleanly), with the
running memory `= m`, `GoodState`, tick/`minstret` noise, and the blanket
`NotWrittenJmp` ghost frame at `g`. -/
def AtSnprintfCall (g : (R : Register) → Option (RegisterType R))
    (dst n link s0e s1e : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = m ∧
  c.σ.regs.get? Register.PC = some (0x80005c44#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some dst ∧
  c.σ.regs.get? Register.x11 = some n ∧
  c.σ.regs.get? Register.x1 = some link ∧ link.toNat % 4 = 0 ∧
  c.σ.regs.get? Register.x8 = some s0e ∧
  c.σ.regs.get? Register.x9 = some s1e ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧ c.tick < 2 ∧
  (∀ R : Register, NotWrittenJmp R → c.σ.regs.get? R = g R)

/-- **The state at a `snprintf` RETURN.**  `PC` restored to the call `link`, `sp`
restored to `spv` (the value at the call site), the callee-saved frame restored to
its call-site ghosts, `GoodState`/tick/`minstret`, the ghost frame preserved, and
the load-bearing **footprint frame** `frame`: every address OUTSIDE `[dst, dst+n)`
holds the byte it held at the call (`AgreeP (snprintfOutside dst n) c'.σ.mem m`).
Output unchanged (`out`). -/
structure SnprintfFrameOut (g : (R : Register) → Option (RegisterType R))
    (dst n link spv s0e s1e out0 : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8))
    (out : String) (c : Config) : Prop where
  good : GoodState c.σ
  /-- returned to the caller's link. -/
  pc : c.σ.regs.get? Register.PC = some link
  /-- `sp` restored (snprintf is a leaf-frame-balanced ABI callee). -/
  sp : c.σ.regs.get? Register.x2 = some spv
  /-- callee-saved `s0` (`x8`) restored (ABI). -/
  s0 : c.σ.regs.get? Register.x8 = some s0e
  /-- callee-saved `s1` (`x9`) restored (ABI). -/
  s1 : c.σ.regs.get? Register.x9 = some s1e
  /-- the **footprint frame**: writes are confined to `[dst, dst+n)`. -/
  frame : AgreeP (snprintfOutside dst n) c.σ.mem m
  /-- console output unchanged (the buffer sink is RAM, not `tohost`). -/
  outEq : output c.σ = out
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  tick : c.tick < 2
  /-- the blanket ghost frame preserved. -/
  ghost : ∀ R : Register, NotWrittenJmp R → c.σ.regs.get? R = g R

/-- **`SnprintfFrameContract`** — the format-generic footprint contract for one
`snprintf(dst, n, …)` call, as a `Triple` from the call site (`AtSnprintfCall`) to
the return (`SnprintfFrameOut`), parameterized by the ghost frame `g`, the buffer
address `dst`, its size `n`, the return link `link`, the restored `sp` value `spv`,
the pre-call memory `m`, and the console output `out`.  A single named field
(`callFrame : Triple …`) — NOT an anonymous tower.  This is the NAMED premise a
`snprintf`-footprint lane discharges by factoring the footprint bound out of
`snprintf_lld_spec`'s residual ledger (independent of the format).  See the module
docstring. -/
structure SnprintfFrameContract (g : (R : Register) → Option (RegisterType R))
    (dst n link spv s0e s1e out0 : BitVec 64) (m : Std.ExtHashMap Nat (BitVec 8))
    (out : String) : Prop where
  callFrame :
    Triple (AtSnprintfCall g dst n link s0e s1e m)
           (SnprintfFrameOut g dst n link spv s0e s1e out0 m out)

/-- The frame contract, unfolded to a `Triple`, for direct `Triple.seq`
composition. -/
theorem SnprintfFrameContract.triple {g dst n link spv s0e s1e out0 m out}
    (FC : SnprintfFrameContract g dst n link spv s0e s1e out0 m out) :
    Triple (AtSnprintfCall g dst n link s0e s1e m)
           (SnprintfFrameOut g dst n link spv s0e s1e out0 m out) :=
  FC.callFrame

/-! ## Transport of a disjoint `read64` across a frame-contract call

The only property the error transfer reads out of `SnprintfFrameOut.frame` is:
a `read64` at an address whose whole 8-byte range lies OUTSIDE `[dst, dst+n)` is
preserved.  This is `read64_agreeP` instantiated at `snprintfOutside`. -/

/-- A `read64` at `a` survives the frame contract's write window when `[a, a+8)` is
disjoint from `[dst, dst+n)`. -/
theorem SnprintfFrameOut.read64_pres {g dst n link spv s0e s1e out0 m out c}
    (h : SnprintfFrameOut g dst n link spv s0e s1e out0 m out c)
    {a : Nat} (hdis : ∀ k, k < 8 → snprintfOutside dst n (a + k)) :
    read64 c.σ.mem a = read64 m a :=
  read64_agreeP h.frame hdis

#print axioms SnprintfFrameContract.triple
#print axioms SnprintfFrameOut.read64_pres

end Vsa.Sim
