import Vsa.Sim.ValueSpec

/-!
# Value bridges for the shared inline comparison arm (`lt`/`le`/`gt`)

The comparison arm @0x80003628 computes, on two int operands `vl = .int a`
(payload word `Wl`, so `Wl.toInt = a`) and `vr = .int b` (payload word `Wr`,
`Wr.toInt = b`):

    cmp = subw (zext (slt Wr Wl)) (zext (slt Wl Wr))          -- = sign(a - b)

then an op-specific fixup, then `value_bool(sret, x11)` — which produces
`ValueRepr … (.bool (x11 != 0))`. These three bridges show that the fixup
output `x11` satisfies `(x11 != 0) = <spec comparison>`:

* **`lt`** (fixup `srli a1,a1,0x3f` = sign-bit extract): `(x11 != 0) = (a < b)`.
* **`le`** (fixup `slti a1,a1,1`):                        `(x11 != 0) = (a ≤ b)`.
* **`gt`** (fixup `sgtz a1,a1` = `slt x0,a1`):            `(x11 != 0) = (b < a)`.

`zopz0zI_s x y = (x.toInt < y.toInt)` (Sail signed-less-than on the 64-bit
payloads, which are in `[-2^63, 2^63)` — so `BitVec.slt` on the payloads
matches `Int` `<` directly, no range side-condition needed).

Proof shape: `zopz0zI_s` unfolds to the `Int` comparison definitionally; the
two comparisons `(a<b)`, `(b<a)` are mutually exclusive, so a trichotomy split
(`by_cases`) reduces each fixup to a concrete `BitVec` computation dischargeable
by `decide` after `unfold bool_to_bit bool_bit_forwards zopz0zI_s`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa

set_option maxHeartbeats 4000000

