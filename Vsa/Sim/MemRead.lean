import Vsa.Elf
import Vsa.Sim.StateNF

/-!
# Layer 0 — characterization of the primitive byte reads

The innermost memory interface of the Sail state: `Sail.ConcurrencyInterfaceV1`'s
`readByte`/`readBytes` on the `Std.ExtHashMap Nat (BitVec 8)` byte memory.
Instruction fetch and all loads bottom out here. Hypotheses are in the
canonical `σ.mem[addr + k]? = some b` form of `PLAN-InterpSim.md` §Tooling.

`readBytes` assembles little-endian: the byte at the highest address is the
most significant. The 2/4/8-byte instances below are the ones the binary
uses (RVC probe, instruction fetch, doubleword loads).
-/

