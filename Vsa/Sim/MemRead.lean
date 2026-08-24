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

namespace Vsa.Sim

open Sail ConcurrencyInterfaceV1 LeanRV64DExecutable

variable {ue : Type} {σ : SequentialState RegisterType trivialChoiceSource}

theorem readByte_char {a : Nat} {b : BitVec 8} (h : σ.mem[a]? = some b) :
    (PreSail.readByte (RegisterType := RegisterType) (c := trivialChoiceSource) (ue := ue) a).run σ = .ok b σ := by
  simp [PreSail.readByte, EStateM.run, bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, pure, EStateM.pure, h]

theorem readBytes_two {a : Nat} {b0 b1 : BitVec 8}
    (h0 : σ.mem[a]? = some b0) (h1 : σ.mem[a + 1]? = some b1) :
    (PreSail.readBytes (RegisterType := RegisterType) (c := trivialChoiceSource) (ue := ue) 2 a).run σ =
      .ok (b1.append b0, none) σ := by
  simp [PreSail.readBytes, PreSail.readByte, EStateM.run, bind, EStateM.bind,
    get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, h0, h1]

theorem readBytes_four {a : Nat} {b0 b1 b2 b3 : BitVec 8}
    (h0 : σ.mem[a]? = some b0) (h1 : σ.mem[a + 1]? = some b1)
    (h2 : σ.mem[a + 2]? = some b2) (h3 : σ.mem[a + 3]? = some b3) :
    (PreSail.readBytes (RegisterType := RegisterType) (c := trivialChoiceSource) (ue := ue) 4 a).run σ =
      .ok (((b3.append b2).append b1).append b0, none) σ := by
  simp [PreSail.readBytes, PreSail.readByte, EStateM.run, bind, EStateM.bind,
    get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure,
    Nat.add_assoc, h0, h1, h2, h3]

theorem readBytes_eight {a : Nat} {b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8}
    (h0 : σ.mem[a]? = some b0) (h1 : σ.mem[a + 1]? = some b1)
    (h2 : σ.mem[a + 2]? = some b2) (h3 : σ.mem[a + 3]? = some b3)
    (h4 : σ.mem[a + 4]? = some b4) (h5 : σ.mem[a + 5]? = some b5)
    (h6 : σ.mem[a + 6]? = some b6) (h7 : σ.mem[a + 7]? = some b7) :
    (PreSail.readBytes (RegisterType := RegisterType) (c := trivialChoiceSource) (ue := ue) 8 a).run σ =
      .ok (((((((b7.append b6).append b5).append b4).append b3).append
        b2).append b1).append b0, none) σ := by
  simp [PreSail.readBytes, PreSail.readByte, EStateM.run, bind, EStateM.bind,
    get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure,
    Nat.add_assoc, h0, h1, h2, h3, h4, h5, h6, h7]

end Vsa.Sim
