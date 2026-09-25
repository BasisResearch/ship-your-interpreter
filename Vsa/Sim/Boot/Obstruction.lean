import Vsa.Sim.Boot.View
import Vsa.Sim.LayoutInstance

/-!
# C4: the natives' value names are `.rodata` literals

`interp_init` defines the three natives with `value_native("print", …)`, so
each native `Value`'s name pointer (word 1) is a string literal in `.rodata`
(`0x80019538`, `0x80019540`, `0x80019548` in every script build), while the
binding keys are heap copies. `FrameOwned.values` makes a native value's name
bytes `shared` (`ValueOwned`, `SharedCString`), and `BootHeapFacts.shared_geom`
(`SharedGeom.ram`) puts every shared byte at or above `0x8001acf0`, the end of
`.rodata`. So no configuration whose global frame holds a native with a
`.rodata` name is `Loaded`: `nativeName_obstruction` derives `False` from
`InterpRunReadyFacts` and three reads of the memory. The generated boot traces
instantiate it at every program's real entry memory (`Gen/<Prog>.lean`,
`c4_obstruction`). REVIEW.md C4; the fix is a statement change (not in P1–P4).
-/

namespace Vsa.Sim.Boot

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim.LayoutInstance Vsa.Sim.RuntimeOwnership

/-- A global frame whose first native's value name lies below `0x8001acf0`
refutes the boundary. -/
theorem nativeName_obstruction {c : Vsa.Machine.Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Vsa.While.Addr → Nat} {aLeft : Nat}
    (F : InterpRunReadyFacts c stmts count inp N A φf φc aLeft) {e pv p : Nat}
    (he : read64 c.σ.mem 0x87fffe10 = some e) (hpv : read64 c.σ.mem (e + 16) = some pv)
    (hp : read64 c.σ.mem (pv + 24 * 0 + 8) = some p) (hlo : p < 0x8001acf0) : False := by
  have hg := F.globals
  rw [F.interp_local] at hg
  have hφ : φf 0 = e := Option.some.inj (hg.symm.trans he)
  obtain ⟨D, top, brkv, chunks, bins, Fr, hB⟩ := F.boot
  have hfo := hB.owned.heap.store.frames 0 (by decide)
  obtain ⟨q, hq, hs⟩ := hfo.values pv (by rw [hφ]; exact hpv) 0 (by decide)
  have hqp : q = p := Option.some.inj (hq.symm.trans hp)
  subst hqp
  have := (hB.facts.shared_geom.ram _ (hs.bytes 0 (Nat.zero_le _))).1
  omega

end Vsa.Sim.Boot
