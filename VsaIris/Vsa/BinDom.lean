import Vsa.Sim.Code.FixedImage

/-!
# The binary's `.text` and `.rodata` domains and bytes

The fixed ELF's code and read-only data as byte functions, below the
representation predicates: `Interp/Repr.lean`'s `world` owns the persistent
image `Newlib.binImg` over them (INTERP_DESIGN.md §10 "STATEMENT CHANGES
(E4)"); `Vsa/BinImg.lean` has its projections.
-/

namespace VsaIris.Newlib

def textDom (a : Nat) : Prop := 0x80000000 ≤ a ∧ a < 0x80018be0
/-- `.rodata` after the embedded script (`Vsa.Sim.Code.FixedRodataLoaded`). -/
def rodataDom (a : Nat) : Prop := 0x80018da6 ≤ a ∧ a < 0x8001acf0

instance (a : Nat) : Decidable (textDom a) := by unfold textDom; infer_instance
instance (a : Nat) : Decidable (rodataDom a) := by unfold rodataDom; infer_instance

def textByte (a : Nat) : BitVec 8 := Vsa.Sim.Code.fixedTextByte (a - 0x80000000)
def rodataByte (a : Nat) : BitVec 8 := Vsa.Sim.Code.fixedRodataByte (a - 0x80018be0)

end VsaIris.Newlib
