import Vsa.Sim.Code.FixedImage

namespace VsaIris.Newlib

def textDom (a : Nat) : Prop := 0x80000000 ≤ a ∧ a < 0x80018be0

def rodataDom (a : Nat) : Prop := 0x80018da6 ≤ a ∧ a < 0x8001acf0

instance (a : Nat) : Decidable (textDom a) := by unfold textDom; infer_instance
instance (a : Nat) : Decidable (rodataDom a) := by unfold rodataDom; infer_instance

def textByte (a : Nat) : BitVec 8 := Vsa.Sim.Code.fixedTextByte (a - 0x80000000)
def rodataByte (a : Nat) : BitVec 8 := Vsa.Sim.Code.fixedRodataByte (a - 0x80018be0)

end VsaIris.Newlib
