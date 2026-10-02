import VsaIris.Vsa.AllocTac
import VsaIris.Vsa.FootKey
import VsaIris.Interp.Repr

namespace VsaIris.Interp

def frameS (G : FrameGeom) (a : Nat) : Prop :=
  InExt G.sblk a ∨ (G.cap ≠ 0 ∧ (InExt G.nblk a ∨ InExt G.vblk a))

theorem frameS_iff (G : FrameGeom) (a : Nat) : frameS G a ↔ BlocksCover G.blocks a := by
  unfold frameS BlocksCover FrameGeom.blocks
  by_cases h : G.cap = 0 <;> simp [h]

end VsaIris.Interp

