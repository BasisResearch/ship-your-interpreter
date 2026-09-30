import VsaIris.Vsa.AllocTac
import VsaIris.Vsa.StepTables.Env0
import VsaIris.Interp.Repr

namespace VsaIris.Interp

def frameS (G : FrameGeom) (a : Nat) : Prop :=
  InExt G.sblk a ∨ (G.cap ≠ 0 ∧ (InExt G.nblk a ∨ InExt G.vblk a))

theorem frameS_iff (G : FrameGeom) (a : Nat) : frameS G a ↔ BlocksCover G.blocks a := by
  unfold frameS BlocksCover FrameGeom.blocks
  by_cases h : G.cap = 0 <;> simp [h]

end VsaIris.Interp

namespace VsaIris.Sym

macro_rules
  | `(tactic| sx_side) => `(tactic| (simp only [VsaIris.Interp.htifLo] at *; sx_addr))

macro_rules
  | `(tactic| sx_side) =>
    `(tactic| (intro b hb; have hb' := of_mem_accAddrs hb; simp only [InExt, VsaIris.Interp.frameS, VsaIris.Interp.htifLo] at *; sx_addr))

end VsaIris.Sym
