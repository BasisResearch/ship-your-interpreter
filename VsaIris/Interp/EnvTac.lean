import VsaIris.Vsa.AllocTac
import VsaIris.Interp.EnvSteps
import VsaIris.Interp.Repr

/-!
# `sx_side` for `env_*` spans

An `env_*` span owns a concrete byte set: a union of intervals (the stack
frame, a value slot, a frame's blocks), written as a `fun a => …` of
interval tests. A store or load's `hS`/`hLDS` obligation
(`∀ b ∈ accAddrs ea w, S b`) is then interval arithmetic: the rules below
unfold the access window, `InExt` and R's HTIF bound `htifLo`, and hand the
goal to `sx_addr`.
-/

namespace VsaIris.Interp

/-- A frame's blocks as intervals (`BlocksCover G.blocks`, `frameS_iff`): the
struct block, and the two array blocks while `cap ≠ 0`. -/
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
