import Lean

/-!
Registers the `bvptr` simp attribute (must live in its own module so the
attribute is initialized before `Vsa/Sim/BvNorm.lean` applies it).
-/

register_simp_attr bvptr
