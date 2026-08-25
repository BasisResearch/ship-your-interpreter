import Lean

/-!
Registers the `mfr` simp attribute (must live in its own module so the
attribute is initialized before `Vsa/Sim/Mfr.lean` applies it) — the
memory-frame twin of `Vsa/Sim/BvNormAttr.lean`'s `bvptr`.
-/

register_simp_attr mfr
