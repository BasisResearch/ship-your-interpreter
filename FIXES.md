# Lean 4.34 port fixes (MBP overnight)

Prior fixes: ~/vsa-iris-spike-logs/prior-fixes.patch

## Fixed

- `Vsa/Sim/RamReadVirtual.lean` — simp unfolding (`EStateM.pure`/`EStateM.bind` no longer
  collapse `pure () >>= k` in a Sail `do` block, so the misalignment `ite_self` stopped firing
  and `rw [hsplit]` lost its pattern): added the local `rfl` lemma `pure_unit_bindCont` and one
  simp argument.
- `Vsa/Sim/EnvSetScanStart.lean` — `simp` no longer evaluates `sign_extend` on literals:
  added `hz : sign_extend (m := 64) 0x000#12 = 0#64` (`BitVec.eq_of_toNat_eq`/`decide`,
  the `EnvSetReturn.lean` idiom) to the `simpa` for `hx8_4`.
