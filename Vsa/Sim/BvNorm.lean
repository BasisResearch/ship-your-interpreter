import Vsa.Sim.BvNormAttr
import Vsa.Sim.PtrArith
import Vsa.Sim.StrlenSpec
import Vsa.Sim.StrcpySpec
import Vsa.Sim.SnprintfSpec18

/-!
# `bvptr` — the canonical pointer-normalization simp set

Tags the recurring effective-address / immediate rewrites so compositions can
normalize site-post values with one bounded call instead of naming each lemma:

```lean
simp (disch := omega) only [bvptr] at hval
```

`simp only` with a fixed set: no search, no unfolding beyond these rules, so
compile times stay flat.  The `disch := omega` discharges the no-wrap side
conditions of the conditional rules (`ptr_toNat`, `ptr_addoff`, `ptr_sub`);
omit it when only the unconditional rules are needed (`sext0_add`, `ptr_succ`,
`sp_dec*_restore`, the `sext_*_toNat` constants).

Grow the set here (`attribute [bvptr] …`) — never inline one-off `show`/`rw`
chains for shapes these rules cover.
-/

namespace Vsa.Sim

attribute [bvptr]
  -- unconditional pointer identities
  sext0_add          -- v + sext 0x000 = v            (StrlenSpec)
  add_sext0          -- (StrcpySpec twin)
  ptr_succ           -- base + ofNat i + sext 1 = base + ofNat (i+1)  (MemcpySpec)
  add_ofNat_zero     -- v + ofNat 0 = v               (SnprintfSpec18)
  sp_dec16_restore sp_dec32_restore sp_dec48_restore sp_dec64_restore
  -- sign-extended negative-immediate constants
  sext_fff_toNat sext_ff8_toNat sext_ff0_toNat
  sext_fe0_toNat sext_fd0_toNat sext_fc0_toNat
  -- conditional (need disch := omega)
  ptr_toNat          -- (base + ofNat k).toNat = base.toNat + k, no-wrap (MemcpySpec)
  ptr_addoff ptr_sub_toNat

end Vsa.Sim
