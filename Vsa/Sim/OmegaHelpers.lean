import Vsa.Sim.EvalSimCommon

/-!
# `OmegaHelpers` — reusable omega-obligation lemmas (omega paid ONCE)

Companion to `Vsa/Sim/SpillSafe.lean`. That file collapsed the "spill load/store safety"
omega shape (the ~45×/file `(by rw [haddrK]; omega)` over `sp.toNat - K`). This file collapses
the OTHER recurring omega shapes catalogued in `experiments/elab-wall-strategy.md`
(the "omega-shape taxonomy" table), each proven once here (omega compiled into the olean)
so that callsites in the `Eval*` / `rows/Eval*Row` cohort apply them by name (typecheck only,
no per-site omega re-run).

Each lemma's conclusion is stated to match the callsite goal VERBATIM so it is
`exact`/`apply`-compatible. See per-lemma docstrings for the exact site signature + callsite
(file:line in `rows/EvalGtRow.lean`) that justifies the statement.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.

## Migration readiness (`import Vsa.Sim.OmegaHelpers`)

The cohort files (`rows/EvalGtRow`, `rows/EvalLeRow`, `EvalBinSim2/3/4`, `EvalLogical3/4`)
already import `EvalBinSim4`/`EvalSimCommon` transitively; add `import Vsa.Sim.OmegaHelpers`
to each and replace the tactic blocks per the table below.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Alloc

namespace Vsa.Sim

/-! ## Shape 1 — expr-relative load (`aExpr + n`)

Site signature: `site_8000351c_ee` (`Vsa/Sim/AddTailSites.lean:160`) takes four separate
preconditions over `(v8 + sign_extend (m := 64) (0x008#12)).toNat`:
`hlo`/`hhiram`/`hhtif`/`halign`. The `.gt` row (`rows/EvalGtRow.lean:176-182`) supplies them as
`(by rw [hop8]; omega)`, `(by rw [hop8]; omega)`, `(by rw [hop8, htoh]; right; omega)`,
`(by rw [hop8]; omega)` — where
`hop8 : (aExpr + sign_extend (0x008#12)).toNat = aExpr.toNat + 8`
(`EvalGtRow:103`) and the frame facts are
`hexprAl : aExpr.toNat % 4 = 0`, `hexprLo : 0x80000000 ≤ aExpr.toNat`,
`hexprHi : aExpr.toNat + 16 ≤ 0x100000000`, `hexprWin : tohostAddr + 8 ≤ aExpr.toNat`
(`EvalGtRow:50-52`, destructured at `:83-85`).

We state the conclusion in the RAW `(aExpr + sign_extend imm).toNat` form (taking the offset
equation `hoff` as `SpillSafe.spill_load_safe4` does with `haddr`), concluding the four-way
conjunction so a caller can
`obtain ⟨hlo, hhi, hhtif, halign⟩ := expr_load_safe4 … hop8 hexprAl hexprLo hexprHi hexprWin (by decide)`
and pass the four fields to the site. `hoff` fixes both the address value AND the register
expression, so the conjuncts match the site's argument types verbatim. -/

/-- The four preconditions of a 4-byte expr-relative LOAD (`lw`) at `aExpr.toNat + n`
(`n ∈ {4, 8}`), derived once from the frame bounds + the ground offset facts. The htif
disjunct is `Or.inr` (`tohostAddr + 8 ≤ addr`) because these addresses are HIGH (≥ aExpr ≥
tohost+8). Matches `site_*_ee`'s `hlo`/`hhiram`/`hhtif`/`halign` after `rw [hoff]`. -/
theorem expr_load_safe4 (aExpr _eAddr : BitVec 64) (imm : BitVec 12) (n : Nat)
    (hoff : (aExpr + sign_extend (m := 64) imm).toNat = aExpr.toNat + n)
    (hexprAl : aExpr.toNat % 4 = 0) (hexprLo : 0x80000000 ≤ aExpr.toNat)
    (hexprHi : aExpr.toNat + 16 ≤ 0x100000000) (hexprWin : tohostAddr + 8 ≤ aExpr.toNat)
    (hn : n + 4 ≤ 16) (hn4 : n % 4 = 0) :
    0x80000000 ≤ (aExpr + sign_extend (m := 64) imm).toNat ∧
    (aExpr + sign_extend (m := 64) imm).toNat + 4 ≤ 0x100000000 ∧
    ((aExpr + sign_extend (m := 64) imm).toNat + 4 ≤ tohostAddr ∨
      tohostAddr + 8 ≤ (aExpr + sign_extend (m := 64) imm).toNat) ∧
    (aExpr + sign_extend (m := 64) imm).toNat % 4 = 0 := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  rw [hoff]
  refine ⟨by omega, by omega, Or.inr (by omega), by omega⟩

/-! ## Shape 2 — low-address slot / constant-string (CS) site

Site signature: same LOAD family (`site_8000354c_ee`, `site_80003660`) — four preconditions
`hlo`/`hhiram`/`hhtif`/`halign` over `(base + sign_extend (0x000#12)).toNat`, but here `base`
is a LOW STATIC address (`0x80019fb0` slot @`EvalGtRow:472-481`, `0x80019ff0` CS ptr
@`EvalGtRow:910-917`). The htif disjunct taken is the LEFT one because the address is BELOW
tohost (`0x8001ad00`): `addr + 4 ≤ tohostAddr`. Callsite:
`(by rw [hslotAddr]; omega)`, `(by rw [hslotAddr]; omega)`,
`(by rw [hslotAddr]; rw [htoh]; left; omega)`, `(by rw [hslotAddr])`
where `hslotAddr : (0x80019fb0#64 + sign_extend (0x000#12)).toNat = 0x80019fb0`.

Note the 4th (align) arg here is `(by rw [hslotAddr])` with NO omega — after the rewrite the
goal is the ground `0x80019fb0 % 4 = 0` closed by `rfl`/the rewrite; we still include the
`% 4 = 0` conjunct (discharged by `decide` inside, paid once).

We generalise over the concrete address `A` and require the ground facts `A % 4 = 0` and
`A + 4 ≤ tohostAddr` and `0x80000000 ≤ A` and `A + 4 ≤ 0x100000000` (all `by decide` at the
callsite for the two concrete addresses in the cohort). -/

/-- The four preconditions of a 4-byte LOAD at a LOW static address `A` (slot/CS site),
with the htif disjunct as `Or.inl` (`A + 4 ≤ tohostAddr`). Matches `site_*_ee`'s
`hlo`/`hhiram`/`hhtif`/`halign` after `rw [hslotAddr]` (which fixes the `.toNat` to `A`). -/
theorem slot_load_safe (_A eAddr : BitVec 64) (imm : BitVec 12) (Aval : Nat)
    (hAddr : (eAddr + sign_extend (m := 64) imm).toNat = Aval)
    (hlo : 0x80000000 ≤ Aval) (hhi : Aval + 4 ≤ 0x100000000)
    (hbelow : Aval + 4 ≤ tohostAddr) (hal : Aval % 4 = 0) :
    0x80000000 ≤ (eAddr + sign_extend (m := 64) imm).toNat ∧
    (eAddr + sign_extend (m := 64) imm).toNat + 4 ≤ 0x100000000 ∧
    ((eAddr + sign_extend (m := 64) imm).toNat + 4 ≤ tohostAddr ∨
      tohostAddr + 8 ≤ (eAddr + sign_extend (m := 64) imm).toNat) ∧
    (eAddr + sign_extend (m := 64) imm).toNat % 4 = 0 := by
  rw [hAddr]
  refine ⟨hlo, hhi, Or.inl hbelow, hal⟩

/-! ## Shape 3 — code-region disjointness (feeds `loaded_eval_expr_agreeP`)

Callsite (`rows/EvalGtRow.lean:1048-1050`, and `:1075, :1237, :1262, :1286`):
```
exact loaded_eval_expr_agreeP c.σ.mem m1
  (fun k hk => (getElem_writeMap8_disjoint c.σ.mem (sp.toNat-848) k (sdData_val V968)
    (by rcases hcodeStk with h | h <;> omega)).symm) hcode
```
`loaded_eval_expr_agreeP` (`EvalSimCommon.lean:533`) requires
`ha : ∀ a, (0x80003164 ≤ a ∧ a < 0x80003fe0) → m[a]? = m'[a]?`, so at the callsite
`hk : 0x80003164 ≤ k ∧ k < 0x80003fe0`. `getElem_writeMap8_disjoint` (`ValueSpec.lean:167`)
requires `hk' : k < a8 ∨ a8 + 8 ≤ k` with `a8 = sp.toNat - 848` (the store window base — the
spill slots written by the store spine are all in `[sp-848, sp-832]`, i.e. `a8 ∈ {848,840,832}`).
The disjunction `hcodeStk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo` (`EvalGtRow:63`,
destructured `:86`) + frame `hSLloSp : SL.lo + 1088 ≤ sp.toNat` (`:67`, `:87`) discharge it:
- left branch `sp.toNat ≤ 0x80003164 ≤ k` ⇒ `sp.toNat - 848 + 8 ≤ k` (right disjunct);
- right branch `0x80003fe0 ≤ SL.lo`, `SL.lo + 1088 ≤ sp.toNat` ⇒ `sp.toNat - 848 > 0x80003fe0 > k`
  (left disjunct).

We expose the disjunctness fact directly (the thing after the `rcases … <;> omega`), so the
callsite becomes `… (code_disjoint hcodeStk hSLloSp hk (by decide))`. `off` is the store base
offset (848/840/832); `hk` is the code-window membership of `k`. -/

/-- Disjointness of a code-window index `k ∈ [0x80003164, 0x80003fe0)` from an 8-byte store at
`sp.toNat - off` (`off ∈ {832,840,848}`), given the frame stack disjunction `hcodeStk`. This is
exactly the goal `k < (sp.toNat - off) ∨ (sp.toNat - off) + 8 ≤ k` fed to
`getElem_writeMap8_disjoint`. -/
theorem code_disjoint (sp : BitVec 64) (SLlo k off : Nat)
    (hcodeStk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SLlo)
    (hSLloSp : SLlo + 1088 ≤ sp.toNat)
    (hk : 0x80003164 ≤ k ∧ k < 0x80003fe0) (hoff8 : 8 ≤ off) (hoff : off ≤ 1088) :
    k < (sp.toNat - off) ∨ (sp.toNat - off) + 8 ≤ k := by
  rcases hcodeStk with h | h <;> omega

/-! ## Shape 4 — value-region disjointness (feeds `loaded_bool_writeMap8`)

Callsite (`rows/EvalGtRow.lean:1514-1518`):
```
loaded_bool_writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val V968)
  (by rcases hviStk with h | h <;> omega) hVbool
```
`loaded_bool_writeMap8` (`EvalBoolSim.lean:159`) requires
`hdis : a8 + 8 ≤ 0x800027f8 ∨ 0x8000280c ≤ a8` with `a8 = sp.toNat - off` (`off ∈ {832,840,848}`).
The frame disjunction `hviStk : sp.toNat ≤ 0x800027f8 ∨ 0x8000280c ≤ SL.lo` (`EvalGtRow:64`,
destructured `:86`) + `hSLloSp : SL.lo + 1088 ≤ sp.toNat` discharge it:
- left `sp.toNat ≤ 0x800027f8` ⇒ `sp.toNat - off + 8 ≤ 0x800027f8` (left disjunct);
- right `0x8000280c ≤ SL.lo`, `SL.lo + 1088 ≤ sp.toNat` ⇒ `0x8000280c ≤ sp.toNat - off` (right).

We expose the `value_bool`-region disjointness fact directly, so the callsite becomes
`(vi_disjoint hviStk hSLloSp (by decide))`. -/

/-- Disjointness of an 8-byte store at `sp.toNat - off` (`off ∈ {832,840,848}`) from the
`value_bool` code window `[0x800027f8, 0x8000280c)`, given the frame stack disjunction `hviStk`.
This is exactly the `hdis` goal of `loaded_bool_writeMap8`. -/
theorem vi_disjoint (sp : BitVec 64) (SLlo off : Nat)
    (hviStk : sp.toNat ≤ 0x800027f8 ∨ 0x8000280c ≤ SLlo)
    (hSLloSp : SLlo + 1088 ≤ sp.toNat) (hoff8 : 8 ≤ off) (hoff : off ≤ 1088) :
    (sp.toNat - off) + 8 ≤ 0x800027f8 ∨ 0x8000280c ≤ (sp.toNat - off) := by
  rcases hviStk with h | h <;> omega

/-! ## Shape 5 — frame-agreement window (feeds `read64_agreeP` / `read32_agreeP`)

Callsite (`rows/EvalGtRow.lean:1688-1695`):
```
rw [← read64_agreeP hAgTop (fun j hj => ⟨by omega, by omega⟩)]; exact hslotRa
```
where `hAgTop : AgreeP (fun k => sp.toNat - 32 ≤ k ∧ k < sp.toNat) c.σ.mem τ38.mem`
(`EvalGtRow:1684`) and `read64_agreeP` (`ReprSurvival.lean:115`) needs
`hP : ∀ j, j < 8 → P (a + j)`, i.e. per index `j < 8` prove
`sp.toNat - 32 ≤ a + j ∧ a + j < sp.toNat` for the four read bases
`a ∈ {sp-8, sp-16, sp-24, sp-32}` (the callee-saved slots). The `⟨by omega, by omega⟩` closes
the two conjuncts from `hsp32 : 32 ≤ sp.toNat` (available as `hsp1088 : 1088 ≤ sp.toNat`,
`EvalGtRow:96`) and `hj : j < 8` (and `a`'s offset ≤ 32).

The same shape reappears at `read32_agreeP hAg (fun j hj => ⟨by omega, by omega⟩)`
(`EvalGtRow:1987`) with window `[sp-968, sp-952)` and read32 base `sp-968`, and at the paired
`read64_agreeP hAg …` (`:1989`) with the same window and read64 base `sp-968`.

We provide the per-index membership term. `frame_window8`/`frame_window4` produce exactly the
`fun j hj => ⟨_, _⟩` witness (a function, applied at each index by `read*_agreeP`), so a callsite
becomes `read64_agreeP hAgTop (frame_window8 sp 8 32 0 hsp1088 (by decide) (by decide))`.
`d` = base distance below `sp`; `w` = window lower distance; `lo` = window upper distance
(`0` when the window's upper edge is `sp` itself, as at `:1688-1695`). Requirements: `w ≤ sp.toNat`
(no underflow), `d ≤ w` (base at-or-above floor), `lo + 8 ≤ d` (the 8-byte span sits under the
upper edge). -/

/-- Per-index window-membership witness for an 8-byte `read64_agreeP` at base `sp.toNat - d`
inside the window `[sp.toNat - w, sp.toNat - lo)`. Produces the `fun j hj => ⟨_, _⟩` argument
verbatim. For the `[sp-32, sp)` slots (`EvalGtRow:1688-1695`) use `lo = 0`; for the
`[sp-968, sp-952)` window (`:1989`) use `w = d = 968, lo = 952`. -/
theorem frame_window8 (sp : BitVec 64) (d w lo : Nat)
    (hsp : w ≤ sp.toNat) (hdw : d ≤ w) (hd : lo + 8 ≤ d) :
    ∀ j, j < 8 →
      (sp.toNat - w ≤ (sp.toNat - d) + j ∧ (sp.toNat - d) + j < sp.toNat - lo) := by
  intro j hj
  exact ⟨by omega, by omega⟩

/-- Per-index window-membership witness for a 4-byte `read32_agreeP` at base `sp.toNat - d`
inside the window `[sp.toNat - w, sp.toNat - lo)`. Produces the `fun j hj => ⟨_, _⟩` argument.
`w` is the window's lower distance below `sp`, `lo` its upper distance (`lo < w`); base `sp - d`
with `d ≤ w` (base at-or-above the window floor) and `lo + 4 ≤ d` (the 4-byte span sits under
the upper edge). For the read32-at-floor case in `EvalGtRow:1987`, `d = w` (base is the floor). -/
theorem frame_window4 (sp : BitVec 64) (d w lo : Nat)
    (hsp : w ≤ sp.toNat) (hdw : d ≤ w) (hd : lo + 4 ≤ d) :
    ∀ j, j < 4 →
      (sp.toNat - w ≤ (sp.toNat - d) + j ∧ (sp.toNat - d) + j < sp.toNat - lo) := by
  intro j hj
  exact ⟨by omega, by omega⟩

end Vsa.Sim
