import Vsa.Sim.EvalBinSim
import Vsa.Sim.rows.StrArmChain

-- discipline: allow(R7-conj-tower-def) The only ∃ in CODE are the two `rPtr`/`lPtr`
-- fields of the NAMED-FIELD structure `StrOperandsStaged` (a CString-pointer witness
-- each); the tower this file consumes (`TwoSubReturn`) is destructured through the
-- SINGLE named lemma `strOperandsStaged_of_twoSubReturn` (one `obtain`, no positional
-- chains), exactly the R7-compliant pattern. The whole-file ∃ count is inflated by the
-- doc-comments that QUOTE the landed tower's shape to explain the readback.

/-!
# `BinStrReadback` — the kind-3 operand readback out of the kind-GENERIC `TwoSubReturn`

## The (a)-vs-(b) verdict, machine-checked

The str-comparison / str-concat cells were blocked (ledger `strarm-kind3-blockb`)
on what the prior note called "`blockB_binary` AT KIND 3 — the str-operand
operand-recursion prologue".  Studying the LANDED statement shows the premise was
wrong: **`blockB_binary` (`Vsa/Sim/EvalBinSim.lean`) is ALREADY kind-generic.**

* its value parameters are `vl vr : Value` — no `.int` anywhere in the signature;
* the entry `ArmEntryK … (.binary op el er)` is kind-blind (it pins the node +
  entry registers + the entry store; nothing about operand kinds);
* the two operand sub-derivations are consumed through `EvalIH`/`SubEvalReturn`
  (`Vsa/Sim/EvalRecCommon.lean`), whose post is `ValueRepr c.σ.mem N φc' subsret vsub`
  for an ARBITRARY `vsub : Value` (`SubEvalReturn` line 205–206);
* the produced post `TwoSubReturn` (`EvalBinSim.lean:118`) stages the sub-values as
  the GENERIC `ValueRepr c.σ.mem N φcr (sp-944) vr` / `ValueRepr … (sp-968) vl`
  (lines 149–150) — again no `.int`.

The ONLY int-flavoured thing in `blockB_binary` is the `hVlSurv` *premise* (the
left value's payload survives the right sub-call), and its own doc says "For
non-string `vl` (e.g. the `int`-pilot) it is vacuous" — i.e. it is the general
survival hypothesis, which the str instance must supply non-vacuously.  It is a
PARAMETER, not baked-in int-ness.

**Verdict: (b).**  The landed statement already lands a kind-blind `TwoSubReturn`;
the str side does NOT need a new `blockB` variant.  What it needs is a *readback
lemma*: from a `.str`-kind `TwoSubReturn` (both operands `.str`), extract the two
operand kind tags (`read32 = 3`, the pins `strKindCheckRow` demands at entry —
`x10 = 3`, `x16 = 3`) and the two CString payload POINTERS (`read64 (a+8) = p`,
`p ≠ 0`, `CString`), which the str arm stages into `a7`/`s3` for the strcmp seam.

That readback is a definitional projection: `ValueRepr m N φc a (.str s)` IS
`read32 m a = some 3 ∧ ∃ p, read64 m (a+8) = some p ∧ p ≠ 0 ∧ CString m p s`
(`Vsa/RuntimeRepr.lean:82–83`).  This file lands that projection as a named bundle
`StrOperandsStaged` + the one destructuring lemma `strOperandsStaged_of_twoSubReturn`
consuming the `TwoSubReturn` tower through its own named field access (per CLAUDE.md
R6/R7: one named destructurer beside the tower, never a positional `.2.2.2` chain).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Vsa.Machine (MState Config)
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While
open Vsa.Alloc
open Vsa.Logic

namespace Vsa.Sim

/-! ## The kind-3 operand bundle -/

/-- **`StrOperandsStaged`** — what a `.str`/`.str` `TwoSubReturn` exposes for the
str arm's kind-check + strcmp seam.  Both operand value boxes (`sp-944` = right,
`sp-968` = left) carry `.str` `ValueRepr`s, so each yields:

* a kind tag `read32 = some 3` — the entry pins `strKindCheckRow` demands
  (`x10 = 3` from the RIGHT box after the `lw a0,8(box)` staging, `x16 = 3` from
  the LEFT box) that drive the `bnez`/`beqz` guards at `0x80003628`/`0x80003634`;
* a CString pointer `pr`/`pl` (`read64 (box+8)`, `≠ 0`) whose bytes spell the
  evaluated operand string — the pointers the arm marshals into `a7` (right) /
  `s3` (left) for the strcmp call seam (`mv a1,a7; mv a0,s3; jal strcmp`).

Named-field structure per CLAUDE.md (never an anonymous ∃/∧ tower). -/
structure StrOperandsStaged
    (m : Mem) (N : NativeAddrs) (spN : Nat) (sl sr : String) : Prop where
  /-- RIGHT operand box (`sp-944`) kind tag = 3 (`str`). -/
  rKind : read32 m (spN - 944) = some 3
  /-- RIGHT operand CString pointer (nonzero) + payload. -/
  rPtr : ∃ pr, read64 m (spN - 944 + 8) = some pr ∧ pr ≠ 0 ∧ CString m pr sr
  /-- LEFT operand box (`sp-968`) kind tag = 3 (`str`). -/
  lKind : read32 m (spN - 968) = some 3
  /-- LEFT operand CString pointer (nonzero) + payload. -/
  lPtr : ∃ pl, read64 m (spN - 968 + 8) = some pl ∧ pl ≠ 0 ∧ CString m pl sl

/-! ## The readback: `.str`/`.str` `TwoSubReturn` → `StrOperandsStaged`

`TwoSubReturn` (`EvalBinSim.lean:118`) is a landed ∃/∧ tower; per CLAUDE.md R7 we
consume it through ONE named destructurer.  The tower's sub-value clause is

```
(∃ φfm φcm, PhiExtends … ∧ PhiExtends … ∧
   (∃ φcr, PhiExtends … ∧ ValueRepr c.σ.mem N φcr (sp-944) vr) ∧
   (∃ φcl,               ValueRepr c.σ.mem N φcl (sp-968) vl) ∧
   (∃ φf' φc', … StoreRepr …))
```

so the two `ValueRepr`s live at fixed positions inside it.  For `vr = .str sr` and
`vl = .str sl`, each `ValueRepr … (.str s)` UNFOLDS definitionally (it is a `def`
by pattern match, `RuntimeRepr.lean:82`) to
`read32 … = some 3 ∧ ∃ p, read64 … (a+8) = some p ∧ p ≠ 0 ∧ CString … p s`.
The readback is that unfold — the kind tag and pointer are the two conjuncts. -/

/-- **The kind-3 readback.**  From a `TwoSubReturn` whose two sub-values are
`.str sr` (right, at `sp-944`) and `.str sl` (left, at `sp-968`), project out the
`StrOperandsStaged` bundle: the two kind tags (= 3) and the two CString pointers.

`spN` is `sp.toNat`; the boxes sit at `spN-944` (right) / `spN-968` (left), exactly
`TwoSubReturn`'s staging addresses.  Consumed by the str arm to satisfy
`strKindCheckRow`'s entry (kind pins) and stage `a7`/`s3` (pointers). -/
theorem strOperandsStaged_of_twoSubReturn
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat) (st' st'' : Vsa.While.St) (sl sr : String)
    (sp r sret : BitVec 64) (v8 v9 v18 : BitVec 64) (m0 : Mem) (c : Config)
    (hTSR : TwoSubReturn gpre N A SL φf φc nf nc st' st'' (.str sl) (.str sr)
      sp r sret v8 v9 v18 m0 c) :
    StrOperandsStaged c.σ.mem N sp.toNat sl sr := by
  -- Peel the tower down to the two sub-value `ValueRepr`s.  Named destructuring
  -- of the LANDED `TwoSubReturn` def (a single `obtain` — no positional chains).
  obtain ⟨_hG, _htick, _hpc, _hra, _hs9, _hsp, _hmi, _hout, _hframe, _hs3spill,
    ⟨_φfm, _φcm, _hpf, _hpc0,
      ⟨_φcr, _hpcr, hvalR⟩, ⟨_φcl, hvalL⟩, _hstoreBundle⟩,
    _hcode, _hslotRa, _hslot8, _hslot9, _hslot18, _hMemExt, _hmemframe⟩ := hTSR
  -- `ValueRepr … (.str s)` is definitionally the kind/pointer conjunction.
  obtain ⟨hrKind, pr, hrRead, hrNe, hrCStr⟩ := hvalR
  obtain ⟨hlKind, pl, hlRead, hlNe, hlCStr⟩ := hvalL
  exact
    { rKind := hrKind
      rPtr := ⟨pr, hrRead, hrNe, hrCStr⟩
      lKind := hlKind
      lPtr := ⟨pl, hlRead, hlNe, hlCStr⟩ }

#print axioms strOperandsStaged_of_twoSubReturn

/-! The readback is consumed by `Vsa/Sim/StrCmpCell.lean`
(`strCmpKindEntry_of_twoSubReturn`, `strCmpSeamGeom_of_resid`). -/

end Vsa.Sim
