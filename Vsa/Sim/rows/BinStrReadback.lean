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

/-! ## Making the readback LOAD-BEARING: reach `strKindCheckRow`'s entry

`strKindCheckRow` (`StrArmChain.lean`) is the LANDED kind-check span; its entry
`SegPre strKindCheck strKindL [] 0x80003628 m0` demands the two operand kind tags
staged into REGISTERS — `strKindL = [(10, 3), (16, 3)]`, i.e. `x10 = 3` (right
kind), `x16 = 3` (left kind) — which drive the `bnez`/`beqz` guards.  Those come
from the op-dispatch's str-arm STAGING span (`0x8000351c … → 0x80003628`): after the
`jr` op-dispatch lands the str-compare arm, the arm loads each operand's kind field
`lw`/`ld` off its value box (`sp-944` right, `sp-968` left — exactly the addresses
my readback pins) into `a0`/`a6`, and stages the two CString pointers (`read64
box+8`) into `a7`/`s3` for the strcmp seam.

The readback (`strOperandsStaged_of_twoSubReturn`) supplies the SEMANTIC content of
that span's premise: the box kind tags ARE 3, the pointers ARE nonzero CStrings.
What remains is the machine reach — the concrete instruction span that MOVES box
bytes into registers.  That is a genuine (unbuilt) straight-line/dispatch span; I
name it as a typed residual rather than assert it.  `StrArmStageSpan` reads
`StrOperandsStaged` and produces the `strKindCheckRow` entry; `strReadbackToKindCheck`
then composes it with the readback + the landed `strKindCheckRow` + the landed
`StrSeamSpan2` seam (`strKindToStrcmp_seam`) to REACH the strcmp entry from a
`.str`/`.str` `TwoSubReturn` — the whole front of `StrArmToStrcmp` modulo this one
named staging span. -/

/-- **The str-arm operand-box STAGING span residual** — the honest machine span
from the `.str`/`.str` `TwoSubReturn` entry config to `strKindCheckRow`'s entry.
`Pre` is any predicate the caller reaches at the `TwoSubReturn` PC `0x8000351c`
(carrying `StrOperandsStaged` for its memory); the span runs the op-dispatch str-arm
box→register staging (`0x8000351c … → 0x80003628`: the `jr` op-dispatch into the
str-compare arm + the `lw`/`ld` box reads that stage each operand's kind field into
`a0`/`a6` and its CString pointer into `a7`/`s3`) to land the kind-check entry
`SegPre strKindCheck strKindL [] 0x80003628 m0` (`x10 = 3`, `x16 = 3` staged).

The readback (`strOperandsStaged_of_twoSubReturn`) supplies this span's SEMANTIC
obligation (box tags = 3, pointers are CStrings); the residual is the concrete
instruction transport, dischargeable as a `#derive_case` seg once the op-dispatch
route to the str-compare arm is pinned.  Named as a typed premise so the kind-3
readback is load-bearing, mirroring `StrSeamSpan2`. -/
def StrArmStageSpan (Pre : Config → Prop) (m0 : Mem) : Prop :=
  Triple Pre (SegPre strKindCheck strKindL [] 0x80003628#64 m0)

/-- **Readback ≫ staging ≫ kind-check ≫ strcmp seam.**  From any `Pre` the caller
reaches at the `.str`/`.str` `TwoSubReturn` entry, the staging span (`StrArmStageSpan`,
named) reaches `strKindCheckRow`'s entry, the LANDED `strKindCheckRow` runs the
kind-check branch to `0x80003b0c`, and the named `StrSeamSpan2` seam marshals into the
strcmp entry — landing `strcmp_full_pre`.  This threads the kind-3 readback THROUGH
the two landed rows (`strKindCheckRow` + the `StrSeamSpan2` seam via
`strKindToStrcmp_seam`), leaving exactly ONE unbuilt machine span (`StrArmStageSpan`)
+ the already-named `StrSeamSpan2`, mirroring how `strKindToStrcmp_seam` keeps
`strKindCheckRow` load-bearing. -/
theorem strReadbackToKindCheck
    (Pre : Config → Prop)
    (g : (R : Register) → Option (RegisterType R))
    (pa pb : BitVec 64) (sa sb : String) (mA : Mem) (out0 : Array String)
    (hStage : StrArmStageSpan Pre mA)
    (hSpan2 : StrSeamSpan2 g pa pb sa sb mA out0) :
    Triple Pre (strcmp_full_pre g pa pb (0x80003b1c#64) sa sb mA out0) :=
  Triple.seq hStage (strKindToStrcmp_seam g pa pb sa sb mA out0 hSpan2)

#print axioms strReadbackToKindCheck

end Vsa.Sim
