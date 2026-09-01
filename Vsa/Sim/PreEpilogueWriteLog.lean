import Vsa.Sim.EvalSimCommon
import Vsa.Sim.Regions

/-!
# `PreEpilogueWriteLog` — the value-region readback off a reflected write-log
(Task #48 proposal 2, `preEpilogueV_of_writeLog`)

`PreEpilogueV` (`EvalSimCommon`) demands a `ValueRepr mpre N φc sret.toNat v` at the
shared-epilogue entry — the sret buffer, filled by the arm's value-materialisation
stores.  For a leaf arm each `blockC_*` derives this by hand off `value_*_spec`'s
sret post; for the composite `EX_FN` closure arm the sret is filled by the
`fnArmClosureBuild` seg's own stores (`sd payload,8(sret)`; `sw kind,0(sret)`),
whose effect is a *reflected write-log* (`FnArmClosureBuildPost` = `mem = writeLog
m0 (evalBlocks …).log`).

This file factors the **value-region readback** ONCE, over the generic memory
shape (no arm-specific `evalBlocks` computation): given the two sret-region reads a
`VAL_CLOSURE`-materialising store pair leaves — `read32 mpre sret = 4` (kind) and
`read64 mpre (sret+8) = φc a` (payload = the closure record's `φc`-image) with
`φc a ≠ 0` — assemble `ValueRepr mpre N φc sret.toNat (.closure a)`.  The two reads
themselves are recovered from a `writeMap8` window by the landed `Regions`
readbacks (`read64_writeMap8_rg` etc.); a row supplies them off its concrete
write-log and this lemma folds them into the `ValueRepr` `PreEpilogueV` wants.

## Scope note (machine-checked, not a workaround)

The FULL `PreEpilogueV` is NOT derivable from the write-log alone: it further
demands register facts (`x9 = sret`, `x2 = sp-1088`, `minstret`, the ABI frame),
`StoreRepr` at `φc'`, `GoodState`, and the ~20 geometric region facts — NONE of
which live in the arm's memory write-log (`FnArmClosureBuildPost` carries only
`GoodState ∧ mem = writeLog … ∧ PC`).  So `preEpilogueV_of_writeLog` factors
exactly the value-region piece (the part the write-log DOES determine); the
register/store/geometry fields remain threaded from the arm's `hArm` seam context
(named in `FnArmGeom`).  The `ArmPostGeomV` structure (`rows/ArmPostGeom`) is the
binary post-`TwoSubReturn` residual over the operator jump-table region
`[opTableBase, …)`, a DIFFERENT memory region than the fn-arm sret buffer, so it is
not a source for this closure `ValueRepr` (its `vloaded` field pins
`Value_intLoaded`/`Value_boolLoaded` code, not the sret contents).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-- **`valueRepr_closure_of_reads`** — the closure value-region readback.  From the
two sret-region reads a `VAL_CLOSURE`-materialising store pair leaves (kind `4` at
`sret`, payload `φc a` at `sret+8`, non-null), assemble `ValueRepr … (.closure a)`.
This is exactly `ValueRepr`'s `.closure` clause; stated as a named lemma so every
arm that fills a closure sret (the `EX_FN` seam and any future closure producer)
consumes it by name instead of re-unfolding the definition. -/
theorem valueRepr_closure_of_reads
    (mpre : Mem) (N : NativeAddrs) (φc : Addr → Nat) (sret : BitVec 64) (a : Addr)
    (hkind : read32 mpre sret.toNat = some 4)
    (hpayload : read64 mpre (sret.toNat + 8) = some (φc a))
    (hnz : φc a ≠ 0) :
    ValueRepr mpre N φc sret.toNat (.closure a) :=
  ⟨hkind, hpayload, hnz⟩

/-- **`preEpilogueV_of_writeLog`** — the value-region marshaller.  Given the arm's
epilogue-entry config `c` whose sret buffer's memory `c.σ.mem` (an arm write-log)
yields the two `VAL_CLOSURE` reads (kind `4`, payload `φc a`, non-null), plus the
remaining `PreEpilogueV` fields threaded from the seam context as a bundled
hypothesis `hrest` at the SAME memory, assemble the full `PreEpilogueV … (.closure
a)`.  The value-region readback (`valueRepr_closure_of_reads`) is discharged HERE
ONCE; `hrest` is precisely the register/store/geometry residual the write-log does
not determine (see the scope note), so the arm supplies it from its `hArm` seam.

`hrest` is taken as the `PreEpilogueV` at an ARBITRARY value placeholder that
agrees with the target on everything EXCEPT the `ValueRepr` clause; we substitute
the derived closure `ValueRepr`.  Because `PreEpilogueV` is value-parametric only
through its `ValueRepr` conjunct, feeding the closure readback yields the closure
instance.  This replaces every closure arm's hand assembly of the sret value
region. -/
theorem preEpilogueV_of_writeLog
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (a : Addr)
    (sp r sret : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (m0 mpre : Mem) (c : Config)
    (hmem : c.σ.mem = mpre)
    (hkind : read32 mpre sret.toNat = some 4)
    (hpayload : read64 mpre (sret.toNat + 8) = some (φc a))
    (hnz : φc a ≠ 0)
    -- everything `PreEpilogueV` demands that the write-log does NOT determine:
    -- registers, `StoreRepr`, `GoodState`, geometry.  Bundled as the SAME
    -- `PreEpilogueV` but at the trivially-representable `.null` value (whose
    -- `ValueRepr` clause `read32 mpre sret = 0` is the ONLY differing conjunct);
    -- we OVERRIDE that clause with the closure readback below.
    (hrest : GoodState c.σ ∧ c.tick < 2 ∧
      c.σ.regs.get? Register.PC = some (0x800033ec#64) ∧
      c.σ.regs.get? Register.x9 = some sret ∧
      c.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧
      (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
      c.σ.sailOutput = out0 ∧ String.join out0.toList = st.out ∧
      Eval_exprLoaded mpre ∧
      StoreRepr mpre N A φf φc st.store ∧
      (∀ R : Register, AbiPreservedNoise R →
        (Register.x8 == R) = false → (Register.x9 == R) = false →
        (Register.x18 == R) = false → (Register.x2 == R) = false →
        c.σ.regs.get? R = g R) ∧
      read64 mpre (sp.toNat - 8) = some r.toNat ∧
      read64 mpre (sp.toNat - 16) = some v8.toNat ∧
      read64 mpre (sp.toNat - 24) = some v9.toNat ∧
      read64 mpre (sp.toNat - 32) = some v18.toNat ∧
      g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧ g Register.x18 = some v18 ∧
      g Register.x2 = some sp ∧
      (∀ aa : Nat, ¬ (SL.lo ≤ aa ∧ aa < sp.toNat) → ¬ (A.lo ≤ aa ∧ aa < A.hi) →
        (sret.toNat ≤ aa ∧ aa < sret.toNat + 24) ∨ mpre[aa]? = m0[aa]?) ∧
      1088 ≤ sp.toNat ∧
      sp.toNat ≤ 0x100000000 ∧ 0x80000000 ≤ sp.toNat ∧
      tohostAddr + 16 + 1088 ≤ sp.toNat ∧ sp.toNat % 8 = 0 ∧
      r.toNat % 4 = 0) :
    PreEpilogueV g N A SL φf φc st (.closure a) sp r sret v8 v9 v18 out0 m0 mpre c := by
  obtain ⟨hG, htick, hpc, hx9, hx2, hmi, hout, houtStr, hcode, hstore, hframe,
    hRa, hS0, hS1, hS2, hgx8, hgx9, hgx18, hgx2, hmemframe,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hraAl⟩ := hrest
  have hval : ValueRepr mpre N φc sret.toNat (.closure a) :=
    valueRepr_closure_of_reads mpre N φc sret a hkind hpayload hnz
  exact ⟨hG, htick, hpc, hx9, hx2, hmi, hout, houtStr, hmem, hcode, hval, hstore, hframe,
    hRa, hS0, hS1, hS2, hgx8, hgx9, hgx18, hgx2, hmemframe,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hraAl⟩

#print axioms valueRepr_closure_of_reads
#print axioms preEpilogueV_of_writeLog

end Vsa.Sim
