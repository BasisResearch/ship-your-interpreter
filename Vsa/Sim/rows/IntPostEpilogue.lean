import Vsa.Sim.EvalRecCommon
import Vsa.Sim.StepFrameOut

/-!
# `intPostToEpilogue` — the SHARED binop value-int arm epilogue assembly

Both landed binop int arms `blockC_mul` (`rows/EvalMulRow.lean`) and `blockC_div`
(`rows/EvalDivRow.lean`) end with a BYTE-IDENTICAL two-instruction epilogue

  `ld s3,<off>(sp) ; j 0x800033ec`

that restores the entry `s3` (= `x19`) from its spill slot and jumps to the shared
value-dispatch exit at `0x800033ec`, then package the resulting state as
`PreEpilogueVD`.  The two arms differ ONLY in (a) the produced boxed value
(`.int (wrap64 (a*b))` vs `.int (wrap64 (a.tdiv b))`), (b) the concrete `ld`/`j`
site helpers (different immediate offsets / decode bytes), and (c) the *reach-back*
memory / callee-saved-register frame collapse through their own arm ladders.

`intPostToEpilogue` factors the SHARED part: the packaging of `PreEpilogueVD` from a
fully-transported epilogue-exit config `c` (PC already at `0x800033ec`, `x9=sret`,
`x2=sp-1088`, callee-saved frame already collapsed to `g`, memory pinned to the
`value_int`-post memory).  The arm supplies the boxed value as a parameter `v`, runs
its two site helpers to reach `c`, collapses its own frame, and hands the transported
facts here.  This removes the ~30-line `PreEpilogueV`/`PreEpilogueVD` marshalling
(`hstore_fin`/`hSurvSL_fin`/`hMemExt_fin` derivations + the ~30-conjunct final
`refine`) from every arm, and battle-tests the shared shape.

The precondition bundle is exactly the set of facts both arms hold at their final
config just before assembling `PreEpilogueVD`:

* the epilogue-exit register/tick/output state (`GoodState`, PC, `x9`, `x2`,
  `minstret`, `sailOutput`, `Eval_exprLoaded`),
* the value + store representations pinned to the exit memory,
* the collapsed callee-saved frame (`AbiPreservedNoise → = g`),
* the four callee-saved spill-slot reads and the `[SL.lo,SL.hi)`-survival of the
  extended store,
* the memory frame vs the entry `m0` (`MemExtends` + the per-address
  `sret`-buffer-or-unchanged split),
* the geometry the epilogue loads need.

It is agnostic to how the arm reached the exit config — the whole divergence
(dispatch ladder, libgcc seam, spill layout) stays at the call site.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code
open Register

namespace Vsa.Sim

/-- **Shared binop value-int arm epilogue packaging.**

Given the epilogue-exit config `c` (already at `0x800033ec` after the arm's
`ld s3 ; j 0x800033ec`) together with the fully-transported epilogue facts both
`blockC_mul` and `blockC_div` establish at that config — the register/store/value
representations, the collapsed callee-saved frame, the spill-slot reads, and the
memory frame vs the entry `m0` — repackage them as the `PreEpilogueVD` existential
that `blockD_v_rec` consumes.  The boxed value `v` is a parameter (the arm supplies
`.int (wrap64 (a*b))` / `.int (wrap64 (a.tdiv b))`). -/
theorem intPostToEpilogue
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc φfm φcm φf' φc' : Addr → Nat)
    (st' st'' : Vsa.While.St) (v : Value)
    (sp r sret : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (m0 : Mem) (c : Config)
    -- φ-extension chain from block C's callee subproofs (`φf → φfm → φf'`)
    (hpfm : PhiExtends φf φfm st'.store.frames.size)
    (hpcm : PhiExtends φc φcm st'.store.closures.size)
    (hpf' : PhiExtends φfm φf' st''.store.frames.size)
    (hpc' : PhiExtends φcm φc' st''.store.closures.size)
    -- epilogue-exit register / tick / output state
    (hG : GoodState c.σ) (htick : c.tick < 2)
    (hpc : c.σ.regs.get? Register.PC = some (0x800033ec#64))
    (hx9 : c.σ.regs.get? Register.x9 = some sret)
    (hx2 : c.σ.regs.get? Register.x2 = some (sp - 1088#64))
    (hminstret : ∃ w, c.σ.regs.get? Register.minstret = some w)
    (hout : c.σ.sailOutput = out0) (houtStr : String.join out0.toList = st''.out)
    (hcode : Eval_exprLoaded c.σ.mem)
    -- value + store at the exit memory
    (hval : ValueRepr c.σ.mem N φc' sret.toNat v)
    (hstore : StoreRepr c.σ.mem N A φf' φc' st''.store)
    (hSurvSL : ∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st''.store)
    -- collapsed callee-saved frame
    (hframeG : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      c.σ.regs.get? R = g R)
    -- the four callee-saved spill-slot reads
    (hslotRa : read64 c.σ.mem (sp.toNat - 8) = some r.toNat)
    (hslotS0 : read64 c.σ.mem (sp.toNat - 16) = some v8.toNat)
    (hslotS1 : read64 c.σ.mem (sp.toNat - 24) = some v9.toNat)
    (hslotS2 : read64 c.σ.mem (sp.toNat - 32) = some v18.toNat)
    -- entry ghost frame values
    (hgv8 : g Register.x8 = some v8) (hgv9 : g Register.x9 = some v9)
    (hgv18 : g Register.x18 = some v18) (hgv2 : g Register.x2 = some sp)
    -- memory frame vs the entry `m0`
    (hMemExt : MemExtends m0 c.σ.mem)
    (hmemframe : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ c.σ.mem[a]? = m0[a]?)
    -- geometry the epilogue loads need
    (hsp1088 : 1088 ≤ sp.toNat) (hspRam : sp.toNat ≤ 0x100000000)
    (hspLo : 0x80000000 ≤ sp.toNat) (hspHtif : tohostAddr + 16 + 1088 ≤ sp.toNat)
    (hsp8 : sp.toNat % 8 = 0) (hraAl : r.toNat % 4 = 0) :
    ∃ (mpre : Mem) (φfm' φcm' φfe φce : Addr → Nat),
      PhiExtends φf φfm' st'.store.frames.size ∧
      PhiExtends φc φcm' st'.store.closures.size ∧
      PhiExtends φfm' φfe st''.store.frames.size ∧
      PhiExtends φcm' φce st''.store.closures.size ∧
      PreEpilogueVD g N A SL φfe φce st'' v sp r sret v8 v9 v18 out0 m0 mpre c := by
  refine ⟨c.σ.mem, φfm, φcm, φf', φc',
    hpfm, hpcm, hpf', hpc', ⟨?_, hMemExt, hSurvSL⟩⟩
  exact ⟨hG, htick, hpc, hx9, hx2, hminstret, hout, houtStr, rfl, hcode, hval,
    hstore, hframeG, hslotRa, hslotS0, hslotS1, hslotS2, hgv8, hgv9, hgv18, hgv2,
    hmemframe, hsp1088, hspRam, hspLo, hspHtif, hsp8, hraAl⟩

#print axioms intPostToEpilogue

end Vsa.Sim
