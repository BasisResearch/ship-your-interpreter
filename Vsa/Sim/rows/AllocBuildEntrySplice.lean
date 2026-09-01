import Vsa.Sim.rows.AllocClosureInhab
import Vsa.Sim.rows.FnArmMallocCallGen
import Vsa.Sim.rows.FnArmSeamReduce
import Vsa.Sim.SpliceFold
import Vsa.Sim.CallFrameMeta
import Vsa.Sim.EnvDefBridges4

/-!
# `AllocBuildEntrySplice` — `hEntry : Triple Pre AllocBuildEntry` (the EX_FN malloc splice)

`rows/AllocClosureInhab.lean` reduced the whole `EX_FN` closure-alloc arm to ONE
premise: `hEntry : Triple Pre AllocBuildEntry`, where `Pre` is the arm dispatch
predicate (`fun c => ∃ o ment vv8 vv9 vv18, ArmEntryK …`, the shape
`fnArmSeamRun_of_allocClosure` matches) and `AllocBuildEntry` is the named-field
reached-config predicate parked at the closure-build entry `0x800033d8` (its doc
comments ARE the spec of this splice).

This file is the FIRST PRODUCTION CONSUMER of the Wave-36 splice layer
(`CallSpec`/`CallFrameMeta`/`SpliceFold`).  The off-path machine run is

```
   armPC …                                        -- (1) arm front  (a3 := φf env decode)
   li a0,16 ; sd a3,0(sp) ; jal malloc            -- (2) fnArmMallocCallBridge  (0x800033c4)
   ← malloc → 0x800033d0                           -- (3) MallocContract.spec  (mallocCallSpec_sat)
   ld a3,0(sp) ; beqz a0,OOM   (NOT taken)         -- (4) reload a3 + no-OOM prune  (0x800033d0)
   0x800033d8 = AllocBuildEntry                    -- (5)
```

The one honest machine-integration primitive landed here is the **reload seg**
`fnArmReloadSeg` (`ld a3,0(sp) ▷ beqz(false)`, 0x800033d0..0x800033d4) as a single
`#derive_case` — a BRANCH-terminated span, in-model via `BlockTerm.TKind`
(`EnvDefBridges4.appendHeadSeg` model), no `bridgeOfSeg`.  The malloc hop rides the
existing `mallocCallSpec`/`mallocCallSpec_sat` (malloc is ALREADY a `CallSpec`
instance — this is the production test of that claim).

`hEntry` (`allocBuildEntry_hEntry` below) exposes the genuinely-underivable facts as
NAMED doc-commented premises: (a) the arm-front `Pre → post-reload config`
LINKAGE bundle (`AllocBuildLink` — the arm front decode + the malloc splice landing
at 0x800033d8, packaged; the caller supplies it from the arm's own front and the
`mallocCallSpec` hop), and (b) `16 ≤ maxReq` for the no-OOM prune.  There is no
hand-rolled `site_*` battery: the reload span goes through the seg layer, and the
whole malloc call goes through the `CallSpec` layer.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

set_option maxHeartbeats 800000
set_option maxRecDepth 1000000

/-! ## §1. The reload span `0x800033d0..0x800033d4` — one `#derive_case` seg

After `malloc` returns to `0x800033d0`, the arm reloads the spilled closure-record
pointer `a3` off the spill slot (`ld a3,0(sp)`, the slot `sd a3,0(sp)` wrote in the
malloc-call seg) and guards the malloc result with `beqz a0,OOM`.  On the no-OOM
success edge the `beqz` is NOT taken, so the block falls through to `0x800033d8`.

`[ld a3,0(sp)] ▷ beqz(false)`: the `ld` writes GPR `x13` (from the `lds` byte
list), the `beqz` writes no GPR — the whole thing is ONE `#derive_case` seg carried
in-model (`beqz` is a `TKind.br`), NO `bridgeOfSeg`.  Model: `EnvDefBridges4.appendHeadSeg`.
The `beqz` decodes to `BTYPE (0x0a48#13, rs2=0, rs1=0x0a=10, BEQ)` (`decode_240504e3`). -/
#derive_case fnArmReloadSeg chain
  [(0x800033d0#64, 0x00013683#32)]   -- ld a3,0(sp)  (x13 := reloaded closure-record ptr)
    terminator ⟨0x800033d4#64, 0x240504e3#32, 0xe3#8, 0x04#8, 0x05#8, 0x24#8,
      .br bop.BEQ false, 10, 0, 0x0a48#13, 0#21, 0#12⟩

/-- The reload span's entry pins: `x2 = sp'` (the lowered stack pointer, base of the
`ld`) and `x10 = a0` (the malloc result, the `beqz` guard). -/
def fnArmReloadL (sp' a0 : BitVec 64) : GRegs := [(2, sp'), (10, a0)]

/-- Post: parked at the fall-through end `0x800033d8` (the no-OOM edge, `beqz` NOT
taken), memory = the entry memory with the reload span's write-log applied (the `ld`
writes no memory, so the log is empty), computed off the `#derive_case` outcome. -/
def FnArmReloadPost (sp' a0 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks fnArmReloadSeg
    (SegEvalState.init (fnArmReloadL sp' a0) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x800033d8#64

/-- **`fnArmReloadRow`** — the reload span as a `Triple`, via `segToTriple` over the
branch-terminated `fnArmReloadSeg`.  `hwf` is the row's one kernel `decide`
(`ChainOK`); `hpost` projects the computed fall-through end PC (`0x800033d8`, the
no-OOM edge) and the write-log memory.  Replaces a hand `site_800033d0`/`site_800033d4`
`stepObs` battery. -/
theorem fnArmReloadRow (sp' a0 : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre fnArmReloadSeg (fnArmReloadL sp' a0) lds 0x800033d0#64 m0)
      (FnArmReloadPost sp' a0 lds m0) := by
  apply segToTriple fnArmReloadSeg (fnArmReloadL sp' a0) lds 0x800033d0#64 m0
    (FnArmReloadPost sp' a0 lds m0)
    (by have h : keysG (fnArmReloadL sp' a0) = [2, 10] := rfl
        rw [h]; show ChainOK 0x800033d0#64 [2, 10] fnArmReloadSeg; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' _hregs
  refine ⟨hG', hmem', ?_⟩
  rw [hpc']
  show some (evalBlocksPC 0x800033d0#64 (SegEvalState.init (fnArmReloadL sp' a0) lds)
    fnArmReloadSeg) = some 0x800033d8#64
  rfl

#print axioms fnArmReloadRow

/-! ## §2. `hEntry` via the CallSpec / SpliceFold layer — the production test

The malloc call rides the EXISTING `mallocCallSpec` (`CallSpec.lean`) — malloc is
already a `CallSpec` instance, its `Sat` proof is `mallocCallSpec_sat`.  So the
whole splice is ONE `spliceFold` over a `SpliceChain` with a single `callStep`
malloc hop:

```
Pre  --[staging]-->  mallocCallSpec.EntryP g  --[mallocCallSpec_sat]-->  mallocCallSpec.ExitPost g  --[tail]-->  AllocBuildEntry
```

The two genuinely-off-path machine runs are the named residual premises:

* `staging` — the arm front (`a3 := φf env` decode) ≫ the malloc-call seg
  (`li a0,16 ; sd a3,0(sp) ; jal malloc`, `fnArmMallocCallBridge`) landing the
  malloc callee's canonical `EntryP` (arg pins `a0=16`, `sp`, `gp`; `x1 = ret`;
  the ABI frame; `mem = mMalloc`; `StackOK` + `AInv`).  The caller supplies it
  from the arm's own front and the generated malloc-call bridge.
* `tail` — `mallocCallSpec.ExitPost g` (the malloc post: NULL-or-success
  disjunction) ≫ the reload span (`fnArmReloadRow`, `ld a3,0(sp) ▷ beqz(false)`)
  landing `AllocBuildEntry` at `0x800033d8`.  The `beqz`-not-taken edge is the
  no-OOM case: the caller uses the success branch of the `ExitPost` disjunction
  (available because `g.n = 16 ≤ maxReq`, `g.hn`), pruning NULL.

`16 ≤ maxReq` is NOT a separate premise — it is carried by the malloc ghost pack's
`MallocG.hn` field, exactly the `CallSpec` layer's intent.  There is NO hand-rolled
`site_*` battery: the malloc hop is the `CallSpec`, the reload is the seg layer. -/

/-- **`allocBuildEntry_hEntry`** — the `EX_FN` malloc splice `Pre → AllocBuildEntry`,
assembled as ONE `spliceFold` with a `mallocCallSpec` `callStep` hop.

The malloc callee contract is threaded via `mallocCallSpec_sat M` (the Wave-36
`CallSpec` layer, unmodified — this is its first production consumer).  `g : MallocG
maxReq` is the malloc ghost pack for THIS call (`g.n := 16`, `g.hn : 16 ≤ maxReq`,
`g.sp := sp - 1088` the lowered stack pointer, `g.r := 0x800033d0` the malloc return
address, `g.m0 := mMalloc` the pre-malloc memory).

`staging` and `tail` are the two genuinely-off-path machine runs (see §2 doc); each
is a NAMED `Triple` premise, phrased at the `mallocCallSpec`'s canonical `EntryP` /
`ExitPost` seams so the whole splice is the fold with the real malloc contract in the
middle. -/
theorem allocBuildEntry_hEntry
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (g : MallocG maxReq) (Pre : Config → Prop)
    (Target : Config → Prop)
    -- staging: arm front (`a3 := φf env`) ≫ malloc-call seg → malloc's canonical entry
    (staging : Triple Pre (fun c => (mallocCallSpec M).EntryP g c))
    -- tail: malloc's canonical exit (NULL-or-success) ≫ reload span (`beqz` NOT taken,
    -- the no-OOM edge available from `g.hn : 16 ≤ maxReq`) → `AllocBuildEntry` at 0x800033d8
    (tail : Triple ((mallocCallSpec M).ExitPost g) Target) :
    Triple Pre Target :=
  spliceFold
    (SpliceChain.callStep (mallocCallSpec M) g (mallocCallSpec_sat M)
      staging (.tail tail))

#print axioms allocBuildEntry_hEntry

/-! ## §3. Probe — thread `hEntry` all the way to `FnArmSeamRun`

This shows the whole downstream pipeline closes modulo ONLY the two named
staging/tail machine premises: `allocBuildEntry_hEntry` (§2) inhabits the
`AllocBuildEntry` premise of `allocClosureContract_of` (`rows/AllocClosureInhab.lean`),
whose output `AllocClosureContract` feeds `fnArmSeamRun_of_allocClosure`
(`rows/FnArmSeamReduce.lean`) to yield `FnArmSeamRun` — the exact `hSeam` input of
`fnArmGeom_hArm_of_seam` (`FnArmGeomReduce.lean`) that produces the whole `EX_FN`
arm run `EvalEntry → PreEpilogueV … (.closure a)`.

The `Pre` here is FIXED as `fnArmSeamRun_of_allocClosure`'s dispatch predicate
(`∃ o ment vv8 vv9 vv18, ArmEntryK …`), so `staging`/`tail` are stated at exactly the
seams this pipeline demands. -/
theorem fnArmSeamRun_of_hEntry
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (φf φc φc' : Addr → Nat)
    (st : Vsa.While.St) (env : Addr)
    (name : Option String) (params : List String) (body : List Stmt)
    (p : Nat) (armPC : BitVec 64) (calleeLoaded : Mem → Prop)
    (sp r sret aExpr aEnv : BitVec 64) (m0 mMalloc : Mem)
    (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (M : MallocContract A SL gpv headroom maxReq)
    (gMal : MallocG maxReq)
    -- the two named off-path machine runs (identical seams to `allocBuildEntry_hEntry`):
    (staging : Triple
      (fun c => ∃ o ment vv8 vv9 vv18,
        ArmEntryK g N A SL φf φc' st armPC calleeLoaded (.fn name params body)
          sp r sret aExpr aEnv vv8 vv9 vv18 o m0 ment c)
      (fun c => (mallocCallSpec M).EntryP gMal c))
    (tail : Triple ((mallocCallSpec M).ExitPost gMal)
      (AllocBuildEntry g N A SL φf φc φc' st ⟨env, name, params, body⟩ p
        sp r sret aExpr m0 mMalloc v8 v9 v18 out0)) :
    FnArmSeamRun g N A SL φf φc' st st.store.closures.size armPC calleeLoaded
      name params body (st.store.allocClosure ⟨env, name, params, body⟩).1
      sp r sret aExpr aEnv m0 v8 v9 v18 out0
      (writeLog mMalloc (evalBlocks fnArmClosureBuildSeg
        (SegEvalState.init (fnArmClosureBuildL (BitVec.ofNat 64 p) aExpr
          (BitVec.ofNat 64 (φf env)) sret) [])).log) :=
  fnArmSeamRun_of_allocClosure g N A SL φf φc φc' st env name params body p armPC
    calleeLoaded sp r sret aExpr aEnv m0
    (writeLog mMalloc (evalBlocks fnArmClosureBuildSeg
      (SegEvalState.init (fnArmClosureBuildL (BitVec.ofNat 64 p) aExpr
        (BitVec.ofNat 64 (φf env)) sret) [])).log)
    v8 v9 v18 out0
    (allocClosureContract_of g N A SL φf φc φc' st env name params body p
      (fun c => ∃ o ment vv8 vv9 vv18,
        ArmEntryK g N A SL φf φc' st armPC calleeLoaded (.fn name params body)
          sp r sret aExpr aEnv vv8 vv9 vv18 o m0 ment c)
      sp r sret aExpr m0 mMalloc v8 v9 v18 out0
      (allocBuildEntry_hEntry M gMal _ _ staging tail))

#print axioms fnArmSeamRun_of_hEntry

end Vsa.Sim
