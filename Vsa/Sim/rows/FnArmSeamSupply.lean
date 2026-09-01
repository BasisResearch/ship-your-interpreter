import Vsa.Sim.rows.LayoutJumpTableGen
import Vsa.Sim.rows.FnResidSupply

/-!
# `FnArmSeamSupply` — the `.fn` arm-site supplier (leg-1 pins ⟶ `FnResidBundle`)

`rows/FnResidSupply.lean` reduced `FnResid` (the recursor's `hFn` slot) to ONE
named bundle `FnResidBundle`, whose `perGhost` field packages the per-ghost
residuals `fnResid_of_pipeline_wf` consumes — among them the **9 Layout-grounded
dispatch facts** (`hkle … htableStk`), of which `hslot : KindSlotPinned k armPC m0`
is the one that needs the concrete `.rodata` jump-table bytes.

This file is the **arm-site supplier**: it discharges the tag-`10` (`EX_FN`, arm PC
`0x800033c4`) slot pin from the GENERATED `LayoutJumpTableGen.groundSlot_10`
(leg-1) — so the caller supplies 4 concrete byte pins instead of an abstract
`KindSlotPinned` — and assembles `FnResidBundle` from:

* `FnDispatchLayout` — a named-field bundle of the tag-`10` dispatch/layout facts
  (`hkind`/`hcallee`/`hcalleeSurv`/`hexprSurv`/`htableStk`, and the slot bytes),
  the `EX_FN` clone of the leaf-arm dispatch shape (int/null/bool/str), with the
  slot pin now GROUNDED (`groundSlot_10`) rather than assumed;
* a per-ghost `FnArmSeamRun` provider — the `EX_FN` middle seam, closed upstream
  by `fnArmSeamRun_of_seams` (`rows/FnArmSeams`, modulo the two irreducible
  off-path bundles `AllocBuildStagingLink`/`AllocBuildTailFacts`) or
  `fnArmSeamRun_of_allocClosure` (`rows/FnArmSeamReduce`, modulo the
  `AllocClosureContract`);
* the closure-alloc `PhiExtends`/output invariant, the store-WF invariant
  `StoreClosuresBounded`, and the `EvalRecWiden` φc-widener.

The two SEAM bundles (`AllocBuildStagingLink`/`AllocBuildTailFacts`) are NOT
supplied here: per the wave-40 analysis they are the irreducible off-path machine
residuals (the arm-front `a3 := φf env` decode; the `AllocBuildEntry` ~30-field
marshalling transported across `malloc` via `CallSpec.memOut`), the exact analog of
strdup's `StrdupMemcpyContent` caller-content bundle — a NAMED premise, never a
theorem.  They enter here ONLY through the `FnArmSeamRun` provider (`hSeamPer`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc Vsa.Sim.Code

namespace Vsa.Sim

/-! ## §1. The tag-`10` slot pin, GROUNDED from the ELF bytes (leg-1) -/

/-- **`FnSlotBytes m`** — the four concrete `.rodata` bytes of the `EX_FN` (tag 10)
jump-table slot at `0x80019f80` (`6c 94 fe ff`, the little-endian offset the ELF
holds).  A named-field predicate (never an anonymous tower): the caller supplies
exactly these four byte pins from its Layout static image, and `fnSlot_grounded`
turns them into the abstract `KindSlotPinned 10 0x800033c4 m` the pipeline wants —
the sign-extended reassembly `0x80019f58 + (Int32)0xfffe946c = 0x800033c4` is
machine-checked inside `LayoutJumpTableGen.groundSlot_10`. -/
structure FnSlotBytes (m : Mem) : Prop where
  h0 : m[(jumpTableBase + 4 * 10 + 0 : Nat)]? = some (0x6c : BitVec 8)
  h1 : m[(jumpTableBase + 4 * 10 + 1 : Nat)]? = some (0x94 : BitVec 8)
  h2 : m[(jumpTableBase + 4 * 10 + 2 : Nat)]? = some (0xfe : BitVec 8)
  h3 : m[(jumpTableBase + 4 * 10 + 3 : Nat)]? = some (0xff : BitVec 8)

/-- **`fnSlot_grounded`** — the `EX_FN` slot pin from the concrete bytes, via the
GENERATED `groundSlot_10` (leg-1).  This is the tag-`10` analog of
`int_slot_kindPinned` (`EvalSimCommon`), except the four bytes are read straight out
of the ELF `.rodata` by `scripts/gen_layout.py` rather than carried by `EvalEntry`. -/
theorem fnSlot_grounded {m : Mem} (h : FnSlotBytes m) :
    KindSlotPinned 10 (0x800033c4#64) m :=
  LayoutJumpTableGen.groundSlot_10 h.h0 h.h1 h.h2 h.h3

#print axioms fnSlot_grounded

/-! ## §2. `FnDispatchLayout` — the tag-`10` dispatch/layout facts (arm site) -/

/-- **`FnDispatchLayout`** — the tag-`10` (`EX_FN`) dispatch/layout facts at the arm
site, the `EX_FN` clone of the leaf-arm dispatch shape (int/null/bool/str), stated
for FIXED ghosts.  The slot pin is GROUNDED (`FnSlotBytes` ⟶ `groundSlot_10`), so
the only Layout residuals left are the standard ones every leaf/arm row threads:
the kind read (`hkind`, `= 10`), the callee-code survival (`hcallee`/`hcalleeSurv`),
the Expr-node survival (`hexprSurv`), and the table/stack disjointness (`htableStk`).
Named-field structure per CLAUDE.md (never a tower); `armPC = 0x800033c4` and
`k = 10` are FIXED (the fn tag), so `hkle`/`hklt`/`harmAl` are `by decide`. -/
structure FnDispatchLayout
    (N : NativeAddrs) (SL : StackLayout)
    (name : Option String) (params : List String) (body : List Stmt)
    (sp aExpr : BitVec 64) (m0 : Mem) : Prop where
  /-- the fn-slot `.rodata` bytes (⟶ `KindSlotPinned 10 0x800033c4 m0`). -/
  hbytes : FnSlotBytes m0
  /-- the dispatched kind read = `10` (from `ExprRepr … (.fn …)`). -/
  hkind : read32 m0 aExpr.toNat = some 10
  /-- the Expr node survives spill writes below `sp`. -/
  hexprSurv : ∀ m' : Mem,
    (∀ aa : Nat, ¬ (SL.lo ≤ aa ∧ aa < sp.toNat) → m0[aa]? = m'[aa]?) →
      ExprRepr m' aExpr.toNat (.fn name params body)
  /-- the jump table is disjoint from the stack window. -/
  htableStk : jumpTableBase + 4 * 10 + 4 ≤ SL.lo ∨ sp.toNat ≤ jumpTableBase + 4 * 10

/-! ## §3. `fnResidBundle_of_parts` — assemble `FnResidBundle` at the arm site

The per-ghost residual set `FnResidBundle.perGhost` mixes ghost-dependent machine
facts (the seam, the widened map φc', the register/geometry ghosts) with the
tag-`10` dispatch/layout facts.  We package the machine half as a single per-ghost
provider `hSeamPer` (the caller runs `fnArmSeamRun_of_seams`/`_of_allocClosure`),
and the layout half comes from `FnDispatchLayout` with its slot pin grounded from
`FnSlotBytes`.  `calleeLoaded` is threaded as a caller-chosen predicate (the real
`eval_expr` code-image predicate); `FnDispatchLayout.hcallee` is a trivial marker,
the genuine `calleeLoaded m0`/survival come from `hSeamPer`. -/

/-- **`fnResidBundle_of_parts`** — assemble `FnResidBundle` for the `.fn` arm from
the closure-alloc facts, the store-WF invariant, and a per-ghost provider of the
`EX_FN` seam + widener + the tag-`10` dispatch layout (slot pin grounded from
`FnSlotBytes` via `groundSlot_10`).  This is the arm-site supplier: every field of
`perGhost` is supplied, with the ONE Layout byte-fact (`hslot`) now discharged from
concrete ELF bytes rather than assumed.  What remains inside `hSeamPer` is exactly
the irreducible `EX_FN` machine (the two seam bundles + `EvalRecWiden`), the same
class every arm carries to the M6 Layout. -/
theorem fnResidBundle_of_parts
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (name : Option String) (params : List String) (body : List Stmt)
    (store' : Store) (a : Addr)
    (hAlloc : st.store.allocClosure ⟨env, name, params, body⟩ = (store', a))
    (hWF : StoreClosuresBounded st.store)
    -- the per-ghost machine + layout provider: for every ghost choice, the
    -- widened closures map, the register/geometry ghosts, a callee-code
    -- predicate, the closure-alloc PhiExtends + output invariant, the tag-10
    -- dispatch layout (slot bytes + kind/survival/disjointness), the EX_FN seam,
    -- and the EvalRecWiden widener.  The seam (`FnArmSeamRun`) is the irreducible
    -- machine residual (the two seam bundles enter through it).
    (hSeamPer : ∀ (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
      ∃ (φc' : Addr → Nat) (v8 v9 v18 : BitVec 64) (out0 : Array String) (mpre : Mem)
        (calleeLoaded : Mem → Prop),
        PhiExtends φc φc' st.store.closures.size ∧
        String.join out0.toList = st.out ∧
        FnDispatchLayout N SL name params body sp aExpr m0 ∧
        calleeLoaded m0 ∧
        (∀ (mem : Mem) (a8 : Nat) (dd : BitVec (8 * 8)),
          SL.lo ≤ a8 → a8 + 8 ≤ sp.toNat → calleeLoaded mem → calleeLoaded (writeMap8 mem a8 dd)) ∧
        FnArmSeamRun g N A SL φf φc' st a (0x800033c4#64) calleeLoaded name params body store'
          sp r sret aExpr aEnv m0 v8 v9 v18 out0 mpre ∧
        EvalRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size
          ⟨store', st.out⟩ (.closure a) sp r sret m0) :
    FnResidBundle st d env name params body store' a where
  hAlloc := hAlloc
  hWF := hWF
  perGhost := by
    intro g N A SL φf φc sp r sret aEnv aExpr m0
    obtain ⟨φc', v8, v9, v18, out0, mpre, calleeLoaded,
      hpc, hout, hLay, hcallee, hcalleeSurv, hSeam, hW⟩ :=
      hSeamPer g N A SL φf φc sp r sret aEnv aExpr m0
    refine ⟨φc', v8, v9, v18, out0, mpre, 10, (0x800033c4#64), calleeLoaded,
      hpc, hout, ?_, ?_, hLay.hkind, ?_, hcallee, hcalleeSurv, hLay.hexprSurv,
      ?_, hLay.htableStk, hSeam, hW⟩
    · decide            -- 10 ≤ 10
    · decide            -- 10 < 128
    · exact fnSlot_grounded hLay.hbytes   -- KindSlotPinned 10 0x800033c4 m0
    · decide            -- (0x800033c4).toNat % 4 = 0

#print axioms fnResidBundle_of_parts

/-! ## §4. `fnResid_of_parts` — `FnResid` directly from the arm-site parts

Compose `fnResidBundle_of_parts` with `fnResid_from_bundle` (`FnResidSupply`): the
recursor's `hFn` slot residual `FnResid`, supplied premise-free MODULO the arm-site
parts (closure-alloc + store-WF + the per-ghost seam/widener/layout provider). -/

/-- **`fnResid_of_parts`** — the whole `hFn` residual `FnResid` from the arm-site
parts, the tag-`10` slot pin grounded from the ELF bytes. -/
theorem fnResid_of_parts
    (st : Vsa.While.St) (d : Nat) (env : Addr)
    (name : Option String) (params : List String) (body : List Stmt)
    (store' : Store) (a : Addr)
    (hAlloc : st.store.allocClosure ⟨env, name, params, body⟩ = (store', a))
    (hWF : StoreClosuresBounded st.store)
    (hSeamPer : ∀ (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
      ∃ (φc' : Addr → Nat) (v8 v9 v18 : BitVec 64) (out0 : Array String) (mpre : Mem)
        (calleeLoaded : Mem → Prop),
        PhiExtends φc φc' st.store.closures.size ∧
        String.join out0.toList = st.out ∧
        FnDispatchLayout N SL name params body sp aExpr m0 ∧
        calleeLoaded m0 ∧
        (∀ (mem : Mem) (a8 : Nat) (dd : BitVec (8 * 8)),
          SL.lo ≤ a8 → a8 + 8 ≤ sp.toNat → calleeLoaded mem → calleeLoaded (writeMap8 mem a8 dd)) ∧
        FnArmSeamRun g N A SL φf φc' st a (0x800033c4#64) calleeLoaded name params body store'
          sp r sret aExpr aEnv m0 v8 v9 v18 out0 mpre ∧
        EvalRecWiden g N A SL φf φc st.store.frames.size st.store.closures.size
          ⟨store', st.out⟩ (.closure a) sp r sret m0) :
    FnResid st d env name params body store' a :=
  fnResid_from_bundle st d env name params body store' a
    (fnResidBundle_of_parts st d env name params body store' a hAlloc hWF hSeamPer)

#print axioms fnResid_of_parts

end Vsa.Sim
