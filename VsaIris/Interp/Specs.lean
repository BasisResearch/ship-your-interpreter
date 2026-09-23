import VsaIris.Vsa.Instance
import VsaIris.MallocRun
import VsaIris.Loop
import VsaIris.Interp.Need
import VsaIris.Interp.Vacuity
import VsaIris.Vsa.AllocHoles
import VsaIris.Interp.SpecEnv
import VsaIris.Vsa.HeapShape
import Vsa.RuntimeRepr
import Vsa.While.Cost
import Vsa.While.StackNeed
import Vsa.Refinement
import Vsa.Sim.LayoutInstance

/-!
# DESIGN SKELETON: interpreter-level specs (see `VsaIris/INTERP_DESIGN.md`)

**NOT IMPORTED, NOT BUILT, NOT A PROOF.** This file fixes the statements the
work packages of INTERP_DESIGN.md §9 must prove. Every `sorry` below is a
deliverable. Definitions are meant to be final modulo elaboration fixes: a
work package that must change a statement records why in INTERP_DESIGN.md §10.
It has never been elaborated (no build was run when it was written).

Section map (INTERP_DESIGN.md section in brackets):
* §A modes and the mode-generic WP interface [§1, F1]
* §B mode-generic function specs, abort continuations [§1, F3]
* §C representation predicates [§3, R]
* §D the three recursive specs, total and partial [§4]
* §E loop and block lemma shapes [§4.3, G]
* §F assembly: boundary, term_sim, stuck_sim, final theorem [§5, A]
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

/-! ## §A Modes and the mode-generic WP interface (F1) — LANDED

Built in `VsaIris/MachWP.lean` (no longer a placeholder here):
* `MachWP M` — fields `W`, `lat` (the step modality: `id` total, `▷` partial),
  `lat_intro`, `lagRun` (the lag kernel `Lag.lag_run` at the WP level), `halt`,
  `fupd`. Derived for every `Wp`: `Wp.run` (= `wp_run`), `Wp.runL` (continuation
  under `Wp.lat`; at `wpW` this is `run_later`), `Wp.local_step`, `Wp.local_stepL`.
* `twpW M` (`W := mTWP M`) and `wpW M` (`W := mWP M`, `PartialWP.lean`).
* `twp_wp : mTWP M Φ ⊢ mWP M Φ` (`PartialWP.lean`).
* Mode-generic rules: `wp_retW`, `wp_jalW`, `wp_callW`, `fnSpecW` (`Call.lean`),
  `wp_localRunW` (`LocalRun.lean`), `Inst.wp_segW` (`Vsa/Instance.lean`);
  the Löb call `wp_call_later` (`Call.lean`).
* Partial adequacy: `mach_adequacyP` (`Adequacy.lean`), `Inst.vsa_adequacyP`
  and `Inst.vsa_adequacyP_nonzero` (exactly `stuck_sim`'s conclusion).
* The console (F2): `MachWP.runOut` (printing run, the `putc` rule) and
  `MachWP.haltConsole` (halt/console agreement), derived for every `Wp`
  (`MachWP.lean`); VSA instances `Inst.wp_putcW`/`Inst.wp_exitW` at the
  newlib `tohost` stores (`Vsa/Console.lean`). -/

/-! ## §B Mode-generic function specs (F3) — LANDED

Built in `VsaIris/CallAbort.lean`, `VsaIris/Stack.lean`, `VsaIris/Loop.lean`
and `VsaIris/Interp/Need.lean` (no longer placeholders here):

* `fnSpecAbort Wp entry P Q A` — a function that returns OR aborts. The two
  continuations are an ADDITIVE pair (xv6iris `durable-notes.md`, "Contracts
  and resources"), so the caller's frame and its own inherited abort
  continuation serve both branches. Persistent, like `fnSpecW`.
* `wp_callAbort Wp hexec` — the `jal` rule for it; `wp_callAbort_later` is the
  Löb twin (the recursive `jal` of `specsP` below).
* `fnSpecAbort_of_fnSpecW` — a helper that always returns (H1-H4's `fnSpecW`
  specs) meets an abort spec with ANY abort resource; `fnSpecAbort_mono` is
  the consequence rule and `fnSpecAbort_rebase` carries the abort-resource
  difference as an extra precondition.
* `blockOwn_split`/`blockOwn_join`/`blockOwn_cast`,
  `stackScratch_narrow`/`_widen`, the prologue/epilogue pair
  `stackScratch_frame`/`stackScratch_unframe` (`addi sp,sp,-f`), and the
  carve/join pair `stackScratch_carve`/`stackScratch_join`: a callee's scratch
  is carved out of the caller's owned stack region and returned. The side
  condition `nc + f ≤ n` is `Vsa.Alloc.StackOK.child`'s.
* `abortAt Core s need` with `abortAt_elim`/`abortAt_intro`, and
  `abort_rebase` (used by `abortRes` in §D).
* `wp_callArmW` and `wp_callArmAbort` — **the call step an arm takes**, once:
  lend the callee a narrower part of the owned stack, keep the slack, and (in
  partial mode) re-base BOTH continuations to the callee's region. E1-E6 call
  these instead of re-deriving the carve per site.
* `stackBudget`, `evalNeed`, `execNeed`, the arithmetic lemmas
  `stackBudget_child` (the Iris route's `StackOK.child`) and
  `stackBudget_call`, one inequality per recursor arm
  (`evalNeed_binary_left`, `execNeed_block`, `execNeed_callBody`, ...), and
  S1's boundary bridge `execNeed_of_stackFits` / `stackScratch_boundary` over
  `ProgramStackFits`.
* `MachWP.loop` / `MachWP.loopI` / `MachWP.loopSeg` — the bounded-loop rule by
  fuel induction, for either WP (§E). -/

/-! ## §C Representation predicates (R) — LANDED

Built in `VsaIris/Interp/{Repr,Store,Bridge,Boundary,Vacuity}.lean` (no longer
a placeholder here; this file imports them):

* `VsaIris/Interp/Repr.lean` — `InterpGS` (two ghost-map names over the
  machine's `Nat ↦ Nat` functor, so no second `GhostMapG` instance is in
  scope), `frameAt`/`closAt`, the byte layers `roImg`/`roOn`/`ownImg`, the
  persistent `strAt`, `astE`/`astS`/`astSs`, `valOf`/`valImg`/`valAt`/
  `slot24`, `closOwn`, `FrameGeom`/`FrameLayout`/`bindings`/`parentAt`/
  `frameBody`/`frameOwn`/`framesOwn`/`closuresOwn`, `StoreMaps`/`storeRepr`,
  `interpCore`/`interpCtx`/`interpCtxPre`, `Regime`/`heapRes`, `world`.
* `VsaIris/Interp/Store.lean` — the ONE frame opener `storeRepr_open` (+ the
  `env_define` closer `storeRepr_open_define`), `storeRepr_frameAt`/
  `_closAt`/`_closure`, `storeRepr_empty`/`_allocFrame`/`_allocClosure`, the
  discard `ownImg_persist`/`strAt_of_owned`, and the two-owner sanity lemmas
  `storeRepr_blocks_disjoint`, `storeRepr_blocks_off_heap`,
  `world_blocks_off_heap`.
* `VsaIris/Interp/Bridge.lean` — VSA's pure relations to these predicates:
  `astE_of_exprRepr`/`astS_of_stmtRepr`/`astSs_of_stmtArrayRepr`/
  `astSs_of_programRepr` (what `InterpRunReadyFacts.ast_owned` gives A0),
  `strAt_of_cstringWithin`, `valOf_of_valueRepr`/`valAt_of_valueWordRepr`,
  `FrameReads`/`FrameBridge`/`frameBody_of_frameRepr`, and the `memImg`
  read calculus (`readLE_memImg`, `imgW_lo32`, `imgW_read64`).
* `VsaIris/Interp/Boundary.lean` — `ownImg_of_memMap`/`roOn_of_memMap`: the
  `[∗map] k ↦ v ∈ mm, k ↦ₘ v` adequacy hands the client becomes the exclusive
  and read-only byte resources, over `extAddrs`/`blockAddrs` address lists.
* `VsaIris/Interp/Vacuity.lean` — the vacuity check: every predicate above
  instantiated at the control program's real initial memory
  (`ctl_predicates_inhabited`).

STATEMENT CHANGES against the skeleton (recorded in INTERP_DESIGN.md §10):
`astE`/`astS`/`astSs` are `*ReprWithin` over a read-only view `roOn P m`
rather than an enumerated byte list; `valAt`/`frameOwn`/`storeRepr` own a
byte IMAGE (`ownImg`) with pure layout facts rather than per-word `word64`
chains, which is the form `LocalRun`/`wp_seg` consume; `frameOwn` carries a
named `FrameGeom`/`FrameLayout` instead of an existential tower; `interpCtx`
splits into `interpCore` plus the `jmp_buf` (read-only after `setjmp`,
exclusive before: `interpCtxPre`). -/

/-! ## §D The three recursive specs -/

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable (M : MachineModel) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)

-- `evalNeed` / `execNeed` are landed in `VsaIris/Interp/Need.lean` (F3).

def evalEntryPC : BitVec 64 := 0x80003164#64
def execEntryPC : BitVec 64 := 0x80003fe0#64
def interpRunPC : BitVec 64 := 0x800043ec#64

/-- `eval_expr`'s caller-visible entry resources (ABI from `EvalEntry`:
`a0 = sret`, `a1 = env`, `a2 = e`). `saved` are the callee-saved registers the
body spills and restores; `clobE` the caller-saved ones it may clobber. -/
def evalPre (ρ : Regime) (st : St) (d env : Nat) (e : Expr) (sret aE aX s : BitVec 64)
    (saved : List (Nat × BitVec 64)) (clobE : List Nat) : IProp GF :=
  iprop((10 : Nat) ↦ᵣ sret ∗ (11 : Nat) ↦ᵣ aE ∗ (12 : Nat) ↦ᵣ aX ∗ □ astE aX.toNat e ∗
    □ frameAt env aE.toNat ∗ sp ↦ᵣ s ∗ stackScratch s (evalNeed e d) ∗ savedOwn saved ∗
    clobbered clobE ∗ slot24 sret.toNat ∗ ⌜e.bodiesBound perCallBudget = true⌝ ∗
    world N L Room inp ρ st d)

def evalPost (ρ : Regime) (st' : St) (d : Nat) (e : Expr) (v : Value) (sret s : BitVec 64)
    (saved : List (Nat × BitVec 64)) (clobE : List Nat) : IProp GF :=
  iprop(sp ↦ᵣ s ∗ stackScratch s (evalNeed e d) ∗ savedOwn saved ∗ clobbered clobE ∗
    (∃ w, (10 : Nat) ↦ᵣ w) ∗ (∃ w, (11 : Nat) ↦ᵣ w) ∗ (∃ w, (12 : Nat) ↦ᵣ w) ∗
    valAt N sret.toNat v ∗ world N L Room inp ρ st' d)

/-- `exec_stmt`'s entry (ABI from `ExecEntry`: `a0 = in`, `a1 = s`, `a2 = env`,
`a3 = ret`). -/
def execPre (ρ : Regime) (st : St) (d env : Nat) (sm : Stmt) (aS aE aRet s : BitVec 64)
    (saved : List (Nat × BitVec 64)) (clobS : List Nat) : IProp GF :=
  iprop((10 : Nat) ↦ᵣ BitVec.ofNat 64 inp ∗ (11 : Nat) ↦ᵣ aS ∗ (12 : Nat) ↦ᵣ aE ∗
    (13 : Nat) ↦ᵣ aRet ∗ □ astS aS.toNat sm ∗ □ frameAt env aE.toNat ∗ sp ↦ᵣ s ∗
    stackScratch s (execNeed sm d) ∗ savedOwn saved ∗ clobbered clobS ∗ slot24 aRet.toNat ∗
    ⌜sm.bodiesBound perCallBudget = true⌝ ∗ world N L Room inp ρ st d)

/-- The `ret` slot holds `v` exactly when the status is `.ret v`. -/
def statusRet (aRet : Nat) : Status → IProp GF
  | .ret v => valAt N aRet v
  | _ => slot24 aRet

def statusCode : Status → Nat
  | .normal => 0 | .ret _ => 1 | .brk => 2 | .cont => 3
  -- R: pin to the binary's `ExecStatus` enum (`Vsa.Sim.StatusCode`).

def execPost (ρ : Regime) (st' : St) (d : Nat) (sm : Stmt) (status : Status) (aRet s : BitVec 64)
    (saved : List (Nat × BitVec 64)) (clobS : List Nat) : IProp GF :=
  iprop(sp ↦ᵣ s ∗ stackScratch s (execNeed sm d) ∗ savedOwn saved ∗ clobbered clobS ∗
    (10 : Nat) ↦ᵣ BitVec.ofNat 64 (statusCode status) ∗ (∃ w, (11 : Nat) ↦ᵣ w) ∗
    (∃ w, (12 : Nat) ↦ᵣ w) ∗ (∃ w, (13 : Nat) ↦ᵣ w) ∗
    statusRet N aRet.toNat status ∗ world N L Room inp ρ st' d)

/-! ### Total, derivation-indexed (term_sim) -/

/-- **`eval_expr`, total.** The continuation gets exactly `D`'s outcome and the
credits drop by `D`'s cost. No error arm: each machine test resolves against
`D`'s pure premises. The recursor motive for `EvalECost` is this `_body`. -/
def evalSpecT_body (st : St) (d env : Nat) (e : Expr) (st' : St) (v : Value) (n : Nat)
    (_D : EvalECost st d env e st' v n) : IProp GF :=
  iprop(∀ (k : Nat) (sret aE aX s : BitVec 64) (saved : List (Nat × BitVec 64)) (clobE : List Nat),
    fnSpecW (twpW M) evalEntryPC
      (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗
        evalPre N L Room inp (.counted (k + n)) st d env e sret aE aX s saved clobE))
      (fun _ => evalPost N L Room inp (.counted k) st' d e v sret s saved clobE))

def execSpecT_body (st : St) (d env : Nat) (sm : Stmt) (st' : St) (status : Status) (n : Nat)
    (_D : ExecSCost st d env sm st' status n) : IProp GF :=
  iprop(∀ (k : Nat) (aS aE aRet s : BitVec 64) (saved : List (Nat × BitVec 64)) (clobS : List Nat),
    fnSpecW (twpW M) execEntryPC
      (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗
        execPre N L Room inp (.counted (k + n)) st d env sm aS aE aRet s saved clobS))
      (fun _ => execPost N L Room inp (.counted k) st' d sm status aRet s saved clobS))

/-- The total theorem the recursor delivers (A): every cost derivation meets
its spec. The 49 recursor rows become the generated `Case/*T` lemmas. -/
theorem evalSpecT (st : St) (d env : Nat) (e : Expr) (st' : St) (v : Value) (n : Nat)
    (D : EvalECost st d env e st' v n) :
    ⊢ evalSpecT_body (GF := GF) M N L Room inp st d env e st' v n D := by sorry

theorem execSpecT (st : St) (d env : Nat) (sm : Stmt) (st' : St) (status : Status) (n : Nat)
    (D : ExecSCost st d env sm st' status n) :
    ⊢ execSpecT_body (GF := GF) M N L Room inp st d env sm st' status n D := by sorry

/-! ### Partial, outcome-quantified, with abort (stuck_sim) -/

/-- What an abort hands the top: the landing registers (H5 pins them from the
`jmp_buf`, or the `exit(1)` entry for OOM), SOME world, and the whole owned
stack below `s`. Callers re-base it at each call (`abort_rebase`). -/
def abortCore : IProp GF :=
  iprop(∃ (landing : Bool) (ρ : Regime) (st : St) (d : Nat),
    world N L Room inp ρ st d ∗
    (if landing then PC ↦ᵣ 0#64 -- H5: the `setjmp` return site in `interp_run`, a0 = 1
     else PC ↦ᵣ 0x80004764#64 ∗ (10 : Nat) ↦ᵣ 1#64)) -- `exit`, a0 = 1

/-- The abort resource at a site: `abortCore` and the whole owned stack below
`s` (F3's landed `VsaIris.abortAt`). The `stackScratch` is OUTSIDE the
existential — nothing under it mentions `s` or `need` — which is what lets
`abort_rebase` move it. -/
def abortRes (s : BitVec 64) (need : Nat) : IProp GF :=
  abortAt (abortCore N L Room inp) s need

/-- **`eval_expr`, partial.** The return branch gets SOME outcome with its
derivation; error arms take the abort branch. Proved by Löb (A). -/
def evalSpecP_body (st : St) (d env : Nat) (e : Expr) : IProp GF :=
  iprop(∀ (sret aE aX s : BitVec 64) (saved : List (Nat × BitVec 64)) (clobE : List Nat),
    fnSpecAbort (wpW M) evalEntryPC
      (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗
        evalPre N L Room inp .uncounted st d env e sret aE aX s saved clobE))
      (fun _ => iprop(∃ st' v, ⌜EvalE st d env e st' v⌝ ∗
        evalPost N L Room inp .uncounted st' d e v sret s saved clobE))
      (abortRes N L Room inp s (evalNeed e d)))

def execSpecP_body (st : St) (d env : Nat) (sm : Stmt) : IProp GF :=
  iprop(∀ (aS aE aRet s : BitVec 64) (saved : List (Nat × BitVec 64)) (clobS : List Nat),
    fnSpecAbort (wpW M) execEntryPC
      (fun r => iprop(⌜r.toNat % 4 = 0⌝ ∗
        execPre N L Room inp .uncounted st d env sm aS aE aRet s saved clobS))
      (fun _ => iprop(∃ st' status, ⌜ExecS st d env sm st' status⌝ ∗
        execPost N L Room inp .uncounted st' d sm status aRet s saved clobS))
      (abortRes N L Room inp s (execNeed sm d)))

/-- The Löb conclusion (A): both partial specs, for every input. -/
theorem specsP :
    ⊢ □ ((∀ st d env e, evalSpecP_body (GF := GF) M N L Room inp st d env e) ∧
         (∀ st d env sm, execSpecP_body (GF := GF) M N L Room inp st d env sm)) := by sorry

/-- F3 (landed as `VsaIris.abort_rebase`): re-basing an abort continuation
from the caller's region to the child's, joining the caller's frame bytes
`[s_c, s_p)` and the slack `[s_p - n_p, s_c - n_c)` back in.

STATEMENT CHANGE (F3): the skeleton's two side conditions were not enough —
the two regions must also lie below their stack pointers (`hnp`, `hnc`),
otherwise `stackScratch` truncates at 0 and the intervals do not join. -/
theorem abort_rebase {Wp : MachWP (GF := GF) M} {Φ : Nat × String → IProp GF}
    (sp_ sc : BitVec 64) (np nc : Nat) (hnp : np ≤ sp_.toNat) (hnc : nc ≤ sc.toNat)
    (hsc : sc.toNat ≤ sp_.toNat) (hle : sp_.toNat - np ≤ sc.toNat - nc) :
    (abortRes N L Room inp sp_ np -∗ Wp.W Φ) ∗
      blockOwn (sc.toNat) (sp_.toNat - sc.toNat) ∗
      blockOwn (sp_.toNat - np) ((sc.toNat - nc) - (sp_.toNat - np))
    ⊢ (abortRes N L Room inp sc nc -∗ Wp.W Φ) :=
  VsaIris.abort_rebase _ sp_ sc np nc hnp hnc hsc hle

end Specs

/-! ## §E Loop and block lemma shapes (G, E)

One lemma per code shape, parameterised by its PCs as literals (xv6iris
durable-notes "Seams and block lemmas"). -/

/-- A statement-sequence loop site: the block arm, the closure body inside the
call arm, and `interp_run`'s loop are three instances. G reads the PCs off the
disassembly (`closure_body_sites.tsv`, `exec_stmt_block_sites.tsv`,
`arm_interp_back_edge.toml`). -/
structure SeqSite where
  head : Nat        -- loop-head PC
  callSite : Nat    -- `jal exec_stmt`
  normalExit : Nat
  abruptExit : Nat
  -- register/slot holding the index, the count, the array base
  idxReg : Nat
  cntReg : Nat
  arrReg : Nat

/-- `seqLoop`, total: induction on the `ExecSeqCost` derivation; each statement
through `execSpecT`. Partial twin: fuel induction on the remaining count, each
statement through the Löb hypothesis. Both are instances of F3's landed
`MachWP.loop` (`VsaIris/Loop.lean`), whose two body continuations are an
additive pair, so the inherited abort continuation survives every iteration
(INTERP_DESIGN.md §10.1); `MachWP.loopSeg` is the shape whose body is one
reflected `RunFact` segment (H3's `strlen`/`memcpy`/`strcmp`). Statement is
G's to fix against the real seam registers; recorded here as the obligation. -/
theorem seqLoop_obligation (_site : SeqSite) : True := trivial

/-! ## §F Assembly -/

/-- The named holes the final theorem keeps (INTERP_DESIGN.md §9). Every
field must come with a satisfiability witness (xv6iris durable-notes
"Vacuity"): the allocator runs at the control image (`ControlEnd`), the
newlib specs at a concrete call. -/
structure IrisHoles : Prop where
  /-- The allocator's first-order runs at the binary, both regimes
  (`VsaIris/Vsa/AllocHoles.lean`); `VsaHeap.allocSpecs` turns them into the
  Iris specs. H4 discharges them field by field. -/
  alloc : VsaHeap.AllocHoles
  /-- `realloc(NULL, n)` at the binary, both regimes (`VsaIris/Interp/SpecEnv.lean`):
  `env_define`'s first array growth. H4 discharges it. -/
  reallocNull : ReallocNullHoles
  /-- Safety of `snprintf` (`%s`/`%d` messages in `runtime_error`) and
  `fprintf` (error and OOM paths). Partial mode only. -/
  newlib : True
  -- DESIGN: replace each `True` with the exact run/spec structure once H4/H5
  -- fix their statements.

/-- The boundary (A0): from `InterpRunReady` and `ProgramRepr`, allocate the
ghost state and produce the initial world, the persistent AST and code, the
top stack region, in either regime. -/
theorem world_of_boundary_obligation : True := trivial

/-- Q1 (approved, landed by S1): the stack admissibility a loaded program
satisfies is `Vsa.Sim.LayoutInstance.StackAdmissible`, a field of
`InterpRunReadyFacts` beside the allocator's `capacity`. So the Iris route's
layout is the concrete one (INTERP_DESIGN.md "STATEMENT CHANGE"). -/
abbrev interpRunLayout' : Vsa.Refine.Layout := Vsa.Sim.LayoutInstance.interpRunLayout

theorem term_sim_iris (_h : IrisHoles) :
    ∀ p c out, Vsa.Refine.Loaded interpRunLayout' p c → BigStep p out →
      Vsa.Machine.Halts c out 0 := by sorry

theorem stuck_sim_iris (_h : IrisHoles) :
    ∀ p c, Vsa.Refine.Loaded interpRunLayout' p c → (¬ ∃ out, BigStep p out) →
      Vsa.Machine.Diverges c ∨ ∃ out e, Vsa.Machine.Halts c out e ∧ e ≠ 0 := by sorry

theorem interpSim_iris (h : IrisHoles) : Vsa.Refine.InterpSim interpRunLayout' :=
  ⟨term_sim_iris h, stuck_sim_iris h⟩

/-- **The end-to-end theorem on the Iris route.** `Refinement.lean` unchanged. -/
theorem endToEnd_refinement_iris (h : IrisHoles) :
    ∀ p c, Vsa.Refine.Loaded interpRunLayout' p c →
      (∀ out, BigStep p out ↔ Vsa.Machine.Halts c out 0) ∧
      (Vsa.Machine.Diverges c → ¬ ∃ out, BigStep p out) :=
  Vsa.Refine.refinement (interpSim_iris h)

end VsaIris.Interp
