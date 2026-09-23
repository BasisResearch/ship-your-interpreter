import VsaIris.Vsa.Instance
import VsaIris.MallocRun
import VsaIris.Vsa.AllocHoles
import VsaIris.Vsa.HeapShape
import Vsa.RuntimeRepr
import Vsa.While.Cost
import Vsa.While.StackNeed
import Vsa.Refinement

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

/-! ## §A Modes and the mode-generic WP interface (F1)

Every block lemma is proved once against `MachWP`; `twpW` (total) and `wpW`
(partial) instantiate it. Helper loops are fuel induction (xv6iris
`ProofMemset.v:1-9`, `ProofMemmove.v:350` `mm_loop`), valid for both. -/

section Modes

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The WP interface blocks are proved against. `run` is `VsaIris.wp_run`'s
statement with the WP abstracted. -/
structure MachWP (M : MachineModel) where
  W : (Nat × String → IProp GF) → IProp GF
  run : ∀ {Φ : Nat × String → IProp GF} (n : Nat)
    (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8))
    (RW : List (Nat × BitVec 64 × BitVec 64)) (MW : List (Nat × BitVec 8 × BitVec 8)),
    RunFact M n RR MR RW MW →
      footPre (GF := GF) RR MR RW MW ∗ (footPost RR MR RW MW -∗ W Φ) ⊢ W Φ
  -- F1/F2 add: `halt` (VsaIris.wp_exec_halt, abstracted) and `putc` (console step).

/-- The total instance: exists today (`mTWP`, `wp_run`). -/
def twpW (M : MachineModel) : MachWP (GF := GF) M where
  W := mTWP M
  run := fun n RR MR RW MW h => wp_run (M := M) n RR MR RW MW h

/-- The partial WP (F1): `cpuTok -∗ WP Loop @ NotStuck; ⊤ {{ Φ }}` over the
same lagging state interpretation. DESIGN: F1 defines it; here it is a
placeholder so the statements below parse. -/
opaque mWP (M : MachineModel) (Φ : Nat × String → IProp GF) : IProp GF

/-- The partial instance (F1 proves `run`, plus `run_later` for Löb). -/
def wpW (M : MachineModel) : MachWP (GF := GF) M where
  W := mWP M
  run := by intros; sorry

/-- F1: the total WP implies the partial one (iris-lean `TotalWeakestPre`). -/
theorem twp_wp (M : MachineModel) (Φ : Nat × String → IProp GF) :
    mTWP M Φ ⊢ mWP M Φ := by sorry

end Modes

/-! ## §B Mode-generic function specs (F3) -/

section Fn

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

/-- `fnSpec` (Call.lean) with the WP a parameter; `fnSpecW (twpW M)` is `fnSpec`. -/
def fnSpecW (Wp : MachWP (GF := GF) M) (entry : BitVec 64) (P Q : BitVec 64 → IProp GF) :
    IProp GF :=
  iprop(□ ∀ (r : BitVec 64) (Φ : Nat × String → IProp GF),
    PC ↦ᵣ entry -∗ ra ↦ᵣ r -∗ P r -∗
      (PC ↦ᵣ r -∗ ra ↦ᵣ r -∗ Q r -∗ Wp.W Φ) -∗ Wp.W Φ)

/-- A function that returns OR aborts (runtime error / OOM exit). The two
continuations are an ADDITIVE pair (xv6iris durable-notes "Contracts and
resources"): both are proved from the caller's one context, so the caller's
frame and its own abort continuation serve both branches. -/
def fnSpecAbort (Wp : MachWP (GF := GF) M) (entry : BitVec 64)
    (P Q : BitVec 64 → IProp GF) (A : IProp GF) : IProp GF :=
  iprop(□ ∀ (r : BitVec 64) (Φ : Nat × String → IProp GF),
    PC ↦ᵣ entry -∗ ra ↦ᵣ r -∗ P r -∗
      ((PC ↦ᵣ r -∗ ra ↦ᵣ r -∗ Q r -∗ Wp.W Φ) ∧ (A -∗ Wp.W Φ)) -∗ Wp.W Φ)

/-- `wp_call` for `fnSpecW` (F3): the jal, the callee's spec, the continuation
at `i + 4`; everything else the caller owns is framed by the wand. -/
theorem wp_callW {Wp : MachWP (GF := GF) M} {Φ : Nat × String → IProp GF} {i : Nat}
    {code : List (BitVec 8)} {entry v : BitVec 64} {P Q : BitVec 64 → IProp GF}
    (hexec : JalExec M i code entry) :
    instrAt (GF := GF) i code ∗ fnSpecW Wp entry P Q ∗ PC ↦ᵣ BitVec.ofNat 64 i ∗ ra ↦ᵣ v ∗
      P (BitVec.ofNat 64 (i + 4)) ∗
      (PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ ra ↦ᵣ BitVec.ofNat 64 (i + 4) -∗
        Q (BitVec.ofNat 64 (i + 4)) -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by sorry

/-- `wp_call` for `fnSpecAbort` (F3): the caller supplies the return branch
and the callee's abort branch from ONE context (`∧`). -/
theorem wp_callAbort {Wp : MachWP (GF := GF) M} {Φ : Nat × String → IProp GF} {i : Nat}
    {code : List (BitVec 8)} {entry v : BitVec 64} {P Q : BitVec 64 → IProp GF} {A : IProp GF}
    (hexec : JalExec M i code entry) :
    instrAt (GF := GF) i code ∗ fnSpecAbort Wp entry P Q A ∗ PC ↦ᵣ BitVec.ofNat 64 i ∗
      ra ↦ᵣ v ∗ P (BitVec.ofNat 64 (i + 4)) ∗
      ((PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ ra ↦ᵣ BitVec.ofNat 64 (i + 4) -∗
          Q (BitVec.ofNat 64 (i + 4)) -∗ Wp.W Φ) ∧ (A -∗ Wp.W Φ))
    ⊢ Wp.W Φ := by sorry

end Fn

/-! ## §C Representation predicates (R) -/

/-- The interpreter's ghost state (INTERP_DESIGN.md §3). Frame and closure
addresses are PERSISTENT map elements: an `Env*` never moves (only its arrays
are reallocated) and a closure is immutable. -/
class InterpGS (GF : BundledGFunctors) where
  frameMapG : GhostMapG GF Nat Nat NatMap
  closMapG : GhostMapG GF Nat Nat NatMap
  consoleG : GhostMapG GF Nat String NatMap
  frameName : GName
  closName : GName
  consoleName : GName

attribute [reducible, instance] InterpGS.frameMapG InterpGS.closMapG InterpGS.consoleG

section Repr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- Spec frame `fa` lives at machine `Env*` `e`, forever. -/
def frameAt (fa e : Nat) : IProp GF := ghost_map_elem I.frameName DFrac.discard fa e
/-- Spec closure `ca` lives at machine `Closure*` `p`, forever. -/
def closAt (ca p : Nat) : IProp GF := ghost_map_elem I.closName DFrac.discard ca p

instance (fa e : Nat) : Persistent (frameAt (GF := GF) fa e) := by unfold frameAt; infer_instance
instance (ca p : Nat) : Persistent (closAt (GF := GF) ca p) := by unfold closAt; infer_instance

/-- The console cell (F2 puts its authority in the state interpretation, tied
to `Vsa.Machine.output`). -/
def consoleOwn (s : String) : IProp GF := ghost_map_elem I.consoleName (DFrac.own 1) 0 s

/-- Immutable bytes. -/
def bytesRO (a : Nat) (bs : List (BitVec 8)) : IProp GF :=
  sepL bs.zipIdx (fun p => (a + p.2) ↦ₘ□ p.1)

/-- A C string, NUL included, read-only forever (`CString`). -/
def strAt (p : Nat) (s : String) : IProp GF :=
  iprop(⌜∀ c ∈ s.toList, 0 < c.toNat ∧ c.toNat < 128⌝ ∗
    bytesRO p (s.toList.map (fun c => BitVec.ofNat 8 c.toNat) ++ [0#8]))

/-- Persistent AST ownership: `ExprRepr` over read-only bytes. R proves the
lift `astE_of_exprRepr` from the boundary image. Stated here by existential
image for the skeleton; R replaces it with the structural definition. -/
def astE (a : Nat) (e : Expr) : IProp GF :=
  iprop(∃ (bs : List (Nat × BitVec 8)) (m : Mem), ⌜ExprRepr m a e ∧ ∀ q ∈ bs, m[q.1]? = some q.2 ∧
      ∀ k, (∃ b, m[k]? = some b) → ∃ b, (k, b) ∈ bs⌝ ∗
    sepL bs (fun q => q.1 ↦ₘ□ q.2))
def astS (a : Nat) (s : Stmt) : IProp GF :=
  iprop(∃ (bs : List (Nat × BitVec 8)) (m : Mem), ⌜StmtRepr m a s ∧ ∀ q ∈ bs, m[q.1]? = some q.2 ∧
      ∀ k, (∃ b, m[k]? = some b) → ∃ b, (k, b) ∈ bs⌝ ∗
    sepL bs (fun q => q.1 ↦ₘ□ q.2))
def astSs (a n : Nat) (ss : List Stmt) : IProp GF :=
  iprop(∃ (bs : List (Nat × BitVec 8)) (m : Mem), ⌜StmtArrayRepr m a n ss ∧ ∀ q ∈ bs, m[q.1]? = some q.2 ∧
      ∀ k, (∃ b, m[k]? = some b) → ∃ b, (k, b) ∈ bs⌝ ∗
    sepL bs (fun q => q.1 ↦ₘ□ q.2))

/-- The meaning of a 24-byte `Value`'s three words (`ValueRepr`), persistent. -/
def valOf (N : NativeAddrs) : Value → BitVec 64 → BitVec 64 → BitVec 64 → IProp GF
  | .null, w0, _, _ => iprop(⌜w0.toNat % 2^32 = 0⌝)
  | .bool b, w0, w1, _ => iprop(⌜w0.toNat % 2^32 = 1 ∧ w1.toNat % 2^32 = cond b 1 0⌝)
  | .int n, w0, w1, _ => iprop(⌜w0.toNat % 2^32 = 2 ∧ w1.toInt = n⌝)
  | .str s, w0, w1, _ => iprop(⌜w0.toNat % 2^32 = 3 ∧ w1.toNat ≠ 0⌝ ∗ strAt w1.toNat s)
  | .closure ca, w0, w1, _ => iprop(⌜w0.toNat % 2^32 = 4 ∧ w1.toNat ≠ 0⌝ ∗ closAt ca w1.toNat)
  | .native f, w0, w1, w2 =>
      iprop(⌜w0.toNat % 2^32 = 5 ∧ w2.toNat = N.addr f⌝ ∗ strAt w1.toNat (nativeName f))

/-- Eight little-endian bytes of a word, exclusive. -/
def word64 (a : Nat) (w : BitVec 64) : IProp GF :=
  sepL (List.range 8) (fun i => (a + i) ↦ₘ BitVec.ofNat 8 (w.toNat / 256 ^ i))

/-- A 24-byte slot of unknown contents (an sret buffer, a frame's spare slot). -/
def slot24 (a : Nat) : IProp GF := blockOwn a 24

/-- A represented value in an owned 24-byte slot (`ValueWordRepr`). -/
def valAt (N : NativeAddrs) (a : Nat) (v : Value) : IProp GF :=
  iprop(∃ w0 w1 w2 : BitVec 64, word64 a w0 ∗ word64 (a + 8) w1 ∗ word64 (a + 16) w2 ∗
    valOf N v w0 w1 w2)

/-- A closure object (`ClosureRepr`), persistent: `fn_expr` and `env` words,
the `EX_FN` node, and the captured frame's address. -/
def closOwn (ca : Nat) (cd : ClosureData) : IProp GF :=
  iprop(∃ p q e, closAt ca p ∗ bytesRO p ((List.range 8).map (fun i => BitVec.ofNat 8 (q / 256 ^ i)) ++
      (List.range 8).map (fun i => BitVec.ofNat 8 (e / 256 ^ i))) ∗
    astE q (.fn cd.name cd.params cd.body) ∗ frameAt cd.env e)

/-- One frame (`FrameRepr` + the ownership of its struct and array blocks).
The arrays are whole heap blocks with spare capacity; names are persistent
strings, slots exclusive. `blocks` are the heap blocks it owns (for
`B ⊆ H`). -/
def frameOwn (N : NativeAddrs) (fa : Nat) (f : Frame) (blocks : List (Nat × Nat)) : IProp GF :=
  iprop(∃ (e pn pv cap : Nat) (par : Nat),
    frameAt fa e ∗
    ⌜f.vars.length ≤ cap ∧ blocks = [(e, 32), (pn, 8 * cap), (pv, 24 * cap)] ∧
      (match f.parent with | none => par = 0 | some _ => par ≠ 0)⌝ ∗
    (match f.parent with | none => iprop(emp) | some pa => frameAt pa par) ∗
    -- the Env struct: count, cap, names, vals, parent
    blockOwn e 32 ∗
    -- names[0..count): persistent strings; names[count..cap): spare
    sepL (f.vars.zipIdx) (fun p => iprop(∃ q, word64 (pn + 8 * p.2) (BitVec.ofNat 64 q) ∗ strAt q p.1.1)) ∗
    blockOwn (pn + 8 * f.vars.length) (8 * (cap - f.vars.length)) ∗
    -- vals[0..count): represented slots; vals[count..cap): spare
    sepL (f.vars.zipIdx) (fun p => valAt N (pv + 24 * p.2) p.1.2) ∗
    blockOwn (pv + 24 * f.vars.length) (24 * (cap - f.vars.length)))
  -- R: the struct words' VALUES (count/cap/pn/pv/par) are pinned inside
  -- `blockOwn e 32` by a structural refinement; kept existential here.

/-- The whole store (`StoreRepr` + `HeapOwned` + `StoreOwned`), monolithic:
BigStep's frames are shared by closures, so every call can reach any frame.
`env_*` specs open ONE frame with one opener/closer (R). -/
def storeRepr (N : NativeAddrs) (s : Store) (B : List (Nat × Nat)) : IProp GF :=
  iprop(∃ (mf mc : NatMap Nat) (Bs : List (List (Nat × Nat))),
    ghost_map_auth I.frameName (DFrac.own 1) mf ∗ ghost_map_auth I.closName (DFrac.own 1) mc ∗
    ⌜(∀ k, (PartialMap.get? mf k).isSome ↔ k < s.frames.size) ∧
      (∀ k, (PartialMap.get? mc k).isSome ↔ k < s.closures.size) ∧
      Bs.length = s.frames.size ∧ B = Bs.flatten ∧
      StoreBodiesBound s perCallBudget⌝ ∗
    sepL (List.range s.frames.size) (fun fa =>
      iprop(∃ (f : Frame) (bl : List (Nat × Nat)), ⌜s.frames[fa]? = some f ∧ Bs[fa]? = some bl⌝ ∗
        frameOwn N fa f bl)) ∗
    sepL (List.range s.closures.size) (fun ca =>
      iprop(∃ cd, ⌜s.closures[ca]? = some cd⌝ ∗ □ closOwn ca cd)))

/-- The `Interp` struct at `inp`: `call_depth` exclusive, `globals` and the
`jmp_buf` read-only, `err_msg` exclusive. Offsets from `interp.h` /
`LayoutInstance.InterpRunPhysicalFacts` (R pins them). -/
def interpCtx (inp : Nat) (d : Nat) : IProp GF :=
  iprop(∃ g, sepL (List.range 4) (fun i => (inp + 8 + i) ↦ₘ BitVec.ofNat 8 (d / 256 ^ i)) ∗
    frameAt 0 g ∗ blockOwn (inp + 24) 256)
  -- R: add the persistent `on_error` bytes once `setjmp` has run.

/-- MachCSL's two allocator regimes (`KvmSpec.v:123` `kalloc_env γ (Some n)` /
`None`, paper §6.5): counted (total mode; cannot fail) and uncounted (partial
mode; malloc may return NULL). -/
inductive Regime where
  | counted (k : Nat)
  | uncounted

def heapRes (L : DlLayout) (Room : RoomPred) : Regime → List (Nat × Nat) → IProp GF
  | .counted k, H => isHeapRoom L Room H k
  | .uncounted, H => isHeap L H

/-- Everything an evaluation threads: heap, store, console, interpreter
context. `B ⊆ H` ties the store's blocks to the allocator's live list. -/
def world (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)
    (ρ : Regime) (st : St) (d : Nat) : IProp GF :=
  iprop(∃ H B, heapRes L Room ρ H ∗ storeRepr N st.store B ∗ consoleOwn st.out ∗
    interpCtx inp d ∗ ⌜∀ b ∈ B, b ∈ H⌝)

/-- R's two-owner sanity lemma (xv6iris durable-notes "The resource form"):
the world is satisfiable, not merely well-typed. Proved at the boundary
world (A0), stated here as the obligation. -/
theorem world_consistent_obligation : True := trivial

end Repr

/-! ## §D The three recursive specs -/

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable (M : MachineModel) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)

/-- ItemZero's budget, verbatim from `EvalEntry.stackBudget`
(`Vsa/Sim/InterpEntry.lean:630`); the sum, never a round number. -/
def evalNeed (e : Expr) (d : Nat) : Nat := e.stackNeed + (maxCallDepth - d) * perCallBudget + evalFrame
def execNeed (s : Stmt) (d : Nat) : Nat := s.stackNeed + (maxCallDepth - d) * perCallBudget + evalFrame

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
    ⊢ evalSpecT_body M N L Room inp st d env e st' v n D := by sorry

theorem execSpecT (st : St) (d env : Nat) (sm : Stmt) (st' : St) (status : Status) (n : Nat)
    (D : ExecSCost st d env sm st' status n) :
    ⊢ execSpecT_body M N L Room inp st d env sm st' status n D := by sorry

/-! ### Partial, outcome-quantified, with abort (stuck_sim) -/

/-- What an abort hands the top: the landing registers (H5 pins them from the
`jmp_buf`, or the `exit(1)` entry for OOM), SOME world, and the whole owned
stack below `s`. Callers re-base it at each call (`abort_rebase`). -/
def abortRes (s : BitVec 64) (need : Nat) : IProp GF :=
  iprop(∃ (landing : Bool) (ρ : Regime) (st : St) (d : Nat),
    world N L Room inp ρ st d ∗ stackScratch s need ∗
    (if landing then PC ↦ᵣ 0#64 -- H5: the `setjmp` return site in `interp_run`, a0 = 1
     else PC ↦ᵣ 0x80004764#64 ∗ (10 : Nat) ↦ᵣ 1#64)) -- `exit`, a0 = 1

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
    ⊢ □ ((∀ st d env e, evalSpecP_body M N L Room inp st d env e) ∧
         (∀ st d env sm, execSpecP_body M N L Room inp st d env sm)) := by sorry

/-- F3: re-basing an abort continuation from the caller's region to the
child's, joining the caller's frame bytes `[s_c, s_p)` back in. -/
theorem abort_rebase {Wp : MachWP (GF := GF) M} {Φ : Nat × String → IProp GF}
    (sp_ sc : BitVec 64) (np nc : Nat) (hle : sp_.toNat - np ≤ sc.toNat - nc)
    (hsc : sc.toNat ≤ sp_.toNat) :
    (abortRes N L Room inp sp_ np -∗ Wp.W Φ) ∗
      blockOwn (sc.toNat) (sp_.toNat - sc.toNat) ∗
      blockOwn (sp_.toNat - np) ((sc.toNat - nc) - (sp_.toNat - np))
    ⊢ (abortRes N L Room inp sc nc -∗ Wp.W Φ) := by sorry

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
statement through the Löb hypothesis. Statement is G's to fix against the real
seam registers; recorded here as the obligation. -/
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
  /-- Safety of `snprintf` (`%s`/`%d` messages in `runtime_error`) and
  `fprintf` (error and OOM paths). Partial mode only. -/
  newlib : True
  -- DESIGN: replace each `True` with the exact run/spec structure once H4/H5
  -- fix their statements.

/-- The boundary (A0): from `InterpRunReady` and `ProgramRepr`, allocate the
ghost state and produce the initial world, the persistent AST and code, the
top stack region, in either regime. -/
theorem world_of_boundary_obligation : True := trivial

/-- Q1 (user approval needed): the stack admissibility a loaded program must
satisfy, beside `DlHeap.InitialAllocatorAt.capacity`. Without it, an AST
deeper than the 8 MiB stack overflows into the heap directly below
(`heapEnd = 0x87800000 = stackSL.lo`) and neither `term_sim` nor `stuck_sim`
is provable. -/
def StackAdmissible (m : Mem) (stmts count : Nat) : Prop :=
  ∀ p : Program, ProgramRepr m stmts count p →
    Stmt.stackNeedList p + maxCallDepth * perCallBudget + evalFrame + execFrame ≤ 0x800000 ∧
    Stmt.bodiesBoundList perCallBudget p = true

/-- The layout with Q1's field (A0 defines it by extending `InterpRunReady`). -/
opaque interpRunLayout' : Vsa.Refine.Layout

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
