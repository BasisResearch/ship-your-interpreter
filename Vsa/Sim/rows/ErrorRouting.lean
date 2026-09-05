import Vsa.Sim.ErrorSiteRows
import Vsa.Sim.ErrorReach
import Vsa.Sim.InterpSimBundle
import Vsa.Sim.rows.ErrSitesBatch0
import Vsa.Sim.rows.ErrSitesBatch1
import Vsa.Sim.rows.ErrSitesBatch2
import Vsa.Sim.rows.ErrSitesBatch3

/-!
# Faithful error-family routing

The semantic error recursors have two kinds of constructors:

* a leaf discovers a new runtime error and must reach its concrete executable
  error site;
* a propagation constructor merely wraps a child error derivation and must
  return the child's `ErrHalts` induction hypothesis.

The previous generated file treated both kinds as leaves.  It discarded the
child induction hypotheses, assigned unrelated fixed PCs to propagation nodes,
and collapsed every `hBinaryOp` failure to one PC.  This file exposes only the
eleven real leaf obligations (ten named leaves plus the cause-indexed binary
family).  Propagation is discharged definitionally in `errFamilyClosed`.

The new `hCallTooMany` field below is still a residual, not an exact supplier.
The constant `ErrHalts c` error motive does not retain an `EvalEntry` relating
the arbitrary `c` to the call node.  Closing it requires an entry-indexed error
motive (or caller-side call-arm composition); the concrete `0x80003fdc` row
alone cannot manufacture that missing relation.

`hBadClosure` remains a specification-only residual because the executable C
store cannot contain a dangling closure pointer.  `hTopAbrupt` is a separate
`InterpRunAbruptPath`: top-level abrupt status is handled directly by
`interp_run`, without a `jal runtime_error`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config)
open Vsa.Logic (Triple)
open Vsa.While
open Register

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-- Shared runtime-error tail data used by every executable leaf site. -/
structure ErrShared where
  g : (R : Register) → Option (RegisterType R)
  inp : BitVec 64
  ra0 : BitVec 64
  s0v : BitVec 64
  s1v : BitVec 64
  s2v : BitVec 64
  s3v : BitVec 64
  s4v : BitVec 64
  s5v : BitVec 64
  s6v : BitVec 64
  s7v : BitVec 64
  s8v : BitVec 64
  s9v : BitVec 64
  s10v : BitVec 64
  s11v : BitVec 64
  spv : BitVec 64
  m0 : Std.ExtHashMap Nat (BitVec 8)
  SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0
  out : String
  HT : ErrorTailChain ra0 ExitStorePreExit out

/-- Close one concrete `jal runtime_error` leaf from an entry-to-site run. -/
theorem errRow_reach (S : ErrShared)
    (pcJal : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (T : Triple (JalErrPre S.g S.inp S.m0 pcJal b0 b1 b2 b3)
      (fun c' => RuntimeErrorAt S.g S.inp S.m0 c'))
    (c : Config) (hreach : ReachJal S.g S.inp S.m0 pcJal b0 b1 b2 b3 c) :
    ErrHalts c :=
  errRow S.g S.inp S.ra0 S.s0v S.s1v S.s2v S.s3v S.s4v S.s5v S.s6v S.s7v
    S.s8v S.s9v S.s10v S.s11v S.spv S.m0 S.SC S.out S.HT
    (SitePre := ReachJal S.g S.inp S.m0 pcJal b0 b1 b2 b3)
    (Triple.seq (reachJal_triple S.g S.inp S.m0 pcJal b0 b1 b2 b3) T) c hreach

/-! ## Executable leaf routes -/

theorem route_hVarUndef (S : ErrShared)
    (hsite : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (x : String),
      st.store.get? env x = none →
      ReachJal S.g S.inp S.m0 0x80003fac#64 0xef#8 0xe0#8 0xdf#8 0xdf#8 c) :
    ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (x : String),
      st.store.get? env x = none → ErrHalts c :=
  fun c st d env x hnone =>
    errRow_reach S 0x80003fac#64 0xef#8 0xe0#8 0xdf#8 0xdf#8
      (errSite_80003fac S.g S.inp S.m0) c (hsite c st d env x hnone)

theorem route_hAssignUnbound (S : ErrShared)
    (hsite : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr)
      (st' : SpecSt) (v : Value), EvalE st d env e st' v →
      st'.store.set? env x v = none →
      ReachJal S.g S.inp S.m0 0x800034e4#64 0xef#8 0xf0#8 0x5f#8 0x8c#8 c) :
    ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr)
      (st' : SpecSt) (v : Value), EvalE st d env e st' v →
      st'.store.set? env x v = none → ErrHalts c :=
  fun c st d env x e st' v he hnone =>
    errRow_reach S 0x800034e4#64 0xef#8 0xf0#8 0x5f#8 0x8c#8
      (errSite_800034e4 S.g S.inp S.m0) c
      (hsite c st d env x e st' v he hnone)

theorem route_hNegType (S : ErrShared)
    (hsite : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr)
      (st' : SpecSt) (v : Value), EvalE st d env e st' v →
      (∀ n : Int, v ≠ .int n) →
      ReachJal S.g S.inp S.m0 0x80003b9c#64 0xef#8 0xf0#8 0xcf#8 0xa0#8 c) :
    ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr)
      (st' : SpecSt) (v : Value), EvalE st d env e st' v →
      (∀ n : Int, v ≠ .int n) → ErrHalts c :=
  fun c st d env e st' v he htype =>
    errRow_reach S 0x80003b9c#64 0xef#8 0xf0#8 0xcf#8 0xa0#8
      (errSite_80003b9c S.g S.inp S.m0) c
      (hsite c st d env e st' v he htype)

/-- The fixed 32-slot call buffer is checked after callee evaluation and before
argument evaluation. -/
theorem route_hCallTooMany (S : ErrShared)
    (hsite : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (f : Expr)
      (args : List Expr) (st' : SpecSt) (fv : Value),
      EvalE st d env f st' fv → maxArgs < args.length →
      ReachJal S.g S.inp S.m0 0x80003fdc#64 0xef#8 0xe0#8 0xdf#8 0xdc#8 c) :
    ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (f : Expr)
      (args : List Expr) (st' : SpecSt) (fv : Value),
      EvalE st d env f st' fv → maxArgs < args.length → ErrHalts c :=
  fun c st d env f args st' fv he hbound =>
    errRow_reach S 0x80003fdc#64 0xef#8 0xe0#8 0xdf#8 0xdc#8
      (errSite_80003fdc S.g S.inp S.m0) c
      (hsite c st d env f args st' fv he hbound)

theorem route_hNotCallable (S : ErrShared)
    (hsite : ∀ (c : Config) (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value),
      (∀ a, fv ≠ .closure a) → (∀ f, fv ≠ .native f) →
      ReachJal S.g S.inp S.m0 0x80003de8#64 0xef#8 0xe0#8 0x1f#8 0xfc#8 c) :
    ∀ (c : Config) (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value),
      (∀ a, fv ≠ .closure a) → (∀ f, fv ≠ .native f) → ErrHalts c :=
  fun c st d fv vs hc hn =>
    errRow_reach S 0x80003de8#64 0xef#8 0xe0#8 0x1f#8 0xfc#8
      (errSite_80003de8 S.g S.inp S.m0) c (hsite c st d fv vs hc hn)

theorem route_hArity (S : ErrShared)
    (hsite : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr)
      (cd : ClosureData) (vs : List Value), st.store.closures[a]? = some cd →
      vs.length ≠ cd.params.length →
      ReachJal S.g S.inp S.m0 0x80003da0#64 0xef#8 0xf0#8 0x8f#8 0x80#8 c) :
    ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr)
      (cd : ClosureData) (vs : List Value), st.store.closures[a]? = some cd →
      vs.length ≠ cd.params.length → ErrHalts c :=
  fun c st d a cd vs hclos hlen =>
    errRow_reach S 0x80003da0#64 0xef#8 0xf0#8 0x8f#8 0x80#8
      (errSite_80003da0 S.g S.inp S.m0) c (hsite c st d a cd vs hclos hlen)

theorem route_hDepth (S : ErrShared)
    (hsite : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr)
      (cd : ClosureData) (vs : List Value), st.store.closures[a]? = some cd →
      vs.length = cd.params.length → ¬ d < maxCallDepth →
      ReachJal S.g S.inp S.m0 0x80003cc4#64 0xef#8 0xf0#8 0x4f#8 0x8e#8 c) :
    ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr)
      (cd : ClosureData) (vs : List Value), st.store.closures[a]? = some cd →
      vs.length = cd.params.length → ¬ d < maxCallDepth → ErrHalts c :=
  fun c st d a cd vs hclos hlen hdepth =>
    errRow_reach S 0x80003cc4#64 0xef#8 0xf0#8 0x4f#8 0x8e#8
      (errSite_80003cc4 S.g S.inp S.m0) c
      (hsite c st d a cd vs hclos hlen hdepth)

theorem route_hEscape (S : ErrShared)
    (hsite : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr)
      (cd : ClosureData) (vs : List Value) (store' : Store) (frame : Addr)
      (st' : SpecSt) (status : Status), st.store.closures[a]? = some cd →
      vs.length = cd.params.length → d < maxCallDepth →
      st.store.allocFrame (some cd.env) = (store', frame) →
      ExecSeq ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store', st.out⟩
        (d + 1) frame cd.body st' status →
      (status = .brk ∨ status = .cont) →
      ReachJal S.g S.inp S.m0 0x80003ce8#64 0xef#8 0xf0#8 0x0f#8 0x8c#8 c) :
    ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr)
      (cd : ClosureData) (vs : List Value) (store' : Store) (frame : Addr)
      (st' : SpecSt) (status : Status), st.store.closures[a]? = some cd →
      vs.length = cd.params.length → d < maxCallDepth →
      st.store.allocFrame (some cd.env) = (store', frame) →
      ExecSeq ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store', st.out⟩
        (d + 1) frame cd.body st' status →
      (status = .brk ∨ status = .cont) → ErrHalts c :=
  fun c st d a cd vs store' frame st' status hclos hlen hdepth halloc hbody hstatus =>
    errRow_reach S 0x80003ce8#64 0xef#8 0xf0#8 0x0f#8 0x8c#8
      (errSite_80003ce8 S.g S.inp S.m0) c
      (hsite c st d a cd vs store' frame st' status hclos hlen hdepth halloc hbody hstatus)

theorem route_hAssertFail (S : ErrShared)
    (hsite : ∀ (c : Config) (st : SpecSt) (d : Nat) (vs : List Value)
      (v m : Value), (vs = [v] ∨ vs = [v, m]) → v.truthy = false →
      ReachJal S.g S.inp S.m0 0x80002ebc#64 0xef#8 0xf0#8 0xdf#8 0xee#8 c) :
    ∀ (c : Config) (st : SpecSt) (d : Nat) (vs : List Value)
      (v m : Value), (vs = [v] ∨ vs = [v, m]) → v.truthy = false → ErrHalts c :=
  fun c st d vs v m hvs hf =>
    errRow_reach S 0x80002ebc#64 0xef#8 0xf0#8 0xdf#8 0xee#8
      (errSite_80002ebc S.g S.inp S.m0) c (hsite c st d vs v m hvs hf)

theorem route_hAssertArity (S : ErrShared)
    (hsite : ∀ (c : Config) (st : SpecSt) (d : Nat) (vs : List Value),
      (∀ v, vs ≠ [v]) → (∀ v m, vs ≠ [v, m]) →
      ReachJal S.g S.inp S.m0 0x80002e90#64 0xef#8 0xf0#8 0x9f#8 0xf1#8 c) :
    ∀ (c : Config) (st : SpecSt) (d : Nat) (vs : List Value),
      (∀ v, vs ≠ [v]) → (∀ v m, vs ≠ [v, m]) → ErrHalts c :=
  fun c st d vs h1 h2 =>
    errRow_reach S 0x80002e90#64 0xef#8 0xf0#8 0x9f#8 0xf1#8
      (errSite_80002e90 S.g S.inp S.m0) c (hsite c st d vs h1 h2)

/-- Close the cause-indexed binary route.  Pattern matching preserves the
constructor's concrete PC; no default or shared binary site exists. -/
theorem errHalts_of_binaryErrReach (S : ErrShared) {c : Config} {s : Store}
    {op : BinOp} {lv rv : Value}
    (h : BinaryErrReach S.g S.inp S.m0 c s op lv rv) : ErrHalts c := by
  cases h with
  | add _ hreach => exact errRow_reach S _ _ _ _ _ (errSite_80003d5c S.g S.inp S.m0) c hreach
  | sub _ hreach => exact errRow_reach S _ _ _ _ _ (errSite_80003b9c S.g S.inp S.m0) c hreach
  | mul _ hreach => exact errRow_reach S _ _ _ _ _ (errSite_80003c7c S.g S.inp S.m0) c hreach
  | divZero _ hreach => exact errRow_reach S _ _ _ _ _ (errSite_80003d14 S.g S.inp S.m0) c hreach
  | divType _ _ hreach => exact errRow_reach S _ _ _ _ _ (errSite_80003f58 S.g S.inp S.m0) c hreach
  | modZero _ hreach => exact errRow_reach S _ _ _ _ _ (errSite_80003bc8 S.g S.inp S.m0) c hreach
  | modType _ _ hreach => exact errRow_reach S _ _ _ _ _ (errSite_80003c10 S.g S.inp S.m0) c hreach
  | lt _ hreach => exact errRow_reach S _ _ _ _ _ (errSite_80003e98 S.g S.inp S.m0) c hreach
  | le _ hreach => exact errRow_reach S _ _ _ _ _ (errSite_80003e98 S.g S.inp S.m0) c hreach
  | gt _ hreach => exact errRow_reach S _ _ _ _ _ (errSite_80003e98 S.g S.inp S.m0) c hreach
  | ge _ hreach => exact errRow_reach S _ _ _ _ _ (errSite_80003e98 S.g S.inp S.m0) c hreach

theorem route_hBinaryOp (S : ErrShared)
    (hsite : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp)
      (l r : Expr) (st' st'' : SpecSt) (lv rv : Value),
      EvalE st d env l st' lv → EvalE st' d env r st'' rv →
      binOpSem st''.store op lv rv = none →
      BinaryErrReach S.g S.inp S.m0 c st''.store op lv rv) :
    ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp)
      (l r : Expr) (st' st'' : SpecSt) (lv rv : Value),
      EvalE st d env l st' lv → EvalE st' d env r st'' rv →
      binOpSem st''.store op lv rv = none → ErrHalts c :=
  fun c st d env op l r st' st'' lv rv hl hr hnone =>
    errHalts_of_binaryErrReach S (hsite c st d env op l r st' st'' lv rv hl hr hnone)

/-! ## Family assembly

Every propagation goal below is solved from its final `ErrHalts c` induction
hypothesis.  Consequently the public interface contains no propagation-site
premises and no fabricated propagation PCs.
-/

/- Obsolete constant-config family assembly.  The route lemmas above remain
useful locally, but this aggregate interface erased every semantic entry.
theorem errFamilyClosed (L : Vsa.Refine.Layout) (S : ErrShared)
    (hsite_hVarUndef : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (x : String),
      st.store.get? env x = none →
      ReachJal S.g S.inp S.m0 0x80003fac#64 0xef#8 0xe0#8 0xdf#8 0xdf#8 c)
    (hsite_hAssignUnbound : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr)
      (x : String) (e : Expr) (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → st'.store.set? env x v = none →
      ReachJal S.g S.inp S.m0 0x800034e4#64 0xef#8 0xf0#8 0x5f#8 0x8c#8 c)
    (hsite_hBinaryOp : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr)
      (op : BinOp) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value),
      EvalE st d env l st' lv → EvalE st' d env r st'' rv →
      binOpSem st''.store op lv rv = none →
      BinaryErrReach S.g S.inp S.m0 c st''.store op lv rv)
    (hsite_hNegType : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr)
      (e : Expr) (st' : SpecSt) (v : Value), EvalE st d env e st' v →
      (∀ n : Int, v ≠ .int n) →
      ReachJal S.g S.inp S.m0 0x80003b9c#64 0xef#8 0xf0#8 0xcf#8 0xa0#8 c)
    (hsite_hCallTooMany : ∀ (c : Config) (st : SpecSt) (d : Nat)
      (env : Addr) (f : Expr) (args : List Expr) (st' : SpecSt) (fv : Value),
      EvalE st d env f st' fv → maxArgs < args.length →
      ReachJal S.g S.inp S.m0 0x80003fdc#64 0xef#8 0xe0#8 0xdf#8 0xdc#8 c)
    (hsite_hNotCallable : ∀ (c : Config) (st : SpecSt) (d : Nat)
      (fv : Value) (vs : List Value), (∀ a, fv ≠ .closure a) →
      (∀ f, fv ≠ .native f) →
      ReachJal S.g S.inp S.m0 0x80003de8#64 0xef#8 0xe0#8 0x1f#8 0xfc#8 c)
    (hsite_hBadClosure : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr)
      (vs : List Value), st.store.closures[a]? = none → ErrHalts c)
    (hsite_hArity : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr)
      (cd : ClosureData) (vs : List Value), st.store.closures[a]? = some cd →
      vs.length ≠ cd.params.length →
      ReachJal S.g S.inp S.m0 0x80003da0#64 0xef#8 0xf0#8 0x8f#8 0x80#8 c)
    (hsite_hDepth : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr)
      (cd : ClosureData) (vs : List Value), st.store.closures[a]? = some cd →
      vs.length = cd.params.length → ¬ d < maxCallDepth →
      ReachJal S.g S.inp S.m0 0x80003cc4#64 0xef#8 0xf0#8 0x4f#8 0x8e#8 c)
    (hsite_hEscape : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr)
      (cd : ClosureData) (vs : List Value) (store' : Store) (frame : Addr)
      (st' : SpecSt) (status : Status), st.store.closures[a]? = some cd →
      vs.length = cd.params.length → d < maxCallDepth →
      st.store.allocFrame (some cd.env) = (store', frame) →
      ExecSeq ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store', st.out⟩
        (d + 1) frame cd.body st' status →
      (status = .brk ∨ status = .cont) →
      ReachJal S.g S.inp S.m0 0x80003ce8#64 0xef#8 0xf0#8 0x0f#8 0x8c#8 c)
    (hsite_hAssertFail : ∀ (c : Config) (st : SpecSt) (d : Nat)
      (vs : List Value) (v m : Value), (vs = [v] ∨ vs = [v, m]) →
      v.truthy = false →
      ReachJal S.g S.inp S.m0 0x80002ebc#64 0xef#8 0xf0#8 0xdf#8 0xee#8 c)
    (hsite_hAssertArity : ∀ (c : Config) (st : SpecSt) (d : Nat)
      (vs : List Value), (∀ v, vs ≠ [v]) → (∀ v m, vs ≠ [v, m]) →
      ReachJal S.g S.inp S.m0 0x80002e90#64 0xef#8 0xf0#8 0x9f#8 0xf1#8 c)
    (hsite_hTopAbrupt : ∀ (p : Program) (c : Config), InterpRunAbruptPath p c) :
    Vsa.Sim.InterpSimBundle.ErrFamily L := by
  apply Vsa.Sim.InterpSimBundle.errFamily_of_sites L
  · exact route_hVarUndef S hsite_hVarUndef
  · intros; assumption
  · exact route_hAssignUnbound S hsite_hAssignUnbound
  · intros; assumption
  · intros; assumption
  · exact route_hBinaryOp S hsite_hBinaryOp
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · exact route_hNegType S hsite_hNegType
  · intros; assumption
  · exact route_hCallTooMany S hsite_hCallTooMany
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · exact route_hNotCallable S hsite_hNotCallable
  · exact hsite_hBadClosure
  · exact route_hArity S hsite_hArity
  · exact route_hDepth S hsite_hDepth
  · intros; assumption
  · exact route_hEscape S hsite_hEscape
  · exact route_hAssertFail S hsite_hAssertFail
  · exact route_hAssertArity S hsite_hAssertArity
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · intros; assumption
  · exact fun p c => errHalts_of_interpRunAbruptPath (hsite_hTopAbrupt p c)

/-- The eleven executable leaf-link residuals.  No propagation constructor is a
field of this structure. -/
structure ErrLeafLinks (S : ErrShared) where
  hVarUndef : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (x : String),
    st.store.get? env x = none →
    ReachJal S.g S.inp S.m0 0x80003fac#64 0xef#8 0xe0#8 0xdf#8 0xdf#8 c
  hAssignUnbound : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr)
    (x : String) (e : Expr) (st' : SpecSt) (v : Value),
    EvalE st d env e st' v → st'.store.set? env x v = none →
    ReachJal S.g S.inp S.m0 0x800034e4#64 0xef#8 0xf0#8 0x5f#8 0x8c#8 c
  hBinaryOp : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr)
    (op : BinOp) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value),
    EvalE st d env l st' lv → EvalE st' d env r st'' rv →
    binOpSem st''.store op lv rv = none →
    BinaryErrReach S.g S.inp S.m0 c st''.store op lv rv
  hNegType : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr)
    (e : Expr) (st' : SpecSt) (v : Value), EvalE st d env e st' v →
    (∀ n : Int, v ≠ .int n) →
    ReachJal S.g S.inp S.m0 0x80003b9c#64 0xef#8 0xf0#8 0xcf#8 0xa0#8 c
  hCallTooMany : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr)
    (f : Expr) (args : List Expr) (st' : SpecSt) (fv : Value),
    EvalE st d env f st' fv → maxArgs < args.length →
    ReachJal S.g S.inp S.m0 0x80003fdc#64 0xef#8 0xe0#8 0xdf#8 0xdc#8 c
  hNotCallable : ∀ (c : Config) (st : SpecSt) (d : Nat)
    (fv : Value) (vs : List Value), (∀ a, fv ≠ .closure a) →
    (∀ f, fv ≠ .native f) →
    ReachJal S.g S.inp S.m0 0x80003de8#64 0xef#8 0xe0#8 0x1f#8 0xfc#8 c
  hArity : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr)
    (cd : ClosureData) (vs : List Value), st.store.closures[a]? = some cd →
    vs.length ≠ cd.params.length →
    ReachJal S.g S.inp S.m0 0x80003da0#64 0xef#8 0xf0#8 0x8f#8 0x80#8 c
  hDepth : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr)
    (cd : ClosureData) (vs : List Value), st.store.closures[a]? = some cd →
    vs.length = cd.params.length → ¬ d < maxCallDepth →
    ReachJal S.g S.inp S.m0 0x80003cc4#64 0xef#8 0xf0#8 0x4f#8 0x8e#8 c
  hEscape : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr)
    (cd : ClosureData) (vs : List Value) (store' : Store) (frame : Addr)
    (st' : SpecSt) (status : Status), st.store.closures[a]? = some cd →
    vs.length = cd.params.length → d < maxCallDepth →
    st.store.allocFrame (some cd.env) = (store', frame) →
    ExecSeq ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store', st.out⟩
      (d + 1) frame cd.body st' status →
    (status = .brk ∨ status = .cont) →
    ReachJal S.g S.inp S.m0 0x80003ce8#64 0xef#8 0xf0#8 0x0f#8 0x8c#8 c
  hAssertFail : ∀ (c : Config) (st : SpecSt) (d : Nat)
    (vs : List Value) (v m : Value), (vs = [v] ∨ vs = [v, m]) →
    v.truthy = false →
    ReachJal S.g S.inp S.m0 0x80002ebc#64 0xef#8 0xf0#8 0xdf#8 0xee#8 c
  hAssertArity : ∀ (c : Config) (st : SpecSt) (d : Nat)
    (vs : List Value), (∀ v, vs ≠ [v]) → (∀ v m, vs ≠ [v, m]) →
    ReachJal S.g S.inp S.m0 0x80002e90#64 0xef#8 0xf0#8 0x9f#8 0xf1#8 c

/-- Assemble the error family from the named leaf bundle and the two
non-executable/non-`jal` residuals. -/
theorem errFamilyClosed_ofLinks (L : Vsa.Refine.Layout) (S : ErrShared)
    (H : ErrLeafLinks S)
    (hBadClosure : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr)
      (vs : List Value), st.store.closures[a]? = none → ErrHalts c)
    (hTopAbrupt : ∀ (p : Program) (c : Config), InterpRunAbruptPath p c) :
    Vsa.Sim.InterpSimBundle.ErrFamily L :=
  errFamilyClosed L S H.hVarUndef H.hAssignUnbound H.hBinaryOp H.hNegType
    H.hCallTooMany H.hNotCallable hBadClosure H.hArity H.hDepth H.hEscape H.hAssertFail
    H.hAssertArity hTopAbrupt

#print axioms errRow_reach
#print axioms errHalts_of_binaryErrReach
#print axioms errFamilyClosed
#print axioms errFamilyClosed_ofLinks
-/

end Vsa.Sim
