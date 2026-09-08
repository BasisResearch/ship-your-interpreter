import Vsa.Sim.rows.CallRows
import Vsa.Sim.rows.ArgsReturnCopy
import Vsa.Sim.ArmSegSplitEval
import Vsa.Sim.rows.CallArmEpilogue
import Vsa.Sim.rows.NativeArmSplice
import Vsa.Sim.rows.NativeArmDispatch
import Vsa.Sim.StackSlotGeom

/-!
# `CallResidProviders` — reducers for the named residuals of `CallRows`

`CallRows` states the call-subsystem cases conditional on named residuals.  This
file gives those residuals stable provider names while preserving every
semantic index and ABI fact in the new `EvalArgsEntryI`/`EvalArgsExitI` and
`CallEntryI`/`CallExitI` boundaries.  The providers remain explicit machine
oracles; these reducers do not claim to prove the decoded spans.

## What each reducer does

| residual | reducer | collapses to |
|---|---|---|
| `ArgsConsResid` | `argsConsResid_of_stages` | decoded head staging, recursive child IH, reflected return/copy block, and exact tail cursor |
| native call residuals | `native*Spec_of_stages` | strict dispatch, native-body, and machine-proved join stages |

## Mechanical-duplication finding (native branch)

`print`, `println`, `assert` share **the entire native dispatch+jalr+join span**
(`callDispatchPC 0x80003254` fv-kind decode ≫ `callNativePC 0x800039e0` ABI
marshal ≫ `jalr a6` ≫ `0x800039f8` restore ≫ `j 0x800033ec` join).  The only
per-native difference is (a) the resolved target `a6 = N.addr f`
(`ValueRepr (.native f)` ghost) and (b) the callee body's store/output effect.
So the route is factored as `NativeCallStages`, and each native residual is a one-line instance. This
mirrors `println = print ≫ fputc('\n')` at the *body* level: `native_println`'s
body contract is `native_print`'s composed with one trailing HTIF append.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.  Every leftover is a NAMED typed
premise (`ArgsBodyStageProvider`, `NativeCallStages`).
-/

namespace Vsa.Sim.Rows

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim
open Vsa.Sim.Scaffold
open Vsa.Sim.TermSimAssembly

local notation "SpecSt" => Vsa.While.St

/-! ## Residual 1 — one argument iteration, split at real machine boundaries -/

/-- A recursive child-call checkpoint that retains the exact enclosing call
node in the same witness package as `JalPreCore`.  This prevents the call node,
stack layout, arena, and pre-call memory from being chosen independently. -/
def CallChildJalPre
    (callNode : BitVec 64) (f : Expr) (args : List Expr) (child : Expr)
    (c : Config) (st : SpecSt) (d : Nat) (env : Addr) : Prop :=
  ∃ (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (callPC retPC : BitVec 64) (jalImm : BitVec 21)
    (sp r sret subsret aIn aOperand : BitVec 64) (v8 v9 v18 : BitVec 64)
    (out0 : Array String) (mcall : Mem) (lo hi : Nat),
    JalPreCore child c st d env gpre N A SL φf φc callPC retPC jalImm
      sp r sret subsret aIn aOperand v8 v9 v18 out0 mcall ∧
    gpre Register.x8 = some callNode ∧
    ExprRepr mcall callNode.toNat (.call f args) ∧
    AstRegionSpec mcall SL A sret.toNat callNode.toNat (.call f args) lo hi

/-- The state after the recursive `eval_expr` child returns at `0x80003224`.
The carrier retains the exact enclosing call node and its transported
`ExprRepr`; these are tied to the same `SubEvalReturn` witnesses. -/
def ArgsChildReturn
    (st st' : SpecSt) (d : Nat) (env : Addr)
    (callNode : BitVec 64) (f : Expr) (args : List Expr)
    (e : Expr) (v : Value) :
    Config → Prop :=
  fun c =>
    ∃ (gpre : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (sp r sret subsret retPC v8 v9 v18 : BitVec 64) (mcall : Mem),
      StackBounds sp SL ∧
        SubEvalReturn gpre N A SL φf φc
          st.store.frames.size st.store.closures.size st' v
          sp r sret subsret retPC v8 v9 v18 mcall c ∧
        c.σ.regs.get? Register.x8 = some callNode ∧
        ExprRepr c.σ.mem callNode.toNat (.call f args) ∧
        ∃ lo hi, AstRegionSpec c.σ.mem SL A sret.toNat callNode.toNat
          (.call f args) lo hi

/-- A staged `jal eval_expr` plus the semantic child IH reaches the exact
post-child boundary used by the copy block. -/
theorem argsChildReturn_of_jalBundle
    (st st' : SpecSt) (d : Nat) (env : Addr)
    (callNode : BitVec 64) (f : Expr) (args : List Expr)
    (e : Expr) (v : Value)
    (hIH : EvalIH st d env e st' v) :
    Triple
      (fun c => CallChildJalPre callNode f args e c st d env)
      (ArgsChildReturn st st' d env callNode f args e v) := by
  intro c hc
  obtain ⟨gpre, N, A, SL, φf, φc, callPC, retPC, jalImm, sp, r, sret,
    subsret, aIn, aOperand, v8, v9, v18, out0, mcall, lo, hi,
    hcore, hgpre8, hcallRepr, hcallRegion⟩ := hc
  obtain ⟨henvValid, hjaltgt, hlink, hretAl, hjalSite, hpre⟩ := hcore
  have hstackBounds : StackBounds sp SL := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega
  obtain ⟨c', hs, hret⟩ :=
    armTail_rec gpre N A SL φf φc st st' d env e v
      callPC retPC jalImm sp r sret subsret aIn aOperand v8 v9 v18
      out0 mcall hjaltgt hlink hretAl henvValid hjalSite hIH c hpre
  have hretRaw := hret
  obtain ⟨_hG, _htick, _hpc, _ha0, _hra, _hs1, _hsp, _hmi, _hout,
    hframe, _hval, _hstore, _hcode, _hslotRa, _hslotS0, _hslotS1,
    _hslotS2, hmemFrame, _hmemExt⟩ := hretRaw
  have hx8 : c'.σ.regs.get? Register.x8 = some callNode :=
    (hframe Register.x8 (by decide)).trans hgpre8
  have hagree : AgreeP (regionP lo hi) mcall c'.σ.mem := by
    intro a ha
    change lo ≤ a ∧ a < hi at ha
    have hOffLower : ¬ (SL.lo ≤ a ∧ a < sp.toNat - 1088) := by
      rcases hcallRegion.stack_disjoint with hbelow | habove <;> omega
    have hOffArena : ¬ (A.lo ≤ a ∧ a < A.hi) := by
      rcases hcallRegion.arena_disjoint with hbelow | habove <;> omega
    rcases hmemFrame a hOffLower hOffArena with hsub | heq
    · exfalso
      rcases hcallRegion.stack_disjoint with hbelow | habove
      · omega
      · have hspHi : sp.toNat ≤ SL.hi := by omega
        omega
    · exact heq.symm
  have hcallRepr' : ExprRepr c'.σ.mem callNode.toNat (.call f args) :=
    exprRepr_agree_region hagree hcallRegion.nodes hcallRepr
  have hcallRegion' : AstRegionSpec c'.σ.mem SL A sret.toNat callNode.toNat
      (.call f args) lo hi :=
    hcallRegion.transport (fun a hlo hhi => hagree a ⟨hlo, hhi⟩)
  exact ⟨c', hs, gpre, N, A, SL, φf, φc, sp, r, sret, subsret, retPC,
    v8, v9, v18, mcall, hstackBounds, hret, hx8, hcallRepr',
    lo, hi, hcallRegion'⟩

/-- The returned-child carrier exposes the call node's concrete signed C count.
This is derived from the transported `ExprRepr`, not restated as a stage
assumption. -/
theorem ArgsChildReturn.call_count
    {st st' : SpecSt} {d : Nat} {env : Addr}
    {callNode : BitVec 64} {f : Expr} {args : List Expr}
    {e : Expr} {v : Value} {c : Config}
    (h : ArgsChildReturn st st' d env callNode f args e v c) :
    read32 c.σ.mem (callNode.toNat + 24) = some args.length ∧
      args.length < 2 ^ 31 := by
  obtain ⟨_gpre, _N, _A, _SL, _φf, _φc, _sp, _r, _sret, _subsret,
    _retPC, _v8, _v9, _v18, _mcall, _hbounds, _hret, _hx8, hrepr,
    _lo, _hi, _hregion⟩ := h
  exact ExprRepr.call_count hrepr

/-- Entry to the reflected return/copy block.  Its branch polarity is selected
by whether another semantic argument remains. -/
def ArgsCopyReady (es : List Expr) : Config → Prop :=
  match es with
  | [] => fun c => ∃ (sp : BitVec 64) (lds : List (List (BitVec 8))) (m : Mem),
      SegPre argsReturnDoneSeg (argsReturnL sp) lds 0x80003224#64 m c
  | _ :: _ => fun c => ∃ (sp : BitVec 64) (lds : List (List (BitVec 8))) (m : Mem),
      SegPre argsReturnMoreSeg (argsReturnL sp) lds 0x80003224#64 m c

/-- Exit from the reflected return/copy block, retaining its computed register
map and write log for semantic marshalling. -/
def ArgsCopyDone (es : List Expr) : Config → Prop :=
  match es with
  | [] => fun c => ∃ (sp : BitVec 64) (lds : List (List (BitVec 8))) (m : Mem),
      ArgsReturnPost argsReturnDoneSeg sp 0x80003254#64 lds m c
  | _ :: _ => fun c => ∃ (sp : BitVec 64) (lds : List (List (BitVec 8))) (m : Mem),
      ArgsReturnPost argsReturnMoreSeg sp 0x800031dc#64 lds m c

/-- The concrete return/copy/backedge block is fully reflected. -/
theorem argsReturnCopyRun (es : List Expr) :
    Triple (ArgsCopyReady es) (ArgsCopyDone es) := by
  cases es with
  | nil =>
      intro c hc
      obtain ⟨sp, lds, m, hpre⟩ := hc
      obtain ⟨c', hs, hpost⟩ := argsReturnDoneRow sp lds m c hpre
      exact ⟨c', hs, sp, lds, m, hpost⟩
  | cons e es =>
      intro c hc
      obtain ⟨sp, lds, m, hpre⟩ := hc
      obtain ⟨c', hs, hpost⟩ := argsReturnMoreRow sp lds m c hpre
      exact ⟨c', hs, sp, lds, m, hpost⟩

/-- Strict staged decomposition of one argument iteration.

`head` ends before the recursive call. `toCopy` marshals only the child return
into the reflected block. `finish` interprets only the reflected block's
computed state as the next indexed cursor. -/
structure ArgsBodyStages
    (st st' : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
    (v : Value) (esPrefix : List Expr) (vsPrefix : List Value)
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem) : Prop where
  head : Triple
    (EvalArgsPrefixEntryI g N A SL φf φc st d env
      esPrefix (e :: es) vsPrefix dLeft aLeft m0)
    (fun c => ∃ callNode f,
      CallChildJalPre callNode f (esPrefix ++ e :: es) e c st d env)
  toCopy : ∀ callNode f,
    Triple (ArgsChildReturn st st' d env callNode f (esPrefix ++ e :: es) e v)
      (ArgsCopyReady es)
  finish : StoreClosuresBounded st.store →
    ValuesClosuresBounded st.store.closures.size vsPrefix →
    Triple (ArgsCopyDone es)
    (fun c => ∃ (φf' φc' : Addr → Nat),
      PhiExtends φf φf' st'.store.frames.size ∧
      PhiExtends φc φc' st'.store.closures.size ∧
      EvalArgsPrefixEntryI g N A SL φf' φc' st' d env
        (esPrefix ++ [e]) es (vsPrefix ++ [v]) dLeft aLeft m0 c)

/-- Provider for one iteration.  It exposes only strict machine stages, never
the whole iteration Triple. -/
def ArgsBodyStageProvider
    (st : SpecSt) (d : Nat) (env : Addr)
    (e : Expr) (es : List Expr) (st' : SpecSt) (v : Value)
    (hE : EvalE st d env e st' v) : Prop :=
  mEvalE st d env e st' v hE →
  ∀ (esPrefix : List Expr) (vsPrefix : List Value),
    esPrefix.length = vsPrefix.length →
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (m0 : Mem),
    ArgsBodyStages st st' d env e es v esPrefix vsPrefix
      g N A SL φf φc dLeft aLeft m0

/-- Discharge the exact one-iteration oracle from strict stages and the
reflected return block, then resume the actual tail IH. -/
theorem argsConsResid_of_stages
    (st : SpecSt) (d : Nat) (env : Addr)
    (e : Expr) (es : List Expr) (st' st'' : SpecSt)
    (v : Value) (vs : List Value)
    (hE : EvalE st d env e st' v)
    (hArgs : EvalArgs st' d env es st'' vs)
    (hBody : ArgsBodyStageProvider st d env e es st' v hE) :
    ArgsConsResid st d env e es st' st'' v vs hE hArgs := by
  intro hHead hTail esPrefix vsPrefix hlen g N A SL φf φc dLeft aLeft m0
  obtain ⟨hStage, hToCopy, hFinish⟩ :=
    hBody hHead esPrefix vsPrefix hlen g N A SL φf φc dLeft aLeft m0
  intro c hc
  have hBounds := EvalArgsPrefixEntryI.semanticBounds hc
  have hChildToCopy : Triple
      (fun c => ∃ callNode f,
        CallChildJalPre callNode f (esPrefix ++ e :: es) e c st d env)
      (ArgsCopyReady es) := by
    intro c0 hc0
    obtain ⟨callNode, f, hpre⟩ := hc0
    obtain ⟨c1, hs1, hret⟩ :=
      (argsChildReturn_of_jalBundle st st' d env callNode f
        (esPrefix ++ e :: es) e v hHead.forget) c0 hpre
    obtain ⟨c2, hs2, hcopy⟩ := hToCopy callNode f c1 hret
    exact ⟨c2, hs1.trans hs2, hcopy⟩
  have hOne : Triple
      (EvalArgsPrefixEntryI g N A SL φf φc st d env
        esPrefix (e :: es) vsPrefix dLeft aLeft m0)
      (fun c => ∃ (φf' φc' : Addr → Nat),
        PhiExtends φf φf' st'.store.frames.size ∧
        PhiExtends φc φc' st'.store.closures.size ∧
        EvalArgsPrefixEntryI g N A SL φf' φc' st' d env
          (esPrefix ++ [e]) es (vsPrefix ++ [v]) dLeft aLeft m0 c) :=
    Triple.seq hStage <| Triple.seq hChildToCopy <|
      Triple.seq (argsReturnCopyRun es)
        (hFinish hBounds.1 hBounds.2)
  obtain ⟨c1, hs1, φf', φc', hpf, hpc, hc1⟩ := hOne c hc
  have hlen' : (esPrefix ++ [e]).length = (vsPrefix ++ [v]).length := by
    simp [hlen]
  have hrun := hTail (esPrefix ++ [e]) (vsPrefix ++ [v]) hlen'
    g N A SL φf' φc' dLeft aLeft m0
  obtain ⟨c2, hs2, hexit⟩ := hrun c1 hc1
  have hmono := evalE_store_mono hE
  have hexit' := evalArgsExitI_mono hmono.1 hmono.2
    (evalArgsExitI_rebase hpf hpc hexit)
  exact ⟨c2, hs1.trans hs2, by simpa [List.append_assoc] using hexit'⟩

/-! ## Native branch via strict dispatch, body, and join stages

The print/println/assert residuals are all concrete
`Triple (CallEntryI … fv vs) (CallExitI … v sret)` contracts. All three share
the dispatch decode (`callDispatchPC 0x80003254` fv-kind → native arm) ≫ the ABI
marshal (`callNativePC 0x800039e0`) ≫ the **same** indirect `jalr a6` ≫ the
restore ≫ `j callJoinPC 0x800033ec`.  The per-native difference is only the
resolved target and the callee's store/output effect.
-/

/-- Raw result of the finite native dispatch/marshal segment and its indirect
call.  This names the machine facts used by the final ABI reconstruction. -/
structure NativeDispatchReached
    (g : (R : Register) → Option (RegisterType R))
    (sp s0v argc interp sret target : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some target
  ra : c.σ.regs.get? Register.x1 = some (0x800039f8#64 : BitVec 64)
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  regs : GHolds c.σ (evalBlocks nativeDispatchStageSeg
    (SegEvalState.init (nativeDispatchStageL sp s0v argc interp sret) lds)).regs
  mem : c.σ.mem = writeLog m0 (evalBlocks nativeDispatchStageSeg
    (SegEvalState.init (nativeDispatchStageL sp s0v argc interp sret) lds)).log
  frame : ∀ R, AbiPreservedNoise R → R ≠ Register.x23 →
    c.σ.regs.get? R = g R

/-- Finite native-dispatch geometry.  The machine segment and `jalr` are run by
`nativeDispatchRun`; fields contain only entry readbacks, code geometry, and
the reached-state ABI marshal. -/
structure NativeDispatchGeom
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value)
    (dLeft aLeft : Nat) (sp sret : BitVec 64) (m0 : Mem)
    (fentry : Nat) (s7v interp argsBase scratch : BitVec 64)
    (Extra : Config → Prop) : Type where
  s0v : BitVec 64
  lds : List (List (BitVec 8))
  entryPins : ∀ c,
    CallEntryI g N A SL φf φc st d fv vs dLeft aLeft sp sret m0 c →
    GHolds c.σ (nativeDispatchStageL sp s0v
      (BitVec.ofNat 64 vs.length) interp sret)
  facts : ∀ c,
    CallEntryI g N A SL φf φc st d fv vs dLeft aLeft sp sret m0 c →
    ChainFacts c.σ.mem c.σ.mem
      (nativeDispatchStageL sp s0v (BitVec.ofNat 64 vs.length) interp sret)
      lds nativeDispatchStageSeg
  keysOut : KeysOK (keysG (evalBlocks nativeDispatchStageSeg
    (SegEvalState.init
      (nativeDispatchStageL sp s0v (BitVec.ofNat 64 vs.length) interp sret) lds)).regs)
  raOut : KeysAvoidRa (evalBlocks nativeDispatchStageSeg
    (SegEvalState.init
      (nativeDispatchStageL sp s0v (BitVec.ofNat 64 vs.length) interp sret) lds)).regs
  pcEq : evalBlocksPC 0x80003254#64
    (SegEvalState.init
      (nativeDispatchStageL sp s0v (BitVec.ofNat 64 vs.length) interp sret) lds)
      nativeDispatchStageSeg = (0x800039f4#64 : BitVec 64)
  targetPin : ∀ σ,
    GHolds σ (evalBlocks nativeDispatchStageSeg
      (SegEvalState.init
        (nativeDispatchStageL sp s0v (BitVec.ofNat 64 vs.length) interp sret) lds)).regs →
    σ.regs.get? Register.x16 = some (BitVec.ofNat 64 fentry)
  loadedOut : Vsa.Sim.Code.Eval_exprLoaded
    (writeLog m0 (evalBlocks nativeDispatchStageSeg
      (SegEvalState.init
        (nativeDispatchStageL sp s0v (BitVec.ofNat 64 vs.length) interp sret) lds)).log)
  aligned : (BitVec.ofNat 64 fentry : BitVec 64).toNat % 4 = 0
  land : ValuesClosuresBounded st.store.closures.size vs →
    ConsoleStream m0 → ∀ c,
    NativeDispatchReached g sp s0v (BitVec.ofNat 64 vs.length) interp sret
      (BitVec.ofNat 64 fentry) lds m0 c →
    NativeBodyPre g N A SL φf φc st vs fentry
      sp s7v sret interp argsBase scratch m0 c ∧ Extra c

/-- Execute the finite native dispatch segment and reconstruct its exact body
boundary. -/
theorem nativeDispatchRun
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value)
    (dLeft aLeft : Nat) (sp sret : BitVec 64) (m0 : Mem)
    (fentry : Nat) (s7v interp argsBase scratch : BitVec 64)
    (Extra : Config → Prop)
    (G : NativeDispatchGeom g N A SL φf φc st d fv vs dLeft aLeft sp sret
      m0 fentry s7v interp argsBase scratch Extra) :
    Triple
      (CallEntryI g N A SL φf φc st d fv vs dLeft aLeft sp sret m0)
      (fun c => NativeBodyPre g N A SL φf φc st vs fentry
        sp s7v sret interp argsBase scratch m0 c ∧ Extra c) := by
  intro c hc
  obtain ⟨vm, hvm⟩ := hc.1.good.minstret
  have hjal := nativeDispatchJalSeam_of (BitVec.ofNat 64 fentry) sp G.s0v
    (BitVec.ofNat 64 vs.length) interp sret G.lds m0 G.pcEq G.targetPin
    G.loadedOut G.aligned
  obtain ⟨σ2, i2, hs, hi2, hgood2, hpc2, hra2, hmi2, hregs2, hmem2, hframe2⟩ :=
    nativeDispatchStageBridge c.σ c.tick c.steps vm (BitVec.ofNat 64 fentry)
      sp G.s0v (BitVec.ofNat 64 vs.length) interp sret G.lds m0
      hc.1.good hc.1.pc hvm hc.1.mem (G.entryPins c hc) (G.facts c hc) hc.1.tick
      G.keysOut G.raOut hjal
  let c2 : Config := ⟨σ2, i2, c.steps + evalBlocksFuel nativeDispatchStageSeg + 1⟩
  have hconsole0 : ConsoleStream m0 := by
    rw [← hc.1.mem]
    exact hc.console
  refine ⟨c2, hs, G.land hc.valuesBounded hconsole0 c2 ?_⟩
  exact
    { good := hgood2
      tick := hi2
      pc := hpc2
      ra := hra2
      minstret := hmi2
      regs := hregs2
      mem := hmem2
      frame := fun R hR hne =>
        (hframe2 R (by simp [AbiExceptS7, hR.1, hne])).trans (hc.1.frame R hR) }

#print axioms nativeDispatchRun

/-- Exact native-call stages.  `dispatch` is finite readback geometry,
`body` covers only the selected native implementation, and `nativeJoin`
discharges the shared restore/join block. -/
structure NativeCallStages
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value)
    (dLeft aLeft : Nat) (sp sret : BitVec 64) (m0 : Mem)
    (stOut : SpecSt) : Type where
  fentry : Nat
  s7v : BitVec 64
  interp : BitVec 64
  argsBase : BitVec 64
  scratch : BitVec 64
  Extra : Config → Prop
  spGhost : g Register.x2 = some sp
  s7Ghost : g Register.x23 = some s7v
  slotLo : 0x80000000 ≤ sp.toNat + 1016
  slotHi : sp.toNat + 1024 ≤ 0x100000000
  slotHtif : sp.toNat + 1024 ≤ tohostAddr ∨
    tohostAddr + 8 ≤ sp.toNat + 1016
  slotAlign : (sp.toNat + 1016) % 8 = 0
  dispatch : NativeDispatchGeom g N A SL φf φc st d fv vs
    dLeft aLeft sp sret m0 fentry s7v interp argsBase scratch Extra
  body : Triple
    (fun c => NativeBodyPre g N A SL φf φc st vs fentry
      sp s7v sret interp argsBase scratch m0 c ∧ Extra c)
    (NativeBodyPost g N A SL φf φc stOut sp s7v sret m0)

/-- Compose the strict native stages with the machine-proved shared join. -/
theorem nativeCallSpec_of_stages
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value)
    (dLeft aLeft : Nat) (sp sret : BitVec 64) (m0 : Mem) (stOut : SpecSt)
    (hS : NativeCallStages g N A SL φf φc st d fv vs
      dLeft aLeft sp sret m0 stOut) :
    Triple
      (CallEntryI g N A SL φf φc st d fv vs dLeft aLeft sp sret m0)
      (CallExitI g N A SL φf φc st.store.frames.size st.store.closures.size
        stOut .null sret m0) :=
  nativeArmSplice g N A SL φf φc st.store.frames.size st.store.closures.size
    stOut sp hS.s7v sret m0 _ _ hS.spGhost hS.s7Ghost hS.slotLo hS.slotHi
    hS.slotHtif hS.slotAlign
    (nativeDispatchRun g N A SL φf φc st d fv vs dLeft aLeft sp sret m0
      hS.fentry hS.s7v hS.interp hS.argsBase hS.scratch hS.Extra hS.dispatch)
    hS.body

/-- Reduce `NativePrintSpec` to strict native stages at the `print` effect. -/
theorem nativePrintSpec_of_stages
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (sp sret : BitVec 64)
    (m0 : Mem) (vs : List Value)
    (hS : NativeCallStages g N A SL φf φc st d (.native .print) vs
      dLeft aLeft sp sret m0 ⟨st.store, st.out ++ printArgs st.store vs⟩) :
    Triple
      (CallEntryI g N A SL φf φc st d (.native .print) vs
        dLeft aLeft sp sret m0)
      (CallExitI g N A SL φf φc st.store.frames.size st.store.closures.size
        ⟨st.store, st.out ++ printArgs st.store vs⟩ .null sret m0) :=
  nativeCallSpec_of_stages g N A SL φf φc st d (.native .print) vs
    dLeft aLeft sp sret m0 _ hS

/-- **Reduce `NativePrintlnSpec` to the shared span** at the `println` effect
(`out ++ printArgs ++ "\n"`).  The body contract is `print`'s composed with the
trailing `fputc('\n')` HTIF append. -/
theorem nativePrintlnSpec_of_stages
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (sp sret : BitVec 64)
    (m0 : Mem) (vs : List Value)
    (hS : NativeCallStages g N A SL φf φc st d (.native .println) vs
      dLeft aLeft sp sret m0 ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩) :
    Triple
      (CallEntryI g N A SL φf φc st d (.native .println) vs
        dLeft aLeft sp sret m0)
      (CallExitI g N A SL φf φc st.store.frames.size st.store.closures.size
        ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩ .null sret m0) :=
  nativeCallSpec_of_stages g N A SL φf φc st d (.native .println) vs
    dLeft aLeft sp sret m0 _ hS

/-- **Reduce `NativeAssertOkSpec` to the shared span** at the `assert` effect
(spec state UNCHANGED — no store or output change).  The body contract is the
`native_assert` truthy path (`value_truthy` ≫ `value_null`, no append). -/
theorem nativeAssertOkSpec_of_stages
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (vs : List Value) (dLeft aLeft : Nat)
    (sp sret : BitVec 64) (m0 : Mem)
    (hS : NativeCallStages g N A SL φf φc st d (.native .assert) vs
      dLeft aLeft sp sret m0 st) :
    Triple
      (CallEntryI g N A SL φf φc st d (.native .assert) vs
        dLeft aLeft sp sret m0)
      (CallExitI g N A SL φf φc st.store.frames.size st.store.closures.size
        st .null sret m0) :=
  nativeCallSpec_of_stages g N A SL φf φc st d (.native .assert) vs
    dLeft aLeft sp sret m0 st hS

/-! ## Wiring the reducers into the `CallRows` residual providers

Each `CallRows` row takes `hR : ∀ …, <Resid> …`.  Composing the row with the
reducer here yields the row conditional on the collapsed oracle instead of the
composite residual.  These wrappers show the exact substitution (no landed
statement changes). -/

/-- `eval_callPrint_row` supplied by strict native stages. -/
theorem eval_callPrint_row_of_stages
    (hStages : ∀ (st : SpecSt) (d : Nat) (vs : List Value)
        (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (dLeft aLeft : Nat) (sp sret : BitVec 64) (m0 : Mem),
        NativeCallStages g N A SL φf φc st d (.native .print) vs
          dLeft aLeft sp sret m0 ⟨st.store, st.out ++ printArgs st.store vs⟩) :
    ∀ (st : SpecSt) (d : Nat) (vs : List Value),
      mCall st d (Value.native NativeFn.print) vs
        { store := st.store, out := st.out +++ printArgs st.store vs } Value.null
        (Call.print st d vs) :=
  eval_callPrint_row (fun st d vs g N A SL φf φc dLeft aLeft sp sret m0 =>
    nativePrintSpec_of_stages g N A SL φf φc st d dLeft aLeft sp sret m0 vs
      (hStages st d vs g N A SL φf φc dLeft aLeft sp sret m0))

/-- `eval_callPrintln_row` with its indexed residual supplied by the shared span. -/
theorem eval_callPrintln_row_of_stages
    (hStages : ∀ (st : SpecSt) (d : Nat) (vs : List Value)
        (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (dLeft aLeft : Nat) (sp sret : BitVec 64) (m0 : Mem),
        NativeCallStages g N A SL φf φc st d (.native .println) vs
          dLeft aLeft sp sret m0 ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩) :
    ∀ (st : SpecSt) (d : Nat) (vs : List Value),
      mCall st d (Value.native NativeFn.println) vs
        { store := st.store, out := st.out +++ printArgs st.store vs +++ "\n" } Value.null
        (Call.println st d vs) :=
  eval_callPrintln_row (fun st d vs g N A SL φf φc dLeft aLeft sp sret m0 =>
    nativePrintlnSpec_of_stages g N A SL φf φc st d dLeft aLeft sp sret m0 vs
      (hStages st d vs g N A SL φf φc dLeft aLeft sp sret m0))

/-- `eval_callAssertOk_row` with its indexed residual supplied by the shared span. -/
theorem eval_callAssertOk_row_of_stages
    (hStages : ∀ (st : SpecSt) (d : Nat) (vs : List Value)
        (g : (R : Register) → Option (RegisterType R))
        (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
        (dLeft aLeft : Nat) (sp sret : BitVec 64) (m0 : Mem),
        NativeCallStages g N A SL φf φc st d (.native .assert) vs
          dLeft aLeft sp sret m0 st) :
    ∀ (st : SpecSt) (d : Nat) (vs : List Value) (v m : Value)
      (hvs : vs = [v] ∨ vs = [v, m]) (htruthy : v.truthy = true),
      mCall st d (Value.native NativeFn.assert) vs st Value.null
        (Call.assertOk st d vs v m hvs htruthy) :=
  eval_callAssertOk_row
    (fun st d vs _v _m _hvs _htruthy g N A SL φf φc
        dLeft aLeft sp sret m0 =>
      nativeAssertOkSpec_of_stages g N A SL φf φc st d vs dLeft aLeft sp sret m0
        (hStages st d vs g N A SL φf φc dLeft aLeft sp sret m0))

/-! ## Residual 5 — the full `EX_CALL` arm as strict stages

The old `CallArmGeom.hArm` repeated the entire arm Triple.  The predicates below
cut it at the callee return, argument-loop exit, call-dispatch exit, and shared
epilogue entry.  The recursive motives run between those cuts.  Only the local
ABI marshalling cuts remain as premises.
-/

/-- Argument-loop entry after the callee value has returned. -/
def CallArgsReady
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : SpecSt) (d : Nat) (env : Addr) (args : List Expr)
    (dLeft aLeft : Nat) (m0 : Mem) : Config → Prop :=
  fun c => ∃ (φf' φc' : Addr → Nat) (mArgs : Mem),
    PhiExtends φf φf' st.store.frames.size ∧
    PhiExtends φc φc' st.store.closures.size ∧
    EvalArgsPrefixEntryI g N A SL φf' φc' st' d env
      [] args [] dLeft aLeft mArgs c

/-- Argument-loop exit with the same dynamically selected maps and baseline. -/
def CallArgsDone
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : SpecSt) (vs : List Value) : Config → Prop :=
  fun c => ∃ (φf' φc' : Addr → Nat) (mArgs : Mem),
    PhiExtends φf φf' st.store.frames.size ∧
    PhiExtends φc φc' st.store.closures.size ∧
    EvalArgsExitI g N A SL φf' φc'
      st'.store.frames.size st'.store.closures.size st'' vs mArgs c

theorem callArgsRun
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : SpecSt) (d : Nat) (env : Addr) (args : List Expr)
    (vs : List Value) (dLeft aLeft : Nat) (m0 : Mem)
    {hArgs : EvalArgs st' d env args st'' vs}
    (hIH : mEvalArgs st' d env args st'' vs hArgs) :
    Triple
      (CallArgsReady g N A SL φf φc st st' d env args dLeft aLeft m0)
      (CallArgsDone g N A SL φf φc st st' st'' vs) := by
  intro c hc
  obtain ⟨φf', φc', mArgs, hpf, hpc, hentry⟩ := hc
  obtain ⟨c', hs, hexit⟩ :=
    hIH [] [] rfl g N A SL φf' φc' dLeft aLeft mArgs c hentry
  exact ⟨c', hs, φf', φc', mArgs, hpf, hpc, by simpa using hexit⟩

/-- Dispatch entry selected after the argument loop. -/
def CallDispatchReady
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st'' : SpecSt) (d : Nat) (fv : Value) (vs : List Value)
    (sret : BitVec 64) : Config → Prop :=
  fun c => ∃ (φf' φc' : Addr → Nat) (dLeft aLeft : Nat)
      (spCall : BitVec 64) (mCall : Mem),
    PhiExtends φf φf' st.store.frames.size ∧
    PhiExtends φc φc' st.store.closures.size ∧
    EntryImage callDispatchPC g mCall ∧
    CallEntryI g N A SL φf' φc' st'' d fv vs
      dLeft aLeft spCall sret mCall c

/-- Dispatch exit, retaining the selected call boundary for the next marshal. -/
def CallDispatchDone
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st'' st''' : SpecSt) (v : Value) (sret : BitVec 64) : Config → Prop :=
  fun c => ∃ (φf' φc' : Addr → Nat) (dLeft aLeft : Nat)
      (spCall : BitVec 64) (mCall : Mem),
    PhiExtends φf φf' st.store.frames.size ∧
    PhiExtends φc φc' st.store.closures.size ∧
    CallExitI g N A SL φf' φc'
      st''.store.frames.size st''.store.closures.size st''' v sret mCall c

theorem callDispatchRun
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st'' st''' : SpecSt) (d : Nat) (fv : Value) (vs : List Value)
    (v : Value) (sret : BitVec 64)
    {hCall : Call st'' d fv vs st''' v}
    (hIH : mCall st'' d fv vs st''' v hCall) :
    Triple
      (CallDispatchReady g N A SL φf φc st st'' d fv vs sret)
      (CallDispatchDone g N A SL φf φc st st'' st''' v sret) := by
  intro c hc
  obtain ⟨φf', φc', dLeft, aLeft, spCall, mCall, hpf, hpc, hImg, hentry⟩ := hc
  obtain ⟨c', hs, hexit⟩ :=
    hIH g N A SL φf' φc' dLeft aLeft spCall sret mCall hImg c hentry
  exact ⟨c', hs, φf', φc', dLeft, aLeft, spCall, mCall,
    hpf, hpc, hexit⟩

/-- Exact shared-epilogue entry, including the maps selected by recursive
children and the saved-register words consumed by `blockD_v_phic`. -/
def CallArmHandoff
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st''' : SpecSt) (v : Value) (sp r sret : BitVec 64) (m0 : Mem) :
    Config → Prop :=
  fun c => ∃ (φf' φc' : Addr → Nat) (v8 v9 v18 : BitVec 64)
      (out0 : Array String) (mpre : Mem),
    PhiExtends φf φf' st.store.frames.size ∧
    PhiExtends φc φc' st.store.closures.size ∧
    st.store.frames.size ≤ st'''.store.frames.size ∧
    st.store.closures.size ≤ st'''.store.closures.size ∧
    String.join out0.toList = st'''.out ∧
    PreEpilogueV g N A SL φf' φc' st''' v
      sp r sret v8 v9 v18 out0 m0 mpre c ∧
    -- the epilogue-entry facts at the SAME selected pair: presence, the complete
    -- result words, and `st'''.store` survival across the stack region.
    EpilogueEntryFacts N A SL φf' φc' st''' sret m0 mpre

/-- The shared epilogue lands the COHERENT return at the pair the call arm
selected (`armReturn_of_facts` = `blockD_v_return` from the handoff's facts). -/
theorem callArmEpilogueReturn
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st''' : SpecSt) (v : Value) (sp r sret : BitVec 64) (m0 : Mem) :
    Triple
      (CallArmHandoff g N A SL φf φc st st''' v sp r sret m0)
      (EvalReturn g N A SL φf φc st.store.frames.size st.store.closures.size
        st''' v sp r sret m0 (fun _ _ _ => True)) := by
  intro c hc
  obtain ⟨φf', φc', v8, v9, v18, out0, mpre,
    hpf, hpc, _hfr, _hcl, _hout, hpre, hF⟩ := hc
  exact armReturn_of_facts g N A SL φf φc φf' φc'
    st.store.frames.size st.store.closures.size st''' v
    sp r sret v8 v9 v18 out0 m0 hpf hpc c ⟨mpre, hpre, hF⟩

theorem callArmEpilogueRun
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st''' : SpecSt) (v : Value) (sp r sret : BitVec 64) (m0 : Mem) :
    Triple
      (CallArmHandoff g N A SL φf φc st st''' v sp r sret m0)
      (EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
        st''' v sp r sret m0) :=
  (callArmEpilogueReturn g N A SL φf φc st st''' v sp r sret m0).conseq
    (fun _ h => h) (fun _ h => h.exit.1)

/-- Four strict residual cuts for the call arm.  No field restates the whole
`EvalEntry → EvalExit` goal. -/
structure CallArmStages
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' st''' : SpecSt) (d : Nat) (env : Addr)
    (f : Expr) (args : List Expr) (fv : Value) (vs : List Value) (v : Value)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) : Prop where
  callee : Triple
    (EvalEntry g N A SL φf φc st d env (.call f args)
      sp r sret aEnv aExpr m0)
    (fun c => CallChildJalPre aExpr f args f c st d env)
  calleeToArgs : Triple (ArgsChildReturn st st' d env aExpr f args f fv)
    (CallArgsReady g N A SL φf φc st st' d env args
      (Vsa.While.maxCallDepth - d) (Vsa.While.maxCallDepth - d) m0)
  argsToCall : Triple
    (CallArgsDone g N A SL φf φc st st' st'' vs)
    (CallDispatchReady g N A SL φf φc st st'' d fv vs sret)
  callToEpilogue : Triple
    (CallDispatchDone g N A SL φf φc st st'' st''' v sret)
    (CallArmHandoff g N A SL φf φc st st''' v sp r sret m0)

/-- Full arm composition to the COHERENT return.  The callee, argument-list, and
call motives are executed at their real indexed boundaries; the epilogue lands
`EvalReturn` at the pair the handoff selected. -/
theorem callReturn_of_stages
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' st''' : SpecSt) (d : Nat) (env : Addr)
    (f : Expr) (args : List Expr) (fv : Value) (vs : List Value) (v : Value)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    {hArgs : EvalArgs st' d env args st'' vs}
    {hCall : Call st'' d fv vs st''' v}
    (hCallee : EvalIH st d env f st' fv)
    (hArgsIH : mEvalArgs st' d env args st'' vs hArgs)
    (hCallIH : mCall st'' d fv vs st''' v hCall)
    (hS : CallArmStages g N A SL φf φc st st' st'' st''' d env
      f args fv vs v sp r sret aEnv aExpr m0) :
    Triple
      (EvalEntry g N A SL φf φc st d env (.call f args) sp r sret aEnv aExpr m0)
      (EvalReturn g N A SL φf φc st.store.frames.size st.store.closures.size
        st''' v sp r sret m0 (fun _ _ _ => True)) :=
  Triple.seq hS.callee <| Triple.seq
    (argsChildReturn_of_jalBundle st st' d env aExpr f args f fv hCallee) <| Triple.seq
    hS.calleeToArgs <| Triple.seq
    (callArgsRun g N A SL φf φc st st' st'' d env args vs
      (Vsa.While.maxCallDepth - d) (Vsa.While.maxCallDepth - d) m0 hArgsIH) <|
    Triple.seq hS.argsToCall <| Triple.seq
    (callDispatchRun g N A SL φf φc st st'' st''' d fv vs v sret hCallIH) <|
    Triple.seq hS.callToEpilogue
      (callArmEpilogueReturn g N A SL φf φc st st''' v sp r sret m0)

/-- The plain-exit projection of the same composition. -/
theorem callArmSpec_of_stages
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' st''' : SpecSt) (d : Nat) (env : Addr)
    (f : Expr) (args : List Expr) (fv : Value) (vs : List Value) (v : Value)
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem)
    {hArgs : EvalArgs st' d env args st'' vs}
    {hCall : Call st'' d fv vs st''' v}
    (hArgsIH : mEvalArgs st' d env args st'' vs hArgs)
    (hCallIH : mCall st'' d fv vs st''' v hCall)
    (hS : CallArmStages g N A SL φf φc st st' st'' st''' d env
      f args fv vs v sp r sret aEnv aExpr m0) :
    CallArmSpec g N A SL φf φc st st' st'' st''' d env
      f args fv vs v sp r sret aEnv aExpr m0 := by
  intro hCallee _hArgs _hCall
  exact (callReturn_of_stages g N A SL φf φc st st' st'' st''' d env f args fv vs v
    sp r sret aEnv aExpr m0 hCallee hArgsIH hCallIH hS).conseq
    (fun _ h => h) (fun _ h => h.exit.1)

/-- Residual provider consumed by `eval_call_row`. -/
theorem callResid_of_stages
    (st st' st'' st''' : SpecSt) (d : Nat) (env : Addr)
    (f : Expr) (args : List Expr) (fv : Value) (vs : List Value) (v : Value)
    (hEf : EvalE st d env f st' fv)
    (hBound : args.length ≤ maxArgs)
    (hArgs : EvalArgs st' d env args st'' vs)
    (hCall : Call st'' d fv vs st''' v)
    (hStages : ∀ (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
      CallArmStages g N A SL φf φc st st' st'' st''' d env
        f args fv vs v sp r sret aEnv aExpr m0) :
    CallResid st st' st'' st''' d env f args fv vs v hEf hBound hArgs hCall := by
  intro hCallee hArgsIH hCallIH g N A SL φf φc sp r sret aEnv aExpr m0
  exact callReturn_of_stages g N A SL φf φc st st' st'' st''' d env
    f args fv vs v sp r sret aEnv aExpr m0 hCallee.forget hArgsIH hCallIH
    (hStages g N A SL φf φc sp r sret aEnv aExpr m0)

#print axioms argsChildReturn_of_jalBundle
#print axioms argsReturnCopyRun
#print axioms argsConsResid_of_stages
#print axioms callArgsRun
#print axioms callDispatchRun
#print axioms callArmEpilogueReturn
#print axioms callArmEpilogueRun
#print axioms callReturn_of_stages
#print axioms callArmSpec_of_stages
#print axioms callResid_of_stages
#print axioms nativeCallSpec_of_stages
#print axioms nativePrintSpec_of_stages
#print axioms nativePrintlnSpec_of_stages
#print axioms nativeAssertOkSpec_of_stages
#print axioms eval_callPrint_row_of_stages
#print axioms eval_callPrintln_row_of_stages
#print axioms eval_callAssertOk_row_of_stages

end Vsa.Sim.Rows
