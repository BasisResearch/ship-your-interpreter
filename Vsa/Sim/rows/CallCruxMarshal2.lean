import Vsa.Sim.rows.CallCruxMarshal
import Vsa.Sim.rows.CallClosureSplice
import Vsa.Sim.EnvCallBridge

/-!
# `CallCruxMarshal2` — the env_define fold splice (wave 43, lane cruxdefine)

The per-param leg of the `hCallClosure` params-fold: marshal the `env_define`
contract post (`PostDef` in `callParamFoldSeam_of`, the
`env_define_update_post`-shaped canonical interface — its `FrameRepr` IS the
`Store.define` result) into `CallParamFoldInv (k+1)`'s `store` field via
`foldStore_succ`, and re-assemble the WHOLE `(k+1)` carrier through the
back-edge span.

## The pieces (each factored ONCE, CLAUDE.md law 3)

* §1 — the `Store.define` getElem algebra (`defineFrame`,
  `define_frames_getElem_self/_ne`, `define_frames_size`): what a supplier
  needs to turn the contract post's per-frame `FrameRepr` into
  `StoreDefineAdvance`'s fields.  `StoreDefineAdvance` (`EnvCallBridge`) is the
  landed whole-store define-step carrier; nobody could DISCHARGE its fields
  before because its statements index the POST store (`(store.define …).frames[fa]`)
  while the honest readbacks are PRE-store-indexed — this algebra is the bridge.
* §2 — `storeDefineAdvance_of` (the named assembler: PRE-store-indexed
  readbacks → `StoreDefineAdvance`) and `foldStoreAdvance_toStoreRepr`
  (`StoreDefineAdvance` at `foldStore … k` → `StoreRepr (foldStore … (k+1))`,
  via `foldStore_succ` — the fold carrier's `store`-field advance).
* §3 — `FoldDefineReturn`: the NAMED-field pin bundle at the env_define RETURN
  config (`0x80003314`), everything the back-edge re-assembly consumes.  The
  back-edge is re-run with the RICHER pin list `callClosureFoldBackL5`
  (x2/x8/x19/x21/x22 — the wave-40 row's two-pin `L` dropped
  cursor/frameReg/closReg, which `CallParamFoldInv (k+1)` needs) in
  `segToTripleOut` form (`OutRepr` carry — the wave-42 brick).
* §4 — `foldDefineReturn_step`: `Triple (FoldDefineReturn … k) (carrier (k+1))`
  — the machine back-edge run + the FULL carrier re-assembly.
* §5 — `callParamFoldSeamStep`: `callParamFoldSeam_of` instantiated — ONE fold
  seam from `(hStage, hDefine, hPins)`.  This closes the per-param leg: the
  `hFoldSeam` obligation of `callClosureEntrySplice` reduces per `k` to the
  staging bridge, the env_define contract, and the pin readback.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no heartbeat raise.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While
open Vsa.Alloc

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

set_option linter.unusedVariables false

/-! ## §1. The `Store.define` getElem algebra -/

/-- **The frame-level body of `Store.define`** — the mutation `define` applies
to the ONE touched frame.  `env_define_update_post`'s `FrameRepr` is stated at
exactly this frame (`{ f with vars := if … }`), so naming it lets the contract
post and the store algebra meet definitionally. -/
def defineFrame (f : Vsa.While.Frame) (x : String) (v : Value) : Vsa.While.Frame :=
  { f with vars :=
      if f.vars.any (·.1 == x) then
        f.vars.map fun p => if p.1 == x then (x, v) else p
      else
        f.vars ++ [(x, v)] }

/-- `define` keeps the frame count (getElem-bound transport form). -/
theorem define_frames_size (s : Store) (a : Addr) (x : String) (v : Value) :
    (s.define a x v).frames.size = s.frames.size :=
  Array.size_modify

/-- `define` leaves the closures array untouched — definitionally. -/
theorem define_closures_eq (s : Store) (a : Addr) (x : String) (v : Value) :
    (s.define a x v).closures = s.closures := rfl

/-- The touched frame of `s.define a x v` IS `defineFrame` of the pre frame. -/
theorem define_frames_getElem_self (s : Store) (a : Addr) (x : String)
    (v : Value) (h : a < (s.define a x v).frames.size) :
    (s.define a x v).frames[a]
      = defineFrame (s.frames[a]'(define_frames_size s a x v ▸ h)) x v := by
  show (s.frames.modify a fun f => defineFrame f x v)[a] = _
  rw [Array.getElem_modify]
  rw [if_pos rfl]

/-- Every OTHER frame of `s.define a x v` is the pre frame unchanged. -/
theorem define_frames_getElem_ne (s : Store) (a : Addr) (x : String)
    (v : Value) (b : Addr) (h : b < (s.define a x v).frames.size)
    (hne : b ≠ a) :
    (s.define a x v).frames[b]
      = s.frames[b]'(define_frames_size s a x v ▸ h) := by
  show (s.frames.modify a fun f => defineFrame f x v)[b] = _
  rw [Array.getElem_modify]
  rw [if_neg (fun heq => hne heq.symm)]

#print axioms define_frames_getElem_self
#print axioms define_frames_getElem_ne

/-! ## §2. The `StoreDefineAdvance` assembler + the `foldStore` succ-step -/

/-- **`storeDefineAdvance_of`** — assemble `StoreDefineAdvance` from
PRE-store-indexed readbacks: the mutated frame's `FrameRepr` (the env_define
contract post, at `defineFrame` of the pre frame — the shapes meet by §1), the
other frames' survival, the closures' survival, and ANY pre `StoreRepr` of the
same store (its injectivity/arena fields are memory-independent, so the entry
carrier's `store` field supplies them at a different memory).  This is the
named bridge that makes `StoreDefineAdvance`'s POST-store-indexed fields
dischargeable. -/
theorem storeDefineAdvance_of
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat}
    {store : Store} {a : Addr} {x : String} {v : Value} {m mPre : Mem}
    (ha : a < store.frames.size)
    (hpre : StoreRepr mPre N A φf φc store)
    (hmut : FrameRepr m N φf φc (φf a) (defineFrame (store.frames[a]'ha) x v))
    (hothers : ∀ fa, (h : fa < store.frames.size) → fa ≠ a →
      FrameRepr m N φf φc (φf fa) (store.frames[fa]'h))
    (hclos : ∀ ca, (h : ca < store.closures.size) →
      ClosureRepr m φf (φc ca) (store.closures[ca]'h)) :
    StoreDefineAdvance N A φf φc store a x v m where
  mutated h := by
    rw [define_frames_getElem_self store a x v h]
    exact hmut
  others fa h hne := by
    rw [define_frames_getElem_ne store a x v fa h hne]
    exact hothers fa (define_frames_size store a x v ▸ h) hne
  closures ca h := hclos ca h
  φf_inj p q hp hq := hpre.φf_inj p q
    (define_frames_size store a x v ▸ hp) (define_frames_size store a x v ▸ hq)
  φc_inj p q hp hq := hpre.φc_inj p q hp hq
  frames_arena fa h := hpre.frames_arena fa (define_frames_size store a x v ▸ h)
  closures_arena ca h := hpre.closures_arena ca h

#print axioms storeDefineAdvance_of

/-- **`foldStoreAdvance_toStoreRepr`** — the fold carrier's `store`-field
advance: a `StoreDefineAdvance` at the `k`-fold store, frame `frame`, and the
`k`-th binding IS the `StoreRepr` of the `(k+1)`-fold store (`foldStore_succ`).
This is the marshalling `CallParamFoldInv (k+1).store` consumes. -/
theorem foldStoreAdvance_toStoreRepr
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat}
    {store' : Store} {cd : ClosureData} {vs : List Value}
    {frame : Addr} {k : Nat} {m : Mem}
    (hk : k < (cd.params.zip vs).length)
    (hAdv : StoreDefineAdvance N A φf φc (foldStore store' cd vs frame k) frame
      ((cd.params.zip vs)[k]'hk).1 ((cd.params.zip vs)[k]'hk).2 m) :
    StoreRepr m N A φf φc (foldStore store' cd vs frame (k + 1)) := by
  rw [foldStore_succ store' cd vs frame k hk]
  exact hAdv.toStoreRepr

#print axioms foldStoreAdvance_toStoreRepr

/-! ## §3. The env_define-return pin bundle (named-field, CLAUDE.md R6)

The back-edge span needs the RICHER pin list: `CallParamFoldInv (k+1)` reads
back `cursor`/`frameReg`/`closReg` (x8/x19/x21), which the wave-40 two-pin
`callClosureFoldBackL` dropped.  The span writes only `x15`, so the extra pins
pass through `GHolds` untouched. -/

/-- The five-pin back-edge list: sp, the (staging-bumped) cursor, the frame
pointer, the closure record pointer, and the fold bound. -/
def callClosureFoldBackL5 (sp cur fp clp s6v : BitVec 64) : GRegs :=
  [(2, sp), (8, cur), (19, fp), (21, clp), (22, s6v)]

/-- `8·(k+1) = 8·k + 8` over `BitVec 64` — the index-bump arithmetic the
`ld a5,0(sp) ; addi a5,a5,8` readback meets. -/
theorem mul8_ofNat_succ (k : Nat) :
    (8#64 : BitVec 64) * BitVec.ofNat 64 (k + 1)
      = 8#64 * BitVec.ofNat 64 k + 8#64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `24·(k+1) = 24·k + 24` over `BitVec 64` — the cursor-bump arithmetic
(`addi s0,s0,24` at `0x80003304`) a `FoldDefineReturn` supplier meets. -/
theorem mul24_ofNat_succ (k : Nat) :
    (24#64 : BitVec 64) * BitVec.ofNat 64 (k + 1)
      = 24#64 * BitVec.ofNat 64 k + 24#64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- **`FoldDefineReturn`** — the pin bundle at the `env_define` RETURN config
(link PC `0x80003314`), one fold iteration's worth of readback: everything the
back-edge re-assembly (§4) consumes to land `CallParamFoldInv (k+1)`.  A
supplier reads these off the staging bridge's ABI frame
(`callClosureFoldStageBridge`, `AbiExceptS0` + the exposed bumped cursor) and
the env_define contract post (`env_define_update_post` shape: ABI-preserved
callee-saveds, sp restored, the mutated frame's `FrameRepr` → `advance` via
`storeDefineAdvance_of`).  The `chain` field carries the spilled-index
readback (`0(sp)`, written by the staging at `0x80003300`, surviving
`env_define` — the supplier owns the callee footprint) together with the
`ChainFacts` of the back-edge at that load, ∃-bound as ONE pair (the
`structure : Prop` data-field gotcha). -/
structure FoldDefineReturn
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf' φc : Addr → Nat)
    (st : SpecSt) (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (sp fp clp : BitVec 64) (m0 : Mem) (k : Nat)
    (hk : k < (cd.params.zip vs).length) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (0x80003314#64 : BitVec 64)
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  spReg : c.σ.regs.get? Register.x2 = some sp
  /-- `s0` — already bumped by the staging span (`addi s0,s0,24`), preserved
  by `env_define` (callee-saved): the `(k+1)` cursor. -/
  cursor : c.σ.regs.get? Register.x8
    = some (sp + 240#64 + 24#64 * BitVec.ofNat 64 (k + 1))
  /-- `s6` — the fold bound `8·n`, untouched across the iteration. -/
  bound : c.σ.regs.get? Register.x22
    = some (8#64 * BitVec.ofNat 64 (cd.params.zip vs).length)
  frameReg : c.σ.regs.get? Register.x19 = some fp
  closReg : c.σ.regs.get? Register.x21 = some clp
  /-- The spilled byte-index readback + the back-edge `ChainFacts` at it:
  `ib` = the 8 bytes at `0(sp)` (the staging spill, surviving the callee),
  assembling to `8·k`; the facts bundle carries the `ld` pin and the
  `bne`-TAKEN guard (`8·n ≠ 8·(k+1)`, from the supplier's `k+1 < n` bound). -/
  spill : ∃ ib : List (BitVec 8),
    bytesVal MKind.ld ib = 8#64 * BitVec.ofNat 64 k ∧
    ChainFacts c.σ.mem c.σ.mem
      (callClosureFoldBackL5 sp (sp + 240#64 + 24#64 * BitVec.ofNat 64 (k + 1))
        fp clp (8#64 * BitVec.ofNat 64 (cd.params.zip vs).length))
      [ib] callClosureFoldBackLoopSeg
  /-- The store-repr define-step (§2): the `k`-th binding landed in machine
  memory — assembled by `storeDefineAdvance_of` from the contract post's
  `FrameRepr` + the entry carrier's `StoreRepr`. -/
  advance : StoreDefineAdvance N A φf' φc (foldStore store' cd vs frame k) frame
    ((cd.params.zip vs)[k]'hk).1 ((cd.params.zip vs)[k]'hk).2 c.σ.mem
  out : OutRepr c.σ st
  memFrame : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    c.σ.mem[a]? = m0[a]?

/-! ## §4. The back-edge re-assembly: `FoldDefineReturn → CallParamFoldInv (k+1)` -/

/-- **`foldDefineReturn_step`** — run the back-edge span (`ld a5,0(sp) ;
addi a5,a5,8 ▷ bne s6,a5` TAKEN → `callParamFoldPC`) from the return pin
bundle and re-assemble the FULL `(k+1)` fold carrier: register pins off the
exit `GHolds` (pass-throughs by `rfl`, the bumped index via the readback peel
+ `mul8_ofNat_succ`), the `store` field via `foldStoreAdvance_toStoreRepr`,
`OutRepr` via the `segToTripleOut` sailOutput carry, and the memory frame
(the span is memory-pure). -/
theorem foldDefineReturn_step
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf' φc : Addr → Nat)
    (st : SpecSt) (store' : Store) (cd : ClosureData) (vs : List Value)
    (frame : Addr) (sp fp clp : BitVec 64) (m0 : Mem) (k : Nat)
    (hk : k < (cd.params.zip vs).length) :
    Triple
      (fun c => FoldDefineReturn N A SL φf' φc st store' cd vs frame sp fp clp
        m0 k hk c)
      (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0
        (k + 1)) := by
  intro c hp
  obtain ⟨ib, hib, hfacts⟩ := hp.spill
  have hwf : ChainOK 0x80003314#64
      (keysG (callClosureFoldBackL5 sp
        (sp + 240#64 + 24#64 * BitVec.ofNat 64 (k + 1)) fp clp
        (8#64 * BitVec.ofNat 64 (cd.params.zip vs).length)))
      callClosureFoldBackLoopSeg := by
    show ChainOK 0x80003314#64 [2, 8, 19, 21, 22] callClosureFoldBackLoopSeg
    decide
  have hkeys : KeysOK (keysG (callClosureFoldBackL5 sp
      (sp + 240#64 + 24#64 * BitVec.ofNat 64 (k + 1)) fp clp
      (8#64 * BitVec.ofNat 64 (cd.params.zip vs).length))) := by
    show KeysOK [2, 8, 19, 21, 22]; decide
  have hGH : GHolds c.σ (callClosureFoldBackL5 sp
      (sp + 240#64 + 24#64 * BitVec.ofNat 64 (k + 1)) fp clp
      (8#64 * BitVec.ofNat 64 (cd.params.zip vs).length)) :=
    ⟨hp.spReg, hp.cursor, hp.frameReg, hp.closReg, hp.bound, trivial⟩
  have hpost : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.mem = writeLog c.σ.mem (evalBlocks callClosureFoldBackLoopSeg
        (SegEvalState.init (callClosureFoldBackL5 sp
          (sp + 240#64 + 24#64 * BitVec.ofNat 64 (k + 1)) fp clp
          (8#64 * BitVec.ofNat 64 (cd.params.zip vs).length)) [ib])).log →
      σ'.sailOutput = c.σ.sailOutput →
      σ'.regs.get? Register.PC = some (evalBlocksPC 0x80003314#64
        (SegEvalState.init (callClosureFoldBackL5 sp
          (sp + 240#64 + 24#64 * BitVec.ofNat 64 (k + 1)) fp clp
          (8#64 * BitVec.ofNat 64 (cd.params.zip vs).length)) [ib])
        callClosureFoldBackLoopSeg) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      GHolds σ' (evalBlocks callClosureFoldBackLoopSeg
        (SegEvalState.init (callClosureFoldBackL5 sp
          (sp + 240#64 + 24#64 * BitVec.ofNat 64 (k + 1)) fp clp
          (8#64 * BitVec.ofNat 64 (cd.params.zip vs).length)) [ib])).regs →
      callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0
        (k + 1) ⟨σ', i', u'⟩ := by
    intro σ' i' u' hG' hi' hmem' hout hpc' hmi' hregs
    have hmm : σ'.mem = c.σ.mem := by
      -- memory-pure span: log = [] ⇒ writeLog m [] = m
      rw [hmem']; rfl
    show CallParamFoldInv N A SL φf' φc st store' cd vs frame sp fp clp m0
      (k + 1) ⟨σ', i', u'⟩
    refine { good := hG', tick := hi', pc := ?_, spReg := ?_, cursor := ?_,
             idx := ?_, bound := ?_, frameReg := ?_, closReg := ?_,
             minstret := hmi', store := ?_, out := ?_, memFrame := ?_ }
    · rw [hpc']; rfl
    · rw [← gprGet_x2]; exact gholds_reg hregs (by rfl)
    · rw [← gprGet_x8]; exact gholds_reg hregs (by rfl)
    · -- the bumped index: readback `bytesVal ib + sext 8`, then `hib` +
      -- `mul8_ofNat_succ`.
      rw [← gprGet_x15]
      refine gholds_reg hregs ?_
      have hr : lookupG 15 (evalBlocks callClosureFoldBackLoopSeg
          (SegEvalState.init (callClosureFoldBackL5 sp
            (sp + 240#64 + 24#64 * BitVec.ofNat 64 (k + 1)) fp clp
            (8#64 * BitVec.ofNat 64 (cd.params.zip vs).length)) [ib])).regs
          = some (bytesVal MKind.ld ib + sign_extend (m := 64) (0x008#12)) := by
        rfl
      rw [hr, hib]
      have h8 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
        decide
      rw [h8, mul8_ofNat_succ]
    · rw [← gprGet_x22]; exact gholds_reg hregs (by rfl)
    · rw [← gprGet_x19]; exact gholds_reg hregs (by rfl)
    · rw [← gprGet_x21]; exact gholds_reg hregs (by rfl)
    · show StoreRepr σ'.mem N A φf' φc (foldStore store' cd vs frame (k + 1))
      rw [hmm]
      exact foldStoreAdvance_toStoreRepr hk hp.advance
    · exact outRepr_transport hout hp.out
    · intro a h1 h2
      show σ'.mem[a]? = m0[a]?
      rw [hmm]
      exact hp.memFrame a h1 h2
  exact (segToTripleOut callClosureFoldBackLoopSeg
      (callClosureFoldBackL5 sp
        (sp + 240#64 + 24#64 * BitVec.ofNat 64 (k + 1)) fp clp
        (8#64 * BitVec.ofNat 64 (cd.params.zip vs).length)) [ib]
      0x80003314#64 c.σ.mem c.σ.sailOutput
      (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0
        (k + 1)) hwf hpost) c
    ⟨⟨hp.good, rfl, hp.pc, hp.minstret, hGH, hkeys, hfacts, hp.tick⟩, rfl⟩

#print axioms foldDefineReturn_step

/-! ## §5. The per-param seam closed -/

/-- **`callParamFoldSeamStep`** — `callParamFoldSeam_of` instantiated: ONE
fold-seam `Triple (carrier k) (carrier (k+1))` from the three named pieces —
the staging hop (`hStage`, the `callClosureFoldStageBridge` marshalling into
the env_define pre), the env_define contract (`hDefine`,
`TermCallees.envDefine`/`envDefContract`), and the return-pin readback
(`hPins`, §3).  The back-edge + carrier re-assembly (`hBack`) is DISCHARGED
here (§4) — the per-param leg of `hFoldSeam` closes to `(hStage, hDefine,
hPins)`. -/
theorem callParamFoldSeamStep
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf' φc : Addr → Nat}
    {st : SpecSt} {store' : Store} {cd : ClosureData} {vs : List Value}
    {frame : Addr} {sp fp clp : BitVec 64} {m0 : Mem} {k : Nat}
    (hk : k < (cd.params.zip vs).length)
    {PreDef PostDef : Config → Prop}
    (hStage : Triple
      (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0 k)
      PreDef)
    (hDefine : Triple PreDef PostDef)
    (hPins : ∀ c, PostDef c →
      FoldDefineReturn N A SL φf' φc st store' cd vs frame sp fp clp m0 k hk c) :
    Triple
      (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0 k)
      (callParamFoldCarrier N A SL φf' φc st store' cd vs frame sp fp clp m0
        (k + 1)) :=
  callParamFoldSeam_of hStage hDefine
    (fun c hc =>
      foldDefineReturn_step N A SL φf' φc st store' cd vs frame sp fp clp m0
        k hk c (hPins c hc))

#print axioms callParamFoldSeamStep

end Vsa.Sim
