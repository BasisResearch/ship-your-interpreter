import Vsa.Sim.HelperCallEnvNew
import Vsa.Sim.EnvNewSuccessSuffix
import Vsa.Sim.BridgeSegFull
import Vsa.Sim.BridgeSegFramed
import Vsa.Sim.rows.CallClosureEnvNewMarshal
import Vsa.Sim.RuntimeOwnershipTransport
import Vsa.Sim.RuntimeOwnershipAllocation
import Vsa.Sim.AllocOff
import Vsa.Sim.AllocRuns
import Vsa.Sim.StoreInvariant
import Vsa.Sim.MemPresence
import Vsa.Sim.Code.FixedImage_Env_new

/-!
# `EnvNewContractSupply` — the `env_new` contract from one named ledger

`EnvNewContract` (`HelperCallEnvNew.lean`) is supplied on the layer:

* the `env_new` prologue `0x800029fc`–`0x80002a0c` (`addi sp,-16; sd s0; mv s0,a0;
  li a0,32; sd ra`) is ONE `#derive_case` seg (`envNewPrologueSeg`), run by
  `segEval_sound`; the `jal malloc` at `0x80002a10` is the generated site
  `site_80002a10_env` through `jalCallFacts_of_obs` (`envNewParked_of_entry`);
* the allocator call is the ledger's `MallocRun` (the `MallocContract.spec`
  Triple with the two clauses the abstract contract omits: no console output,
  no byte removal); `MallocContract.nonNull_of_bounded` selects the block;
* the landed success suffix `envNewSuccess_run` (`EnvNewSuccessSuffix.lean`)
  initialises the 32-byte frame and returns;
* the pushed store is `storeRepr_allocFrame` (`rows/CallClosureEnvNewMarshal`)
  under `pushFrameMap`, after the ownership transport
  `StoreOwned.repr_transport` (allocator-private and fresh bytes are outside
  every represented byte by `HeapOwned`) and the frame-map rebase
  `storeRepr_phif_mono` (new here).

The facts the entry state does not carry are ONE named ledger, `EnvNewLedger`,
each field naming its supplier.  The landed `env_new_spec` is not used: its
premise `∀ p, EnvRegions … p` is false at `p = 0` (`frame_lo`).
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code
open Vsa.Sim.RuntimeOwnership

/-! ## 1. The frame-map rebase (`φf ⊑ φf'` on the allocated prefix) -/

/-- `FrameRepr` rebases under a frame map agreeing at the parent index. -/
theorem frameRepr_phif_mono {m : Mem} {N : NativeAddrs} {φf φf' φc : Addr → Nat}
    {e : Nat} {f : Vsa.While.Frame}
    (hpar : ∀ pa, f.parent = some pa → φf' pa = φf pa)
    (hf : FrameRepr m N φf φc e f) : FrameRepr m N φf' φc e f := by
  obtain ⟨hcount, hcap, hbind, hparent⟩ := hf
  refine ⟨hcount, hcap, hbind, ?_⟩
  cases hp : f.parent with
  | none => simp only [hp] at hparent ⊢; exact hparent
  | some pa => simp only [hp] at hparent ⊢; rw [hpar pa hp]; exact hparent

/-- `ClosureRepr` rebases under a frame map agreeing at the captured environment. -/
theorem closureRepr_phif_mono {m : Mem} {φf φf' : Addr → Nat} {p : Nat} {cd : ClosureData}
    (henv : φf' cd.env = φf cd.env) (h : ClosureRepr m φf p cd) : ClosureRepr m φf' p cd := by
  obtain ⟨hq, hread, hnz⟩ := h
  exact ⟨hq, by rw [henv]; exact hread, by rw [henv]; exact hnz⟩

/-- **`storeRepr_phif_mono`** — the frame-map sibling of `storeRepr_phic_mono`:
under `PhiExtends φf φf' s.frames.size`, with parents older than their frames
(`StoreParents`) and captured environments allocated, the representation rebases
verbatim (every `φf` use is at an index below `s.frames.size`). -/
theorem storeRepr_phif_mono {m : Mem} {N : NativeAddrs} {A : Arena}
    {φf φf' φc : Addr → Nat} {s : Store}
    (hparents : StoreParents s)
    (henvs : ∀ ca, (h : ca < s.closures.size) → s.closures[ca].env < s.frames.size)
    (hpe : PhiExtends φf φf' s.frames.size)
    (hr : StoreRepr m N A φf φc s) : StoreRepr m N A φf' φc s where
  frames fa hfa := by
    rw [hpe fa hfa]
    exact frameRepr_phif_mono
      (fun pa hpa => hpe pa (Nat.lt_trans (hparents fa hfa pa hpa) hfa)) (hr.frames fa hfa)
  closures ca hca := closureRepr_phif_mono (hpe _ (henvs ca hca)) (hr.closures ca hca)
  φf_inj a b ha hb h := hr.φf_inj a b ha hb (by rwa [hpe a ha, hpe b hb] at h)
  φc_inj := hr.φc_inj
  frames_arena fa hfa := by rw [hpe fa hfa]; exact hr.frames_arena fa hfa
  closures_arena := hr.closures_arena

/-! ## 2. The prologue seg and the `jal malloc` seam -/

#derive_case envNewPrologueSeg chain
  [(0x800029fc#64, 0xff010113#32),
   (0x80002a00#64, 0x00813023#32),
   (0x80002a04#64, 0x00050413#32),
   (0x80002a08#64, 0x02000513#32),
   (0x80002a0c#64, 0x00113423#32)]

/-- The prologue's entry pins (read order): `sp`, `s0`, `a0`, `ra`. -/
def envNewPrologueL (esp s0 aEnv r : BitVec 64) : GRegs :=
  [(2, esp), (8, s0), (10, aEnv), (1, r)]

/-- The prologue's two spills: `s0` at `sp-16`, `ra` at `sp-8`. -/
def envNewSpillLog (esp r s0 : BitVec 64) : List WEntry :=
  [(esp.toNat - 16, 8, s0), (esp.toNat - 16 + 8, 8, r)]

private theorem sext8_64 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
  apply BitVec.eq_of_toNat_eq; decide

private theorem sext0_64' : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq; decide

theorem envNewPrologueLog (esp s0 aEnv r : BitVec 64) (h16 : 16 ≤ esp.toNat) :
    (evalBlocks envNewPrologueSeg
      (SegEvalState.init (envNewPrologueL esp s0 aEnv r) [])).log = envNewSpillLog esp r s0 := by
  have hlt := esp.isLt
  have h1 : (esp - 16#64 + sign_extend (m := 64) (0x000#12)).toNat = esp.toNat - 16 := by
    rw [sext0_64', BitVec.add_zero, sp_sub16_toNat esp h16]
  have h2 : (esp - 16#64 + sign_extend (m := 64) (0x008#12)).toNat = esp.toNat - 16 + 8 := by
    rw [sext8_64, BitVec.toNat_add, sp_sub16_toNat esp h16]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    exact Nat.mod_eq_of_lt (by omega)
  simp [envNewPrologueSeg, evalBlocks, evalBlock, SegEvalState.init, wlogM,
    wentryM, widthOfM, runGM, stepGM, stepLdsM, ldsRunM, wvalM,
    srcVal, lookupG, eraseG, mkLine, decodeM, eaddrM, envNewPrologueL, envNewSpillLog, sp_sub16,
    h1, h2]

private theorem envNewMemFactsSd {m : Mem} {L : GRegs} {bs : List (BitVec 8)} {a : MInstr}
    (esp : BitVec 64) (off : Nat)
    (hlo : 0x80000000 ≤ esp.toNat - 16) (hhi : esp.toNat ≤ 0x100000000)
    (hhtif : tohostAddr + 16 ≤ esp.toNat - 16) (halign : esp.toNat % 16 = 0)
    (h16 : 16 ≤ esp.toNat)
    (hk : a.kind = .sd) (hsrc : srcVal a.rs1 L = esp + sign_extend (m := 64) (0xff0#12))
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hoff : off + 8 ≤ 16) (hoff8 : off % 8 = 0) : MemFacts m L bs a := by
  have hlt := esp.isLt
  have hea : (eaddrM a L).toNat = esp.toNat - 16 + off := by
    unfold eaddrM
    rw [hsrc, sp_sub16, BitVec.toNat_add, himm, sp_sub16_toNat esp h16,
      Nat.mod_eq_of_lt (by omega)]
  unfold MemFacts
  rw [hk, hea]
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- The prologue's memory obligations: the two in-frame spills. -/
theorem envNewPrologueChainFacts (m : Mem) (esp s0 aEnv r : BitVec 64)
    (hcode : Env_newLoaded m)
    (hlo : 0x80000000 ≤ esp.toNat - 16) (hhi : esp.toNat ≤ 0x100000000)
    (hhtif : tohostAddr + 16 ≤ esp.toNat - 16) (halign : esp.toNat % 16 = 0)
    (h16 : 16 ≤ esp.toNat) :
    ChainFacts m m (envNewPrologueL esp s0 aEnv r) [] envNewPrologueSeg := by
  chain_facts hcode with "Vsa.Sim.Code.env_new_at_"
  · exact envNewMemFactsSd esp 0 hlo hhi hhtif halign h16 (by decide) (by rfl) (by decide)
      (by decide) (by decide)
  · exact envNewMemFactsSd esp 8 hlo hhi hhtif halign h16 (by decide) (by rfl) (by decide)
      (by decide) (by decide)

/-- The state parked at `malloc`'s entry after the `env_new` prologue. -/
structure EnvNewParked (g : (R : Register) → Option (RegisterType R))
    (esp aEnv r sv : BitVec 64) (m : Mem) (out : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 mallocEntry)
  ra : c.σ.regs.get? Register.x1 = some 0x80002a14#64
  a0 : c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 32)
  sp : c.σ.regs.get? Register.x2 = some (esp - 16#64)
  s0 : c.σ.regs.get? Register.x8 = some aEnv
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  mem : c.σ.mem = writeLog m (envNewSpillLog esp r sv)
  out : c.σ.sailOutput = out
  /-- Every ABI register but `sp` and `s0` is untouched. -/
  keep : ∀ R, envNewSuccessKeep R = true → c.σ.regs.get? R = g R

theorem envNewSuccessKeep.abi {R : Register} (h : envNewSuccessKeep R = true) :
    AbiPreserved R = true := by
  simp only [envNewSuccessKeep, Bool.and_eq_true] at h
  exact h.1

private theorem sext32_64 : (sign_extend (m := 64) (0x020#12) : BitVec 64) = 32#64 := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Entry ⟶ parked at `malloc`.**  The reflected prologue and the observed
`jal`. -/
theorem envNewParked_of_entry
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {esp aEnv r s0 : BitVec 64} {m : Mem}
    {out : Array String} {c : Config}
    (h : EnvNewEntryState g N A SL φf φc st env esp aEnv r m out c)
    (hg8 : g Register.x8 = some s0) (hcode : Env_newLoaded m) :
    ∃ c', Steps c c' ∧ EnvNewParked g esp aEnv r s0 m out c' := by
  have F := h.facts
  obtain ⟨hsp1, hsp2, hsp3⟩ := F.stack
  have hram := F.stack_ram
  have hwin := F.stack_win
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hlt := esp.isLt
  have h16 : 16 ≤ esp.toNat := by omega
  have hx8 : c.σ.regs.get? Register.x8 = some s0 := (h.frame _ (by decide)).trans hg8
  have hL : GHolds c.σ (envNewPrologueL esp s0 aEnv r) :=
    ⟨by simpa [gprGet] using h.sp, by simpa [gprGet] using hx8,
      by simpa [gprGet] using h.a0, by simpa [gprGet] using h.ra, trivial⟩
  have hfacts : ChainFacts c.σ.mem c.σ.mem (envNewPrologueL esp s0 aEnv r) []
      envNewPrologueSeg := by
    rw [h.mem]
    exact envNewPrologueChainFacts m esp s0 aEnv r hcode (by omega) (by omega) (by omega) hsp3 h16
  obtain ⟨vm, hmi⟩ := h.good.minstret
  obtain ⟨σ1, i1, hsteps, hi1, hG1, hmem1, hout1, hpc1, hmi1, hregs1, hframe1⟩ :=
    segEval_sound envNewPrologueSeg c.σ c.tick c.steps 0x800029fc#64 vm
      (envNewPrologueL esp s0 aEnv r) [] h.good h.pc hmi hL
      (by show KeysOK [2, 8, 10, 1]; decide) hfacts
      (by show ChainOK 0x800029fc#64 [2, 8, 10, 1] envNewPrologueSeg; decide) h.tick
  have hlog := envNewPrologueLog esp s0 aEnv r h16
  have hmem1' : σ1.mem = writeLog m (envNewSpillLog esp r s0) := by
    rw [hmem1, hlog, h.mem]
  have hpc1' : σ1.regs.get? Register.PC = some 0x80002a10#64 := by
    rw [hpc1]; rfl
  have hcode1 : Env_newLoaded σ1.mem := by
    rw [hmem1']
    apply loaded_env_of_agree m _ _ hcode
    intro a hlo hhi
    apply writeLog_out
    simp only [envNewSpillLog, OutL, and_true]
    omega
  obtain ⟨vm1, hvm1⟩ := hmi1
  obtain ⟨σ2, i2, hstep, hi2, hG2, hmem2, hobs⟩ :=
    site_80002a10_env σ1 i1 (c.steps + evalBlocksFuel envNewPrologueSeg) 0x80002a10#64 vm1
      hG1 hpc1' hvm1 hcode1 rfl hi1
  have hlink : BitVec.addInt 0x80002a10#64 4 = (0x80002a14#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hlink] at hobs
  have J := jalCallFacts_of_obs hstep hi2 hG2 hmem2 hobs
    (callee := BitVec.ofNat 64 mallocEntry) (by apply BitVec.eq_of_toNat_eq; decide)
  have reg (n : Nat) (hn1 : 1 ≤ n) (hn2 : n ≤ 31) (hn3 : n ≠ 1) (v : BitVec 64)
      (hl : lookupG n (evalBlocks envNewPrologueSeg
        (SegEvalState.init (envNewPrologueL esp s0 aEnv r) [])).regs = some v) :
      gprGet σ2 n = some v :=
    J.nonra n hn1 hn2 hn3 v (gholds_lookup _ hregs1 hl)
  refine ⟨⟨σ2, i2, c.steps + evalBlocksFuel envNewPrologueSeg + 1⟩, hsteps.trans (Steps.single J.step), ?_⟩
  refine
    { good := J.good
      tick := J.tick
      pc := J.pc
      ra := J.ra
      a0 := ?_
      sp := ?_
      s0 := ?_
      minstret := J.minstret
      mem := by
        show σ2.mem = _
        rw [J.mem]; exact hmem1'
      out := by
        show σ2.sailOutput = out
        rw [J.frame.out]
        exact hout1.trans h.out
      keep := ?_ }
  · have := reg 10 (by decide) (by decide) (by decide) (BitVec.ofNat 64 32) (by
      simp [envNewPrologueSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,
        stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, envNewPrologueL,
        sext32_64])
    simpa [gprGet] using this
  · have := reg 2 (by decide) (by decide) (by decide) (esp - 16#64) (by
      simp [envNewPrologueSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,
        stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, envNewPrologueL,
        sp_sub16])
    simpa [gprGet] using this
  · have := reg 8 (by decide) (by decide) (by decide) aEnv (by
      simp [envNewPrologueSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,
        stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, envNewPrologueL,
        sext0_64'])
    simpa [gprGet] using this
  · intro R hR
    have hnoise : ∀ rr ∈ noiseRegs, envNewSuccessKeep rr = false := by decide
    have h1 : σ2.regs.get? R = σ1.regs.get? R := by
      apply J.frame.frame R
      intro rr hrr
      rcases List.mem_cons.mp hrr with rfl | hrr
      · exact regAvoids_ne hR (by decide)
      · exact noise_avoids hnoise hR rr hrr
    have h2 : σ1.regs.get? R = c.σ.regs.get? R :=
      frame_of_wrChain_avoids (P := envNewSuccessKeep) hnoise
        (by show WrChainAvoids envNewSuccessKeep envNewPrologueSeg; decide) hframe1 R hR
    exact (h1.trans h2).trans (h.frame R (envNewSuccessKeep.abi hR))

#print axioms envNewParked_of_entry

/-! ## 4. The ledger -/

/-- **The external ledger** for `env_new`: the facts `EnvNewEntryState` does not
carry.  Each field names its supplier. -/
structure EnvNewLedger (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (esp aEnv r : BitVec 64) (m : Mem)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent) : Prop where
  /-- The global pointer at entry (the interpreter's pinned `gp`; the caller's
  ABI frame). -/
  gp : g Register.x3 = some gpv
  /-- The caller's ghost is total on the spilled `s0` (the caller's `GRegs` pins:
  `HelperCall.callL`). -/
  s0_present : (g Register.x8).isSome = true
  /-- The allocator invariant at the entry memory with the pinned `gp`
  (the caller's `MallocContract` state). -/
  ainv_entry : ∀ σ : MState, σ.regs.get? Register.x3 = some gpv → σ.mem = m → M.AInv σ exts
  /-- The allocator invariant reads only `gp` and bytes outside the callee's stack
  window (the `MallocContract` footprint discipline). -/
  ainv_stable : ∀ σa σb : MState,
    σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
    (∀ a, ¬ (SL.lo ≤ a ∧ a < esp.toNat) → σa.mem[a]? = σb.mem[a]?) →
    M.AInv σa exts → M.AInv σb exts
  /-- The run-global allocator ledger (`Vsa/Sim/AllocRuns.lean`). -/
  alloc : AllocLedger A SL gpv headroom maxReq M
  /-- Parent frames are older than their children (source invariant
  `StoreInvariant.parents`). -/
  parents : StoreParents st.store
  /-- Runtime ownership of the store at entry (the interpreter's ownership
  invariant `HeapOwned`), with the stack region inside the caller's write
  footprint. -/
  owned : ∃ (alloc : Allocations) (shared readable writes : Nat → Prop),
    HeapOwned A exts m φf φc alloc shared readable writes st.store ∧
    ∀ k, SL.lo ≤ k → k < SL.hi → writes k

/-! ## 5. The pushed store at any memory agreeing off the three windows -/

/-- Bytes outside the stack region, the allocator-private footprint and the
fresh 32-byte chunk. -/
def EnvNewOff (SL : StackLayout) (privFoot : Nat → Prop) (p : Nat) (k : Nat) : Prop :=
  ¬ (SL.lo ≤ k ∧ k < SL.hi) ∧ ¬ privFoot k ∧ ¬ (p ≤ k ∧ k < p + 32)

/-- **The pushed store** at any memory agreeing with the entry memory off the
three windows, given the fresh frame's representation there. -/
theorem envNewPushedRepr
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {m m' : Mem}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {exts : List Extent}
    {alloc : Allocations} {shared readable writes : Nat → Prop} {σ : MState} {p : Nat}
    (hown : HeapOwned A exts m φf φc alloc shared readable writes st.store)
    (hwrites : ∀ k, SL.lo ≤ k → k < SL.hi → writes k)
    (hr : StoreRepr m N A φf φc st.store)
    (hainv : M.AInv σ exts)
    (priv_arena : ∀ a, M.privFoot a → A.lo ≤ a ∧ a < A.hi)
    (arena_stack : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo)
    (hparents : StoreParents st.store)
    (hpA : A.contains p 32) (hpalign : p % 16 = 0)
    (hpdisj : ∀ e ∈ exts, ExtDisjoint (p, 32) e)
    (hag : AgreeP (EnvNewOff SL M.privFoot p) m m')
    (hfr : FrameRepr m' N (pushFrameMap φf st.store.frames.size p) φc p ⟨some env, []⟩) :
    StoreRepr m' N A (pushFrameMap φf st.store.frames.size p) φc
      (st.store.allocFrame (some env)).1 := by
  -- the ONE proof that owned and shared bytes are off the allocator's three
  -- windows (`AllocOff.lean`); `EnvNewOff` is its single-block instance at 32 bytes
  have O : OwnedOff SL M.privFoot [(p, 32)] alloc shared :=
    hown.ownedOff hwrites (M.privFoot_disjoint σ exts hainv) priv_arena arena_stack
      (freshExtents_single hpA hpdisj)
  have ha : ∀ role q n, Allocated alloc role q n → ∀ k, ExtentByte (q, n) k →
      EnvNewOff SL M.privFoot p k :=
    fun role q n hq k hk => (O.alloc role q n hq k hk).single
  have hs : ∀ k, shared k → EnvNewOff SL M.privFoot p k := fun k hk => (O.shared k hk).single
  have hold : StoreRepr m' N A φf φc st.store :=
    hown.store.repr_transport hr hag ha hs
  have hold' : StoreRepr m' N A (pushFrameMap φf st.store.frames.size p) φc st.store :=
    storeRepr_phif_mono hparents hown.store.capturedEnvs
      (pushFrameMap_extends φf st.store.frames.size p) hold
  refine storeRepr_allocFrame hold' (pushFrameMap_fresh φf _ p) hfr hpA (by omega) ?_
  intro fa hfa heq
  rw [pushFrameMap_extends φf st.store.frames.size p fa hfa] at heq
  have hmem := hown.ledger.live _ _ _ (hown.store.frames fa hfa).record
  have hd := hpdisj _ hmem
  change p + 32 ≤ φf fa ∨ φf fa + 32 ≤ p at hd
  omega

#print axioms envNewPushedRepr

/-! ## 6. Entry ⟶ return -/

private theorem envNew_offMem {m : Mem} {esp r s0 : BitVec 64} {SL : StackLayout}
    (hsp1 : SL.lo + 1088 ≤ esp.toNat)
    (a : Nat) (ha : ¬ (SL.lo ≤ a ∧ a < esp.toNat)) :
    (writeLog m (envNewSpillLog esp r s0))[a]? = m[a]? := by
  apply writeLog_out
  simp only [envNewSpillLog, OutL, and_true]
  omega

/-- **The `env_new` contract's Triple from the ledger.** -/
theorem envNewReturn_of_ledger
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st : Vsa.While.St} {env : Addr} {esp aEnv r : BitVec 64} {m : Mem}
    {out : Array String}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {exts : List Extent}
    (L : EnvNewLedger g N A SL φf φc st env esp aEnv r m M exts) :
    Triple (EnvNewEntryState g N A SL φf φc st env esp aEnv r m out)
      (EnvNewReturnState g N A SL φf φc st env esp r m out) := by
  intro c h
  have F := h.facts
  obtain ⟨hsp1, hsp2, hsp3⟩ := F.stack
  have hram := F.stack_ram
  have hwin := F.stack_win
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hlt := esp.isLt
  have h16 : 16 ≤ esp.toNat := by omega
  have hAhtif := L.alloc.arena_htif
  have hAhi := L.alloc.arena_hi
  have hAstack := L.alloc.arena_stack
  obtain ⟨s0, hg8⟩ := Option.isSome_iff_exists.mp L.s0_present
  have hcode : Env_newLoaded m := FixedTextLoaded.Env_newLoaded F.text
  obtain ⟨alloc, shared, readable, writes, hown, hwrites⟩ := L.owned
  -- 1. prologue + jal
  obtain ⟨c1, hs1, P⟩ := envNewParked_of_entry h hg8 hcode
  have hmem1 : c1.σ.mem = writeLog m (envNewSpillLog esp r s0) := P.mem
  have hoff1 : ∀ a, ¬ (SL.lo ≤ a ∧ a < esp.toNat) → c1.σ.mem[a]? = m[a]? := by
    intro a ha; rw [hmem1]; exact envNew_offMem hsp1 a ha
  have hgp0 : c.σ.regs.get? Register.x3 = some gpv := (h.frame _ (by decide)).trans L.gp
  have hgp1 : c1.σ.regs.get? Register.x3 = some gpv := (P.keep _ (by decide)).trans L.gp
  have hainv0 : M.AInv c.σ exts := L.ainv_entry c.σ hgp0 h.mem
  have hainv1 : M.AInv c1.σ exts :=
    L.ainv_stable c.σ c1.σ (hgp0.trans hgp1.symm)
      (fun a ha => by rw [hoff1 a ha, h.mem]) hainv0
  have hspn := sp_sub16_toNat esp h16
  have hstack1 : StackOK SL (esp - 16#64) headroom := by
    have := L.alloc.headroom_le
    refine ⟨by omega, by omega, by omega⟩
  -- 2. malloc
  obtain ⟨c2, hs2, X⟩ := L.alloc.malloc (fun R => c1.σ.regs.get? R) exts 32 (esp - 16#64)
    0x80002a14#64 c1.σ.mem out L.alloc.req32 c1
    { good := P.good, tick := P.tick, pc := P.pc, a0 := P.a0, ra := P.ra
      ra_align := by decide, sp := P.sp, stack := hstack1, gp := hgp1
      frame := fun _ _ => rfl, ainv := hainv1, mem := rfl, out := P.out }
  obtain ⟨p, ha0, hp0, hp16, hpA, hpdisj, hainv2⟩ := M.nonNull_of_bounded c2.σ exts 32 L.alloc.req32 X.result
  obtain ⟨hplo, hphi⟩ := hpA
  have hp64 : p < 2 ^ 64 := by omega
  have hpn : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hp64
  -- the spill window is off the allocator's footprint and above its stack window
  have hspill_priv : ∀ a, esp.toNat - 16 ≤ a → a < esp.toNat → ¬ M.privFoot a := by
    intro a h1 h2 hp
    have := L.alloc.priv_arena a hp
    omega
  have hoff2 : ∀ a, ¬ (A.lo ≤ a ∧ a < A.hi) → ¬ (SL.lo ≤ a ∧ a < esp.toNat) →
      c2.σ.mem[a]? = c1.σ.mem[a]? := by
    intro a hA hst
    exact X.mem_frame a (fun hp => hA (L.alloc.priv_arena a hp)) (fun hw => hst ⟨hw.1, by omega⟩)
  have hcode1 : Env_newLoaded c1.σ.mem := by
    rw [hmem1]
    exact loaded_env_of_agree m _ (fun a hlo hhi => envNew_offMem hsp1 a (by omega)) hcode
  have hcode2 : Env_newLoaded c2.σ.mem :=
    loaded_env_of_agree c1.σ.mem c2.σ.mem (fun a hlo hhi => hoff2 a (by omega) (by omega)) hcode1
  have hagree12 : AgreeP (fun k => esp.toNat - 16 ≤ k ∧ k < esp.toNat) c1.σ.mem c2.σ.mem := by
    intro a ha
    exact (X.mem_frame a (hspill_priv a ha.1 ha.2) (by omega)).symm
  have hmem1w : c1.σ.mem = writeMap8 (writeMap8 m (esp.toNat - 16) (sdData_val s0))
      (esp.toNat - 16 + 8) (sdData_val r) := hmem1
  have hsaved_ra : read64 c2.σ.mem (esp.toNat - 16 + 8) = some r.toNat := by
    rw [← read64_agreeP hagree12 (fun k hk => ⟨by omega, by omega⟩), hmem1w, read64_writeMap8,
      sdData_toNat]
  have hsaved_s0 : read64 c2.σ.mem (esp.toNat - 16) = some s0.toNat := by
    rw [← read64_agreeP hagree12 (fun k hk => ⟨by omega, by omega⟩), hmem1w,
      read64_writeMap8_disjoint _ _ _ _ (by omega), read64_writeMap8, sdData_toNat]
  -- 3. the success suffix
  have Pre : EnvNewSuccessPre (esp - 16#64) (BitVec.ofNat 64 p) aEnv r s0 c2 :=
    { good := X.good
      tick := X.tick
      pc := X.pc
      sp := X.sp
      result := ha0
      parent := (X.frame Register.x8 (by decide)).trans P.s0
      code := hcode2
      caller :=
        { lo := by omega
          hi := by omega
          win := by omega
          align := by omega
          ret_align := h.ra_align }
      fresh :=
        { nonzero := by
            intro heq
            apply hp0
            have := congrArg BitVec.toNat heq
            rw [hpn] at this
            simpa using this
          lo := by omega
          hi := by omega
          win := by omega
          align := by omega
          stack_disjoint := by omega }
      saved_ra := by rw [hspn]; exact hsaved_ra
      saved_s0 := by rw [hspn]; exact hsaved_s0 }
  obtain ⟨c3, S, FS⟩ := envNewSuccess_run Pre
  have hmem3 : c3.σ.mem = writeLog c2.σ.mem (envNewSuccessLog (BitVec.ofNat 64 p) aEnv) := S.mem
  have hoff3 : ∀ a, ¬ (p ≤ a ∧ a < p + 32) → c3.σ.mem[a]? = c2.σ.mem[a]? := by
    intro a ha
    rw [hmem3]
    apply writeLog_out
    simp only [envNewSuccessLog, OutL, and_true, hpn]
    omega
  -- 4. memory agreement off the three windows, entry ⟶ return
  have hagree03 : AgreeP (EnvNewOff SL M.privFoot p) m c3.σ.mem := by
    intro a ⟨hst, hpriv, hfresh⟩
    rw [hoff3 a hfresh, X.mem_frame a hpriv (fun hw => hst ⟨hw.1, by omega⟩), hoff1 a
      (fun hw => hst ⟨hw.1, by omega⟩)]
  -- the fresh frame's map
  let φf' := pushFrameMap φf st.store.frames.size p
  have henv : env < st.store.frames.size := F.env_valid
  obtain ⟨henvA, _⟩ := F.store.frames_arena env henv
  change A.lo ≤ φf env ∧ φf env + 32 ≤ A.hi at henvA
  have haEnvNat : aEnv.toNat = φf env := by
    rw [F.env_addr, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hlink : φf' env = aEnv.toNat := by
    show pushFrameMap φf st.store.frames.size p env = aEnv.toNat
    unfold pushFrameMap
    rw [if_neg (Nat.ne_of_lt henv), haEnvNat]
  have hne : aEnv ≠ 0#64 := by
    intro heq
    have h0 : aEnv.toNat = 0 := by rw [heq]; rfl
    rw [haEnvNat] at h0
    omega
  have hfr3 : FrameRepr c3.σ.mem N φf' φc p ⟨some env, []⟩ := by
    have := S.frameRepr N φf' φc (some env) ⟨hlink, hne⟩
    rwa [hpn] at this
  refine ⟨c3, (hs1.trans hs2).trans FS.steps, ?_⟩
  refine
    { good := S.good
      tick := S.tick
      pc := S.pc
      ra := S.ra
      sp := by rw [S.sp, BitVec.sub_add_cancel]
      minstret := S.minstret
      out := S.output.trans X.out
      frame := ?_
      fresh := ⟨BitVec.ofNat 64 p, φf', S.result, ?_⟩
      mem_frame := ?_
      mem_extends := ?_ }
  · intro R hR
    by_cases h2 : R = Register.x2
    · subst h2
      rw [S.sp, BitVec.sub_add_cancel]
      exact ((h.frame _ hR).symm.trans h.sp).symm
    · by_cases h8 : R = Register.x8
      · subst h8
        rw [S.s0]; exact hg8.symm
      · have hk : envNewSuccessKeep R = true := by
          simp only [envNewSuccessKeep, hR, Bool.true_and, Bool.not_eq_true', Bool.or_eq_false_iff,
            beq_eq_false_iff_ne, ne_eq]
          exact ⟨h2, h8⟩
        have h3 : c3.σ.regs.get? R = c2.σ.regs.get? R := FS.frame.regs.eq R hk
        exact (h3.trans (X.frame R hR)).trans (P.keep R hk)
  · exact
      { map_extends := pushFrameMap_extends φf _ p
        addr := by rw [hpn]; exact pushFrameMap_fresh φf _ p
        nonzero := Pre.fresh.nonzero
        arena := by rw [hpn]; exact ⟨hplo, hphi⟩
        align := by rw [hpn]; omega
        store := envNewPushedRepr hown hwrites F.store hainv0 L.alloc.priv_arena hAstack L.parents
          ⟨hplo, hphi⟩ hp16 hpdisj hagree03 hfr3
        survives := by
          intro m' hm'
          have hag' : AgreeP (EnvNewOff SL M.privFoot p) m m' :=
            hagree03.trans (fun a ha => hm' a ha.1)
          have hfr' : FrameRepr m' N φf' φc p ⟨some env, []⟩ := by
            refine frameRepr_agreeP (P := fun k => p ≤ k ∧ k < p + 32)
              (fun a ha => hm' a (by omega)) (fun k hk => hk) ?_ ?_ ?_ hfr3
            · intro _ _ _ _ i hi; exact absurd hi (Nat.not_lt_zero _)
            · intro _ _ _ _ i hi; exact absurd hi (Nat.not_lt_zero _)
            · intro _ _ _ _ i hi; exact absurd hi (Nat.not_lt_zero _)
          exact envNewPushedRepr hown hwrites F.store hainv0 L.alloc.priv_arena hAstack L.parents
            ⟨hplo, hphi⟩ hp16 hpdisj hag' hfr' }
  · intro k hA hst
    rw [hoff3 k (by omega), hoff2 k hA hst, hoff1 k hst]
  · have e1 : MemExtends m c1.σ.mem := by rw [hmem1]; exact memExtends_writeLog _ _
    have e3 : MemExtends c2.σ.mem c3.σ.mem := by rw [hmem3]; exact memExtends_writeLog _ _
    exact (e1.trans X.mem_extends).trans e3

#print axioms envNewReturn_of_ledger

/-- **`EnvNewContract` from the ledger.**  Every entry state has a
`MallocContract` instance and a live-extent list under which the ledger holds. -/
theorem envNewContract_of_ledger
    (hL : ∀ (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (st : Vsa.While.St) (env : Addr) (esp aEnv r : BitVec 64) (m : Mem)
      (out : Array String) (cfg : Config),
      EnvNewEntryState g N A SL φf φc st env esp aEnv r m out cfg →
      ∃ (gpv : BitVec 64) (headroom maxReq : Nat)
        (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent),
        EnvNewLedger g N A SL φf φc st env esp aEnv r m M exts) :
    EnvNewContract := by
  intro g N A SL φf φc st env esp aEnv r m out c h
  obtain ⟨gpv, headroom, maxReq, M, exts, L⟩ := hL g N A SL φf φc st env esp aEnv r m out c h
  exact envNewReturn_of_ledger L c h

#print axioms envNewContract_of_ledger

end Vsa.Sim
