import Vsa.Sim.rows.StrdupTailBridges
import Vsa.Sim.rows.StringifyStrdupTail
import Vsa.Sim.BridgeSeg
import Vsa.Sim.BridgeSegFramed
import Vsa.Sim.Code.Stringify
import Vsa.Sim.DecodeTable.Batch12Part10
import Vsa.Sim.DecodeTable.Batch12Part32
import Vsa.Sim.DecodeTable.Batch11Part08

/-!
# `StrdupTailJalSeams` — the three `strdup`-tail `jal` seams, discharged

`stringifyStrdupTailContract` (`Vsa/Sim/rows/StringifyStrdupTail.lean`) composed the
shared `stringify` strdup tail as pure `callSeg` algebra over the framed callee
contracts, leaving FOUR named machine-bridge premises.  The three ARG-STAGING
bridges (`bridgeStrlenPre`/`bridgeMallocPre`/`bridgeMemcpyPre`) are each a
straight-line arg-marshalling span ▷ `jal callee`; the seg BODIES of those spans are
landed (`strdupStrlenArgSeg`/`strdupMallocArgSeg`/`strdupMemcpyArgSeg`, re-exported by
`StrdupTailBridges`).  This file lands the `jal` SEAMS on top of those seg bodies via
the mandated `BridgeSeg.bridgeOfSeg` (seg body run + ABI frame both FREE) +
`jalStep_of_obs` (the ONE genuinely region-specific step, the callee entry `jal`).

This is EXACTLY the `EnvDefSeg.capComputeSeg_run` idiom (`Vsa/Sim/EnvDefSeg.lean`:186):
`bridgeOfSeg` over the seg + `jalStep_of_obs` fed a `stepObs_jal` off the `Stringify`
Code pins (`Vsa/Sim/Code/Stringify.lean`, generated wave-32) on the parked seg-post
memory.  The parked memory is `writeLog m0 out.log`; the caller supplies a
`StringifyLoaded (writeLog …)` datum (the code region is outside every span's store
footprint), so the jal byte pins hold at the seam.

The three seams:

| seam | span end / jal PC | callee entry | link | jal word |
|------|-------------------|--------------|------|----------|
| strlen | `0x80003048` | `0x80006cf0` | `0x8000304c` | `0x4a9030ef` |
| malloc | `0x80003058` | `0x80004790` | `0x8000305c` | `0x738010ef` |
| memcpy | `0x8000306c` | `0x80006bc8` | `0x80003070` | `0x35d030ef` |

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.Alloc
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Sim.Code (StringifyLoaded StrlenLoaded stringify_at_80003048 stringify_at_80003058
  stringify_at_8000306c)

namespace Vsa.Sim

set_option maxHeartbeats 1600000
set_option maxRecDepth 1000000

/-! ## §1. The strlen seam: `mv a0,s1` body ▷ `jal strlen @0x80006cf0`

The `strdupStrlenArgSeg` body is `mv a0,s1` (`0x80003044 → 0x80003048`); the seam is
`jal strlen`.  `bridgeOfSeg` runs the body (FREE) and `jalStep_of_obs` (over
`stepObs_jal` + the `stringify_at_80003048` code pins) takes the `jal`. -/

/-- **`strdupTail_strlen_run`** — the `mv a0,s1 ; jal strlen` prefix, landed via
`bridgeOfSeg` + `jalStep_of_obs`.  From the entry at `0x80003044` (`x9 = s1`,
`mem = m0`), runs to the strlen entry `0x80006cf0` with `x10 = s1`, `x1 = 0x8000304c`
(link), memory = the seg write-log (= `m0`, the `mv` stores nothing), a `minstret`
witness, `GHolds` for the marshalled regs, and the ABI callee-saved frame. -/
theorem strdupTail_strlen_run
    (σ : MState) (i u : Nat) (vminstret s1 : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some (0x80003044#64 : BitVec 64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : σ.mem = m0)
    (hL : GHolds σ (strdupStrlenArgL s1))
    (hfacts : ChainFacts σ.mem σ.mem (strdupStrlenArgL s1) [] strdupStrlenArgSeg)
    (hjalmem : StringifyLoaded (writeLog m0
      (evalBlocks strdupStrlenArgSeg (SegEvalState.init (strdupStrlenArgL s1) [])).log))
    (hi : i < 2) :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel strdupStrlenArgSeg + 1⟩ ∧ i2 < 2 ∧
        GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (0x80006cf0#64 : BitVec 64) ∧
      σ2.regs.get? Register.x1 = some (0x8000304c#64 : BitVec 64) ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      GHolds σ2 (evalBlocks strdupStrlenArgSeg (SegEvalState.init (strdupStrlenArgL s1) [])).regs ∧
      σ2.mem = writeLog m0 (evalBlocks strdupStrlenArgSeg (SegEvalState.init (strdupStrlenArgL s1) [])).log ∧
      (∀ R, AbiPreserved R = true → σ2.regs.get? R = σ.regs.get? R) := by
  apply bridgeOfSeg strdupStrlenArgSeg (strdupStrlenArgL s1) []
    σ i u (0x80003044#64) (0x80006cf0#64) (0x8000304c#64) vminstret m0
    hG hpc hminstret hmem hL
    (by have h : keysG (strdupStrlenArgL s1) = [9] := rfl
        rw [h]; decide)
    hfacts hi
    (by have h : keysG (strdupStrlenArgL s1) = [9] := rfl
        rw [h]; show ChainOK (0x80003044#64) [9] strdupStrlenArgSeg; decide)
    (by show WrChainAvoidAbi strdupStrlenArgSeg; decide)
    (by have h : keysG (evalBlocks strdupStrlenArgSeg
          (SegEvalState.init (strdupStrlenArgL s1) [])).regs = [10, 9] := rfl
        rw [h]; decide)
    (by have h : keysG (evalBlocks strdupStrlenArgSeg
          (SegEvalState.init (strdupStrlenArgL s1) [])).regs = [10, 9] := rfl
        show ∀ n ∈ keysG _, n ≠ 1; rw [h]; decide)
  -- the jal seam: `jal strlen` at the parked PC `0x80003048`.
  intro σ' i' u' hG' hi' hpc' hmi' hmem' _hregs'
  obtain ⟨vm', hmi'v⟩ := hmi'
  have hpcE : (evalBlocksPC (0x80003044#64)
      (SegEvalState.init (strdupStrlenArgL s1) []) strdupStrlenArgSeg)
      = (0x80003048#64 : BitVec 64) := by rfl
  have hpc'' : σ'.regs.get? Register.PC = some (0x80003048#64 : BitVec 64) := hpcE ▸ hpc'
  obtain ⟨hb0, hb1, hb2, hb3⟩ := stringify_at_80003048 (hmem' ▸ hjalmem)
  obtain ⟨σ2, i2, hstep, hi2, hG2, hmem2, hobs⟩ :=
    stepObs_jal σ' i' u' (0x80003048#64) vm' (0x4a9030ef#32) (0x003ca8#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80003048#64) 4)
      (0xef#8) (0x30#8) (0x90#8) (0x4a#8)
      hG' hpc'' hmi'v hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (Vsa.Sim.DecodeTable.decode_4a9030ef (afterPrelude σ')
        (by rw [get?_afterPrelude σ' _ (by decide)]; exact hG'.misa)
        (by rw [get?_afterPrelude σ' _ (by decide)]; exact hG'.cur_privilege)
        (by rw [get?_afterPrelude σ' _ (by decide)]; exact hG'.mseccfg))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x80003048#64) 4)) hi'
  have hlink : BitVec.addInt (0x80003048#64) 4 = (0x8000304c#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hlink] at hobs
  exact jalStep_of_obs hstep hi2 hG2 hmem2 hobs (by apply BitVec.eq_of_toNat_eq; decide)

#print axioms strdupTail_strlen_run

/-! ## §1b. `bridgeStrlenPre` closed — the frame-carrying strlen prefix wrapper

`stringifyStrdupTailContract`'s `bridgeStrlenPre` premise is
`Triple P (fun c => strlen_pre bufPtr rStrlen str m0 c ∧ EnvDefFrame …)` with `P`
caller-supplied.  We name the honest entry predicate `StrdupTailStrlenEntry` (the
strlen-arg facts at `0x80003044` PLUS the carried `EnvDefFrame` ghosts) and land the
bridge over `strdupTail_strlen_run` — the EXACT `bridgeStrlenPre_closed` idiom
(`Vsa/Sim/EnvDefBridges.lean`:334), the `mv;jal` prefix having no stores so the frame
survives (`GHolds`/ABI-frame carry sp/gp; `AInv` survives mem-and-gp agreement). -/

/-- Strdup-tail strlen entry predicate at `0x80003044`: the `strlen` arg facts
(`StrlenLoaded`, `StrRegions`, 8-alignment, `CString`, `x9 = bufPtr`) + the carried
caller-frame (`EnvDefFrame`). -/
def StrdupTailStrlenEntry (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List (Nat × Nat) → Prop) (exts : List (Nat × Nat))
    (sp : BitVec 64) (gm : (R : Register) → Option (RegisterType R))
    (bufPtr : BitVec 64) (str : String) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (c : Config) : Prop :=
  GoodState c.σ ∧ StringifyLoaded c.σ.mem ∧ StrlenLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x80003044#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x9 = some bufPtr ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
  StrRegions bufPtr str.length ∧ bufPtr.toNat % 8 = 0 ∧
  CString m0 bufPtr.toNat str ∧
  EnvDefFrame SL gpv headroom AInv exts sp gm c

/-- **`bridgeStrlenPre` discharged (frame-carrying).**  From `StrdupTailStrlenEntry`,
the `mv a0,s1 ; jal strlen` prefix lands
`strlen_pre bufPtr 0x8000304c str m0 ∧ EnvDefFrame …` at the strlen entry.  `hAInvStable`
is `AInv`'s stability under (gp-agree ∧ mem-agree) — the `MallocContract`-interface
property; the prefix stores nothing (mem = m0) and preserves gp, so `AInv` survives. -/
theorem strdupTailBridgeStrlenPre_closed
    (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List (Nat × Nat) → Prop) (exts : List (Nat × Nat))
    (sp : BitVec 64) (gm : (R : Register) → Option (RegisterType R))
    (bufPtr : BitVec 64) (str : String) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hAInvStable : ∀ (σa σb : MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a : Nat, σa.mem[a]? = σb.mem[a]?) → AInv σa exts → AInv σb exts) :
    Triple (StrdupTailStrlenEntry SL gpv headroom AInv exts sp gm bufPtr str m0)
      (fun c => strlen_pre bufPtr (0x8000304c#64 : BitVec 64) str m0 c ∧
        EnvDefFrame SL gpv headroom AInv exts sp gm c) := by
  intro c hpre
  obtain ⟨hG, hstrfy, hstrlen, hmem, hpc, hx9, ⟨vmi, hmi⟩, htick, hreg, halign8, hcstr,
    hFrame⟩ := hpre
  obtain ⟨hsp, hstackOK, hgp, hAbi, hAInv, _htickF⟩ := hFrame
  -- the `mv` seg has no stores, so its write-log leaves `m0` unchanged (`rfl`).
  have hlogNil : writeLog m0 (evalBlocks strdupStrlenArgSeg
      (SegEvalState.init (strdupStrlenArgL bufPtr) [])).log = m0 := by rfl
  have hL : GHolds c.σ (strdupStrlenArgL bufPtr) := ⟨hx9, trivial⟩
  have hfacts : ChainFacts c.σ.mem c.σ.mem (strdupStrlenArgL bufPtr) [] strdupStrlenArgSeg := by
    chain_facts hstrfy with "Vsa.Sim.Code.stringify_at_"
  have hjalmem : StringifyLoaded (writeLog m0 (evalBlocks strdupStrlenArgSeg
      (SegEvalState.init (strdupStrlenArgL bufPtr) [])).log) := by
    rw [hlogNil, ← hmem]; exact hstrfy
  obtain ⟨σ2, i2, hsteps, hi2, hG2, hpc2, hra2, ⟨w2, hmi2⟩, hregs2, hmem2, habi2⟩ :=
    strdupTail_strlen_run c.σ c.tick c.steps vmi bufPtr m0 hG hpc hmi hmem hL hfacts hjalmem htick
  -- read the marshalled `x10 = bufPtr` off the `GHolds` post; mem = m0 off the write-log.
  have hsext0 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  have hx10 : σ2.regs.get? Register.x10 = some bufPtr := by
    have h := gholds_lookup _ hregs2 (show lookupG 10
      (evalBlocks strdupStrlenArgSeg (SegEvalState.init (strdupStrlenArgL bufPtr) [])).regs
      = some (bufPtr + sign_extend (m := 64) (0x000#12)) from rfl)
    rwa [hsext0, BitVec.add_zero] at h
  have hmemEq : σ2.mem = m0 := by rw [hmem2, hlogNil]
  -- sp/gp preserved through the ABI frame (both callee-saved).
  have hsp2 : σ2.regs.get? Register.x2 = some sp := by rw [habi2 Register.x2 (by decide)]; exact hsp
  have hgp2 : σ2.regs.get? Register.x3 = some gpv := by rw [habi2 Register.x3 (by decide)]; exact hgp
  refine ⟨⟨σ2, i2, c.steps + evalBlocksFuel strdupStrlenArgSeg + 1⟩, ?_, ?_, ?_⟩
  · cases c; exact hsteps
  · -- strlen_pre
    refine ⟨hG2, ?_, hmemEq, hpc2, hx10, hra2, ⟨w2, hmi2⟩, hi2, hreg, halign8, ?_, by decide⟩
    · rw [hmemEq, ← hmem]; exact hstrlen
    · exact hcstr
  · -- EnvDefFrame
    refine ⟨hsp2, hstackOK, hgp2, ?_, ?_, hi2⟩
    · intro R hR; rw [habi2 R (by exact hR)]; exact hAbi R hR
    · -- AInv survives: mem = m0 (unchanged), gp preserved.
      refine hAInvStable c.σ σ2 ?_ ?_ hAInv
      · rw [hgp2, hgp]
      · intro a; rw [hmemEq, hmem]

#print axioms strdupTailBridgeStrlenPre_closed

/-! ## §2. The malloc seam: `addi a2,a0,1 ; mv a0,a2 ; sd a2,8(sp)` body ▷ `jal malloc`

The `strdupMallocArgSeg` body (`0x8000304c → 0x80003058`) marshals `len+1` into `a0`
and spills it; the seam is `jal malloc @0x80004790` (imm `0x001738`, link `0x8000305c`). -/

/-- **`strdupTail_malloc_run`** — the malloc arg-staging prefix ▷ `jal malloc`, landed
via `bridgeOfSeg` + `jalStep_of_obs`.  From the entry at `0x8000304c` (`x10 = a0`,
`x2 = sp`, `mem = m0`), runs to the malloc entry `0x80004790` with `x1 = 0x8000305c`
(link), memory = the seg write-log (the `sd` spill at `8(sp)`), `GHolds` for the
marshalled regs, and the ABI callee-saved frame. -/
theorem strdupTail_malloc_run
    (σ : MState) (i u : Nat) (vminstret a0 sp : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some (0x8000304c#64 : BitVec 64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : σ.mem = m0)
    (hL : GHolds σ (strdupMallocArgL a0 sp))
    (hfacts : ChainFacts σ.mem σ.mem (strdupMallocArgL a0 sp) [] strdupMallocArgSeg)
    (hjalmem : StringifyLoaded (writeLog m0
      (evalBlocks strdupMallocArgSeg (SegEvalState.init (strdupMallocArgL a0 sp) [])).log))
    (hi : i < 2) :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel strdupMallocArgSeg + 1⟩ ∧ i2 < 2 ∧
        GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (0x80004790#64 : BitVec 64) ∧
      σ2.regs.get? Register.x1 = some (0x8000305c#64 : BitVec 64) ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      GHolds σ2 (evalBlocks strdupMallocArgSeg (SegEvalState.init (strdupMallocArgL a0 sp) [])).regs ∧
      σ2.mem = writeLog m0 (evalBlocks strdupMallocArgSeg (SegEvalState.init (strdupMallocArgL a0 sp) [])).log ∧
      (∀ R, AbiPreserved R = true → σ2.regs.get? R = σ.regs.get? R) := by
  apply bridgeOfSeg strdupMallocArgSeg (strdupMallocArgL a0 sp) []
    σ i u (0x8000304c#64) (0x80004790#64) (0x8000305c#64) vminstret m0
    hG hpc hminstret hmem hL
    (by have h : keysG (strdupMallocArgL a0 sp) = [10, 2] := rfl
        rw [h]; decide)
    hfacts hi
    (by have h : keysG (strdupMallocArgL a0 sp) = [10, 2] := rfl
        rw [h]; show ChainOK (0x8000304c#64) [10, 2] strdupMallocArgSeg; decide)
    (by show WrChainAvoidAbi strdupMallocArgSeg; decide)
    (by have h : keysG (evalBlocks strdupMallocArgSeg
          (SegEvalState.init (strdupMallocArgL a0 sp) [])).regs = [10, 12, 2] := rfl
        rw [h]; decide)
    (by have h : keysG (evalBlocks strdupMallocArgSeg
          (SegEvalState.init (strdupMallocArgL a0 sp) [])).regs = [10, 12, 2] := rfl
        show ∀ n ∈ keysG _, n ≠ 1; rw [h]; decide)
  intro σ' i' u' hG' hi' hpc' hmi' hmem' _hregs'
  obtain ⟨vm', hmi'v⟩ := hmi'
  have hpcE : (evalBlocksPC (0x8000304c#64)
      (SegEvalState.init (strdupMallocArgL a0 sp) []) strdupMallocArgSeg)
      = (0x80003058#64 : BitVec 64) := by rfl
  have hpc'' : σ'.regs.get? Register.PC = some (0x80003058#64 : BitVec 64) := hpcE ▸ hpc'
  obtain ⟨hb0, hb1, hb2, hb3⟩ := stringify_at_80003058 (hmem' ▸ hjalmem)
  obtain ⟨σ2, i2, hstep, hi2, hG2, hmem2, hobs⟩ :=
    stepObs_jal σ' i' u' (0x80003058#64) vm' (0x738010ef#32) (0x001738#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80003058#64) 4)
      (0xef#8) (0x10#8) (0x80#8) (0x73#8)
      hG' hpc'' hmi'v hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (Vsa.Sim.DecodeTable.decode_738010ef (afterPrelude σ')
        (by rw [get?_afterPrelude σ' _ (by decide)]; exact hG'.misa)
        (by rw [get?_afterPrelude σ' _ (by decide)]; exact hG'.cur_privilege)
        (by rw [get?_afterPrelude σ' _ (by decide)]; exact hG'.mseccfg))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x80003058#64) 4)) hi'
  have hlink : BitVec.addInt (0x80003058#64) 4 = (0x8000305c#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hlink] at hobs
  exact jalStep_of_obs hstep hi2 hG2 hmem2 hobs (by apply BitVec.eq_of_toNat_eq; decide)

#print axioms strdupTail_malloc_run

/-! ## §3. The memcpy seam: `ld a2,8(sp) ; mv s0,a0 ▷ beqz(false) ; mv a1,s1` body ▷ `jal memcpy`

The `strdupMemcpyArgSeg` body (`0x8000305c → 0x8000306c`, two blocks, first ending in
a not-taken `beqz`) marshals the memcpy args across the OOM guard; the seam is
`jal memcpy @0x80006bc8` (imm `0x003b5c`, link `0x80003070`).

The `mv s0,a0` step REWRITES the callee-saved `x8`/s0 (deliberate: s0 holds the fresh
malloc result across the memcpy call, to be returned by the epilogue), so
`WrChainAvoidAbi` legitimately FAILS on this span.  We use `BridgeSegFramed.bridgeOfSegFramed`
at `P := AbiExceptS0` (ABI callee-saveds MINUS s0): every callee-saved EXCEPT s0 is
framed; the reseated s0 value (= the malloc result) is EXPOSED via the `GHolds σ2 out.regs`
post (its computed delta, free), exactly the `mvS7Seg` idiom in `BridgeSegFramed`. -/

/-- `AbiPreserved` restricted to drop the reseated `s0`/x8 (which `mv s0,a0` overwrites
with the malloc result across the memcpy call). -/
def AbiExceptS0 (R : Register) : Bool := AbiPreserved R && !(R == Register.x8)

theorem strdupTail_memcpy_run
    (σ : MState) (i u : Nat) (vminstret sp a0 s1 : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (lds : List (List (BitVec 8)))
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some (0x8000305c#64 : BitVec 64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : σ.mem = m0)
    (hL : GHolds σ (strdupMemcpyArgL sp a0 s1))
    (hfacts : ChainFacts σ.mem σ.mem (strdupMemcpyArgL sp a0 s1) lds strdupMemcpyArgSeg)
    (hjalmem : StringifyLoaded (writeLog m0
      (evalBlocks strdupMemcpyArgSeg (SegEvalState.init (strdupMemcpyArgL sp a0 s1) lds)).log))
    (hi : i < 2) :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel strdupMemcpyArgSeg + 1⟩ ∧ i2 < 2 ∧
        GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (0x80006bc8#64 : BitVec 64) ∧
      σ2.regs.get? Register.x1 = some (0x80003070#64 : BitVec 64) ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      GHolds σ2 (evalBlocks strdupMemcpyArgSeg (SegEvalState.init (strdupMemcpyArgL sp a0 s1) lds)).regs ∧
      σ2.mem = writeLog m0 (evalBlocks strdupMemcpyArgSeg (SegEvalState.init (strdupMemcpyArgL sp a0 s1) lds)).log ∧
      (∀ R, AbiExceptS0 R = true → σ2.regs.get? R = σ.regs.get? R) := by
  apply bridgeOfSegFramed AbiExceptS0 strdupMemcpyArgSeg (strdupMemcpyArgL sp a0 s1) lds
    σ i u (0x8000305c#64) (0x80006bc8#64) (0x80003070#64) vminstret m0
    hG hpc hminstret hmem hL
    (by have h : keysG (strdupMemcpyArgL sp a0 s1) = [2, 10, 9] := rfl
        rw [h]; decide)
    hfacts hi
    (by have h : keysG (strdupMemcpyArgL sp a0 s1) = [2, 10, 9] := rfl
        rw [h]; show ChainOK (0x8000305c#64) [2, 10, 9] strdupMemcpyArgSeg; decide)
    (by show ∀ rr ∈ noiseRegs, AbiExceptS0 rr = false; decide)
    (by show WrChainAvoids AbiExceptS0 strdupMemcpyArgSeg; decide)
    (by have h : keysG (evalBlocks strdupMemcpyArgSeg
          (SegEvalState.init (strdupMemcpyArgL sp a0 s1) lds)).regs = [11, 8, 12, 2, 10, 9] := rfl
        rw [h]; decide)
    (by have h : keysG (evalBlocks strdupMemcpyArgSeg
          (SegEvalState.init (strdupMemcpyArgL sp a0 s1) lds)).regs = [11, 8, 12, 2, 10, 9] := rfl
        show ∀ n ∈ keysG _, n ≠ 1; rw [h]; decide)
    (by intro R hR; show AbiPreserved R = true
        have := (Bool.and_eq_true _ _).mp hR; exact this.1)
  intro σ' i' u' hG' hi' hpc' hmi' hmem' _hregs'
  obtain ⟨vm', hmi'v⟩ := hmi'
  have hpcE : (evalBlocksPC (0x8000305c#64)
      (SegEvalState.init (strdupMemcpyArgL sp a0 s1) lds) strdupMemcpyArgSeg)
      = (0x8000306c#64 : BitVec 64) := by rfl
  have hpc'' : σ'.regs.get? Register.PC = some (0x8000306c#64 : BitVec 64) := hpcE ▸ hpc'
  obtain ⟨hb0, hb1, hb2, hb3⟩ := stringify_at_8000306c (hmem' ▸ hjalmem)
  obtain ⟨σ2, i2, hstep, hi2, hG2, hmem2, hobs⟩ :=
    stepObs_jal σ' i' u' (0x8000306c#64) vm' (0x35d030ef#32) (0x003b5c#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000306c#64) 4)
      (0xef#8) (0x30#8) (0xd0#8) (0x35#8)
      hG' hpc'' hmi'v hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (Vsa.Sim.DecodeTable.decode_35d030ef (afterPrelude σ')
        (by rw [get?_afterPrelude σ' _ (by decide)]; exact hG'.misa)
        (by rw [get?_afterPrelude σ' _ (by decide)]; exact hG'.cur_privilege)
        (by rw [get?_afterPrelude σ' _ (by decide)]; exact hG'.mseccfg))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000306c#64) 4)) hi'
  have hlink : BitVec.addInt (0x8000306c#64) 4 = (0x80003070#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hlink] at hobs
  exact jalStep_of_obs hstep hi2 hG2 hmem2 hobs (by apply BitVec.eq_of_toNat_eq; decide)

#print axioms strdupTail_memcpy_run

end Vsa.Sim
