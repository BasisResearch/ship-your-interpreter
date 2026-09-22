import Vsa.Sim.rows.EnvDefineMissLedger
import Vsa.Sim.TruthyCopy
import Vsa.Sim.rows.EnvDefineAppendPrefix
import Vsa.Sim.EnvDefBridges2
import Vsa.Sim.EnvDefBridges3
import Vsa.Sim.EnvDefBridges4
import Vsa.Sim.BridgeSegFull
import Vsa.Sim.DecodeTable.Batch08Part31

/-!
# `EnvDefineCallRuns` — the miss lanes' call prefixes, with output

Every callee of `env_define`'s miss lanes is reached through a straight-line
prefix and a `jal`.  The landed prefix runs (`strlenPrefix_run`,
`mallocPrefix_run`, `envDefineMemcpyCallRun`, `capComputePrefix_run`,
`namesToValsPrefix_run`) export no `sailOutput` clause, which
`EnvDefineReturnState.out` demands.  This file lands each prefix as ONE
`#derive_case` seg run through `bridgeOfSegFull` (`SegCallFacts.output` keeps
the output; `jalCallFacts_of_obs` retains the actual `jal` endpoint), packaged
as a named-field parked state at the callee entry:

* `envDefineSegCall` — the generic seg + `jal` run over any `env_define` `jal`
  site lemma;
* `EnvDefineStrlenParked` / `EnvDefineMallocParked` / `EnvDefineMemcpyParked`
  — the append lane's three callee entries;
* `EnvDefineReallocNamesParked` (from the grow arm at `0x80002b90` or the
  empty frame's `0x80002b98`) / `EnvDefineReallocValsParked` — the grow lane's
  two `realloc` entries;
* `EnvDefineRejoinDone` — the reflected rejoin `0x80002bc0` → `0x80002b1c`
  after the second `realloc`, with output and the ABI frame.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.MemRepr Vsa.RuntimeRepr
open Vsa.Alloc (AbiPreserved)
open Vsa.Sim.Code (Env_defineLoaded)

-- discipline: allow(R7-conj-tower-def) every existential here is the reached config
-- (`∃ c'`) or the `minstret` word over a NAMED-FIELD parked structure, not an ∃/∧ tower
open Vsa.Sim.TruthyCopy (abiButS0 abiButS0_noise)

namespace Vsa.Sim

/-! ## 1. The generic prefix + `jal` run -/

/-- One reflected prefix followed by an observed `jal` (`env_define`'s image
loaded), keeping every non-ABI clause of `SegCallFacts`, in particular the
console output. -/
theorem envDefineSegCall (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 jalPC callee : BitVec 64) (imm : BitVec 21) (c : Config)
    (site : ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some jalPC →
      σ.regs.get? Register.minstret = some vmi → Env_defineLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ jalPC vmi imm Register.x1 (BitVec.addInt jalPC 4)))
    (htgt : jalPC + sign_extend (m := 64) imm = callee)
    (hg : GoodState c.σ) (hp : c.σ.regs.get? Register.PC = some pc0) (ht : c.tick < 2)
    (hl : GHolds c.σ L) (hk : KeysOK (keysG L))
    (hf : ChainFacts c.σ.mem c.σ.mem L lds bs) (hw : ChainOK pc0 (keysG L) bs)
    (hko : KeysOK (keysG (evalBlocks bs (SegEvalState.init L lds)).regs))
    (hra : KeysAvoidRa (evalBlocks bs (SegEvalState.init L lds)).regs)
    (hend : evalBlocksPC pc0 (SegEvalState.init L lds) bs = jalPC)
    (hcode : Env_defineLoaded (writeLog c.σ.mem (evalBlocks bs (SegEvalState.init L lds)).log)) :
    ∃ after, SegCallFacts bs L lds callee (BitVec.addInt jalPC 4) c after := by
  apply bridgeOfSegFull bs L lds pc0 callee (BitVec.addInt jalPC 4) c hg hp hg.minstret ht hl hk
    hf hw hko hra
  intro middle hGm htm hpcm hmim hmemm _
  obtain ⟨σ', i', u'⟩ := middle
  obtain ⟨vm', hmi'⟩ := hmim
  rw [hend] at hpcm
  have hloaded' : Env_defineLoaded σ'.mem := by
    show Env_defineLoaded (⟨σ', i', u'⟩ : Config).σ.mem
    rw [hmemm]
    exact hcode
  obtain ⟨σ2, i2, hstep, hi2, hG2, hmem2, hobs⟩ := site σ' i' u' vm' hGm hpcm hmi' hloaded' htm
  exact ⟨⟨σ2, i2, u' + 1⟩, jalCallFacts_of_obs hstep hi2 hG2 hmem2 hobs htgt⟩

/-- The `jal memcpy` observation at `0x80002b40` (the call seam is outside
`TKind`). -/
theorem envDefineMemcpyJal (σ : MState) (i u : Nat) (vmi : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some 0x80002b40#64)
    (hmi : σ.regs.get? Register.minstret = some vmi)
    (hmem : Env_defineLoaded σ.mem) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jal σ 0x80002b40#64 vmi 0x004088#21 Register.x1
        (BitVec.addInt 0x80002b40#64 4)) := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.env_define_at_80002b40 hmem
  exact stepObs_jal σ i u 0x80002b40#64 vmi 0x088040ef#32 0x004088#21
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt 0x80002b40#64 4)
    0xef#8 0x40#8 0x80#8 0x08#8 hG hpc hmi hb0 hb1 hb2 hb3
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Vsa.Sim.DecodeTable.decode_088040ef (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (wX_bits_x1 _ (BitVec.addInt 0x80002b40#64 4)) hi

/-- The ABI frame of a seg call whose prefix writes no register of `P`. -/
private theorem segCallFrame {P : Register → Bool} {bs : List BBlock} {σ' σ : MState}
    (hnoise : ∀ rr ∈ noiseRegs, P rr = false) (havoid : WrChainAvoids P bs)
    (hne1 : P Register.x1 = false)
    (hframe : ∀ R, (∀ r ∈ noiseRegs, (r == R) = false) →
      (∀ n ∈ wrChain bs, (gprReg n == R) = false) →
      (Register.x1 == R) = false → σ'.regs.get? R = σ.regs.get? R) :
    ∀ R, P R = true → σ'.regs.get? R = σ.regs.get? R := by
  intro R hR
  exact hframe R (noise_avoids hnoise hR) (wrChain_avoids havoid hR)
    (by cases R <;> simp_all)

private theorem sext0_64 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by decide
private theorem sext1_64 : (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 := by decide
theorem sext4_64 : (sign_extend (m := 64) (0x004#12) : BitVec 64).toNat = 4 := by decide
theorem sext8_64 : (sign_extend (m := 64) (0x008#12) : BitVec 64).toNat = 8 := by decide
private theorem sext16_64 : (sign_extend (m := 64) (0x010#12) : BitVec 64).toNat = 16 := by decide

theorem memFactsLw {m : Mem} {L : GRegs} {a : MInstr} {bs : List (BitVec 8)}
    (base : Nat) (hk : a.kind = .lw) (hea : (eaddrM a L).toNat = base)
    (hlo : 0x80000000 ≤ base) (hhi : base + 4 ≤ 0x100000000)
    (hht : base + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ base)
    (hp : LPins4 m base bs) : MemFacts m L bs a := by
  unfold MemFacts
  rw [hk, hea]
  exact ⟨⟨hlo, hhi, hht⟩, hp⟩

theorem memFactsLd {m : Mem} {L : GRegs} {a : MInstr} {bs : List (BitVec 8)}
    (base : Nat) (hk : a.kind = .ld) (hea : (eaddrM a L).toNat = base)
    (hlo : 0x80000000 ≤ base) (hhi : base + 8 ≤ 0x100000000)
    (hht : base + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ base)
    (hp : LPins8 m base bs) : MemFacts m L bs a := by
  unfold MemFacts
  rw [hk, hea]
  exact ⟨⟨hlo, hhi, hht⟩, hp⟩

private theorem memFactsSd {m : Mem} {L : GRegs} {a : MInstr} {bs : List (BitVec 8)}
    (base : Nat) (hk : a.kind = .sd) (hea : (eaddrM a L).toNat = base)
    (hlo : 0x80000000 ≤ base) (hhi : base + 8 ≤ 0x100000000)
    (hht : tohostAddr + 16 ≤ base) (hal : base % 8 = 0) : MemFacts m L bs a := by
  unfold MemFacts
  rw [hk, hea]
  exact ⟨hlo, hhi, hht, hal⟩

private theorem memFactsSw {m : Mem} {L : GRegs} {a : MInstr} {bs : List (BitVec 8)}
    (base : Nat) (hk : a.kind = .sw) (hea : (eaddrM a L).toNat = base)
    (hlo : 0x80000000 ≤ base) (hhi : base + 4 ≤ 0x100000000)
    (hht : tohostAddr + 16 ≤ base) (hal : base % 4 = 0) : MemFacts m L bs a := by
  unfold MemFacts
  rw [hk, hea]
  exact ⟨hlo, hhi, hht, hal⟩

theorem stepMemM_load {m : Mem} {a : MInstr} {L : GRegs} (hk : a.kind = .lw) :
    stepMemM m a L = m := by
  unfold stepMemM
  rw [hk]

private theorem stepMemM_sd_outside {m : Mem} {a : MInstr} {L : GRegs} (hk : a.kind = .sd)
    (x : Nat) (hx : x < (eaddrM a L).toNat ∨ (eaddrM a L).toNat + 8 ≤ x) :
    (stepMemM m a L)[x]? = m[x]? := by
  have h1 : stepMemM m a L = writeMap8 m (eaddrM a L).toNat (sdData_val (srcVal a.rs2 L)) := by
    unfold stepMemM wentryM
    rw [hk]
    rfl
  rw [h1]
  exact getElem_writeMap8_disjoint _ _ _ _ hx

theorem lpins8_of_agree {m m' : Mem} {a : Nat} {bs : List (BitVec 8)}
    (hag : ∀ k, k < 8 → m'[a + k]? = m[a + k]?) (h : LPins8 m a bs) : LPins8 m' a bs := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hag 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; exact h0
  · rw [hag 1 (by omega)]; exact h1
  · rw [hag 2 (by omega)]; exact h2
  · rw [hag 3 (by omega)]; exact h3
  · rw [hag 4 (by omega)]; exact h4
  · rw [hag 5 (by omega)]; exact h5
  · rw [hag 6 (by omega)]; exact h6
  · rw [hag 7 (by omega)]; exact h7

/-- The geometry every `Env` record access of the miss lanes needs: the
32-byte record is RAM above the HTIF window, 8-aligned, off the `env_define`
text. -/
structure EnvRecordGeom (env : BitVec 64) : Prop where
  lo : 0x80000000 ≤ env.toNat
  hi : env.toNat + 32 ≤ 0x100000000
  htif : tohostAddr + 16 ≤ env.toNat
  align : env.toNat % 8 = 0
  code : env.toNat + 32 ≤ 0x80002a5c ∨ 0x80002c10 ≤ env.toNat

/-! ## 2. `strlen` -/

#derive_case envDefineStrlenPreSeg chain
  [(0x80002b1c#64, 0x00090513#32)]

def envDefineStrlenPreL (name : BitVec 64) : GRegs := [(18, name)]

/-- Parked at `strlen`'s entry from the append head. -/
structure EnvDefineStrlenParked (name : BitVec 64) (c c' : Config) : Prop where
  steps : Steps c c'
  good : GoodState c'.σ
  tick : c'.tick < 2
  mem : c'.σ.mem = c.σ.mem
  pc : c'.σ.regs.get? Register.PC = some 0x80006cf0#64
  ra : c'.σ.regs.get? Register.x1 = some 0x80002b24#64
  a0 : c'.σ.regs.get? Register.x10 = some name
  minstret : ∃ w, c'.σ.regs.get? Register.minstret = some w
  abi : ∀ R, AbiPreserved R = true → c'.σ.regs.get? R = c.σ.regs.get? R
  out : c'.σ.sailOutput = c.σ.sailOutput

theorem envDefineStrlenParked_of (name : BitVec 64) (c : Config)
    (hG : GoodState c.σ) (hpc : c.σ.regs.get? Register.PC = some 0x80002b1c#64)
    (hname : c.σ.regs.get? Register.x18 = some name)
    (hloaded : Env_defineLoaded c.σ.mem) (htick : c.tick < 2) :
    ∃ c', EnvDefineStrlenParked name c c' := by
  have hL : GHolds c.σ (envDefineStrlenPreL name) := ⟨by simpa [gprGet] using hname, trivial⟩
  have hfacts : ChainFacts c.σ.mem c.σ.mem (envDefineStrlenPreL name) [] envDefineStrlenPreSeg := by
    chain_facts hloaded with "Vsa.Sim.Code.env_define_at_"
  have hmemLog : writeLog c.σ.mem (evalBlocks envDefineStrlenPreSeg
      (SegEvalState.init (envDefineStrlenPreL name) [])).log = c.σ.mem := rfl
  obtain ⟨after, S⟩ := envDefineSegCall envDefineStrlenPreSeg (envDefineStrlenPreL name) []
    0x80002b1c#64 0x80002b20#64 0x80006cf0#64 0x0041d0#21 c
    (fun σ i u vmi hG hpc hmi hmem hi => site_80002b20_ed σ i u _ vmi hG hpc hmi hmem rfl hi)
    (by apply BitVec.eq_of_toNat_eq; decide) hG hpc htick hL
    (by show KeysOK [18]; decide) hfacts
    (by show ChainOK 0x80002b1c#64 [18] envDefineStrlenPreSeg; decide)
    (by show KeysOK [10, 18]; decide)
    (by
      have h : keysG (evalBlocks envDefineStrlenPreSeg
        (SegEvalState.init (envDefineStrlenPreL name) [])).regs = [10, 18] := rfl
      show ∀ n ∈ keysG _, n ≠ 1
      rw [h]
      decide)
    rfl (by rw [hmemLog]; exact hloaded)
  have hx10 : gprGet after.σ 10 = some name := by
    apply gholds_lookup _ S.registers
    change some (name + sign_extend (m := 64) (0#12)) = some name
    rw [sext0_64, BitVec.add_zero]
  refine ⟨after, S.run, S.good, S.tick, S.mem.trans hmemLog, S.pc, S.ra, ?_, S.minstret, ?_,
    S.output⟩
  · simpa [gprGet] using hx10
  · exact segCallFrame abiPreserved_noise
      (by show WrChainAvoids AbiPreserved envDefineStrlenPreSeg; decide) (by decide) S.frame

/-! ## 3. `malloc` -/

#derive_case envDefineMallocPreSeg chain
  [(0x80002b24#64, 0x00150413#32),
   (0x80002b28#64, 0x00040513#32)]

def envDefineMallocPreL (len : BitVec 64) : GRegs := [(10, len)]

/-- `abiButS0` (`TruthyCopy.lean`): the ABI frame but `s0`, which the malloc
prefix rewrites with the size. -/
theorem abiButS0_abi {R : Register} (h : abiButS0 R = true) : AbiPreserved R = true :=
  (Bool.and_eq_true _ _).mp h |>.1

/-- Parked at `malloc`'s entry after `strlen` returned `len`. -/
structure EnvDefineMallocParked (len : Nat) (c c' : Config) : Prop where
  steps : Steps c c'
  good : GoodState c'.σ
  tick : c'.tick < 2
  mem : c'.σ.mem = c.σ.mem
  pc : c'.σ.regs.get? Register.PC = some (BitVec.ofNat 64 Vsa.Alloc.mallocEntry)
  ra : c'.σ.regs.get? Register.x1 = some 0x80002b30#64
  a0 : c'.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 (len + 1))
  s0 : c'.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 (len + 1))
  minstret : ∃ w, c'.σ.regs.get? Register.minstret = some w
  abi : ∀ R, abiButS0 R = true → c'.σ.regs.get? R = c.σ.regs.get? R
  out : c'.σ.sailOutput = c.σ.sailOutput

theorem envDefineMallocParked_of (len : Nat) (c : Config) (hlen : len + 1 < 2^64)
    (hG : GoodState c.σ) (hpc : c.σ.regs.get? Register.PC = some 0x80002b24#64)
    (ha0 : c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 len))
    (hloaded : Env_defineLoaded c.σ.mem) (htick : c.tick < 2) :
    ∃ c', EnvDefineMallocParked len c c' := by
  have hL : GHolds c.σ (envDefineMallocPreL (BitVec.ofNat 64 len)) :=
    ⟨by simpa [gprGet] using ha0, trivial⟩
  have hfacts : ChainFacts c.σ.mem c.σ.mem (envDefineMallocPreL (BitVec.ofNat 64 len)) []
      envDefineMallocPreSeg := by
    chain_facts hloaded with "Vsa.Sim.Code.env_define_at_"
  have hmemLog : writeLog c.σ.mem (evalBlocks envDefineMallocPreSeg
      (SegEvalState.init (envDefineMallocPreL (BitVec.ofNat 64 len)) [])).log = c.σ.mem := rfl
  have hlen1 : BitVec.ofNat 64 len + sign_extend (m := 64) (0x001#12) = BitVec.ofNat 64 (len + 1) := by
    rw [sext1_64]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
    omega
  obtain ⟨after, S⟩ := envDefineSegCall envDefineMallocPreSeg
    (envDefineMallocPreL (BitVec.ofNat 64 len)) []
    0x80002b24#64 0x80002b2c#64 (BitVec.ofNat 64 Vsa.Alloc.mallocEntry) 0x001c64#21 c
    (fun σ i u vmi hG hpc hmi hmem hi => site_80002b2c_ed σ i u _ vmi hG hpc hmi hmem rfl hi)
    (by apply BitVec.eq_of_toNat_eq; decide) hG hpc htick hL
    (by show KeysOK [10]; decide) hfacts
    (by show ChainOK 0x80002b24#64 [10] envDefineMallocPreSeg; decide)
    (by show KeysOK [10, 8]; decide)
    (by
      have h : keysG (evalBlocks envDefineMallocPreSeg
        (SegEvalState.init (envDefineMallocPreL (BitVec.ofNat 64 len)) [])).regs = [10, 8] := rfl
      show ∀ n ∈ keysG _, n ≠ 1
      rw [h]
      decide)
    rfl (by rw [hmemLog]; exact hloaded)
  have hx10 : gprGet after.σ 10 = some (BitVec.ofNat 64 (len + 1)) := by
    apply gholds_lookup _ S.registers
    change some ((BitVec.ofNat 64 len + sign_extend (m := 64) (0x001#12)) +
      sign_extend (m := 64) (0x000#12)) = _
    rw [sext0_64, BitVec.add_zero, hlen1]
  have hx8 : gprGet after.σ 8 = some (BitVec.ofNat 64 (len + 1)) := by
    apply gholds_lookup _ S.registers
    change some (BitVec.ofNat 64 len + sign_extend (m := 64) (0x001#12)) = _
    rw [hlen1]
  refine ⟨after, S.run, S.good, S.tick, S.mem.trans hmemLog, S.pc, S.ra, ?_, ?_, S.minstret, ?_,
    S.output⟩
  · simpa [gprGet] using hx10
  · simpa [gprGet] using hx8
  · exact segCallFrame (by show ∀ rr ∈ noiseRegs, abiButS0 rr = false; decide)
      (by show WrChainAvoids abiButS0 envDefineMallocPreSeg; decide) (by decide) S.frame

/-! ## 4. `memcpy` -/

/-- Parked at `memcpy`'s entry after `malloc` returned the copy block. -/
structure EnvDefineMemcpyParked (copy size name : BitVec 64) (c c' : Config) : Prop where
  steps : Steps c c'
  good : GoodState c'.σ
  tick : c'.tick < 2
  mem : c'.σ.mem = c.σ.mem
  pc : c'.σ.regs.get? Register.PC = some 0x80006bc8#64
  ra : c'.σ.regs.get? Register.x1 = some 0x80002b44#64
  a0 : c'.σ.regs.get? Register.x10 = some copy
  a1 : c'.σ.regs.get? Register.x11 = some name
  a2 : c'.σ.regs.get? Register.x12 = some size
  s1 : c'.σ.regs.get? Register.x9 = some copy
  minstret : ∃ w, c'.σ.regs.get? Register.minstret = some w
  abi : ∀ R, AbiExceptS1 R = true → c'.σ.regs.get? R = c.σ.regs.get? R
  out : c'.σ.sailOutput = c.σ.sailOutput

theorem envDefineMemcpyParked_of (copy size name : BitVec 64) (c : Config)
    (hcopy : copy ≠ 0#64)
    (hG : GoodState c.σ) (hpc : c.σ.regs.get? Register.PC = some 0x80002b30#64)
    (ha0 : c.σ.regs.get? Register.x10 = some copy)
    (hs0 : c.σ.regs.get? Register.x8 = some size)
    (hs2 : c.σ.regs.get? Register.x18 = some name)
    (hloaded : Env_defineLoaded c.σ.mem) (htick : c.tick < 2) :
    ∃ c', EnvDefineMemcpyParked copy size name c c' := by
  have hL : GHolds c.σ (envDefineMemcpyArgL copy size name) :=
    ⟨by simpa [gprGet] using ha0, by simpa [gprGet] using hs0, by simpa [gprGet] using hs2,
      trivial⟩
  have hfacts : ChainFacts c.σ.mem c.σ.mem (envDefineMemcpyArgL copy size name) []
      envDefineMemcpyArgSeg := by
    chain_facts hloaded with "Vsa.Sim.Code.env_define_at_"
    · change guardB bop.BEQ copy 0#64 = false
      simp [guardB, hcopy]
  have hmemLog : writeLog c.σ.mem (evalBlocks envDefineMemcpyArgSeg
      (SegEvalState.init (envDefineMemcpyArgL copy size name) [])).log = c.σ.mem := rfl
  obtain ⟨after, S⟩ := envDefineSegCall envDefineMemcpyArgSeg
    (envDefineMemcpyArgL copy size name) []
    0x80002b30#64 0x80002b40#64 0x80006bc8#64 0x004088#21 c
    (fun σ i u vmi hG hpc hmi hmem hi => envDefineMemcpyJal σ i u vmi hG hpc hmi hmem hi)
    (by apply BitVec.eq_of_toNat_eq; decide) hG hpc htick hL
    (by show KeysOK [10, 8, 18]; decide) hfacts
    (by show ChainOK 0x80002b30#64 [10, 8, 18] envDefineMemcpyArgSeg; decide)
    (by show KeysOK [11, 12, 9, 10, 8, 18]; decide)
    (by
      have h : keysG (evalBlocks envDefineMemcpyArgSeg
        (SegEvalState.init (envDefineMemcpyArgL copy size name) [])).regs =
          [11, 12, 9, 10, 8, 18] := rfl
      show ∀ n ∈ keysG _, n ≠ 1
      rw [h]
      decide)
    rfl (by rw [hmemLog]; exact hloaded)
  have reg (n : Nat) (w : BitVec 64)
      (hl : lookupG n (evalBlocks envDefineMemcpyArgSeg
        (SegEvalState.init (envDefineMemcpyArgL copy size name) [])).regs = some w) :
      gprGet after.σ n = some w := gholds_lookup _ S.registers hl
  have hx10 := reg 10 copy rfl
  have hx11 : gprGet after.σ 11 = some name := reg 11 name (by
    change some (name + sign_extend (m := 64) (0#12)) = some name
    rw [sext0_64, BitVec.add_zero])
  have hx12 : gprGet after.σ 12 = some size := reg 12 size (by
    change some (size + sign_extend (m := 64) (0#12)) = some size
    rw [sext0_64, BitVec.add_zero])
  have hx9 : gprGet after.σ 9 = some copy := reg 9 copy (by
    change some (copy + sign_extend (m := 64) (0#12)) = some copy
    rw [sext0_64, BitVec.add_zero])
  refine ⟨after, S.run, S.good, S.tick, S.mem.trans hmemLog, S.pc, S.ra, ?_, ?_, ?_, ?_,
    S.minstret, ?_, S.output⟩
  · simpa [gprGet] using hx10
  · simpa [gprGet] using hx11
  · simpa [gprGet] using hx12
  · simpa [gprGet] using hx9
  · exact segCallFrame (by show ∀ rr ∈ noiseRegs, AbiExceptS1 rr = false; decide)
      (by show WrChainAvoids AbiExceptS1 envDefineMemcpyArgSeg; decide) (by decide) S.frame

/-! ## 5. `realloc(names)` — from the grow arm or the empty frame -/

#derive_case envDefineGrowPreSeg chain
  [(0x80002b90#64, 0x0017979b#32),
   (0x80002b94#64, 0x00379593#32),
   (0x80002b98#64, 0x00fa2223#32),
   (0x80002b9c#64, 0x000b0513#32)]

#derive_case envDefineInitPreSeg chain
  [(0x80002b98#64, 0x00fa2223#32),
   (0x80002b9c#64, 0x000b0513#32)]

def envDefineGrowPreL (capReg env names : BitVec 64) : GRegs :=
  [(15, capReg), (20, env), (22, names)]

def envDefineInitPreL (env names : BitVec 64) : GRegs :=
  [(15, 8#64), (11, 64#64), (20, env), (22, names)]

/-- Parked at `realloc`'s entry for the names array, with `cap'` stored. -/
structure EnvDefineReallocNamesParked (env names : BitVec 64) (cap' : Nat) (c c' : Config) :
    Prop where
  steps : Steps c c'
  good : GoodState c'.σ
  tick : c'.tick < 2
  mem : c'.σ.mem = writeMap4 c.σ.mem (env.toNat + 4) (swData (BitVec.ofNat 64 cap'))
  pc : c'.σ.regs.get? Register.PC = some (BitVec.ofNat 64 reallocEntry)
  ra : c'.σ.regs.get? Register.x1 = some 0x80002ba4#64
  a0 : c'.σ.regs.get? Register.x10 = some names
  a1 : c'.σ.regs.get? Register.x11 = some (BitVec.ofNat 64 (8 * cap'))
  minstret : ∃ w, c'.σ.regs.get? Register.minstret = some w
  abi : ∀ R, AbiPreserved R = true → c'.σ.regs.get? R = c.σ.regs.get? R
  out : c'.σ.sailOutput = c.σ.sailOutput

/-- `slliw a5,a5,1` on a small capacity. -/
theorem slliw_ofNat (cap : Nat) (h : cap < 2^30) :
    sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb (BitVec.ofNat 64 cap) 31 0)
        (1#5 : BitVec 5)) = BitVec.ofNat 64 (2 * cap) := by
  simp only [shift_bits_left]
  have hx : (Sail.BitVec.extractLsb (BitVec.ofNat 64 cap) 31 0 <<< (1#5 : BitVec 5)).toNat
      = 2 * cap := by
    rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', BitVec.toNat_ofNat,
      Nat.shiftRight_zero, Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMod, Nat.reduceSub,
      Nat.reduceAdd]
    omega
  apply BitVec.eq_of_toNat_eq
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend]
  have hmsb : (Sail.BitVec.extractLsb (BitVec.ofNat 64 cap) 31 0 <<< (1#5 : BitVec 5)).msb
      = false := by
    rw [BitVec.msb_eq_decide]
    simp only [decide_eq_false_iff_not, Nat.not_le]
    rw [hx]; omega
  rw [hmsb]
  simp only [Bool.false_eq_true, if_false, Nat.add_zero, BitVec.toNat_setWidth]
  rw [hx, BitVec.toNat_ofNat]

/-- `slli rd,rs,3` as the `8 *` stride. -/
theorem shl3_ofNat (k : Nat) (h : 8 * k < 2^64) :
    shift_bits_left (BitVec.ofNat 64 k) (Sail.BitVec.extractLsb (0x03#6) 5 0) =
      BitVec.ofNat 64 (8 * k) := by
  rw [shl3_lit]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show k < 2^64 by omega)]
  simp only [Nat.reducePow]
  omega

theorem envDefineReallocNamesParked_grow (env names : BitVec 64) (cap : Nat) (c : Config)
    (hcap : cap < 2^30) (hgeom : EnvRecordGeom env)
    (hG : GoodState c.σ) (hpc : c.σ.regs.get? Register.PC = some 0x80002b90#64)
    (ha5 : c.σ.regs.get? Register.x15 = some (BitVec.ofNat 64 cap))
    (hs4 : c.σ.regs.get? Register.x20 = some env)
    (hs6 : c.σ.regs.get? Register.x22 = some names)
    (hloaded : Env_defineLoaded c.σ.mem) (htick : c.tick < 2) :
    ∃ c', EnvDefineReallocNamesParked env names (2 * cap) c c' := by
  have hL : GHolds c.σ (envDefineGrowPreL (BitVec.ofNat 64 cap) env names) :=
    ⟨by simpa [gprGet] using ha5, by simpa [gprGet] using hs4, by simpa [gprGet] using hs6,
      trivial⟩
  have henv4 : (env + sign_extend (m := 64) (0x004#12)).toNat = env.toNat + 4 := by
    rw [BitVec.toNat_add, sext4_64, Nat.mod_eq_of_lt (by have := hgeom.hi; omega)]
  have hfacts : ChainFacts c.σ.mem c.σ.mem (envDefineGrowPreL (BitVec.ofNat 64 cap) env names) []
      envDefineGrowPreSeg := by
    chain_facts hloaded with "Vsa.Sim.Code.env_define_at_"
    · refine memFactsSw (env.toNat + 4) (by decide) ?_ (by have := hgeom.lo; omega)
        (by have := hgeom.hi; omega) (by have := hgeom.htif; omega)
        (by have := hgeom.align; omega)
      simpa +ground [eaddrM, envDefineGrowPreL, srcVal, lookupG, eraseG, stepGM] using henv4
  have hmemLog : writeLog c.σ.mem (evalBlocks envDefineGrowPreSeg
      (SegEvalState.init (envDefineGrowPreL (BitVec.ofNat 64 cap) env names) [])).log =
      writeMap4 c.σ.mem (env.toNat + 4) (swData (BitVec.ofNat 64 (2 * cap))) := by
    simp [envDefineGrowPreSeg, evalBlocks, evalBlock, SegEvalState.init, wlogM, wentryM,
      widthOfM, runGM, stepGM, wvalM, srcVal, lookupG, eaddrM, mkLine, decodeM,
      envDefineGrowPreL, eraseG, writeLog, applyW, shamt5Of]
    rw [sext4_64, Nat.mod_eq_of_lt (by have := hgeom.hi; omega), slliw_ofNat cap hcap]
  have hcodeAgree : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 →
      (writeMap4 c.σ.mem (env.toNat + 4) (swData (BitVec.ofNat 64 (2 * cap))))[a]? =
        c.σ.mem[a]? := by
    intro a ha0 ha1
    apply getElem_writeMap4_disjoint
    rcases hgeom.code with h | h <;> omega
  obtain ⟨after, S⟩ := envDefineSegCall envDefineGrowPreSeg
    (envDefineGrowPreL (BitVec.ofNat 64 cap) env names) []
    0x80002b90#64 0x80002ba0#64 (BitVec.ofNat 64 reallocEntry) 0x0026dc#21 c
    (fun σ i u vmi hG hpc hmi hmem hi => site_80002ba0_ed σ i u _ vmi hG hpc hmi hmem rfl hi)
    (by apply BitVec.eq_of_toNat_eq; decide) hG hpc htick hL
    (by show KeysOK [15, 20, 22]; decide) hfacts
    (by show ChainOK 0x80002b90#64 [15, 20, 22] envDefineGrowPreSeg; decide)
    (by show KeysOK [10, 11, 15, 20, 22]; decide)
    (by
      have h : keysG (evalBlocks envDefineGrowPreSeg
        (SegEvalState.init (envDefineGrowPreL (BitVec.ofNat 64 cap) env names) [])).regs =
          [10, 11, 15, 20, 22] := rfl
      show ∀ n ∈ keysG _, n ≠ 1
      rw [h]
      decide)
    rfl (by rw [hmemLog]; exact envDefineLoaded_of_agree _ _ hcodeAgree hloaded)
  have reg (n : Nat) (w : BitVec 64)
      (hl : lookupG n (evalBlocks envDefineGrowPreSeg
        (SegEvalState.init (envDefineGrowPreL (BitVec.ofNat 64 cap) env names) [])).regs
          = some w) :
      gprGet after.σ n = some w := gholds_lookup _ S.registers hl
  have hx10 : gprGet after.σ 10 = some names := reg 10 names (by
    change some (names + sign_extend (m := 64) (0#12)) = some names
    rw [sext0_64, BitVec.add_zero])
  have hx11 : gprGet after.σ 11 = some (BitVec.ofNat 64 (8 * (2 * cap))) := reg 11 _ (by
    change some (shift_bits_left (sign_extend (m := 64)
      (shift_bits_left (Sail.BitVec.extractLsb (BitVec.ofNat 64 cap) 31 0)
        (shamt5Of (mkLine 0x80002b90#64 0x0017979b#32))))
      (Sail.BitVec.extractLsb (shamtOf (mkLine 0x80002b94#64 0x00379593#32)) 5 0)) = _
    rw [show shamt5Of (mkLine 0x80002b90#64 0x0017979b#32) = (1#5 : BitVec 5) by decide,
      show Sail.BitVec.extractLsb (shamtOf (mkLine 0x80002b94#64 0x00379593#32)) 5 0 =
        Sail.BitVec.extractLsb (0x03#6) 5 0 by decide,
      slliw_ofNat cap hcap, shl3_ofNat (2 * cap) (by omega)])
  refine ⟨after, S.run, S.good, S.tick, S.mem.trans hmemLog, S.pc, S.ra, ?_, ?_, S.minstret, ?_,
    S.output⟩
  · simpa [gprGet] using hx10
  · simpa [gprGet] using hx11
  · exact segCallFrame abiPreserved_noise
      (by show WrChainAvoids AbiPreserved envDefineGrowPreSeg; decide) (by decide) S.frame

theorem envDefineReallocNamesParked_init (env names : BitVec 64) (c : Config)
    (hgeom : EnvRecordGeom env)
    (hG : GoodState c.σ) (hpc : c.σ.regs.get? Register.PC = some 0x80002b98#64)
    (ha5 : c.σ.regs.get? Register.x15 = some 8#64)
    (ha1 : c.σ.regs.get? Register.x11 = some 64#64)
    (hs4 : c.σ.regs.get? Register.x20 = some env)
    (hs6 : c.σ.regs.get? Register.x22 = some names)
    (hloaded : Env_defineLoaded c.σ.mem) (htick : c.tick < 2) :
    ∃ c', EnvDefineReallocNamesParked env names 8 c c' := by
  have hL : GHolds c.σ (envDefineInitPreL env names) :=
    ⟨by simpa [gprGet] using ha5, by simpa [gprGet] using ha1, by simpa [gprGet] using hs4,
      by simpa [gprGet] using hs6, trivial⟩
  have henv4 : (env + sign_extend (m := 64) (0x004#12)).toNat = env.toNat + 4 := by
    rw [BitVec.toNat_add, sext4_64, Nat.mod_eq_of_lt (by have := hgeom.hi; omega)]
  have hfacts : ChainFacts c.σ.mem c.σ.mem (envDefineInitPreL env names) []
      envDefineInitPreSeg := by
    chain_facts hloaded with "Vsa.Sim.Code.env_define_at_"
    · refine memFactsSw (env.toNat + 4) (by decide) ?_ (by have := hgeom.lo; omega)
        (by have := hgeom.hi; omega) (by have := hgeom.htif; omega)
        (by have := hgeom.align; omega)
      simpa +ground [eaddrM, envDefineInitPreL, srcVal, lookupG, eraseG, stepGM] using henv4
  have hmemLog : writeLog c.σ.mem (evalBlocks envDefineInitPreSeg
      (SegEvalState.init (envDefineInitPreL env names) [])).log =
      writeMap4 c.σ.mem (env.toNat + 4) (swData (BitVec.ofNat 64 8)) := by
    simp [envDefineInitPreSeg, evalBlocks, evalBlock, SegEvalState.init, wlogM, wentryM,
      widthOfM, runGM, stepGM, wvalM, srcVal, lookupG, eaddrM, mkLine, decodeM,
      envDefineInitPreL, eraseG, writeLog, applyW]
    rw [sext4_64, Nat.mod_eq_of_lt (by have := hgeom.hi; omega)]
  have hcodeAgree : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 →
      (writeMap4 c.σ.mem (env.toNat + 4) (swData (BitVec.ofNat 64 8)))[a]? = c.σ.mem[a]? := by
    intro a ha0 ha1
    apply getElem_writeMap4_disjoint
    rcases hgeom.code with h | h <;> omega
  obtain ⟨after, S⟩ := envDefineSegCall envDefineInitPreSeg (envDefineInitPreL env names) []
    0x80002b98#64 0x80002ba0#64 (BitVec.ofNat 64 reallocEntry) 0x0026dc#21 c
    (fun σ i u vmi hG hpc hmi hmem hi => site_80002ba0_ed σ i u _ vmi hG hpc hmi hmem rfl hi)
    (by apply BitVec.eq_of_toNat_eq; decide) hG hpc htick hL
    (by show KeysOK [15, 11, 20, 22]; decide) hfacts
    (by show ChainOK 0x80002b98#64 [15, 11, 20, 22] envDefineInitPreSeg; decide)
    (by show KeysOK [10, 15, 11, 20, 22]; decide)
    (by
      have h : keysG (evalBlocks envDefineInitPreSeg
        (SegEvalState.init (envDefineInitPreL env names) [])).regs = [10, 15, 11, 20, 22] := rfl
      show ∀ n ∈ keysG _, n ≠ 1
      rw [h]
      decide)
    rfl (by rw [hmemLog]; exact envDefineLoaded_of_agree _ _ hcodeAgree hloaded)
  have reg (n : Nat) (w : BitVec 64)
      (hl : lookupG n (evalBlocks envDefineInitPreSeg
        (SegEvalState.init (envDefineInitPreL env names) [])).regs = some w) :
      gprGet after.σ n = some w := gholds_lookup _ S.registers hl
  have hx10 : gprGet after.σ 10 = some names := reg 10 names (by
    change some (names + sign_extend (m := 64) (0#12)) = some names
    rw [sext0_64, BitVec.add_zero])
  have hx11 : gprGet after.σ 11 = some (BitVec.ofNat 64 (8 * 8)) := reg 11 _ rfl
  refine ⟨after, S.run, S.good, S.tick, S.mem.trans hmemLog, S.pc, S.ra, ?_, ?_, S.minstret, ?_,
    S.output⟩
  · simpa [gprGet] using hx10
  · simpa [gprGet] using hx11
  · exact segCallFrame abiPreserved_noise
      (by show WrChainAvoids AbiPreserved envDefineInitPreSeg; decide) (by decide) S.frame

/-! ## 6. `realloc(vals)` -/

#derive_case envDefineValsPreSeg chain
  [(0x80002ba4#64, 0x004a2783#32),
   (0x80002ba8#64, 0x00aa3423#32),
   (0x80002bac#64, 0x010a3503#32),
   (0x80002bb0#64, 0x00179593#32),
   (0x80002bb4#64, 0x00f585b3#32),
   (0x80002bb8#64, 0x00359593#32)]

def envDefineValsPreL (env pn : BitVec 64) : GRegs := [(20, env), (10, pn)]

/-- Parked at `realloc`'s entry for the values array, with the new names
pointer stored. -/
structure EnvDefineReallocValsParked (env pn : BitVec 64) (cap' pv : Nat) (c c' : Config) :
    Prop where
  steps : Steps c c'
  good : GoodState c'.σ
  tick : c'.tick < 2
  mem : c'.σ.mem = writeMap8 c.σ.mem (env.toNat + 8) (sdData_val pn)
  pc : c'.σ.regs.get? Register.PC = some (BitVec.ofNat 64 reallocEntry)
  ra : c'.σ.regs.get? Register.x1 = some 0x80002bc0#64
  a0 : c'.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 pv)
  a1 : c'.σ.regs.get? Register.x11 = some (BitVec.ofNat 64 (24 * cap'))
  minstret : ∃ w, c'.σ.regs.get? Register.minstret = some w
  abi : ∀ R, AbiPreserved R = true → c'.σ.regs.get? R = c.σ.regs.get? R
  out : c'.σ.sailOutput = c.σ.sailOutput

theorem envDefineReallocValsParked_of (env pn : BitVec 64) (cap' pv : Nat) (c : Config)
    (hgeom : EnvRecordGeom env) (hcapS : cap' < 2^31)
    (hcap : read32 c.σ.mem (env.toNat + 4) = some cap')
    (hpv : read64 c.σ.mem (env.toNat + 16) = some pv)
    (hG : GoodState c.σ) (hpc : c.σ.regs.get? Register.PC = some 0x80002ba4#64)
    (ha0 : c.σ.regs.get? Register.x10 = some pn)
    (hs4 : c.σ.regs.get? Register.x20 = some env)
    (hloaded : Env_defineLoaded c.σ.mem) (htick : c.tick < 2) :
    ∃ c', EnvDefineReallocValsParked env pn cap' pv c c' := by
  obtain ⟨c0, c1, c2, c3, hc0, hc1, hc2, hc3, hcRe⟩ := read32_bytes c.σ.mem (env.toNat + 4) cap' hcap
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, _⟩ :=
    read64_bytes_eg4 c.σ.mem (env.toNat + 16) pv hpv
  let lds : List (List (BitVec 8)) := [[c0, c1, c2, c3], [d0, d1, d2, d3, d4, d5, d6, d7]]
  have hpins4 : LPins4 c.σ.mem (env.toNat + 4) [c0, c1, c2, c3] :=
    ⟨lpin_of_present hc0, lpin_of_present hc1, lpin_of_present hc2, lpin_of_present hc3⟩
  have hpins8 : LPins8 c.σ.mem (env.toNat + 16) [d0, d1, d2, d3, d4, d5, d6, d7] :=
    ⟨lpin_of_present hd0, lpin_of_present hd1, lpin_of_present hd2, lpin_of_present hd3,
      lpin_of_present hd4, lpin_of_present hd5, lpin_of_present hd6, lpin_of_present hd7⟩
  have hcapWord : bytesVal .lw [c0, c1, c2, c3] = BitVec.ofNat 64 cap' := by
    simpa [bytesVal] using sext_count_ed c0 c1 c2 c3 cap' hcapS hcRe
  have hpvWord : bytesVal .ld [d0, d1, d2, d3, d4, d5, d6, d7] = BitVec.ofNat 64 pv := by
    simpa [bytesVal] using
      ld_value_eq_read64 c.σ.mem (env.toNat + 16) pv d0 d1 d2 d3 d4 d5 d6 d7 hpv
        hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd7
  have hL : GHolds c.σ (envDefineValsPreL env pn) :=
    ⟨by simpa [gprGet] using hs4, by simpa [gprGet] using ha0, trivial⟩
  have henv4 : (env + sign_extend (m := 64) (0x004#12)).toNat = env.toNat + 4 := by
    rw [BitVec.toNat_add, sext4_64, Nat.mod_eq_of_lt (by have := hgeom.hi; omega)]
  have henv8 : (env + sign_extend (m := 64) (0x008#12)).toNat = env.toNat + 8 := by
    rw [BitVec.toNat_add, sext8_64, Nat.mod_eq_of_lt (by have := hgeom.hi; omega)]
  have henv16 : (env + sign_extend (m := 64) (0x010#12)).toNat = env.toNat + 16 := by
    rw [BitVec.toNat_add, sext16_64, Nat.mod_eq_of_lt (by have := hgeom.hi; omega)]
  have hfacts : ChainFacts c.σ.mem c.σ.mem (envDefineValsPreL env pn) lds
      envDefineValsPreSeg := by
    chain_facts hloaded with "Vsa.Sim.Code.env_define_at_"
    · refine memFactsLw (env.toNat + 4) (by decide) ?_ (by have := hgeom.lo; omega)
        (by have := hgeom.hi; omega) (by right; have := hgeom.htif; omega) ?_
      · simpa +ground [eaddrM, envDefineValsPreL, srcVal, lookupG] using henv4
      · simpa [lds] using hpins4
    · refine memFactsSd (env.toNat + 8) (by decide) ?_ (by have := hgeom.lo; omega)
        (by have := hgeom.hi; omega) (by have := hgeom.htif; omega)
        (by have := hgeom.align; omega)
      simpa [eaddrM, envDefineValsPreL, srcVal, lookupG, eraseG, stepGM, wvalM, stepLdsM,
        mkLine, decodeM, lds] using henv8
    · refine memFactsLd (env.toNat + 16) (by decide) ?_ (by have := hgeom.lo; omega)
        (by have := hgeom.hi; omega) (by right; have := hgeom.htif; omega) ?_
      · simpa [eaddrM, envDefineValsPreL, srcVal, lookupG, eraseG, stepGM, wvalM, stepLdsM,
          mkLine, decodeM, lds] using henv16
      · refine lpins8_of_agree ?_ (by simpa +ground [lds, stepLdsM] using hpins8)
        intro k hk
        rw [stepMemM_sd_outside (by decide) _ (by
          simp [eaddrM, envDefineValsPreL, srcVal, lookupG, eraseG, stepGM, wvalM, stepLdsM,
            mkLine, decodeM, lds]
          rw [Nat.mod_eq_of_lt (by have := hgeom.hi; omega)]
          omega), stepMemM_load (by decide)]
  have hmemLog : writeLog c.σ.mem (evalBlocks envDefineValsPreSeg
      (SegEvalState.init (envDefineValsPreL env pn) lds)).log =
      writeMap8 c.σ.mem (env.toNat + 8) (sdData_val pn) := by
    simp [envDefineValsPreSeg, evalBlocks, evalBlock, SegEvalState.init, wlogM, wentryM,
      widthOfM, runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eaddrM, mkLine, decodeM,
      envDefineValsPreL, eraseG, writeLog, applyW, lds]
    rw [Nat.mod_eq_of_lt (by have := hgeom.hi; omega)]
  have hcodeAgree : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 →
      (writeMap8 c.σ.mem (env.toNat + 8) (sdData_val pn))[a]? = c.σ.mem[a]? := by
    intro a ha0 ha1
    apply getElem_writeMap8_disjoint
    rcases hgeom.code with h | h <;> omega
  obtain ⟨after, S⟩ := envDefineSegCall envDefineValsPreSeg (envDefineValsPreL env pn) lds
    0x80002ba4#64 0x80002bbc#64 (BitVec.ofNat 64 reallocEntry) 0x0026c0#21 c
    (fun σ i u vmi hG hpc hmi hmem hi => site_80002bbc_ed σ i u _ vmi hG hpc hmi hmem rfl hi)
    (by apply BitVec.eq_of_toNat_eq; decide) hG hpc htick hL
    (by show KeysOK [20, 10]; decide) hfacts
    (by show ChainOK 0x80002ba4#64 [20, 10] envDefineValsPreSeg; decide)
    (by show KeysOK [11, 10, 15, 20]; decide)
    (by
      have h : keysG (evalBlocks envDefineValsPreSeg
        (SegEvalState.init (envDefineValsPreL env pn) lds)).regs = [11, 10, 15, 20] := rfl
      show ∀ n ∈ keysG _, n ≠ 1
      rw [h]
      decide)
    rfl (by rw [hmemLog]; exact envDefineLoaded_of_agree _ _ hcodeAgree hloaded)
  have reg (n : Nat) (w : BitVec 64)
      (hl : lookupG n (evalBlocks envDefineValsPreSeg
        (SegEvalState.init (envDefineValsPreL env pn) lds)).regs = some w) :
      gprGet after.σ n = some w := gholds_lookup _ S.registers hl
  have hx10 : gprGet after.σ 10 = some (BitVec.ofNat 64 pv) := reg 10 _ (by
    simp [envDefineValsPreSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,
      stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG, envDefineValsPreL, mkLine, decodeM,
      shamtOf, bytesVal, lds]
    simpa [bytesVal] using hpvWord)
  have hx11 : gprGet after.σ 11 = some (BitVec.ofNat 64 (24 * cap')) := reg 11 _ (by
    simp [envDefineValsPreSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,
      stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG, envDefineValsPreL, mkLine, decodeM,
      shamtOf, lds]
    rw [hcapWord]
    exact stride_24 cap' (by omega))
  refine ⟨after, S.run, S.good, S.tick, S.mem.trans hmemLog, S.pc, S.ra, ?_, ?_, S.minstret, ?_,
    S.output⟩
  · simpa [gprGet] using hx10
  · simpa [gprGet] using hx11
  · exact segCallFrame abiPreserved_noise
      (by show WrChainAvoids AbiPreserved envDefineValsPreSeg; decide) (by decide) S.frame

/-! ## 7. The rejoin `0x80002bc0` → `0x80002b1c` -/

/-- Parked at the append head after the reflected rejoin. -/
structure EnvDefineRejoinDone (env valsNew : BitVec 64) (c c' : Config) : Prop where
  steps : Steps c c'
  good : GoodState c'.σ
  tick : c'.tick < 2
  mem : c'.σ.mem = writeMap8 c.σ.mem (env.toNat + 16) (sdData_val valsNew)
  pc : c'.σ.regs.get? Register.PC = some 0x80002b1c#64
  minstret : ∃ w, c'.σ.regs.get? Register.minstret = some w
  abi : ∀ R, AbiPreserved R = true → c'.σ.regs.get? R = c.σ.regs.get? R
  out : c'.σ.sailOutput = c.σ.sailOutput

theorem envDefineRejoinDone_of (env names valsNew : BitVec 64) (c : Config)
    (hgeom : EnvRecordGeom env)
    (hnames : read64 c.σ.mem (env.toNat + 8) = some names.toNat)
    (hnz : names ≠ 0#64) (hvz : valsNew ≠ 0#64)
    (hG : GoodState c.σ) (hpc : c.σ.regs.get? Register.PC = some 0x80002bc0#64)
    (ha0 : c.σ.regs.get? Register.x10 = some valsNew)
    (hs4 : c.σ.regs.get? Register.x20 = some env)
    (hloaded : Env_defineLoaded c.σ.mem) (htick : c.tick < 2) :
    ∃ c', EnvDefineRejoinDone env valsNew c c' := by
  have hentry : AppendHeadGeom env names valsNew c.σ.mem :=
    ⟨hnames, hnz, hvz, by have := hgeom.hi; omega, by have := hgeom.lo; omega,
      by have := hgeom.hi; omega, Or.inr (by have := hgeom.htif; omega),
      by have := hgeom.align; omega, by have := hgeom.lo; omega, by have := hgeom.hi; omega,
      by have := hgeom.htif; omega, by have := hgeom.align; omega⟩
  obtain ⟨lds, hfacts⟩ := appendHeadFacts env names valsNew c.σ.mem hloaded hentry
  have hL : GHolds c.σ (appendHeadL env valsNew) :=
    ⟨by simpa [gprGet] using hs4, by simpa [gprGet] using ha0, trivial⟩
  obtain ⟨vm, hvm⟩ := hG.minstret
  obtain ⟨σ', i', hs, hi', hG', hmem', hout, hpc', hmi', _, hframe⟩ :=
    segEval_sound appendHeadSeg c.σ c.tick c.steps 0x80002bc0#64 vm (appendHeadL env valsNew)
      lds hG hpc hvm hL (by show KeysOK [20, 10]; decide) hfacts
      (by show ChainOK 0x80002bc0#64 [20, 10] appendHeadSeg; decide) htick
  refine ⟨⟨σ', i', c.steps + evalBlocksFuel appendHeadSeg⟩, hs, hG', hi', ?_, ?_, hmi', ?_, hout⟩
  · show σ'.mem = _
    rw [hmem', appendHeadMemoryExact env valsNew lds c.σ.mem (by have := hgeom.hi; omega)]
  · show σ'.regs.get? Register.PC = _
    rw [hpc']
    rfl
  · exact frame_of_wrChain_avoids_abi (by show WrChainAvoidAbi appendHeadSeg; decide) hframe

#print axioms envDefineSegCall
#print axioms envDefineMemcpyJal
#print axioms envDefineStrlenParked_of
#print axioms envDefineMallocParked_of
#print axioms envDefineMemcpyParked_of
#print axioms slliw_ofNat
#print axioms shl3_ofNat
#print axioms envDefineReallocNamesParked_grow
#print axioms envDefineReallocNamesParked_init
#print axioms envDefineReallocValsParked_of
#print axioms envDefineRejoinDone_of

end Vsa.Sim
