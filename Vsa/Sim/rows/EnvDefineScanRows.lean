import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.EnvDefSites
import Vsa.Sim.BridgeSeg
import Vsa.Sim.EnvGetSpec3

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.Logic (Triple)

namespace Vsa.Sim

/- Positive-count entry: take the nonzero polarity, load the names base,
initialize the index/cursor, and jump to the scan head. -/
#derive_case envDefineScanInitSeg chain
  [] terminator ⟨0x80002a90#64, 0x17305263#32,
    0x63#8, 0x52#8, 0x30#8, 0x17#8,
    .br bop.BGE false, 0, 19, 0x0164#13, 0#21, 0#12⟩ ;;
  [(0x80002a94#64, 0x00853b03#32),
   (0x80002a98#64, 0x00000413#32),
   (0x80002a9c#64, 0x000b0493#32)]
    terminator ⟨0x80002aa0#64, 0x0100006f#32,
      0x6f#8, 0x00#8, 0x00#8, 0x01#8,
      .j, 0, 0, 0#13, 0x000010#21, 0#12⟩

def envDefineScanInitL (env count : BitVec 64) : GRegs :=
  [(10, env), (19, count)]

def EnvDefineScanInitPost (env count : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = writeLog m0
    (evalBlocks envDefineScanInitSeg
      (SegEvalState.init (envDefineScanInitL env count) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x80002ab0#64 ∧
  GHolds c.σ (evalBlocks envDefineScanInitSeg
    (SegEvalState.init (envDefineScanInitL env count) lds)).regs

theorem envDefineScanInitRow (env count : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre envDefineScanInitSeg (envDefineScanInitL env count) lds
        0x80002a90#64 m0)
      (EnvDefineScanInitPost env count lds m0) := by
  apply segToTriple envDefineScanInitSeg (envDefineScanInitL env count) lds
    0x80002a90#64 m0 (EnvDefineScanInitPost env count lds m0)
    (by show ChainOK 0x80002a90#64 [10, 19] envDefineScanInitSeg; decide)
  intro σ' i' u' hG' _ hmem' hpc' _ hregs'
  refine ⟨hG', hmem', ?_, hregs'⟩
  rw [hpc']; rfl

/- Full-live scan initialization used by the semantic env_define composition. -/
def envDefineScanInitLiveL
    (env count name pv sp : BitVec 64) : GRegs :=
  [(10, env), (19, count), (18, name), (21, pv), (2, sp), (20, env)]

def EnvDefineScanInitLivePost
    (env count name pv sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x80002ab0#64 ∧
  GHolds c.σ (evalBlocks envDefineScanInitSeg
    (SegEvalState.init (envDefineScanInitLiveL env count name pv sp) lds)).regs ∧
  c.tick < 2

theorem envDefineScanInitLiveRow
    (env count name pv sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre envDefineScanInitSeg
        (envDefineScanInitLiveL env count name pv sp) lds 0x80002a90#64 m0)
      (EnvDefineScanInitLivePost env count name pv sp lds m0) := by
  apply segToTriple envDefineScanInitSeg
    (envDefineScanInitLiveL env count name pv sp) lds 0x80002a90#64 m0 _
    (by show ChainOK 0x80002a90#64 [10, 19, 18, 21, 2, 20] envDefineScanInitSeg; decide)
  intro σ' i' u' hG' hi' hmem' hpc' _ hregs'
  refine ⟨hG', ?_, ?_, hregs', hi'⟩
  · simpa [envDefineScanInitSeg, evalBlocks, SegEvalState.init, writeLog] using hmem'
  · rw [hpc']; rfl

/- One scan-head argument marshal, ending immediately before `jal strcmp`. -/
#derive_case envDefineScanCallSeg chain
  [(0x80002ab0#64, 0x0004b503#32),
   (0x80002ab4#64, 0x00090593#32)]

def envDefineScanCallL (cursor name : BitVec 64) : GRegs :=
  [(9, cursor), (18, name)]

def EnvDefineScanCallPost (cursor name : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = writeLog m0
    (evalBlocks envDefineScanCallSeg
      (SegEvalState.init (envDefineScanCallL cursor name) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x80002ab8#64 ∧
  GHolds c.σ (evalBlocks envDefineScanCallSeg
    (SegEvalState.init (envDefineScanCallL cursor name) lds)).regs

theorem envDefineScanCallRow (cursor name : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre envDefineScanCallSeg (envDefineScanCallL cursor name) lds
        0x80002ab0#64 m0)
      (EnvDefineScanCallPost cursor name lds m0) := by
  apply segToTriple envDefineScanCallSeg (envDefineScanCallL cursor name) lds
    0x80002ab0#64 m0 (EnvDefineScanCallPost cursor name lds m0)
    (by show ChainOK 0x80002ab0#64 [9, 18] envDefineScanCallSeg; decide)
  intro σ' i' u' hG' _ hmem' hpc' _ hregs'
  refine ⟨hG', hmem', ?_, hregs'⟩
  rw [hpc']
  rfl

/-- The two scan argument loads followed by the exact `jal strcmp` step. -/
theorem envDefineScanCallRun (cursor name : BitVec 64)
    (lds : List (List (BitVec 8))) (σ : Vsa.Machine.MState)
    (i u : Nat) (vmi : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x80002ab0#64)
    (hmi : σ.regs.get? Register.minstret = some vmi)
    (hmem : σ.mem = m0)
    (hL : GHolds σ (envDefineScanCallL cursor name))
    (hfacts : ChainFacts σ.mem σ.mem (envDefineScanCallL cursor name) lds
      envDefineScanCallSeg)
    (hloaded : Vsa.Sim.Code.Env_defineLoaded m0) (hi : i < 2) :
    ∃ (σ2 : Vsa.Machine.MState) (i2 : Nat),
      Vsa.Machine.Steps ⟨σ, i, u⟩
        ⟨σ2, i2, u + evalBlocksFuel envDefineScanCallSeg + 1⟩ ∧
      i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some 0x80006ea0#64 ∧
      σ2.regs.get? Register.x1 = some 0x80002abc#64 ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      GHolds σ2 (evalBlocks envDefineScanCallSeg
        (SegEvalState.init (envDefineScanCallL cursor name) lds)).regs ∧
      σ2.mem = writeLog m0 (evalBlocks envDefineScanCallSeg
        (SegEvalState.init (envDefineScanCallL cursor name) lds)).log ∧
      (∀ R, Vsa.Alloc.AbiPreserved R = true → σ2.regs.get? R = σ.regs.get? R) := by
  apply bridgeOfSeg envDefineScanCallSeg (envDefineScanCallL cursor name) lds
    σ i u 0x80002ab0#64 0x80006ea0#64 0x80002abc#64 vmi m0
    hG hpc hmi hmem hL
    (by show KeysOK [9, 18]; decide) hfacts hi
    (by show ChainOK 0x80002ab0#64 [9, 18] envDefineScanCallSeg; decide)
    (by show WrChainAvoidAbi envDefineScanCallSeg; decide)
    (by show KeysOK [11, 10, 9, 18]; decide)
    (by
      have h : keysG (evalBlocks envDefineScanCallSeg
        (SegEvalState.init (envDefineScanCallL cursor name) lds)).regs =
          [11, 10, 9, 18] := rfl
      show ∀ n ∈ keysG _, n ≠ 1
      rw [h]
      decide)
  intro σ' i' u' hG' hi' hpc' hmi' hmem' _hregs'
  obtain ⟨vm', hmi'v⟩ := hmi'
  have hpcE : evalBlocksPC 0x80002ab0#64
      (SegEvalState.init (envDefineScanCallL cursor name) lds)
      envDefineScanCallSeg = 0x80002ab8#64 := by rfl
  have hloaded' : Vsa.Sim.Code.Env_defineLoaded σ'.mem := by
    rw [hmem']
    simpa using hloaded
  obtain ⟨σ2, i2, hstep, hi2, hG2, hmem2, hobs⟩ :=
    site_80002ab8_ed σ' i' u' 0x80002ab8#64 vm' hG'
      (hpcE ▸ hpc') hmi'v hloaded' rfl (by decide) hi'
  have hlink : BitVec.addInt 0x80002ab8#64 4 = (0x80002abc#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hlink] at hobs
  exact jalStep_of_obs hstep hi2 hG2 hmem2 hobs
    (by apply BitVec.eq_of_toNat_eq; decide)

/-- Close the scan-call load facts from the represented name-pointer slot. -/
theorem envDefineScanCallRead64
    (cursor name : BitVec 64) (q : Nat) (c : Config)
    (hG : GoodState c.σ)
    (hpc : c.σ.regs.get? Register.PC = some 0x80002ab0#64)
    (hcursor : c.σ.regs.get? Register.x9 = some cursor)
    (hname : c.σ.regs.get? Register.x18 = some name)
    (hread : Vsa.MemRepr.read64 c.σ.mem cursor.toNat = some q)
    (hlo : 0x80000000 ≤ cursor.toNat)
    (hhi : cursor.toNat + 8 ≤ 0x100000000)
    (hhtif : cursor.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ cursor.toNat)
    (halign : cursor.toNat % 8 = 0)
    (hloaded : Vsa.Sim.Code.Env_defineLoaded c.σ.mem)
    (htick : c.tick < 2) :
    ∃ c', Vsa.Machine.Steps c c' ∧ GoodState c'.σ ∧ c'.tick < 2 ∧
      c'.σ.mem = c.σ.mem ∧
      c'.σ.regs.get? Register.PC = some 0x80006ea0#64 ∧
      c'.σ.regs.get? Register.x1 = some 0x80002abc#64 ∧
      c'.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 q) ∧
      c'.σ.regs.get? Register.x11 = some name ∧
      (∃ w, c'.σ.regs.get? Register.minstret = some w) ∧
      (∀ R, Vsa.Alloc.AbiPreserved R = true →
        c'.σ.regs.get? R = c.σ.regs.get? R) := by
  obtain ⟨vmi, hmi⟩ := hG.minstret
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7,
      hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, _⟩ :=
    read64_bytes_eg4 c.σ.mem cursor.toNat q hread
  let bs := [b0, b1, b2, b3, b4, b5, b6, b7]
  have hpins : LPins8 c.σ.mem cursor.toNat bs := by
    simp [LPins8, bs, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]
  have hea : eaddrM (mkLine 0x80002ab0#64 0x0004b503#32)
      (envDefineScanCallL cursor name) = cursor := by
    change cursor + sign_extend (m := 64) (0#12) = cursor
    rw [sext_zero, BitVec.add_zero]
  have hfacts : ChainFacts c.σ.mem c.σ.mem
      (envDefineScanCallL cursor name) [bs] envDefineScanCallSeg := by
    chain_facts hloaded with "Vsa.Sim.Code.env_define_at_"
    unfold MemFacts
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hea]; exact hlo
    · rw [hea]; exact hhi
    · rw [hea]; exact hhtif
    · rw [hea]; exact halign
    · rw [hea]; exact hpins
  have hL : GHolds c.σ (envDefineScanCallL cursor name) := by
    exact ⟨by simpa [gprGet] using hcursor,
      by simpa [gprGet] using hname, trivial⟩
  obtain ⟨σ', i', hsteps, hi', hG', hpc', hra', hmi', hregs', hmem', habi⟩ :=
    envDefineScanCallRun cursor name [bs] c.σ c.tick c.steps vmi c.σ.mem
      hG hpc hmi rfl hL hfacts hloaded htick
  let c' : Config := ⟨σ', i', c.steps + evalBlocksFuel envDefineScanCallSeg + 1⟩
  have hval : (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 q :=
    ld_value_eq_read64 c.σ.mem cursor.toNat q b0 b1 b2 b3 b4 b5 b6 b7 hread
      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  have hx10g : gprGet σ' 10 = some (BitVec.ofNat 64 q) := by
    have hpin := gholds_lookup _ hregs' (show lookupG 10
      (evalBlocks envDefineScanCallSeg
        (SegEvalState.init (envDefineScanCallL cursor name) [bs])).regs =
          some (BitVec.ofNat 64 q) by
        change some (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))) =
            some (BitVec.ofNat 64 q)
        rw [hval])
    exact hpin
  have hx11g : gprGet σ' 11 = some name := by
    apply gholds_lookup _ hregs'
    change some (name + sign_extend (m := 64) (0#12)) = some name
    rw [sext_zero, BitVec.add_zero]
  refine ⟨c', ?_, hG', hi', ?_, hpc', hra', ?_, ?_, hmi', ?_⟩
  · exact hsteps
  · simpa [c'] using hmem'
  · simpa [c', gprGet] using hx10g
  · simpa [c', gprGet] using hx11g
  · intro R hR
    exact habi R hR

/- `strcmp == 0`: fall through into the update store. -/
#derive_case envDefineScanHitSeg chain
  [] terminator ⟨0x80002abc#64, 0xfe0514e3#32,
    0xe3#8, 0x14#8, 0x05#8, 0xfe#8,
    .br bop.BNE false, 10, 0, 0x1fe8#13, 0#21, 0#12⟩

def envDefineScanCmpL (cmp : BitVec 64) : GRegs := [(10, cmp)]

def EnvDefineScanHitPost (cmp : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x80002ac0#64

theorem envDefineScanHitRow (cmp : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre envDefineScanHitSeg (envDefineScanCmpL cmp) []
        0x80002abc#64 m0)
      (EnvDefineScanHitPost cmp m0) := by
  apply segToTriple envDefineScanHitSeg (envDefineScanCmpL cmp) []
    0x80002abc#64 m0 (EnvDefineScanHitPost cmp m0)
    (by show ChainOK 0x80002abc#64 [10] envDefineScanHitSeg; decide)
  intro σ' i' u' hG' _ hmem' hpc' _ _
  refine ⟨hG', ?_, ?_⟩
  · exact hmem'
  · rw [hpc']; rfl

/- A miss followed by a non-final index: advance and return to the scan head. -/
#derive_case envDefineScanNextSeg chain
  [] terminator ⟨0x80002abc#64, 0xfe0514e3#32,
    0xe3#8, 0x14#8, 0x05#8, 0xfe#8,
    .br bop.BNE true, 10, 0, 0x1fe8#13, 0#21, 0#12⟩ ;;
  [(0x80002aa4#64, 0x00140413#32),
   (0x80002aa8#64, 0x00848493#32)]
    terminator ⟨0x80002aac#64, 0x06898463#32,
      0x63#8, 0x84#8, 0x89#8, 0x06#8,
      .br bop.BEQ false, 19, 8, 0x0068#13, 0#21, 0#12⟩

/- A miss at the final index: advance and branch to the capacity check. -/
#derive_case envDefineScanDoneSeg chain
  [] terminator ⟨0x80002abc#64, 0xfe0514e3#32,
    0xe3#8, 0x14#8, 0x05#8, 0xfe#8,
    .br bop.BNE true, 10, 0, 0x1fe8#13, 0#21, 0#12⟩ ;;
  [(0x80002aa4#64, 0x00140413#32),
   (0x80002aa8#64, 0x00848493#32)]
    terminator ⟨0x80002aac#64, 0x06898463#32,
      0x63#8, 0x84#8, 0x89#8, 0x06#8,
      .br bop.BEQ true, 19, 8, 0x0068#13, 0#21, 0#12⟩

def envDefineScanStepL (cmp idx cursor count : BitVec 64) : GRegs :=
  [(10, cmp), (8, idx), (9, cursor), (19, count)]

def EnvDefineScanStepPost (seg : List BBlock) (target : BitVec 64)
    (cmp idx cursor count : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks seg
    (SegEvalState.init (envDefineScanStepL cmp idx cursor count) lds)).log ∧
  c.σ.regs.get? Register.PC = some target ∧
  GHolds c.σ (evalBlocks seg
    (SegEvalState.init (envDefineScanStepL cmp idx cursor count) lds)).regs

theorem envDefineScanNextRow (cmp idx cursor count : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre envDefineScanNextSeg
        (envDefineScanStepL cmp idx cursor count) lds 0x80002abc#64 m0)
      (EnvDefineScanStepPost envDefineScanNextSeg 0x80002ab0#64
        cmp idx cursor count lds m0) := by
  apply segToTriple envDefineScanNextSeg
    (envDefineScanStepL cmp idx cursor count) lds 0x80002abc#64 m0
    (EnvDefineScanStepPost envDefineScanNextSeg 0x80002ab0#64
      cmp idx cursor count lds m0)
    (by
      show ChainOK 0x80002abc#64 [10, 8, 9, 19] envDefineScanNextSeg
      decide)
  intro σ' i' u' hG' _ hmem' hpc' _ hregs'
  refine ⟨hG', hmem', ?_, hregs'⟩
  rw [hpc']; rfl

theorem envDefineScanDoneRow (cmp idx cursor count : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre envDefineScanDoneSeg
        (envDefineScanStepL cmp idx cursor count) lds 0x80002abc#64 m0)
      (EnvDefineScanStepPost envDefineScanDoneSeg 0x80002b14#64
        cmp idx cursor count lds m0) := by
  apply segToTriple envDefineScanDoneSeg
    (envDefineScanStepL cmp idx cursor count) lds 0x80002abc#64 m0
    (EnvDefineScanStepPost envDefineScanDoneSeg 0x80002b14#64
      cmp idx cursor count lds m0)
    (by
      show ChainOK 0x80002abc#64 [10, 8, 9, 19] envDefineScanDoneSeg
      decide)
  intro σ' i' u' hG' _ hmem' hpc' _ hregs'
  refine ⟨hG', hmem', ?_, hregs'⟩
  rw [hpc']; rfl

/- Full-live variants used by the semantic scan loop. -/
def envDefineScanLiveL (cmp idx cursor count env name pv sp : BitVec 64) : GRegs :=
  [(10, cmp), (8, idx), (9, cursor), (19, count), (20, env), (18, name),
   (21, pv), (2, sp)]

def EnvDefineScanLivePost (seg : List BBlock) (target : BitVec 64)
    (cmp idx cursor count env name pv sp : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = writeLog m0 (evalBlocks seg
    (SegEvalState.init
      (envDefineScanLiveL cmp idx cursor count env name pv sp) lds)).log ∧
  c.σ.regs.get? Register.PC = some target ∧
  GHolds c.σ (evalBlocks seg (SegEvalState.init
    (envDefineScanLiveL cmp idx cursor count env name pv sp) lds)).regs ∧
  c.tick < 2

theorem envDefineScanHitLiveRow
    (cmp idx cursor count env name pv sp : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre envDefineScanHitSeg
        (envDefineScanLiveL cmp idx cursor count env name pv sp) []
        0x80002abc#64 m0)
      (EnvDefineScanLivePost envDefineScanHitSeg 0x80002ac0#64
        cmp idx cursor count env name pv sp [] m0) := by
  apply segToTriple envDefineScanHitSeg
    (envDefineScanLiveL cmp idx cursor count env name pv sp) [] 0x80002abc#64 m0 _
    (by show ChainOK 0x80002abc#64 [10, 8, 9, 19, 20, 18, 21, 2] envDefineScanHitSeg
        decide)
  intro σ' i' u' hG' hi' hmem' hpc' _ hregs'
  refine ⟨hG', ?_, ?_, hregs', hi'⟩
  · exact hmem'
  · rw [hpc']; rfl

theorem envDefineScanNextLiveRow
    (cmp idx cursor count env name pv sp : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre envDefineScanNextSeg
        (envDefineScanLiveL cmp idx cursor count env name pv sp) []
        0x80002abc#64 m0)
      (EnvDefineScanLivePost envDefineScanNextSeg 0x80002ab0#64
        cmp idx cursor count env name pv sp [] m0) := by
  apply segToTriple envDefineScanNextSeg
    (envDefineScanLiveL cmp idx cursor count env name pv sp) [] 0x80002abc#64 m0 _
    (by show ChainOK 0x80002abc#64 [10, 8, 9, 19, 20, 18, 21, 2] envDefineScanNextSeg
        decide)
  intro σ' i' u' hG' hi' hmem' hpc' _ hregs'
  refine ⟨hG', hmem', ?_, hregs', hi'⟩
  rw [hpc']; rfl

theorem envDefineScanDoneLiveRow
    (cmp idx cursor count env name pv sp : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre envDefineScanDoneSeg
        (envDefineScanLiveL cmp idx cursor count env name pv sp) []
        0x80002abc#64 m0)
      (EnvDefineScanLivePost envDefineScanDoneSeg 0x80002b14#64
        cmp idx cursor count env name pv sp [] m0) := by
  apply segToTriple envDefineScanDoneSeg
    (envDefineScanLiveL cmp idx cursor count env name pv sp) [] 0x80002abc#64 m0 _
    (by show ChainOK 0x80002abc#64 [10, 8, 9, 19, 20, 18, 21, 2] envDefineScanDoneSeg
        decide)
  intro σ' i' u' hG' hi' hmem' hpc' _ hregs'
  refine ⟨hG', hmem', ?_, hregs', hi'⟩
  rw [hpc']; rfl

#print axioms envDefineScanCallRow
#print axioms envDefineScanCallRun
#print axioms envDefineScanInitRow
#print axioms envDefineScanHitRow
#print axioms envDefineScanNextRow
#print axioms envDefineScanDoneRow
#print axioms envDefineScanHitLiveRow
#print axioms envDefineScanNextLiveRow
#print axioms envDefineScanDoneLiveRow

end Vsa.Sim
