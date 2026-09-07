import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.EnvDefSites
import Vsa.Sim.SegFrameFactsAuto
import Vsa.Sim.PinW

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.Logic (Triple)

namespace Vsa.Sim

set_option maxHeartbeats 1000000

#derive_case envDefineEpilogueSeg chain
  [(0x80002aec#64, 0x03813083#32),
   (0x80002af0#64, 0x03013403#32),
   (0x80002af4#64, 0x02813483#32),
   (0x80002af8#64, 0x02013903#32),
   (0x80002afc#64, 0x01813983#32),
   (0x80002b00#64, 0x01013a03#32),
   (0x80002b04#64, 0x00813a83#32),
   (0x80002b08#64, 0x00013b03#32),
   (0x80002b0c#64, 0x04010113#32)]
    terminator ⟨0x80002b10#64, 0x00008067#32,
      0x67#8, 0x80#8, 0x00#8, 0x00#8,
      .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def envDefineEpilogueL (sp : BitVec 64) : GRegs := [(2, sp)]

def envDefineEpilogueBody : List MInstr :=
  [mkLine 0x80002aec#64 0x03813083#32,
   mkLine 0x80002af0#64 0x03013403#32,
   mkLine 0x80002af4#64 0x02813483#32,
   mkLine 0x80002af8#64 0x02013903#32,
   mkLine 0x80002afc#64 0x01813983#32,
   mkLine 0x80002b00#64 0x01013a03#32,
   mkLine 0x80002b04#64 0x00813a83#32,
   mkLine 0x80002b08#64 0x00013b03#32,
   mkLine 0x80002b0c#64 0x04010113#32]

def envDefineEpilogueTerm : Option TInstr :=
  some ⟨0x80002b10#64, 0x00008067#32,
    0x67#8, 0x80#8, 0x00#8, 0x00#8,
    .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def EnvDefineEpiloguePost (sp : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks envDefineEpilogueSeg
    (SegEvalState.init (envDefineEpilogueL sp) lds)).log ∧
  c.σ.regs.get? Register.PC = some
    (evalBlocksPC 0x80002aec#64
      (SegEvalState.init (envDefineEpilogueL sp) lds)
      envDefineEpilogueSeg) ∧
  GHolds c.σ (evalBlocks envDefineEpilogueSeg
    (SegEvalState.init (envDefineEpilogueL sp) lds)).regs ∧
  c.tick < 2

theorem envDefineEpilogueRow (sp : BitVec 64)
    (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple
      (SegPre envDefineEpilogueSeg (envDefineEpilogueL sp) lds
        0x80002aec#64 m0)
      (EnvDefineEpiloguePost sp lds m0) := by
  apply segToTriple envDefineEpilogueSeg (envDefineEpilogueL sp) lds
    0x80002aec#64 m0 (EnvDefineEpiloguePost sp lds m0)
    (by
      show ChainOK 0x80002aec#64 [2] envDefineEpilogueSeg
      decide)
  intro σ' i' u' hG' hi' hmem' hpc' _hmi' hregs'
  exact ⟨hG', hmem', hpc', hregs', hi'⟩

/-- The eight epilogue load values, tied to the entry ABI ghost. -/
def EnvDefineSpillValues
    (gm : (R : Register) → Option (RegisterType R))
    (lds : List (List (BitVec 8))) : Prop :=
  bytesVal .ld (lds.getD 0 []) = (gm Register.x1).getD 0#64 ∧
  bytesVal .ld (lds.getD 1 []) = (gm Register.x8).getD 0#64 ∧
  bytesVal .ld (lds.getD 2 []) = (gm Register.x9).getD 0#64 ∧
  bytesVal .ld (lds.getD 3 []) = (gm Register.x18).getD 0#64 ∧
  bytesVal .ld (lds.getD 4 []) = (gm Register.x19).getD 0#64 ∧
  bytesVal .ld (lds.getD 5 []) = (gm Register.x20).getD 0#64 ∧
  bytesVal .ld (lds.getD 6 []) = (gm Register.x21).getD 0#64 ∧
  bytesVal .ld (lds.getD 7 []) = (gm Register.x22).getD 0#64

def envDefineWordBytes (v : BitVec 64) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8,
   v.extractLsb' 24 8, v.extractLsb' 32 8, v.extractLsb' 40 8,
   v.extractLsb' 48 8, v.extractLsb' 56 8]

theorem lpins8_of_pinw8 {m : Std.ExtHashMap Nat (BitVec 8)} {a : Nat}
    {v : BitVec 64} (h : PinW8 m a v) : LPins8 m a (envDefineWordBytes v) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨by simpa [envDefineWordBytes] using lpin_of_present h0,
    by simpa [envDefineWordBytes] using lpin_of_present h1,
    by simpa [envDefineWordBytes] using lpin_of_present h2,
    by simpa [envDefineWordBytes] using lpin_of_present h3,
    by simpa [envDefineWordBytes] using lpin_of_present h4,
    by simpa [envDefineWordBytes] using lpin_of_present h5,
    by simpa [envDefineWordBytes] using lpin_of_present h6,
    by simpa [envDefineWordBytes] using lpin_of_present h7⟩

theorem bytesVal_wordBytes (v : BitVec 64) :
    bytesVal .ld (envDefineWordBytes v) = v := by
  simpa [envDefineWordBytes, bytesVal] using pinw8_sext_reassemble v

/-- Exact code pins, stack geometry, and all eight raw spill readbacks. -/
def EnvDefineSpillImage (sp : BitVec 64) (c : Config)
    (lds : List (List (BitVec 8))) : Prop :=
    Vsa.Sim.Code.Env_defineLoaded c.σ.mem ∧
    0x80000000 ≤ sp.toNat ∧ sp.toNat + 64 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ sp.toNat ∧ sp.toNat % 8 = 0 ∧
    LPins8 c.σ.mem (sp.toNat + 56) (lds.getD 0 []) ∧
    LPins8 c.σ.mem (sp.toNat + 48) (lds.getD 1 []) ∧
    LPins8 c.σ.mem (sp.toNat + 40) (lds.getD 2 []) ∧
    LPins8 c.σ.mem (sp.toNat + 32) (lds.getD 3 []) ∧
    LPins8 c.σ.mem (sp.toNat + 24) (lds.getD 4 []) ∧
    LPins8 c.σ.mem (sp.toNat + 16) (lds.getD 5 []) ∧
    LPins8 c.σ.mem (sp.toNat + 8) (lds.getD 6 []) ∧
    LPins8 c.σ.mem sp.toNat (lds.getD 7 []) ∧
    TermFactsO (runGM envDefineEpilogueBody
      (envDefineEpilogueL sp) lds) envDefineEpilogueTerm

/-- Helper-local carrier.  The live callee ghost is intentionally not related to
the saved outer values: env_define repurposes its callee-saved registers. -/
def EnvDefineSpillFrame (sp : BitVec 64)
    (_live : (R : Register) → Option (RegisterType R)) (c : Config) : Prop :=
  ∃ lds, EnvDefineSpillImage sp c lds

/-- Epilogue carrier relating the raw spill image to the outer caller snapshot. -/
def EnvDefineSavedSpillFrame (sp : BitVec 64)
    (saved : (R : Register) → Option (RegisterType R)) (c : Config) : Prop :=
  ∃ lds, EnvDefineSpillImage sp c lds ∧ EnvDefineSpillValues saved lds

theorem EnvDefineSavedSpillFrame.of_pinw8
    {sp : BitVec 64} {saved : (R : Register) → Option (RegisterType R)}
    {c : Config} (ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (hra : saved Register.x1 = some ra) (hs0 : saved Register.x8 = some s0)
    (hs1 : saved Register.x9 = some s1) (hs2 : saved Register.x18 = some s2)
    (hs3 : saved Register.x19 = some s3) (hs4 : saved Register.x20 = some s4)
    (hs5 : saved Register.x21 = some s5) (hs6 : saved Register.x22 = some s6)
    (hcode : Vsa.Sim.Code.Env_defineLoaded c.σ.mem)
    (hlo : 0x80000000 ≤ sp.toNat) (hhi : sp.toNat + 64 ≤ 0x100000000)
    (hhtif : tohostAddr + 16 ≤ sp.toNat) (halign : sp.toNat % 8 = 0)
    (p56 : PinW8 c.σ.mem (sp.toNat + 56) ra)
    (p48 : PinW8 c.σ.mem (sp.toNat + 48) s0)
    (p40 : PinW8 c.σ.mem (sp.toNat + 40) s1)
    (p32 : PinW8 c.σ.mem (sp.toNat + 32) s2)
    (p24 : PinW8 c.σ.mem (sp.toNat + 24) s3)
    (p16 : PinW8 c.σ.mem (sp.toNat + 16) s4)
    (p08 : PinW8 c.σ.mem (sp.toNat + 8) s5)
    (p00 : PinW8 c.σ.mem sp.toNat s6)
    (hterm : TermFactsO (runGM envDefineEpilogueBody (envDefineEpilogueL sp)
      [envDefineWordBytes ra, envDefineWordBytes s0, envDefineWordBytes s1,
       envDefineWordBytes s2, envDefineWordBytes s3, envDefineWordBytes s4,
       envDefineWordBytes s5, envDefineWordBytes s6]) envDefineEpilogueTerm) :
    EnvDefineSavedSpillFrame sp saved c := by
  let lds := [envDefineWordBytes ra, envDefineWordBytes s0, envDefineWordBytes s1,
    envDefineWordBytes s2, envDefineWordBytes s3, envDefineWordBytes s4,
    envDefineWordBytes s5, envDefineWordBytes s6]
  refine ⟨lds, ?_, ?_⟩
  · exact ⟨hcode, hlo, hhi, hhtif, halign,
      by simpa [lds] using lpins8_of_pinw8 p56,
      by simpa [lds] using lpins8_of_pinw8 p48,
      by simpa [lds] using lpins8_of_pinw8 p40,
      by simpa [lds] using lpins8_of_pinw8 p32,
      by simpa [lds] using lpins8_of_pinw8 p24,
      by simpa [lds] using lpins8_of_pinw8 p16,
      by simpa [lds] using lpins8_of_pinw8 p08,
      by simpa [lds] using lpins8_of_pinw8 p00,
      by simpa [lds] using hterm⟩
  · simp only [EnvDefineSpillValues, lds, List.getD_cons_zero,
      List.getD_cons_succ, bytesVal_wordBytes, hra, hs0, hs1, hs2, hs3, hs4, hs5,
      hs6, Option.getD_some]
    simp

theorem envDefineLoaded_of_agree
    (m m' : Std.ExtHashMap Nat (BitVec 8))
    (hagree : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 → m'[a]? = m[a]?)
    (h : Vsa.Sim.Code.Env_defineLoaded m) : Vsa.Sim.Code.Env_defineLoaded m' := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Vsa.Sim.Code.env_defineChunk0] at c0 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_defineChunk1] at c1 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_defineChunk2] at c2 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_defineChunk3] at c3 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_defineChunk4] at c4 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_defineChunk5] at c5 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_defineChunk6] at c6 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])

theorem EnvDefineSpillFrame.of_mem_eq {sp : BitVec 64}
    {gm : (R : Register) → Option (RegisterType R)} {c c' : Config}
    (hmem : c'.σ.mem = c.σ.mem) (h : EnvDefineSpillFrame sp gm c) :
    EnvDefineSpillFrame sp gm c' := by
  obtain ⟨lds, h⟩ := h
  refine ⟨lds, ?_⟩
  unfold EnvDefineSpillImage at h ⊢
  rw [hmem]
  exact h

private theorem envDefineCodePinsM_of_agree
    {m m' : Std.ExtHashMap Nat (BitVec 8)} (a : MInstr)
    (ha : 0x80002aec ≤ a.pc.toNat ∧ a.pc.toNat + 4 ≤ 0x80002b14)
    (hag : ∀ k, 0x80002aec ≤ k → k < 0x80002b14 → m'[k]? = m[k]?)
    (h : BytePinsM m a) : BytePinsM m' a := by
  unfold BytePinsM at h ⊢
  rw [hag a.pc.toNat (by omega) (by omega),
    hag (a.pc.toNat + 1) (by omega) (by omega),
    hag (a.pc.toNat + 2) (by omega) (by omega),
    hag (a.pc.toNat + 3) (by omega) (by omega)]
  exact h

private theorem envDefineCodePinsT_of_agree
    {m m' : Std.ExtHashMap Nat (BitVec 8)} (a : TInstr)
    (ha : 0x80002aec ≤ a.pc.toNat ∧ a.pc.toNat + 4 ≤ 0x80002b14)
    (hag : ∀ k, 0x80002aec ≤ k → k < 0x80002b14 → m'[k]? = m[k]?)
    (h : BytePinsT m a) : BytePinsT m' a := by
  unfold BytePinsT at h ⊢
  rw [hag a.pc.toNat (by omega) (by omega),
    hag (a.pc.toNat + 1) (by omega) (by omega),
    hag (a.pc.toNat + 2) (by omega) (by omega),
    hag (a.pc.toNat + 3) (by omega) (by omega)]
  exact h

private theorem envDefineLPins8_of_agree
    {m m' : Std.ExtHashMap Nat (BitVec 8)} {ea : Nat}
    {bs : List (BitVec 8)}
    (hag : ∀ k, ea ≤ k → k < ea + 8 → m'[k]? = m[k]?)
    (h : LPins8 m ea bs) : LPins8 m' ea bs := by
  unfold LPins8 at h ⊢
  rw [hag ea (by omega) (by omega), hag (ea + 1) (by omega) (by omega),
    hag (ea + 2) (by omega) (by omega), hag (ea + 3) (by omega) (by omega),
    hag (ea + 4) (by omega) (by omega), hag (ea + 5) (by omega) (by omega),
    hag (ea + 6) (by omega) (by omega), hag (ea + 7) (by omega) (by omega)]
  exact h

theorem envDefLdsHead (lds : List (List (BitVec 8))) :
    lds.headD [] = lds.getD 0 [] := by cases lds <;> rfl

theorem envDefLdsHeadGetD (lds : List (List (BitVec 8))) :
    lds.head?.getD [] = lds.getD 0 [] := by cases lds <;> rfl

theorem envDefLdsTail (lds : List (List (BitVec 8))) (n : Nat) :
    lds.tail.getD n [] = lds.getD (n + 1) [] := by cases lds <;> rfl

@[simp] theorem epiKind0 : (mkLine 0x80002aec#64 0x03813083#32).kind = .ld := by decide
@[simp] theorem epiKind1 : (mkLine 0x80002af0#64 0x03013403#32).kind = .ld := by decide
@[simp] theorem epiKind2 : (mkLine 0x80002af4#64 0x02813483#32).kind = .ld := by decide
@[simp] theorem epiKind3 : (mkLine 0x80002af8#64 0x02013903#32).kind = .ld := by decide
@[simp] theorem epiKind4 : (mkLine 0x80002afc#64 0x01813983#32).kind = .ld := by decide
@[simp] theorem epiKind5 : (mkLine 0x80002b00#64 0x01013a03#32).kind = .ld := by decide
@[simp] theorem epiKind6 : (mkLine 0x80002b04#64 0x00813a83#32).kind = .ld := by decide
@[simp] theorem epiKind7 : (mkLine 0x80002b08#64 0x00013b03#32).kind = .ld := by decide

private theorem envDefineMemFactsLd
    {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs} {a : MInstr}
    (sp : BitVec 64) (off : Nat) {bs : List (BitVec 8)}
    (hlo : 0x80000000 ≤ sp.toNat) (hhi : sp.toNat + 64 ≤ 0x100000000)
    (hhtif : tohostAddr + 16 ≤ sp.toNat) (halign : sp.toNat % 8 = 0)
    (hk : a.kind = .ld) (hsrc : srcVal a.rs1 L = sp)
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hoff : off + 8 ≤ 64) (hoff8 : off % 8 = 0)
    (hpins : LPins8 m (sp.toNat + off) bs) : MemFacts m L bs a := by
  have hea : (eaddrM a L).toNat = sp.toNat + off := by
    unfold eaddrM
    rw [hsrc, BitVec.toNat_add, himm, Nat.mod_eq_of_lt (by omega)]
  unfold MemFacts
  rw [hk]
  exact ⟨⟨by rw [hea]; omega, by rw [hea]; omega, by rw [hea]; right; omega⟩,
    by rw [hea]; exact hpins⟩

theorem EnvDefineSpillImage.chainFacts {sp : BitVec 64} {c : Config}
    {lds : List (List (BitVec 8))} (h : EnvDefineSpillImage sp c lds) :
    ChainFacts c.σ.mem c.σ.mem (envDefineEpilogueL sp) lds
      envDefineEpilogueSeg := by
  obtain ⟨hcode, hlo, hhi, hhtif, halign, p56, p48, p40, p32,
    p24, p16, p08, p00, hterm⟩ := h
  chain_facts hcode with "Vsa.Sim.Code.env_define_at_"
  · refine envDefineMemFactsLd (sp := sp) (off := 56) hlo hhi hhtif halign
      (by decide) (by rfl) (by decide) (by decide) (by decide) ?_
    simpa only [envDefLdsHead] using p56
  · refine envDefineMemFactsLd (sp := sp) (off := 48) hlo hhi hhtif halign
      (by decide) (by rfl) (by decide) (by decide) (by decide) ?_
    simpa only [stepMemM, stepLdsM, epiKind0, envDefLdsHead, envDefLdsTail] using p48
  · refine envDefineMemFactsLd (sp := sp) (off := 40) hlo hhi hhtif halign
      (by decide) (by rfl) (by decide) (by decide) (by decide) ?_
    simpa only [stepMemM, stepLdsM, epiKind0, epiKind1, envDefLdsHead, envDefLdsTail,
      Nat.zero_add, Nat.add_assoc, Nat.reduceAdd] using p40
  · refine envDefineMemFactsLd (sp := sp) (off := 32) hlo hhi hhtif halign
      (by decide) (by rfl) (by decide) (by decide) (by decide) ?_
    simpa only [stepMemM, stepLdsM, epiKind0, epiKind1, epiKind2, envDefLdsHead,
      envDefLdsTail, Nat.zero_add, Nat.add_assoc, Nat.reduceAdd] using p32
  · refine envDefineMemFactsLd (sp := sp) (off := 24) hlo hhi hhtif halign
      (by decide) (by rfl) (by decide) (by decide) (by decide) ?_
    simpa only [stepMemM, stepLdsM, epiKind0, epiKind1, epiKind2, epiKind3,
      envDefLdsHead, envDefLdsTail, Nat.zero_add, Nat.add_assoc, Nat.reduceAdd] using p24
  · refine envDefineMemFactsLd (sp := sp) (off := 16) hlo hhi hhtif halign
      (by decide) (by rfl) (by decide) (by decide) (by decide) ?_
    simpa only [stepMemM, stepLdsM, epiKind0, epiKind1, epiKind2, epiKind3, epiKind4,
      envDefLdsHead, envDefLdsTail, Nat.zero_add, Nat.add_assoc, Nat.reduceAdd] using p16
  · refine envDefineMemFactsLd (sp := sp) (off := 8) hlo hhi hhtif halign
      (by decide) (by rfl) (by decide) (by decide) (by decide) ?_
    simpa only [stepMemM, stepLdsM, epiKind0, epiKind1, epiKind2, epiKind3, epiKind4,
      epiKind5, envDefLdsHead, envDefLdsTail, Nat.zero_add, Nat.add_assoc,
      Nat.reduceAdd] using p08
  · refine envDefineMemFactsLd (sp := sp) (off := 0) hlo hhi hhtif halign
      (by decide) (by rfl) (by decide) (by decide) (by decide) ?_
    simpa only [stepMemM, stepLdsM, epiKind0, epiKind1, epiKind2, epiKind3, epiKind4,
      epiKind5, epiKind6, envDefLdsHead, envDefLdsTail, Nat.zero_add, Nat.add_assoc,
      Nat.reduceAdd] using p00
  · exact hterm

theorem EnvDefineSpillFrame.chainFacts {sp : BitVec 64}
    {gm : (R : Register) → Option (RegisterType R)} {c : Config}
    (h : EnvDefineSpillFrame sp gm c) :
    ∃ lds, ChainFacts c.σ.mem c.σ.mem (envDefineEpilogueL sp) lds
      envDefineEpilogueSeg := by
  obtain ⟨lds, himage⟩ := h
  exact ⟨lds, himage.chainFacts⟩

theorem EnvDefineSavedSpillFrame.chainFacts {sp : BitVec 64}
    {saved : (R : Register) → Option (RegisterType R)} {c : Config}
    (h : EnvDefineSavedSpillFrame sp saved c) :
    ∃ lds, ChainFacts c.σ.mem c.σ.mem (envDefineEpilogueL sp) lds
      envDefineEpilogueSeg ∧ EnvDefineSpillValues saved lds := by
  obtain ⟨lds, himage, hvalues⟩ := h
  exact ⟨lds, himage.chainFacts, hvalues⟩

/-- Arena-confined writes preserve env_define code and its 64-byte spill frame. -/
theorem EnvDefineSpillFrame.of_arena_frame
    (A : Vsa.RuntimeRepr.Arena) {sp dst : BitVec 64} {n : Nat}
    {gm : (R : Register) → Option (RegisterType R)} {c c' : Config}
    (hdst : A.contains dst.toNat n)
    (harenaStack : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo)
    (hout : ∀ a : Nat, (a < dst.toNat ∨ dst.toNat + n ≤ a) →
      c'.σ.mem[a]? = c.σ.mem[a]?)
    (h : EnvDefineSpillFrame sp gm c) : EnvDefineSpillFrame sp gm c' := by
  obtain ⟨lds, hcode, hlo, hhi, hhtif, halign, p56, p48, p40, p32,
    p24, p16, p08, p00, hterm⟩ := h
  have hCodeAgree : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 →
      c'.σ.mem[a]? = c.σ.mem[a]? := by
    intro a ha0 ha1
    apply hout
    rcases hdst with ⟨hdlo, hdhi⟩
    rcases harenaCode with hbefore | hafter
    · right; omega
    · left; omega
  have hSpillAgree : ∀ a, sp.toNat ≤ a → a < sp.toNat + 64 →
      c'.σ.mem[a]? = c.σ.mem[a]? := by
    intro a ha0 ha1
    apply hout
    rcases hdst with ⟨hdlo, hdhi⟩
    rcases harenaStack with hbefore | hafter
    · right; omega
    · left; omega
  refine ⟨lds, envDefineLoaded_of_agree _ _ hCodeAgree hcode,
    hlo, hhi, hhtif, halign, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hterm⟩
  · exact envDefineLPins8_of_agree
      (fun k hk0 hk1 => hSpillAgree k (by omega) (by omega)) p56
  · exact envDefineLPins8_of_agree
      (fun k hk0 hk1 => hSpillAgree k (by omega) (by omega)) p48
  · exact envDefineLPins8_of_agree
      (fun k hk0 hk1 => hSpillAgree k (by omega) (by omega)) p40
  · exact envDefineLPins8_of_agree
      (fun k hk0 hk1 => hSpillAgree k (by omega) (by omega)) p32
  · exact envDefineLPins8_of_agree
      (fun k hk0 hk1 => hSpillAgree k (by omega) (by omega)) p24
  · exact envDefineLPins8_of_agree
      (fun k hk0 hk1 => hSpillAgree k (by omega) (by omega)) p16
  · exact envDefineLPins8_of_agree
      (fun k hk0 hk1 => hSpillAgree k (by omega) (by omega)) p08
  · exact envDefineLPins8_of_agree
      (fun k hk0 hk1 => hSpillAgree k (by omega) (by omega)) p00

/-- Pointwise public-memory framing over the code and spill intervals preserves the
exact epilogue carrier.  Allocator contracts discharge these two interval clauses. -/
theorem EnvDefineSpillImage.of_interval_agree
    {sp : BitVec 64} {lds : List (List (BitVec 8))} {c c' : Config}
    (hCodeAgree : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 →
      c'.σ.mem[a]? = c.σ.mem[a]?)
    (hSpillAgree : ∀ a, sp.toNat ≤ a → a < sp.toNat + 64 →
      c'.σ.mem[a]? = c.σ.mem[a]?)
    (h : EnvDefineSpillImage sp c lds) : EnvDefineSpillImage sp c' lds := by
  obtain ⟨hcode, hlo, hhi, hhtif, halign, p56, p48, p40, p32,
    p24, p16, p08, p00, hterm⟩ := h
  refine ⟨envDefineLoaded_of_agree _ _ hCodeAgree hcode,
    hlo, hhi, hhtif, halign, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hterm⟩
  · exact envDefineLPins8_of_agree
      (fun k hk0 hk1 => hSpillAgree k (by omega) (by omega)) p56
  · exact envDefineLPins8_of_agree
      (fun k hk0 hk1 => hSpillAgree k (by omega) (by omega)) p48
  · exact envDefineLPins8_of_agree
      (fun k hk0 hk1 => hSpillAgree k (by omega) (by omega)) p40
  · exact envDefineLPins8_of_agree
      (fun k hk0 hk1 => hSpillAgree k (by omega) (by omega)) p32
  · exact envDefineLPins8_of_agree
      (fun k hk0 hk1 => hSpillAgree k (by omega) (by omega)) p24
  · exact envDefineLPins8_of_agree
      (fun k hk0 hk1 => hSpillAgree k (by omega) (by omega)) p16
  · exact envDefineLPins8_of_agree
      (fun k hk0 hk1 => hSpillAgree k (by omega) (by omega)) p08
  · exact envDefineLPins8_of_agree
      (fun k hk0 hk1 => hSpillAgree k (by omega) (by omega)) p00

theorem EnvDefineSpillFrame.of_interval_agree
    {sp : BitVec 64} {gm : (R : Register) → Option (RegisterType R)}
    {c c' : Config}
    (hCodeAgree : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 →
      c'.σ.mem[a]? = c.σ.mem[a]?)
    (hSpillAgree : ∀ a, sp.toNat ≤ a → a < sp.toNat + 64 →
      c'.σ.mem[a]? = c.σ.mem[a]?)
    (h : EnvDefineSpillFrame sp gm c) : EnvDefineSpillFrame sp gm c' := by
  obtain ⟨lds, himage⟩ := h
  exact ⟨lds, himage.of_interval_agree hCodeAgree hSpillAgree⟩

theorem EnvDefineSavedSpillFrame.of_interval_agree
    {sp : BitVec 64} {saved : (R : Register) → Option (RegisterType R)}
    {c c' : Config}
    (hCodeAgree : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 →
      c'.σ.mem[a]? = c.σ.mem[a]?)
    (hSpillAgree : ∀ a, sp.toNat ≤ a → a < sp.toNat + 64 →
      c'.σ.mem[a]? = c.σ.mem[a]?)
    (h : EnvDefineSavedSpillFrame sp saved c) :
    EnvDefineSavedSpillFrame sp saved c' := by
  obtain ⟨lds, himage, hvalues⟩ := h
  exact ⟨lds, himage.of_interval_agree hCodeAgree hSpillAgree, hvalues⟩

theorem EnvDefineSavedSpillFrame.of_mem_eq
    {sp : BitVec 64} {saved : (R : Register) → Option (RegisterType R)}
    {c c' : Config} (hmem : c'.σ.mem = c.σ.mem)
    (h : EnvDefineSavedSpillFrame sp saved c) :
    EnvDefineSavedSpillFrame sp saved c' := by
  apply h.of_interval_agree
  · intro a _ _
    rw [hmem]
  · intro a _ _
    rw [hmem]

theorem EnvDefineSavedSpillFrame.of_arena_frame
    (A : Vsa.RuntimeRepr.Arena) {sp dst : BitVec 64} {n : Nat}
    {saved : (R : Register) → Option (RegisterType R)} {c c' : Config}
    (hdst : A.contains dst.toNat n)
    (harenaStack : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo)
    (hout : ∀ a : Nat, (a < dst.toNat ∨ dst.toNat + n ≤ a) →
      c'.σ.mem[a]? = c.σ.mem[a]?)
    (h : EnvDefineSavedSpillFrame sp saved c) :
    EnvDefineSavedSpillFrame sp saved c' := by
  apply h.of_interval_agree
  · intro a ha0 ha1
    apply hout
    rcases hdst with ⟨hdlo, hdhi⟩
    rcases harenaCode with hbefore | hafter
    · right; omega
    · left; omega
  · intro a ha0 ha1
    apply hout
    rcases hdst with ⟨hdlo, hdhi⟩
    rcases harenaStack with hbefore | hafter
    · right; omega
    · left; omega

theorem EnvDefineSavedSpillFrame.raw
    {sp : BitVec 64} {saved live : (R : Register) → Option (RegisterType R)}
    {c : Config} (h : EnvDefineSavedSpillFrame sp saved c) :
    EnvDefineSpillFrame sp live c := by
  obtain ⟨lds, himage, _⟩ := h
  exact ⟨lds, himage⟩

#print axioms envDefineEpilogueRow
#print axioms EnvDefineSpillFrame.of_mem_eq
#print axioms EnvDefineSavedSpillFrame.of_mem_eq
#print axioms EnvDefineSavedSpillFrame.of_arena_frame

end Vsa.Sim
