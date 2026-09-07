import Vsa.Sim.rows.EnvDefineScanRows
import Vsa.Sim.rows.EnvDefinePrologueSaved
import Vsa.Sim.StrcmpSpecW4

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config Steps)
open Vsa.MemRepr
open Vsa.RuntimeRepr
open Vsa.Logic (Triple)

namespace Vsa.Sim

/-- Semantic and machine carrier at the env_define scan head. -/
structure EnvDefineScanSt
    (saved : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (φf φc : Vsa.While.Addr → Nat) (m0 : Mem) (c : Config) : Prop where
  good : GoodState c.σ
  loadedD : Vsa.Sim.Code.Env_defineLoaded c.σ.mem
  loadedS : Vsa.Sim.Code.StrcmpLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some 0x80002ab0#64
  envReg : c.σ.regs.get? Register.x20 = some env
  nameReg : c.σ.regs.get? Register.x18 = some name
  value : c.σ.regs.get? Register.x21 = some pv
  countReg : c.σ.regs.get? Register.x19 = some count
  cursor : c.σ.regs.get? Register.x9 =
    some (pn + BitVec.ofNat 64 (8 * i))
  idx : c.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 i)
  spReg : c.σ.regs.get? Register.x2 = some sp
  tick : c.tick < 2
  frame : FrameRepr m0 N φf φc env.toNat f
  names : ScanNames m0 pn.toNat name nameStr f
  countEq : count.toNat = f.vars.length
  index : i < f.vars.length
  savedSpills : EnvDefineSavedSpillFrame sp saved c

/-- Exact post-strcmp carrier, parked at the env_define result branch. -/
structure EnvDefineScanCmpSt
    (saved : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (φf φc : Vsa.While.Addr → Nat) (m0 : Mem) (c : Config) : Prop where
  good : GoodState c.σ
  loadedD : Vsa.Sim.Code.Env_defineLoaded c.σ.mem
  loadedS : Vsa.Sim.Code.StrcmpLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some 0x80002abc#64
  envReg : c.σ.regs.get? Register.x20 = some env
  nameReg : c.σ.regs.get? Register.x18 = some name
  value : c.σ.regs.get? Register.x21 = some pv
  countReg : c.σ.regs.get? Register.x19 = some count
  cursor : c.σ.regs.get? Register.x9 =
    some (pn + BitVec.ofNat 64 (8 * i))
  idx : c.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 i)
  spReg : c.σ.regs.get? Register.x2 = some sp
  index : i < f.vars.length
  xres : ∃ x csa csb,
    c.σ.regs.get? Register.x10 = some x ∧
    String.ofList csa = (f.vars[i]'index).1 ∧ String.ofList csb = nameStr ∧
    strcmpSign x = strcmpSpecSign csa csb ∧
    (strcmpSpecSign csa csb = 0 ↔ (f.vars[i]'index).1 = nameStr)
  tick : c.tick < 2
  frame : FrameRepr m0 N φf φc env.toNat f
  names : ScanNames m0 pn.toNat name nameStr f
  countEq : count.toNat = f.vars.length
  savedSpills : EnvDefineSavedSpillFrame sp saved c

/-- One exact argument-load/JAL/strcmp composition. -/
theorem envDefineScanCompare
    (saved : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (φf φc : Vsa.While.Addr → Nat) (m0 : Mem) :
    Triple
      (EnvDefineScanSt saved env name pv count pn sp i f nameStr N φf φc m0)
      (EnvDefineScanCmpSt saved env name pv count pn sp i f nameStr N φf φc m0) := by
  intro c h
  obtain ⟨q, hq, hqstr⟩ := h.names.bindPtr i h.index
  have hcursorNat : (pn + BitVec.ofNat 64 (8 * i)).toNat = pn.toNat + 8 * i := by
    apply ptrN
    have hhi := h.names.slotHi i h.index
    omega
  obtain ⟨c1, hs1, hG1, htick1, hmem1, hpc1, hra1, ha01, ha11, hmi1, habi1⟩ :=
    envDefineScanCallRead64 (pn + BitVec.ofNat 64 (8 * i)) name q c h.good h.pc
      h.cursor h.nameReg (by rw [h.mem, hcursorNat]; exact hq)
      (by rw [hcursorNat]; exact h.names.slotLo i h.index)
      (by rw [hcursorNat]; exact h.names.slotHi i h.index)
      (by rw [hcursorNat]; exact h.names.slotHtif i h.index)
      (by rw [hcursorNat]; exact h.names.slotAlign i h.index)
      h.loadedD h.tick
  have hqLt : q < 2^64 := read64_lt_eg4 m0 (pn.toNat + 8 * i) q hq
  have hqNat : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqLt]
  let g1 : (R : Register) → Option (RegisterType R) := fun R => c1.σ.regs.get? R
  have hpre : strcmp_full_pre g1 (BitVec.ofNat 64 q) name 0x80002abc#64
      (f.vars[i]'h.index).1 nameStr m0 c1.σ.sailOutput c1 := by
    refine ⟨hG1, ?_, ?_, rfl, hpc1, ha01, ha11, hra1, hmi1, htick1,
      (by decide), ?_, h.names.nameCStr, h.names.maskPinned, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hmem1]
      exact h.loadedS
    · exact hmem1.trans h.mem
    · rw [hqNat]; exact hqstr
    · rw [hqNat]; exact fun cs hcs => h.names.bindRegB i h.index q hq cs hcs
    · exact h.names.nameRegB
    · rw [hqNat]; exact fun cs hcs => h.names.bindRegW i h.index q hq cs hcs
    · exact h.names.nameRegW
    · intro R _; rfl
  obtain ⟨c2, hs2, hp⟩ := strcmp_full_spec g1 (BitVec.ofNat 64 q) name
    0x80002abc#64 (f.vars[i]'h.index).1 nameStr m0 c1.σ.sailOutput c1 hpre
  obtain ⟨hG2, hpc2, _hra2, hmem2, _hout2, htick2, hframe2,
    csa, csb, x, hcsa, hcsb, hsa, hsb, hx, hsign⟩ := hp
  have preserve (R : Register) (hR : Vsa.Alloc.AbiPreserved R = true) :
      c2.σ.regs.get? R = c.σ.regs.get? R := by
    rw [hframe2 R (notWrittenStrcmp_of_abiPreserved R hR)]
    exact habi1 R hR
  have hsaved2 : EnvDefineSavedSpillFrame sp saved c2 := by
    apply h.savedSpills.of_mem_eq
    exact hmem2.trans h.mem.symm
  refine ⟨c2, hs1.trans hs2, hG2, ?_, ?_, hmem2, hpc2,
    (preserve Register.x20 (by decide)).trans h.envReg,
    (preserve Register.x18 (by decide)).trans h.nameReg,
    (preserve Register.x21 (by decide)).trans h.value,
    (preserve Register.x19 (by decide)).trans h.countReg,
    (preserve Register.x9 (by decide)).trans h.cursor,
    (preserve Register.x8 (by decide)).trans h.idx,
    (preserve Register.x2 (by decide)).trans h.spReg, h.index, ?_, htick2, h.frame,
    h.names, h.countEq, hsaved2⟩
  · rw [hmem2]
    exact h.mem ▸ h.loadedD
  · rw [hmem2]
    exact h.mem ▸ h.loadedS
  refine ⟨x, csa, csb, hx, hsa.symm, hsb.symm, hsign, ?_⟩
  exact string_eq_iff_strcmpSpecSign_zero m0 q name.toNat
    (f.vars[i]'h.index).1 nameStr csa csb
    (by simpa [hqNat] using hcsa) hcsb hsa hsb

/-- One exact branch result after strcmp: hit, continuing miss, or exhausted miss. -/
def EnvDefineScanBranchPost
    (saved : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (m0 : Mem)
    (hi : i < f.vars.length) (c : Config) : Prop :=
  ((f.vars[i]'hi).1 = nameStr ∧
    ∃ x, EnvDefineScanLivePost envDefineScanHitSeg 0x80002ac0#64
      x (BitVec.ofNat 64 i) (pn + BitVec.ofNat 64 (8 * i)) count
      env name pv sp [] m0 c ∧ EnvDefineSavedSpillFrame sp saved c) ∨
  ((f.vars[i]'hi).1 ≠ nameStr ∧
    ((i + 1 < f.vars.length ∧ ∃ x,
      EnvDefineScanLivePost envDefineScanNextSeg 0x80002ab0#64
        x (BitVec.ofNat 64 i) (pn + BitVec.ofNat 64 (8 * i)) count
        env name pv sp [] m0 c ∧ EnvDefineSavedSpillFrame sp saved c) ∨
     (i + 1 = f.vars.length ∧ ∃ x,
      EnvDefineScanLivePost envDefineScanDoneSeg 0x80002b14#64
        x (BitVec.ofNat 64 i) (pn + BitVec.ofNat 64 (8 * i)) count
        env name pv sp [] m0 c ∧ EnvDefineSavedSpillFrame sp saved c)))

private theorem x_zero_of_strcmpSign_zero (x : BitVec 64)
    (h : strcmpSign x = 0) : x = 0#64 := by
  unfold strcmpSign at h
  by_cases hx : x = 0#64
  · exact hx
  · have hx' : ¬ x = 0 := hx
    rw [if_neg hx'] at h
    by_cases hlt : x.toInt < 0
    · rw [if_pos hlt] at h
      contradiction
    · rw [if_neg hlt] at h
      contradiction

theorem envDefineScanBranchHit
    (saved : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (φf φc : Vsa.While.Addr → Nat) (m0 : Mem) (hi : i < f.vars.length) :
    Triple
      (fun c => EnvDefineScanCmpSt saved env name pv count pn sp i f nameStr
        N φf φc m0 c ∧ (f.vars[i]'hi).1 = nameStr)
      (EnvDefineScanBranchPost saved env name pv count pn sp i f nameStr m0 hi) := by
  intro c ⟨h, hnameEq⟩
  obtain ⟨x, csa, csb, hx, hsa, hsb, hsign, hzero⟩ := h.xres
  have hspec : strcmpSpecSign csa csb = 0 := hzero.mpr hnameEq
  have hx0 : x = 0#64 := x_zero_of_strcmpSign_zero x (hsign.trans hspec)
  have hL : GHolds c.σ
      (envDefineScanLiveL x (BitVec.ofNat 64 i)
        (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp) := by
    exact ⟨by simpa [gprGet] using hx,
      by simpa [gprGet] using h.idx,
      by simpa [gprGet] using h.cursor,
      by simpa [gprGet] using h.countReg,
      by simpa [gprGet] using h.envReg,
      by simpa [gprGet] using h.nameReg,
      by simpa [gprGet] using h.value,
      by simpa [gprGet] using h.spReg, trivial⟩
  have hfacts : ChainFacts c.σ.mem c.σ.mem
      (envDefineScanLiveL x (BitVec.ofNat 64 i)
        (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp) []
      envDefineScanHitSeg := by
    chain_facts h.loadedD with "Vsa.Sim.Code.env_define_at_"
    simp [guardB, envDefineScanLiveL, hx0, srcVal, runGM, lookupG]
  obtain ⟨vmi, hmi⟩ := h.good.minstret
  have hpre : SegPre envDefineScanHitSeg
      (envDefineScanLiveL x (BitVec.ofNat 64 i)
        (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp) []
      0x80002abc#64 m0 c :=
    ⟨h.good, h.mem, h.pc, ⟨vmi, hmi⟩, hL,
      (by show KeysOK [10, 8, 9, 19, 20, 18, 21, 2]; decide), hfacts, h.tick⟩
  obtain ⟨c', hs, hp⟩ := envDefineScanHitLiveRow x (BitVec.ofNat 64 i)
    (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp m0 c hpre
  have hsaved' : EnvDefineSavedSpillFrame sp saved c' := by
    apply h.savedSpills.of_mem_eq
    exact hp.2.1.trans h.mem.symm
  exact ⟨c', hs, Or.inl ⟨hnameEq, x, hp, hsaved'⟩⟩

theorem envDefineScanBranchMiss
    (saved : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (φf φc : Vsa.While.Addr → Nat) (m0 : Mem) (hi : i < f.vars.length) :
    Triple
      (fun c => EnvDefineScanCmpSt saved env name pv count pn sp i f nameStr
        N φf φc m0 c ∧ (f.vars[i]'hi).1 ≠ nameStr)
      (EnvDefineScanBranchPost saved env name pv count pn sp i f nameStr m0 hi) := by
  intro c ⟨h, hnameNe⟩
  obtain ⟨x, csa, csb, hx, _hsa, _hsb, hsign, hzero⟩ := h.xres
  have hspecNe : strcmpSpecSign csa csb ≠ 0 := fun hz => hnameNe (hzero.mp hz)
  have hxNe : x ≠ 0#64 := x10_ne_zero_of_specSign_ne x csa csb hsign hspecNe
  have hL : GHolds c.σ
      (envDefineScanLiveL x (BitVec.ofNat 64 i)
        (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp) := by
    exact ⟨by simpa [gprGet] using hx,
      by simpa [gprGet] using h.idx,
      by simpa [gprGet] using h.cursor,
      by simpa [gprGet] using h.countReg,
      by simpa [gprGet] using h.envReg,
      by simpa [gprGet] using h.nameReg,
      by simpa [gprGet] using h.value,
      by simpa [gprGet] using h.spReg, trivial⟩
  obtain ⟨vmi, hmi⟩ := h.good.minstret
  have hcount : count = BitVec.ofNat 64 f.vars.length := by
    apply BitVec.eq_of_toNat_eq
    rw [h.countEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    rw [← h.countEq]
    exact BitVec.isLt count
  by_cases hn : i + 1 < f.vars.length
  · have hlenLt : f.vars.length < 2^64 := by rw [← h.countEq]; exact count.isLt
    have hiLt : i + 1 < 2^64 := Nat.lt_trans hn hlenLt
    have hcountNe : count ≠ BitVec.ofNat 64 (i + 1) := by
      rw [hcount]
      intro heq
      have heqNat := congrArg BitVec.toNat heq
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlenLt,
        Nat.mod_eq_of_lt hiLt] at heqNat
      omega
    have hfacts : ChainFacts c.σ.mem c.σ.mem
        (envDefineScanLiveL x (BitVec.ofNat 64 i)
          (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp) []
        envDefineScanNextSeg := by
      chain_facts h.loadedD with "Vsa.Sim.Code.env_define_at_"
      simp [guardB, envDefineScanLiveL, hxNe, srcVal, runGM, lookupG]
      change guardB bop.BEQ count (BitVec.ofNat 64 i + 1#64) = false
      rw [ofNat_succ_bv i hiLt]
      simp [guardB, hcountNe]
    have hpre : SegPre envDefineScanNextSeg
        (envDefineScanLiveL x (BitVec.ofNat 64 i)
          (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp) []
        0x80002abc#64 m0 c :=
      ⟨h.good, h.mem, h.pc, ⟨vmi, hmi⟩, hL,
        (by show KeysOK [10, 8, 9, 19, 20, 18, 21, 2]; decide), hfacts, h.tick⟩
    obtain ⟨c', hs, hp⟩ := envDefineScanNextLiveRow x (BitVec.ofNat 64 i)
      (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp m0 c hpre
    have hsaved' : EnvDefineSavedSpillFrame sp saved c' := by
      apply h.savedSpills.of_mem_eq
      exact hp.2.1.trans h.mem.symm
    exact ⟨c', hs, Or.inr ⟨hnameNe, Or.inl ⟨hn, x, hp, hsaved'⟩⟩⟩
  · have heq : i + 1 = f.vars.length := by omega
    have hiLt : i + 1 < 2^64 := by rw [heq, ← h.countEq]; exact count.isLt
    have hcountSucc : count = BitVec.ofNat 64 (i + 1) := by simpa [heq] using hcount
    have hfacts : ChainFacts c.σ.mem c.σ.mem
        (envDefineScanLiveL x (BitVec.ofNat 64 i)
          (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp) []
        envDefineScanDoneSeg := by
      chain_facts h.loadedD with "Vsa.Sim.Code.env_define_at_"
      simp [guardB, envDefineScanLiveL, hxNe, srcVal, runGM, lookupG]
      change guardB bop.BEQ count (BitVec.ofNat 64 i + 1#64) = true
      rw [ofNat_succ_bv i hiLt]
      simp [guardB, hcountSucc]
    have hpre : SegPre envDefineScanDoneSeg
        (envDefineScanLiveL x (BitVec.ofNat 64 i)
          (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp) []
        0x80002abc#64 m0 c :=
      ⟨h.good, h.mem, h.pc, ⟨vmi, hmi⟩, hL,
        (by show KeysOK [10, 8, 9, 19, 20, 18, 21, 2]; decide), hfacts, h.tick⟩
    obtain ⟨c', hs, hp⟩ := envDefineScanDoneLiveRow x (BitVec.ofNat 64 i)
      (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp m0 c hpre
    have hsaved' : EnvDefineSavedSpillFrame sp saved c' := by
      apply h.savedSpills.of_mem_eq
      exact hp.2.1.trans h.mem.symm
    exact ⟨c', hs, Or.inr ⟨hnameNe, Or.inr ⟨heq, x, hp, hsaved'⟩⟩⟩

theorem envDefineScanBranch
    (saved : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (φf φc : Vsa.While.Addr → Nat) (m0 : Mem) (hi : i < f.vars.length) :
    Triple
      (EnvDefineScanCmpSt saved env name pv count pn sp i f nameStr N φf φc m0)
      (EnvDefineScanBranchPost saved env name pv count pn sp i f nameStr m0 hi) := by
  intro c h
  by_cases heq : (f.vars[i]'hi).1 = nameStr
  · exact envDefineScanBranchHit saved env name pv count pn sp i f nameStr N φf φc m0 hi
      c ⟨h, heq⟩
  · exact envDefineScanBranchMiss saved env name pv count pn sp i f nameStr N φf φc m0 hi
      c ⟨h, heq⟩

/-- Marshal the exact non-final branch row back into the semantic scan-head carrier. -/
theorem envDefineScanNextCarrier
    (saved : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp x : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (φf φc : Vsa.While.Addr → Nat) (m0 : Mem) (c : Config)
    (hi : i + 1 < f.vars.length)
    (hloadedD : Vsa.Sim.Code.Env_defineLoaded m0)
    (hloadedS : Vsa.Sim.Code.StrcmpLoaded m0)
    (hframe : FrameRepr m0 N φf φc env.toNat f)
    (hnames : ScanNames m0 pn.toNat name nameStr f)
    (hcount : count.toNat = f.vars.length)
    (hp : EnvDefineScanLivePost envDefineScanNextSeg 0x80002ab0#64
      x (BitVec.ofNat 64 i) (pn + BitVec.ofNat 64 (8 * i)) count
      env name pv sp [] m0 c)
    (hsaved : EnvDefineSavedSpillFrame sp saved c) :
    EnvDefineScanSt saved env name pv count pn sp (i + 1) f nameStr N φf φc m0 c := by
  have hmem : c.σ.mem = m0 := by
    simpa [EnvDefineScanLivePost, envDefineScanNextSeg, evalBlocks,
      SegEvalState.init, writeLog] using hp.2.1
  have hregs := hp.2.2.2.1
  have hlenLt : f.vars.length < 2^64 := by rw [← hcount]; exact count.isLt
  have hiLt : i + 1 < 2^64 := Nat.lt_trans hi hlenLt
  have hcursorLt : 8 * (i + 1) < 2^64 := by
    have := hnames.slotHi (i + 1) hi
    omega
  have reg (n : Nat) (v : BitVec 64)
      (hl : lookupG n (evalBlocks envDefineScanNextSeg
        (SegEvalState.init (envDefineScanLiveL x (BitVec.ofNat 64 i)
          (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp) [])).regs = some v) :
      gprGet c.σ n = some v :=
    gholds_lookup _ hregs hl
  refine ⟨hp.1, ?_, ?_, hmem, hp.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hp.2.2.2.2,
    hframe, hnames, hcount, hi, hsaved⟩
  · rw [hmem]; exact hloadedD
  · rw [hmem]; exact hloadedS
  · simpa [gprGet] using reg 20 env (by rfl)
  · simpa [gprGet] using reg 18 name (by rfl)
  · simpa [gprGet] using reg 21 pv (by rfl)
  · simpa [gprGet] using reg 19 count (by rfl)
  · simpa [cursor_succ_bv pn i hcursorLt, gprGet] using
      reg 9 ((pn + BitVec.ofNat 64 (8 * i)) + 8#64) (by rfl)
  · simpa [ofNat_succ_bv i hiLt, gprGet] using
      reg 8 (BitVec.ofNat 64 i + 1#64) (by rfl)
  · simpa [gprGet] using reg 2 sp (by rfl)

/-- Exact load geometry for `ld s6,8(a0)` in scan initialization. -/
structure EnvDefineScanInitGeom (env pn : BitVec 64) (m : Mem) : Prop where
  read : read64 m (env.toNat + 8) = some pn.toNat
  lo : 0x80000000 ≤ env.toNat + 8
  hi : env.toNat + 16 ≤ 0x100000000
  htif : env.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 8 ≤ env.toNat + 8
  align : (env.toNat + 8) % 8 = 0

private theorem scanInitLdLine :
    mkLine 0x80002a94#64 0x00853b03#32 =
      ⟨0x80002a94#64, 0x00853b03#32, 0x03#8, 0x3b#8, 0x85#8, 0x00#8,
        .ld, 22, 10, 0, 0x008#12⟩ := by rfl

private theorem scanInitZeroLine :
    mkLine 0x80002a98#64 0x00000413#32 =
      ⟨0x80002a98#64, 0x00000413#32, 0x13#8, 0x04#8, 0x00#8, 0x00#8,
        .addi, 8, 0, 0, 0x000#12⟩ := by rfl

private theorem scanInitCursorLine :
    mkLine 0x80002a9c#64 0x000b0493#32 =
      ⟨0x80002a9c#64, 0x000b0493#32, 0x93#8, 0x04#8, 0x0b#8, 0x00#8,
        .addi, 9, 22, 0, 0x000#12⟩ := by rfl

/-- Execute the positive-count dispatch and marshal it into scan index zero. -/
theorem envDefineScanStart
    (saved : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (φf φc : Vsa.While.Addr → Nat) (m0 : Mem)
    (hframe : FrameRepr m0 N φf φc env.toNat f)
    (hnames : ScanNames m0 pn.toNat name nameStr f)
    (hcount : count.toNat = f.vars.length)
    (hpositive : 0 < f.vars.length) (hcountSigned : f.vars.length < 2^31)
    (hgeom : EnvDefineScanInitGeom env pn m0) :
    Triple
      (fun c => GoodState c.σ ∧ Vsa.Sim.Code.Env_defineLoaded c.σ.mem ∧
        Vsa.Sim.Code.StrcmpLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
        c.σ.regs.get? Register.PC = some 0x80002a90#64 ∧
        c.σ.regs.get? Register.x10 = some env ∧
        c.σ.regs.get? Register.x20 = some env ∧
        c.σ.regs.get? Register.x18 = some name ∧
        c.σ.regs.get? Register.x21 = some pv ∧
        c.σ.regs.get? Register.x19 = some count ∧
        c.σ.regs.get? Register.x2 = some sp ∧ c.tick < 2 ∧
        EnvDefineSavedSpillFrame sp saved c)
      (EnvDefineScanSt saved env name pv count pn sp 0 f nameStr N φf φc m0) := by
  intro c h
  obtain ⟨hG, hloadedD, hloadedS, hmem, hpc, hx10, hx20, hx18, hx21, hx19,
    hx2, htick, hsaved⟩ := h
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7,
      hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, _⟩ :=
    read64_bytes_eg4 m0 (env.toNat + 8) pn.toNat hgeom.read
  let bs := [b0, b1, b2, b3, b4, b5, b6, b7]
  have hpins : LPins8 m0 (env.toNat + 8) bs := by
    exact ⟨by simpa [bs] using lpin_of_present hb0,
      by simpa [bs] using lpin_of_present hb1,
      by simpa [bs] using lpin_of_present hb2,
      by simpa [bs] using lpin_of_present hb3,
      by simpa [bs] using lpin_of_present hb4,
      by simpa [bs] using lpin_of_present hb5,
      by simpa [bs] using lpin_of_present hb6,
      by simpa [bs] using lpin_of_present hb7⟩
  have hL : GHolds c.σ (envDefineScanInitLiveL env count name pv sp) := by
    exact ⟨by simpa [gprGet] using hx10, by simpa [gprGet] using hx19,
      by simpa [gprGet] using hx18, by simpa [gprGet] using hx21,
      by simpa [gprGet] using hx2, by simpa [gprGet] using hx20, trivial⟩
  have hfacts : ChainFacts c.σ.mem c.σ.mem
      (envDefineScanInitLiveL env count name pv sp) [bs] envDefineScanInitSeg := by
    chain_facts hloadedD with "Vsa.Sim.Code.env_define_at_"
    · have hcountNat : 2 * count.toNat < 2 ^ 64 := by omega
      have hpos : 0 < count.toInt := by
        rw [BitVec.toInt_eq_toNat_of_lt hcountNat]
        exact_mod_cast (hcount ▸ hpositive)
      unfold guardB
      unfold zopz0zKzJ_s
      rw [decide_eq_false_iff_not]
      simpa only [envDefineScanInitSeg, envDefineScanInitLiveL, srcVal, lookupG, runGM,
        BitVec.toInt_zero, ge_iff_le, Int.not_le] using hpos
    · unfold MemFacts
      have hea :
          (eaddrM (mkLine 0x80002a94#64 0x00853b03#32)
            (runGM [] (envDefineScanInitLiveL env count name pv sp) [bs])).toNat =
            env.toNat + 8 := by
        rw [scanInitLdLine]
        unfold eaddrM
        simp only [runGM, envDefineScanInitLiveL, srcVal, lookupG, reduceCtorEq,
          ↓reduceIte, Option.getD_some, BitVec.toNat_add]
        have himm : (sign_extend (m := 64) (0x008#12) : BitVec 64).toNat = 8 := by decide
        rw [himm]
        have h8 : env.toNat + 8 < 2 ^ 64 := by
          have hhi := hgeom.hi
          omega
        exact Nat.mod_eq_of_lt h8
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [hea]; exact hgeom.lo
      · rw [hea]; exact hgeom.hi
      · rw [hea]; exact hgeom.htif
      · rw [hmem, hea]
        exact hpins
  have hpre : SegPre envDefineScanInitSeg
      (envDefineScanInitLiveL env count name pv sp) [bs] 0x80002a90#64 m0 c :=
    ⟨hG, hmem, hpc, hG.minstret, hL,
      (by show KeysOK [10, 19, 18, 21, 2, 20]; decide), hfacts, htick⟩
  obtain ⟨c', hs, hp⟩ := envDefineScanInitLiveRow env count name pv sp [bs] m0 c hpre
  have hregs := hp.2.2.2.1
  have hpn : (BitVec.ofNat 64 pn.toNat : BitVec 64) = pn := by
    simpa using BitVec.ofNat_toNat 64 pn
  have reg (n : Nat) (v : BitVec 64)
      (hl : lookupG n (evalBlocks envDefineScanInitSeg
        (SegEvalState.init (envDefineScanInitLiveL env count name pv sp) [bs])).regs = some v) :
      gprGet c'.σ n = some v := gholds_lookup _ hregs hl
  have hsaved' : EnvDefineSavedSpillFrame sp saved c' := by
    apply hsaved.of_mem_eq
    exact hp.2.1.trans hmem.symm
  refine ⟨c', hs, hp.1, ?_, ?_, hp.2.1, hp.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hp.2.2.2.2, hframe, hnames, hcount, hpositive, hsaved'⟩
  · rw [hp.2.1]; exact hmem ▸ hloadedD
  · rw [hp.2.1]; exact hmem ▸ hloadedS
  · simpa [gprGet] using reg 20 env (by rfl)
  · simpa [gprGet] using reg 18 name (by rfl)
  · simpa [gprGet] using reg 21 pv (by rfl)
  · simpa [gprGet] using reg 19 count (by rfl)
  · simpa [hpn, gprGet] using reg 9 (BitVec.ofNat 64 pn.toNat) (by
      simp only [envDefineScanInitSeg, scanInitLdLine, scanInitZeroLine, scanInitCursorLine,
        evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,
        stepLdsM, ldsRunM, wvalM, bytesVal, envDefineScanInitLiveL, lookupG,
        eraseG, List.headD, bs]
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 by decide,
        BitVec.add_zero]
      simpa [srcVal, lookupG] using
        (ld_value_eq_read64 m0 (env.toNat + 8) pn.toNat
          b0 b1 b2 b3 b4 b5 b6 b7 hgeom.read hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7))
  · simpa [gprGet] using reg 8 0#64 (by rfl)
  · simpa [gprGet] using reg 2 sp (by rfl)

/-- All slots before `i` have been ruled out by prior exact strcmp calls. -/
def EnvDefineNamesMissBefore (f : Vsa.While.Frame) (nameStr : String) (i : Nat) : Prop :=
  ∀ j (hj : j < f.vars.length), j < i → (f.vars[j]'hj).1 ≠ nameStr

/-- Semantic and machine exit of the finite scan: a first hit, or exhaustive miss. -/
def EnvDefineScanResult
    (saved : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64) (f : Vsa.While.Frame)
    (nameStr : String) (m0 : Mem) (c : Config) : Prop :=
  (∃ i, ∃ hi : i < f.vars.length,
    EnvDefineNamesMissBefore f nameStr i ∧ (f.vars[i]'hi).1 = nameStr ∧
    ∃ x, EnvDefineScanLivePost envDefineScanHitSeg 0x80002ac0#64
      x (BitVec.ofNat 64 i) (pn + BitVec.ofNat 64 (8 * i)) count
      env name pv sp [] m0 c ∧ EnvDefineSavedSpillFrame sp saved c) ∨
  ((∀ j (hj : j < f.vars.length), (f.vars[j]'hj).1 ≠ nameStr) ∧
    ∃ i, i + 1 = f.vars.length ∧ ∃ x,
      EnvDefineScanLivePost envDefineScanDoneSeg 0x80002b14#64
        x (BitVec.ofNat 64 i) (pn + BitVec.ofNat 64 (8 * i)) count
        env name pv sp [] m0 c ∧ EnvDefineSavedSpillFrame sp saved c)

/-- Total finite scan, proved by the decreasing number of unvisited slots. -/
theorem envDefineScanFinite
    (saved : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (φf φc : Vsa.While.Addr → Nat) (m0 : Mem) (hi : i < f.vars.length) :
    Triple
      (fun c => EnvDefineScanSt saved env name pv count pn sp i f nameStr
        N φf φc m0 c ∧ EnvDefineNamesMissBefore f nameStr i)
      (EnvDefineScanResult saved env name pv count pn sp f nameStr m0) := by
  intro c ⟨h, hmiss⟩
  obtain ⟨c', hs, hb⟩ :=
    (envDefineScanCompare saved env name pv count pn sp i f nameStr N φf φc m0).seq
      (envDefineScanBranch saved env name pv count pn sp i f nameStr N φf φc m0 hi)
      c h
  rcases hb with hhit | ⟨hnameNe, hnext | hdone⟩
  · obtain ⟨hnameEq, x, hp, hsaved⟩ := hhit
    exact ⟨c', hs, Or.inl ⟨i, hi, hmiss, hnameEq, x, hp, hsaved⟩⟩
  · obtain ⟨hn, x, hp, hsaved⟩ := hnext
    have hloadedD : Vsa.Sim.Code.Env_defineLoaded m0 := by rw [← h.mem]; exact h.loadedD
    have hloadedS : Vsa.Sim.Code.StrcmpLoaded m0 := by rw [← h.mem]; exact h.loadedS
    have hhead := envDefineScanNextCarrier saved env name pv count pn sp x i f nameStr
      N φf φc m0 c' hn hloadedD hloadedS h.frame h.names h.countEq hp hsaved
    have hmiss' : EnvDefineNamesMissBefore f nameStr (i + 1) := by
      intro j hj hjlt
      by_cases hji : j = i
      · subst j
        simpa using hnameNe
      · exact hmiss j hj (by omega)
    obtain ⟨c'', hs', hr⟩ :=
      envDefineScanFinite saved env name pv count pn sp (i + 1) f nameStr N φf φc m0 hn
        c' ⟨hhead, hmiss'⟩
    exact ⟨c'', hs.trans hs', hr⟩
  · obtain ⟨heq, x, hp, hsaved⟩ := hdone
    have hall : ∀ j (hj : j < f.vars.length), (f.vars[j]'hj).1 ≠ nameStr := by
      intro j hj
      by_cases hji : j = i
      · subst j
        simpa using hnameNe
      · exact hmiss j hj (by omega)
    exact ⟨c', hs, Or.inr ⟨hall, i, heq, x, hp, hsaved⟩⟩
termination_by f.vars.length - i
decreasing_by omega

#print axioms envDefineScanCompare
#print axioms envDefineScanBranch
#print axioms envDefineScanNextCarrier
#print axioms envDefineScanFinite

end Vsa.Sim
