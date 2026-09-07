import Vsa.Sim.rows.EnvDefineAppendPrefix
import Vsa.Sim.rows.EnvDefineGrowExact
import Vsa.Sim.rows.EnvDefineScanFramed
import Vsa.Sim.DecodeTable.Batch03Part11
import Vsa.Sim.DecodeTable.Batch08Part22

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.Logic (Triple)
open Vsa.MemRepr
open Vsa.RuntimeRepr
open Vsa.Alloc

namespace Vsa.Sim

theorem envDefineCapSigned_of_heap
    {A : Arena} {exts : List Extent} {m0 : Mem}
    {phif : Vsa.While.Addr → Nat} {target : Vsa.While.Addr}
    {f : Vsa.While.Frame} {cap : Nat}
    (harena : HeapArena A exts)
    (howned : FrameHeapOwned m0 phif exts target f)
    (hcap : read32 m0 (phif target + 4) = some cap)
    (hAhi : A.hi ≤ 2^32) : cap < 2^31 := by
  obtain ⟨cap', pn', pv', hcap', _hnames, _hvals, _hcount,
    _hnamesMem, hvalsMem, _hnamesOwned⟩ := howned.arrays
  have hcapEq : cap' = cap := Option.some.inj (hcap'.symm.trans hcap)
  subst cap'
  obtain ⟨_hpositive, hvalsArena⟩ := harena.1 (pv', 24 * cap) hvalsMem
  change A.lo ≤ pv' ∧ pv' + 24 * cap ≤ A.hi at hvalsArena
  omega

/-- The exact positive-count scan prefix and its finite first-hit/exhaustive-
miss loop, with the allocator, ABI and saved-spill frames retained. -/
theorem envDefineScanDispatchFramed
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List (Nat × Nat))
    (saved gm : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (phif phic : Vsa.While.Addr → Nat) (m0 : Mem)
    (hframe : FrameRepr m0 N phif phic env.toNat f)
    (hnames : ScanNames m0 pn.toNat name nameStr f)
    (hcount : count.toNat = f.vars.length)
    (hpositive : 0 < f.vars.length) (hcountSigned : f.vars.length < 2^31)
    (hgeom : EnvDefineScanInitGeom env pn m0)
    (hAInvStable : ∀ (sigmaa sigmab : Vsa.Machine.MState),
      sigmaa.regs.get? Register.x3 = sigmab.regs.get? Register.x3 →
      (∀ a : Nat, sigmaa.mem[a]? = sigmab.mem[a]?) →
      M.AInv sigmaa exts → M.AInv sigmab exts) :
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
        EnvDefineSavedSpillFrame sp saved c ∧
        EnvDefineScanEntryFrame M exts sp gm c)
      (EnvDefineScanFramedResult M exts saved (envDefineScanBaseGhost gm pn)
        env name pv count pn sp f nameStr m0) := by
  exact Triple.seq
    (envDefineScanStartFramed M exts saved gm env name pv count pn sp f nameStr
      N phif phic m0 hframe hnames hcount hpositive hcountSigned hgeom hAInvStable)
    (fun c h =>
      envDefineScanFiniteFramed M exts saved (envDefineScanBaseGhost gm pn)
        env name pv count pn sp 0 f nameStr N phif phic m0 hpositive hAInvStable
        c ⟨h, by intro _ _ hj; omega⟩)

#print axioms envDefineScanDispatchFramed

/- Exact missing-name cap check. The two variants differ only in branch polarity. -/
#derive_case envDefineCapAppendSeg chain
  [(0x80002b14#64, 0x004a2783#32)]
    terminator ⟨0x80002b18#64, 0x07378c63#32, 0x63#8, 0x8c#8, 0x37#8, 0x07#8,
      .br bop.BEQ false, 15, 19, 0x0078#13, 0#21, 0#12⟩

#derive_case envDefineCapGrowSeg chain
  [(0x80002b14#64, 0x004a2783#32)]
    terminator ⟨0x80002b18#64, 0x07378c63#32, 0x63#8, 0x8c#8, 0x37#8, 0x07#8,
      .br bop.BEQ true, 15, 19, 0x0078#13, 0#21, 0#12⟩

private theorem envDefineCapLoadLine :
    mkLine 0x80002b14#64 0x004a2783#32 =
      ⟨0x80002b14#64, 0x004a2783#32, 0x83#8, 0x27#8, 0x4a#8, 0x00#8,
        .lw, 15, 20, 0, 0x004#12⟩ := by rfl

def envDefineCapL (env count : BitVec 64) : GRegs := [(20, env), (19, count)]

def EnvDefineCapPost (seg : List BBlock) (pc : BitVec 64)
    (env count : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Mem) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some pc ∧
  GHolds c.σ (evalBlocks seg
    (SegEvalState.init (envDefineCapL env count) lds)).regs ∧
  c.tick < 2

def EnvDefineCapFramedPost
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List (Nat × Nat))
    (gm : (R : Register) → Option (RegisterType R))
    (idx cursor sp : BitVec 64) (seg : List BBlock) (pc env count : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) (c : Config) : Prop :=
  EnvDefineCapPost seg pc env count lds m0 c ∧
  EnvDefineScanFrame M exts sp gm idx cursor c

theorem envDefineCapRowFramed
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List (Nat × Nat))
    (gm : (R : Register) → Option (RegisterType R))
    (idx cursor sp : BitVec 64) (seg : List BBlock) (target env count : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem)
    (hwf : ChainOK 0x80002b14#64 [20, 19] seg)
    (hpcEval : evalBlocksPC 0x80002b14#64
      (SegEvalState.init (envDefineCapL env count) lds) seg = target)
    (hmemEval : writeLog m0 (evalBlocks seg
      (SegEvalState.init (envDefineCapL env count) lds)).log = m0)
    (hAvoid : WrChainAvoidAbi seg)
    (hAInvStable : ∀ (sigmaa sigmab : Vsa.Machine.MState),
      sigmaa.regs.get? Register.x3 = sigmab.regs.get? Register.x3 →
      (∀ a : Nat, sigmaa.mem[a]? = sigmab.mem[a]?) →
      M.AInv sigmaa exts → M.AInv sigmab exts) :
    Triple
      (fun c => SegPre seg (envDefineCapL env count) lds 0x80002b14#64 m0 c ∧
        EnvDefineScanFrame M exts sp gm idx cursor c)
      (EnvDefineCapFramedPost M exts gm idx cursor sp seg target env count lds m0) := by
  intro c ⟨hseg, hframe⟩
  obtain ⟨hG0, hmem0, hpc0, ⟨vmi, hmi0⟩, hL0, hkeys0, hfacts0, htick0⟩ := hseg
  obtain ⟨sigma', i', hsteps, htick', hG', hmem', _hout, hpc', _hmi', hregs', hraw⟩ :=
    segEval_sound seg c.σ c.tick c.steps 0x80002b14#64 vmi
      (envDefineCapL env count) lds hG0 hpc0 hmi0 hL0 hkeys0 hfacts0 hwf htick0
  rw [hmem0] at hmem'
  let c' : Config := ⟨sigma', i', c.steps + evalBlocksFuel seg⟩
  have hmemEq : c'.σ.mem = c.σ.mem := by rw [hmem', hmemEval, hmem0]
  have habi : ∀ R, AbiPreserved R = true →
      c'.σ.regs.get? R = c.σ.regs.get? R :=
    frame_of_wrChain_avoids_abi hAvoid hraw
  have hframe' : EnvDefineScanFrame M exts sp gm idx cursor c' := by
    refine ⟨hframe.stack, (habi Register.x3 (by decide)).trans hframe.gp, ?_, ?_⟩
    · intro R hR
      exact (habi R hR).trans (hframe.abi R hR)
    · exact hAInvStable c.σ c'.σ
        (habi Register.x3 (by decide)).symm
        (fun a => by rw [hmemEq]) hframe.ainv
  refine ⟨c', hsteps, ?_, hframe'⟩
  exact ⟨hG', by rw [hmem', hmemEval], by simpa [hpcEval] using hpc', hregs', htick'⟩

theorem envDefineCapAppendRow (env count : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) :
    Triple
      (SegPre envDefineCapAppendSeg (envDefineCapL env count) lds
        0x80002b14#64 m0)
      (EnvDefineCapPost envDefineCapAppendSeg 0x80002b1c#64
        env count lds m0) := by
  apply segToTriple envDefineCapAppendSeg (envDefineCapL env count) lds
    0x80002b14#64 m0 _
    (by show ChainOK 0x80002b14#64 [20, 19] envDefineCapAppendSeg; decide)
  intro σ' i' u' hG' hi' hmem' hpc' _hmi' hregs'
  refine ⟨hG', ?_, ?_, hregs', hi'⟩
  · simpa [envDefineCapAppendSeg, evalBlocks, SegEvalState.init, writeLog] using hmem'
  · rw [hpc']; rfl

theorem envDefineCapGrowRow (env count : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) :
    Triple
      (SegPre envDefineCapGrowSeg (envDefineCapL env count) lds
        0x80002b14#64 m0)
      (EnvDefineCapPost envDefineCapGrowSeg 0x80002b90#64
        env count lds m0) := by
  apply segToTriple envDefineCapGrowSeg (envDefineCapL env count) lds
    0x80002b14#64 m0 _
    (by show ChainOK 0x80002b14#64 [20, 19] envDefineCapGrowSeg; decide)
  intro σ' i' u' hG' hi' hmem' hpc' _hmi' hregs'
  refine ⟨hG', ?_, ?_, hregs', hi'⟩
  · simpa [envDefineCapGrowSeg, evalBlocks, SegEvalState.init, writeLog] using hmem'
  · rw [hpc']; rfl

theorem envDefineCapAppendRowFramed
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List (Nat × Nat))
    (gm : (R : Register) → Option (RegisterType R))
    (idx cursor sp env count : BitVec 64) (lds : List (List (BitVec 8))) (m0 : Mem)
    (hAInvStable : ∀ (sigmaa sigmab : Vsa.Machine.MState),
      sigmaa.regs.get? Register.x3 = sigmab.regs.get? Register.x3 →
      (∀ a : Nat, sigmaa.mem[a]? = sigmab.mem[a]?) →
      M.AInv sigmaa exts → M.AInv sigmab exts) :
    Triple
      (fun c => SegPre envDefineCapAppendSeg (envDefineCapL env count) lds
          0x80002b14#64 m0 c ∧ EnvDefineScanFrame M exts sp gm idx cursor c)
      (EnvDefineCapFramedPost M exts gm idx cursor sp envDefineCapAppendSeg
        0x80002b1c#64 env count lds m0) := by
  apply envDefineCapRowFramed M exts gm idx cursor sp envDefineCapAppendSeg
    0x80002b1c#64 env count lds m0
  · decide
  · rfl
  · rfl
  · decide
  · exact hAInvStable

theorem envDefineCapGrowRowFramed
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List (Nat × Nat))
    (gm : (R : Register) → Option (RegisterType R))
    (idx cursor sp env count : BitVec 64) (lds : List (List (BitVec 8))) (m0 : Mem)
    (hAInvStable : ∀ (sigmaa sigmab : Vsa.Machine.MState),
      sigmaa.regs.get? Register.x3 = sigmab.regs.get? Register.x3 →
      (∀ a : Nat, sigmaa.mem[a]? = sigmab.mem[a]?) →
      M.AInv sigmaa exts → M.AInv sigmab exts) :
    Triple
      (fun c => SegPre envDefineCapGrowSeg (envDefineCapL env count) lds
          0x80002b14#64 m0 c ∧ EnvDefineScanFrame M exts sp gm idx cursor c)
      (EnvDefineCapFramedPost M exts gm idx cursor sp envDefineCapGrowSeg
        0x80002b90#64 env count lds m0) := by
  apply envDefineCapRowFramed M exts gm idx cursor sp envDefineCapGrowSeg
    0x80002b90#64 env count lds m0
  · decide
  · rfl
  · rfl
  · decide
  · exact hAInvStable

/-- Address geometry shared by all env-owned header and array accesses. -/
structure EnvDefineArenaGeom (A : Arena) : Prop where
  ramLo : 0x80000000 ≤ A.lo
  ramHi : A.hi ≤ 0x100000000
  htif : A.hi ≤ tohostAddr ∨ tohostAddr + 8 ≤ A.lo

def EnvDefineMissCapResult
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (saved gm : (R : Register) → Option (RegisterType R))
    (env count pn sp : BitVec 64) (f : Vsa.While.Frame)
    (m0 : Mem) (c : Config) : Prop :=
  ∃ cap, (f.vars.length < cap ∧ ∃ i lds,
    i + 1 = f.vars.length ∧
    EnvDefineCapFramedPost M exts gm (BitVec.ofNat 64 (i + 1))
      (pn + BitVec.ofNat 64 (8 * (i + 1))) sp envDefineCapAppendSeg
      0x80002b1c#64 env count lds m0 c ∧
    EnvDefineSavedSpillFrame sp saved c) ∨
  (f.vars.length = cap ∧ ∃ i lds,
    i + 1 = f.vars.length ∧
    EnvDefineCapFramedPost M exts gm (BitVec.ofNat 64 (i + 1))
      (pn + BitVec.ofNat 64 (8 * (i + 1))) sp envDefineCapGrowSeg
      0x80002b90#64 env count lds m0 c ∧
    EnvDefineSavedSpillFrame sp saved c)

/-- Turn the exhaustive scan miss into the exact append/grow cap branch.  The
signed `lw` fact is derived from the owned values-array extent and bounded
arena, rather than assumed as an unrelated arithmetic oracle. -/
theorem envDefineMissCapDispatch
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (saved gm : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64)
    (f : Vsa.While.Frame) (nameStr : String) (m0 : Mem)
    (phif : Vsa.While.Addr → Nat) (target : Vsa.While.Addr)
    (henv : env.toNat = phif target)
    (howned : FrameHeapOwned m0 phif exts target f)
    (harena : HeapArena A exts) (hgeom : EnvDefineArenaGeom A)
    (henvArena : A.contains env.toNat 32) (henvAlign : env.toNat % 8 = 0)
    (hcount : count.toNat = f.vars.length)
    (hAInvStable : ∀ (sigmaa sigmab : Vsa.Machine.MState),
      sigmaa.regs.get? Register.x3 = sigmab.regs.get? Register.x3 →
      (∀ a : Nat, sigmaa.mem[a]? = sigmab.mem[a]?) →
      M.AInv sigmaa exts → M.AInv sigmab exts) :
    Triple
      (fun c =>
        (∀ j (hj : j < f.vars.length), (f.vars[j]'hj).1 ≠ nameStr) ∧
        ∃ i, i + 1 = f.vars.length ∧ ∃ x,
          EnvDefineScanLivePost envDefineScanDoneSeg 0x80002b14#64
            x (BitVec.ofNat 64 i) (pn + BitVec.ofNat 64 (8 * i)) count
            env name pv sp [] m0 c ∧ EnvDefineSavedSpillFrame sp saved c ∧
          EnvDefineScanFrame M exts sp gm (BitVec.ofNat 64 (i + 1))
            (pn + BitVec.ofNat 64 (8 * (i + 1))) c)
      (EnvDefineMissCapResult M exts saved gm env count pn sp f m0) := by
  intro c h
  obtain ⟨_hall, i, hiLen, x, hdone, hsaved, hscanFrame⟩ := h
  obtain ⟨cap, names, vals, hcap, _hnames, _hvals, hlenCap,
    _hnamesMem, _hvalsMem, _hnamesOwned⟩ := howned.arrays
  have hcapAddr : phif target + 4 = env.toNat + 4 := by omega
  have hcap' : read32 m0 (env.toNat + 4) = some cap := by
    rw [← hcapAddr]
    exact hcap
  have hcapSigned : cap < 2^31 := by
    apply envDefineCapSigned_of_heap harena howned hcap
    exact hgeom.ramHi
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, hrec⟩ :=
    read32_bytes_ed m0 (env.toNat + 4) cap hcap'
  let bs := [b0, b1, b2, b3]
  have hpins : LPins4 m0 (env.toNat + 4) bs := by
    exact ⟨by simpa [bs] using lpin_of_present hb0,
      by simpa [bs] using lpin_of_present hb1,
      by simpa [bs] using lpin_of_present hb2,
      by simpa [bs] using lpin_of_present hb3⟩
  have hcapWord : bytesVal .lw bs = BitVec.ofNat 64 cap := by
    simpa [bytesVal, bs] using sext_count_ed b0 b1 b2 b3 cap hcapSigned hrec
  have hmem : c.σ.mem = m0 := by
    simpa [EnvDefineScanLivePost, envDefineScanDoneSeg, evalBlocks,
      SegEvalState.init, writeLog] using hdone.2.1
  have hregs := hdone.2.2.2.1
  have reg (n : Nat) (w : BitVec 64)
      (hl : lookupG n (evalBlocks envDefineScanDoneSeg
        (SegEvalState.init (envDefineScanLiveL x (BitVec.ofNat 64 i)
          (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp) [])).regs = some w) :
      gprGet c.σ n = some w := gholds_lookup _ hregs hl
  have hL : GHolds c.σ (envDefineCapL env count) := by
    exact ⟨by simpa [gprGet] using reg 20 env (by rfl),
      by simpa [gprGet] using reg 19 count (by rfl), trivial⟩
  obtain ⟨spillLds, himage, hspillValues⟩ := hsaved
  have hsaved0 : EnvDefineSavedSpillFrame sp saved c :=
    ⟨spillLds, himage, hspillValues⟩
  have hloaded : Vsa.Sim.Code.Env_defineLoaded m0 := by
    rw [← hmem]
    exact himage.1
  change A.lo ≤ env.toNat ∧ env.toNat + 32 ≤ A.hi at henvArena
  obtain ⟨henvLo, henvHi⟩ := henvArena
  have hfieldLo : 0x80000000 ≤ env.toNat + 4 := by
    have := hgeom.ramLo
    omega
  have hfieldHi : env.toNat + 8 ≤ 0x100000000 := by
    have := hgeom.ramHi
    omega
  have hfieldHtif : env.toNat + 8 ≤ tohostAddr ∨
      tohostAddr + 8 ≤ env.toNat + 4 := by
    rcases hgeom.htif with hbefore | hafter
    · left; omega
    · right; omega
  have hfieldAlign : (env.toNat + 4) % 4 = 0 := by
    have hd8 : 8 ∣ env.toNat := Nat.dvd_of_mod_eq_zero henvAlign
    obtain ⟨k, hk⟩ := hd8
    rw [hk]
    omega
  by_cases hlt : f.vars.length < cap
  · have hneNat : cap ≠ f.vars.length := by omega
    have hneBV : BitVec.ofNat 64 cap ≠ count := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hcount] at this
      omega
    have hfacts : ChainFacts c.σ.mem c.σ.mem (envDefineCapL env count) [bs]
        envDefineCapAppendSeg := by
      chain_facts himage.1 with "Vsa.Sim.Code.env_define_at_"
      · unfold MemFacts
        have hea : (eaddrM (mkLine 0x80002b14#64 0x004a2783#32)
            (envDefineCapL env count)).toNat = env.toNat + 4 := by
          rw [envDefineCapLoadLine]
          unfold eaddrM
          simp only [runGM, envDefineCapL, srcVal, lookupG, ↓reduceIte,
            Option.getD_some, BitVec.toNat_add]
          have himm : (sign_extend (m := 64) (0x004#12) : BitVec 64).toNat = 4 := by decide
          rw [himm]
          have h4 : env.toNat + 4 < 2^64 := by omega
          exact Nat.mod_eq_of_lt h4
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · rw [hea]; exact hfieldLo
        · rw [hea]; exact hfieldHi
        · rw [hea]; exact hfieldHtif
        · rw [hmem, hea]
          exact hpins
      · simp only [envDefineCapAppendSeg, evalBlocks, evalBlock, SegEvalState.init]
        rw [envDefineCapLoadLine]
        simp only [runGM, stepGM, stepLdsM, ldsRunM, wvalM]
        change guardB bop.BEQ
          (srcVal 15 ((15, bytesVal MKind.lw bs) :: eraseG 15 (envDefineCapL env count)))
          (srcVal 19 ((15, bytesVal MKind.lw bs) :: eraseG 15 (envDefineCapL env count))) = false
        rw [hcapWord]
        simp [envDefineCapL, guardB, hneBV, srcVal, lookupG, eraseG]
    have hpre : SegPre envDefineCapAppendSeg (envDefineCapL env count) [bs]
        0x80002b14#64 m0 c :=
      ⟨hdone.1, hmem, hdone.2.2.1, hdone.1.minstret, hL,
        (by show KeysOK [20, 19]; decide), hfacts, hdone.2.2.2.2⟩
    obtain ⟨c', hsteps, hpost, hframe'⟩ :=
      envDefineCapAppendRowFramed M exts gm (BitVec.ofNat 64 (i + 1))
        (pn + BitVec.ofNat 64 (8 * (i + 1))) sp env count [bs] m0 hAInvStable
        c ⟨hpre, hscanFrame⟩
    have hsaved' : EnvDefineSavedSpillFrame sp saved c' :=
      EnvDefineSavedSpillFrame.of_mem_eq (hpost.2.1.trans hmem.symm) hsaved0
    exact ⟨c', hsteps, cap, Or.inl ⟨hlt, i, [bs], hiLen,
      ⟨hpost, hframe'⟩, hsaved'⟩⟩
  · have heqNat : f.vars.length = cap := by omega
    have heqBV : BitVec.ofNat 64 cap = count := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hcount, heqNat]
    have hfacts : ChainFacts c.σ.mem c.σ.mem (envDefineCapL env count) [bs]
        envDefineCapGrowSeg := by
      chain_facts himage.1 with "Vsa.Sim.Code.env_define_at_"
      · unfold MemFacts
        have hea : (eaddrM (mkLine 0x80002b14#64 0x004a2783#32)
            (envDefineCapL env count)).toNat = env.toNat + 4 := by
          rw [envDefineCapLoadLine]
          unfold eaddrM
          simp only [runGM, envDefineCapL, srcVal, lookupG, ↓reduceIte,
            Option.getD_some, BitVec.toNat_add]
          have himm : (sign_extend (m := 64) (0x004#12) : BitVec 64).toNat = 4 := by decide
          rw [himm]
          have h4 : env.toNat + 4 < 2^64 := by omega
          exact Nat.mod_eq_of_lt h4
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · rw [hea]; exact hfieldLo
        · rw [hea]; exact hfieldHi
        · rw [hea]; exact hfieldHtif
        · rw [hmem, hea]
          exact hpins
      · simp only [envDefineCapGrowSeg, evalBlocks, evalBlock, SegEvalState.init]
        rw [envDefineCapLoadLine]
        simp only [runGM, stepGM, stepLdsM, ldsRunM, wvalM]
        change guardB bop.BEQ
          (srcVal 15 ((15, bytesVal MKind.lw bs) :: eraseG 15 (envDefineCapL env count)))
          (srcVal 19 ((15, bytesVal MKind.lw bs) :: eraseG 15 (envDefineCapL env count))) = true
        rw [hcapWord]
        simp [envDefineCapL, guardB, heqBV, srcVal, lookupG, eraseG]
    have hpre : SegPre envDefineCapGrowSeg (envDefineCapL env count) [bs]
        0x80002b14#64 m0 c :=
      ⟨hdone.1, hmem, hdone.2.2.1, hdone.1.minstret, hL,
        (by show KeysOK [20, 19]; decide), hfacts, hdone.2.2.2.2⟩
    obtain ⟨c', hsteps, hpost, hframe'⟩ :=
      envDefineCapGrowRowFramed M exts gm (BitVec.ofNat 64 (i + 1))
        (pn + BitVec.ofNat 64 (8 * (i + 1))) sp env count [bs] m0 hAInvStable
        c ⟨hpre, hscanFrame⟩
    have hsaved' : EnvDefineSavedSpillFrame sp saved c' :=
      EnvDefineSavedSpillFrame.of_mem_eq (hpost.2.1.trans hmem.symm) hsaved0
    exact ⟨c', hsteps, cap, Or.inr ⟨heqNat, i, [bs], hiLen,
      ⟨hpost, hframe'⟩, hsaved'⟩⟩

/-- The append cap arm already contains the complete carried frame needed by
the exact strlen prefix.  This is a zero-step ABI marshal, not a machine-stage
oracle. -/
theorem envDefineAppendEntry_of_cap
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (saved gm : (R : Register) → Option (RegisterType R))
    (idx cursor sp env name count : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) (nameStr : String)
    (hghostSp : envDefineScanGhost gm idx cursor Register.x2 = some sp)
    (hghostName : envDefineScanGhost gm idx cursor Register.x18 = some name)
    (hstrlen : Vsa.Sim.Code.StrlenLoaded m0)
    (hregions : StrRegions name nameStr.length)
    (halign : name.toNat % 8 = 0) (hcstr : CString m0 name.toNat nameStr) :
    Triple
      (fun c => EnvDefineCapFramedPost M exts gm idx cursor sp
          envDefineCapAppendSeg 0x80002b1c#64 env count lds m0 c ∧
        EnvDefineSavedSpillFrame sp saved c)
      (fun c => AppendStrlenEntry SL gpv headroom M.AInv exts sp
          (envDefineScanGhost gm idx cursor) name nameStr m0 c ∧
        EnvDefineSavedSpillFrame sp saved c) := by
  intro c ⟨hcap, hsaved⟩
  obtain ⟨hpost, hframe⟩ := hcap
  have hsp : c.σ.regs.get? Register.x2 = some sp :=
    (hframe.abi Register.x2 (by decide)).trans hghostSp
  have hname : c.σ.regs.get? Register.x18 = some name :=
    (hframe.abi Register.x18 (by decide)).trans hghostName
  have hloaded : Vsa.Sim.Code.Env_defineLoaded c.σ.mem := by
    obtain ⟨_spillLds, himage, _hvalues⟩ := hsaved
    exact himage.1
  have hspill : EnvDefineSpillFrame sp (envDefineScanGhost gm idx cursor) c := by
    obtain ⟨spillLds, himage, _hvalues⟩ := hsaved
    exact ⟨spillLds, himage⟩
  refine ⟨c, Vsa.Machine.Steps.refl c, ?_⟩
  exact ⟨⟨hpost.1, hloaded, (by rw [hpost.2.1]; exact hstrlen),
    hpost.2.1, hpost.2.2.1, hname, hpost.1.minstret, hpost.2.2.2.2,
    hregions, halign, hcstr,
    hsp, hframe.stack, hframe.gp, hframe.abi, hframe.ainv,
    hpost.2.2.2.2, hspill⟩, hsaved⟩

#print axioms envDefineCapAppendRow
#print axioms envDefineCapGrowRow
#print axioms envDefineCapAppendRowFramed
#print axioms envDefineCapGrowRowFramed
#print axioms envDefineMissCapDispatch

end Vsa.Sim
