import Vsa.Sim.rows.EnvDefineScanLoop
import Vsa.Sim.SegToTripleFramed
import Vsa.Sim.BridgeSegFramed
import Vsa.Alloc

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.MemRepr
open Vsa.RuntimeRepr
open Vsa.Logic (Triple)
open Vsa.Alloc (AbiPreserved StackLayout StackOK MallocContract)

namespace Vsa.Sim

set_option maxHeartbeats 1600000

/-- The scan changes `s0`/`s1` (`x8`/`x9`) deliberately.  Its ABI ghost is
therefore the caller ghost reseated at the current index and name-slot cursor. -/
def envDefineScanGhost
    (gm : (R : Register) → Option (RegisterType R))
    (idx cursor : BitVec 64) : (R : Register) → Option (RegisterType R) :=
  fun R =>
    if h8 : R = Register.x8 then some (h8 ▸ idx)
    else if h9 : R = Register.x9 then some (h9 ▸ cursor)
    else gm R

@[simp] theorem envDefineScanGhost_x8
    (gm : (R : Register) → Option (RegisterType R)) (idx cursor : BitVec 64) :
    envDefineScanGhost gm idx cursor Register.x8 = some idx := by
  simp [envDefineScanGhost]

@[simp] theorem envDefineScanGhost_x9
    (gm : (R : Register) → Option (RegisterType R)) (idx cursor : BitVec 64) :
    envDefineScanGhost gm idx cursor Register.x9 = some cursor := by
  simp [envDefineScanGhost]

theorem envDefineScanGhost_ne
    (gm : (R : Register) → Option (RegisterType R)) (idx cursor : BitVec 64)
    {R : Register} (h8 : R ≠ Register.x8) (h9 : R ≠ Register.x9) :
    envDefineScanGhost gm idx cursor R = gm R := by
  simp [envDefineScanGhost, h8, h9]

/-- Initialization also loads the names-vector base into `s6`/`x22`.  Record
that deliberate callee-saved reseat before the loop starts. -/
def envDefineScanBaseGhost
    (gm : (R : Register) → Option (RegisterType R))
    (pn : BitVec 64) : (R : Register) → Option (RegisterType R) :=
  fun R => if h22 : R = Register.x22 then some (h22 ▸ pn) else gm R

@[simp] theorem envDefineScanBaseGhost_x22
    (gm : (R : Register) → Option (RegisterType R)) (pn : BitVec 64) :
    envDefineScanBaseGhost gm pn Register.x22 = some pn := by
  simp [envDefineScanBaseGhost]

theorem envDefineScanBaseGhost_ne
    (gm : (R : Register) → Option (RegisterType R)) (pn : BitVec 64)
    {R : Register} (h22 : R ≠ Register.x22) :
    envDefineScanBaseGhost gm pn R = gm R := by
  simp [envDefineScanBaseGhost, h22]

/-- The allocator/caller frame at scan entry, before `s0` and `s1` are
initialized for the loop. -/
structure EnvDefineScanEntryFrame
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (exts : List (Nat × Nat)) (sp : BitVec 64)
    (gm : (R : Register) → Option (RegisterType R)) (c : Config) : Prop where
  stack : StackOK SL sp headroom
  gp : c.σ.regs.get? Register.x3 = some gpv
  abi : ∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R
  ainv : M.AInv c.σ exts

/-- The same frame while scanning.  The full ABI relation is retained against
the dynamically reseated `s0`/`s1` ghost. -/
structure EnvDefineScanFrame
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (exts : List (Nat × Nat)) (sp : BitVec 64)
    (gm : (R : Register) → Option (RegisterType R))
    (idx cursor : BitVec 64) (c : Config) : Prop where
  stack : StackOK SL sp headroom
  gp : c.σ.regs.get? Register.x3 = some gpv
  abi : ∀ R, AbiPreserved R = true →
    c.σ.regs.get? R = envDefineScanGhost gm idx cursor R
  ainv : M.AInv c.σ exts

/-- Rebuild the scan frame after an exact memory-free row.  Only `x8` and
`x9` may be reseated. -/
theorem EnvDefineScanFrame.reseat
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {exts : List (Nat × Nat)} {sp oldIdx oldCursor newIdx newCursor : BitVec 64}
    {gm : (R : Register) → Option (RegisterType R)} {c c' : Config}
    (h : EnvDefineScanFrame M exts sp gm oldIdx oldCursor c)
    (hmem : c'.σ.mem = c.σ.mem)
    (hreg : ∀ R, AbiPreserved R = true → R ≠ Register.x8 → R ≠ Register.x9 →
      c'.σ.regs.get? R = c.σ.regs.get? R)
    (hx8 : c'.σ.regs.get? Register.x8 = some newIdx)
    (hx9 : c'.σ.regs.get? Register.x9 = some newCursor)
    (hAInvStable : ∀ (sigmaa sigmab : MState),
      sigmaa.regs.get? Register.x3 = sigmab.regs.get? Register.x3 ->
      (∀ a : Nat, sigmaa.mem[a]? = sigmab.mem[a]?) →
      M.AInv sigmaa exts → M.AInv sigmab exts) :
    EnvDefineScanFrame M exts sp gm newIdx newCursor c' := by
  have hgpEq : c'.σ.regs.get? Register.x3 = c.σ.regs.get? Register.x3 :=
    hreg Register.x3 (by decide) (by decide) (by decide)
  refine ⟨h.stack, hgpEq.trans h.gp, ?_, ?_⟩
  · intro R hR
    by_cases h8 : R = Register.x8
    · subst R
      simpa using hx8
    · by_cases h9 : R = Register.x9
      · subst R
        simpa using hx9
      · rw [envDefineScanGhost_ne gm newIdx newCursor h8 h9,
          hreg R hR h8 h9, h.abi R hR,
          envDefineScanGhost_ne gm oldIdx oldCursor h8 h9]
  · exact hAInvStable c.σ c'.σ hgpEq.symm
      (fun a => by rw [hmem]) h.ainv

/-- Semantic scan-head carrier with the complete allocator/caller frame. -/
structure EnvDefineScanFramedSt
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (exts : List (Nat × Nat))
    (saved gm : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (phif phic : Vsa.While.Addr → Nat) (m0 : Mem) (c : Config) : Prop where
  scan : EnvDefineScanSt saved env name pv count pn sp i f nameStr N phif phic m0 c
  frame : EnvDefineScanFrame M exts sp gm (BitVec.ofNat 64 i)
    (pn + BitVec.ofNat 64 (8 * i)) c

/-- Post-`strcmp` carrier with the complete allocator/caller frame. -/
structure EnvDefineScanCmpFramedSt
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (exts : List (Nat × Nat))
    (saved gm : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (phif phic : Vsa.While.Addr → Nat) (m0 : Mem) (c : Config) : Prop where
  scan : EnvDefineScanCmpSt saved env name pv count pn sp i f nameStr N phif phic m0 c
  frame : EnvDefineScanFrame M exts sp gm (BitVec.ofNat 64 i)
    (pn + BitVec.ofNat 64 (8 * i)) c

private theorem scanFramedInitLdLine :
    mkLine 0x80002a94#64 0x00853b03#32 =
      ⟨0x80002a94#64, 0x00853b03#32, 0x03#8, 0x3b#8, 0x85#8, 0x00#8,
        .ld, 22, 10, 0, 0x008#12⟩ := by rfl

private theorem scanFramedInitZeroLine :
    mkLine 0x80002a98#64 0x00000413#32 =
      ⟨0x80002a98#64, 0x00000413#32, 0x13#8, 0x04#8, 0x00#8, 0x00#8,
        .addi, 8, 0, 0, 0x000#12⟩ := by rfl

private theorem scanFramedInitCursorLine :
    mkLine 0x80002a9c#64 0x000b0493#32 =
      ⟨0x80002a9c#64, 0x000b0493#32, 0x93#8, 0x04#8, 0x0b#8, 0x00#8,
        .addi, 9, 22, 0, 0x000#12⟩ := by rfl

private def AbiExceptS0S1S6 (R : Register) : Bool :=
  AbiPreserved R && !(R == Register.x8) && !(R == Register.x9) &&
    !(R == Register.x22)

/-- Execute the positive-count dispatch while retaining the allocator and full
callee-saved frame needed by the append/grow continuations. -/
theorem envDefineScanStartFramed
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
    (hAInvStable : ∀ (sigmaa sigmab : MState),
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
      (EnvDefineScanFramedSt M exts saved (envDefineScanBaseGhost gm pn)
        env name pv count pn sp 0
        f nameStr N phif phic m0) := by
  intro c h
  obtain ⟨hG, hloadedD, hloadedS, hmem, hpc, hx10, hx20, hx18, hx21, hx19,
    hx2, htick, hsaved, hentry⟩ := h
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
        rw [scanFramedInitLdLine]
        unfold eaddrM
        simp only [runGM, envDefineScanInitLiveL, srcVal, lookupG, reduceCtorEq,
          ↓reduceIte, Option.getD_some, BitVec.toNat_add]
        have himm : (sign_extend (m := 64) (0x008#12) : BitVec 64).toNat = 8 := by decide
        rw [himm]
        have h8 : env.toNat + 8 < 2 ^ 64 := by
          have hhi := hgeom.hi
          omega
        exact Nat.mod_eq_of_lt h8
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [hea]; exact hgeom.lo
      · rw [hea]; exact hgeom.hi
      · rw [hea]; exact hgeom.htif
      · rw [hea]; exact hgeom.align
      · rw [hmem, hea]
        exact hpins
  obtain ⟨vmi, hmi⟩ := hG.minstret
  obtain ⟨sigma', i', hsteps, htick', hG', hmem', _hout, hpc', _hmi', hregs, hraw⟩ :=
    segEval_sound envDefineScanInitSeg c.σ c.tick c.steps 0x80002a90#64 vmi
      (envDefineScanInitLiveL env count name pv sp) [bs]
      hG hpc hmi hL (by show KeysOK [10, 19, 18, 21, 2, 20]; decide) hfacts
      (by
        show ChainOK 0x80002a90#64 [10, 19, 18, 21, 2, 20] envDefineScanInitSeg
        decide) htick
  rw [hmem] at hmem'
  let c' : Config := ⟨sigma', i', c.steps + evalBlocksFuel envDefineScanInitSeg⟩
  have hpn : (BitVec.ofNat 64 pn.toNat : BitVec 64) = pn := by
    simpa using BitVec.ofNat_toNat 64 pn
  have reg (n : Nat) (v : BitVec 64)
      (hl : lookupG n (evalBlocks envDefineScanInitSeg
        (SegEvalState.init (envDefineScanInitLiveL env count name pv sp) [bs])).regs = some v) :
      gprGet c'.σ n = some v := gholds_lookup _ hregs hl
  have hmemEq : c'.σ.mem = m0 := by
    simpa [envDefineScanInitSeg, evalBlocks, SegEvalState.init, writeLog] using hmem'
  have hsaved' : EnvDefineSavedSpillFrame sp saved c' := by
    exact hsaved.of_mem_eq (hmemEq.trans hmem.symm)
  have hx9' : c'.σ.regs.get? Register.x9 = some pn := by
    simpa [hpn, gprGet] using reg 9 (BitVec.ofNat 64 pn.toNat) (by
      simp only [envDefineScanInitSeg, scanFramedInitLdLine, scanFramedInitZeroLine,
        scanFramedInitCursorLine, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,
        stepLdsM, ldsRunM, wvalM, bytesVal, envDefineScanInitLiveL, lookupG,
        eraseG, List.headD, bs]
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 by decide,
        BitVec.add_zero]
      simpa [srcVal, lookupG, eraseG] using
        (ld_value_eq_read64 m0 (env.toNat + 8) pn.toNat
          b0 b1 b2 b3 b4 b5 b6 b7 hgeom.read hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7))
  have hx8' : c'.σ.regs.get? Register.x8 = some 0#64 := by
    simpa [gprGet] using reg 8 0#64 (by rfl)
  have hscan : EnvDefineScanSt saved env name pv count pn sp 0 f nameStr
      N phif phic m0 c' := by
    refine ⟨hG', ?_, ?_, hmemEq, ?_, ?_, ?_, ?_, ?_, (by simpa using hx9'), hx8', ?_, htick',
      hframe, hnames, hcount, hpositive, hsaved'⟩
    · rw [hmemEq, ← hmem]; exact hloadedD
    · rw [hmemEq, ← hmem]; exact hloadedS
    · simpa using hpc'
    · simpa [gprGet] using reg 20 env (by rfl)
    · simpa [gprGet] using reg 18 name (by rfl)
    · simpa [gprGet] using reg 21 pv (by rfl)
    · simpa [gprGet] using reg 19 count (by rfl)
    · simpa [gprGet] using reg 2 sp (by rfl)
  have hx22' : c'.σ.regs.get? Register.x22 = some pn := by
    simpa [hpn, gprGet] using reg 22 (BitVec.ofNat 64 pn.toNat) (by
      simp only [envDefineScanInitSeg, scanFramedInitLdLine, scanFramedInitZeroLine,
        scanFramedInitCursorLine, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,
        stepLdsM, ldsRunM, wvalM, bytesVal, envDefineScanInitLiveL, lookupG,
        eraseG, List.headD, bs]
      simpa [srcVal, lookupG, eraseG] using
        (ld_value_eq_read64 m0 (env.toNat + 8) pn.toNat
          b0 b1 b2 b3 b4 b5 b6 b7 hgeom.read hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7))
  have hrawAbi : ∀ R, AbiExceptS0S1S6 R = true →
      c'.σ.regs.get? R = c.σ.regs.get? R := by
    apply frame_of_wrChain_avoids
      (P := AbiExceptS0S1S6) (bs := envDefineScanInitSeg)
      (by show ∀ rr ∈ noiseRegs, AbiExceptS0S1S6 rr = false; decide)
      (by show WrChainAvoids AbiExceptS0S1S6 envDefineScanInitSeg; decide)
      hraw
  have hgp : c'.σ.regs.get? Register.x3 = some gpv :=
    (hrawAbi Register.x3 (by decide)).trans hentry.gp
  have hframe' : EnvDefineScanFrame M exts sp (envDefineScanBaseGhost gm pn)
      0#64 pn c' := by
    refine ⟨hentry.stack, ?_, ?_, ?_⟩
    · exact hgp
    · intro R hR
      by_cases h8 : R = Register.x8
      · subst R
        simpa using hx8'
      · by_cases h9 : R = Register.x9
        · subst R
          simpa using hx9'
        · rw [envDefineScanGhost_ne (envDefineScanBaseGhost gm pn) 0#64 pn h8 h9]
          by_cases h22 : R = Register.x22
          · subst R
            simpa using hx22'
          · rw [envDefineScanBaseGhost_ne gm pn h22]
            have hExcept : AbiExceptS0S1S6 R = true := by
              simp [AbiExceptS0S1S6, hR, h8, h9, h22]
            exact (hrawAbi R hExcept).trans (hentry.abi R hR)
    · apply hAInvStable c.σ c'.σ
      · exact hentry.gp.trans hgp.symm
      · intro a
        rw [hmemEq, hmem]
      · exact hentry.ainv
  exact ⟨c', hsteps, hscan, by simpa using hframe'⟩

#print axioms envDefineScanStartFramed

/-- One exact scan argument-load/JAL/`strcmp` composition with the complete
allocator/caller frame retained. -/
theorem envDefineScanCompareFramed
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (exts : List (Nat × Nat))
    (saved gm : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (phif phic : Vsa.While.Addr → Nat) (m0 : Mem)
    (hAInvStable : ∀ (sigmaa sigmab : MState),
      sigmaa.regs.get? Register.x3 = sigmab.regs.get? Register.x3 →
      (∀ a : Nat, sigmaa.mem[a]? = sigmab.mem[a]?) →
      M.AInv sigmaa exts → M.AInv sigmab exts) :
    Triple
      (EnvDefineScanFramedSt M exts saved gm env name pv count pn sp i
        f nameStr N phif phic m0)
      (EnvDefineScanCmpFramedSt M exts saved gm env name pv count pn sp i
        f nameStr N phif phic m0) := by
  intro c h
  let hs := h.scan
  obtain ⟨q, hq, hqstr⟩ := hs.names.bindPtr i hs.index
  have hcursorNat : (pn + BitVec.ofNat 64 (8 * i)).toNat = pn.toNat + 8 * i := by
    apply ptrN
    have hhi := hs.names.slotHi i hs.index
    omega
  obtain ⟨c1, hsteps1, hG1, htick1, hmem1, hpc1, hra1, ha01, ha11, hmi1, habi1⟩ :=
    envDefineScanCallRead64 (pn + BitVec.ofNat 64 (8 * i)) name q c hs.good hs.pc
      hs.cursor hs.nameReg (by rw [hs.mem, hcursorNat]; exact hq)
      (by rw [hcursorNat]; exact hs.names.slotLo i hs.index)
      (by rw [hcursorNat]; exact hs.names.slotHi i hs.index)
      (by rw [hcursorNat]; exact hs.names.slotHtif i hs.index)
      (by rw [hcursorNat]; exact hs.names.slotAlign i hs.index)
      hs.loadedD hs.tick
  have hqLt : q < 2^64 := read64_lt_eg4 m0 (pn.toNat + 8 * i) q hq
  have hqNat : (BitVec.ofNat 64 q).toNat = q := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqLt]
  let g1 : (R : Register) → Option (RegisterType R) := fun R => c1.σ.regs.get? R
  have hpre : strcmp_full_pre g1 (BitVec.ofNat 64 q) name 0x80002abc#64
      (f.vars[i]'hs.index).1 nameStr m0 c1.σ.sailOutput c1 := by
    refine ⟨hG1, ?_, ?_, rfl, hpc1, ha01, ha11, hra1, hmi1, htick1,
      (by decide), ?_, hs.names.nameCStr, hs.names.maskPinned, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hmem1]
      exact hs.loadedS
    · exact hmem1.trans hs.mem
    · rw [hqNat]
      exact hqstr
    · rw [hqNat]
      exact fun cs hcs => hs.names.bindRegB i hs.index q hq cs hcs
    · exact hs.names.nameRegB
    · rw [hqNat]
      exact fun cs hcs => hs.names.bindRegW i hs.index q hq cs hcs
    · exact hs.names.nameRegW
    · intro R _
      rfl
  obtain ⟨c2, hsteps2, hp⟩ := strcmp_full_spec g1 (BitVec.ofNat 64 q) name
    0x80002abc#64 (f.vars[i]'hs.index).1 nameStr m0 c1.σ.sailOutput c1 hpre
  obtain ⟨hG2, hpc2, _hra2, hmem2, _hout2, htick2, hframe2,
    csa, csb, x, hcsa, hcsb, hsa, hsb, hx, hsign⟩ := hp
  have preserve (R : Register) (hR : AbiPreserved R = true) :
      c2.σ.regs.get? R = c.σ.regs.get? R := by
    rw [hframe2 R (notWrittenStrcmp_of_abiPreserved R hR)]
    exact habi1 R hR
  have hsaved2 : EnvDefineSavedSpillFrame sp saved c2 := by
    apply hs.savedSpills.of_mem_eq
    exact hmem2.trans hs.mem.symm
  have hbase : EnvDefineScanCmpSt saved env name pv count pn sp i f nameStr
      N phif phic m0 c2 := by
    refine ⟨hG2, ?_, ?_, hmem2, hpc2,
      (preserve Register.x20 (by decide)).trans hs.envReg,
      (preserve Register.x18 (by decide)).trans hs.nameReg,
      (preserve Register.x21 (by decide)).trans hs.value,
      (preserve Register.x19 (by decide)).trans hs.countReg,
      (preserve Register.x9 (by decide)).trans hs.cursor,
      (preserve Register.x8 (by decide)).trans hs.idx,
      (preserve Register.x2 (by decide)).trans hs.spReg, hs.index, ?_, htick2,
      hs.frame, hs.names, hs.countEq, hsaved2⟩
    · rw [hmem2]
      exact hs.mem ▸ hs.loadedD
    · rw [hmem2]
      exact hs.mem ▸ hs.loadedS
    · refine ⟨x, csa, csb, hx, hsa.symm, hsb.symm, hsign, ?_⟩
      exact string_eq_iff_strcmpSpecSign_zero m0 q name.toNat
        (f.vars[i]'hs.index).1 nameStr csa csb
        (by simpa [hqNat] using hcsa) hcsb hsa hsb
  have hframe : EnvDefineScanFrame M exts sp gm (BitVec.ofNat 64 i)
      (pn + BitVec.ofNat 64 (8 * i)) c2 := by
    apply h.frame.reseat (hmem2.trans hs.mem.symm)
      (fun R hR _ _ => preserve R hR)
      ((preserve Register.x8 (by decide)).trans hs.idx)
      ((preserve Register.x9 (by decide)).trans hs.cursor)
      hAInvStable
  exact ⟨c2, hsteps1.trans hsteps2, hbase, hframe⟩

#print axioms envDefineScanCompareFramed

/-- Generic exact branch-row frame transport.  The three scan result rows
instantiate it with kernel-checked concrete control-flow and write sets. -/
theorem envDefineScanLiveRowFramed
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (exts : List (Nat × Nat))
    (gm : (R : Register) → Option (RegisterType R))
    (bs : List BBlock) (target cmp idx cursor count env name pv sp : BitVec 64)
    (newIdx newCursor : BitVec 64) (m0 : Mem)
    (hwf : ChainOK 0x80002abc#64
      (keysG (envDefineScanLiveL cmp idx cursor count env name pv sp)) bs)
    (hpcEval : evalBlocksPC 0x80002abc#64
      (SegEvalState.init
        (envDefineScanLiveL cmp idx cursor count env name pv sp) []) bs = target)
    (hmemEval : writeLog m0 (evalBlocks bs (SegEvalState.init
      (envDefineScanLiveL cmp idx cursor count env name pv sp) [])).log = m0)
    (hx8Eval : lookupG 8 (evalBlocks bs (SegEvalState.init
      (envDefineScanLiveL cmp idx cursor count env name pv sp) [])).regs = some newIdx)
    (hx9Eval : lookupG 9 (evalBlocks bs (SegEvalState.init
      (envDefineScanLiveL cmp idx cursor count env name pv sp) [])).regs = some newCursor)
    (hpres : ∀ R, AbiPreserved R = true → R ≠ Register.x8 → R ≠ Register.x9 →
      (∀ rr ∈ noiseRegs, (rr == R) = false) ∧
      (∀ n ∈ wrChain bs, (gprReg n == R) = false))
    (hAInvStable : ∀ (sigmaa sigmab : MState),
      sigmaa.regs.get? Register.x3 = sigmab.regs.get? Register.x3 →
      (∀ a : Nat, sigmaa.mem[a]? = sigmab.mem[a]?) →
      M.AInv sigmaa exts → M.AInv sigmab exts) :
    Triple
      (fun c => SegPre bs
        (envDefineScanLiveL cmp idx cursor count env name pv sp) []
        0x80002abc#64 m0 c ∧
        EnvDefineScanFrame M exts sp gm idx cursor c)
      (fun c => EnvDefineScanLivePost bs target cmp idx cursor count env name pv sp [] m0 c ∧
        EnvDefineScanFrame M exts sp gm newIdx newCursor c) := by
  intro c ⟨hseg, hframe⟩
  obtain ⟨hG0, hmem0, hpc0, ⟨vm, hmi0⟩, hL0, hkeys0, hfacts0, htick0⟩ := hseg
  obtain ⟨sigma', i', hsteps, htick, hG, hmem, _hout, hpc, _hmi, hregs, hraw⟩ :=
    segEval_sound bs c.σ c.tick c.steps 0x80002abc#64 vm
      (envDefineScanLiveL cmp idx cursor count env name pv sp) []
      hG0 hpc0 hmi0 hL0 hkeys0 hfacts0 hwf htick0
  rw [hmem0] at hmem
  let c' : Config := ⟨sigma', i', c.steps + evalBlocksFuel bs⟩
  have hpost : EnvDefineScanLivePost bs target cmp idx cursor count env name pv sp [] m0 c' := by
    exact ⟨hG, hmem, by simpa [hpcEval] using hpc, hregs, htick⟩
  have hmemEq : c'.σ.mem = c.σ.mem := by
    rw [hmem, hmemEval, hmem0]
  have habiOff : ∀ R, AbiPreserved R = true → R ≠ Register.x8 → R ≠ Register.x9 →
      c'.σ.regs.get? R = c.σ.regs.get? R := by
    intro R hR h8 h9
    exact hraw R (hpres R hR h8 h9).1 (hpres R hR h8 h9).2
  have hx8 : c'.σ.regs.get? Register.x8 = some newIdx := by
    simpa [gprGet] using gholds_lookup _ hregs hx8Eval
  have hx9 : c'.σ.regs.get? Register.x9 = some newCursor := by
    simpa [gprGet] using gholds_lookup _ hregs hx9Eval
  exact ⟨c', hsteps, hpost,
    hframe.reseat hmemEq habiOff hx8 hx9 hAInvStable⟩

theorem envDefineScanHitLiveRowFramed
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List (Nat × Nat))
    (gm : (R : Register) → Option (RegisterType R))
    (cmp idx cursor count env name pv sp : BitVec 64) (m0 : Mem)
    (hAInvStable : ∀ (sigmaa sigmab : MState),
      sigmaa.regs.get? Register.x3 = sigmab.regs.get? Register.x3 →
      (∀ a : Nat, sigmaa.mem[a]? = sigmab.mem[a]?) →
      M.AInv sigmaa exts → M.AInv sigmab exts) :
    Triple
      (fun c => SegPre envDefineScanHitSeg
        (envDefineScanLiveL cmp idx cursor count env name pv sp) []
        0x80002abc#64 m0 c ∧ EnvDefineScanFrame M exts sp gm idx cursor c)
      (fun c => EnvDefineScanLivePost envDefineScanHitSeg 0x80002ac0#64
        cmp idx cursor count env name pv sp [] m0 c ∧
        EnvDefineScanFrame M exts sp gm idx cursor c) := by
  apply envDefineScanLiveRowFramed M exts gm envDefineScanHitSeg 0x80002ac0#64
    cmp idx cursor count env name pv sp idx cursor m0
  · show ChainOK 0x80002abc#64 [10, 8, 9, 19, 20, 18, 21, 2]
      envDefineScanHitSeg
    decide
  · rfl
  · rfl
  · rfl
  · rfl
  · intro R hR h8 h9
    cases R <;> simp_all [AbiPreserved, noiseRegs, envDefineScanHitSeg] <;> decide
  · exact hAInvStable

theorem envDefineScanNextLiveRowFramed
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List (Nat × Nat))
    (gm : (R : Register) → Option (RegisterType R))
    (cmp idx cursor count env name pv sp : BitVec 64) (m0 : Mem)
    (hAInvStable : ∀ (sigmaa sigmab : MState),
      sigmaa.regs.get? Register.x3 = sigmab.regs.get? Register.x3 →
      (∀ a : Nat, sigmaa.mem[a]? = sigmab.mem[a]?) →
      M.AInv sigmaa exts → M.AInv sigmab exts) :
    Triple
      (fun c => SegPre envDefineScanNextSeg
        (envDefineScanLiveL cmp idx cursor count env name pv sp) []
        0x80002abc#64 m0 c ∧ EnvDefineScanFrame M exts sp gm idx cursor c)
      (fun c => EnvDefineScanLivePost envDefineScanNextSeg 0x80002ab0#64
        cmp idx cursor count env name pv sp [] m0 c ∧
        EnvDefineScanFrame M exts sp gm (idx + 1#64) (cursor + 8#64) c) := by
  apply envDefineScanLiveRowFramed M exts gm envDefineScanNextSeg 0x80002ab0#64
    cmp idx cursor count env name pv sp (idx + 1#64) (cursor + 8#64) m0
  · show ChainOK 0x80002abc#64 [10, 8, 9, 19, 20, 18, 21, 2]
      envDefineScanNextSeg
    decide
  · rfl
  · rfl
  · rfl
  · rfl
  · intro R hR h8 h9
    cases R <;> simp_all [AbiPreserved, noiseRegs, envDefineScanNextSeg] <;> decide
  · exact hAInvStable

theorem envDefineScanDoneLiveRowFramed
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List (Nat × Nat))
    (gm : (R : Register) → Option (RegisterType R))
    (cmp idx cursor count env name pv sp : BitVec 64) (m0 : Mem)
    (hAInvStable : ∀ (sigmaa sigmab : MState),
      sigmaa.regs.get? Register.x3 = sigmab.regs.get? Register.x3 →
      (∀ a : Nat, sigmaa.mem[a]? = sigmab.mem[a]?) →
      M.AInv sigmaa exts → M.AInv sigmab exts) :
    Triple
      (fun c => SegPre envDefineScanDoneSeg
        (envDefineScanLiveL cmp idx cursor count env name pv sp) []
        0x80002abc#64 m0 c ∧ EnvDefineScanFrame M exts sp gm idx cursor c)
      (fun c => EnvDefineScanLivePost envDefineScanDoneSeg 0x80002b14#64
        cmp idx cursor count env name pv sp [] m0 c ∧
        EnvDefineScanFrame M exts sp gm (idx + 1#64) (cursor + 8#64) c) := by
  apply envDefineScanLiveRowFramed M exts gm envDefineScanDoneSeg 0x80002b14#64
    cmp idx cursor count env name pv sp (idx + 1#64) (cursor + 8#64) m0
  · show ChainOK 0x80002abc#64 [10, 8, 9, 19, 20, 18, 21, 2]
      envDefineScanDoneSeg
    decide
  · rfl
  · rfl
  · rfl
  · rfl
  · intro R hR h8 h9
    cases R <;> simp_all [AbiPreserved, noiseRegs, envDefineScanDoneSeg] <;> decide
  · exact hAInvStable

#print axioms envDefineScanHitLiveRowFramed
#print axioms envDefineScanNextLiveRowFramed
#print axioms envDefineScanDoneLiveRowFramed

/-- Exact framed branch result after `strcmp`: hit, continuing miss, or
exhausted miss. -/
def EnvDefineScanBranchFramedPost
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List (Nat × Nat))
    (saved gm : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (m0 : Mem)
    (hi : i < f.vars.length) (c : Config) : Prop :=
  ((f.vars[i]'hi).1 = nameStr ∧
    ∃ x, EnvDefineScanLivePost envDefineScanHitSeg 0x80002ac0#64
      x (BitVec.ofNat 64 i) (pn + BitVec.ofNat 64 (8 * i)) count
      env name pv sp [] m0 c ∧ EnvDefineSavedSpillFrame sp saved c ∧
      EnvDefineScanFrame M exts sp gm (BitVec.ofNat 64 i)
        (pn + BitVec.ofNat 64 (8 * i)) c) ∨
  ((f.vars[i]'hi).1 ≠ nameStr ∧
    ((i + 1 < f.vars.length ∧ ∃ x,
      EnvDefineScanLivePost envDefineScanNextSeg 0x80002ab0#64
        x (BitVec.ofNat 64 i) (pn + BitVec.ofNat 64 (8 * i)) count
        env name pv sp [] m0 c ∧ EnvDefineSavedSpillFrame sp saved c ∧
      EnvDefineScanFrame M exts sp gm (BitVec.ofNat 64 (i + 1))
        (pn + BitVec.ofNat 64 (8 * (i + 1))) c) ∨
     (i + 1 = f.vars.length ∧ ∃ x,
      EnvDefineScanLivePost envDefineScanDoneSeg 0x80002b14#64
        x (BitVec.ofNat 64 i) (pn + BitVec.ofNat 64 (8 * i)) count
        env name pv sp [] m0 c ∧ EnvDefineSavedSpillFrame sp saved c ∧
      EnvDefineScanFrame M exts sp gm (BitVec.ofNat 64 (i + 1))
        (pn + BitVec.ofNat 64 (8 * (i + 1))) c)))

private theorem scanCmp_zero_value (x : BitVec 64)
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

theorem envDefineScanBranchHitFramed
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List (Nat × Nat))
    (saved gm : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (phif phic : Vsa.While.Addr → Nat) (m0 : Mem) (hi : i < f.vars.length)
    (hAInvStable : ∀ (sigmaa sigmab : MState),
      sigmaa.regs.get? Register.x3 = sigmab.regs.get? Register.x3 →
      (∀ a : Nat, sigmaa.mem[a]? = sigmab.mem[a]?) →
      M.AInv sigmaa exts → M.AInv sigmab exts) :
    Triple
      (fun c => EnvDefineScanCmpFramedSt M exts saved gm env name pv count pn sp i
        f nameStr N phif phic m0 c ∧ (f.vars[i]'hi).1 = nameStr)
      (EnvDefineScanBranchFramedPost M exts saved gm env name pv count pn sp i
        f nameStr m0 hi) := by
  intro c ⟨h, hnameEq⟩
  let hs := h.scan
  obtain ⟨x, csa, csb, hx, _hsa, _hsb, hsign, hzero⟩ := hs.xres
  have hx0 : x = 0#64 := scanCmp_zero_value x
    (hsign.trans (hzero.mpr hnameEq))
  have hL : GHolds c.σ (envDefineScanLiveL x (BitVec.ofNat 64 i)
      (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp) := by
    exact ⟨by simpa [gprGet] using hx, by simpa [gprGet] using hs.idx,
      by simpa [gprGet] using hs.cursor, by simpa [gprGet] using hs.countReg,
      by simpa [gprGet] using hs.envReg, by simpa [gprGet] using hs.nameReg,
      by simpa [gprGet] using hs.value, by simpa [gprGet] using hs.spReg, trivial⟩
  have hfacts : ChainFacts c.σ.mem c.σ.mem
      (envDefineScanLiveL x (BitVec.ofNat 64 i)
        (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp) []
      envDefineScanHitSeg := by
    chain_facts hs.loadedD with "Vsa.Sim.Code.env_define_at_"
    simp [guardB, envDefineScanLiveL, hx0, srcVal, runGM, lookupG]
  obtain ⟨vmi, hmi⟩ := hs.good.minstret
  have hpre : SegPre envDefineScanHitSeg
      (envDefineScanLiveL x (BitVec.ofNat 64 i)
        (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp) []
      0x80002abc#64 m0 c :=
    ⟨hs.good, hs.mem, hs.pc, ⟨vmi, hmi⟩, hL,
      (by show KeysOK [10, 8, 9, 19, 20, 18, 21, 2]; decide), hfacts, hs.tick⟩
  obtain ⟨c', hsteps, hp, hframe⟩ := envDefineScanHitLiveRowFramed M exts gm x
    (BitVec.ofNat 64 i) (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp m0
    hAInvStable c ⟨hpre, h.frame⟩
  have hsaved : EnvDefineSavedSpillFrame sp saved c' := by
    apply hs.savedSpills.of_mem_eq
    exact hp.2.1.trans hs.mem.symm
  exact ⟨c', hsteps, Or.inl ⟨hnameEq, x, hp, hsaved, hframe⟩⟩

theorem envDefineScanBranchMissFramed
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List (Nat × Nat))
    (saved gm : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (phif phic : Vsa.While.Addr → Nat) (m0 : Mem) (hi : i < f.vars.length)
    (hAInvStable : ∀ (sigmaa sigmab : MState),
      sigmaa.regs.get? Register.x3 = sigmab.regs.get? Register.x3 →
      (∀ a : Nat, sigmaa.mem[a]? = sigmab.mem[a]?) →
      M.AInv sigmaa exts → M.AInv sigmab exts) :
    Triple
      (fun c => EnvDefineScanCmpFramedSt M exts saved gm env name pv count pn sp i
        f nameStr N phif phic m0 c ∧ (f.vars[i]'hi).1 ≠ nameStr)
      (EnvDefineScanBranchFramedPost M exts saved gm env name pv count pn sp i
        f nameStr m0 hi) := by
  intro c ⟨h, hnameNe⟩
  let hs := h.scan
  obtain ⟨x, csa, csb, hx, _hsa, _hsb, hsign, hzero⟩ := hs.xres
  have hxNe : x ≠ 0#64 := x10_ne_zero_of_specSign_ne x csa csb hsign
    (fun hz => hnameNe (hzero.mp hz))
  have hL : GHolds c.σ (envDefineScanLiveL x (BitVec.ofNat 64 i)
      (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp) := by
    exact ⟨by simpa [gprGet] using hx, by simpa [gprGet] using hs.idx,
      by simpa [gprGet] using hs.cursor, by simpa [gprGet] using hs.countReg,
      by simpa [gprGet] using hs.envReg, by simpa [gprGet] using hs.nameReg,
      by simpa [gprGet] using hs.value, by simpa [gprGet] using hs.spReg, trivial⟩
  obtain ⟨vmi, hmi⟩ := hs.good.minstret
  have hcount : count = BitVec.ofNat 64 f.vars.length := by
    apply BitVec.eq_of_toNat_eq
    rw [hs.countEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    rw [← hs.countEq]
    exact count.isLt
  by_cases hn : i + 1 < f.vars.length
  · have hlenLt : f.vars.length < 2^64 := by rw [← hs.countEq]; exact count.isLt
    have hiLt : i + 1 < 2^64 := Nat.lt_trans hn hlenLt
    have hcursorLt : 8 * (i + 1) < 2^64 := by
      have := hs.names.slotHi (i + 1) hn
      omega
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
      chain_facts hs.loadedD with "Vsa.Sim.Code.env_define_at_"
      simp [guardB, envDefineScanLiveL, hxNe, srcVal, runGM, lookupG]
      change guardB bop.BEQ count (BitVec.ofNat 64 i + 1#64) = false
      rw [ofNat_succ_bv i hiLt]
      simp [guardB, hcountNe]
    have hpre : SegPre envDefineScanNextSeg
        (envDefineScanLiveL x (BitVec.ofNat 64 i)
          (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp) []
        0x80002abc#64 m0 c :=
      ⟨hs.good, hs.mem, hs.pc, ⟨vmi, hmi⟩, hL,
        (by show KeysOK [10, 8, 9, 19, 20, 18, 21, 2]; decide), hfacts, hs.tick⟩
    obtain ⟨c', hsteps, hp, hframe⟩ := envDefineScanNextLiveRowFramed M exts gm x
      (BitVec.ofNat 64 i) (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp m0
      hAInvStable c ⟨hpre, h.frame⟩
    have hsaved : EnvDefineSavedSpillFrame sp saved c' := by
      apply hs.savedSpills.of_mem_eq
      exact hp.2.1.trans hs.mem.symm
    have hframe' : EnvDefineScanFrame M exts sp gm (BitVec.ofNat 64 (i + 1))
        (pn + BitVec.ofNat 64 (8 * (i + 1))) c' := by
      simpa [ofNat_succ_bv i hiLt, cursor_succ_bv pn i hcursorLt] using hframe
    exact ⟨c', hsteps, Or.inr ⟨hnameNe, Or.inl ⟨hn, x, hp, hsaved, hframe'⟩⟩⟩
  · have heq : i + 1 = f.vars.length := by omega
    have hiLt : i + 1 < 2^64 := by rw [heq, ← hs.countEq]; exact count.isLt
    have hcursorLt : 8 * (i + 1) < 2^64 := by
      have := hs.names.slotHi i hi
      omega
    have hcountSucc : count = BitVec.ofNat 64 (i + 1) := by simpa [heq] using hcount
    have hfacts : ChainFacts c.σ.mem c.σ.mem
        (envDefineScanLiveL x (BitVec.ofNat 64 i)
          (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp) []
        envDefineScanDoneSeg := by
      chain_facts hs.loadedD with "Vsa.Sim.Code.env_define_at_"
      simp [guardB, envDefineScanLiveL, hxNe, srcVal, runGM, lookupG]
      change guardB bop.BEQ count (BitVec.ofNat 64 i + 1#64) = true
      rw [ofNat_succ_bv i hiLt]
      simp [guardB, hcountSucc]
    have hpre : SegPre envDefineScanDoneSeg
        (envDefineScanLiveL x (BitVec.ofNat 64 i)
          (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp) []
        0x80002abc#64 m0 c :=
      ⟨hs.good, hs.mem, hs.pc, ⟨vmi, hmi⟩, hL,
        (by show KeysOK [10, 8, 9, 19, 20, 18, 21, 2]; decide), hfacts, hs.tick⟩
    obtain ⟨c', hsteps, hp, hframe⟩ := envDefineScanDoneLiveRowFramed M exts gm x
      (BitVec.ofNat 64 i) (pn + BitVec.ofNat 64 (8 * i)) count env name pv sp m0
      hAInvStable c ⟨hpre, h.frame⟩
    have hsaved : EnvDefineSavedSpillFrame sp saved c' := by
      apply hs.savedSpills.of_mem_eq
      exact hp.2.1.trans hs.mem.symm
    have hframe' : EnvDefineScanFrame M exts sp gm (BitVec.ofNat 64 (i + 1))
        (pn + BitVec.ofNat 64 (8 * (i + 1))) c' := by
      simpa [ofNat_succ_bv i hiLt, cursor_succ_bv pn i hcursorLt] using hframe
    exact ⟨c', hsteps, Or.inr ⟨hnameNe, Or.inr ⟨heq, x, hp, hsaved, hframe'⟩⟩⟩

theorem envDefineScanBranchFramed
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List (Nat × Nat))
    (saved gm : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (phif phic : Vsa.While.Addr → Nat) (m0 : Mem) (hi : i < f.vars.length)
    (hAInvStable : ∀ (sigmaa sigmab : MState),
      sigmaa.regs.get? Register.x3 = sigmab.regs.get? Register.x3 →
      (∀ a : Nat, sigmaa.mem[a]? = sigmab.mem[a]?) →
      M.AInv sigmaa exts → M.AInv sigmab exts) :
    Triple
      (EnvDefineScanCmpFramedSt M exts saved gm env name pv count pn sp i
        f nameStr N phif phic m0)
      (EnvDefineScanBranchFramedPost M exts saved gm env name pv count pn sp i
        f nameStr m0 hi) := by
  intro c h
  by_cases heq : (f.vars[i]'hi).1 = nameStr
  · exact envDefineScanBranchHitFramed M exts saved gm env name pv count pn sp i
      f nameStr N phif phic m0 hi hAInvStable c ⟨h, heq⟩
  · exact envDefineScanBranchMissFramed M exts saved gm env name pv count pn sp i
      f nameStr N phif phic m0 hi hAInvStable c ⟨h, heq⟩

#print axioms envDefineScanBranchFramed

/-- First-hit or exhaustive-miss result of the finite scan, including the
complete allocator/caller frame at the concrete exit register image. -/
def EnvDefineScanFramedResult
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List (Nat × Nat))
    (saved gm : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64) (f : Vsa.While.Frame)
    (nameStr : String) (m0 : Mem) (c : Config) : Prop :=
  (∃ i, ∃ hi : i < f.vars.length,
    EnvDefineNamesMissBefore f nameStr i ∧ (f.vars[i]'hi).1 = nameStr ∧
    ∃ x, EnvDefineScanLivePost envDefineScanHitSeg 0x80002ac0#64
      x (BitVec.ofNat 64 i) (pn + BitVec.ofNat 64 (8 * i)) count
      env name pv sp [] m0 c ∧ EnvDefineSavedSpillFrame sp saved c ∧
      EnvDefineScanFrame M exts sp gm (BitVec.ofNat 64 i)
        (pn + BitVec.ofNat 64 (8 * i)) c) ∨
  ((∀ j (hj : j < f.vars.length), (f.vars[j]'hj).1 ≠ nameStr) ∧
    ∃ i, i + 1 = f.vars.length ∧ ∃ x,
      EnvDefineScanLivePost envDefineScanDoneSeg 0x80002b14#64
        x (BitVec.ofNat 64 i) (pn + BitVec.ofNat 64 (8 * i)) count
        env name pv sp [] m0 c ∧ EnvDefineSavedSpillFrame sp saved c ∧
      EnvDefineScanFrame M exts sp gm (BitVec.ofNat 64 (i + 1))
        (pn + BitVec.ofNat 64 (8 * (i + 1))) c)

/-- Total finite env-define scan with StackOK, gp, all ABI-preserved registers,
the allocator invariant, and the independent spill image carried to either
concrete exit. -/
theorem envDefineScanFiniteFramed
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List (Nat × Nat))
    (saved gm : (R : Register) → Option (RegisterType R))
    (env name pv count pn sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (phif phic : Vsa.While.Addr → Nat) (m0 : Mem) (hi : i < f.vars.length)
    (hAInvStable : ∀ (sigmaa sigmab : MState),
      sigmaa.regs.get? Register.x3 = sigmab.regs.get? Register.x3 →
      (∀ a : Nat, sigmaa.mem[a]? = sigmab.mem[a]?) →
      M.AInv sigmaa exts → M.AInv sigmab exts) :
    Triple
      (fun c => EnvDefineScanFramedSt M exts saved gm env name pv count pn sp i
        f nameStr N phif phic m0 c ∧ EnvDefineNamesMissBefore f nameStr i)
      (EnvDefineScanFramedResult M exts saved gm env name pv count pn sp
        f nameStr m0) := by
  intro c ⟨h, hmiss⟩
  obtain ⟨c', hsteps, hb⟩ :=
    (envDefineScanCompareFramed M exts saved gm env name pv count pn sp i
      f nameStr N phif phic m0 hAInvStable).seq
      (envDefineScanBranchFramed M exts saved gm env name pv count pn sp i
        f nameStr N phif phic m0 hi hAInvStable) c h
  rcases hb with hhit | ⟨hnameNe, hnext | hdone⟩
  · obtain ⟨hnameEq, x, hp, hsaved, hframe⟩ := hhit
    exact ⟨c', hsteps, Or.inl ⟨i, hi, hmiss, hnameEq, x, hp, hsaved, hframe⟩⟩
  · obtain ⟨hn, x, hp, hsaved, hframe⟩ := hnext
    let hs := h.scan
    have hloadedD : Vsa.Sim.Code.Env_defineLoaded m0 := by
      rw [← hs.mem]
      exact hs.loadedD
    have hloadedS : Vsa.Sim.Code.StrcmpLoaded m0 := by
      rw [← hs.mem]
      exact hs.loadedS
    have hheadBase := envDefineScanNextCarrier saved env name pv count pn sp x i f nameStr
      N phif phic m0 c' hn hloadedD hloadedS hs.frame hs.names hs.countEq hp hsaved
    have hhead : EnvDefineScanFramedSt M exts saved gm env name pv count pn sp (i + 1)
        f nameStr N phif phic m0 c' := ⟨hheadBase, hframe⟩
    have hmiss' : EnvDefineNamesMissBefore f nameStr (i + 1) := by
      intro j hj hjlt
      by_cases hji : j = i
      · subst j
        simpa using hnameNe
      · exact hmiss j hj (by omega)
    obtain ⟨c'', hsteps', hr⟩ :=
      envDefineScanFiniteFramed M exts saved gm env name pv count pn sp (i + 1)
        f nameStr N phif phic m0 hn hAInvStable c' ⟨hhead, hmiss'⟩
    exact ⟨c'', hsteps.trans hsteps', hr⟩
  · obtain ⟨heq, x, hp, hsaved, hframe⟩ := hdone
    have hall : ∀ j (hj : j < f.vars.length), (f.vars[j]'hj).1 ≠ nameStr := by
      intro j hj
      by_cases hji : j = i
      · subst j
        simpa using hnameNe
      · exact hmiss j hj (by omega)
    exact ⟨c', hsteps, Or.inr ⟨hall, i, heq, x, hp, hsaved, hframe⟩⟩
termination_by f.vars.length - i
decreasing_by omega

#print axioms envDefineScanFiniteFramed

end Vsa.Sim
