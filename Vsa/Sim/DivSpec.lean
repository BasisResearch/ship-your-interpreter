import Vsa.Sim.Code.«__hidden___udivdi3»
import Vsa.Sim.Muldi3Spec
import Vsa.Triple

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev NotWritten (R : Register) : Prop :=
  (Register.x10 == R) = false ∧ (Register.x11 == R) = false ∧
  (Register.x12 == R) = false ∧ (Register.x13 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

abbrev Frame (g : (R : Register) → Option (RegisterType R)) (c : Config) : Prop :=
  ∀ R : Register, NotWritten R → c.σ.regs.get? R = g R

structure Ust (g : (R : Register) → Option (RegisterType R))
    (pc a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : __hidden___udivdi3Loaded c.σ.mem
  mem : c.σ.mem = m0
  sailOut : c.σ.sailOutput = o
  pc : c.σ.regs.get? Register.PC = some pc
  a0 : c.σ.regs.get? Register.x10 = some a0
  a1 : c.σ.regs.get? Register.x11 = some a1
  a2 : c.σ.regs.get? Register.x12 = some a2
  a3 : c.σ.regs.get? Register.x13 = some a3
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  hframe : ∀ R : Register, NotWritten R → c.σ.regs.get? R = g R

theorem Ust.held {g : (R : Register) → Option (RegisterType R)} {pc a0 a1 a2 a3 r : BitVec 64}
    {m0 : Std.ExtHashMap Nat (BitVec 8)} {o : Array String} {c : Config}
    (h : Ust g pc a0 a1 a2 a3 r m0 o c) : GHolds c.σ (mulRegs a0 a1 a2 a3 r) :=
  ⟨h.a0, h.a1, h.a2, h.a3, h.ra, trivial⟩

theorem Ust.of_seg {g : (R : Register) → Option (RegisterType R)}
    {pc pc' a0 a1 a2 a3 b0 b1 b2 b3 r : BitVec 64}
    {m0 : Std.ExtHashMap Nat (BitVec 8)} {o : Array String} {c c' : Config}
    {bs : List BBlock} {L : GRegs} {lds : List (List (BitVec 8))} {pc0 : BitVec 64}
    (h : Ust g pc a0 a1 a2 a3 r m0 o c)
    (res : SelectedFramedSegResult bs L lds pc0 (fun _ => False) mulKeep
      (mulRegs b0 b1 b2 b3 r) c c')
    (hpc : evalBlocksPC pc0 (SegEvalState.init L lds) bs = pc') :
    Ust g pc' b0 b1 b2 b3 r m0 o c' := by
  have hmem := res.mem_eq
  obtain ⟨h0, h1, h2, h3, hr, _⟩ := res.selected_regs
  exact ⟨res.good, hmem ▸ h.loaded, hmem.trans h.mem, res.output.trans h.sailOut,
    hpc ▸ res.pc, h0, h1, h2, h3, hr, res.minstret, res.tick,
    fun R hR => (res.reg_frame R (decide_eq_true hR)).trans (h.hframe R hR)⟩

#derive_case udivSkipSeg chain []
  terminator ⟨0x800046d8#64, 0x00c5e663#32, 0x63#8, 0xe6#8, 0xc5#8, 0x00#8,
    .br bop.BLTU false, 11, 12, 0x00c#13, 0#21, 0#12⟩
#derive_case udivMvA1Seg chain [(0x800046b0#64, 0x00050593#32)]

theorem Ust.seg {g : (R : Register) → Option (RegisterType R)}
    {pc pc' a0 a1 a2 a3 b0 b1 b2 b3 r : BitVec 64}
    {m0 : Std.ExtHashMap Nat (BitVec 8)} {o : Array String} {c : Config} (bs : List BBlock)
    (h : Ust g pc a0 a1 a2 a3 r m0 o c)
    (facts : ChainFacts c.σ.mem c.σ.mem (mulRegs a0 a1 a2 a3 r) [] bs)
    (hwf : ChainOK pc [10, 11, 12, 13, 1] bs)
    (hfoot : ∀ k : Nat, ¬ False → c.σ.mem[k]? = (writeLog c.σ.mem
      (evalBlocks bs (SegEvalState.init (mulRegs a0 a1 a2 a3 r) [])).log)[k]?)
    (havoid : WrChainAvoids mulKeep bs)
    (hproj : GProjects (evalBlocks bs (SegEvalState.init (mulRegs a0 a1 a2 a3 r) [])).regs
      (mulRegs b0 b1 b2 b3 r))
    (hpc : evalBlocksPC pc (SegEvalState.init (mulRegs a0 a1 a2 a3 r) []) bs = pc') :
    ∃ c', Steps c c' ∧ Ust g pc' b0 b1 b2 b3 r m0 o c' := by
  obtain ⟨vm, hmi⟩ := h.minstret
  obtain ⟨c', res⟩ := segEval_selected_framed bs _ [] pc vm (fun _ => False) mulKeep _ c h.good
    h.pc hmi h.held (by show KeysOK [10, 11, 12, 13, 1]; decide) facts hwf h.tick hfoot
    (by decide) havoid hproj
  exact ⟨c', res.steps, h.of_seg res hpc⟩

#derive_case udivSlliA2Seg chain [(0x800046c8#64, 0x00161613#32)]
#derive_case udivSlliA3Seg chain [(0x800046cc#64, 0x00169693#32)]
#derive_case udivLiSeg chain [(0x800046d4#64, 0x00000513#32)]
#derive_case udivSubSeg chain [(0x800046dc#64, 0x40c585b3#32)]
#derive_case udivOrSeg chain [(0x800046e0#64, 0x00d56533#32)]
#derive_case udivSrliA3Seg chain [(0x800046e4#64, 0x0016d693#32)]
#derive_case udivSrliA2Seg chain [(0x800046e8#64, 0x00165613#32)]
#derive_case udivBgeuTSeg chain []
  terminator ⟨0x800046c0#64, 0x00b67a63#32, 0x63#8, 0x7a#8, 0xb6#8, 0x00#8,
    .br bop.BGEU true, 12, 11, 0x0014#13, 0#21, 0#12⟩
#derive_case udivBgeuNSeg chain []
  terminator ⟨0x800046c0#64, 0x00b67a63#32, 0x63#8, 0x7a#8, 0xb6#8, 0x00#8,
    .br bop.BGEU false, 12, 11, 0x0014#13, 0#21, 0#12⟩
#derive_case udivBlezTSeg chain []
  terminator ⟨0x800046c4#64, 0x00c05863#32, 0x63#8, 0x58#8, 0xc0#8, 0x00#8,
    .br bop.BGE true, 0, 12, 0x0010#13, 0#21, 0#12⟩
#derive_case udivBlezNSeg chain []
  terminator ⟨0x800046c4#64, 0x00c05863#32, 0x63#8, 0x58#8, 0xc0#8, 0x00#8,
    .br bop.BGE false, 0, 12, 0x0010#13, 0#21, 0#12⟩
#derive_case udivBltuBackTSeg chain []
  terminator ⟨0x800046d0#64, 0xfeb66ae3#32, 0xe3#8, 0x6a#8, 0xb6#8, 0xfe#8,
    .br bop.BLTU true, 12, 11, 0x1ff4#13, 0#21, 0#12⟩
#derive_case udivBltuBackNSeg chain []
  terminator ⟨0x800046d0#64, 0xfeb66ae3#32, 0xe3#8, 0x6a#8, 0xb6#8, 0xfe#8,
    .br bop.BLTU false, 12, 11, 0x1ff4#13, 0#21, 0#12⟩
#derive_case udivBltuSkipTSeg chain []
  terminator ⟨0x800046d8#64, 0x00c5e663#32, 0x63#8, 0xe6#8, 0xc5#8, 0x00#8,
    .br bop.BLTU true, 11, 12, 0x00c#13, 0#21, 0#12⟩
#derive_case udivBnezTSeg chain []
  terminator ⟨0x800046ec#64, 0xfe0696e3#32, 0xe3#8, 0x96#8, 0x06#8, 0xfe#8,
    .br bop.BNE true, 13, 0, 0x1fec#13, 0#21, 0#12⟩
#derive_case udivBnezNSeg chain []
  terminator ⟨0x800046ec#64, 0xfe0696e3#32, 0xe3#8, 0x96#8, 0x06#8, 0xfe#8,
    .br bop.BNE false, 13, 0, 0x1fec#13, 0#21, 0#12⟩

theorem utr_b0_b4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1old a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust g (0x800046b0#64) a0 a1old a2 a3 r m0 o) (Ust g (0x800046b4#64) a0 a0 a2 a3 r m0 o) := by
  intro c hSt
  obtain ⟨vm, hmi⟩ := hSt.minstret
  have facts : ChainFacts c.σ.mem c.σ.mem (mulRegs a0 a1old a2 a3 r) [] udivMvA1Seg := by
    chain_facts hSt.loaded
  obtain ⟨c', res⟩ := segEval_selected_framed udivMvA1Seg _ [] _ vm (fun _ => False) mulKeep
    (mulRegs a0 a0 a2 a3 r) c hSt.good hSt.pc hmi hSt.held
    (by show KeysOK [10, 11, 12, 13, 1]; decide) facts
    (by show ChainOK _ [10, 11, 12, 13, 1] _; decide) hSt.tick (fun _ _ => rfl) (by decide)
    (by decide) ⟨rfl, congrArg some (show a0 + sign_extend (m := 64) (0x000#12) = a0 by rw [sext_zero]; exact BitVec.add_zero a0), rfl, rfl, rfl, trivial⟩
  exact ⟨c', res.steps, hSt.of_seg res rfl⟩

theorem utr_c8_cc (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust g (0x800046c8#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046cc#64) a0 a1 (a2 <<< (1:Nat)) a3 r m0 o) :=
  fun _ hSt => hSt.seg udivSlliA2Seg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨rfl, rfl, congrArg some (shl_shamt a2), rfl, rfl, trivial⟩ rfl

theorem utr_cc_d0 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust g (0x800046cc#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046d0#64) a0 a1 a2 (a3 <<< (1:Nat)) r m0 o) :=
  fun _ hSt => hSt.seg udivSlliA3Seg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨rfl, rfl, rfl, congrArg some (shl_shamt a3), rfl, trivial⟩ rfl

theorem utr_d4_d8 (g : (R : Register) → Option (RegisterType R))
    (a0old a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust g (0x800046d4#64) a0old a1 a2 a3 r m0 o) (Ust g (0x800046d8#64) (0#64) a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.seg udivLiSeg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨congrArg some (show (0#64) + sign_extend (m := 64) (0x000#12) = (0#64) by rw [sext_zero]; exact BitVec.add_zero (0#64)), rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utr_dc_e0 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust g (0x800046dc#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046e0#64) a0 (a1 - a2) a2 a3 r m0 o) :=
  fun _ hSt => hSt.seg udivSubSeg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utr_e0_e4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust g (0x800046e0#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046e4#64) (a0 ||| a3) a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.seg udivOrSeg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utr_e4_e8 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust g (0x800046e4#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046e8#64) a0 a1 a2 (a3 >>> (1:Nat)) r m0 o) :=
  fun _ hSt => hSt.seg udivSrliA3Seg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨rfl, rfl, rfl, congrArg some (shr_shamt a3), rfl, trivial⟩ rfl

theorem utr_e8_ec (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (Ust g (0x800046e8#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046ec#64) a0 a1 (a2 >>> (1:Nat)) a3 r m0 o) :=
  fun _ hSt => hSt.seg udivSrliA2Seg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨rfl, rfl, congrArg some (shr_shamt a2), rfl, rfl, trivial⟩ rfl

theorem utr_c0_d4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zKzJ_u a2 a1 = true) :
    Triple (Ust g (0x800046c0#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046d4#64) a0 a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.seg udivBgeuTSeg (by chain_facts hSt.loaded; exact hv) (by decide) (fun _ _ => rfl)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utr_c0_c4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zKzJ_u a2 a1 = false) :
    Triple (Ust g (0x800046c0#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046c4#64) a0 a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.seg udivBgeuNSeg (by chain_facts hSt.loaded; exact hv) (by decide) (fun _ _ => rfl)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utr_c4_d4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zKzJ_s (0#64) a2 = true) :
    Triple (Ust g (0x800046c4#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046d4#64) a0 a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.seg udivBlezTSeg (by chain_facts hSt.loaded; exact hv) (by decide) (fun _ _ => rfl)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utr_c4_c8 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zKzJ_s (0#64) a2 = false) :
    Triple (Ust g (0x800046c4#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046c8#64) a0 a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.seg udivBlezNSeg (by chain_facts hSt.loaded; exact hv) (by decide) (fun _ _ => rfl)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utr_d0_c4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zI_u a2 a1 = true) :
    Triple (Ust g (0x800046d0#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046c4#64) a0 a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.seg udivBltuBackTSeg (by chain_facts hSt.loaded; exact hv) (by decide) (fun _ _ => rfl)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utr_d0_d4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zI_u a2 a1 = false) :
    Triple (Ust g (0x800046d0#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046d4#64) a0 a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.seg udivBltuBackNSeg (by chain_facts hSt.loaded; exact hv) (by decide) (fun _ _ => rfl)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utr_d8_e4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zI_u a1 a2 = true) :
    Triple (Ust g (0x800046d8#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046e4#64) a0 a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.seg udivBltuSkipTSeg (by chain_facts hSt.loaded; exact hv) (by decide) (fun _ _ => rfl)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utr_d8_dc (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zI_u a1 a2 = false) :
    Triple (Ust g (0x800046d8#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046dc#64) a0 a1 a2 a3 r m0 o) := by
  intro c hSt
  obtain ⟨vm, hmi⟩ := hSt.minstret
  have facts : ChainFacts c.σ.mem c.σ.mem (mulRegs a0 a1 a2 a3 r) [] udivSkipSeg := by
    chain_facts hSt.loaded
    exact hv
  obtain ⟨c', res⟩ := segEval_selected_framed udivSkipSeg _ [] _ vm (fun _ => False) mulKeep
    (mulRegs a0 a1 a2 a3 r) c hSt.good hSt.pc hmi hSt.held
    (by show KeysOK [10, 11, 12, 13, 1]; decide) facts
    (by show ChainOK _ [10, 11, 12, 13, 1] _; decide) hSt.tick (fun _ _ => rfl) (by decide)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
  exact ⟨c', res.steps, hSt.of_seg res rfl⟩

theorem utr_ec_d8 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : (a3 != (0#64)) = true) :
    Triple (Ust g (0x800046ec#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046d8#64) a0 a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.seg udivBnezTSeg (by chain_facts hSt.loaded; exact hv) (by decide) (fun _ _ => rfl)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utr_ec_f0 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : (a3 != (0#64)) = false) :
    Triple (Ust g (0x800046ec#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046f0#64) a0 a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.seg udivBnezNSeg (by chain_facts hSt.loaded; exact hv) (by decide) (fun _ _ => rfl)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem bgeu_true (a b : BitVec 64) (h : zopz0zKzJ_u a b = true) : b.toNat ≤ a.toNat := by
  unfold zopz0zKzJ_u at h; simp only [Sail.BitVec.toNatInt] at h
  exact Int.ofNat_le.mp (of_decide_eq_true h)

theorem bltu_true (a b : BitVec 64) (h : zopz0zI_u a b = true) : a.toNat < b.toNat := by
  unfold zopz0zI_u at h; simp only [Sail.BitVec.toNatInt] at h
  exact Int.ofNat_lt.mp (of_decide_eq_true h)

theorem bltu_false (a b : BitVec 64) (h : zopz0zI_u a b = false) : b.toNat ≤ a.toNat := by
  unfold zopz0zI_u at h; simp only [Sail.BitVec.toNatInt] at h
  have h2 : ¬ (Int.ofNat a.toNat < Int.ofNat b.toNat) := of_decide_eq_false h
  rw [Int.not_lt] at h2; exact Int.ofNat_le.mp h2

theorem blez_true (a : BitVec 64) (h : zopz0zKzJ_s (0#64) a = true) : a.toInt ≤ 0 := by
  unfold zopz0zKzJ_s at h
  have := of_decide_eq_true h; simp only [BitVec.toInt_zero, ge_iff_le] at this; exact this

theorem blez_false (a : BitVec 64) (h : zopz0zKzJ_s (0#64) a = false) : 0 < a.toInt := by
  unfold zopz0zKzJ_s at h
  have h2 : ¬ (a.toInt ≤ 0) := by
    have := of_decide_eq_false h; simpa only [BitVec.toInt_zero, ge_iff_le] using this
  rw [Int.not_le] at h2; exact h2

theorem bgeu_cases (a b : BitVec 64) : zopz0zKzJ_u a b = true ∨ zopz0zKzJ_u a b = false :=
  Bool.eq_false_or_eq_true (zopz0zKzJ_u a b)

theorem bltu_cases (a b : BitVec 64) : zopz0zI_u a b = true ∨ zopz0zI_u a b = false :=
  Bool.eq_false_or_eq_true (zopz0zI_u a b)

theorem blez_cases (a : BitVec 64) : zopz0zKzJ_s (0#64) a = true ∨ zopz0zKzJ_s (0#64) a = false :=
  Bool.eq_false_or_eq_true (zopz0zKzJ_s (0#64) a)

theorem shl1_toNat (a : BitVec 64) (h : 2 * a.toNat < 2^64) :
    (a <<< (1:Nat)).toNat = a.toNat * 2 := by
  rw [BitVec.toNat_shiftLeft]; simp only [Nat.shiftLeft_eq]
  have hp : (2:Nat)^1 = 2 := by decide
  rw [hp]; omega

theorem shr1_toNat (a : BitVec 64) : (a >>> (1:Nat)).toNat = a.toNat / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toInt_nonpos_top (a : BitVec 64) (h : a.toInt ≤ 0) (hne : a ≠ 0#64) : 2^63 ≤ a.toNat := by
  have hcond := BitVec.toInt_eq_toNat_cond a
  have hlt := a.isLt
  by_cases hb : 2 * a.toNat < 2^64
  · rw [if_pos hb] at hcond
    have hpos : 0 < a.toNat := by
      rcases Nat.eq_zero_or_pos a.toNat with h0 | h0
      · exact absurd (by apply BitVec.eq_of_toNat_eq; simpa using h0) hne
      · exact h0
    omega
  · omega

theorem toInt_pos_notop (a : BitVec 64) (h : 0 < a.toInt) : 2 * a.toNat < 2^64 := by
  have hcond := BitVec.toInt_eq_toNat_cond a
  have hlt := a.isLt
  by_cases hb : 2 * a.toNat < 2^64
  · exact hb
  · rw [if_neg hb] at hcond; omega

end Vsa.Sim
