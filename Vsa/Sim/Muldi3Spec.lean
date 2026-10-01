import Vsa.Sim.Code.«__muldi3»
import Vsa.Sim.ObsBasics
import Vsa.Triple
import Vsa.Sim.SegEffect

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__muldi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim


abbrev NotWrittenM (R : Register) : Prop :=
  (Register.x10 == R) = false ∧ (Register.x11 == R) = false ∧
  (Register.x12 == R) = false ∧ (Register.x13 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

structure St (g : (R : Register) → Option (RegisterType R))
    (pc a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (c : Config) : Prop where
  good : GoodState c.σ
  loaded : __muldi3Loaded c.σ.mem
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
  hframe : ∀ R : Register, NotWrittenM R → c.σ.regs.get? R = g R

theorem SelectedFramedSegResult.mem_eq {bs : List BBlock} {L : GRegs}
    {lds : List (List (BitVec 8))} {pc0 : BitVec 64} {keep : Register → Bool} {sel : GRegs}
    {c c' : Config} (res : SelectedFramedSegResult bs L lds pc0 (fun _ => False) keep sel c c') :
    c'.σ.mem = c.σ.mem :=
  Std.ExtHashMap.ext_getElem? fun k => (res.outside k id).symm

def mulRegs (a0 a1 a2 a3 r : BitVec 64) : GRegs :=
  [(10, a0), (11, a1), (12, a2), (13, a3), (1, r)]

def mulKeep (R : Register) : Bool := decide (NotWrittenM R)

theorem St.held {g : (R : Register) → Option (RegisterType R)} {pc a0 a1 a2 a3 r : BitVec 64}
    {m0 : Std.ExtHashMap Nat (BitVec 8)} {o : Array String} {c : Config}
    (h : St g pc a0 a1 a2 a3 r m0 o c) : GHolds c.σ (mulRegs a0 a1 a2 a3 r) :=
  ⟨h.a0, h.a1, h.a2, h.a3, h.ra, trivial⟩

theorem St.of_seg {g : (R : Register) → Option (RegisterType R)}
    {pc pc' a0 a1 a2 a3 b0 b1 b2 b3 r : BitVec 64}
    {m0 : Std.ExtHashMap Nat (BitVec 8)} {o : Array String} {c c' : Config}
    {bs : List BBlock} {L : GRegs} {lds : List (List (BitVec 8))} {pc0 : BitVec 64}
    (h : St g pc a0 a1 a2 a3 r m0 o c)
    (res : SelectedFramedSegResult bs L lds pc0 (fun _ => False) mulKeep
      (mulRegs b0 b1 b2 b3 r) c c')
    (hpc : evalBlocksPC pc0 (SegEvalState.init L lds) bs = pc') :
    St g pc' b0 b1 b2 b3 r m0 o c' := by
  have hmem := res.mem_eq
  obtain ⟨h0, h1, h2, h3, hr, _⟩ := res.selected_regs
  exact ⟨res.good, hmem ▸ h.loaded, hmem.trans h.mem, res.output.trans h.sailOut,
    hpc ▸ res.pc, h0, h1, h2, h3, hr, res.minstret, res.tick,
    fun R hR => (res.reg_frame R (decide_eq_true hR)).trans (h.hframe R hR)⟩

#derive_case mulShlSeg chain [(0x80004658#64, 0x00161613#32)]

#derive_case mulLoopExitSeg chain []
  terminator ⟨0x8000465c#64, 0xfe0596e3#32, 0xe3#8, 0x96#8, 0x05#8, 0xfe#8,
    .br bop.BNE false, 11, 0, 0x1fec#13, 0#21, 0#12⟩



theorem St.seg {g : (R : Register) → Option (RegisterType R)}
    {pc pc' a0 a1 a2 a3 b0 b1 b2 b3 r : BitVec 64}
    {m0 : Std.ExtHashMap Nat (BitVec 8)} {o : Array String} {c : Config} (bs : List BBlock)
    (h : St g pc a0 a1 a2 a3 r m0 o c)
    (facts : ChainFacts c.σ.mem c.σ.mem (mulRegs a0 a1 a2 a3 r) [] bs)
    (hwf : ChainOK pc [10, 11, 12, 13, 1] bs)
    (hfoot : ∀ k : Nat, ¬ False → c.σ.mem[k]? = (writeLog c.σ.mem
      (evalBlocks bs (SegEvalState.init (mulRegs a0 a1 a2 a3 r) [])).log)[k]?)
    (havoid : WrChainAvoids mulKeep bs)
    (hproj : GProjects (evalBlocks bs (SegEvalState.init (mulRegs a0 a1 a2 a3 r) [])).regs
      (mulRegs b0 b1 b2 b3 r))
    (hpc : evalBlocksPC pc (SegEvalState.init (mulRegs a0 a1 a2 a3 r) []) bs = pc') :
    ∃ c', Steps c c' ∧ St g pc' b0 b1 b2 b3 r m0 o c' := by
  obtain ⟨vm, hmi⟩ := h.minstret
  obtain ⟨c', res⟩ := segEval_selected_framed bs _ [] pc vm (fun _ => False) mulKeep _ c h.good
    h.pc hmi h.held (by show KeysOK [10, 11, 12, 13, 1]; decide) facts hwf h.tick hfoot
    (by decide) havoid hproj
  exact ⟨c', res.steps, h.of_seg res hpc⟩

#derive_case mulMvSeg chain [(0x80004640#64, 0x00050613#32)]
#derive_case mulLiSeg chain [(0x80004644#64, 0x00000513#32)]
#derive_case mulAndiSeg chain [(0x80004648#64, 0x0015f693#32)]
#derive_case mulAddSeg chain [(0x80004650#64, 0x00c50533#32)]
#derive_case mulSrliSeg chain [(0x80004654#64, 0x0015d593#32)]
#derive_case mulOddFallSeg chain []
  terminator ⟨0x8000464c#64, 0x00068463#32, 0x63#8, 0x84#8, 0x06#8, 0x00#8,
    .br bop.BEQ false, 13, 0, 0x0008#13, 0#21, 0#12⟩
#derive_case mulLoopBackSeg chain []
  terminator ⟨0x8000465c#64, 0xfe0596e3#32, 0xe3#8, 0x96#8, 0x05#8, 0xfe#8,
    .br bop.BNE true, 11, 0, 0x1fec#13, 0#21, 0#12⟩
#derive_case mulRetSeg chain []
  terminator ⟨0x80004660#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8,
    .jr, 1, 0, 0#13, 0#21, 0#12⟩

private theorem addi0 (v : BitVec 64) : v + sign_extend (m := 64) (0x000#12) = v := by
  rw [sext_zero]; exact BitVec.add_zero v

private theorem andi1 (v : BitVec 64) : v &&& sign_extend (m := 64) (0x001#12) = v &&& 1#64 := by
  rw [sext_one]

theorem tr_40_44 (g : (R : Register) → Option (RegisterType R))
    (x y r a2old a3old : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (St g (0x80004640#64) x y a2old a3old r m0 o) (St g (0x80004644#64) x y x a3old r m0 o) :=
  fun _ hSt => hSt.seg mulMvSeg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨rfl, rfl, congrArg some (addi0 x), rfl, rfl, trivial⟩ rfl

theorem tr_44_48 (g : (R : Register) → Option (RegisterType R))
    (x y r a2 a3old : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (St g (0x80004644#64) x y a2 a3old r m0 o) (St g (0x80004648#64) (0#64) y a2 a3old r m0 o) :=
  fun _ hSt => hSt.seg mulLiSeg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨congrArg some (addi0 0#64), rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem tr_48_4c (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 a3old : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (St g (0x80004648#64) a0 y a2 a3old r m0 o) (St g (0x8000464c#64) a0 y a2 (y &&& 1#64) r m0 o) :=
  fun _ hSt => hSt.seg mulAndiSeg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨rfl, rfl, rfl, congrArg some (andi1 y), rfl, trivial⟩ rfl

theorem tr_50_54 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 a3 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (St g (0x80004650#64) a0 y a2 a3 r m0 o) (St g (0x80004654#64) (a0 + a2) y a2 a3 r m0 o) :=
  fun _ hSt => hSt.seg mulAddSeg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem tr_54_58 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a1 a2 a3 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (St g (0x80004654#64) a0 a1 a2 a3 r m0 o) (St g (0x80004658#64) a0 (a1 >>> (1:Nat)) a2 a3 r m0 o) :=
  fun _ hSt => hSt.seg mulSrliSeg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨rfl, congrArg some (shr_shamt a1), rfl, rfl, rfl, trivial⟩ rfl

theorem tr_58_5c (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a1 a2 a3 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (St g (0x80004658#64) a0 a1 a2 a3 r m0 o) (St g (0x8000465c#64) a0 a1 (a2 <<< (1:Nat)) a3 r m0 o) := by
  intro c hSt
  obtain ⟨vm, hmi⟩ := hSt.minstret
  have facts : ChainFacts c.σ.mem c.σ.mem (mulRegs a0 a1 a2 a3 r) [] mulShlSeg := by
    chain_facts hSt.loaded
  obtain ⟨c', res⟩ := segEval_selected_framed mulShlSeg _ [] _ vm (fun _ => False) mulKeep
    (mulRegs a0 a1 (a2 <<< (1:Nat)) a3 r) c hSt.good hSt.pc hmi hSt.held (by show KeysOK [10, 11, 12, 13, 1]; decide) facts
    (by show ChainOK _ [10, 11, 12, 13, 1] _; decide) hSt.tick (fun _ _ => rfl) (by decide) (by decide)
    ⟨rfl, rfl, congrArg some (shl_shamt a2), rfl, rfl, trivial⟩
  exact ⟨c', res.steps, hSt.of_seg res rfl⟩

#derive_case mulOddSkipSeg chain []
  terminator ⟨0x8000464c#64, 0x00068463#32, 0x63#8, 0x84#8, 0x06#8, 0x00#8,
    .br bop.BEQ true, 13, 0, 0x0008#13, 0#21, 0#12⟩

theorem tr_4c_54 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hodd : ((y &&& 1#64) == (0#64)) = true) :
    Triple (St g (0x8000464c#64) a0 y a2 (y &&& 1#64) r m0 o) (St g (0x80004654#64) a0 y a2 (y &&& 1#64) r m0 o) := by
  intro c hSt
  obtain ⟨vm, hmi⟩ := hSt.minstret
  have facts : ChainFacts c.σ.mem c.σ.mem (mulRegs a0 y a2 (y &&& 1#64) r) [] mulOddSkipSeg := by
    chain_facts hSt.loaded
    exact hodd
  obtain ⟨c', res⟩ := segEval_selected_framed mulOddSkipSeg _ [] _ vm (fun _ => False) mulKeep
    (mulRegs a0 y a2 (y &&& 1#64) r) c hSt.good hSt.pc hmi hSt.held
    (by show KeysOK [10, 11, 12, 13, 1]; decide) facts
    (by show ChainOK _ [10, 11, 12, 13, 1] _; decide) hSt.tick (fun _ _ => rfl) (by decide)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
  exact ⟨c', res.steps, hSt.of_seg res rfl⟩


theorem tr_4c_50 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hodd : ((y &&& 1#64) == (0#64)) = false) :
    Triple (St g (0x8000464c#64) a0 y a2 (y &&& 1#64) r m0 o) (St g (0x80004650#64) a0 y a2 (y &&& 1#64) r m0 o) :=
  fun _ hSt => hSt.seg mulOddFallSeg (by chain_facts hSt.loaded; exact hodd) (by decide)
    (fun _ _ => rfl) (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem tr_5c_48 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 a3 a1 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hne : (a1 != (0#64)) = true) :
    Triple (St g (0x8000465c#64) a0 a1 a2 a3 r m0 o) (St g (0x80004648#64) a0 a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.seg mulLoopBackSeg (by chain_facts hSt.loaded; exact hne) (by decide)
    (fun _ _ => rfl) (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem tr_5c_60 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 a3 a1 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hne : (a1 != (0#64)) = false) :
    Triple (St g (0x8000465c#64) a0 a1 a2 a3 r m0 o) (St g (0x80004660#64) a0 a1 a2 a3 r m0 o) := by
  intro c hSt
  obtain ⟨vm, hmi⟩ := hSt.minstret
  have facts : ChainFacts c.σ.mem c.σ.mem (mulRegs a0 a1 a2 a3 r) [] mulLoopExitSeg := by
    chain_facts hSt.loaded
    exact hne
  obtain ⟨c', res⟩ := segEval_selected_framed mulLoopExitSeg _ [] _ vm (fun _ => False) mulKeep
    (mulRegs a0 a1 a2 a3 r) c hSt.good hSt.pc hmi hSt.held
    (by show KeysOK [10, 11, 12, 13, 1]; decide) facts
    (by show ChainOK _ [10, 11, 12, 13, 1] _; decide) hSt.tick (fun _ _ => rfl) (by decide)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
  exact ⟨c', res.steps, hSt.of_seg res rfl⟩


theorem tr_60_ret (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a1 a2 a3 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (halign : r.toNat % 4 = 0) :
    Triple (St g (0x80004660#64) a0 a1 a2 a3 r m0 o)
           (fun c => GoodState c.σ ∧ c.σ.mem = m0 ∧ c.σ.sailOutput = o ∧
             c.σ.regs.get? Register.PC = some r ∧
             c.σ.regs.get? Register.x10 = some a0 ∧ c.σ.regs.get? Register.x11 = some a1 ∧
             c.σ.regs.get? Register.x12 = some a2 ∧ c.σ.regs.get? Register.x1 = some r ∧
             c.tick < 2 ∧ (∀ R : Register, NotWrittenM R → c.σ.regs.get? R = g R)) := by
  intro c hSt
  obtain ⟨c', hs, h'⟩ := hSt.seg (b0 := a0) (b1 := a1) (b2 := a2) (b3 := a3) mulRetSeg
    (by chain_facts hSt.loaded; exact ret_tgt_aligned r halign) (by decide) (fun _ _ => rfl)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl
  exact ⟨c', hs, h'.good, h'.mem, h'.sailOut, h'.pc.trans (congrArg some (ret_tgt r halign)),
    h'.a0, h'.a1, h'.a2, h'.ra, h'.tick, h'.hframe⟩

def AtHead (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  ∃ a0 a1 a2 a3, St g (0x80004648#64) a0 a1 a2 a3 r m0 o c ∧ a0 + a2 * a1 = x * y

def AtDone (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  ∃ a1 a2 a3, St g (0x80004660#64) (x * y) a1 a2 a3 r m0 o c

def LoopI (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  AtHead g x y r m0 o c ∨ AtDone g x y r m0 o c

def LoopB (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  ∃ a0 a1 a2 a3, St g (0x80004648#64) a0 a1 a2 a3 r m0 o c ∧ a0 + a2 * a1 = x * y ∧ a1 ≠ 0#64

def LoopMu (c : Config) : Nat :=
  ((c.σ.regs.get? Register.x11).getD (0#64)).toNat

theorem and1_cases (a1 : BitVec 64) : a1 &&& 1#64 = 0#64 ∨ a1 &&& 1#64 = 1#64 := by
  have hval : (a1 &&& 1#64).toNat = a1.toNat % 2 := by
    rw [BitVec.toNat_and]; have h1 : (1#64).toNat = 1 := by decide
    rw [h1, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one a1.toNat with h0 | h1
  · left; apply BitVec.eq_of_toNat_eq; rw [hval, h0]; rfl
  · right; apply BitVec.eq_of_toNat_eq; rw [hval, h1]; rfl

theorem inv_even (a0 a1 a2 : BitVec 64) (hev : a1 &&& 1#64 = 0#64) :
    a0 + (a2 <<< (1:Nat)) * (a1 >>> (1:Nat)) = a0 + a2 * a1 := by
  rw [invmul_bv a2 a1, hev, BitVec.zero_mul, BitVec.add_zero]

theorem inv_odd (a0 a1 a2 : BitVec 64) (hod : a1 &&& 1#64 = 1#64) :
    (a0 + a2) + (a2 <<< (1:Nat)) * (a1 >>> (1:Nat)) = a0 + a2 * a1 := by
  rw [invmul_bv a2 a1, hod, BitVec.one_mul, BitVec.add_assoc, BitVec.add_comm a2 _,
    ← BitVec.add_assoc]

theorem iter_48_5c (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a1 a2 a3old : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hinv : a0 + a2 * a1 = x * y) :
    Triple (St g (0x80004648#64) a0 a1 a2 a3old r m0 o)
           (fun c => ∃ a0', St g (0x8000465c#64) a0' (a1 >>> (1:Nat)) (a2 <<< (1:Nat)) (a1 &&& 1#64) r m0 o c
             ∧ a0' + (a2 <<< (1:Nat)) * (a1 >>> (1:Nat)) = x * y) := by

  have h1 : Triple (St g (0x80004648#64) a0 a1 a2 a3old r m0 o)
      (St g (0x8000464c#64) a0 a1 a2 (a1 &&& 1#64) r m0 o) := tr_48_4c g x a1 r a0 a2 a3old m0 o
  rcases and1_cases a1 with hev | hod
  ·
    have hbeq : ((a1 &&& 1#64) == (0#64)) = true := by rw [hev]; rfl
    have h2 := tr_4c_54 g x a1 r a0 a2 m0 o hbeq
    have h3 := tr_54_58 g x y r a0 a1 a2 (a1 &&& 1#64) m0 o
    have h4 := tr_58_5c g x y r a0 (a1 >>> (1:Nat)) a2 (a1 &&& 1#64) m0 o
    have hchain : Triple (St g (0x80004648#64) a0 a1 a2 a3old r m0 o)
        (St g (0x8000465c#64) a0 (a1 >>> (1:Nat)) (a2 <<< (1:Nat)) (a1 &&& 1#64) r m0 o) :=
      (h1.seq h2).seq (h3.seq h4)
    exact hchain.conseq (fun _ h => h) (fun c hc =>
      ⟨a0, hc, by rw [inv_even a0 a1 a2 hev]; exact hinv⟩)
  ·
    have hbne : ((a1 &&& 1#64) == (0#64)) = false := by rw [hod]; rfl
    have h2 := tr_4c_50 g x a1 r a0 a2 m0 o hbne
    have h2' := tr_50_54 g x a1 r a0 a2 (a1 &&& 1#64) m0 o
    have h3 := tr_54_58 g x a1 r (a0 + a2) a1 a2 (a1 &&& 1#64) m0 o
    have h4 := tr_58_5c g x a1 r (a0 + a2) (a1 >>> (1:Nat)) a2 (a1 &&& 1#64) m0 o
    have hchain : Triple (St g (0x80004648#64) a0 a1 a2 a3old r m0 o)
        (St g (0x8000465c#64) (a0 + a2) (a1 >>> (1:Nat)) (a2 <<< (1:Nat)) (a1 &&& 1#64) r m0 o) :=
      ((h1.seq h2).seq h2').seq (h3.seq h4)
    exact hchain.conseq (fun _ h => h) (fun c hc =>
      ⟨a0 + a2, hc, by rw [inv_odd a0 a1 a2 hod]; exact hinv⟩)

theorem loop_body (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (n : Nat) :
    Triple (fun c => LoopI g x y r m0 o c ∧ LoopB g x y r m0 o c ∧ LoopMu c = n)
           (fun c => LoopI g x y r m0 o c ∧ LoopMu c < n) := by
  intro c hc
  obtain ⟨_, ⟨a0, a1, a2, a3, hSt, hinv, hne⟩, hmu⟩ := hc

  have hmu_eq : LoopMu c = a1.toNat := by
    simp only [LoopMu, hSt.a1, Option.getD_some]
  rw [hmu_eq] at hmu

  obtain ⟨c1, hs1, a0', h5c, hinv'⟩ := iter_48_5c g x y r a0 a1 a2 a3 m0 o hinv c hSt
  by_cases hnew : (a1 >>> (1:Nat)) = 0#64
  ·
    have hbne : ((a1 >>> (1:Nat)) != (0#64)) = false := by rw [hnew]; rfl
    obtain ⟨c2, hs2, hSt2⟩ := tr_5c_60 g x y r a0' (a2 <<< (1:Nat)) (a1 &&& 1#64) (a1 >>> (1:Nat)) m0 o hbne c1 h5c
    have ha0' : a0' = x * y := by
      have := hinv'
      rw [hnew, BitVec.mul_zero, BitVec.add_zero] at this
      exact this
    refine ⟨c2, hs1.trans hs2, Or.inr ⟨_, _, _, ha0' ▸ hSt2⟩, ?_⟩

    have hmc2 : LoopMu c2 = (a1 >>> (1:Nat)).toNat := by simp only [LoopMu, hSt2.a1, Option.getD_some]
    have hnpos : 0 < n := by
      rw [← hmu]
      have : 0 < a1.toNat := by
        rcases Nat.eq_zero_or_pos a1.toNat with h0 | h0
        · exact absurd (by apply BitVec.eq_of_toNat_eq; simpa using h0) hne
        · exact h0
      exact this
    rw [hmc2, hnew]
    show (0#64).toNat < n
    have h0 : (0#64 : BitVec 64).toNat = 0 := by decide
    rw [h0]; exact hnpos
  ·
    have hbne : ((a1 >>> (1:Nat)) != (0#64)) = true := by
      rw [bne_iff_ne]; exact hnew
    obtain ⟨c2, hs2, hSt2⟩ := tr_5c_48 g x y r a0' (a2 <<< (1:Nat)) (a1 &&& 1#64) (a1 >>> (1:Nat)) m0 o hbne c1 h5c
    refine ⟨c2, hs1.trans hs2, Or.inl ⟨a0', a1 >>> (1:Nat), a2 <<< (1:Nat), a1 &&& 1#64, hSt2, hinv'⟩, ?_⟩
    have hmu2 : LoopMu c2 = (a1 >>> (1:Nat)).toNat := by simp only [LoopMu, hSt2.a1, Option.getD_some]
    rw [hmu2, ← hmu]
    exact shr_lt a1 hne

theorem loop_to_done (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (LoopI g x y r m0 o) (AtDone g x y r m0 o) := by
  have hloop := Triple.loop (I := LoopI g x y r m0 o) (B := LoopB g x y r m0 o) LoopMu (loop_body g x y r m0 o)
  refine hloop.seq ?_
  intro c hc
  obtain ⟨hI, hnB⟩ := hc
  rcases hI with hHead | hDone
  ·
    obtain ⟨a0, a1, a2, a3, hSt, hinv⟩ := hHead
    have ha1 : a1 = 0#64 := by
      by_cases hne : a1 = 0#64
      · exact hne
      · exact absurd ⟨a0, a1, a2, a3, hSt, hinv, hne⟩ hnB

    obtain ⟨c1, hs1, a0', h5c, hinv'⟩ := iter_48_5c g x y r a0 a1 a2 a3 m0 o hinv c hSt
    have hnew : (a1 >>> (1:Nat)) = 0#64 := by rw [ha1]; rfl
    have hbne : ((a1 >>> (1:Nat)) != (0#64)) = false := by rw [hnew]; rfl
    obtain ⟨c2, hs2, hSt2⟩ := tr_5c_60 g x y r a0' (a2 <<< (1:Nat)) (a1 &&& 1#64) (a1 >>> (1:Nat)) m0 o hbne c1 h5c
    have ha0' : a0' = x * y := by
      have := hinv'; rw [hnew, BitVec.mul_zero, BitVec.add_zero] at this; exact this
    exact ⟨c2, hs1.trans hs2, _, _, _, ha0' ▸ hSt2⟩
  · exact ⟨c, .refl c, hDone⟩

def muldi3_pre (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  (∃ a2old a3old, St g (0x80004640#64) x y a2old a3old r m0 o c) ∧ r.toNat % 4 = 0

def muldi3_post (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧ c.σ.sailOutput = o ∧ c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x10 = some (x * y) ∧ c.σ.regs.get? Register.x1 = some r ∧
  c.tick < 2 ∧ (∀ R : Register, NotWrittenM R → c.σ.regs.get? R = g R)

theorem muldi3_spec (g : (R : Register) → Option (RegisterType R)) (x y r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (muldi3_pre g x y r m0 o) (muldi3_post g x y r m0 o) := by

  have hpre : Triple (muldi3_pre g x y r m0 o) (fun c => LoopI g x y r m0 o c ∧ r.toNat % 4 = 0) := by
    intro c hc
    obtain ⟨⟨a2old, a3old, hEntry⟩, halign⟩ := hc

    obtain ⟨c1, hs1, hSt1⟩ := tr_40_44 g x y r a2old a3old m0 o c hEntry

    obtain ⟨c2, hs2, hSt2⟩ := tr_44_48 g x y r x a3old m0 o c1 hSt1
    refine ⟨c2, hs1.trans hs2, Or.inl ⟨0#64, y, x, a3old, hSt2, ?_⟩, halign⟩

    rw [BitVec.zero_add]

  have hbody : Triple (fun c => LoopI g x y r m0 o c ∧ r.toNat % 4 = 0)
      (fun c => AtDone g x y r m0 o c ∧ r.toNat % 4 = 0) := by
    intro c hc
    obtain ⟨hI, halign⟩ := hc
    obtain ⟨c', hs, hDone⟩ := loop_to_done g x y r m0 o c hI
    exact ⟨c', hs, hDone, halign⟩

  have hret : Triple (fun c => AtDone g x y r m0 o c ∧ r.toNat % 4 = 0) (muldi3_post g x y r m0 o) := by
    intro c hc
    obtain ⟨⟨a1, a2, a3, hSt⟩, halign⟩ := hc
    obtain ⟨c', hs, hG, hmem, hout, hpc, ha0, ha1, ha2, hra, htick, hframe⟩ := tr_60_ret g x y r (x*y) a1 a2 a3 m0 o halign c hSt
    exact ⟨c', hs, hG, hmem, hout, hpc, ha0, hra, htick, hframe⟩
  exact (hpre.seq hbody).seq hret

end Vsa.Sim
