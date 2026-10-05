import Vsa.Sim.Muldi3Spec
import Vsa.Sim.DivT

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps RunT)
open Vsa.Logic
open Vsa.Sim.Code (__muldi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem addi0M (v : BitVec 64) : v + sign_extend (m := 64) (0x000#12) = v := by
  rw [sext_zero]; exact BitVec.add_zero v

theorem andi1M (v : BitVec 64) : v &&& sign_extend (m := 64) (0x001#12) = v &&& 1#64 := by
  rw [sext_one]

theorem St.segT {g : (R : Register) → Option (RegisterType R)}
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
    ∃ c', RunT c (pcsC bs) c' ∧ St g pc' b0 b1 b2 b3 r m0 o c' := by
  obtain ⟨vm, hmi⟩ := h.minstret
  obtain ⟨c', res, hrun⟩ := segEval_selected_framedT bs _ [] pc vm (fun _ => False) mulKeep _ c h.good
    h.pc hmi h.held (by show KeysOK [10, 11, 12, 13, 1]; decide) facts hwf h.tick hfoot
    (by decide) havoid hproj
  exact ⟨c', hrun, h.of_seg res hpc⟩

theorem trT_40_44 (g : (R : Register) → Option (RegisterType R))
    (x y r a2old a3old : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    TripleT (pcsC mulMvSeg) (St g (0x80004640#64) x y a2old a3old r m0 o) (St g (0x80004644#64) x y x a3old r m0 o) :=
  fun _ hSt => hSt.segT mulMvSeg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨rfl, rfl, congrArg some (addi0M x), rfl, rfl, trivial⟩ rfl

theorem trT_44_48 (g : (R : Register) → Option (RegisterType R))
    (x y r a2 a3old : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    TripleT (pcsC mulLiSeg) (St g (0x80004644#64) x y a2 a3old r m0 o) (St g (0x80004648#64) (0#64) y a2 a3old r m0 o) :=
  fun _ hSt => hSt.segT mulLiSeg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨congrArg some (addi0M 0#64), rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem trT_48_4c (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 a3old : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    TripleT (pcsC mulAndiSeg) (St g (0x80004648#64) a0 y a2 a3old r m0 o) (St g (0x8000464c#64) a0 y a2 (y &&& 1#64) r m0 o) :=
  fun _ hSt => hSt.segT mulAndiSeg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨rfl, rfl, rfl, congrArg some (andi1M y), rfl, trivial⟩ rfl

theorem trT_50_54 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 a3 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    TripleT (pcsC mulAddSeg) (St g (0x80004650#64) a0 y a2 a3 r m0 o) (St g (0x80004654#64) (a0 + a2) y a2 a3 r m0 o) :=
  fun _ hSt => hSt.segT mulAddSeg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem trT_54_58 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a1 a2 a3 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    TripleT (pcsC mulSrliSeg) (St g (0x80004654#64) a0 a1 a2 a3 r m0 o) (St g (0x80004658#64) a0 (a1 >>> (1:Nat)) a2 a3 r m0 o) :=
  fun _ hSt => hSt.segT mulSrliSeg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨rfl, congrArg some (shr_shamt a1), rfl, rfl, rfl, trivial⟩ rfl

theorem trT_58_5c (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a1 a2 a3 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    TripleT (pcsC mulShlSeg) (St g (0x80004658#64) a0 a1 a2 a3 r m0 o) (St g (0x8000465c#64) a0 a1 (a2 <<< (1:Nat)) a3 r m0 o) := by
  intro c hSt
  obtain ⟨vm, hmi⟩ := hSt.minstret
  have facts : ChainFacts c.σ.mem c.σ.mem (mulRegs a0 a1 a2 a3 r) [] mulShlSeg := by
    chain_facts hSt.loaded
  obtain ⟨c', res, hrun⟩ := segEval_selected_framedT mulShlSeg _ [] _ vm (fun _ => False) mulKeep
    (mulRegs a0 a1 (a2 <<< (1:Nat)) a3 r) c hSt.good hSt.pc hmi hSt.held (by show KeysOK [10, 11, 12, 13, 1]; decide) facts
    (by show ChainOK _ [10, 11, 12, 13, 1] _; decide) hSt.tick (fun _ _ => rfl) (by decide) (by decide)
    ⟨rfl, rfl, congrArg some (shl_shamt a2), rfl, rfl, trivial⟩
  exact ⟨c', hrun, hSt.of_seg res rfl⟩

theorem trT_4c_54 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hodd : ((y &&& 1#64) == (0#64)) = true) :
    TripleT (pcsC mulOddSkipSeg) (St g (0x8000464c#64) a0 y a2 (y &&& 1#64) r m0 o) (St g (0x80004654#64) a0 y a2 (y &&& 1#64) r m0 o) := by
  intro c hSt
  obtain ⟨vm, hmi⟩ := hSt.minstret
  have facts : ChainFacts c.σ.mem c.σ.mem (mulRegs a0 y a2 (y &&& 1#64) r) [] mulOddSkipSeg := by
    chain_facts hSt.loaded
    exact hodd
  obtain ⟨c', res, hrun⟩ := segEval_selected_framedT mulOddSkipSeg _ [] _ vm (fun _ => False) mulKeep
    (mulRegs a0 y a2 (y &&& 1#64) r) c hSt.good hSt.pc hmi hSt.held
    (by show KeysOK [10, 11, 12, 13, 1]; decide) facts
    (by show ChainOK _ [10, 11, 12, 13, 1] _; decide) hSt.tick (fun _ _ => rfl) (by decide)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
  exact ⟨c', hrun, hSt.of_seg res rfl⟩


theorem trT_4c_50 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hodd : ((y &&& 1#64) == (0#64)) = false) :
    TripleT (pcsC mulOddFallSeg) (St g (0x8000464c#64) a0 y a2 (y &&& 1#64) r m0 o) (St g (0x80004650#64) a0 y a2 (y &&& 1#64) r m0 o) :=
  fun _ hSt => hSt.segT mulOddFallSeg (by chain_facts hSt.loaded; exact hodd) (by decide)
    (fun _ _ => rfl) (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem trT_5c_48 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 a3 a1 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hne : (a1 != (0#64)) = true) :
    TripleT (pcsC mulLoopBackSeg) (St g (0x8000465c#64) a0 a1 a2 a3 r m0 o) (St g (0x80004648#64) a0 a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.segT mulLoopBackSeg (by chain_facts hSt.loaded; exact hne) (by decide)
    (fun _ _ => rfl) (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem trT_5c_60 (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a2 a3 a1 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hne : (a1 != (0#64)) = false) :
    TripleT (pcsC mulLoopExitSeg) (St g (0x8000465c#64) a0 a1 a2 a3 r m0 o) (St g (0x80004660#64) a0 a1 a2 a3 r m0 o) := by
  intro c hSt
  obtain ⟨vm, hmi⟩ := hSt.minstret
  have facts : ChainFacts c.σ.mem c.σ.mem (mulRegs a0 a1 a2 a3 r) [] mulLoopExitSeg := by
    chain_facts hSt.loaded
    exact hne
  obtain ⟨c', res, hrun⟩ := segEval_selected_framedT mulLoopExitSeg _ [] _ vm (fun _ => False) mulKeep
    (mulRegs a0 a1 a2 a3 r) c hSt.good hSt.pc hmi hSt.held
    (by show KeysOK [10, 11, 12, 13, 1]; decide) facts
    (by show ChainOK _ [10, 11, 12, 13, 1] _; decide) hSt.tick (fun _ _ => rfl) (by decide)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
  exact ⟨c', hrun, hSt.of_seg res rfl⟩


theorem trT_60_ret (g : (R : Register) → Option (RegisterType R))
    (x y r a0 a1 a2 a3 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (halign : r.toNat % 4 = 0) :
    TripleT (pcsC mulRetSeg) (St g (0x80004660#64) a0 a1 a2 a3 r m0 o)
           (fun c => GoodState c.σ ∧ c.σ.mem = m0 ∧ c.σ.sailOutput = o ∧
             c.σ.regs.get? Register.PC = some r ∧
             c.σ.regs.get? Register.x10 = some a0 ∧ c.σ.regs.get? Register.x11 = some a1 ∧
             c.σ.regs.get? Register.x12 = some a2 ∧ c.σ.regs.get? Register.x1 = some r ∧
             c.tick < 2 ∧ (∀ R : Register, NotWrittenM R → c.σ.regs.get? R = g R)) := by
  intro c hSt
  obtain ⟨c', hs, h'⟩ := hSt.segT (b0 := a0) (b1 := a1) (b2 := a2) (b3 := a3) mulRetSeg
    (by chain_facts hSt.loaded; exact ret_tgt_aligned r halign) (by decide) (fun _ _ => rfl)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl
  exact ⟨c', hs, h'.good, h'.mem, h'.sailOut, h'.pc.trans (congrArg some (ret_tgt r halign)),
    h'.a0, h'.a1, h'.a2, h'.ra, h'.tick, h'.hframe⟩

theorem iterT_48_5c (x y r a0 a1 a2 : BitVec 64) (hinv : a0 + a2 * a1 = x * y) :
    ∃ (a0' : BitVec 64) (τ : List (BitVec 64)), a0' + (a2 <<< (1:Nat)) * (a1 >>> (1:Nat)) = x * y ∧
      ∀ g a3old m0 o, TripleT τ (St g (0x80004648#64) a0 a1 a2 a3old r m0 o)
        (St g (0x8000465c#64) a0' (a1 >>> (1:Nat)) (a2 <<< (1:Nat)) (a1 &&& 1#64) r m0 o) := by
  rcases and1_cases a1 with hev | hod
  · have hbeq : ((a1 &&& 1#64) == (0#64)) = true := by rw [hev]; rfl
    exact ⟨a0, _, by rw [inv_even a0 a1 a2 hev]; exact hinv, fun g a3old m0 o =>
      (((trT_48_4c g x a1 r a0 a2 a3old m0 o).seq (trT_4c_54 g x a1 r a0 a2 m0 o hbeq)).seq
        (trT_54_58 g x y r a0 a1 a2 (a1 &&& 1#64) m0 o)).seq
        (trT_58_5c g x y r a0 (a1 >>> (1:Nat)) a2 (a1 &&& 1#64) m0 o)⟩
  · have hbne : ((a1 &&& 1#64) == (0#64)) = false := by rw [hod]; rfl
    exact ⟨a0 + a2, _, by rw [inv_odd a0 a1 a2 hod]; exact hinv, fun g a3old m0 o =>
      ((((trT_48_4c g x a1 r a0 a2 a3old m0 o).seq (trT_4c_50 g x a1 r a0 a2 m0 o hbne)).seq
        (trT_50_54 g x a1 r a0 a2 (a1 &&& 1#64) m0 o)).seq
        (trT_54_58 g x a1 r (a0 + a2) a1 a2 (a1 &&& 1#64) m0 o)).seq
        (trT_58_5c g x a1 r (a0 + a2) (a1 >>> (1:Nat)) a2 (a1 &&& 1#64) m0 o)⟩

theorem mul_loopT (x y r : BitVec 64) : ∀ (M : Nat) (a0 a1 a2 : BitVec 64), a1.toNat ≤ M →
    a0 + a2 * a1 = x * y →
    ∃ (b1 b2 b3 : BitVec 64) (τ : List (BitVec 64)), ∀ g a3 m0 o,
      TripleT τ (St g (0x80004648#64) a0 a1 a2 a3 r m0 o) (St g (0x80004660#64) (x * y) b1 b2 b3 r m0 o) := by
  intro M
  induction M with
  | zero =>
    intro a0 a1 a2 hM hinv
    obtain ⟨a0', τ, hinv', hT⟩ := iterT_48_5c x y r a0 a1 a2 hinv
    have ha1 : a1 = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
    have hnew : (a1 >>> (1:Nat)) = 0#64 := by rw [ha1]; rfl
    have hbne : ((a1 >>> (1:Nat)) != (0#64)) = false := by rw [hnew]; rfl
    have ha0' : a0' = x * y := by
      have := hinv'; rw [hnew, BitVec.mul_zero, BitVec.add_zero] at this; exact this
    subst ha0'
    exact ⟨_, _, _, _, fun g a3 m0 o => (hT g a3 m0 o).seq
      (trT_5c_60 g x y r (x * y) (a2 <<< (1:Nat)) (a1 &&& 1#64) (a1 >>> (1:Nat)) m0 o hbne)⟩
  | succ M ih =>
    intro a0 a1 a2 hM hinv
    obtain ⟨a0', τ, hinv', hT⟩ := iterT_48_5c x y r a0 a1 a2 hinv
    by_cases hnew : (a1 >>> (1:Nat)) = 0#64
    · have hbne : ((a1 >>> (1:Nat)) != (0#64)) = false := by rw [hnew]; rfl
      have ha0' : a0' = x * y := by
        have := hinv'; rw [hnew, BitVec.mul_zero, BitVec.add_zero] at this; exact this
      subst ha0'
      exact ⟨_, _, _, _, fun g a3 m0 o => (hT g a3 m0 o).seq
        (trT_5c_60 g x y r (x * y) (a2 <<< (1:Nat)) (a1 &&& 1#64) (a1 >>> (1:Nat)) m0 o hbne)⟩
    · have hbne : ((a1 >>> (1:Nat)) != (0#64)) = true := by rw [bne_iff_ne]; exact hnew
      have hlt : (a1 >>> (1:Nat)).toNat ≤ M := by
        rw [shr1_toNat]; omega
      obtain ⟨b1, b2, b3, τ', hT'⟩ := ih a0' (a1 >>> (1:Nat)) (a2 <<< (1:Nat)) hlt hinv'
      exact ⟨b1, b2, b3, _, fun g a3 m0 o => ((hT g a3 m0 o).seq
        (trT_5c_48 g x y r a0' (a2 <<< (1:Nat)) (a1 &&& 1#64) (a1 >>> (1:Nat)) m0 o hbne)).seq
        (hT' g (a1 &&& 1#64) m0 o)⟩

theorem muldi3_specT (x y r : BitVec 64) (halign : r.toNat % 4 = 0) :
    ∃ τ : List (BitVec 64), ∀ g m0 o, TripleT τ (muldi3_pre g x y r m0 o) (muldi3_post g x y r m0 o) := by
  obtain ⟨b1, b2, b3, τl, hL⟩ := mul_loopT x y r _ (0#64) y x (Nat.le_refl _) (by rw [BitVec.zero_add])
  refine ⟨pcsC mulMvSeg ++ pcsC mulLiSeg ++ τl ++ pcsC mulRetSeg, fun g m0 o c hc => ?_⟩
  obtain ⟨⟨a2old, a3old, hEntry⟩, -⟩ := hc
  obtain ⟨c1, hs1, hSt1⟩ := trT_40_44 g x y r a2old a3old m0 o c hEntry
  obtain ⟨c2, hs2, hSt2⟩ := trT_44_48 g x y r x a3old m0 o c1 hSt1
  obtain ⟨c3, hs3, hSt3⟩ := hL g a3old m0 o c2 hSt2
  obtain ⟨c4, hs4, hG, hmem, hout, hpc, ha0, _, _, hra, htick, hframe⟩ :=
    trT_60_ret g x y r (x * y) b1 b2 b3 m0 o halign c3 hSt3
  exact ⟨c4, ((hs1.trans hs2).trans hs3).trans hs4, hG, hmem, hout, hpc, ha0, hra, htick, hframe⟩

end Vsa.Sim
