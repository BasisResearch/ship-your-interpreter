import Vsa.Sim.DivLoops
import Vsa.Sim.SegTrace

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps RunT)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

set_option maxRecDepth 1000000

namespace Vsa.Sim

def TripleT (τ : List (BitVec 64)) (P Q : Config → Prop) : Prop :=
  ∀ c, P c → ∃ c', RunT c τ c' ∧ Q c'

theorem TripleT.seq {τ1 τ2 : List (BitVec 64)} {P Q R : Config → Prop} (h1 : TripleT τ1 P Q)
    (h2 : TripleT τ2 Q R) : TripleT (τ1 ++ τ2) P R := by
  intro c hc
  obtain ⟨c1, r1, hq⟩ := h1 c hc
  obtain ⟨c2, r2, hr⟩ := h2 c1 hq
  exact ⟨c2, r1.trans r2, hr⟩

theorem TripleT.conseq {τ : List (BitVec 64)} {P P' Q Q' : Config → Prop} (h : TripleT τ P Q)
    (hp : ∀ c, P' c → P c) (hq : ∀ c, Q c → Q' c) : TripleT τ P' Q' := by
  intro c hc
  obtain ⟨c1, r1, h1⟩ := h c (hp c hc)
  exact ⟨c1, r1, hq c1 h1⟩

theorem TripleT.nil {P : Config → Prop} : TripleT [] P P := fun c h => ⟨c, .refl c, h⟩

theorem Ust.segT {g : (R : Register) → Option (RegisterType R)}
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
    ∃ c', RunT c (pcsC bs) c' ∧ Ust g pc' b0 b1 b2 b3 r m0 o c' := by
  obtain ⟨vm, hmi⟩ := h.minstret
  obtain ⟨c', res, hrun⟩ := segEval_selected_framedT bs _ [] pc vm (fun _ => False) mulKeep _ c h.good
    h.pc hmi h.held (by show KeysOK [10, 11, 12, 13, 1]; decide) facts hwf h.tick hfoot
    (by decide) havoid hproj
  exact ⟨c', hrun, h.of_seg res hpc⟩

theorem utrT_b0_b4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1old a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    TripleT (pcsC udivMvA1Seg) (Ust g (0x800046b0#64) a0 a1old a2 a3 r m0 o) (Ust g (0x800046b4#64) a0 a0 a2 a3 r m0 o) := by
  intro c hSt
  obtain ⟨vm, hmi⟩ := hSt.minstret
  have facts : ChainFacts c.σ.mem c.σ.mem (mulRegs a0 a1old a2 a3 r) [] udivMvA1Seg := by
    chain_facts hSt.loaded
  obtain ⟨c', res, hrun⟩ := segEval_selected_framedT udivMvA1Seg _ [] _ vm (fun _ => False) mulKeep
    (mulRegs a0 a0 a2 a3 r) c hSt.good hSt.pc hmi hSt.held
    (by show KeysOK [10, 11, 12, 13, 1]; decide) facts
    (by show ChainOK _ [10, 11, 12, 13, 1] _; decide) hSt.tick (fun _ _ => rfl) (by decide)
    (by decide) ⟨rfl, congrArg some (show a0 + sign_extend (m := 64) (0x000#12) = a0 by rw [sext_zero]; exact BitVec.add_zero a0), rfl, rfl, rfl, trivial⟩
  exact ⟨c', hrun, hSt.of_seg res rfl⟩

theorem utrT_c8_cc (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    TripleT (pcsC udivSlliA2Seg) (Ust g (0x800046c8#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046cc#64) a0 a1 (a2 <<< (1:Nat)) a3 r m0 o) :=
  fun _ hSt => hSt.segT udivSlliA2Seg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨rfl, rfl, congrArg some (shl_shamt a2), rfl, rfl, trivial⟩ rfl

theorem utrT_cc_d0 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    TripleT (pcsC udivSlliA3Seg) (Ust g (0x800046cc#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046d0#64) a0 a1 a2 (a3 <<< (1:Nat)) r m0 o) :=
  fun _ hSt => hSt.segT udivSlliA3Seg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨rfl, rfl, rfl, congrArg some (shl_shamt a3), rfl, trivial⟩ rfl

theorem utrT_d4_d8 (g : (R : Register) → Option (RegisterType R))
    (a0old a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    TripleT (pcsC udivLiSeg) (Ust g (0x800046d4#64) a0old a1 a2 a3 r m0 o) (Ust g (0x800046d8#64) (0#64) a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.segT udivLiSeg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨congrArg some (show (0#64) + sign_extend (m := 64) (0x000#12) = (0#64) by rw [sext_zero]; exact BitVec.add_zero (0#64)), rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utrT_dc_e0 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    TripleT (pcsC udivSubSeg) (Ust g (0x800046dc#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046e0#64) a0 (a1 - a2) a2 a3 r m0 o) :=
  fun _ hSt => hSt.segT udivSubSeg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utrT_e0_e4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    TripleT (pcsC udivOrSeg) (Ust g (0x800046e0#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046e4#64) (a0 ||| a3) a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.segT udivOrSeg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utrT_e4_e8 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    TripleT (pcsC udivSrliA3Seg) (Ust g (0x800046e4#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046e8#64) a0 a1 a2 (a3 >>> (1:Nat)) r m0 o) :=
  fun _ hSt => hSt.segT udivSrliA3Seg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨rfl, rfl, rfl, congrArg some (shr_shamt a3), rfl, trivial⟩ rfl

theorem utrT_e8_ec (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    TripleT (pcsC udivSrliA2Seg) (Ust g (0x800046e8#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046ec#64) a0 a1 (a2 >>> (1:Nat)) a3 r m0 o) :=
  fun _ hSt => hSt.segT udivSrliA2Seg (by chain_facts hSt.loaded) (by decide) (fun _ _ => rfl) (by decide)
    ⟨rfl, rfl, congrArg some (shr_shamt a2), rfl, rfl, trivial⟩ rfl

theorem utrT_c0_d4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zKzJ_u a2 a1 = true) :
    TripleT (pcsC udivBgeuTSeg) (Ust g (0x800046c0#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046d4#64) a0 a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.segT udivBgeuTSeg (by chain_facts hSt.loaded; exact hv) (by decide) (fun _ _ => rfl)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utrT_c0_c4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zKzJ_u a2 a1 = false) :
    TripleT (pcsC udivBgeuNSeg) (Ust g (0x800046c0#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046c4#64) a0 a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.segT udivBgeuNSeg (by chain_facts hSt.loaded; exact hv) (by decide) (fun _ _ => rfl)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utrT_c4_d4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zKzJ_s (0#64) a2 = true) :
    TripleT (pcsC udivBlezTSeg) (Ust g (0x800046c4#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046d4#64) a0 a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.segT udivBlezTSeg (by chain_facts hSt.loaded; exact hv) (by decide) (fun _ _ => rfl)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utrT_c4_c8 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zKzJ_s (0#64) a2 = false) :
    TripleT (pcsC udivBlezNSeg) (Ust g (0x800046c4#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046c8#64) a0 a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.segT udivBlezNSeg (by chain_facts hSt.loaded; exact hv) (by decide) (fun _ _ => rfl)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utrT_d0_c4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zI_u a2 a1 = true) :
    TripleT (pcsC udivBltuBackTSeg) (Ust g (0x800046d0#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046c4#64) a0 a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.segT udivBltuBackTSeg (by chain_facts hSt.loaded; exact hv) (by decide) (fun _ _ => rfl)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utrT_d0_d4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zI_u a2 a1 = false) :
    TripleT (pcsC udivBltuBackNSeg) (Ust g (0x800046d0#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046d4#64) a0 a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.segT udivBltuBackNSeg (by chain_facts hSt.loaded; exact hv) (by decide) (fun _ _ => rfl)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utrT_d8_e4 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zI_u a1 a2 = true) :
    TripleT (pcsC udivBltuSkipTSeg) (Ust g (0x800046d8#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046e4#64) a0 a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.segT udivBltuSkipTSeg (by chain_facts hSt.loaded; exact hv) (by decide) (fun _ _ => rfl)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utrT_d8_dc (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : zopz0zI_u a1 a2 = false) :
    TripleT (pcsC udivSkipSeg) (Ust g (0x800046d8#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046dc#64) a0 a1 a2 a3 r m0 o) := by
  intro c hSt
  obtain ⟨vm, hmi⟩ := hSt.minstret
  have facts : ChainFacts c.σ.mem c.σ.mem (mulRegs a0 a1 a2 a3 r) [] udivSkipSeg := by
    chain_facts hSt.loaded
    exact hv
  obtain ⟨c', res, hrun⟩ := segEval_selected_framedT udivSkipSeg _ [] _ vm (fun _ => False) mulKeep
    (mulRegs a0 a1 a2 a3 r) c hSt.good hSt.pc hmi hSt.held
    (by show KeysOK [10, 11, 12, 13, 1]; decide) facts
    (by show ChainOK _ [10, 11, 12, 13, 1] _; decide) hSt.tick (fun _ _ => rfl) (by decide)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
  exact ⟨c', hrun, hSt.of_seg res rfl⟩

theorem utrT_ec_d8 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : (a3 != (0#64)) = true) :
    TripleT (pcsC udivBnezTSeg) (Ust g (0x800046ec#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046d8#64) a0 a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.segT udivBnezTSeg (by chain_facts hSt.loaded; exact hv) (by decide) (fun _ _ => rfl)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

theorem utrT_ec_f0 (g : (R : Register) → Option (RegisterType R))
    (a0 a1 a2 a3 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hv : (a3 != (0#64)) = false) :
    TripleT (pcsC udivBnezNSeg) (Ust g (0x800046ec#64) a0 a1 a2 a3 r m0 o) (Ust g (0x800046f0#64) a0 a1 a2 a3 r m0 o) :=
  fun _ hSt => hSt.segT udivBnezNSeg (by chain_facts hSt.loaded; exact hv) (by decide) (fun _ _ => rfl)
    (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl

end Vsa.Sim
