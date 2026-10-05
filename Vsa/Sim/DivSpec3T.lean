import Vsa.Sim.DivSpec3
import Vsa.Sim.DivLoopsT

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps RunT)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem addi0T (v : BitVec 64) : v + sign_extend (m := 64) (0x000#12) = v := by
  rw [sext_zero]; exact BitVec.add_zero v

theorem core_call_tail_fT (A B q : BitVec 64) (hBpos : 0 < B.toNat) (halign : q.toNat % 4 = 0) :
    ∃ τ : List (BitVec 64), ∀ (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (cent : Config),
    GoodState cent.σ → __hidden___udivdi3Loaded cent.σ.mem → cent.σ.mem = m0 →
    cent.σ.sailOutput = o → cent.σ.regs.get? Register.PC = some (0x800046ac#64) →
    cent.σ.regs.get? Register.x10 = some A → cent.σ.regs.get? Register.x11 = some B →
    cent.σ.regs.get? Register.x1 = some q → (∃ v, cent.σ.regs.get? Register.x12 = some v) →
    (∃ v, cent.σ.regs.get? Register.x13 = some v) →
    (∃ v, cent.σ.regs.get? Register.minstret = some v) → cent.tick < 2 →
    ∃ c3 : Config, RunT cent τ c3 ∧ GoodState c3.σ ∧ c3.σ.mem = m0 ∧
      c3.σ.sailOutput = o ∧
      c3.σ.regs.get? Register.PC = some q ∧
      c3.σ.regs.get? Register.x10 = some (A / B) ∧
      c3.σ.regs.get? Register.x11 = some (A % B) ∧
      c3.σ.regs.get? Register.x1 = some q ∧ c3.tick < 2 ∧
      (∀ R : Register, NotWritten R → c3.σ.regs.get? R = cent.σ.regs.get? R) ∧
      (∃ v, c3.σ.regs.get? Register.minstret = some v) := by
  obtain ⟨τ, hT⟩ := udivdi3_specT A B q hBpos halign
  refine ⟨τ, fun m0 o cent hG hcl hmem hout hpc hx10 hx11 hx1 hx12 hx13 hmi htick => ?_⟩
  obtain ⟨v12, h12⟩ := hx12
  obtain ⟨v13, h13⟩ := hx13
  obtain ⟨c3, hs3, hG3, hmem3, hout3, hpc3, hq3, hrem3, hra3, htick3, hframe3, _hx12_3, _hx13_3⟩ :=
    hT (fun R => cent.σ.regs.get? R) m0 o cent ⟨v12, v13,
      { good := hG, loaded := hcl, mem := hmem, sailOut := hout, pc := hpc,
        a0 := hx10, a1 := hx11, a2 := h12, a3 := h13, ra := hx1, minstret := hmi,
        tick := htick, hframe := fun R _ => rfl }⟩
  obtain ⟨vmi3, hmi3⟩ := hG3.minstret
  exact ⟨c3, hs3, hG3, hmem3, hout3, hpc3, hq3, hrem3, hra3, htick3, hframe3, ⟨vmi3, hmi3⟩⟩

theorem core_call_segT (A B link : BitVec 64) (hBpos : 0 < B.toNat) (hlink : link.toNat % 4 = 0) :
    ∃ τ : List (BitVec 64), ∀ {c : Config} {pc vm r w12 w13 : BitVec 64} {imm : BitVec 21}
      {m0 : Std.ExtHashMap Nat (BitVec 8)} {o : Array String},
    c.σ.regs.get? Register.PC = some pc →
    (∃ (σ' : MState) (i' : Nat), Step ⟨c.σ, c.tick, c.steps⟩ ⟨σ', i', c.steps + 1⟩ ∧
      i' < 2 ∧ GoodState σ' ∧ σ'.mem = c.σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jal c.σ pc vm imm Register.x1 link)) →
    pc + sign_extend (m := 64) imm = 0x800046ac#64 →
    __hidden___udivdi3Loaded c.σ.mem → c.σ.mem = m0 → c.σ.sailOutput = o →
    GHolds c.σ [(10, A), (11, B), (5, r), (12, w12), (13, w13)] →
    ∃ c3 : Config, RunT c (pc :: τ) c3 ∧ GoodState c3.σ ∧ c3.σ.mem = m0 ∧ c3.σ.sailOutput = o ∧
      c3.σ.regs.get? Register.PC = some link ∧ c3.tick < 2 ∧
      (∃ v, c3.σ.regs.get? Register.minstret = some v) ∧
      GHolds c3.σ [(10, A / B), (11, A % B), (5, r)] ∧
      ∀ R : Register, NotWrittenD R → c3.σ.regs.get? R = c.σ.regs.get? R := by
  obtain ⟨τ, hT⟩ := core_call_tail_fT A B link hBpos hlink
  refine ⟨τ, fun {c pc vm r w12 w13 imm m0 o} hpcc hsite hce hcl hmem hout hL => ?_⟩
  obtain ⟨σ2, i2, hstep, hi2, hG2, hmem2, hobs⟩ := hsite
  obtain ⟨h10, h11, h5, h12, h13, _⟩ := hL
  have keepJ : ∀ (R : Register) {w : RegisterType R}, NotWritten R → (Register.x1 == R) = false →
      c.σ.regs.get? R = some w → σ2.regs.get? R = some w :=
    fun R _ hR h1 hw => (frame_jal hobs R h1 hR).trans hw
  obtain ⟨c3, hs3, hG3, hmem3, hout3, hpc3, hq3, hrem3, _, hi3, hfr3, hmi3⟩ :=
    hT m0 o ⟨σ2, i2, c.steps + 1⟩ hG2 (hmem2 ▸ hcl) (hmem2.trans hmem)
      (hobs.2.trans hout) ((obs_jal_pc_env hobs).trans (congrArg some hce))
      (obs_jal_other_env hobs Register.x10 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) h10)
      (obs_jal_other_env hobs Register.x11 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) h11)
      (obs_jal_rd_env hobs (by decide) (by decide) (by decide) (by decide) (by decide))
      ⟨w12, obs_jal_other_env hobs Register.x12 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) h12⟩
      ⟨w13, obs_jal_other_env hobs Register.x13 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) h13⟩
      (obs_jal_minstret_env hobs) hi2
  refine ⟨c3, RunT.step hstep hpcc hs3, hG3, hmem3, hout3, hpc3, hi3, hmi3,
    ⟨hq3, hrem3, (hfr3 Register.x5 (by decide)).trans (keepJ Register.x5 (by decide) (by decide) h5),
      trivial⟩, fun R hR => (hfr3 R hR.nw).trans (frame_jal hobs R hR.2.1 hR.nw)⟩

theorem moddi3_fin_posT (n d A B r : BitVec 64) (hBpos : 0 < B.toNat) (halign : r.toNat % 4 = 0) :
    ∃ τ : List (BitVec 64), ∀ (g : (R : Register) → Option (RegisterType R))
    (w12 w13 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (c : Config), GoodState c.σ → c.σ.regs.get? Register.PC = some 0x80004734#64 →
    (∃ v, c.σ.regs.get? Register.minstret = some v) → c.tick < 2 →
    Vsa.Sim.Code.__moddi3Loaded c.σ.mem → __hidden___udivdi3Loaded c.σ.mem →
    c.σ.mem = m0 → c.σ.sailOutput = o →
    GHolds c.σ [(10, A), (11, B), (5, r), (12, w12), (13, w13)] →
    A.toNat = n.toInt.natAbs → B.toNat = d.toInt.natAbs → d.toInt ≠ 0 → 0 ≤ n.toInt →
    (∀ R : Register, NotWrittenD R → c.σ.regs.get? R = g R) →
    ∃ c' : Config, RunT c τ c' ∧ moddi3_post g n d r m0 o c' := by
  obtain ⟨τ, hT⟩ := core_call_segT A B (BitVec.addInt 0x80004734#64 4) hBpos (by decide)
  refine ⟨0x80004734#64 :: τ ++ pcsC moddi3PosTailSeg, fun g w12 w13 m0 o c hG hpc hmi hi hwl hcl hmem hout hL hA hB
    hd0 hsign hframe0 => ?_⟩
  obtain ⟨vm, hvm⟩ := hmi
  obtain ⟨c3, hs3, hG3, hmem3, hout3, hpc3, hi3, ⟨vm3, hvm3⟩, hL3, hfr3⟩ :=
    hT hpc (site3_80004734 c.σ c.tick c.steps _ vm hG hpc hvm hwl rfl hi) (by decide)
      hcl hmem hout hL
  have hwl3 : Vsa.Sim.Code.__moddi3Loaded c3.σ.mem := by rw [hmem3, ← hmem]; exact hwl
  have facts : ChainFacts c3.σ.mem c3.σ.mem [(10, A / B), (11, A % B), (5, r)] []
      moddi3PosTailSeg := by
    chain_facts hwl3
    exact ret_tgt_aligned r halign
  obtain ⟨c4, res, hrun⟩ := segEval_selected_framedT moddi3PosTailSeg _ [] 0x80004738#64 vm3
    (fun _ => False) divOverflowKeep [(10, A % B)] c3 hG3 hpc3 hvm3 hL3
    (by show KeysOK [10, 11, 5]; decide) facts (by show ChainOK _ [10, 11, 5] _; decide) hi3
    (fun _ _ => rfl) (by decide) (by decide) ⟨congrArg some (addi0T _), trivial⟩
  obtain ⟨hq, _⟩ := res.selected_regs
  refine ⟨c4, hs3.trans hrun, res.good, res.mem_eq.trans hmem3, res.output.trans hout3,
    res.pc.trans (congrArg some (ret_tgt r halign)), res.tick, ?_, _, hq,
    res_pos n d A B hA hB hsign hd0⟩
  intro R hR
  exact (res.reg_frame R (decide_eq_true hR)).trans ((hfr3 R hR).trans (hframe0 R hR))

theorem moddi3_fin_negT (n d A B r : BitVec 64) (hBpos : 0 < B.toNat) (halign : r.toNat % 4 = 0) :
    ∃ τ : List (BitVec 64), ∀ (g : (R : Register) → Option (RegisterType R))
    (w12 w13 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (c : Config), GoodState c.σ → c.σ.regs.get? Register.PC = some 0x8000474c#64 →
    (∃ v, c.σ.regs.get? Register.minstret = some v) → c.tick < 2 →
    Vsa.Sim.Code.__moddi3Loaded c.σ.mem → __hidden___udivdi3Loaded c.σ.mem →
    c.σ.mem = m0 → c.σ.sailOutput = o →
    GHolds c.σ [(10, A), (11, B), (5, r), (12, w12), (13, w13)] →
    A.toNat = n.toInt.natAbs → B.toNat = d.toInt.natAbs → d.toInt ≠ 0 → n.toInt < 0 →
    (∀ R : Register, NotWrittenD R → c.σ.regs.get? R = g R) →
    ∃ c' : Config, RunT c τ c' ∧ moddi3_post g n d r m0 o c' := by
  obtain ⟨τ, hT⟩ := core_call_segT A B (BitVec.addInt 0x8000474c#64 4) hBpos (by decide)
  refine ⟨0x8000474c#64 :: τ ++ pcsC moddi3NegTailSeg, fun g w12 w13 m0 o c hG hpc hmi hi hwl hcl hmem hout hL hA hB
    hd0 hsign hframe0 => ?_⟩
  obtain ⟨vm, hvm⟩ := hmi
  obtain ⟨c3, hs3, hG3, hmem3, hout3, hpc3, hi3, ⟨vm3, hvm3⟩, hL3, hfr3⟩ :=
    hT hpc (site3_8000474c c.σ c.tick c.steps _ vm hG hpc hvm hwl rfl hi) (by decide)
      hcl hmem hout hL
  have hwl3 : Vsa.Sim.Code.__moddi3Loaded c3.σ.mem := by rw [hmem3, ← hmem]; exact hwl
  have facts : ChainFacts c3.σ.mem c3.σ.mem [(10, A / B), (11, A % B), (5, r)] []
      moddi3NegTailSeg := by
    chain_facts hwl3
    exact ret_tgt_aligned r halign
  obtain ⟨c4, res, hrun⟩ := segEval_selected_framedT moddi3NegTailSeg _ [] 0x80004750#64 vm3
    (fun _ => False) divOverflowKeep [(10, 0#64 - A % B)] c3 hG3 hpc3 hvm3 hL3
    (by show KeysOK [10, 11, 5]; decide) facts (by show ChainOK _ [10, 11, 5] _; decide) hi3
    (fun _ _ => rfl) (by decide) (by decide) ⟨rfl, trivial⟩
  obtain ⟨hq, _⟩ := res.selected_regs
  refine ⟨c4, hs3.trans hrun, res.good, res.mem_eq.trans hmem3, res.output.trans hout3,
    res.pc.trans (congrArg some (ret_tgt r halign)), res.tick, ?_, _, hq,
    res_neg n d A B hA hB hsign hd0⟩
  intro R hR
  exact (res.reg_frame R (decide_eq_true hR)).trans ((hfr3 R hR).trans (hframe0 R hR))

theorem divdi3_mixed_finT (n d A B r : BitVec 64) (hBpos : 0 < B.toNat) (halign : r.toNat % 4 = 0) :
    ∃ τ : List (BitVec 64), ∀ (g : (R : Register) → Option (RegisterType R))
    (w12 w13 : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (c : Config), GoodState c.σ → c.σ.regs.get? Register.PC = some 0x8000471c#64 →
    (∃ v, c.σ.regs.get? Register.minstret = some v) → c.tick < 2 →
    Vsa.Sim.Code.__umoddi3Loaded c.σ.mem → __hidden___udivdi3Loaded c.σ.mem →
    c.σ.mem = m0 → c.σ.sailOutput = o →
    GHolds c.σ [(10, A), (11, B), (5, r), (12, w12), (13, w13)] →
    A.toNat = n.toInt.natAbs → B.toNat = d.toInt.natAbs → d.toInt ≠ 0 → ¬(0 ≤ n.toInt ↔ 0 ≤ d.toInt) →
    (∀ R : Register, NotWrittenD R → c.σ.regs.get? R = g R) →
    ∃ c' : Config, RunT c τ c' ∧ divdi3_post g n d r m0 o c' := by
  obtain ⟨τ, hT⟩ := core_call_segT A B (BitVec.addInt 0x8000471c#64 4) hBpos (by decide)
  refine ⟨0x8000471c#64 :: τ ++ pcsC divdi3NegTailSeg, fun g w12 w13 m0 o c hG hpc hmi hi hwl hcl hmem hout hL hA hB
    hd0 hsign hframe0 => ?_⟩
  obtain ⟨vm, hvm⟩ := hmi
  obtain ⟨c3, hs3, hG3, hmem3, hout3, hpc3, hi3, ⟨vm3, hvm3⟩, hL3, hfr3⟩ :=
    hT hpc (site3_8000471c c.σ c.tick c.steps _ vm hG hpc hvm hwl rfl hi) (by decide)
      hcl hmem hout hL
  have hwl3 : Vsa.Sim.Code.__umoddi3Loaded c3.σ.mem := by rw [hmem3, ← hmem]; exact hwl
  have facts : ChainFacts c3.σ.mem c3.σ.mem [(10, A / B), (11, A % B), (5, r)] []
      divdi3NegTailSeg := by
    chain_facts hwl3
    exact ret_tgt_aligned r halign
  obtain ⟨c4, res, hrun⟩ := segEval_selected_framedT divdi3NegTailSeg _ [] 0x80004720#64 vm3
    (fun _ => False) divOverflowKeep [(10, 0#64 - A / B)] c3 hG3 hpc3 hvm3 hL3
    (by show KeysOK [10, 11, 5]; decide) facts (by show ChainOK _ [10, 11, 5] _; decide) hi3
    (fun _ _ => rfl) (by decide) (by decide) ⟨rfl, trivial⟩
  obtain ⟨hq, _⟩ := res.selected_regs
  refine ⟨c4, hs3.trans hrun, res.good, res.mem_eq.trans hmem3, res.output.trans hout3,
    res.pc.trans (congrArg some (ret_tgt r halign)), res.tick, ?_, _, hq,
    res_div_mixed n d A B hA hB hsign hd0⟩
  intro R hR
  exact (res.reg_frame R (decide_eq_true hR)).trans ((hfr3 R hR).trans (hframe0 R hR))

theorem moddi3_specT (n d r : BitVec 64) (hd0 : d.toInt ≠ 0) (halign : r.toNat % 4 = 0) :
    ∃ τ : List (BitVec 64), ∀ g m0 o, TripleT τ (moddi3_pre g n d r m0 o) (moddi3_post g n d r m0 o) := by
  have hd0' : d.toInt.natAbs ≠ 0 := fun h => hd0 (Int.natAbs_eq_zero.mp h)
  rcases bltz_cases' d with hdlt | hdge
  · have hdtop : 2^63 ≤ d.toNat := bltz_true' d hdlt
    have hBmag : ((0#64) - d).toNat = d.toInt.natAbs := mag_neg_top d hdtop
    rcases bgez_cases' n with hnge | hnlt
    · have hntop : n.toNat < 2^63 := bgez_true' n hnge
      obtain ⟨τf, hT⟩ := moddi3_fin_posT n d n (0#64 - d) r (by rw [hBmag]; omega) halign
      refine ⟨pcsC moddi3PNSeg ++ τf, fun g m0 o c hc => ?_⟩
      obtain ⟨hG, hwl, hcl, hmem, hout, hpc, hn, hd, hr, ⟨vm, hmi⟩,
        ⟨w12, h12⟩, ⟨w13, h13⟩, htick, _, _, hframeE⟩ := hc
      have held : GHolds c.σ (divIn n d r w12 w13) := ⟨hn, hd, hr, h12, h13, trivial⟩
      have f1 : ChainFacts c.σ.mem c.σ.mem (divIn n d r w12 w13) [] moddi3PNSeg := by
        chain_facts hwl
        exact hdlt
        exact hnge
      obtain ⟨c1, r1, hrun1⟩ := segEval_selected_framedT moddi3PNSeg _ [] _ vm (fun _ => False)
        divOverflowKeep [(10, n), (11, 0#64 - d), (5, r), (12, w12), (13, w13)] c hG hpc hmi held
        (by show KeysOK [10, 11, 1, 12, 13]; decide) f1
        (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) htick (fun _ _ => rfl) (by decide)
        (by decide) ⟨rfl, rfl, congrArg some (addi0T r), rfl, rfl, trivial⟩
      have m1 := r1.mem_eq
      obtain ⟨cf, hsf, post⟩ := hT g w12 w13 m0 o c1 r1.good r1.pc r1.minstret r1.tick (m1 ▸ hwl)
        (m1 ▸ hcl) (m1.trans hmem) (r1.output.trans hout) r1.selected_regs (mag_notop n hntop) hBmag hd0 (by rw [toInt_of_notop n hntop]; exact Int.natCast_nonneg _)
        (r1.frameD hframeE)
      exact ⟨cf, hrun1.trans hsf, post⟩
    · have hntop : 2^63 ≤ n.toNat := bgez_false' n hnlt
      obtain ⟨τf, hT⟩ := moddi3_fin_negT n d (0#64 - n) (0#64 - d) r (by rw [hBmag]; omega) halign
      refine ⟨pcsC moddi3NNSeg ++ τf, fun g m0 o c hc => ?_⟩
      obtain ⟨hG, hwl, hcl, hmem, hout, hpc, hn, hd, hr, ⟨vm, hmi⟩,
        ⟨w12, h12⟩, ⟨w13, h13⟩, htick, _, _, hframeE⟩ := hc
      have held : GHolds c.σ (divIn n d r w12 w13) := ⟨hn, hd, hr, h12, h13, trivial⟩
      have f1 : ChainFacts c.σ.mem c.σ.mem (divIn n d r w12 w13) [] moddi3NNSeg := by
        chain_facts hwl
        exact hdlt
        exact hnlt
      obtain ⟨c1, r1, hrun1⟩ := segEval_selected_framedT moddi3NNSeg _ [] _ vm (fun _ => False)
        divOverflowKeep [(10, 0#64 - n), (11, 0#64 - d), (5, r), (12, w12), (13, w13)] c hG hpc hmi held
        (by show KeysOK [10, 11, 1, 12, 13]; decide) f1
        (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) htick (fun _ _ => rfl) (by decide)
        (by decide) ⟨rfl, rfl, congrArg some (addi0T r), rfl, rfl, trivial⟩
      have m1 := r1.mem_eq
      obtain ⟨cf, hsf, post⟩ := hT g w12 w13 m0 o c1 r1.good r1.pc r1.minstret r1.tick (m1 ▸ hwl)
        (m1 ▸ hcl) (m1.trans hmem) (r1.output.trans hout) r1.selected_regs (mag_neg_top n hntop) hBmag hd0 (by rw [toInt_of_top n hntop]; have := n.isLt; omega)
        (r1.frameD hframeE)
      exact ⟨cf, hrun1.trans hsf, post⟩
  · have hdtop : d.toNat < 2^63 := bltz_false' d hdge
    have hBmag : d.toNat = d.toInt.natAbs := mag_notop d hdtop
    rcases bltz_cases' n with hnlt | hnge
    · have hntop : 2^63 ≤ n.toNat := bltz_true' n hnlt
      obtain ⟨τf, hT⟩ := moddi3_fin_negT n d (0#64 - n) d r (by rw [hBmag]; omega) halign
      refine ⟨pcsC moddi3NPSeg ++ τf, fun g m0 o c hc => ?_⟩
      obtain ⟨hG, hwl, hcl, hmem, hout, hpc, hn, hd, hr, ⟨vm, hmi⟩,
        ⟨w12, h12⟩, ⟨w13, h13⟩, htick, _, _, hframeE⟩ := hc
      have held : GHolds c.σ (divIn n d r w12 w13) := ⟨hn, hd, hr, h12, h13, trivial⟩
      have f1 : ChainFacts c.σ.mem c.σ.mem (divIn n d r w12 w13) [] moddi3NPSeg := by
        chain_facts hwl
        exact hdge
        exact hnlt
      obtain ⟨c1, r1, hrun1⟩ := segEval_selected_framedT moddi3NPSeg _ [] _ vm (fun _ => False)
        divOverflowKeep [(10, 0#64 - n), (11, d), (5, r), (12, w12), (13, w13)] c hG hpc hmi held
        (by show KeysOK [10, 11, 1, 12, 13]; decide) f1
        (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) htick (fun _ _ => rfl) (by decide)
        (by decide) ⟨rfl, rfl, congrArg some (addi0T r), rfl, rfl, trivial⟩
      have m1 := r1.mem_eq
      obtain ⟨cf, hsf, post⟩ := hT g w12 w13 m0 o c1 r1.good r1.pc r1.minstret r1.tick (m1 ▸ hwl)
        (m1 ▸ hcl) (m1.trans hmem) (r1.output.trans hout) r1.selected_regs (mag_neg_top n hntop) hBmag hd0 (by rw [toInt_of_top n hntop]; have := n.isLt; omega)
        (r1.frameD hframeE)
      exact ⟨cf, hrun1.trans hsf, post⟩
    · have hntop : n.toNat < 2^63 := bltz_false' n hnge
      obtain ⟨τf, hT⟩ := moddi3_fin_posT n d n d r (by rw [hBmag]; omega) halign
      refine ⟨pcsC moddi3PPSeg ++ τf, fun g m0 o c hc => ?_⟩
      obtain ⟨hG, hwl, hcl, hmem, hout, hpc, hn, hd, hr, ⟨vm, hmi⟩,
        ⟨w12, h12⟩, ⟨w13, h13⟩, htick, _, _, hframeE⟩ := hc
      have held : GHolds c.σ (divIn n d r w12 w13) := ⟨hn, hd, hr, h12, h13, trivial⟩
      have f1 : ChainFacts c.σ.mem c.σ.mem (divIn n d r w12 w13) [] moddi3PPSeg := by
        chain_facts hwl
        exact hdge
        exact hnge
      obtain ⟨c1, r1, hrun1⟩ := segEval_selected_framedT moddi3PPSeg _ [] _ vm (fun _ => False)
        divOverflowKeep [(10, n), (11, d), (5, r), (12, w12), (13, w13)] c hG hpc hmi held
        (by show KeysOK [10, 11, 1, 12, 13]; decide) f1
        (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) htick (fun _ _ => rfl) (by decide)
        (by decide) ⟨rfl, rfl, congrArg some (addi0T r), rfl, rfl, trivial⟩
      have m1 := r1.mem_eq
      obtain ⟨cf, hsf, post⟩ := hT g w12 w13 m0 o c1 r1.good r1.pc r1.minstret r1.tick (m1 ▸ hwl)
        (m1 ▸ hcl) (m1.trans hmem) (r1.output.trans hout) r1.selected_regs (mag_notop n hntop) hBmag hd0 (by rw [toInt_of_notop n hntop]; exact Int.natCast_nonneg _)
        (r1.frameD hframeE)
      exact ⟨cf, hrun1.trans hsf, post⟩

theorem divdi3_specT (n d r : BitVec 64) (hd0 : d.toInt ≠ 0)
    (hexcl : ¬(n.toInt = -2^63 ∧ d.toInt = -1)) (halign : r.toNat % 4 = 0) :
    ∃ τ : List (BitVec 64), ∀ g m0 o, TripleT τ (divdi3_pre g n d r m0 o) (divdi3_post g n d r m0 o) := by
  have hd0' : d.toInt.natAbs ≠ 0 := fun h => hd0 (Int.natAbs_eq_zero.mp h)
  rcases bltz_cases' n with hnlt | hnge
  · have hntop : 2^63 ≤ n.toNat := bltz_true' n hnlt
    have hnneg : n.toInt < 0 := by rw [toInt_of_top n hntop]; have := n.isLt; omega
    have hAmag : ((0#64) - n).toNat = n.toInt.natAbs := mag_neg_top n hntop
    rcases bgtz_cases' d with hdgt | hdle
    · have hdpos : 0 < d.toInt := bgtz_true' d hdgt
      have hdtop : d.toNat < 2^63 := by
        by_cases hc' : d.toNat < 2^63
        · exact hc'
        · rw [toInt_of_top d (by omega)] at hdpos; have := d.isLt; omega
      have hBmag : d.toNat = d.toInt.natAbs := mag_notop d hdtop
      obtain ⟨τf, hT⟩ := divdi3_mixed_finT n d (0#64 - n) d r (by rw [hBmag]; omega) halign
      refine ⟨pcsC divOverflowBranchSeg ++ pcsC divdi3NegPosSeg ++ τf, fun g m0 o c hc => ?_⟩
      obtain ⟨hG, hdl, hul, hcl, hmem, hout, hpc, hn, hd, hr, ⟨vm, hmi⟩,
        ⟨w12, h12⟩, ⟨w13, h13⟩, htick, _, _, _, hframeE⟩ := hc
      have held : GHolds c.σ (divIn n d r w12 w13) := ⟨hn, hd, hr, h12, h13, trivial⟩
      have f1 : ChainFacts c.σ.mem c.σ.mem (divIn n d r w12 w13) [] divOverflowBranchSeg := by
        chain_facts hdl
        exact hnlt
      obtain ⟨c1, r1, hrun1⟩ := segEval_selected_framedT divOverflowBranchSeg _ [] _ vm
        (fun _ => False) divOverflowKeep (divIn n d r w12 w13) c hG hpc hmi held
        (by show KeysOK [10, 11, 1, 12, 13]; decide) f1
        (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) htick (fun _ _ => rfl) (by decide)
        (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
      have m1 := r1.mem_eq
      obtain ⟨vm1, hvm1⟩ := r1.minstret
      have hul1 : Vsa.Sim.Code.__umoddi3Loaded c1.σ.mem := m1 ▸ hul
      have f2 : ChainFacts c1.σ.mem c1.σ.mem (divIn n d r w12 w13) [] divdi3NegPosSeg := by
        chain_facts hul1
        exact hdgt
      obtain ⟨c2, r2, hrun2⟩ := segEval_selected_framedT divdi3NegPosSeg _ [] 0x80004704#64 vm1
        (fun _ => False) divOverflowKeep [(10, 0#64 - n), (11, d), (5, r), (12, w12), (13, w13)]
        c1 r1.good r1.pc hvm1 r1.selected_regs (by show KeysOK [10, 11, 1, 12, 13]; decide) f2
        (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) r1.tick (fun _ _ => rfl) (by decide)
        (by decide) ⟨rfl, rfl, congrArg some (addi0T r), rfl, rfl, trivial⟩
      have m2 := r2.mem_eq.trans m1
      obtain ⟨cf, hsf, post⟩ := hT g w12 w13 m0 o c2 r2.good r2.pc r2.minstret r2.tick (m2 ▸ hul)
        (m2 ▸ hcl) (m2.trans hmem) (r2.output.trans (r1.output.trans hout)) r2.selected_regs
        hAmag hBmag hd0 (fun hi => absurd (hi.mpr (Int.le_of_lt hdpos)) (by omega))
        (r2.frameD (r1.frameD hframeE))
      exact ⟨cf, (hrun1.trans hrun2).trans hsf, post⟩
    · have hdle' : d.toInt ≤ 0 := bgtz_false' d hdle
      have hdneg : d.toInt < 0 := by omega
      have hdtop : 2^63 ≤ d.toNat := by
        by_cases hc' : d.toNat < 2^63
        · rw [toInt_of_notop d hc'] at hdneg; have := d.isLt; omega
        · omega
      have hBmag : ((0#64) - d).toNat = d.toInt.natAbs := mag_neg_top d hdtop
      have hsame : (0 ≤ n.toInt ↔ 0 ≤ d.toInt) :=
        ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
      obtain ⟨τf, hT⟩ := core_call_tail_fT (0#64 - n) (0#64 - d) r (by rw [hBmag]; omega) halign
      refine ⟨pcsC divOverflowBranchSeg ++ pcsC divdi3NegNegSeg ++ τf, fun g m0 o c hc => ?_⟩
      obtain ⟨hG, hdl, hul, hcl, hmem, hout, hpc, hn, hd, hr, ⟨vm, hmi⟩,
        ⟨w12, h12⟩, ⟨w13, h13⟩, htick, _, _, _, hframeE⟩ := hc
      have held : GHolds c.σ (divIn n d r w12 w13) := ⟨hn, hd, hr, h12, h13, trivial⟩
      have f1 : ChainFacts c.σ.mem c.σ.mem (divIn n d r w12 w13) [] divOverflowBranchSeg := by
        chain_facts hdl
        exact hnlt
      obtain ⟨c1, r1, hrun1⟩ := segEval_selected_framedT divOverflowBranchSeg _ [] _ vm
        (fun _ => False) divOverflowKeep (divIn n d r w12 w13) c hG hpc hmi held
        (by show KeysOK [10, 11, 1, 12, 13]; decide) f1
        (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) htick (fun _ _ => rfl) (by decide)
        (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
      have m1 := r1.mem_eq
      obtain ⟨vm1, hvm1⟩ := r1.minstret
      have hul1 : Vsa.Sim.Code.__umoddi3Loaded c1.σ.mem := m1 ▸ hul
      have f2 : ChainFacts c1.σ.mem c1.σ.mem (divIn n d r w12 w13) [] divdi3NegNegSeg := by
        chain_facts hul1
        exact hdle
      obtain ⟨c2, r2, hrun2⟩ := segEval_selected_framedT divdi3NegNegSeg _ [] 0x80004704#64 vm1
        (fun _ => False) divOverflowKeep (divIn (0#64 - n) (0#64 - d) r w12 w13)
        c1 r1.good r1.pc hvm1 r1.selected_regs (by show KeysOK [10, 11, 1, 12, 13]; decide) f2
        (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) r1.tick (fun _ _ => rfl) (by decide)
        (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
      have m2 := r2.mem_eq.trans m1
      obtain ⟨x10, x11, x1, x12, x13, _⟩ := r2.selected_regs
      obtain ⟨c3, hs3, hG3, hmem3, hout3, hpc3, hq3, _, _, htick3, hframe3, _⟩ :=
        hT m0 o c2 r2.good (m2 ▸ hcl) (m2.trans hmem) (r2.output.trans (r1.output.trans hout))
          r2.pc x10 x11 x1 ⟨w12, x12⟩ ⟨w13, x13⟩ r2.minstret r2.tick
      refine ⟨c3, (hrun1.trans hrun2).trans hs3, hG3, hmem3, hout3, hpc3, htick3, ?_, _, hq3,
        res_div_same n d _ _ hAmag hBmag hsame hd0
          (udiv_lt_of_not_overflow n d _ _ hAmag hBmag hsame hd0 hexcl)⟩
      intro R hR
      rw [hframe3 R hR.nw]; exact r2.frameD (r1.frameD hframeE) R hR
  · have hntop : n.toNat < 2^63 := bltz_false' n hnge
    have hnInt : 0 ≤ n.toInt := by rw [toInt_of_notop n hntop]; exact Int.natCast_nonneg _
    have hAmag : n.toNat = n.toInt.natAbs := mag_notop n hntop
    rcases bltz_cases' d with hdlt | hdge
    · have hdtop : 2^63 ≤ d.toNat := bltz_true' d hdlt
      have hdneg : d.toInt < 0 := by rw [toInt_of_top d hdtop]; have := d.isLt; omega
      have hBmag : ((0#64) - d).toNat = d.toInt.natAbs := mag_neg_top d hdtop
      obtain ⟨τf, hT⟩ := divdi3_mixed_finT n d n (0#64 - d) r (by rw [hBmag]; omega) halign
      refine ⟨pcsC divdi3PosNegSeg ++ pcsC divdi3PosNegSeg2 ++ τf, fun g m0 o c hc => ?_⟩
      obtain ⟨hG, hdl, hul, hcl, hmem, hout, hpc, hn, hd, hr, ⟨vm, hmi⟩,
        ⟨w12, h12⟩, ⟨w13, h13⟩, htick, _, _, _, hframeE⟩ := hc
      have held : GHolds c.σ (divIn n d r w12 w13) := ⟨hn, hd, hr, h12, h13, trivial⟩
      have f1 : ChainFacts c.σ.mem c.σ.mem (divIn n d r w12 w13) [] divdi3PosNegSeg := by
        chain_facts hdl
        exact hnge
        exact hdlt
      obtain ⟨c1, r1, hrun1⟩ := segEval_selected_framedT divdi3PosNegSeg _ [] _ vm (fun _ => False)
        divOverflowKeep (divIn n d r w12 w13) c hG hpc hmi held
        (by show KeysOK [10, 11, 1, 12, 13]; decide) f1
        (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) htick (fun _ _ => rfl) (by decide)
        (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
      have m1 := r1.mem_eq
      obtain ⟨vm1, hvm1⟩ := r1.minstret
      have f2 : ChainFacts c1.σ.mem c1.σ.mem (divIn n d r w12 w13) [] divdi3PosNegSeg2 := by
        chain_facts (m1 ▸ hul : Vsa.Sim.Code.__umoddi3Loaded c1.σ.mem)
          with "Vsa.Sim.Code.__umoddi3_at_"
      obtain ⟨c2, r2, hrun2⟩ := segEval_selected_framedT divdi3PosNegSeg2 _ [] 0x80004714#64 vm1
        (fun _ => False) divOverflowKeep [(10, n), (11, 0#64 - d), (5, r), (12, w12), (13, w13)]
        c1 r1.good r1.pc hvm1 r1.selected_regs (by show KeysOK [10, 11, 1, 12, 13]; decide) f2
        (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) r1.tick (fun _ _ => rfl) (by decide)
        (by decide) ⟨rfl, rfl, congrArg some (addi0T r), rfl, rfl, trivial⟩
      have m2 := r2.mem_eq.trans m1
      obtain ⟨cf, hsf, post⟩ := hT g w12 w13 m0 o c2 r2.good r2.pc r2.minstret r2.tick (m2 ▸ hul)
        (m2 ▸ hcl) (m2.trans hmem) (r2.output.trans (r1.output.trans hout)) r2.selected_regs
        hAmag hBmag hd0 (fun hi => absurd (hi.mp hnInt) (by omega))
        (r2.frameD (r1.frameD hframeE))
      exact ⟨cf, (hrun1.trans hrun2).trans hsf, post⟩
    · have hdtop : d.toNat < 2^63 := bltz_false' d hdge
      have hdInt : 0 ≤ d.toInt := by rw [toInt_of_notop d hdtop]; exact Int.natCast_nonneg _
      have hBmag : d.toNat = d.toInt.natAbs := mag_notop d hdtop
      have hsame : (0 ≤ n.toInt ↔ 0 ≤ d.toInt) := ⟨fun _ => hdInt, fun _ => hnInt⟩
      obtain ⟨τf, hT⟩ := core_call_tail_fT n d r (by rw [hBmag]; omega) halign
      refine ⟨pcsC divdi3PosSeg ++ τf, fun g m0 o c hc => ?_⟩
      obtain ⟨hG, hdl, hul, hcl, hmem, hout, hpc, hn, hd, hr, ⟨vm, hmi⟩,
        ⟨w12, h12⟩, ⟨w13, h13⟩, htick, _, _, _, hframeE⟩ := hc
      have held : GHolds c.σ (divIn n d r w12 w13) := ⟨hn, hd, hr, h12, h13, trivial⟩
      have f1 : ChainFacts c.σ.mem c.σ.mem (divIn n d r w12 w13) [] divdi3PosSeg := by
        chain_facts hdl
        exact hnge
        exact hdge
      obtain ⟨c1, r1, hrun1⟩ := segEval_selected_framedT divdi3PosSeg _ [] _ vm (fun _ => False)
        divOverflowKeep (divIn n d r w12 w13) c hG hpc hmi held
        (by show KeysOK [10, 11, 1, 12, 13]; decide) f1
        (by show ChainOK _ [10, 11, 1, 12, 13] _; decide) htick (fun _ _ => rfl) (by decide)
        (by decide) ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩
      have m1 := r1.mem_eq
      obtain ⟨x10, x11, x1, x12, x13, _⟩ := r1.selected_regs
      obtain ⟨c3, hs3, hG3, hmem3, hout3, hpc3, hq3, _, _, htick3, hframe3, _⟩ :=
        hT m0 o c1 r1.good (m1 ▸ hcl) (m1.trans hmem) (r1.output.trans hout) r1.pc x10 x11 x1
          ⟨w12, x12⟩ ⟨w13, x13⟩ r1.minstret r1.tick
      refine ⟨c3, hrun1.trans hs3, hG3, hmem3, hout3, hpc3, htick3, ?_, _, hq3,
        res_div_same n d _ _ hAmag hBmag hsame hd0
          (udiv_lt_of_not_overflow n d _ _ hAmag hBmag hsame hd0 hexcl)⟩
      intro R hR
      rw [hframe3 R hR.nw]; exact r1.frameD hframeE R hR

end Vsa.Sim
