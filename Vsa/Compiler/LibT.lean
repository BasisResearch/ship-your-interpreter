import Vsa.Compiler.Lift
import Vsa.Sim.DivWrapT
import Vsa.Sim.MulT

namespace Vsa.Compiler

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa Vsa.Sim
open Vsa.Machine (MState Config Step Steps RunT)

theorem sim_divT (x y r : BitVec 64) (hy0 : y.toInt ≠ 0) (hral : r.toNat % 4 = 0) :
    ∃ τ : List (BitVec 64), ∀ {A : AM} {c : Config}, Corr c A → A.pc = 0x800046a4#64 →
      lookupG 1 A.regs = some r → lookupG 10 A.regs = some x → lookupG 11 A.regs = some y →
      12 ∈ keysG A.regs → 13 ∈ keysG A.regs → LibLoaded A.mem →
      ∃ c', RunT c τ c' ∧ Corr c' ⟨r, (10, BitVec.ofInt 64 (x.toInt.tdiv y.toInt)) ::
        eraseAll clobbered A.regs, A.mem, A.out⟩ := by
  obtain ⟨τ, hT⟩ := divdi3_wrap_specT x y r hy0 hral
  refine ⟨τ, fun {A c} hc hpc hr hx hy h12 h13 hlib => ?_⟩
  obtain ⟨c', hs, post⟩ :=
    hT (fun R => c.σ.regs.get? R) c.σ.mem c.σ.sailOutput c
      ⟨hc.good, hc.mem ▸ hlib.div, hc.mem ▸ hlib.umod, hc.mem ▸ hlib.udiv, rfl, rfl,
        hpc ▸ hc.pc, corr_reg hc hx, corr_reg hc hy, corr_reg hc hr, hc.good.minstret,
        corr_reg_ex hc h12, corr_reg_ex hc h13, hc.tick, hy0, hral, fun _ _ => rfl⟩
  exact ⟨c', hs, corr_after_lib hc post.good post.tick post.mem post.output post.pc
    post.quotient post.frame⟩

theorem sim_modT (x y r : BitVec 64) (hy0 : y.toInt ≠ 0) (hral : r.toNat % 4 = 0) :
    ∃ τ : List (BitVec 64), ∀ {A : AM} {c : Config}, Corr c A → A.pc = 0x80004728#64 →
      lookupG 1 A.regs = some r → lookupG 10 A.regs = some x → lookupG 11 A.regs = some y →
      12 ∈ keysG A.regs → 13 ∈ keysG A.regs → LibLoaded A.mem →
      ∃ c', RunT c τ c' ∧ Corr c' ⟨r, (10, BitVec.ofInt 64 (x.toInt.tmod y.toInt)) ::
        eraseAll clobbered A.regs, A.mem, A.out⟩ := by
  obtain ⟨τ, hT⟩ := moddi3_specT x y r hy0 hral
  refine ⟨τ, fun {A c} hc hpc hr hx hy h12 h13 hlib => ?_⟩
  obtain ⟨c', hs, hG, hmem, hout, hpc', ht, hfr, res, h10, hres⟩ :=
    hT (fun R => c.σ.regs.get? R) c.σ.mem c.σ.sailOutput c
      ⟨hc.good, hc.mem ▸ hlib.mod, hc.mem ▸ hlib.udiv, rfl, rfl, hpc ▸ hc.pc,
        corr_reg hc hx, corr_reg hc hy, corr_reg hc hr, hc.good.minstret,
        corr_reg_ex hc h12, corr_reg_ex hc h13, hc.tick, hy0, hral, fun _ _ => rfl⟩
  have hres' : BitVec.ofInt 64 (x.toInt.tmod y.toInt) = res := by
    rw [← hres, BitVec.ofInt_toInt]
  exact ⟨c', hs, corr_after_lib hc hG ht hmem hout hpc' (hres' ▸ h10) hfr⟩

theorem sim_mulT (x y r : BitVec 64) (hral : r.toNat % 4 = 0) :
    ∃ τ : List (BitVec 64), ∀ {A : AM} {c : Config}, Corr c A → A.pc = 0x80004640#64 →
      lookupG 1 A.regs = some r → lookupG 10 A.regs = some x → lookupG 11 A.regs = some y →
      12 ∈ keysG A.regs → 13 ∈ keysG A.regs → LibLoaded A.mem →
      ∃ c', RunT c τ c' ∧ Corr c' ⟨r, (10, x * y) :: eraseAll clobbered A.regs, A.mem, A.out⟩ := by
  obtain ⟨τ, hT⟩ := muldi3_specT x y r hral
  refine ⟨τ, fun {A c} hc hpc hr hx hy h12 h13 hlib => ?_⟩
  obtain ⟨v12, h12'⟩ := corr_reg_ex hc h12
  obtain ⟨v13, h13'⟩ := corr_reg_ex hc h13
  obtain ⟨c', hs, hG, hmem, hout, hpc', h10, _, ht, hfr⟩ :=
    hT (fun R => c.σ.regs.get? R) c.σ.mem c.σ.sailOutput c
      ⟨⟨v12, v13, ⟨hc.good, hc.mem ▸ hlib.mul, rfl, rfl, hpc ▸ hc.pc, corr_reg hc hx,
        corr_reg hc hy, h12', h13', corr_reg hc hr, hc.good.minstret, hc.tick,
        fun _ _ => rfl⟩⟩, hral⟩
  exact ⟨c', hs, corr_after_lib hc hG ht hmem hout hpc' h10 (fun R h => hfr R h.1)⟩

end Vsa.Compiler
