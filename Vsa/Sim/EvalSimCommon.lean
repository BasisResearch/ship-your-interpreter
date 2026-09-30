import Vsa.Sim.ObsAvoid
import Vsa.Sim.EvalExprSites
import Vsa.Sim.InterpEntry

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

def MemExtends (m0 m : Mem) : Prop :=
  ∀ (a : Nat) (b : BitVec 8), m0[a]? = some b → ∃ b', m[a]? = some b'

theorem memExtends_writeMap8 (mem : Mem) (a8 : Nat) (d : BitVec (8 * 8)) :
    MemExtends mem (writeMap8 mem a8 d) := by
  intro k b hk
  by_cases hin : a8 ≤ k ∧ k < a8 + 8
  · obtain ⟨hlo, hhi⟩ := hin
    rcases (show k = a8 ∨ k = a8 + 1 ∨ k = a8 + 2 ∨ k = a8 + 3 ∨ k = a8 + 4 ∨
        k = a8 + 5 ∨ k = a8 + 6 ∨ k = a8 + 7 from by omega)
      with h | h | h | h | h | h | h | h
    · exact ⟨_, by rw [show k = a8 + 0 from by omega]; exact getElem_writeMap8_0 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_1 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_2 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_3 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_4 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_5 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_6 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_7 mem a8 d⟩
  · exact ⟨b, by rw [getElem_writeMap8_disjoint mem a8 k d (by omega)]; exact hk⟩

theorem MemExtends.trans {m0 m1 m2 : Mem}
    (h1 : MemExtends m0 m1) (h2 : MemExtends m1 m2) : MemExtends m0 m2 := by
  intro a b h
  obtain ⟨b', hb'⟩ := h1 a b h
  exact h2 a b' hb'

theorem read64_total_of_memExtends {m0 m : Mem} {a : Nat}
    (hExt : MemExtends m0 m)
    (h : ∃ d : BitVec 64, read64 m0 a = some d.toNat) :
    ∃ d : BitVec 64, read64 m a = some d.toNat := by
  obtain ⟨d, hd⟩ := h
  simp only [read64, readLE, Option.bind_eq_bind, Option.bind_eq_some_iff] at hd
  obtain ⟨b0, hb0, r0, hr0, _⟩ := hd
  obtain ⟨b1, hb1, r1, hr1, _⟩ := hr0
  obtain ⟨b2, hb2, r2, hr2, _⟩ := hr1
  obtain ⟨b3, hb3, r3, hr3, _⟩ := hr2
  obtain ⟨b4, hb4, r4, hr4, _⟩ := hr3
  obtain ⟨b5, hb5, r5, hr5, _⟩ := hr4
  obtain ⟨b6, hb6, r6, hr6, _⟩ := hr5
  obtain ⟨b7, hb7, _, _, _⟩ := hr6
  obtain ⟨b0', hb0'⟩ := hExt a b0 hb0
  obtain ⟨b1', hb1'⟩ := hExt (a + 1) b1 hb1
  obtain ⟨b2', hb2'⟩ := hExt (a + 2) b2 hb2
  obtain ⟨b3', hb3'⟩ := hExt (a + 3) b3 hb3
  obtain ⟨b4', hb4'⟩ := hExt (a + 4) b4 hb4
  obtain ⟨b5', hb5'⟩ := hExt (a + 5) b5 hb5
  obtain ⟨b6', hb6'⟩ := hExt (a + 6) b6 hb6
  obtain ⟨b7', hb7'⟩ := hExt (a + 7) b7 hb7
  let d' : BitVec 64 := sign_extend (m := 64)
    (((((((b7'.append b6').append b5').append b4').append b3').append b2').append b1').append b0')
  refine ⟨d', ?_⟩
  simp only [read64, readLE, bind, Option.bind, pure, hb0', hb1', hb2', hb3', hb4', hb5',
    hb6', hb7', Nat.mul_zero, Nat.add_zero, d']
  rw [sext_full]
  apply congrArg some
  exact (word8_toNat_recon b0' b1' b2' b3' b4' b5' b6' b7').symm

theorem valueWordsTotal_of_interval {m : Mem} {lo hi a : Nat}
    (hPop : ∀ k : Nat, lo ≤ k → k < hi → ∃ b : BitVec 8, m[k]? = some b)
    (hlo : lo ≤ a) (hhi : a + 24 ≤ hi) :
    ValueWordsTotal m a := by
  have word (x : Nat) (hxlo : lo ≤ x) (hxhi : x + 8 ≤ hi) :
      ∃ d : BitVec 64, read64 m x = some d.toNat := by
    obtain ⟨b0, hb0⟩ := hPop x (by omega) (by omega)
    obtain ⟨b1, hb1⟩ := hPop (x + 1) (by omega) (by omega)
    obtain ⟨b2, hb2⟩ := hPop (x + 2) (by omega) (by omega)
    obtain ⟨b3, hb3⟩ := hPop (x + 3) (by omega) (by omega)
    obtain ⟨b4, hb4⟩ := hPop (x + 4) (by omega) (by omega)
    obtain ⟨b5, hb5⟩ := hPop (x + 5) (by omega) (by omega)
    obtain ⟨b6, hb6⟩ := hPop (x + 6) (by omega) (by omega)
    obtain ⟨b7, hb7⟩ := hPop (x + 7) (by omega) (by omega)
    let d : BitVec 64 := sign_extend (m := 64)
      (((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
    refine ⟨d, ?_⟩
    simp only [read64, readLE, bind, Option.bind, pure, hb0, hb1, hb2, hb3, hb4, hb5,
      hb6, hb7, Nat.mul_zero, Nat.add_zero, d]
    rw [sext_full]
    apply congrArg some
    exact (word8_toNat_recon b0 b1 b2 b3 b4 b5 b6 b7).symm
  obtain ⟨d0, h0⟩ := word a hlo (by omega)
  obtain ⟨d1, h1⟩ := word (a + 8) (by omega) (by omega)
  obtain ⟨d2, h2⟩ := word (a + 16) (by omega) (by omega)
  exact ⟨d0, d1, d2, h0, h1, h2⟩

theorem ValueWordsTotal.mono {m0 m : Mem} {a : Nat}
    (hExt : MemExtends m0 m) (h : ValueWordsTotal m0 a) :
    ValueWordsTotal m a := by
  obtain ⟨d0, d1, d2, h0, h1, h2⟩ := h
  obtain ⟨d0', h0'⟩ := read64_total_of_memExtends hExt ⟨d0, h0⟩
  obtain ⟨d1', h1'⟩ := read64_total_of_memExtends hExt ⟨d1, h1⟩
  obtain ⟨d2', h2'⟩ := read64_total_of_memExtends hExt ⟨d2, h2⟩
  exact ⟨d0', d1', d2', h0', h1', h2'⟩

end Vsa.Sim
