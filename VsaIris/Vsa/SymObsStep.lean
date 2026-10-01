import VsaIris.Vsa.SymObs
import Vsa.Sim.DecodeNF

/-!
# Unsigned compares, for any registers

`sltu rd, rs1, rs2` and `sltiu rd, rs1, imm` are outside the block model (`MKind`); the per-pc
step tables prove one `AluStep` per site. `aluStep_sltu` / `aluStep_sltiu` prove it once, for
every register triple, from the generic register accessors (`rX_src`, `wX_gpr`).
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast
open Vsa.Machine (Config MState)
open Iris
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- Source operand of a register-register line: `x0` reads zero. -/
def srcO (R : Nat → BitVec 64) (r : Nat) : BitVec 64 := if r = 0 then 0#64 else R r

/-- The register pins a site needs, as the generic accessor states them. -/
theorem srcPin_of_pins {σ : MState} {R : Nat → BitVec 64} {ks : List Nat}
    (hRR : ∀ q ∈ ks.map (fun k => (k, DFrac.own 1, R k)), gprGet σ q.1 = some q.2.2) :
    ∀ r, (r = 0 ∨ r ∈ ks) → srcPin σ r (srcO R r)
  | 0, _ => rfl
  | m + 1, hr => by
    have hm : m + 1 ∈ ks := by
      rcases hr with h | h
      · exact absurd h (by omega)
      · exact h
    have := hRR (m + 1, DFrac.own 1, R (m + 1)) (List.mem_map.2 ⟨m + 1, hm, rfl⟩)
    show gprGet σ (m + 1) = some (srcO R (m + 1))
    rw [show srcO R (m + 1) = R (m + 1) from if_neg (by omega)]
    exact this

section site

variable {live : Nat → Prop} (i : Nat) (w : BitVec 32) (b0 b1 b2 b3 : BitVec 8)
  (rd : Nat) (R : Nat → BitVec 64) (ks : List Nat)

/-- The byte pins of a four-byte site. -/
theorem site_bytes {σ : MState}
    (hMR : ∀ q ∈ codeFoot i [b0, b1, b2, b3], σ.mem[q.1]? = some q.2.2) :
    σ.mem[i]? = some b0 ∧ σ.mem[i + 1]? = some b1 ∧ σ.mem[i + 2]? = some b2 ∧
      σ.mem[i + 3]? = some b3 :=
  ⟨hMR (i, .discard, b0) (by simp [codeFoot]), hMR (i + 1, .discard, b1) (by simp [codeFoot]),
    hMR (i + 2, .discard, b2) (by simp [codeFoot]), hMR (i + 3, .discard, b3) (by simp [codeFoot])⟩

/-- An ALU site whose `execute` fact is given for the generic destination register. -/
theorem aluStep_site (val : BitVec 64) (ast : instruction)
    (hrd1 : 1 ≤ rd) (hrd31 : rd ≤ 31) (hks : KeysOK ks)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : ∀ σ, decodeN w σ = .ok ast σ)
    (hlo : 0x80000000 ≤ i) (hhi : i + 4 ≤ tohostAddr) (hal : i % 4 = 0)
    (hlive : ∀ p ∈ codeFoot i [b0, b1, b2, b3], live p.1)
    (hexec : ∀ σ : MState,
      (∀ q ∈ ks.map (fun k => (k, DFrac.own 1, R k)), gprGet σ q.1 = some q.2.2) →
      (execute ast).run (afterNextPC (afterPrelude σ) (BitVec.ofNat 64 i))
        = .ok RETIRE_SUCCESS (sigma3_alu σ (BitVec.ofNat 64 i) (gprReg rd) (gprRT rd val))) :
    AluStep live i (ks.map fun k => (k, DFrac.own 1, R k)) (codeFoot i [b0, b1, b2, b3]) rd val := by
  refine aluStep_of_obs hrd1 hrd31 (fun q hq => ?_) hlive (fun c hG hi hpc hRR hMR => ?_)
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
    exact hks k hk
  · obtain ⟨vm, hmi⟩ := hG.minstret
    have hi64 : (BitVec.ofNat 64 i).toNat = i := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by unfold tohostAddr at hhi; omega)
    obtain ⟨hb0, hb1, hb2, hb3⟩ := site_bytes i b0 b1 b2 b3 hMR
    obtain ⟨g1, g2, g3, g4, g5⟩ := gpr_rd_ok rd (by omega) hrd1
    obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
      stepObs_exec (u := c.steps) (BitVec.addInt (BitVec.ofNat 64 i) 4) vm
        (Fetched.of_bytes hG hpc
          (by rw [hi64]; exact hb0) (by rw [hi64]; exact hb1) (by rw [hi64]; exact hb2)
          (by rw [hi64]; exact hb3) (by rw [hi64]; exact hlo) (by rw [hi64]; exact hhi)
          (by rw [hi64]; exact hal) hrvc hword
          (Vsa.Sim.decodeW (afterPrelude c.σ)
            (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
            (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
            (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg) (hdec _)))
        (hexec c.σ hRR)
        ⟨by reg_reads [g4, hG.hart_state], by reg_reads [g1], by reg_reads [g2], by reg_reads [g3, hmi]⟩
        ((hG.prelude _).insert_nonpinned g5 _) hi
    exact ⟨σ', i', vm, hs, hi', hG', hmem, hobs⟩

/-- `sltu rd, rs1, rs2`. -/
theorem aluStep_sltu (rs1 rs2 : Nat)
    (hrd1 : 1 ≤ rd) (hrd31 : rd ≤ 31) (h1 : rs1 ≤ 31) (h2 : rs2 ≤ 31) (hks : KeysOK ks)
    (hk1 : rs1 = 0 ∨ rs1 ∈ ks) (hk2 : rs2 = 0 ∨ rs2 ∈ ks)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : ∀ σ, decodeN w σ =
      .ok (instruction.RTYPE (gprIdx rs2, gprIdx rs1, gprIdx rd, rop.SLTU)) σ)
    (hlo : 0x80000000 ≤ i) (hhi : i + 4 ≤ tohostAddr) (hal : i % 4 = 0)
    (hlive : ∀ p ∈ codeFoot i [b0, b1, b2, b3], live p.1) :
    AluStep live i (ks.map fun k => (k, DFrac.own 1, R k)) (codeFoot i [b0, b1, b2, b3]) rd
      (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (srcO R rs1) (srcO R rs2)))) :=
  aluStep_site i w b0 b1 b2 b3 rd R ks _ _ hrd1 hrd31 hks hword hrvc hdec hlo hhi hal hlive
    (fun σ hRR =>
      execute_rtype_sltu_char (gprIdx rs2) (gprIdx rs1) (gprIdx rd) (srcO R rs1) (srcO R rs2) _ _
        (rX_src σ _ rs1 h1 _ (srcPin_of_pins hRR rs1 hk1))
        (rX_src σ _ rs2 h2 _ (srcPin_of_pins hRR rs2 hk2))
        (wX_gpr _ _ rd hrd1 hrd31))

/-- `sltiu rd, rs1, imm`. -/
theorem aluStep_sltiu (rs1 : Nat) (imm : BitVec 12)
    (hrd1 : 1 ≤ rd) (hrd31 : rd ≤ 31) (h1 : rs1 ≤ 31) (hks : KeysOK ks)
    (hk1 : rs1 = 0 ∨ rs1 ∈ ks)
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : ∀ σ, decodeN w σ = .ok (instruction.ITYPE (imm, gprIdx rs1, gprIdx rd, iop.SLTIU)) σ)
    (hlo : 0x80000000 ≤ i) (hhi : i + 4 ≤ tohostAddr) (hal : i % 4 = 0)
    (hlive : ∀ p ∈ codeFoot i [b0, b1, b2, b3], live p.1) :
    AluStep live i (ks.map fun k => (k, DFrac.own 1, R k)) (codeFoot i [b0, b1, b2, b3]) rd
      (zero_extend (m := 64)
        (bool_to_bit (zopz0zI_u (srcO R rs1) (sign_extend (m := 64) imm)))) :=
  aluStep_site i w b0 b1 b2 b3 rd R ks _ _ hrd1 hrd31 hks hword hrvc hdec hlo hhi hal hlive
    (fun σ hRR =>
      execute_itype_sltiu_char imm (gprIdx rs1) (gprIdx rd) (srcO R rs1) _ _
        (rX_src σ _ rs1 h1 _ (srcPin_of_pins hRR rs1 hk1))
        (wX_gpr _ _ rd hrd1 hrd31))

end site

end VsaIris.Sym
