import Vsa.Sim.DivLoops
import Vsa.Sim.DivSites2

/-!
# Layer 3 — total-correctness specs for the signed/remainder division wrappers

Config-level composition of the wrapper site steps (`Vsa/Sim/DivSites2.lean`)
around the shared unsigned core `udivdi3_spec` (`Vsa/Sim/DivLoops.lean`) into
total-correctness triples for the three libgcc wrapper entries:

* `umoddi3_spec` (`__umoddi3`, entry `0x800046f4`): unsigned remainder.
* `moddi3_spec`  (`__moddi3`,  entry `0x80004728`): signed remainder.
* `divdi3_spec`  (`__divdi3`,  entry `0x800046a4`): signed quotient.

## Threading the core call

The wrappers save the return address in `t0`/`x5` and call the unsigned core via
`jal`, returning through `jr t0`. Preservation of `x5` (and every other
non-clobbered register) across the core is recovered through the blanket
ghost-frame conjunct now carried by `Ust`/`udivdi3_post` (`DivSpec.lean`): at the
`jal`-successor state `cent`, we instantiate the core's ghost `g` with
`cent.σ.regs.get?` (so the entry frame `hframe` is `rfl`), and `udivdi3_post` then
returns `∀ R, NotWritten R → cent'.σ.regs.get? R = cent.σ.regs.get? R`; specialised
at `x5` this recovers the saved return address after the core runs.

## `divdi3` control-flow map (from `experiments/disasm.txt`)

```
46a4 bltz a0 → 4704            ; a0 < 0 ?
46a8 bltz a1 → 4714            ; a1 < 0 ?
46ac …core…  (a0≥0, a1≥0) ; core returns via ret/x1 straight to divdi3's caller
                            ; (no result fixup — quotient already correct sign)
--- a0 < 0 arm (from 4704) ---
4704 neg a0,a0                ; a0 := -a0
4708 bgtz a1 → 4718           ; a1 > 0 ? (mixed signs) → save-ra path
470c neg a1,a1                ; a1 ≤ 0 : both negative → negate a1 too
4710 j 46ac                   ; tail-call core (returns via ret/x1; quotient +)
--- a1 < 0 arm (from 4714), also fall-through target of the mixed path ---
4714 neg a1,a1                ; a1 := -a1
4718 mv t0,ra                 ; save ra (mixed signs: result must be negated)
471c jal 46ac                 ; call core, ra := 4720
4720 neg a0,a0                ; a0 := -quotient
4724 jr t0                    ; return
```

So `divdi3` has TWO ways into the core: (a) fall-through / `j` at `4710`
(same-sign, core returns straight via `x1 = ` original caller `ra`, no fixup);
(b) `jal` at `471c` (mixed sign, `t0 = ra`, negate result, `jr t0`). This is why
`divdi3` does not uniformly use `jal`: the same-sign paths reuse the caller's
return slot directly.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `__umoddi3` — unsigned remainder (entry `0x800046f4`)

```
f4 mv t0,ra   ; t0 := r
f8 jal 46ac   ; call unsigned core; ra := fc
fc mv a0,a1   ; a0 := a1 = n % d
00 jr t0      ; return to r
```

`umoddi3_pre`: at `0x800046f4` with `x10 = n`, `x11 = d`, `x1 = r`, `mem = m0`,
`d ≠ 0`, `r` 4-aligned, and BOTH the wrapper (`__umoddi3Loaded`) and core
(`__hidden___udivdi3Loaded`) regions loaded. -/
def umoddi3_pre (n d r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ Vsa.Sim.Code.__umoddi3Loaded c.σ.mem ∧ __hidden___udivdi3Loaded c.σ.mem ∧
  c.σ.mem = m0 ∧ c.σ.regs.get? Register.PC = some (0x800046f4#64) ∧
  c.σ.regs.get? Register.x10 = some n ∧ c.σ.regs.get? Register.x11 = some d ∧
  c.σ.regs.get? Register.x1 = some r ∧ (∃ v, c.σ.regs.get? Register.minstret = some v) ∧
  (∃ v, c.σ.regs.get? Register.x12 = some v) ∧ (∃ v, c.σ.regs.get? Register.x13 = some v) ∧
  c.tick < 2 ∧ 0 < d.toNat ∧ r.toNat % 4 = 0

/-- `umoddi3_post`: PC back at the return address `r`, `x10 = n % d` (unsigned),
`GoodState` preserved, memory unchanged. Note `x1`/`ra` is CLOBBERED by the
internal `jal` (the wrapper returns via `t0`, per the RISC-V calling convention
where `ra` is caller-saved). -/
def umoddi3_post (n d r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧ c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x10 = some (n % d)

/-- `t0 := ra` folds `r + sext 0 = r`. -/
private theorem addi0 (v : BitVec 64) : v + sign_extend (m := 64) (0x000#12) = v := by
  rw [sext_zero]; exact BitVec.add_zero v

/-- **`umoddi3_spec`** — total-correctness triple for libgcc `__umoddi3`
(unsigned 64-bit remainder). Saves `ra` in `t0`, calls the unsigned core, moves
the remainder into `a0`, and returns via `t0`. The `t0`/`x5` return address is
preserved across the core through the blanket ghost-frame conjunct. -/
theorem umoddi3_spec (n d r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (umoddi3_pre n d r m0) (umoddi3_post n d r m0) := by
  intro c hc
  obtain ⟨hG, huload, hcload, hmem, hpc, hn, hd, hr, ⟨vmi, hmi⟩,
    ⟨v12, h12⟩, ⟨v13, h13⟩, htick, hdpos, halign⟩ := hc
  -- Step f4: mv t0,ra ⇒ x5 := r
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site2_800046f4 c.σ c.tick c.steps (0x800046f4#64) vmi r hG hpc hmi hr
      (hmem ▸ huload) rfl htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1  : σ1.regs.get? Register.PC = some (0x800046f8#64) := obs_alu_pc hobs1
  have hx5_1 : σ1.regs.get? Register.x5 = some r := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addi0 r] at this
  have hx10_1 : σ1.regs.get? Register.x10 = some n :=
    obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hn
  have hx11_1 : σ1.regs.get? Register.x11 = some d :=
    obs_alu_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd
  have hx12_1 : σ1.regs.get? Register.x12 = some v12 :=
    obs_alu_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h12
  have hx13_1 : σ1.regs.get? Register.x13 = some v13 :=
    obs_alu_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h13
  obtain ⟨vmi1, hmi1v⟩ := obs_alu_minstret hobs1
  have hmemq1 : σ1.mem = m0 := by rw [hmem1]; exact hmem
  -- Step f8: jal core ⇒ x1 := fc, PC := 46ac
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site2_800046f8 σ1 i1 (c.steps + 1) (0x800046f8#64) vmi1 hG1 hpc1 hmi1v
      (hmem1 ▸ hmem ▸ huload) rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x800046ac#64) := by
    have := obs_jal_pc hobs2
    rwa [show (0x800046f8#64 : BitVec 64) + sign_extend (m := 64) (0x1fffb4#21)
        = (0x800046ac#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx1_2 : σ2.regs.get? Register.x1 = some (0x800046fc#64) := by
    have := obs_jal_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x800046f8#64 : BitVec 64) 4 = (0x800046fc#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx10_2 : σ2.regs.get? Register.x10 = some n :=
    obs_jal_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_1
  have hx11_2 : σ2.regs.get? Register.x11 = some d :=
    obs_jal_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_1
  have hx12_2 : σ2.regs.get? Register.x12 = some v12 :=
    obs_jal_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_1
  have hx13_2 : σ2.regs.get? Register.x13 = some v13 :=
    obs_jal_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_1
  have hx5_2 : σ2.regs.get? Register.x5 = some r :=
    obs_jal_other hobs2 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_1
  have hmi2 : ∃ v, σ2.regs.get? Register.minstret = some v := obs_jal_minstret hobs2
  have hmemq2 : σ2.mem = m0 := by rw [hmem2]; exact hmemq1
  -- core entry config: instantiate the ghost with the entry state's own reads,
  -- so the entry `hframe` is `rfl` and `udivdi3_post` returns preservation of x5.
  have hcorepre : udivdi3_pre (fun R => σ2.regs.get? R) n d (0x800046fc#64) m0 σ2.sailOutput ⟨σ2, i2, c.steps + 1 + 1⟩ := by
    refine ⟨⟨v12, v13, ?_⟩, hdpos, by decide⟩
    exact {
      good := hG2, loaded := by rw [hmemq2]; exact hmem ▸ hcload, mem := hmemq2,
      sailOut := rfl,
      pc := hpc2, a0 := hx10_2, a1 := hx11_2, a2 := hx12_2, a3 := hx13_2,
      ra := hx1_2, minstret := hmi2, tick := hi2,
      hframe := fun R _ => rfl }
  obtain ⟨c3, hs3, hG3, hmem3, _hout3, hpc3, _hq3, hrem3, _hra3, htick3, hframe3, _hx12_3, _hx13_3⟩ :=
    udivdi3_spec (fun R => σ2.regs.get? R) n d (0x800046fc#64) m0 σ2.sailOutput ⟨σ2, i2, c.steps + 1 + 1⟩ hcorepre
  -- x5 preserved across core: NotWritten x5 ⇒ get? x5 = σ2.regs.get? x5 = r
  have hx5_3 : c3.σ.regs.get? Register.x5 = some r := by
    rw [hframe3 Register.x5 (by decide)]; exact hx5_2
  have huload3 : Vsa.Sim.Code.__umoddi3Loaded c3.σ.mem := hmem3 ▸ hmem ▸ huload
  obtain ⟨vmi3, hmi3⟩ := hG3.minstret
  -- Step fc: mv a0,a1 ⇒ x10 := x11 = n % d
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site2_800046fc c3.σ c3.tick c3.steps (0x800046fc#64) vmi3 (n % d) hG3 hpc3 hmi3 hrem3
      huload3 rfl htick3
  have hstep4 : Step c3 ⟨σ4, i4, c3.steps + 1⟩ := by cases c3; exact hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x80004700#64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x800046fc#64 : BitVec 64) 4 = (0x80004700#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx10_4 : σ4.regs.get? Register.x10 = some (n % d) := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addi0 (n % d)] at this
  have hx5_4 : σ4.regs.get? Register.x5 = some r :=
    obs_alu_other hobs4 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hmemq4 : σ4.mem = m0 := by rw [hmem4]; exact hmem3
  have huload4 : Vsa.Sim.Code.__umoddi3Loaded σ4.mem := hmemq4 ▸ hmem ▸ huload
  -- Step 4700: jr t0 ⇒ PC := r
  have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt r halign]; exact halign
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site2_80004700 σ4 i4 (c3.steps + 1) (0x80004700#64) vmi4 r hG4 hpc4 hmi4 hx5_4
      huload4 rfl htgt hi4
  have hstep5 : Step ⟨σ4, i4, c3.steps + 1⟩ ⟨σ5, i5, c3.steps + 1 + 1⟩ := hs5
  refine ⟨⟨σ5, i5, c3.steps + 1 + 1⟩, ?_, hG5, ?_, ?_, ?_⟩
  · -- assemble the full run
    exact (Steps.single hstep1).trans ((Steps.single hstep2).trans
      (hs3.trans ((Steps.single hstep4).trans ((Steps.single hstep5).trans (.refl _)))))
  · rw [hmem5]; exact hmemq4
  · -- PC = r
    rw [obs_jr_pc hobs5, ret_tgt r halign]
  · -- x10 = n % d (preserved through jr)
    exact obs_jr_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_4

end Vsa.Sim
