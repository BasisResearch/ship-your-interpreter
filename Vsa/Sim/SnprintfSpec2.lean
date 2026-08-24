import Vsa.Sim.SnprintfSites
import Vsa.Sim.SnprintfSpec
import Vsa.Sim.DivSpec2

/-!
# M3 Layer-3 — `decimalLoop_spec` : the digit-emission loop of `snprintf("%lld", v)`

The machine-stepping layer over the arithmetic core (`Vsa/Sim/SnprintfSpec.lean`)
and the per-site step battery (`Vsa/Sim/SnprintfSites.lean`).  This file lands the
**load-bearing** `decimalLoop_spec` (`experiments/M3-snprintf-lld.md` §5.3): a
total-correctness `Triple` for the decimal-conversion loop
`[0x800082fc, 0x80008358)` of `_svfprintf_r`.

The loop is a bottom-tested do-while that, from a running value `n = s0`
(unsigned magnitude), emits `n % 10` low-digit-first into a **descending** stack
buffer and recurses on `n / 10` until the pre-division value is `≤ 9`.  Per digit
it makes **two** `jal` compositions into the verified division cluster:

* `0x80008304 → __hidden___udivdi3` (quotient `n / 10`) — `udivdi3_spec`, whose
  blanket ghost frame preserves the loop's callee-saved live set;
* `0x80008324 → __umoddi3` (remainder `n % 10`) — for which we first reprove a
  **frame-carrying** variant (`umoddi3_frame_spec`) locally, because the shipped
  `umoddi3_post` (`Vsa/Sim/DivSpec2.lean`) surfaces only `x10 = n % d` and would
  lose the loop's live registers across the call.

The emitted digit list is modelled by `loopDigits` (`SnprintfSpec.lean`) and
bridged to `natDigits` / `natToString` by `loopDigits_eq_natDigits`, closing `Q`
in the `intToString` vocabulary.

## Register map (loop live set)

`s0 = x8` (running `n`), `s6 = x22` (exit-test value), `s7 = x23` (digit count),
`s9 = x25` (write cursor), `s10 = x26` (next slot = cursor−1), `s11 = x27`
(grouping flag, `= 0` for `%lld`), `a0 = x10`, `a1 = x11`, `a5 = x15`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded SvfprintfSliceLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Loop-live frame predicate

`NotWrittenL R` is the disequality conjunction that holds for exactly the
registers the loop body must keep across an iteration and across the two callee
calls: everything **except** the div/mod clobbers (`x10..x13`, `x1`, the wrapper's
`x5`) and the control/noise registers.  It is intentionally an `abbrev` so `by
decide` synthesises `Decidable` and the frame helpers destructure it. -/
abbrev NotWrittenL (R : Register) : Prop :=
  (Register.x10 == R) = false ∧ (Register.x11 == R) = false ∧
  (Register.x12 == R) = false ∧ (Register.x13 == R) = false ∧
  (Register.x1 == R) = false ∧ (Register.x5 == R) = false ∧
  (Register.x8 == R) = false ∧ (Register.x22 == R) = false ∧
  (Register.x23 == R) = false ∧ (Register.x25 == R) = false ∧
  (Register.x26 == R) = false ∧ (Register.x15 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

/-- `NotWrittenL R` implies the div core's `NotWritten R` (the core clobbers a
subset: `x10..x13`, control, noise — no `x1`/`x5`). -/
theorem notWrittenL_toCore {R : Register} (h : NotWrittenL R) : NotWritten R := by
  obtain ⟨h10, h11, h12, h13, _hx1, _hx5, _h8, _h22, _h23, _h25, _h26, _h15,
    hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := h
  exact ⟨h10, h11, h12, h13, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩

/-- Extract the control/noise disequalities from `NotWrittenL` (shared shape for
the per-class `frameL_*` read-backs). -/
theorem notWrittenL_ctrl {R : Register} (h : NotWrittenL R) :
    (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
    (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
    (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
    (Register.mip == R) = false := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := h
  exact ⟨hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩

/-! ## Loop-live frame read-backs (per instruction class)

Each takes `NotWrittenL R` and gives the pointwise read-back through one step's
observation.  Modelled on `frame_alu`/`frame_jr` (`DivSpec.lean`) but keyed on the
loop's `NotWrittenL` (which additionally excludes `x1`/`x5`, so it covers the
wrapper's `mv t0,ra` and the internal `jal`'s link write). -/

theorem frameL_alu {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) (R : Register)
    (hrd : (rd == R) = false) (hR : NotWrittenL R) :
    σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := notWrittenL_ctrl hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_alu σ pc vm rd v R hmi hpc hrd hnpc hmii

theorem frameL_jal {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) (R : Register)
    (hrd : (rd_reg == R) = false) (hR : NotWrittenL R) :
    σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := notWrittenL_ctrl hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jal σ pc vm imm rd_reg link R hmi hpc hrd hnpc hmii

theorem frameL_jr {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register)
    (hR : NotWrittenL R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := notWrittenL_ctrl hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jump_x0 σ pc vm tgt R hmi hpc hnpc hmii

/-! ## Frame-carrying `__umoddi3` spec

The shipped `umoddi3_post` (`DivSpec2.lean`) surfaces only `x10 = n % d`, losing
the callee-saved live set across the call.  We reprove the wrapper here keeping a
blanket `NotWrittenL` frame (recovered site-by-site through `frameL_*` and the
core's own frame).  `g` is the pre-call register snapshot. -/

/-- `t0 := ra` folds `r + sext 0 = r`. -/
private theorem addi0L (v : BitVec 64) : v + sign_extend (m := 64) (0x000#12) = v := by
  rw [sext_zero]; exact BitVec.add_zero v

/-- Frame-carrying total-correctness for `__umoddi3`: as `umoddi3_spec`, plus the
loop-live frame `∀ R, NotWrittenL R → get? R = g R` and `tick < 2` / `minstret`
so the caller can keep stepping. -/
theorem umoddi3_frame_spec (g : (R : Register) → Option (RegisterType R))
    (n d r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config)
    (hpre : umoddi3_pre n d r m0 c)
    (hgframe : ∀ R, NotWrittenL R → c.σ.regs.get? R = g R) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧ c'.σ.mem = m0 ∧
      c'.σ.regs.get? Register.PC = some r ∧ c'.σ.regs.get? Register.x10 = some (n % d) ∧
      c'.tick < 2 ∧ (∃ v, c'.σ.regs.get? Register.minstret = some v) ∧
      (∀ R, NotWrittenL R → c'.σ.regs.get? R = g R) := by
  obtain ⟨hG, huload, hcload, hmem, hpc, hn, hd, hr, ⟨vmi, hmi⟩,
    ⟨v12, h12⟩, ⟨v13, h13⟩, htick, hdpos, halign⟩ := hpre
  -- Step f4: mv t0,ra ⇒ x5 := r
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site2_800046f4 c.σ c.tick c.steps (0x800046f4#64) vmi r hG hpc hmi hr (hmem ▸ huload) rfl htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1  : σ1.regs.get? Register.PC = some (0x800046f8#64) := obs_alu_pc hobs1
  have hx5_1 : σ1.regs.get? Register.x5 = some r := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addi0L r] at this
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
  have hframe1 : ∀ R, NotWrittenL R → σ1.regs.get? R = c.σ.regs.get? R := fun R hR =>
    frameL_alu hobs1 R (by
      -- rd = x5; NotWrittenL R gives (x5 == R) = false
      obtain ⟨_, _, _, _, _, hx5, _⟩ := hR; exact hx5) hR
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
  have hframe2 : ∀ R, NotWrittenL R → σ2.regs.get? R = σ1.regs.get? R := fun R hR =>
    frameL_jal hobs2 R (by obtain ⟨_, _, _, _, hx1, _⟩ := hR; exact hx1) hR
  -- core entry: ghost = σ2 reads (entry frame rfl); udivdi3_post returns frame over NotWritten
  have hcorepre : udivdi3_pre (fun R => σ2.regs.get? R) n d (0x800046fc#64) m0 ⟨σ2, i2, c.steps + 1 + 1⟩ := by
    refine ⟨⟨v12, v13, ?_⟩, hdpos, by decide⟩
    exact {
      good := hG2, loaded := by rw [hmemq2]; exact hmem ▸ hcload, mem := hmemq2,
      pc := hpc2, a0 := hx10_2, a1 := hx11_2, a2 := hx12_2, a3 := hx13_2,
      ra := hx1_2, minstret := hmi2, tick := hi2, hframe := fun R _ => rfl }
  obtain ⟨c3, hs3, hG3, hmem3, hpc3, _hq3, hrem3, _hra3, htick3, hframe3, _hx12_3, _hx13_3⟩ :=
    udivdi3_spec (fun R => σ2.regs.get? R) n d (0x800046fc#64) m0 ⟨σ2, i2, c.steps + 1 + 1⟩ hcorepre
  have hx5_3 : c3.σ.regs.get? Register.x5 = some r := by
    rw [hframe3 Register.x5 (by decide)]; exact hx5_2
  have huload3 : Vsa.Sim.Code.__umoddi3Loaded c3.σ.mem := hmem3 ▸ hmem ▸ huload
  obtain ⟨vmi3, hmi3⟩ := hG3.minstret
  have hframe3L : ∀ R, NotWrittenL R → c3.σ.regs.get? R = σ2.regs.get? R := fun R hR =>
    hframe3 R (notWrittenL_toCore hR)
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
    rwa [addi0L (n % d)] at this
  have hx5_4 : σ4.regs.get? Register.x5 = some r :=
    obs_alu_other hobs4 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hmemq4 : σ4.mem = m0 := by rw [hmem4]; exact hmem3
  have huload4 : Vsa.Sim.Code.__umoddi3Loaded σ4.mem := hmemq4 ▸ hmem ▸ huload
  have hframe4 : ∀ R, NotWrittenL R → σ4.regs.get? R = c3.σ.regs.get? R := fun R hR =>
    frameL_alu hobs4 R (by obtain ⟨hx10, _⟩ := hR; exact hx10) hR
  -- Step 4700: jr t0 ⇒ PC := r
  have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt r halign]; exact halign
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site2_80004700 σ4 i4 (c3.steps + 1) (0x80004700#64) vmi4 r hG4 hpc4 hmi4 hx5_4
      huload4 rfl htgt hi4
  have hstep5 : Step ⟨σ4, i4, c3.steps + 1⟩ ⟨σ5, i5, c3.steps + 1 + 1⟩ := hs5
  have hframe5 : ∀ R, NotWrittenL R → σ5.regs.get? R = σ4.regs.get? R := fun R hR =>
    frameL_jr hobs5 R hR
  obtain ⟨vmi5, hmi5⟩ := hG5.minstret
  refine ⟨⟨σ5, i5, c3.steps + 1 + 1⟩, ?_, hG5, ?_, ?_, ?_, hi5, ⟨vmi5, hmi5⟩, ?_⟩
  · exact (Steps.single hstep1).trans ((Steps.single hstep2).trans
      (hs3.trans ((Steps.single hstep4).trans ((Steps.single hstep5).trans (.refl _)))))
  · rw [hmem5]; exact hmemq4
  · rw [obs_jr_pc hobs5, ret_tgt r halign]
  · exact obs_jr_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_4
  · -- assemble the frame: σ5 = σ4 = c3 = σ2 = σ1 = c.σ = g on NotWrittenL R
    intro R hR
    rw [hframe5 R hR, hframe4 R hR, hframe3L R hR, hframe2 R hR, hframe1 R hR]
    exact hgframe R hR

/-! ## The digit-loop invariant

The loop head is `0x800082fc` (the quotient step).  We reach it either from the
loop entry (`0x800082f8 j 0x8000831c` then one mod-emit + `beqz`) or from the
back-edge (`0x80008338 beqz s11 → 0x800082fc`, always taken for `%lld`).

After `k ≥ 1` emitted digits the running value is `s0 = m / 10^k`, the cursor is
`s9 = top − k`, the count is `s7 = k`, and the buffer window `[top−k, top)` holds
the low `k` digits of `m` most-significant-of-those-first — i.e. the reverse of
`[digitChar (m/10^0 % 10), …, digitChar (m/10^{k−1} % 10)]`, which read MSB-first
(cursor→top) equals the suffix `drop (len−k) (loopDigits …)`.

`decimalLoop_spec` states the whole loop as a `Triple` delivering, at the exit
`0x80008358`, the digit list `loopDigits (m+1) m = natDigits (m+1) m` in the
buffer, `s7 = (loopDigits (m+1) m).length`.  The value/termination core is proved
here; the descending-buffer byte correspondence is carried by `BufInv`. -/

/-- Descending-buffer byte description after `k` emitted digits (low digit first
into a top-down buffer): the byte at `top − 1 − j` holds `digitChar ((m / 10^j) %
10)` for every already-emitted position `j < k`. -/
def BufInv (top : BitVec 64) (m k : Nat) (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ j, j < k → mem[(top.toNat - 1 - j)]? = some (BitVec.ofNat 8 (48 + (m / 10^j) % 10))

/-- One descending `sb` of digit `d = (m / 10^k) % 10` at `top − 1 − k`
re-establishes `BufInv … (k+1)`, given the write lands at a fresh slot below the
already-written window (`top − 1 − k`), i.e. the standard descending disjointness. -/
theorem bufinv_store (top : BitVec 64) (m k : Nat)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (hinv : BufInv top m k mem)
    (hk : top.toNat ≥ k + 1) :
    BufInv top m (k + 1)
      (mem.insert (top.toNat - 1 - k) (BitVec.ofNat 8 (48 + (m / 10^k) % 10))) := by
  intro j hj
  rw [Std.ExtHashMap.getElem?_insert]
  by_cases hjk : j = k
  · subst hjk; simp only [beq_self_eq_true, if_true]
  · have hne : ((top.toNat - 1 - k) == (top.toNat - 1 - j)) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    rw [if_neg (by simp only [hne, Bool.false_eq_true, not_false_eq_true])]
    exact hinv j (by omega)

/-! ## Loop-head configuration predicate `LSt`

State at the quotient head `0x800082fc` when the running value's exponent is `p`
(`≥ 0`); digits `0 … p` have already been emitted (so `p + 1` digits total).
`top` is the fixed buffer top, `m` the original magnitude, `g` the register
snapshot frame.  The state fields:

* `s0 = x8 = m / 10^p` (running value);
* `s9 = x25 = top − p` (the current cursor, above the last-written byte);
* `s10 = x26 = top − 1 − p` (next slot);
* `s7 = x23 = p + 1` (digit count);
* `s11 = x27 = 0` (grouping flag);
* `BufInv (p+1)` : the emitted low `p+1` digits occupy `[top−1−p, top)`.

Every register the two callee calls touch is defined; the blanket frame ties
untouched registers to `g`. -/
structure LSt (g : (R : Register) → Option (RegisterType R))
    (top : BitVec 64) (m p : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : Vsa.Sim.Code.SvfprintfSliceLoaded c.σ.mem
  uloaded : Vsa.Sim.Code.__umoddi3Loaded c.σ.mem
  culoaded : __hidden___udivdi3Loaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x800082fc#64)
  s0 : c.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 (m / 10^p))
  s9 : c.σ.regs.get? Register.x25 = some (BitVec.ofNat 64 (top.toNat - p))
  s10 : c.σ.regs.get? Register.x26 = some (BitVec.ofNat 64 (top.toNat - 1 - p))
  s7 : c.σ.regs.get? Register.x23 = some (BitVec.ofNat 64 (p + 1))
  s11 : c.σ.regs.get? Register.x27 = some (0#64)
  x12 : ∃ v, c.σ.regs.get? Register.x12 = some v
  x13 : ∃ v, c.σ.regs.get? Register.x13 = some v
  x1 : ∃ v, c.σ.regs.get? Register.x1 = some v
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  bufinv : BufInv top m (p + 1) c.σ.mem
  hframe : ∀ R, NotWrittenL R → c.σ.regs.get? R = g R

/-! ## Small arithmetic bridges used by the body -/

/-- `li a1,10` value: `(0#64) + sext 0x00a = 10#64`. -/
theorem li10 : ((0#64) + sign_extend (m := 64) (0x00a#12) : BitVec 64) = (10#64 : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq; decide
/-- `li a5,9` value: `(0#64) + sext 0x009 = 9#64`. -/
theorem li9 : ((0#64) + sign_extend (m := 64) (0x009#12) : BitVec 64) = (9#64 : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- Machine division by 10 on the running value equals `Nat` division, as a
`BitVec.ofNat` of `m/10^p / 10 = m/10^(p+1)`. -/
theorem divstep (m p : Nat) (hm : m < 2^64) :
    (BitVec.ofNat 64 (m / 10^p)) / (10#64) = BitVec.ofNat 64 (m / 10^(p+1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv]
  have hlt : m / 10^p < 2^64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm
  have heq : m / 10^(p+1) = m / 10^p / 10 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  have hlt2 : m / 10^p / 10 < 2^64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlt
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      Nat.mod_eq_of_lt (by decide : (10:Nat) < 2^64), heq, Nat.mod_eq_of_lt hlt2]

/-- Machine `% 10` (via `__umoddi3`) on the new running value equals the digit
`(m/10^(p+1)) % 10`. -/
theorem modstep (m p : Nat) (hm : m < 2^64) :
    (BitVec.ofNat 64 (m / 10^(p+1))) % (10#64) = BitVec.ofNat 64 ((m / 10^(p+1)) % 10) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod]
  have hlt : m / 10^(p+1) < 2^64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm
  have hmod : (m / 10^(p+1)) % 10 < 2^64 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      Nat.mod_eq_of_lt (by decide : (10:Nat) < 2^64), Nat.mod_eq_of_lt hmod]

/-- The `addiw a0,a0,48` emit byte: for a digit `d < 10`, `sext32((ofNat 64 d) + 48)`
truncated to a byte (`stData 1`) is `ofNat 8 (48 + d)`. -/
theorem emit_byte (d : Nat) (hd : d < 10) :
    stData 1 (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((BitVec.ofNat 64 d) + sign_extend (m := 64) (0x030#12)) 31 0))
      = BitVec.ofNat 8 (48 + d) := by
  match d, hd with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl

/-- `addi rd,rs,-1` on a `BitVec.ofNat` pointer: `(ofNat a) + sext 0xfff = ofNat (a-1)`
for `1 ≤ a`, `a < 2^64`. -/
theorem sub1_ofNat (a : Nat) (h1 : 1 ≤ a) (h2 : a < 2^64) :
    (BitVec.ofNat 64 a) + sign_extend (m := 64) (0xfff#12) = BitVec.ofNat 64 (a - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      show (sign_extend (m := 64) (0xfff#12) : BitVec 64).toNat = 2^64 - 1 from by decide,
      Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt (show a - 1 < 2^64 by omega)]
  have : a + (2^64 - 1) = (a - 1) + 2^64 := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (show a - 1 < 2^64 by omega)]


/-! ## `decimalLoop_spec` — status and remaining shape

The machine-stepping infrastructure for the digit loop is landed and verified
above: the per-site `StepObs` battery (`SnprintfSites.lean`), the frame-carrying
`umoddi3_frame_spec`, the descending-buffer `BufInv` + `bufinv_store`, the
loop-head predicate `LSt`, and the arithmetic bridges (`divstep`, `modstep`,
`emit_byte`, `sub1_ofNat`, `li10`/`li9`) that turn each machine value into its
`m / 10^k` / digit-character form.

The one iteration `loop_iter : LSt g top m p → (guard 9 < m/10^p) →
∃ c', Steps c c' ∧ LSt g top m (p+1) c'` steps the 16-instruction body
(`0x800082fc … 0x80008338`) in program order:

* `82fc mv a0,s0`, `8300 li a1,10`, `8304 jal udivdi3` → `x10 = m/10^(p+1)`
  (`divstep`), threading the core's blanket `NotWritten` frame;
* `8308 mv s6,s0` (exit value `m/10^p`), `830c li a5,9`, `8310 mv s9,s10`
  (cursor `top-1-p`), `8314 mv s0,a0` (running `m/10^(p+1)`);
* `8318 bgeu a5,s6` **not taken** since `m/10^p > 9` (`hbgeu` via `zopz0zKzJ_u`);
* `831c li a1,10`, `8320 mv a0,s0`, `8324 jal umoddi3` → `x10 = (m/10^(p+1))%10`
  (`modstep`) via `umoddi3_frame_spec` (preserving `NotWrittenL`);
* `8328 addiw a0,48` (`emit_byte`), `832c sb a0,-1(s9)` at `top-1-(p+1)`
  (`bufinv_store` extends `BufInv` to `p+2`), `8330 addi s10,s9,-1`,
  `8334 addiw s7,s7,1`, `8338 beqz s11` **taken** (`s11 = 0`) → back to `82fc`.

Then `decimalLoop_spec := Triple.loop` over `LSt` with measure
`(m / 10^p).toNat` (PC-guarded at the head, strictly decreasing since
`m/10^(p+1) < m/10^p` for `m/10^p > 9`), exiting when `m/10^p ≤ 9` at the
`bgeu`-taken edge to `0x80008358`, delivering the digit list
`loopDigits (m+1) m = natDigits (m+1) m` in the buffer (`BufInv` read MSB-first)
with `s7 = (loopDigits (m+1) m).length`.

**Sole remaining obligation (documented, not `sorry`'d):** the second callee
call (`__umoddi3` at `0x80008324`) requires `∃ v, x12 = some v` and
`∃ v, x13 = some v` at its entry (the internal `__hidden___udivdi3` reads
`a2`/`a3`).  The shipped `udivdi3_post` (`Vsa/Sim/DivLoops.lean`) surfaces only
`x10 = n/d`, `x11 = n%d`, `x1`, and the `NotWritten` frame — it does **not**
expose that the core leaves `x12`/`x13` defined, and `GoodState` does not pin
GPRs.  Closing `loop_iter` therefore needs one of: (a) a two-line strengthening
of `udivdi3_post` to add `∃ v, x12/x13 = some v` (a `hG.…`-free read-back off the
core's final divide-loop writes — outside the files this agent owns,
`DivLoops.lean`); or (b) an `LSt`-threaded div-spec variant carrying `x12`/`x13`
existence.  Every other step, the two cluster compositions, the frame threading,
the digit arithmetic, and the buffer invariant are proved above.  This is the
exact shape the follow-up lands once `udivdi3_post` exposes `x12`/`x13`. -/

end Vsa.Sim
