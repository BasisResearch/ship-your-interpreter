import Vsa.Sim.EnvGetSpec3
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — `env_get` scan-loop per-iteration body (`hbody` discharge)

This session's deliverable (task 1 of the continuation): discharge the
per-iteration loop body `hbody` that `env_get_scan_spec` (`EnvGetSpec3`) takes as
a hypothesis, turning the scan-loop `Triple` into an UNCONDITIONAL result
`env_get_scan_spec'`.

The body runs, from the scan-test config (`ScanSt` at `0x80002c5c`) at index
`i < count`:

```
c5c beq s0,s2,cc4   -- NOT taken (i < count ⇒ ofNat i ≠ count)     → c60
c60 ld  a0,0(s1)    -- a0 := names[i] = ofNat qᵢ                     → c64
c64 mv  a1,s3       -- a1 := name                                    → c68
c68 jal strcmp      -- ra := c6c, PC := strcmp entry
    ‹strcmp callee› -- strcmp_full_spec : sign x10 = strcmpSpecSign  → c6c
c6c bnez a0,c54     -- TAKEN  (name ≠ query ⇒ x10 ≠ 0)               → c54  (MISS-iter)
                    -- NOT taken (name = query ⇒ x10 = 0)            → c70  (HIT-in-body)
c54 addi s0,s0,1    -- i := i+1                                      → c58
c58 addi s1,s1,8    -- names += 8                                    → c5c  (AtHead@i+1)
```

Everything the body needs is landed: the 8 site lemmas (`EnvGetSites2`), the
`strcmp_full_spec` callee (`StrcmpSpecW4`), the load↔pointer bridge and index
arithmetic (`EnvGetSpec3`), the equality bridges (`EnvDefSpec2`/`EnvDefSpec3`),
and the `ScanNames` per-binding carrier.  The `strcmp` cross-call is spliced with
the ghost-at-call-site pattern (`g_call := σ_call.regs.get?`, so the callee's
ABI-frame entry is `rfl`), exactly as `env_new_spec` splices `malloc`.

## What this file lands (verified, `sorry`/`axiom`/`native_decide`/`bv_decide`-free)

* `scan_iter` — the per-iteration `Steps` chain from `ScanSt`@c5c (i<count) to the
  disjunctive next config: `ScanSt`@c5c at i+1 with the first-match invariant
  extended (MISS), OR the HIT block `0x80002c70` (HIT-in-body).
* `env_get_scan_body` — `scan_iter` packaged as the `hbody` loop-body `Triple`.
* `env_get_scan_spec'` — `env_get_scan_spec` with `hbody` discharged: the
  UNCONDITIONAL scan-loop disjunctive `Triple`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (Store Value)
open Vsa.Alloc
open Vsa.Sim.Code (Env_getLoaded StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Local `jal` read-back consumers

`EnvGetSpec3`'s import closure (via `Muldi3Spec`/`StepJump`) has `readback` and
`get?_sigmaPost_jal`, but the DivSites2 `post_jal_*`/`obs_jal_*` read-back
consumers are outside it.  We re-derive the two we need (`PC`, `rd`) locally. -/

theorem post_jal_pc_eg4 (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg) :
    (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? Register.PC
      = some (pc + sign_extend (m := 64) imm) := by
  show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq,
    not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem post_jal_rd_eg4 (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg)
    (h1 : (Register.minstret == rd_reg) = false) (h2 : (Register.PC == rd_reg) = false) :
    (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? rd_reg = some link := by
  show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? rd_reg = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
  show (((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
    (pc + sign_extend (m := 64) imm)).insert rd_reg link).get? rd_reg = _
  rw [Std.ExtDHashMap.get?_insert_self]

theorem obs_jal_pc_eg4 {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) :
    σ'.regs.get? Register.PC = some (pc + sign_extend (m := 64) imm) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_jal_pc_eg4 σ pc vm imm rd_reg link)

theorem obs_jal_rd_eg4 {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link))
    (hmc : (Register.mcycle == rd_reg) = false) (hmt : (Register.mtime == rd_reg) = false)
    (hmi : (Register.mip == rd_reg) = false)
    (h1 : (Register.minstret == rd_reg) = false) (h2 : (Register.PC == rd_reg) = false) :
    σ'.regs.get? rd_reg = some link :=
  readback σ' _ hobs rd_reg hmc hmt hmi (post_jal_rd_eg4 σ pc vm imm rd_reg link h1 h2)

theorem obs_jal_other_eg4 {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h3 : (rd_reg == R) = false) (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi
    ((get?_sigmaPost_jal σ pc vm imm rd_reg link R h1 h2 h3 h4 h5).trans hσ)

theorem obs_jal_minstret_eg4 {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-- The `jal` blanket-frame step, specialised to `NotWrittenStrcmp` (so the
ghost tie survives the call).  `rd = x1`; the caller supplies `(x1 == R) = false`
from `NotWrittenStrcmp R`. -/
theorem sframe_jal_eg4 {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) (R : Register)
    (hrd : (rd_reg == R) = false) (hR : NotWrittenStrcmp R) :
    σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jal σ pc vm imm rd_reg link R hmi hpc hrd hnpc hmii

/-! ## The per-iteration body chain (`scan_iter`)

From a scan-test config (`ScanSt`@`0x80002c5c`) at index `i < count` with the
first-match invariant, one loop body runs to the disjunctive next config:

* MISS-iter: `ScanSt`@`0x80002c5c` at `i+1` with the first-match invariant
  extended to `i+1` (the slot-`i` name differed), OR
* HIT-in-body: the HIT block `0x80002c70` at index `i` with `f.vars[i].1 = nameStr`
  and the first-match invariant (the slot-`i` name matched).

The chain: `c5c`(beq not taken) → `c60`(load `names[i]=ofNat qᵢ`, via `scan_c60_load`)
→ `c64`(`mv a1,s3`) → `c68`(`jal strcmp`, ghost `g' := σ_call.regs.get?`) → `strcmp`
(`strcmp_full_spec`; pre from `ScanNames`) → `c6c`(`bnez a0`): TAKEN (x10≠0 ⇒ names
differ ⇒ MISS-iter after `c54`/`c58`), NOT taken (x10=0 ⇒ names equal ⇒ HIT-in-body). -/

/-- **The per-iteration body chain.** From `ScanSt`@`0x80002c5c` at `i < count`
with the first-match invariant, the machine runs one loop body to the disjunctive
next config: the scan-test at `i+1` (MISS, first-match extended) OR the HIT block
`0x80002c70` at `i` (HIT). -/
theorem scan_iter (g : (R : Register) → Option (RegisterType R))
    (env name out count pn r sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (c : Config)
    (hSt : ScanSt g scanTestPC env name out count pn r sp i f nameStr N φf φc m0 c)
    (hfm : ∀ j, (hj : j < f.vars.length) → j < i → f.vars[j].1 ≠ nameStr)
    (hilt : i < f.vars.length) (hr : r = (0x80002c6c#64 : BitVec 64)) :
    ∃ c', Steps c c' ∧
      ((∃ (g' : (R : Register) → Option (RegisterType R)),
          ScanSt g' scanTestPC env name out count pn r sp (i+1) f nameStr N φf φc m0 c' ∧
          ∀ j, (hj : j < f.vars.length) → j < i + 1 → f.vars[j].1 ≠ nameStr)
       ∨ (i < f.vars.length ∧ f.vars[i].1 = nameStr ∧
          (∀ j, (hj : j < f.vars.length) → j < i → f.vars[j].1 ≠ nameStr) ∧
          c'.σ.regs.get? Register.PC = some (0x80002c70#64 : BitVec 64) ∧ GoodState c'.σ)) := by
  -- abbreviations from the standing invariant
  have hcnt : count.toNat = f.vars.length := hSt.count_eq
  have hcntlt : f.vars.length < 2^64 := by rw [← hcnt]; exact count.isLt
  have hi_lt_cnt : (BitVec.ofNat 64 i).toNat < count.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hcnt]; exact hilt
  obtain ⟨vmi0, hmi0⟩ := hSt.minstret
  -- ============ c5c: beq s0,s2 NOT taken (i ≠ count) → c60 ============
  have hbeq : ((BitVec.ofNat 64 i) == count) = false := by
    have hc : count = BitVec.ofNat 64 f.vars.length := by
      apply BitVec.eq_of_toNat_eq
      rw [hcnt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcntlt]
    rw [hc]; exact beq_scan_nottaken i f.vars.length hilt hcntlt
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80002c5c_nottaken_eg2 c.σ c.tick c.steps scanTestPC vmi0 (BitVec.ofNat 64 i) count
      hSt.good hSt.pc hmi0 hSt.idx0 hSt.count2 hSt.loadedG rfl hbeq hSt.tick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002c60#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs1
    rwa [show BitVec.addInt scanTestPC 4 = (0x80002c60#64 : BitVec 64) from by decide] at this
  -- carry the scan live registers through the not-taken branch (all preserved)
  have bcarry : ∀ (R : Register) (w : RegisterType R),
      (Register.minstret == R) = false → (Register.PC == R) = false →
      (Register.nextPC == R) = false → (Register.minstret_increment == R) = false →
      (Register.mcycle == R) = false → (Register.mtime == R) = false →
      (Register.mip == R) = false → c.σ.regs.get? R = some w → σ1.regs.get? R = some w := by
    intro R w h1 h2 h4 h5 hmc hmt hmi hσ
    exact obs_bnottaken_other hobs1 R hmc hmt hmi h1 h2 h4 h5 hσ
  have he1 := bcarry Register.x20 env (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.env4
  have hn1 := bcarry Register.x19 name (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.name3
  have ho1 := bcarry Register.x21 out (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.out5
  have hcn1 := bcarry Register.x18 count (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.count2
  have hcur1 := bcarry Register.x9 (pn + BitVec.ofNat 64 (8 * i)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.cursor1
  have hidx1 := bcarry Register.x8 (BitVec.ofNat 64 i) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.idx0
  have hra1 := bcarry Register.x1 r (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra
  have hsp1 := bcarry Register.x2 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.sp2
  obtain ⟨vmi1, hmi1⟩ := obs_bnottaken_minstret hobs1
  have hmem1' : σ1.mem = m0 := by rw [hmem1]; exact hSt.mem
  have hloadedG_m0 : Env_getLoaded m0 := hSt.mem ▸ hSt.loadedG
  have hloadedS_m0 : StrcmpLoaded m0 := hSt.mem ▸ hSt.loadedS
  have hghost1 : ∀ R : Register, AbiPreserved R = true → σ1.regs.get? R = g R := by
    intro R hR
    have hnws : NotWrittenStrcmp R := notWrittenStrcmp_of_abiPreserved R hR
    rw [sframe_bnottaken hobs1 R hnws]; exact hSt.ghost R hR
  -- rebuild ScanSt at c60
  have hSt60 : ScanSt g (0x80002c60#64) env name out count pn r sp i f nameStr N φf φc m0
      ⟨σ1, i1, c.steps + 1⟩ :=
    { good := hG1, loadedG := by rw [hmem1']; exact hloadedG_m0, loadedS := by rw [hmem1']; exact hloadedS_m0,
      mem := hmem1', pc := hpc1, env4 := he1, name3 := hn1, out5 := ho1, count2 := hcn1,
      cursor1 := hcur1, idx0 := hidx1, ra := hra1, sp2 := hsp1, minstret := ⟨vmi1, hmi1⟩,
      tick := hi1, frame := hSt.frame, names := hSt.names, count_eq := hSt.count_eq, ile := hSt.ile,
      ghost := hghost1 }
  -- the slot-i name pointer from ScanNames
  obtain ⟨q, hq, hCSq⟩ := hSt.names.bindPtr i hilt
  -- ghost values of the saved registers (recovered after any AbiPreserved-frame step)
  have hg_x8 : g Register.x8 = some (BitVec.ofNat 64 i) := by rw [← hSt.ghost _ (by decide)]; exact hSt.idx0
  have hg_x9 : g Register.x9 = some (pn + BitVec.ofNat 64 (8 * i)) := by rw [← hSt.ghost _ (by decide)]; exact hSt.cursor1
  have hg_x18 : g Register.x18 = some count := by rw [← hSt.ghost _ (by decide)]; exact hSt.count2
  have hg_x19 : g Register.x19 = some name := by rw [← hSt.ghost _ (by decide)]; exact hSt.name3
  have hg_x20 : g Register.x20 = some env := by rw [← hSt.ghost _ (by decide)]; exact hSt.env4
  have hg_x21 : g Register.x21 = some out := by rw [← hSt.ghost _ (by decide)]; exact hSt.out5
  have hg_x2 : g Register.x2 = some sp := by rw [← hSt.ghost _ (by decide)]; exact hSt.sp2
  -- ============ c60: ld a0,0(s1) → x10 = ofNat q (via scan_c60_load) ============
  obtain ⟨c2, hstep2, hpc2, hx10_2, hn2, hra2, hmem2, hG2, htick2, hmi2, hghost2⟩ :=
    scan_c60_load g env name out count pn r sp i f nameStr N φf φc m0 ⟨σ1, i1, c.steps + 1⟩ q hSt60 hilt hq
  have hmem2' : c2.σ.mem = m0 := hmem2
  obtain ⟨vmi2, hmi2'⟩ := hmi2
  -- recover saved registers at c2 from the ghost tie
  have he2 : c2.σ.regs.get? Register.x20 = some env := by rw [hghost2 _ (by decide)]; exact hg_x20
  have ho2 : c2.σ.regs.get? Register.x21 = some out := by rw [hghost2 _ (by decide)]; exact hg_x21
  have hcn2 : c2.σ.regs.get? Register.x18 = some count := by rw [hghost2 _ (by decide)]; exact hg_x18
  have hcur2 : c2.σ.regs.get? Register.x9 = some (pn + BitVec.ofNat 64 (8 * i)) := by rw [hghost2 _ (by decide)]; exact hg_x9
  have hidx2 : c2.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 i) := by rw [hghost2 _ (by decide)]; exact hg_x8
  have hsp2 : c2.σ.regs.get? Register.x2 = some sp := by rw [hghost2 _ (by decide)]; exact hg_x2
  -- ============ c64: mv a1,s3 → x11 := x19 + sext 0 = name → c68 ============
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80002c64_eg2 c2.σ c2.tick c2.steps (0x80002c64#64) vmi2 name hG2 hpc2 hmi2' hn2 (by rw [hmem2']; exact hloadedG_m0) rfl htick2
  have hstep3 : Step c2 ⟨σ3, i3, c2.steps + 1⟩ := by cases c2; exact hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x80002c68#64 : BitVec 64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80002c64#64 : BitVec 64) 4 = (0x80002c68#64 : BitVec 64) from by decide] at this
  have hx11_3 : σ3.regs.get? Register.x11 = some name := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_zero, BitVec.add_zero] at this
  have hx10_3 := obs_alu_other' hobs3 Register.x10 (by decide) hx10_2
  have hra3 := obs_alu_other' hobs3 Register.x1 (by decide) hra2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hmem3' : σ3.mem = m0 := by rw [hmem3]; exact hmem2'
  -- ALU frame: AbiPreserved regs preserved (rd = x11, not AbiPreserved)
  have hghost3 : ∀ R : Register, AbiPreserved R = true → σ3.regs.get? R = g R := by
    intro R hR
    have hnws : NotWrittenStrcmp R := notWrittenStrcmp_of_abiPreserved R hR
    have hx11 : (Register.x11 == R) = false := hnws.2.2.2.2.1
    rw [(sframe_alu hobs3 R hx11 hnws)]; exact hghost2 R hR
  -- ============ c68: jal strcmp → ra := c6c, PC := strcmp entry ============
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80002c68_eg2 σ3 i3 (c2.steps + 1) (0x80002c68#64) vmi3 hG3 hpc3 hmi3 (by rw [hmem3']; exact hloadedG_m0) rfl (by decide) hi3
  have hstep4 : Step (⟨σ3, i3, c2.steps + 1⟩ : Config) ⟨σ4, i4, c2.steps + 1 + 1⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006ea0#64 : BitVec 64) := by
    have := obs_jal_pc_eg4 hobs4
    rwa [show (0x80002c68#64 : BitVec 64) + sign_extend (m := 64) (0x004238#21) = (0x80006ea0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hra4 : σ4.regs.get? Register.x1 = some (0x80002c6c#64 : BitVec 64) := by
    have := obs_jal_rd_eg4 hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80002c68#64 : BitVec 64) 4 = (0x80002c6c#64 : BitVec 64) from by decide] at this
  have hx10_4 := obs_jal_other_eg4 hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_3
  have hx11_4 := obs_jal_other_eg4 hobs4 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_3
  obtain ⟨vmi4, hmi4⟩ := obs_jal_minstret_eg4 hobs4
  have hmem4' : σ4.mem = m0 := by rw [hmem4]; exact hmem3'
  have hloadedS4 : StrcmpLoaded σ4.mem := by rw [hmem4']; exact hloadedS_m0
  have hloadedG4 : Env_getLoaded σ4.mem := by rw [hmem4']; exact hloadedG_m0
  -- jal frame (rd = x1) preserves AbiPreserved regs; ra is now c6c (x1 is NOT AbiPreserved)
  have hghost4 : ∀ R : Register, AbiPreserved R = true → σ4.regs.get? R = g R := by
    intro R hR
    have hnws : NotWrittenStrcmp R := notWrittenStrcmp_of_abiPreserved R hR
    have hx1 : (Register.x1 == R) = false := by
      rcases hb : (Register.x1 == R) with _ | _
      · rfl
      · rw [beq_iff_eq] at hb; rw [← hb] at hR; exact absurd hR (by decide)
    rw [(sframe_jal_eg4 hobs4 R hx1 hnws)]; exact hghost3 R hR
  -- ============ strcmp callee: strcmp_full_spec (pa = ofNat q, pb = name) ============
  -- q < 2^64 so (ofNat q).toNat = q, bridging ScanNames' region facts to strcmp_full_pre.
  have hqlt : q < 2^64 := read64_lt_eg4 m0 (pn.toNat + 8 * i) q hq
  have hqNat : (BitVec.ofNat 64 q).toNat = q := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqlt]
  -- the ghost at the call site: the ABI-frame entry is `rfl`.
  let g4 : (R : Register) → Option (RegisterType R) := fun R => σ4.regs.get? R
  have hStrPre : strcmp_full_pre g4 (BitVec.ofNat 64 q) name (0x80002c6c#64) (f.vars[i].1) nameStr m0
      σ4.sailOutput ⟨σ4, i4, c2.steps + 1 + 1⟩ := by
    refine ⟨hG4, hloadedS4, hmem4', rfl, hpc4, hx10_4, hx11_4, hra4, ⟨vmi4, hmi4⟩, hi4, by decide, ?_, ?_,
      hSt.names.maskPinned, ?_, ?_, ?_, ?_, ?_⟩
    · -- CString m0 (ofNat q).toNat (f.vars[i].1)
      rw [hqNat]; exact hCSq
    · -- CString m0 name.toNat nameStr
      exact hSt.names.nameCStr
    · -- byte region for pa
      rw [hqNat]; exact fun cs hcs => hSt.names.bindRegB i hilt q hq cs hcs
    · -- byte region for pb
      exact fun cs hcs => hSt.names.nameRegB cs hcs
    · -- word region for pa
      rw [hqNat]; exact fun cs hcs => hSt.names.bindRegW i hilt q hq cs hcs
    · -- word region for pb
      exact fun cs hcs => hSt.names.nameRegW cs hcs
    · -- frame: g4 R = σ4.get? R, so this is rfl
      intro R _; rfl
  obtain ⟨c5, hstepsStr, hStrPost⟩ :=
    strcmp_full_spec g4 (BitVec.ofNat 64 q) name (0x80002c6c#64) (f.vars[i].1) nameStr m0
      σ4.sailOutput ⟨σ4, i4, c2.steps + 1 + 1⟩ hStrPre
  obtain ⟨hG5, hpc5, hra5, hmem5, _hout5, htick5, hframe5,
    csa, csb, xres, hCSa, hCSb, hsaEq, hsbEq, hx10_5, hsign5⟩ := hStrPost
  -- recover saved registers at c5 through strcmp's frame ∘ hghost4 (AbiPreserved ⊆ NotWrittenStrcmp)
  have crecover : ∀ (R : Register) (w : RegisterType R), AbiPreserved R = true →
      g R = some w → c5.σ.regs.get? R = some w := by
    intro R w hR hgw
    have hnws : NotWrittenStrcmp R := notWrittenStrcmp_of_abiPreserved R hR
    rw [hframe5 R hnws]; show σ4.regs.get? R = some w; rw [hghost4 R hR]; exact hgw
  have he5 : c5.σ.regs.get? Register.x20 = some env := crecover _ _ (by decide) hg_x20
  have ho5 : c5.σ.regs.get? Register.x21 = some out := crecover _ _ (by decide) hg_x21
  have hcn5 : c5.σ.regs.get? Register.x18 = some count := crecover _ _ (by decide) hg_x18
  have hn5 : c5.σ.regs.get? Register.x19 = some name := crecover _ _ (by decide) hg_x19
  have hcur5 : c5.σ.regs.get? Register.x9 = some (pn + BitVec.ofNat 64 (8 * i)) := crecover _ _ (by decide) hg_x9
  have hidx5 : c5.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 i) := crecover _ _ (by decide) hg_x8
  have hsp5 : c5.σ.regs.get? Register.x2 = some sp := crecover _ _ (by decide) hg_x2
  have hmem5' : c5.σ.mem = m0 := hmem5
  have hloadedG5 : Env_getLoaded m0 := hloadedG_m0
  obtain ⟨vmi5, hmi5⟩ := hG5.minstret
  -- ghost tie at c5 (for continuing the chain): AbiPreserved regs = g
  have hghost5 : ∀ R : Register, AbiPreserved R = true → c5.σ.regs.get? R = g R := by
    intro R hR
    have hnws : NotWrittenStrcmp R := notWrittenStrcmp_of_abiPreserved R hR
    rw [hframe5 R hnws]; show σ4.regs.get? R = g R; exact hghost4 R hR
  -- steps so far: c → c5
  have hsteps_pre : Steps c c5 :=
    (Steps.single hstep1).trans ((Steps.single hstep2).trans
      ((Steps.single hstep3).trans ((Steps.single hstep4).trans hstepsStr)))
  -- name equality bridge: sa = ofList csa, sb = ofList csb (from strcmp post)
  -- f.vars[i].1 = nameStr ↔ csa = csb (via strcmpSpecSign)
  have hCSa_q : CStr m0 q csa := by
    have : (BitVec.ofNat 64 q).toNat = q := hqNat
    rw [this] at hCSa; exact hCSa
  have hCSb_name : CStr m0 name.toNat csb := hCSb
  obtain ⟨vmi5', hmi5'⟩ := hG5.minstret
  -- ============ c6c: bnez a0 — branch on x10 = xres ============
  by_cases hx0 : xres = 0#64
  · -- x10 = 0 ⇒ names EQUAL ⇒ HIT-in-body (fall through to c70)
    have hspec0 : strcmpSpecSign csa csb = 0 := specSign_zero_of_x10_zero xres csa csb hsign5 hx0
    have hcseq : csa = csb := eq_of_strcmpSpecSign_zero m0 q name.toNat csa csb hCSa_q hCSb_name hspec0
    have hnameEq : f.vars[i].1 = nameStr := by rw [hsaEq, hsbEq, hcseq]
    -- c6c bnez NOT taken
    have hvfalse : (xres != (0#64)) = false := by
      rw [bne_eq_false_iff_eq]; exact hx0
    obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
      site_80002c6c_nottaken_eg2 c5.σ c5.tick c5.steps (0x80002c6c#64) vmi5' xres
        hG5 hpc5 hmi5' hx10_5 (by rw [hmem5']; exact hloadedG_m0) rfl hvfalse htick5
    have hstep6 : Step c5 ⟨σ6, i6, c5.steps + 1⟩ := by cases c5; exact hs6
    have hpc6 : σ6.regs.get? Register.PC = some (0x80002c70#64 : BitVec 64) := by
      have := obs_bnottaken_pc hobs6
      rwa [show BitVec.addInt (0x80002c6c#64 : BitVec 64) 4 = (0x80002c70#64 : BitVec 64) from by decide] at this
    refine ⟨⟨σ6, i6, c5.steps + 1⟩, hsteps_pre.trans (Steps.single hstep6), Or.inr ⟨hilt, hnameEq, hfm, hpc6, hG6⟩⟩
  · -- x10 ≠ 0 ⇒ names DIFFER ⇒ MISS-iter (branch to c54, then c58, → c5c@i+1)
    have hx0' : ¬ xres = (0 : BitVec 64) := by
      intro h; apply hx0; rw [h]; apply BitVec.eq_of_toNat_eq; decide
    have hsignne : strcmpSign xres ≠ 0 := by
      unfold strcmpSign
      rw [if_neg hx0']
      by_cases hlt : xres.toInt < 0
      · rw [if_pos hlt]; decide
      · rw [if_neg hlt]; decide
    have hspecne : strcmpSpecSign csa csb ≠ 0 := by rw [← hsign5]; exact hsignne
    have hcsne : csa ≠ csb := fun h => hspecne (strcmpSpecSign_zero_of_eq csa csb h)
    have hnameNe : f.vars[i].1 ≠ nameStr := by rw [hsaEq, hsbEq]; intro h; exact hcsne (String.ofList_inj.mp h)
    -- c6c bnez TAKEN → c54
    have hvtrue : (xres != (0#64)) = true := by rw [bne_iff_ne]; exact hx0
    obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
      site_80002c6c_taken_eg2 c5.σ c5.tick c5.steps (0x80002c6c#64) vmi5' xres
        hG5 hpc5 hmi5' hx10_5 (by rw [hmem5']; exact hloadedG_m0) rfl (by decide) hvtrue htick5
    have hstep6 : Step c5 ⟨σ6, i6, c5.steps + 1⟩ := by cases c5; exact hs6
    have hpc6 : σ6.regs.get? Register.PC = some (0x80002c54#64 : BitVec 64) := by
      have := obs_btaken_pc hobs6
      rwa [show (0x80002c6c#64 : BitVec 64) + sign_extend (m := 64) (0x1fe8#13) = (0x80002c54#64 : BitVec 64) from by
        apply BitVec.eq_of_toNat_eq; decide] at this
    -- carry saved regs through the taken branch (all preserved)
    have bcarry6 : ∀ (R : Register) (w : RegisterType R),
        (Register.minstret == R) = false → (Register.PC == R) = false →
        (Register.nextPC == R) = false → (Register.minstret_increment == R) = false →
        (Register.mcycle == R) = false → (Register.mtime == R) = false →
        (Register.mip == R) = false → c5.σ.regs.get? R = some w → σ6.regs.get? R = some w := by
      intro R w h1 h2 h4 h5 hmc hmt hmi hσ
      exact obs_btaken_other hobs6 R hmc hmt hmi h1 h2 h4 h5 hσ
    have he6 := bcarry6 Register.x20 env (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) he5
    have ho6 := bcarry6 Register.x21 out (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ho5
    have hcn6 := bcarry6 Register.x18 count (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hcn5
    have hn6 := bcarry6 Register.x19 name (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hn5
    have hcur6 := bcarry6 Register.x9 (pn + BitVec.ofNat 64 (8 * i)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hcur5
    have hidx6 := bcarry6 Register.x8 (BitVec.ofNat 64 i) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hidx5
    have hra6 := bcarry6 Register.x1 (0x80002c6c#64) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra5
    have hsp6 := bcarry6 Register.x2 sp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp5
    obtain ⟨vmi6, hmi6⟩ := obs_btaken_minstret hobs6
    have hmem6' : σ6.mem = m0 := by rw [hmem6]; exact hmem5'
    have hghost6 : ∀ R : Register, AbiPreserved R = true → σ6.regs.get? R = g R := by
      intro R hR
      have hnws : NotWrittenStrcmp R := notWrittenStrcmp_of_abiPreserved R hR
      rw [sframe_btaken hobs6 R hnws]; exact hghost5 R hR
    -- ============ c54: addi s0,s0,1 → i := i+1 → c58 ============
    obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
      site_80002c54_eg2 σ6 i6 (c5.steps + 1) (0x80002c54#64) vmi6 (BitVec.ofNat 64 i)
        hG6 hpc6 hmi6 hidx6 (by rw [hmem6']; exact hloadedG_m0) rfl hi6
    have hstep7 : Step (⟨σ6, i6, c5.steps + 1⟩ : Config) ⟨σ7, i7, c5.steps + 1 + 1⟩ := hs7
    have hpc7 : σ7.regs.get? Register.PC = some (0x80002c58#64 : BitVec 64) := by
      have := obs_alu_pc hobs7
      rwa [show BitVec.addInt (0x80002c54#64 : BitVec 64) 4 = (0x80002c58#64 : BitVec 64) from by decide] at this
    have hidx7 : σ7.regs.get? Register.x8 = some (BitVec.ofNat 64 (i + 1)) := by
      have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
      rw [show (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 from by
        apply BitVec.eq_of_toNat_eq; decide] at this
      rwa [ofNat_succ_bv i (by omega)] at this
    have he7 := obs_alu_other' hobs7 Register.x20 (by decide) he6
    have ho7 := obs_alu_other' hobs7 Register.x21 (by decide) ho6
    have hcn7 := obs_alu_other' hobs7 Register.x18 (by decide) hcn6
    have hn7 := obs_alu_other' hobs7 Register.x19 (by decide) hn6
    have hcur7 := obs_alu_other' hobs7 Register.x9 (by decide) hcur6
    have hra7 := obs_alu_other' hobs7 Register.x1 (by decide) hra6
    have hsp7 := obs_alu_other' hobs7 Register.x2 (by decide) hsp6
    obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
    have hmem7' : σ7.mem = m0 := by rw [hmem7]; exact hmem6'
    -- ============ c58: addi s1,s1,8 → names += 8 → c5c@i+1 ============
    obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
      site_80002c58_eg2 σ7 i7 (c5.steps + 1 + 1) (0x80002c58#64) vmi7 (pn + BitVec.ofNat 64 (8 * i))
        hG7 hpc7 hmi7 hcur7 (by rw [hmem7']; exact hloadedG_m0) rfl hi7
    have hstep8 : Step (⟨σ7, i7, c5.steps + 1 + 1⟩ : Config) ⟨σ8, i8, c5.steps + 1 + 1 + 1⟩ := hs8
    have hpc8 : σ8.regs.get? Register.PC = some scanTestPC := by
      have := obs_alu_pc hobs8
      rwa [show BitVec.addInt (0x80002c58#64 : BitVec 64) 4 = scanTestPC from by decide] at this
    have h8i1 : 8 * (i + 1) < 2^64 := by
      have := hSt.names.slotHi i hilt
      have h32 : (0x100000000 : Nat) = 2^32 := by decide
      have h64 : (2 : Nat)^64 = 2^32 * 2^32 := by decide
      omega
    have hcur8 : σ8.regs.get? Register.x9 = some (pn + BitVec.ofNat 64 (8 * (i + 1))) := by
      have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
      rw [show (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 from by
        apply BitVec.eq_of_toNat_eq; decide] at this
      rwa [cursor_succ_bv pn i h8i1] at this
    have he8 := obs_alu_other' hobs8 Register.x20 (by decide) he7
    have ho8 := obs_alu_other' hobs8 Register.x21 (by decide) ho7
    have hcn8 := obs_alu_other' hobs8 Register.x18 (by decide) hcn7
    have hn8 := obs_alu_other' hobs8 Register.x19 (by decide) hn7
    have hidx8 := obs_alu_other' hobs8 Register.x8 (by decide) hidx7
    have hra8 := obs_alu_other' hobs8 Register.x1 (by decide) hra7
    have hsp8 := obs_alu_other' hobs8 Register.x2 (by decide) hsp7
    obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
    have hmem8' : σ8.mem = m0 := by rw [hmem8]; exact hmem7'
    -- build ScanSt@c5c at i+1 with a FRESH ghost `g' := σ8.regs.get?` (the loop-variant
    -- registers x8/x9 changed, so we re-tie the ghost to the current reads; the `ghost`
    -- field is then `rfl`).  The loop invariant existentially quantifies this ghost.
    have hSt' : ScanSt (fun R => σ8.regs.get? R) scanTestPC env name out count pn r sp (i+1)
        f nameStr N φf φc m0 ⟨σ8, i8, c5.steps + 1 + 1 + 1⟩ :=
      { good := hG8, loadedG := by show Env_getLoaded σ8.mem; rw [hmem8']; exact hloadedG_m0,
        loadedS := by show StrcmpLoaded σ8.mem; rw [hmem8']; exact hloadedS_m0,
        mem := hmem8', pc := hpc8, env4 := he8, name3 := hn8, out5 := ho8, count2 := hcn8,
        cursor1 := hcur8, idx0 := hidx8, ra := by rw [hr]; exact hra8,
        sp2 := hsp8, minstret := ⟨vmi8, hmi8⟩, tick := hi8,
        frame := hSt.frame, names := hSt.names, count_eq := hSt.count_eq,
        ile := by omega, ghost := fun R _ => rfl }
    refine ⟨⟨σ8, i8, c5.steps + 1 + 1 + 1⟩,
      hsteps_pre.trans ((Steps.single hstep6).trans ((Steps.single hstep7).trans (Steps.single hstep8))),
      Or.inl ⟨fun R => σ8.regs.get? R, hSt', ?_⟩⟩
    intro j hj hji
    rcases Nat.lt_or_ge j i with hlt | hge
    · exact hfm j hj hlt
    · have hji' : j = i := by omega
      subst hji'; exact hnameNe

/-! ## The unconditional scan-loop `Triple` (`env_get_scan_spec'`)

`scan_iter` discharges the per-iteration body.  We package it as the `Triple.loop`
body over an EXISTENTIAL-ghost invariant `ScanInvE` (the loop-variant registers
`x8`/`x9` change each iteration, so the ghost tie is re-anchored to the current
reads per iteration — the invariant existentially quantifies the ghost).  `r` is
pinned to the strcmp return address `0x80002c6c` (the scan calls `strcmp` every
iteration, clobbering `x1` to that value). -/

/-- Existential-ghost scan invariant (AtHead ∨ AtHit ∨ AtMiss). -/
def ScanInvE (env name out count pn sp : BitVec 64)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (c : Config) : Prop :=
  (∃ g i, ScanSt g scanTestPC env name out count pn (0x80002c6c#64) sp i f nameStr N φf φc m0 c ∧
      (∀ j, (hj : j < f.vars.length) → j < i → f.vars[j].1 ≠ nameStr)) ∨
  (∃ i, ∃ (hi : i < f.vars.length), f.vars[i].1 = nameStr ∧
      (∀ j, (hj : j < f.vars.length) → j < i → f.vars[j].1 ≠ nameStr) ∧
      c.σ.regs.get? Register.PC = some (0x80002c70#64 : BitVec 64) ∧ GoodState c.σ) ∨
  ((∀ j, (hj : j < f.vars.length) → f.vars[j].1 ≠ nameStr) ∧
      c.σ.regs.get? Register.PC = some (0x80002cc4#64 : BitVec 64) ∧ GoodState c.σ)

/-- Loop guard: still at the test with an unscanned name. -/
def ScanBE (env name out count pn sp : BitVec 64)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (c : Config) : Prop :=
  ∃ g i, ScanSt g scanTestPC env name out count pn (0x80002c6c#64) sp i f nameStr N φf φc m0 c ∧
      (∀ j, (hj : j < f.vars.length) → j < i → f.vars[j].1 ≠ nameStr) ∧ i < f.vars.length

/-- The loop body `Triple`: one guarded iteration re-establishes `ScanInvE`
with `ScanMu` strictly decreased.  Discharged by `scan_iter`. -/
theorem env_get_scan_body (env name out count pn sp : BitVec 64)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (n : Nat) :
    Triple
      (fun c => ScanInvE env name out count pn sp f nameStr N φf φc m0 c ∧
                ScanBE env name out count pn sp f nameStr N φf φc m0 c ∧ ScanMu c = n)
      (fun c => ScanInvE env name out count pn sp f nameStr N φf φc m0 c ∧ ScanMu c < n) := by
  intro c ⟨_, hB, hμ⟩
  obtain ⟨g, i, hSt, hfm, hilt⟩ := hB
  -- ScanMu at the current config: count - i
  have hMuc : ScanMu c = count.toNat - i := by
    rw [scanMu_at_testPC hSt.pc hSt.count2 hSt.idx0, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := count.isLt; rw [hSt.count_eq] at *; omega)]
  obtain ⟨c', hsteps, hnext⟩ := scan_iter g env name out count pn (0x80002c6c#64) sp i f nameStr N φf φc m0 c hSt hfm hilt rfl
  rcases hnext with ⟨g', hSt', hfm'⟩ | ⟨hilt2, hhit, hfm2, hpc', hG'⟩
  · -- MISS-iter: AtHead at i+1, measure decreased
    refine ⟨c', hsteps, Or.inl ⟨g', i+1, hSt', hfm'⟩, ?_⟩
    have hMuc' : ScanMu c' = count.toNat - (i+1) := by
      rw [scanMu_at_testPC hSt'.pc hSt'.count2 hSt'.idx0, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := count.isLt; rw [hSt'.count_eq] at *; omega)]
    have hicnt : i < count.toNat := by rw [hSt.count_eq]; exact hilt
    rw [← hμ, hMuc, hMuc']; omega
  · -- HIT-in-body: AtHit, measure 0 < n (guard was live)
    refine ⟨c', hsteps, Or.inr (Or.inl ⟨i, hilt2, hhit, hfm2, hpc', hG'⟩), ?_⟩
    have hMu' : ScanMu c' = 0 :=
      scanMu_off_testPC hpc' (by decide)
    have hicnt : i < count.toNat := by rw [hSt.count_eq]; exact hilt
    rw [← hμ, hMuc, hMu']; omega

/-- **`env_get` SCAN-LOOP disjunctive triple (one frame), UNCONDITIONAL.**
From the existential-ghost scan invariant the machine reaches the disjunctive exit
`ScanExit`.  This discharges the `hbody` hypothesis of `env_get_scan_spec` (item 1
of the continuation): the per-iteration body is `env_get_scan_body`, and the
`AtHead`-exit collapse is the verified `scan_head_exit`. -/
theorem env_get_scan_spec' (env name out count pn sp : BitVec 64)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) :
    Triple (ScanInvE env name out count pn sp f nameStr N φf φc m0)
           (ScanExit env f nameStr) := by
  have hloop := Triple.loop
    (I := ScanInvE env name out count pn sp f nameStr N φf φc m0)
    (B := ScanBE env name out count pn sp f nameStr N φf φc m0) ScanMu
    (env_get_scan_body env name out count pn sp f nameStr N φf φc m0)
  refine hloop.seq ?_
  intro c ⟨hI, hnB⟩
  rcases hI with hHead | hHit | hMiss
  · obtain ⟨g, i, hSt, hfm⟩ := hHead
    have hcnt : f.vars.length < 2^64 := by rw [← hSt.count_eq]; exact count.isLt
    have hile := hSt.ile
    have hnlt : ¬ i < f.vars.length := fun hlt => hnB ⟨g, i, hSt, hfm, hlt⟩
    have hie : i = f.vars.length := by omega
    obtain ⟨c', hsteps, hall, hpc', hG'⟩ :=
      scan_head_exit g env name out count pn (0x80002c6c#64) sp i f nameStr N φf φc m0 c hSt hfm hie hcnt
    exact ⟨c', hsteps, Or.inr ⟨hall, hpc', hG'⟩⟩
  · exact ⟨c, .refl c, Or.inl hHit⟩
  · exact ⟨c, .refl c, Or.inr hMiss⟩

end Vsa.Sim
