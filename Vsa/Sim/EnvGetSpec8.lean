import Vsa.Sim.EnvGetSpec7

/-!
# Layer 3 — `env_get` do-while FIRST body (from `0x80002c60`) and the truly
hypothesis-free immediate-frame FOUND case (`env_get_found_uncond'`).

The prologue (`env_get_prologue`, EnvGetSpec7) is a **do-while**: after `li s0,0`
it jumps (`c50 j`) straight to the loop BODY at `0x80002c60`, SKIPPING the test
`0x80002c5c`.  Hence `env_get_scan_spec'` (EnvGetSpec4), whose `ScanInvE`/AtHead
disjunct pins the machine at the test PC `0x80002c5c`, does NOT plug directly onto
the prologue's exit.  The missing piece is the **first body iteration entered at
`0x80002c60`** (skipping the initial `beq` guard, which the prologue's `c44 blez`
already discharged: `0 = i < count`).

`scan_iter_from_c60` is exactly `scan_iter`'s body from the `c60` load onward: from
a `ScanSt` at `0x80002c60` at index `i < count` it runs one loop body to the
disjunctive next config — the scan-test at `i+1` (MISS, first-match extended) OR
the HIT block `0x80002c70` at `i` (HIT).  It is `scan_iter` with the leading
`c5c beq` step removed; every subsequent site/composition is identical.

We then package the immediate-frame FOUND case WITHOUT the `hbody` residual of
`env_get_found_uncond`: from a strengthened prologue-entry predicate `FoundSt`
(the `PrologueSt` geometry PLUS the `ScanNames` carrier, `StrcmpLoaded`, and the
HIT-tail geometry the `AtHit → HitTailSt` repackaging consumes), the machine runs

  prologue (c10→c60) ≫ from-c60 first body + full scan loop (→ AtHit @ c70)
    ≫ AtHit→HitTailSt repackaging ≫ `env_get_hit_tail` (c70→ret).

The first-match index is EXISTENTIAL (the scan finds it), and the found value is
`f.vars[iHit].2` for that first-match `iHit`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
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

/-! ## 0. A register-carrying HIT exit (`HitAt`)

`ScanExit`/`ScanInvE`'s HIT disjunct only exposes `PC = c70 ∧ GoodState`; the
`AtHit → HitTailSt` repackaging additionally needs the scan live registers
(`s4=env`, `s0=ofNat i`, `s5=out`, `sp`, and `x1`) at `0x80002c70`, plus the
first-match witness and the standing `mem=m0`.  `HitAt` bundles exactly those, so
the loop below can carry them out of the HIT branch (where they are all in scope)
into the `HitTailSt` assembly. -/
structure HitAt (env out sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (m0 : Mem) (c : Config) : Prop where
  good : GoodState c.σ
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80002c70#64 : BitVec 64)
  env4 : c.σ.regs.get? Register.x20 = some env       -- s4
  idx0 : c.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 i)  -- s0
  out5 : c.σ.regs.get? Register.x21 = some out       -- s5
  sp2 : c.σ.regs.get? Register.x2 = some sp
  ra1 : c.σ.regs.get? Register.x1 = some (0x80002c6c#64 : BitVec 64)  -- strcmp link
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  ilt : i < f.vars.length
  hit : f.vars[i].1 = nameStr
  firstMatch : ∀ j, (hj : j < f.vars.length) → j < i → f.vars[j].1 ≠ nameStr

/-! ## 1. The do-while FIRST body chain (`scan_iter_from_c60`)

Identical to `scan_iter` (EnvGetSpec4) but ENTERED at the `c60` load instead of the
`c5c` test — the prologue's `j` lands here, having already discharged the `beq`
guard via the `blez count` null-check.  The proof is `scan_iter`'s body verbatim
from its line-233 `scan_c60_load` onward, with the standing `ScanSt` taken at
`0x80002c60`. -/
theorem scan_iter_from_c60 (g : (R : Register) → Option (RegisterType R))
    (env name out count pn r sp : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (c : Config)
    (hSt : ScanSt g (0x80002c60#64) env name out count pn r sp i f nameStr N φf φc m0 c)
    (hfm : ∀ j, (hj : j < f.vars.length) → j < i → f.vars[j].1 ≠ nameStr)
    (hilt : i < f.vars.length) :
    ∃ c', Steps c c' ∧
      ((∃ (g' : (R : Register) → Option (RegisterType R)),
          -- the do-while body sets `x1 := 0x80002c6c` (the strcmp link) via the `c68`
          -- jal, so the next-iteration test state carries that link regardless of the
          -- c60-entry `ra`; the input `r` (`hSt.ra`) is not read.
          ScanSt g' scanTestPC env name out count pn (0x80002c6c#64) sp (i+1) f nameStr N φf φc m0 c' ∧
          ∀ j, (hj : j < f.vars.length) → j < i + 1 → f.vars[j].1 ≠ nameStr)
       ∨ HitAt env out sp i f nameStr m0 c') := by
  have hcnt : count.toNat = f.vars.length := hSt.count_eq
  have hcntlt : f.vars.length < 2^64 := by rw [← hcnt]; exact count.isLt
  have hloadedG_m0 : Env_getLoaded m0 := hSt.mem ▸ hSt.loadedG
  have hloadedS_m0 : StrcmpLoaded m0 := hSt.mem ▸ hSt.loadedS
  -- the slot-i name pointer from ScanNames
  obtain ⟨q, hq, hCSq⟩ := hSt.names.bindPtr i hilt
  -- ghost values of the saved registers
  have hg_x8 : g Register.x8 = some (BitVec.ofNat 64 i) := by rw [← hSt.ghost _ (by decide)]; exact hSt.idx0
  have hg_x9 : g Register.x9 = some (pn + BitVec.ofNat 64 (8 * i)) := by rw [← hSt.ghost _ (by decide)]; exact hSt.cursor1
  have hg_x18 : g Register.x18 = some count := by rw [← hSt.ghost _ (by decide)]; exact hSt.count2
  have hg_x19 : g Register.x19 = some name := by rw [← hSt.ghost _ (by decide)]; exact hSt.name3
  have hg_x20 : g Register.x20 = some env := by rw [← hSt.ghost _ (by decide)]; exact hSt.env4
  have hg_x21 : g Register.x21 = some out := by rw [← hSt.ghost _ (by decide)]; exact hSt.out5
  have hg_x2 : g Register.x2 = some sp := by rw [← hSt.ghost _ (by decide)]; exact hSt.sp2
  -- ============ c60: ld a0,0(s1) → x10 = ofNat q (via scan_c60_load) ============
  obtain ⟨c2, hstep2, hpc2, hx10_2, hn2, hra2, hmem2, hG2, htick2, hmi2, hghost2⟩ :=
    scan_c60_load g env name out count pn r sp i f nameStr N φf φc m0 c q hSt hilt hq
  have hmem2' : c2.σ.mem = m0 := hmem2
  obtain ⟨vmi2, hmi2'⟩ := hmi2
  have he2 : c2.σ.regs.get? Register.x20 = some env := by rw [hghost2 _ (by decide)]; exact hg_x20
  have ho2 : c2.σ.regs.get? Register.x21 = some out := by rw [hghost2 _ (by decide)]; exact hg_x21
  have hcn2 : c2.σ.regs.get? Register.x18 = some count := by rw [hghost2 _ (by decide)]; exact hg_x18
  have hcur2 : c2.σ.regs.get? Register.x9 = some (pn + BitVec.ofNat 64 (8 * i)) := by rw [hghost2 _ (by decide)]; exact hg_x9
  have hidx2 : c2.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 i) := by rw [hghost2 _ (by decide)]; exact hg_x8
  have hsp2 : c2.σ.regs.get? Register.x2 = some sp := by rw [hghost2 _ (by decide)]; exact hg_x2
  -- ============ c64: mv a1,s3 → x11 := name → c68 ============
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80002c64_eg2 c2.σ c2.tick c2.steps (0x80002c64#64) vmi2 name hG2 hpc2 hmi2' hn2 (by rw [hmem2']; exact hloadedG_m0) rfl htick2
  have hstep3 : Step c2 ⟨σ3, i3, c2.steps + 1⟩ := by cases c2; exact hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x80002c68#64 : BitVec 64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80002c64#64 : BitVec 64) 4 = (0x80002c68#64 : BitVec 64) from by decide] at this
  have hx11_3 : σ3.regs.get? Register.x11 = some name := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_zero, BitVec.add_zero] at this
  have hx10_3 := obs_alu_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_2
  have hra3 := obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hmem3' : σ3.mem = m0 := by rw [hmem3]; exact hmem2'
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
  have hghost4 : ∀ R : Register, AbiPreserved R = true → σ4.regs.get? R = g R := by
    intro R hR
    have hnws : NotWrittenStrcmp R := notWrittenStrcmp_of_abiPreserved R hR
    have hx1 : (Register.x1 == R) = false := by
      cases R <;> simp_all [AbiPreserved]
    rw [(sframe_jal_eg4 hobs4 R hx1 hnws)]; exact hghost3 R hR
  -- ============ strcmp callee: strcmp_full_spec ============
  have hqlt : q < 2^64 := read64_lt_eg4 m0 (pn.toNat + 8 * i) q hq
  have hqNat : (BitVec.ofNat 64 q).toNat = q := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqlt]
  let g4 : (R : Register) → Option (RegisterType R) := fun R => σ4.regs.get? R
  have hStrPre : strcmp_full_pre g4 (BitVec.ofNat 64 q) name (0x80002c6c#64) (f.vars[i].1) nameStr m0
      σ4.sailOutput ⟨σ4, i4, c2.steps + 1 + 1⟩ := by
    refine ⟨hG4, hloadedS4, hmem4', rfl, hpc4, hx10_4, hx11_4, hra4, ⟨vmi4, hmi4⟩, hi4, by decide, ?_, ?_,
      hSt.names.maskPinned, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hqNat]; exact hCSq
    · exact hSt.names.nameCStr
    · rw [hqNat]; exact fun cs hcs => hSt.names.bindRegB i hilt q hq cs hcs
    · exact fun cs hcs => hSt.names.nameRegB cs hcs
    · rw [hqNat]; exact fun cs hcs => hSt.names.bindRegW i hilt q hq cs hcs
    · exact fun cs hcs => hSt.names.nameRegW cs hcs
    · intro R _; rfl
  obtain ⟨c5, hstepsStr, hStrPost⟩ :=
    strcmp_full_spec g4 (BitVec.ofNat 64 q) name (0x80002c6c#64) (f.vars[i].1) nameStr m0
      σ4.sailOutput ⟨σ4, i4, c2.steps + 1 + 1⟩ hStrPre
  obtain ⟨hG5, hpc5, hra5, hmem5, _hout5, htick5, hframe5,
    csa, csb, xres, hCSa, hCSb, hsaEq, hsbEq, hx10_5, hsign5⟩ := hStrPost
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
  obtain ⟨vmi5, hmi5⟩ := hG5.minstret
  have hghost5 : ∀ R : Register, AbiPreserved R = true → c5.σ.regs.get? R = g R := by
    intro R hR
    have hnws : NotWrittenStrcmp R := notWrittenStrcmp_of_abiPreserved R hR
    rw [hframe5 R hnws]; show σ4.regs.get? R = g R; exact hghost4 R hR
  -- steps so far: c → c5  (from-c60: c → c2 is scan_c60_load's single step)
  have hsteps_pre : Steps c c5 :=
    (Steps.single hstep2).trans ((Steps.single hstep3).trans ((Steps.single hstep4).trans hstepsStr))
  have hCSa_q : CStr m0 q csa := by
    have : (BitVec.ofNat 64 q).toNat = q := hqNat
    rw [this] at hCSa; exact hCSa
  have hCSb_name : CStr m0 name.toNat csb := hCSb
  obtain ⟨vmi5', hmi5'⟩ := hG5.minstret
  -- ============ c6c: bnez a0 ============
  by_cases hx0 : xres = 0#64
  · -- HIT
    have hspec0 : strcmpSpecSign csa csb = 0 := specSign_zero_of_x10_zero xres csa csb hsign5 hx0
    have hcseq : csa = csb := eq_of_strcmpSpecSign_zero m0 q name.toNat csa csb hCSa_q hCSb_name hspec0
    have hnameEq : f.vars[i].1 = nameStr := by rw [hsaEq, hsbEq, hcseq]
    have hvfalse : (xres != (0#64)) = false := by
      rw [bne_eq_false_iff_eq]; exact hx0
    obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
      site_80002c6c_nottaken_eg2 c5.σ c5.tick c5.steps (0x80002c6c#64) vmi5' xres
        hG5 hpc5 hmi5' hx10_5 (by rw [hmem5']; exact hloadedG_m0) rfl hvfalse htick5
    have hstep6 : Step c5 ⟨σ6, i6, c5.steps + 1⟩ := by cases c5; exact hs6
    have hpc6 : σ6.regs.get? Register.PC = some (0x80002c70#64 : BitVec 64) := by
      have := obs_bnottaken_pc hobs6
      rwa [show BitVec.addInt (0x80002c6c#64 : BitVec 64) 4 = (0x80002c70#64 : BitVec 64) from by decide] at this
    have he6 := obs_bnottaken_other hobs6 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) he5
    have hidx6 := obs_bnottaken_other hobs6 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hidx5
    have ho6 := obs_bnottaken_other hobs6 Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ho5
    have hsp6 := obs_bnottaken_other hobs6 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp5
    have hra6 := obs_bnottaken_other hobs6 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra5
    have hmem6' : σ6.mem = m0 := by rw [hmem6]; exact hmem5'
    refine ⟨⟨σ6, i6, c5.steps + 1⟩, hsteps_pre.trans (Steps.single hstep6),
      Or.inr ⟨hG6, hmem6', hpc6, he6, hidx6, ho6, hsp6, hra6, obs_bnottaken_minstret hobs6, hi6, hilt, hnameEq, hfm⟩⟩
  · -- MISS
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
    have hvtrue : (xres != (0#64)) = true := by rw [bne_iff_ne]; exact hx0
    obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
      site_80002c6c_taken_eg2 c5.σ c5.tick c5.steps (0x80002c6c#64) vmi5' xres
        hG5 hpc5 hmi5' hx10_5 (by rw [hmem5']; exact hloadedG_m0) rfl (by decide) hvtrue htick5
    have hstep6 : Step c5 ⟨σ6, i6, c5.steps + 1⟩ := by cases c5; exact hs6
    have hpc6 : σ6.regs.get? Register.PC = some (0x80002c54#64 : BitVec 64) := by
      have := obs_btaken_pc hobs6
      rwa [show (0x80002c6c#64 : BitVec 64) + sign_extend (m := 64) (0x1fe8#13) = (0x80002c54#64 : BitVec 64) from by
        apply BitVec.eq_of_toNat_eq; decide] at this
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
    have he7 := obs_alu_other hobs7 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) he6
    have ho7 := obs_alu_other hobs7 Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ho6
    have hcn7 := obs_alu_other hobs7 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hcn6
    have hn7 := obs_alu_other hobs7 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hn6
    have hcur7 := obs_alu_other hobs7 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hcur6
    have hra7 := obs_alu_other hobs7 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra6
    have hsp7 := obs_alu_other hobs7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp6
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
    have he8 := obs_alu_other hobs8 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) he7
    have ho8 := obs_alu_other hobs8 Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ho7
    have hcn8 := obs_alu_other hobs8 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hcn7
    have hn8 := obs_alu_other hobs8 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hn7
    have hidx8 := obs_alu_other hobs8 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hidx7
    have hra8 := obs_alu_other hobs8 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra7
    have hsp8 := obs_alu_other hobs8 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp7
    obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
    have hmem8' : σ8.mem = m0 := by rw [hmem8]; exact hmem7'
    have hSt' : ScanSt (fun R => σ8.regs.get? R) scanTestPC env name out count pn (0x80002c6c#64) sp (i+1)
        f nameStr N φf φc m0 ⟨σ8, i8, c5.steps + 1 + 1 + 1⟩ :=
      { good := hG8, loadedG := by show Env_getLoaded σ8.mem; rw [hmem8']; exact hloadedG_m0,
        loadedS := by show StrcmpLoaded σ8.mem; rw [hmem8']; exact hloadedS_m0,
        mem := hmem8', pc := hpc8, env4 := he8, name3 := hn8, out5 := ho8, count2 := hcn8,
        cursor1 := hcur8, idx0 := hidx8, ra := hra8,
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

/-! ## 2. The from-`c5c` body producing `HitAt` (`scan_iter_hit`)

`scan_iter_from_c60` handles the do-while FIRST body (entered at `c60`).  Every
SUBSEQUENT iteration re-enters at the test `c5c` (scanTestPC).  `scan_iter_hit`
runs the `c5c` `beq`-not-taken step (guard live: `i < count`), rebuilds the
`ScanSt` at `c60`, and delegates to `scan_iter_from_c60`.  Result: the same
`ScanSt@c5c(i+1)` (MISS) or `HitAt` (HIT) disjunction, register-carrying. -/
theorem scan_iter_hit (g : (R : Register) → Option (RegisterType R))
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
       ∨ HitAt env out sp i f nameStr m0 c') := by
  have hcnt : count.toNat = f.vars.length := hSt.count_eq
  have hcntlt : f.vars.length < 2^64 := by rw [← hcnt]; exact count.isLt
  obtain ⟨vmi0, hmi0⟩ := hSt.minstret
  have hbeq : ((BitVec.ofNat 64 i) == count) = false := by
    have hc : count = BitVec.ofNat 64 f.vars.length := by
      apply BitVec.eq_of_toNat_eq
      rw [hcnt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcntlt]
    rw [hc]; exact beq_scan_nottaken i f.vars.length hilt hcntlt
  -- ============ c5c: beq s0,s2 NOT taken (i ≠ count) → c60 ============
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80002c5c_nottaken_eg2 c.σ c.tick c.steps scanTestPC vmi0 (BitVec.ofNat 64 i) count
      hSt.good hSt.pc hmi0 hSt.idx0 hSt.count2 hSt.loadedG rfl hbeq hSt.tick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002c60#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs1
    rwa [show BitVec.addInt scanTestPC 4 = (0x80002c60#64 : BitVec 64) from by decide] at this
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
  have hSt60 : ScanSt g (0x80002c60#64) env name out count pn r sp i f nameStr N φf φc m0
      ⟨σ1, i1, c.steps + 1⟩ :=
    { good := hG1, loadedG := by rw [hmem1']; exact hloadedG_m0, loadedS := by rw [hmem1']; exact hloadedS_m0,
      mem := hmem1', pc := hpc1, env4 := he1, name3 := hn1, out5 := ho1, count2 := hcn1,
      cursor1 := hcur1, idx0 := hidx1, ra := hra1, sp2 := hsp1, minstret := ⟨vmi1, hmi1⟩,
      tick := hi1, frame := hSt.frame, names := hSt.names, count_eq := hSt.count_eq, ile := hSt.ile,
      ghost := hghost1 }
  obtain ⟨c', hsteps60, hdisj⟩ :=
    scan_iter_from_c60 g env name out count pn r sp i f nameStr N φf φc m0
      ⟨σ1, i1, c.steps + 1⟩ hSt60 hfm hilt
  -- `scan_iter_from_c60` outputs the next-iteration `ScanSt` with `x1 = 0x80002c6c`
  -- (the strcmp link set by the `c68` jal); `scan_iter_hit`'s `r = 0x80002c6c` (`hr`).
  subst hr
  exact ⟨c', (Steps.single hstep1).trans hsteps60, hdisj⟩

/-! ## 3. The register-carrying scan-to-HIT loop (`scan_from_c5c_to_hit`)

Given a `ScanSt` at `c5c` (scanTestPC) at index `i`, a concrete HIT witness
`iw` (`iw < count`, `f.vars[iw].1 = nameStr`) with `i ≤ iw`, the machine reaches
a `HitAt` at the first-match index.  Strong induction on the fuel `iw - i`:
`scan_iter_hit` either HITs (done) or advances to `i+1`.  In the MISS case the
slot-`i` name differed, so `i ≠ iw` (the witness matches), hence `i < iw`, so
`i+1 ≤ iw` — the fuel strictly decreases and `i+1 ≤ iw < count` keeps the guard
live.  The first-match at any reached HIT equals `iw` by first-match uniqueness,
but we only need SOME `HitAt`; the `HitAt.firstMatch` field pins its index. -/
theorem scan_from_c5c_to_hit (env name out count pn sp : BitVec 64)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (iw : Nat) (hiw : iw < f.vars.length) (hhit : f.vars[iw].1 = nameStr) :
    ∀ (fuel : Nat) (g : (R : Register) → Option (RegisterType R)) (i : Nat) (c : Config),
      ScanSt g scanTestPC env name out count pn (0x80002c6c#64) sp i f nameStr N φf φc m0 c →
      (∀ j, (hj : j < f.vars.length) → j < i → f.vars[j].1 ≠ nameStr) →
      i ≤ iw → iw - i ≤ fuel →
      ∃ (c' : Config) (iHit : Nat),
        Steps c c' ∧ HitAt env out sp iHit f nameStr m0 c' := by
  intro fuel
  induction fuel with
  | zero =>
    intro g i c hSt hfm hle hfuel
    -- fuel = 0 ⇒ iw - i = 0 ⇒ i = iw (with i ≤ iw); so slot i matches ⇒ this iteration HITs.
    have hie : i = iw := by omega
    have hilt : i < f.vars.length := by omega
    obtain ⟨c', hsteps, hdisj⟩ :=
      scan_iter_hit g env name out count pn (0x80002c6c#64) sp i f nameStr N φf φc m0 c hSt hfm hilt rfl
    rcases hdisj with ⟨g', hSt', hfm'⟩ | hHit
    · -- MISS at i = iw contradicts the witness `f.vars[iw].1 = nameStr`
      exact absurd hhit (hfm' iw hiw (by omega))
    · exact ⟨c', i, hsteps, hHit⟩
  | succ fuel ih =>
    intro g i c hSt hfm hle hfuel
    have hilt : i < f.vars.length := by omega
    obtain ⟨c', hsteps, hdisj⟩ :=
      scan_iter_hit g env name out count pn (0x80002c6c#64) sp i f nameStr N φf φc m0 c hSt hfm hilt rfl
    rcases hdisj with ⟨g', hSt', hfm'⟩ | hHit
    · -- MISS: slot i differed, so i ≠ iw ⇒ i < iw ⇒ i+1 ≤ iw, fuel decreases
      have hne : i ≠ iw := by
        intro h; exact absurd hhit (hfm' iw hiw (by omega))
      have hlt : i < iw := by omega
      obtain ⟨c'', iHit, hsteps2, hHit2⟩ :=
        ih g' (i + 1) c' hSt' hfm' (by omega) (by omega)
      exact ⟨c'', iHit, hsteps.trans hsteps2, hHit2⟩
    · exact ⟨c', i, hsteps, hHit⟩

/-! ## 4. The strengthened FOUND-case entry predicate (`FoundSt`)

`FoundSt` is `PrologueSt` PLUS the facts the scan loop and the `HitTailSt`
assembly consume that `PrologueSt` did not carry:

* `namesC` — the `ScanNames` carrier (per-binding CString + strcmp regions + the
  `c60` load-address side conditions), phrased over `pn`;
* `loadedS` — `StrcmpLoaded` (the scan calls `strcmp` every iteration);
* the HIT witness `iw` (`iw < count`, `f.vars[iw].1 = nameStr`) — this is what the
  FOUND case asserts (`Store.lookup` succeeded ⇒ some binding name matches);
* the per-slot source-value word readability + the `HitTailSt` geometry
  (`env`/`out`/`src`/`spill` RAM/HTIF/alignment/disjointness), the out buffer,
  and the string-payload disjointness `payDisj`, quantified over every slot `i`.

The prologue's own frame is `[sp0-64, sp0)`; the out buffer, env frame, and value
slots are all in the arena (disjoint from that stack frame and from the code). -/
structure FoundSt
    (env name out r sp0 : BitVec 64) (r0 r8 r9 r18 r19 r20 r21 : BitVec 64) (len pn : Nat)
    (nameStr : String) (iw : Nat)
    (f : Vsa.While.Frame) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (c : Config) : Prop where
  base : PrologueSt env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn f N φf φc m0 c
  loadedS : StrcmpLoaded m0
  namesC : ScanNames m0 pn name nameStr f
  pnSmall : pn < 2^64
  rLinkEq : r0 = r   -- incoming ra (spilled at sp+56) = caller return link
  -- HIT witness (the FOUND case: some binding's name equals the query)
  iwLt : iw < f.vars.length
  iwHit : f.vars[iw].1 = nameStr
  -- geometry consumed by `HitTailSt`, quantified over the reachable slots
  ismall : ∀ i, i < f.vars.length → i < 2^32
  -- env->vals header slot geometry
  envValsLo : 0x80000000 ≤ env.toNat + 16
  envValsWin : env.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 8 ≤ env.toNat + 16
  envValsAlign : (env.toNat + 16) % 8 = 0
  envNoWrap : env.toNat + 24 < 2^64
  envValsHi : env.toNat + 24 ≤ 0x100000000
  -- out buffer geometry
  outLo : 0x80000000 ≤ out.toNat
  outHi : out.toNat + 24 ≤ 0x100000000
  outWin : tohostAddr + 16 ≤ out.toNat
  outAlign : out.toNat % 8 = 0
  outCode : out.toNat + 24 ≤ 0x80002c10 ∨ 0x80002cdc ≤ out.toNat
  -- spill window geometry
  spillLo : 0x80000000 ≤ (sp0 - 64#64).toNat + 8
  spillHi : (sp0 - 64#64).toNat + 64 ≤ 0x100000000
  spillWin : tohostAddr + 16 ≤ (sp0 - 64#64).toNat + 8
  spillAlign : (sp0 - 64#64).toNat % 8 = 0
  spillNoWrap : (sp0 - 64#64).toNat + 64 < 2^64
  -- source value slot geometry + words, per slot (pv = read64 (env+16))
  pvVals : ∀ pv, read64 m0 (env.toNat + 16) = some pv →
    ∀ i, i < f.vars.length →
      (∃ w0 w1 w2, read64 m0 (pv + 24 * i) = some w0 ∧ read64 m0 (pv + 24 * i + 8) = some w1 ∧
        read64 m0 (pv + 24 * i + 16) = some w2) ∧
      0x80000000 ≤ pv + 24 * i ∧ pv + 24 * i + 24 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ pv + 24 * i ∧ (pv + 24 * i) % 8 = 0 ∧ pv + 24 * i + 24 < 2^64 ∧
      pv + 24 * i < 2^64 ∧
      (pv + 24 * i + 24 ≤ out.toNat ∨ out.toNat + 24 ≤ pv + 24 * i) ∧
      (∀ (p : Nat) (s : String), read64 m0 (pv + 24 * i + 8) = some p →
        ∀ k, k ≤ s.length → (p + k < out.toNat ∨ out.toNat + 24 ≤ p + k))
  -- out buffer disjoint from the spill window
  outSpillDisj : out.toNat + 24 ≤ (sp0 - 64#64).toNat + 8 ∨ (sp0 - 64#64).toNat + 64 ≤ out.toNat
  -- return-address alignment (the caller link r)
  rAlign : r.toNat % 4 = 0

/-! ## 5. `AtHit → HitTailSt` geometry repackaging (`hitAt_to_hitTail`)

From a register-carrying `HitAt` at `0x80002c70` (index `iHit`, standing memory
`m0`), the `FrameRepr` at `env`, the seven spill reads (from the prologue), and the
`HitTailSt` geometry (all quantified over `iHit` via `FoundSt`), assemble a
`HitTailSt` so `env_get_hit_tail` can fire.  `pv = read64 (env+16)` and the three
source words come from `FrameRepr` header + `FoundSt.pvVals`. -/
theorem hitAt_to_hitTail
    (env name out r sp0 : BitVec 64) (r0 r8 r9 r18 r19 r20 r21 : BitVec 64) (len pn : Nat)
    (nameStr : String) (iw iHit : Nat)
    (f : Vsa.While.Frame) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 m9 : Mem) (c c0 : Config)
    (hFS : FoundSt env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn nameStr iw f N φf φc m0 c0)
    (hframe9 : FrameRepr m9 N φf φc env.toNat f)
    (hmem9 : m9 = c.σ.mem)  -- the scan's standing memory (post-prologue spills)
    (hHit : HitAt env out (sp0 - 64#64) iHit f nameStr m9 c)
    (hloaded9 : Env_getLoaded m9)
    -- geometry over m9 for slot iHit, transported by FoundSt over m9
    (hgeom : ∀ pv, read64 m9 (env.toNat + 16) = some pv →
      (∃ w0 w1 w2, read64 m9 (pv + 24 * iHit) = some w0 ∧ read64 m9 (pv + 24 * iHit + 8) = some w1 ∧
        read64 m9 (pv + 24 * iHit + 16) = some w2) ∧
      0x80000000 ≤ pv + 24 * iHit ∧ pv + 24 * iHit + 24 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ pv + 24 * iHit ∧ (pv + 24 * iHit) % 8 = 0 ∧ pv + 24 * iHit + 24 < 2^64 ∧
      pv + 24 * iHit < 2^64 ∧
      (pv + 24 * iHit + 24 ≤ out.toNat ∨ out.toNat + 24 ≤ pv + 24 * iHit) ∧
      (∀ (p : Nat) (s : String), read64 m9 (pv + 24 * iHit + 8) = some p →
        ∀ k, k ≤ s.length → (p + k < out.toNat ∨ out.toNat + 24 ≤ p + k)))
    -- the seven spill slots over m9 (from the prologue's output)
    (hs56 : read64 m9 ((sp0 - 64#64).toNat + 56) = some r0.toNat)
    (hs48 : read64 m9 ((sp0 - 64#64).toNat + 48) = some r8.toNat)
    (hs40 : read64 m9 ((sp0 - 64#64).toNat + 40) = some r9.toNat)
    (hs32 : read64 m9 ((sp0 - 64#64).toNat + 32) = some r18.toNat)
    (hs24 : read64 m9 ((sp0 - 64#64).toNat + 24) = some r19.toNat)
    (hs16 : read64 m9 ((sp0 - 64#64).toNat + 16) = some r20.toNat)
    (hs8 : read64 m9 ((sp0 - 64#64).toNat + 8) = some r21.toNat) :
    ∃ (pv w0 w1 w2 : Nat),
      HitTailSt (c.σ.regs.get?) env out (sp0 - 64#64) r r0 r8 r9 r18 r19 r20 r21 iHit pv w0 w1 w2
        f N φf φc m9 c := by
  -- value pointer from the FrameRepr header
  obtain ⟨_hlen, _hcap, ⟨pn', pv, _hpn, hpv, _hslots⟩, _hpar⟩ := id hframe9
  have hgeomI := hgeom pv hpv
  obtain ⟨⟨w0, w1, w2, hw0, hw1, hw2⟩, hslo, hshi, hswin, hsalign, hsnw, hpvnw, hsod, hpayd⟩ := hgeomI
  refine ⟨pv, w0, w1, w2, ?_⟩
  refine
    { good := hHit.good, loadedG := by rw [hHit.mem]; exact hloaded9,
      mem := hHit.mem, pc := hHit.pc, env4 := hHit.env4, idx0 := hHit.idx0, out5 := hHit.out5,
      sp2 := hHit.sp2, minstret := hHit.minstret, tick := hHit.tick,
      frame := hframe9, ilt := hHit.ilt, ismall := hFS.ismall iHit hHit.ilt,
      pv_eq := hpv, srcW0 := hw0, srcW1 := hw1, srcW2 := hw2,
      envLo := hFS.envValsLo, envHi := hFS.envValsHi, envWin := hFS.envValsWin,
      envAlign := hFS.envValsAlign, envNoWrap := hFS.envNoWrap,
      outLo := hFS.outLo, outHi := hFS.outHi, outWin := hFS.outWin, outAlign := hFS.outAlign,
      outCode := hFS.outCode,
      slotRa := hs56, slotS0 := hs48, slotS1 := hs40, slotS2 := hs32, slotS3 := hs24,
      slotS4 := hs16, slotS5 := hs8, rr_eq := ?_,
      spLo := hFS.spillLo, spHi := hFS.spillHi, spWin := hFS.spillWin, spAlign := hFS.spillAlign,
      spNoWrap := hFS.spillNoWrap,
      srcLo := hslo, srcHi := hshi, srcWin := hswin, srcAlign := hsalign, srcNoWrap := hsnw,
      pvNoWrap := hpvnw, src_out_disjoint := hsod, out_spill_disjoint := hFS.outSpillDisj,
      payDisj := hpayd, rAlign := hFS.rAlign }
  -- rr_eq: the spilled ra (r0) equals the caller link r (FoundSt.rLinkEq).
  exact hFS.rLinkEq

/-! ## 6. The immediate-frame FOUND case, scan+repackaging+tail discharged
(`env_get_found_uncond'`)

`env_get_found_uncond'` runs the verified prologue (`env_get_prologue`) to the
do-while body entry `0x80002c60`, then — given the post-prologue scan-ready state
`hScanReady` (a `ScanSt` at `c60` for index `0` over the post-spill memory `m9`,
the `FrameRepr`/geometry transported to `m9`, and the seven spill reads over `m9`)
— discharges ALL of:

  from-`c60` first body (`scan_iter_from_c60`) ≫ register-carrying scan-to-HIT
  loop (`scan_from_c5c_to_hit`) ≫ `AtHit → HitTailSt` repackaging
  (`hitAt_to_hitTail`) ≫ verified HIT tail (`env_get_hit_tail`),

reaching `PC = r`, `a0 = 1`, `x1 = r`, `sp` popped, callee-saveds restored, and
`*out = ValueRepr (f.vars[iHit].2)` at the first-match index `iHit`.

The ONE remaining residual is `hScanReady`: the memory-transport of the
`FrameRepr`/`ScanNames`/geometry from the entry memory `m0` across the prologue's
seven callee-saved spills into `[sp0-64, sp0)` to the scan memory `m9`.  The
prologue proves `∀ a ∉ [sp0-64, sp0), m9[a]? = m0[a]?`; the transport is exactly
the arena-vs-stack disjointness of the frame footprint (header + names/values
arrays + name/value payload strings), a pure byte-agreement rewrite of the reads.
Every MACHINE piece — prologue, the whole scan, the HIT-tail — is discharged. -/
theorem env_get_found_uncond'
    (env name out r sp0 : BitVec 64) (r0 r8 r9 r18 r19 r20 r21 : BitVec 64) (len pn : Nat)
    (nameStr : String) (iw : Nat)
    (f : Vsa.While.Frame) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (c : Config)
    (hFS : FoundSt env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn nameStr iw f N φf φc m0 c)
    -- the post-prologue scan-ready bundle over `m9` (the memory-transport residual)
    (hScanReady : ∀ (c60 : Config) (m9 : Mem),
      c60.σ.regs.get? Register.PC = some (0x80002c60#64 : BitVec 64) →
      c60.σ.regs.get? Register.x20 = some env → c60.σ.regs.get? Register.x19 = some name →
      c60.σ.regs.get? Register.x21 = some out →
      c60.σ.regs.get? Register.x18 = some (BitVec.ofNat 64 len) →
      c60.σ.regs.get? Register.x9 = some (BitVec.ofNat 64 pn) →
      c60.σ.regs.get? Register.x8 = some (0#64 : BitVec 64) →
      c60.σ.regs.get? Register.x1 = some r0 → c60.σ.regs.get? Register.x2 = some (sp0 - 64#64) →
      c60.σ.mem = m9 → GoodState c60.σ → c60.tick < 2 → Env_getLoaded m9 →
      read64 m9 ((sp0 - 64#64).toNat + 56) = some r0.toNat →
      read64 m9 ((sp0 - 64#64).toNat + 48) = some r8.toNat →
      read64 m9 ((sp0 - 64#64).toNat + 40) = some r9.toNat →
      read64 m9 ((sp0 - 64#64).toNat + 32) = some r18.toNat →
      read64 m9 ((sp0 - 64#64).toNat + 24) = some r19.toNat →
      read64 m9 ((sp0 - 64#64).toNat + 16) = some r20.toNat →
      read64 m9 ((sp0 - 64#64).toNat + 8) = some r21.toNat →
      (∀ a : Nat,
        ¬ ((sp0 - 64#64).toNat ≤ a ∧ a < (sp0 - 64#64).toNat + 64) →
          m9[a]? = m0[a]?) →
      -- the scan-ready package over m9:
      ∃ (g0 : (R : Register) → Option (RegisterType R)),
        ScanSt g0 (0x80002c60#64) env name out (BitVec.ofNat 64 len) (BitVec.ofNat 64 pn)
          r0 (sp0 - 64#64) 0 f nameStr N φf φc m9 c60 ∧
        FrameRepr m9 N φf φc env.toNat f ∧ Env_getLoaded m9 ∧
        (∀ pv, read64 m9 (env.toNat + 16) = some pv →
          ∀ i, i < f.vars.length →
            (∃ w0 w1 w2, read64 m9 (pv + 24 * i) = some w0 ∧ read64 m9 (pv + 24 * i + 8) = some w1 ∧
              read64 m9 (pv + 24 * i + 16) = some w2) ∧
            0x80000000 ≤ pv + 24 * i ∧ pv + 24 * i + 24 ≤ 0x100000000 ∧
            tohostAddr + 16 ≤ pv + 24 * i ∧ (pv + 24 * i) % 8 = 0 ∧ pv + 24 * i + 24 < 2^64 ∧
            pv + 24 * i < 2^64 ∧
            (pv + 24 * i + 24 ≤ out.toNat ∨ out.toNat + 24 ≤ pv + 24 * i) ∧
            (∀ (p : Nat) (s : String), read64 m9 (pv + 24 * i + 8) = some p →
              ∀ k, k ≤ s.length → (p + k < out.toNat ∨ out.toNat + 24 ≤ p + k)))) :
    ∃ (c' : Config) (m' : Mem) (iHit : Nat) (hi : iHit < f.vars.length),
      Steps c c' ∧ GoodState c'.σ ∧ c'.tick < 2 ∧
      c'.σ.regs.get? Register.PC = some r ∧
      c'.σ.regs.get? Register.x10 = some (1#64 : BitVec 64) ∧
      c'.σ.regs.get? Register.x1 = some r ∧
      c'.σ.regs.get? Register.x2 = some ((sp0 - 64#64) + 64#64) ∧
      c'.σ.regs.get? Register.x8 = some r8 ∧
      c'.σ.regs.get? Register.x9 = some r9 ∧
      c'.σ.regs.get? Register.x18 = some r18 ∧
      c'.σ.regs.get? Register.x19 = some r19 ∧
      c'.σ.regs.get? Register.x20 = some r20 ∧
      c'.σ.regs.get? Register.x21 = some r21 ∧
      c'.σ.mem = m' ∧ Env_getLoaded m' ∧
      ValueRepr m' N φc out.toNat (f.vars[iHit]'hi).2 := by
  -- run the verified prologue to the body entry `c60`
  obtain ⟨c60, m9, hsP, hGP, htickP, hpcP, h20P, h19P, h21P, h18P, h9P, h8P, hraP, hspP,
    hmemP, hcodeP, s56, s48, s40, s32, s24, s16, s8, houtside, _hsout⟩ :=
    env_get_prologue env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn f N φf φc m0 c hFS.base
  -- unpack the scan-ready bundle over m9
  obtain ⟨g0, hSt60, hframe9, hloaded9, hgeom9⟩ :=
    hScanReady c60 m9 hpcP h20P h19P h21P h18P h9P h8P hraP hspP hmemP hGP htickP hcodeP
      s56 s48 s40 s32 s24 s16 s8 houtside
  -- normalize `0 < f.vars.length` (iw witnesses it)
  have h0lt : 0 < f.vars.length := Nat.lt_of_le_of_lt (Nat.zero_le iw) hFS.iwLt
  -- run the from-c60 first body: HIT (i=0) or MISS (advance to ScanSt@c5c i=1)
  obtain ⟨c1, hs1, hdisj1⟩ :=
    scan_iter_from_c60 g0 env name out (BitVec.ofNat 64 len) (BitVec.ofNat 64 pn) r0
      (sp0 - 64#64) 0 f nameStr N φf φc m9 c60 hSt60 (by intro j hj hji; omega) h0lt
  -- reach a register-carrying HitAt at the first-match index
  obtain ⟨cHit, iHit, hsHit, hHit⟩ :
      ∃ (cHit : Config) (iHit : Nat), Steps c60 cHit ∧
        HitAt env out (sp0 - 64#64) iHit f nameStr m9 cHit := by
    rcases hdisj1 with ⟨g1, hSt1, hfm1⟩ | hHit0
    · -- MISS at 0: slot 0 differed, so iw ≠ 0 ⇒ 1 ≤ iw
      have h1le : 1 ≤ iw := by
        rcases Nat.eq_zero_or_pos iw with h | h
        · subst h; exact absurd hFS.iwHit (hfm1 0 h0lt (by omega))
        · omega
      -- continue the loop from ScanSt@c5c at index 1
      obtain ⟨cHit, iHit, hs2, hHit⟩ :=
        scan_from_c5c_to_hit env name out (BitVec.ofNat 64 len) (BitVec.ofNat 64 pn) (sp0 - 64#64)
          f nameStr N φf φc m9 iw hFS.iwLt hFS.iwHit iw g1 1 c1 hSt1 hfm1 h1le (by omega)
      exact ⟨cHit, iHit, hs1.trans hs2, hHit⟩
    · exact ⟨c1, 0, hs1, hHit0⟩
  -- repackage AtHit → HitTailSt
  obtain ⟨pv, w0, w1, w2, hHitTail⟩ :=
    hitAt_to_hitTail env name out r sp0 r0 r8 r9 r18 r19 r20 r21 len pn nameStr iw iHit
      f N φf φc m0 m9 cHit c hFS hframe9 hHit.mem.symm hHit hloaded9
      (fun pv hpv => hgeom9 pv hpv iHit hHit.ilt) s56 s48 s40 s32 s24 s16 s8
  -- run the verified HIT tail
  obtain ⟨c', m', hsT, hG, htick, hpc, ha0, hra, hsp', hx8, hx9, hx18, hx19, hx20, hx21,
    hmem', hcode', hvr, _, _⟩ :=
    env_get_hit_tail (cHit.σ.regs.get?) env out (sp0 - 64#64) r r0 r8 r9 r18 r19 r20 r21 iHit pv w0 w1 w2
      f N φf φc m9 cHit hHit.ilt hHitTail
  exact ⟨c', m', iHit, hHit.ilt, (hsP.trans hsHit).trans hsT, hG, htick, hpc, ha0, hra, hsp',
    hx8, hx9, hx18, hx19, hx20, hx21, hmem', hcode', hvr⟩

#print axioms scan_iter_from_c60
#print axioms scan_iter_hit
#print axioms scan_from_c5c_to_hit
#print axioms hitAt_to_hitTail
#print axioms env_get_found_uncond'

end Vsa.Sim
