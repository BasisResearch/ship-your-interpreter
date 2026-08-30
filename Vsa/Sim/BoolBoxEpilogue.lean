import Vsa.Sim.BinopTailGen
import Vsa.Sim.BoxSuffixSeams

/-!
# `BoolBoxEpilogue` — the `value_bool` box variant of `intBoxEpilogue`

A faithful clone of `intBoxEpilogue` (`BinopTailGen.lean`) swapping the `value_int`
box for the `value_bool` box.  From the `value_bool` entry config `τ0` (payload `pay`
= the boolean word in `x11`, `sret` in `x10`/`x9`, `boxLink` in `x1`,
`PC = 0x800027f8`) it runs

  `value_bool (call) ; ld s3,0x418(sp) ; j 0x800033ec`  →  `PreEpilogueVD`

and packages `PreEpilogueVD` (via `intPostToEpilogue`, which takes `v : Value`
generically) for the boxed value `.bool bres`.

The suffix (`ld s3,0x418(sp) ; j 0x800033ec`), the geometry, and `intPostToEpilogue`
are op-agnostic.  The `.bool`-specific pieces are ONLY: the `value_bool_box` call,
`boxBool_pre`/`boxBool_post`, `BoolRegion`, entry PC `0x800027f8`, and the `.bool bres`
value.  Shared by `eq`/`ne`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

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

/-- **The shared bool-box value-tail epilogue** (`value_bool` clone of
`intBoxEpilogue`).

From the `value_bool` entry config `τ0` (`pay` = boolean word in `x11`,
`sret` in `x10`/`x9`, `boxLink` in `x1`, `sp-1088` in `x2`, `PC = 0x800027f8`,
`tick<2`, `sailOutput = out0`, `Value_boolLoaded τ0.mem`) plus the transport
hypotheses both arms establish, run `value_bool_box ≫ ld s3,0x418(sp) ≫ j 0x800033ec`
and package `PreEpilogueVD` at `0x800033ec` for the boxed value `.bool bres`. -/
theorem boolBoxEpilogue
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc φfm φcm φf' φc' : Addr → Nat)
    (nf nc nf2 nc2 : Nat)
    (st' st'' : Vsa.While.St)
    (sp r sret : BitVec 64) (v8 v9 v18 v19 w19 : BitVec 64) (pay : BitVec 64)
    (bres : Bool) (out0 : Array String)
    (m0 : Mem) (τ0 : Config) (boxLink : BitVec 64)
    (ldPC jPC : BitVec 64) (jImm : BitVec 21)
    (ldS3 : LdS3Site ldPC) (jExit : JExitSite jPC jImm)
    -- suffix PC / target facts
    (hboxLink : boxLink = ldPC)
    (hldPCupdate : BitVec.update (ldPC + sign_extend (m := 64) (0x000#12)) 0 0#1 = ldPC)
    (hldAfter : BitVec.addInt ldPC 4 = jPC)
    (hjTgt : (jPC + sign_extend (m := 64) jImm) = (0x800033ec#64 : BitVec 64))
    (hjTgtAl : (jPC + sign_extend (m := 64) jImm).toNat % 4 = 0)
    (hldPCeq : ((sp - 1088#64) + sign_extend (m := 64) (0x418#12)).toNat = sp.toNat - 40)
    -- === `value_bool` entry `τ0` (boxBool_pre pieces; ghost := τ0-snapshot internally) ===
    (hGτ0 : GoodState τ0.σ) (hVboolτ0 : Value_boolLoaded τ0.σ.mem)
    (hpcτ0 : τ0.σ.regs.get? Register.PC = some (0x800027f8#64))
    (hx10τ0 : τ0.σ.regs.get? Register.x10 = some sret)
    (hx11τ0 : τ0.σ.regs.get? Register.x11 = some pay)
    (hlinkτ0 : τ0.σ.regs.get? Register.x1 = some boxLink)
    (hs1τ0 : τ0.σ.regs.get? Register.x9 = some sret)
    (hspτ0 : τ0.σ.regs.get? Register.x2 = some (sp - 1088#64))
    (hminτ0 : ∃ v, τ0.σ.regs.get? Register.minstret = some v)
    (htickτ0 : τ0.tick < 2) (houtτ0 : τ0.σ.sailOutput = out0)
    (hcodeτ0 : Eval_exprLoaded τ0.σ.mem)
    (hBoolRegion : BoolRegion sret)
    (hlinkAl : (BitVec.update (boxLink + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    -- boxed-value bridge
    (hval_bridge : (pay != 0#64) = bres)
    -- === the arm's transport of `τ0.σ.mem` back to `c`/`m0`/store/geometry ===
    -- φ-extension chain
    (hpfm : PhiExtends φf φfm nf)
    (hpcm : PhiExtends φc φcm nc)
    (hpf' : PhiExtends φfm φf' nf2)
    (hpc' : PhiExtends φcm φc' nc2)
    (houtStr : String.join out0.toList = st''.out)
    -- store survival outside SL (from τ0.mem)
    (hSurvSL0 : ∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → τ0.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st''.store)
    -- the s3 restore slot at τ0 holds entry `w19`
    (hs3τ0 : read64 τ0.σ.mem (sp.toNat - 40) = some w19.toNat)
    -- four callee-saved spill reads at τ0 (survive value_bool's [sret,+24) write)
    (hslotRa0 : read64 τ0.σ.mem (sp.toNat - 8) = some r.toNat)
    (hslotS00 : read64 τ0.σ.mem (sp.toNat - 16) = some v8.toNat)
    (hslotS10 : read64 τ0.σ.mem (sp.toNat - 24) = some v9.toNat)
    (hslotS20 : read64 τ0.σ.mem (sp.toNat - 32) = some v18.toNat)
    -- entry ghost frame values (+ x19 = v19, w19 = v19)
    (hgv8 : g Register.x8 = some v8) (hgv9 : g Register.x9 = some v9)
    (hgv18 : g Register.x18 = some v18) (hgv2 : g Register.x2 = some sp)
    (hgx19 : g Register.x19 = some v19) (hw19 : w19 = v19)
    -- frame collapse to `g` for R ≠ x19 (threaded by the arm through its front + callees)
    (hframeGτ0 : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      (Register.x19 == R) = false → τ0.σ.regs.get? R = g R)
    -- memory frame vs entry m0
    (hMemExt0 : MemExtends m0 τ0.σ.mem)
    (hmemframe0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ τ0.σ.mem[a]? = m0[a]?)
    -- geometry the epilogue + s3-restore need
    (hsretEvalCode : sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat)
    (hsretStk : sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat)
    (hsretInSL : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi)
    (hSLlo40 : SL.lo ≤ sp.toNat - 40) (hSLlo32 : SL.lo ≤ sp.toNat - 32)
    (hsp1088 : 1088 ≤ sp.toNat) (hspRam : sp.toNat ≤ 0x100000000)
    (hspLo : 0x80000000 ≤ sp.toNat) (hspHtif : tohostAddr + 16 + 1088 ≤ sp.toNat)
    (hsp8 : sp.toNat % 8 = 0) (hraAl : r.toNat % 4 = 0)
    -- ld-slot geometry (bounds for the ld site's side conditions, from Phase-0 bundle)
    (hldLo : 0x80000000 ≤ (sp.toNat - 40))
    (hldHiRam : (sp.toNat - 40) + 8 ≤ 0x100000000)
    (hldHtif : (sp.toNat - 40) + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (sp.toNat - 40))
    (hldAl : (sp.toNat - 40) % 8 = 0) :
    ∃ (mpre : Mem) (φfm' φcm' φfe φce : Addr → Nat)
      (cfin : Config),
      Steps τ0 cfin ∧
      PhiExtends φf φfm' nf ∧
      PhiExtends φc φcm' nc ∧
      PhiExtends φfm' φfe nf2 ∧
      PhiExtends φcm' φce nc2 ∧
      PreEpilogueVD g N A SL φfe φce st'' (.bool bres) sp r sret v8 v9 v18 out0 m0 mpre cfin := by
  -- === value_bool callee (via value_bool_box): buf = sret, vb = pay, ghost = τ0 snapshot ===
  have hcallpre : boxBool_pre (fun R => τ0.σ.regs.get? R) sret pay boxLink τ0.σ.mem out0 τ0 := by
    refine ⟨hGτ0, hVboolτ0, rfl, hpcτ0, hx10τ0, hx11τ0, hlinkτ0, hminτ0, htickτ0, hBoolRegion,
      hlinkAl, houtτ0, fun R _ => rfl⟩
  obtain ⟨cvi, hsvi, hpost⟩ :=
    value_bool_box (fun R => τ0.σ.regs.get? R) sret pay boxLink N φc' τ0.σ.mem out0 τ0 hcallpre
  obtain ⟨hGvi, hpcvi, hx10vi, hravi, ⟨vmivi, hmivi⟩, htickvi, hvalvi, houtvi,
      hmemframevi, hpresvi, hframevi⟩ := hpost
  have hTopW := topSlotWin (by omega : (32 : Nat) ≤ sp.toNat)
  have hvalfinal : ValueRepr cvi.σ.mem N φc' sret.toNat (.bool bres) := by
    rw [← hval_bridge]; exact hvalvi
  have hpcvi' : cvi.σ.regs.get? Register.PC = some ldPC := by
    rw [hpcvi, hboxLink, hldPCupdate]
  have hcode_vi : Eval_exprLoaded cvi.σ.mem :=
    loaded_eval_expr_agreeP τ0.σ.mem cvi.σ.mem
      (fun k hk => hmemframevi k (notInSret_of_inRegion hsretEvalCode hk)) hcodeτ0
  have hs1_vi : cvi.σ.regs.get? Register.x9 = some sret := by
    rw [hframevi Register.x9 (by decide)]; exact hs1τ0
  have hsp_vi : cvi.σ.regs.get? Register.x2 = some (sp - 1088#64) := by
    rw [hframevi Register.x2 (by decide)]; exact hspτ0
  -- === s3 restore slot [sp-40, sp-32): survives value_bool's [sret,+24) write ===
  have hs3vi : read64 cvi.σ.mem (sp.toNat - 40) = some w19.toNat := by
    rw [← read64_agreeP (P := fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat - 32)
      (a := sp.toNat - 40) (m := τ0.σ.mem) (m' := cvi.σ.mem)
      (fun k hk => hmemframevi k (notInSret_of_frameWin hsretStk hSLlo40 (Nat.sub_le _ _) hk))
      (fun k hk => ⟨by omega, by omega⟩)]
    exact hs3τ0
  obtain ⟨s3b0, s3b1, s3b2, s3b3, s3b4, s3b5, s3b6, s3b7, hs3b0, hs3b1, hs3b2, hs3b3, hs3b4, hs3b5, hs3b6, hs3b7, hs3rec⟩ :=
    read64_bytes cvi.σ.mem (sp.toNat - 40) w19.toNat hs3vi
  -- === ld s3,0x418(sp) → x19 := w19 (restore entry s3) ===
  obtain ⟨τ4, j4, ht4, hj4, hGτ4, hmemτ4, hoτ4⟩ :=
    ldS3 cvi.σ cvi.tick cvi.steps ldPC vmivi (sp - 1088#64)
      s3b0 s3b1 s3b2 s3b3 s3b4 s3b5 s3b6 s3b7 hGvi hpcvi' hmivi hsp_vi hcode_vi rfl
      (by rw [hldPCeq]; exact hldLo) (by rw [hldPCeq]; exact hldHiRam)
      (by rw [hldPCeq]; exact hldHtif) (by rw [hldPCeq]; exact hldAl)
      (by rw [hldPCeq]; exact hs3b0) (by rw [hldPCeq]; exact hs3b1)
      (by rw [hldPCeq]; exact hs3b2) (by rw [hldPCeq]; exact hs3b3)
      (by rw [hldPCeq]; exact hs3b4) (by rw [hldPCeq]; exact hs3b5)
      (by rw [hldPCeq]; exact hs3b6) (by rw [hldPCeq]; exact hs3b7) htickvi
  have hstepτ4 : Step cvi ⟨τ4, j4, cvi.steps + 1⟩ := by cases cvi; exact ht4
  have hmemτ4e : τ4.mem = cvi.σ.mem := hmemτ4
  have hpcτ4 : τ4.regs.get? Register.PC = some jPC := by
    have := obs_alu_pc hoτ4; rwa [hldAfter] at this
  have hx19τ4 : τ4.regs.get? Register.x19 = some w19 := by
    have := obs_alu_rd hoτ4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64) ((((((((s3b7.append s3b6).append s3b5).append s3b4).append s3b3).append s3b2).append s3b1).append s3b0) : BitVec (8*8))) = w19 from by
      apply BitVec.eq_of_toNat_eq; rw [sext_full, word8_toNat_recon, hs3rec]] at this
  have hs1τ4 : τ4.regs.get? Register.x9 = some sret := obs_alu_other hoτ4 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_vi
  have hspτ4 : τ4.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_vi
  obtain ⟨vmiτ4, hmiτ4⟩ := obs_alu_minstret hoτ4
  have houtτ4 : τ4.sailOutput = out0 := by rw [hoτ4.out, sailOutput_sigmaPost_alu]; exact houtvi
  have hcodeτ4 : Eval_exprLoaded τ4.mem := by rw [hmemτ4e]; exact hcode_vi
  -- === j 0x800033ec → shared epilogue entry ===
  obtain ⟨τ5, j5, ht5, hj5, hGτ5, hmemτ5, hoτ5⟩ :=
    jExit τ4 j4 (cvi.steps + 1) jPC vmiτ4 hGτ4 hpcτ4 hmiτ4 hcodeτ4 rfl hjTgtAl hj4
  have hstepτ5 : Step ⟨τ4, j4, cvi.steps + 1⟩ ⟨τ5, j5, cvi.steps + 1 + 1⟩ := ht5
  have hmemτ5e : τ5.mem = cvi.σ.mem := by rw [hmemτ5]; exact hmemτ4e
  have hpc_fin : τ5.regs.get? Register.PC = some (0x800033ec#64) := by
    have := obs_jr_pc hoτ5; rwa [hjTgt] at this
  have hs1_fin : τ5.regs.get? Register.x9 = some sret := obs_jr_other hoτ5 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ4
  have hsp_fin : τ5.regs.get? Register.x2 = some (sp - 1088#64) := obs_jr_other hoτ5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ4
  have hx19_fin : τ5.regs.get? Register.x19 = some w19 := obs_jr_other hoτ5 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx19τ4
  obtain ⟨vmifin, hmifin⟩ := obs_jr_minstret hoτ5
  have hout_fin : τ5.sailOutput = out0 := by rw [hoτ5.out, sailOutput_sigmaPost_jump_x0]; exact houtτ4
  have hcode_fin : Eval_exprLoaded τ5.mem := by rw [hmemτ5e]; exact hcode_vi
  -- === ASSEMBLE PreEpilogueVD at 0x800033ec ===
  -- τ5.mem = cvi.mem = value_bool(τ0.mem).  Agreement outside SL:
  have hSLfin : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → τ0.σ.mem[k]? = τ5.mem[k]? := by
    intro k hk
    rw [hmemτ5e, ← hmemframevi k (notInSret_of_notInSL hsretInSL hk)]
  have hstore_fin : StoreRepr τ5.mem N A φf' φc' st''.store :=
    hSurvSL0 τ5.mem (fun k hk => hSLfin k hk)
  have hSurvSL_fin : ∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → τ5.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st''.store :=
    fun m' hm' => hSurvSL0 m' (fun k hk => (hSLfin k hk).trans (hm' k hk))
  have hMemExt_0_5 : MemExtends τ0.σ.mem τ5.mem := by
    intro k bb hbb; rw [hmemτ5e]; exact hpresvi k bb hbb
  have hMemExt_fin : MemExtends m0 τ5.mem := hMemExt0.trans hMemExt_0_5
  -- Agreement on the top slots [sp-32, sp): survives value_bool's [sret,+24) write.
  have hAgTop : AgreeP (fun k => sp.toNat - 32 ≤ k ∧ k < sp.toNat) τ0.σ.mem τ5.mem := by
    intro k hk
    rw [hmemτ5e, ← hmemframevi k (notInSret_of_frameWin hsretStk hSLlo32 (Nat.le_refl _) hk)]
  have hslotRa_f : read64 τ5.mem (sp.toNat - 8) = some r.toNat := by
    rw [← read64_agreeP hAgTop hTopW.1]; exact hslotRa0
  have hslotS0_f : read64 τ5.mem (sp.toNat - 16) = some v8.toNat := by
    rw [← read64_agreeP hAgTop hTopW.2.1]; exact hslotS00
  have hslotS1_f : read64 τ5.mem (sp.toNat - 24) = some v9.toNat := by
    rw [← read64_agreeP hAgTop hTopW.2.2.1]; exact hslotS10
  have hslotS2_f : read64 τ5.mem (sp.toNat - 32) = some v18.toNat := by
    rw [← read64_agreeP hAgTop hTopW.2.2.2]; exact hslotS20
  -- callee-saved (noise) frame: collapse the suffix (ld;j;value_bool) to τ0, then τ0 → g.
  have hframeG : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      τ5.regs.get? R = g R := by
    intro R hR he8 he9 he18 he2
    obtain ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    have hR' : AbiPreservedNoise R := ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    have ne : ∀ {X : Register}, AbiPreserved X = false → (X == R) = false := by
      intro X hX
      rcases hXR : (X == R) with _ | _
      · rfl
      · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hab; exact absurd hab (by decide)
    by_cases hx19R : Register.x19 = R
    · subst hx19R
      have : τ5.regs.get? Register.x19 = some w19 := hx19_fin
      rw [this, hw19]; exact hgx19.symm
    · have h19ne : (Register.x19 == R) = false := by
        rcases hXR : (Register.x19 == R) with _ | _
        · rfl
        · rw [beq_iff_eq] at hXR; exact absurd hXR hx19R
      -- collapse: τ5 ← τ4 ← cvi ← τ0 (value_bool frame), then τ0 → g via hframeGτ0.
      have f_5 : τ5.regs.get? R = τ4.regs.get? R :=
        (hoτ5.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')
      have f_4 : τ4.regs.get? R = cvi.σ.regs.get? R :=
        (hoτ4.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' h19ne hnpc' hmii')
      have fvi : cvi.σ.regs.get? R = τ0.σ.regs.get? R :=
        hframevi R ⟨ne (by decide), ne (by decide), hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
      rw [f_5, f_4, fvi]
      exact hframeGτ0 R hR' he8 he9 he18 he2 h19ne
  have hmemframe_fin : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ τ5.mem[a]? = m0[a]? := by
    intro a ha hA
    by_cases hsr : sret.toNat ≤ a ∧ a < sret.toNat + 24
    · exact Or.inl hsr
    · refine Or.inr ?_
      rw [hmemτ5e, ← hmemframevi a hsr]
      rcases hmemframe0 a ha hA with h | h
      · exact absurd h hsr
      · exact h
  -- the full Steps chain τ0 → τ5
  have hchain : Steps τ0 ⟨τ5, j5, cvi.steps + 1 + 1⟩ :=
    hsvi.trans <| (Steps.single hstepτ4).trans (Steps.single hstepτ5)
  obtain ⟨mpre, φfm2, φcm2, φfe, φce, hp1, hp2, hp3, hp4, hPre⟩ :=
    intPostToEpilogue g N A SL φf φc φfm φcm φf' φc' nf nc nf2 nc2 st' st'' (.bool bres)
      sp r sret v8 v9 v18 out0 m0 ⟨τ5, j5, cvi.steps + 1 + 1⟩
      hpfm hpcm hpf' hpc' hGτ5 hj5 hpc_fin hs1_fin hsp_fin ⟨vmifin, hmifin⟩
      hout_fin houtStr hcode_fin (by rw [hmemτ5e]; exact hvalfinal) hstore_fin hSurvSL_fin
      hframeG hslotRa_f hslotS0_f hslotS1_f hslotS2_f hgv8 hgv9 hgv18 hgv2
      hMemExt_fin hmemframe_fin hsp1088 hspRam hspLo hspHtif hsp8 hraAl
  exact ⟨mpre, φfm2, φcm2, φfe, φce, ⟨τ5, j5, cvi.steps + 1 + 1⟩, hchain, hp1, hp2, hp3, hp4, hPre⟩

#print axioms boolBoxEpilogue

end Vsa.Sim
