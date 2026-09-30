import VsaIris.Interp.IntOpRuns

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

#ix_seg IntOp.divRun1 : IntOpRun .div (fun _ b => b ≠ 0) (fun a b => wrap64 (a.tdiv b)) 0x80003828#64 by
  int_pre_nz 0x800037dc
#ix_piece IntOp.divRun2 from IntOp.divRun1 by
  ix_run hlive using [h8, h2, h9, h19, hop, hKL, hKR, hsf] at 0x8000381c
#ix_piece IntOp.divRun3 from IntOp.divRun2 by
  refine iw_jal 0x8000381c _ _ (jalx_8000381c live (fun p hp => hlive _ ((interp_code (by decide)) p hp)))
    (interp_code (by decide)) rfl ?_
  refine divdi3_iw hlive w1 u1 0x80003820#64 _ _ hy (by reg_close) (by reg_close)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, Nat.reduceAdd]) (by decide)
    (fun R' hq hkeep => ?_)
  have h9' : R' 9 = sret := by
    rw [hkeep 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; reg_close
  ix_run hlive using [h9', hsf] at 0x80003828
  int_helper_post (by rw [hq, hw1, hu1])
#ix_tree IntOp.divRun := IntOp.divRun1 [IntOp.divRun2 [IntOp.divRun3]]

theorem epi_8000382c : EpiRun 0x8000382c#64 := by epi_run

#ix_seg IntOp.modRun1 : IntOpRun .mod (fun _ b => b ≠ 0) (fun a b => wrap64 (a.tmod b)) 0x800037d0#64 by
  int_pre_nz 0x80003784
#ix_piece IntOp.modRun2 from IntOp.modRun1 by
  ix_run hlive using [h8, h2, h9, h19, hop, hKL, hKR, hsf] at 0x800037c4
#ix_piece IntOp.modRun3 from IntOp.modRun2 by
  refine iw_jal 0x800037c4 _ _ (jalx_800037c4 live (fun p hp => hlive _ ((interp_code (by decide)) p hp)))
    (interp_code (by decide)) rfl ?_
  refine moddi3_iw hlive w1 u1 0x800037c8#64 _ _ hy (by reg_close) (by reg_close)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, Nat.reduceAdd]) (by decide)
    (fun R' hq hkeep => ?_)
  have h9' : R' 9 = sret := by
    rw [hkeep 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; reg_close
  ix_run hlive using [h9', hsf] at 0x800037d0
  int_helper_post (by rw [hq, hw1, hu1])
#ix_tree IntOp.modRun := IntOp.modRun1 [IntOp.modRun2 [IntOp.modRun3]]

theorem epi_800037d4 : EpiRun 0x800037d4#64 := by epi_run

end VsaIris.Interp
