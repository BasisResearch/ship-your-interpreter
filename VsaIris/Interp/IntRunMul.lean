import VsaIris.Interp.IntOpRuns

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

#ix_seg IntOp.mulRun1 : IntOpRun .mul (fun _ _ => True) (fun a b => wrap64 (a * b)) 0x8000387c#64 by
  int_pre 0x80003834
#ix_piece IntOp.mulRun2 from IntOp.mulRun1 by
  ix_run hlive using [h8, h2, h9, h19, hop, hKL, hKR, hsf] at 0x80003870
#ix_piece IntOp.mulRun3 from IntOp.mulRun2 by
  refine iw_jal 0x80003870 _ _ (jalx_80003870 live (fun p hp => hlive _ ((interp_code (by decide)) p hp)))
    (interp_code (by decide)) rfl ?_
  refine mul_iw hlive u1 w1 0x80003874#64 _ _ (by reg_close) (by reg_close)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, Nat.reduceAdd]) (by decide)
    (fun R' hq hkeep => ?_)
  have h9' : R' 9 = sret := by rw [hkeep 9 (by decide) (by decide) (by decide) (by decide)]; reg_close
  ix_run hlive using [h9', hsf] at 0x8000387c
  int_helper_post (by rw [hq, toInt_mul_wrap, hw1, hu1, Int.mul_comm])
#ix_tree IntOp.mulRun := IntOp.mulRun1 [IntOp.mulRun2 [IntOp.mulRun3]]

theorem epi_80003880 : EpiRun 0x80003880#64 := by epi_run

end VsaIris.Interp
