import VsaIris.Interp.Abort
import VsaIris.Vsa.AluStep
import Vsa.Sim.JmpSites

/-!
# `runtime_error` and `longjmp`: an error aborts (H5)

`runtime_error(in, line, fmt, a1, a2)` (`0x80002da8`) formats the message into
a stack buffer, formats `"runtime error [line %d]: %s"` into `in->err_msg`
(both through `IrisHoles.newlib.snprintf`), and calls
`longjmp(in->on_error, 1)`, which restores `ra`, `s0`–`s11` and `sp` from the
`jmp_buf` and returns 1 to `interp_run`'s `setjmp` return. It never returns
to its caller: its `fnSpecAbort` has an empty return branch and hands the
abort branch the `longjmp` landing (`landingCore`) with its whole stack region.

```
80002da8: addi sp,sp,-224; sd s0,208(sp); sd s1,200(sp); mv s0,a0; mv s1,a1;
          mv a0,sp; li a1,192; sd ra,216(sp)
80002dc8: jal snprintf                     body = snprintf(sp, 192, fmt, a1, a2)
80002dcc: li a1,256; mv a4,sp; mv a3,s1; addi a0,s0,224; auipc a2; addi a2
80002de4: jal snprintf                     snprintf(err_msg, 256, fmt2, line, body)
80002de8: addi a0,s0,16; li a1,1
80002df0: jal longjmp
8000703c: ld ra,0(a0) … ld s11,96(a0); ld sp,104(a0)
80007074: seqz a0,a1                       (observed ALU step: no `sltiu` in `MKind`)
80007078: add a0,a0,a1; ret
```
-/

namespace VsaIris.Newlib.RtErr

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Sim VsaIris.Inst VsaIris.Interp VsaIris.Stdio VsaIris.Newlib.Sites
  VsaIris.Newlib.Exit VsaIris.Newlib.MainErr VsaIris.Newlib.Landing

/-! ## Segments -/

#derive_case rtASeg chain
  [(0x80002da8#64, 0xf2010113#32),
   (0x80002dac#64, 0x0c813823#32),
   (0x80002db0#64, 0x0c913423#32),
   (0x80002db4#64, 0x00050413#32),
   (0x80002db8#64, 0x00058493#32),
   (0x80002dbc#64, 0x00010513#32),
   (0x80002dc0#64, 0x0c000593#32),
   (0x80002dc4#64, 0x0c113c23#32)]

#derive_case rtBSeg chain
  [(0x80002dcc#64, 0x10000593#32),
   (0x80002dd0#64, 0x00010713#32),
   (0x80002dd4#64, 0x00048693#32),
   (0x80002dd8#64, 0x0e040513#32),
   (0x80002ddc#64, 0x00016617#32),
   (0x80002de0#64, 0x53c60613#32)]

#derive_case rtCSeg chain
  [(0x80002de8#64, 0x01040513#32),
   (0x80002dec#64, 0x00100593#32)]

#derive_case lj1Seg chain
  [(0x8000703c#64, 0x00053083#32),
   (0x80007040#64, 0x00853403#32),
   (0x80007044#64, 0x01053483#32),
   (0x80007048#64, 0x01853903#32),
   (0x8000704c#64, 0x02053983#32),
   (0x80007050#64, 0x02853a03#32),
   (0x80007054#64, 0x03053a83#32),
   (0x80007058#64, 0x03853b03#32),
   (0x8000705c#64, 0x04053b83#32),
   (0x80007060#64, 0x04853c03#32),
   (0x80007064#64, 0x05053c83#32),
   (0x80007068#64, 0x05853d03#32),
   (0x8000706c#64, 0x06053d83#32),
   (0x80007070#64, 0x06853103#32)]

#derive_case lj2Seg chain
  [(0x80007078#64, 0x00b50533#32)] terminator ⟨0x8000707c#64, 0x00008067#32, 0x67#8, 0x80#8,
      0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

/-! ## Segment facts -/

/-- `runtime_error`'s stack: its 224-byte frame and `snprintf`'s scratch below. -/
def rtErrNeed : Nat := 224 + snprintfNeed

abbrev aL (s s0v s1v inp line r : BitVec 64) : GRegs :=
  [(2, s), (8, s0v), (9, s1v), (10, inp), (11, line), (1, r)]

/-- The frame below `s`, in RAM above the HTIF words, 16-aligned. -/
structure Frame224 (s : BitVec 64) : Prop where
  lo : Vsa.Sim.tohostAddr + 16 + 224 ≤ s.toNat
  hi : s.toNat ≤ 0x88000000
  align : s.toNat % 16 = 0

theorem frame_sub (s : BitVec 64) (h : Frame224 s) :
    (s + sign_extend (m := 64) (0xf20#12)).toNat = s.toNat - 224 := by
  have h1 := h.lo
  rw [show (sign_extend (m := 64) (0xf20#12) : BitVec 64) = -(224#64) by decide, ← BitVec.sub_eq_add_neg]
  exact toNat_sub_frame (by simp; unfold tohostAddr at h1; omega)

/-- An address `sp' + off` in `runtime_error`'s frame. -/
theorem sp_off (s : BitVec 64) (hg : Frame224 s) (off : Nat) (imm : BitVec 12)
    (himm : (sign_extend (m := 64) imm : BitVec 64).toNat = off) (hoff : off < 224) :
    ∀ x : BitVec 64, x = s + sign_extend (m := 64) (0xf20#12) + sign_extend (m := 64) imm →
      x.toNat = s.toNat - 224 + off := by
  intro x hx
  have hb := frame_sub s hg
  have h1 := hg.lo; have h2 := hg.hi
  unfold tohostAddr at h1
  rw [hx, addr_off _ _ off himm (by omega), hb]

theorem a_facts {m : Std.ExtHashMap Nat (BitVec 8)} {s s0v s1v inp line r : BitVec 64}
    (hcode : rtErrCodeLoaded m) (hg : Frame224 s) :
    ChainFacts m m (aL s s0v s1v inp line r) [] rtASeg := by
  have hb := frame_sub s hg
  have h1 := hg.lo; have h2 := hg.hi; have h3 := hg.align
  unfold tohostAddr at h1
  unfold rtASeg ChainFacts
  chain_facts hcode with "VsaIris.Newlib.Sites.rtErrCode_at_"
  · exact sdFact (ea := s.toNat - 224 + 208) rfl
      (sp_off s hg 208 (0x0d0#12) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (by unfold tohostAddr; omega) (by omega)
  · exact sdFact (ea := s.toNat - 224 + 200) rfl
      (sp_off s hg 200 (0x0c8#12) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (by unfold tohostAddr; omega) (by omega)
  · exact sdFact (ea := s.toNat - 224 + 216) rfl
      (sp_off s hg 216 (0x0d8#12) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (by unfold tohostAddr; omega) (by omega)

theorem a_log (s s0v s1v inp line r : BitVec 64) :
    (segOut rtASeg (aL s s0v s1v inp line r) []).log =
      [((s + sign_extend (m := 64) (0xf20#12) + sign_extend (m := 64) (0x0d0#12)).toNat, 8, s0v),
       ((s + sign_extend (m := 64) (0xf20#12) + sign_extend (m := 64) (0x0c8#12)).toNat, 8, s1v),
       ((s + sign_extend (m := 64) (0xf20#12) + sign_extend (m := 64) (0x0d8#12)).toNat, 8, r)] :=
  rfl

theorem a_pc (s s0v s1v inp line r : BitVec 64) :
    evalBlocksPC 0x80002da8#64 (SegEvalState.init (aL s s0v s1v inp line r) []) rtASeg =
      0x80002dc8#64 := rfl

theorem a_fin (s s0v s1v inp line r : BitVec 64) :
    finReg rtASeg (aL s s0v s1v inp line r) [] 2 = s + sign_extend (m := 64) (0xf20#12) ∧
    finReg rtASeg (aL s s0v s1v inp line r) [] 8 = inp ∧
    finReg rtASeg (aL s s0v s1v inp line r) [] 9 = line ∧
    finReg rtASeg (aL s s0v s1v inp line r) [] 10 = s + sign_extend (m := 64) (0xf20#12) ∧
    finReg rtASeg (aL s s0v s1v inp line r) [] 11 = 192#64 ∧
    finReg rtASeg (aL s s0v s1v inp line r) [] 1 = r := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl⟩
  · show inp + sign_extend (m := 64) (0x000#12) = _; exact addi0_env inp
  · show line + sign_extend (m := 64) (0x000#12) = _; exact addi0_env line
  · show (s + sign_extend (m := 64) (0xf20#12)) + sign_extend (m := 64) (0x000#12) = _
    exact addi0_env _
  · show 0#64 + sign_extend (m := 64) (0x0c0#12) = _; decide

abbrev bL (a1v a4v s' a3v line a0v inp a2v : BitVec 64) : GRegs :=
  [(11, a1v), (14, a4v), (2, s'), (13, a3v), (9, line), (10, a0v), (8, inp), (12, a2v)]

theorem b_facts {m : Std.ExtHashMap Nat (BitVec 8)} {a1v a4v s' a3v line a0v inp a2v : BitVec 64}
    (hcode : rtErrCodeLoaded m) :
    ChainFacts m m (bL a1v a4v s' a3v line a0v inp a2v) [] rtBSeg := by
  unfold rtBSeg ChainFacts
  chain_facts hcode with "VsaIris.Newlib.Sites.rtErrCode_at_"

theorem b_pc (a1v a4v s' a3v line a0v inp a2v : BitVec 64) :
    evalBlocksPC 0x80002dcc#64 (SegEvalState.init (bL a1v a4v s' a3v line a0v inp a2v) [])
      rtBSeg = 0x80002de4#64 := rfl

/-- `runtime_error`'s second format, `"runtime error [line %d]: %s"`. -/
def fmt2 : BitVec 64 := 0x80019318#64

theorem b_fin (a1v a4v s' a3v line a0v inp a2v : BitVec 64) :
    finReg rtBSeg (bL a1v a4v s' a3v line a0v inp a2v) [] 11 = 256#64 ∧
    finReg rtBSeg (bL a1v a4v s' a3v line a0v inp a2v) [] 14 = s' ∧
    finReg rtBSeg (bL a1v a4v s' a3v line a0v inp a2v) [] 2 = s' ∧
    finReg rtBSeg (bL a1v a4v s' a3v line a0v inp a2v) [] 13 = line ∧
    finReg rtBSeg (bL a1v a4v s' a3v line a0v inp a2v) [] 9 = line ∧
    finReg rtBSeg (bL a1v a4v s' a3v line a0v inp a2v) [] 10 =
      inp + sign_extend (m := 64) (0x0e0#12) ∧
    finReg rtBSeg (bL a1v a4v s' a3v line a0v inp a2v) [] 8 = inp ∧
    finReg rtBSeg (bL a1v a4v s' a3v line a0v inp a2v) [] 12 = fmt2 := by
  refine ⟨?_, ?_, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · show 0#64 + sign_extend (m := 64) (0x100#12) = _; decide
  · show s' + sign_extend (m := 64) (0x000#12) = _; exact addi0_env _
  · show line + sign_extend (m := 64) (0x000#12) = _; exact addi0_env _
  · show (0x80002ddc#64 + sign_extend (m := 64) ((0x00016#20) +++ (0x000#12))) +
      sign_extend (m := 64) (0x53c#12) = _
    decide

abbrev cL (a0v inp a1v : BitVec 64) : GRegs := [(10, a0v), (8, inp), (11, a1v)]

theorem c_facts {m : Std.ExtHashMap Nat (BitVec 8)} {a0v inp a1v : BitVec 64}
    (hcode : rtErrCodeLoaded m) : ChainFacts m m (cL a0v inp a1v) [] rtCSeg := by
  unfold rtCSeg ChainFacts
  chain_facts hcode with "VsaIris.Newlib.Sites.rtErrCode_at_"

theorem c_pc (a0v inp a1v : BitVec 64) :
    evalBlocksPC 0x80002de8#64 (SegEvalState.init (cL a0v inp a1v) []) rtCSeg = 0x80002df0#64 :=
  rfl

theorem c_fin (a0v inp a1v : BitVec 64) :
    finReg rtCSeg (cL a0v inp a1v) [] 10 = inp + sign_extend (m := 64) (0x010#12) ∧
    finReg rtCSeg (cL a0v inp a1v) [] 8 = inp ∧ finReg rtCSeg (cL a0v inp a1v) [] 11 = 1#64 :=
  ⟨rfl, rfl, by show 0#64 + sign_extend (m := 64) (0x001#12) = _; decide⟩

/-- The `jmp_buf` at `jbp`, in RAM above the HTIF words. -/
structure JbGeom (jbp : BitVec 64) : Prop where
  lo : Vsa.Sim.tohostAddr + 16 ≤ jbp.toNat
  hi : jbp.toNat + 112 ≤ 0x100000000

theorem jb_off (jbp : BitVec 64) (hg : JbGeom jbp) (off : Nat) (imm : BitVec 12)
    (himm : (sign_extend (m := 64) imm : BitVec 64).toNat = off) (hoff : off < 112) :
    ∀ x : BitVec 64, x = jbp + sign_extend (m := 64) imm → x.toNat = jbp.toNat + off := by
  intro x hx
  have h2 := hg.hi
  rw [hx, addr_off _ _ off himm (by omega)]

abbrev lj1L (jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2 : BitVec 64) : GRegs :=
  [(10, jbp), (1, v1), (8, v8), (9, v9), (18, v18), (19, v19), (20, v20), (21, v21), (22, v22), (23, v23), (24, v24), (25, v25), (26, v26), (27, v27), (2, v2)]

abbrev lj1Lds (jbp : BitVec 64) (jb : Nat → BitVec 8) : List (List (BitVec 8)) :=
  [imgWord jb (jbp.toNat + 0), imgWord jb (jbp.toNat + 8), imgWord jb (jbp.toNat + 16), imgWord jb (jbp.toNat + 24), imgWord jb (jbp.toNat + 32), imgWord jb (jbp.toNat + 40), imgWord jb (jbp.toNat + 48), imgWord jb (jbp.toNat + 56), imgWord jb (jbp.toNat + 64), imgWord jb (jbp.toNat + 72), imgWord jb (jbp.toNat + 80), imgWord jb (jbp.toNat + 88), imgWord jb (jbp.toNat + 96), imgWord jb (jbp.toNat + 104)]

theorem lj1_facts {m : Std.ExtHashMap Nat (BitVec 8)} {jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2 : BitVec 64}
    {jb : Nat → BitVec 8} (hcode : ljCodeLoaded m) (hg : JbGeom jbp)
    (hpin : ∀ k, jbp.toNat ≤ k → k < jbp.toNat + 112 → (m[k]?).getD 0 = jb k) :
    ChainFacts m m (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) lj1Seg := by
  have h1 := hg.lo; have h2 := hg.hi
  unfold tohostAddr at h1
  unfold lj1Seg ChainFacts
  chain_facts hcode with "VsaIris.Newlib.Sites.ljCode_at_"
  · exact ldFact (img := jb) rfl (jb_off jbp hg 0 (BitVec.ofNat 12 0) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (.inr (by unfold tohostAddr; omega)) (fun k hk => hpin _ (by omega) (by omega))
  · exact ldFact (img := jb) rfl (jb_off jbp hg 8 (BitVec.ofNat 12 8) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (.inr (by unfold tohostAddr; omega)) (fun k hk => hpin _ (by omega) (by omega))
  · exact ldFact (img := jb) rfl (jb_off jbp hg 16 (BitVec.ofNat 12 16) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (.inr (by unfold tohostAddr; omega)) (fun k hk => hpin _ (by omega) (by omega))
  · exact ldFact (img := jb) rfl (jb_off jbp hg 24 (BitVec.ofNat 12 24) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (.inr (by unfold tohostAddr; omega)) (fun k hk => hpin _ (by omega) (by omega))
  · exact ldFact (img := jb) rfl (jb_off jbp hg 32 (BitVec.ofNat 12 32) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (.inr (by unfold tohostAddr; omega)) (fun k hk => hpin _ (by omega) (by omega))
  · exact ldFact (img := jb) rfl (jb_off jbp hg 40 (BitVec.ofNat 12 40) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (.inr (by unfold tohostAddr; omega)) (fun k hk => hpin _ (by omega) (by omega))
  · exact ldFact (img := jb) rfl (jb_off jbp hg 48 (BitVec.ofNat 12 48) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (.inr (by unfold tohostAddr; omega)) (fun k hk => hpin _ (by omega) (by omega))
  · exact ldFact (img := jb) rfl (jb_off jbp hg 56 (BitVec.ofNat 12 56) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (.inr (by unfold tohostAddr; omega)) (fun k hk => hpin _ (by omega) (by omega))
  · exact ldFact (img := jb) rfl (jb_off jbp hg 64 (BitVec.ofNat 12 64) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (.inr (by unfold tohostAddr; omega)) (fun k hk => hpin _ (by omega) (by omega))
  · exact ldFact (img := jb) rfl (jb_off jbp hg 72 (BitVec.ofNat 12 72) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (.inr (by unfold tohostAddr; omega)) (fun k hk => hpin _ (by omega) (by omega))
  · exact ldFact (img := jb) rfl (jb_off jbp hg 80 (BitVec.ofNat 12 80) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (.inr (by unfold tohostAddr; omega)) (fun k hk => hpin _ (by omega) (by omega))
  · exact ldFact (img := jb) rfl (jb_off jbp hg 88 (BitVec.ofNat 12 88) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (.inr (by unfold tohostAddr; omega)) (fun k hk => hpin _ (by omega) (by omega))
  · exact ldFact (img := jb) rfl (jb_off jbp hg 96 (BitVec.ofNat 12 96) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (.inr (by unfold tohostAddr; omega)) (fun k hk => hpin _ (by omega) (by omega))
  · exact ldFact (img := jb) rfl (jb_off jbp hg 104 (BitVec.ofNat 12 104) (by decide) (by omega) _ rfl)
      (by omega) (by omega) (.inr (by unfold tohostAddr; omega)) (fun k hk => hpin _ (by omega) (by omega))

theorem lj1_pc (jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2 : BitVec 64) (jb : Nat → BitVec 8) :
    evalBlocksPC 0x8000703c#64 (SegEvalState.init (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb)) lj1Seg =
      0x80007074#64 := rfl

theorem lj1_fin_1 (jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2 : BitVec 64) (jb : Nat → BitVec 8) :
    finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 1 = imgW jb (jbp.toNat + 0) :=
  (rfl : finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 1 =
    bytesVal .ld (imgWord jb (jbp.toNat + 0))).trans (bytesVal_imgWord jb _)

theorem lj1_fin_8 (jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2 : BitVec 64) (jb : Nat → BitVec 8) :
    finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 8 = imgW jb (jbp.toNat + 8) :=
  (rfl : finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 8 =
    bytesVal .ld (imgWord jb (jbp.toNat + 8))).trans (bytesVal_imgWord jb _)

theorem lj1_fin_9 (jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2 : BitVec 64) (jb : Nat → BitVec 8) :
    finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 9 = imgW jb (jbp.toNat + 16) :=
  (rfl : finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 9 =
    bytesVal .ld (imgWord jb (jbp.toNat + 16))).trans (bytesVal_imgWord jb _)

theorem lj1_fin_18 (jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2 : BitVec 64) (jb : Nat → BitVec 8) :
    finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 18 = imgW jb (jbp.toNat + 24) :=
  (rfl : finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 18 =
    bytesVal .ld (imgWord jb (jbp.toNat + 24))).trans (bytesVal_imgWord jb _)

theorem lj1_fin_19 (jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2 : BitVec 64) (jb : Nat → BitVec 8) :
    finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 19 = imgW jb (jbp.toNat + 32) :=
  (rfl : finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 19 =
    bytesVal .ld (imgWord jb (jbp.toNat + 32))).trans (bytesVal_imgWord jb _)

theorem lj1_fin_20 (jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2 : BitVec 64) (jb : Nat → BitVec 8) :
    finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 20 = imgW jb (jbp.toNat + 40) :=
  (rfl : finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 20 =
    bytesVal .ld (imgWord jb (jbp.toNat + 40))).trans (bytesVal_imgWord jb _)

theorem lj1_fin_21 (jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2 : BitVec 64) (jb : Nat → BitVec 8) :
    finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 21 = imgW jb (jbp.toNat + 48) :=
  (rfl : finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 21 =
    bytesVal .ld (imgWord jb (jbp.toNat + 48))).trans (bytesVal_imgWord jb _)

theorem lj1_fin_22 (jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2 : BitVec 64) (jb : Nat → BitVec 8) :
    finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 22 = imgW jb (jbp.toNat + 56) :=
  (rfl : finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 22 =
    bytesVal .ld (imgWord jb (jbp.toNat + 56))).trans (bytesVal_imgWord jb _)

theorem lj1_fin_23 (jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2 : BitVec 64) (jb : Nat → BitVec 8) :
    finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 23 = imgW jb (jbp.toNat + 64) :=
  (rfl : finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 23 =
    bytesVal .ld (imgWord jb (jbp.toNat + 64))).trans (bytesVal_imgWord jb _)

theorem lj1_fin_24 (jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2 : BitVec 64) (jb : Nat → BitVec 8) :
    finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 24 = imgW jb (jbp.toNat + 72) :=
  (rfl : finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 24 =
    bytesVal .ld (imgWord jb (jbp.toNat + 72))).trans (bytesVal_imgWord jb _)

theorem lj1_fin_25 (jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2 : BitVec 64) (jb : Nat → BitVec 8) :
    finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 25 = imgW jb (jbp.toNat + 80) :=
  (rfl : finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 25 =
    bytesVal .ld (imgWord jb (jbp.toNat + 80))).trans (bytesVal_imgWord jb _)

theorem lj1_fin_26 (jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2 : BitVec 64) (jb : Nat → BitVec 8) :
    finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 26 = imgW jb (jbp.toNat + 88) :=
  (rfl : finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 26 =
    bytesVal .ld (imgWord jb (jbp.toNat + 88))).trans (bytesVal_imgWord jb _)

theorem lj1_fin_27 (jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2 : BitVec 64) (jb : Nat → BitVec 8) :
    finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 27 = imgW jb (jbp.toNat + 96) :=
  (rfl : finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 27 =
    bytesVal .ld (imgWord jb (jbp.toNat + 96))).trans (bytesVal_imgWord jb _)

theorem lj1_fin_2 (jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2 : BitVec 64) (jb : Nat → BitVec 8) :
    finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 2 = imgW jb (jbp.toNat + 104) :=
  (rfl : finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 2 =
    bytesVal .ld (imgWord jb (jbp.toNat + 104))).trans (bytesVal_imgWord jb _)

theorem lj1_fin_10 (jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2 : BitVec 64) (jb : Nat → BitVec 8) :
    finReg lj1Seg (lj1L jbp v1 v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v2) (lj1Lds jbp jb) 10 = jbp := rfl

theorem lj2_facts {m : Std.ExtHashMap Nat (BitVec 8)} {rv : BitVec 64}
    (hcode : ljCodeLoaded m) (hal : rv.toNat % 4 = 0) :
    ChainFacts m m [(10, 0#64), (11, 1#64), (1, rv)] [] lj2Seg := by
  unfold lj2Seg ChainFacts
  chain_facts hcode with "VsaIris.Newlib.Sites.ljCode_at_"
  have e : ∀ x : BitVec 64, x = rv →
      (BitVec.update (x + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    intro x hx; rw [hx, ret_tgt rv hal]; exact hal
  exact e _ rfl

theorem lj2_pc (rv : BitVec 64) (hal : rv.toNat % 4 = 0) :
    evalBlocksPC 0x80007078#64 (SegEvalState.init [(10, 0#64), (11, 1#64), (1, rv)] []) lj2Seg =
      rv := by
  have e : ∀ x : BitVec 64, x = rv →
      BitVec.update (x + sign_extend (m := 64) (0x000#12)) 0 0#1 = rv := by
    intro x hx; rw [hx, ret_tgt rv hal]
  exact e _ rfl

theorem lj2_fin (rv : BitVec 64) :
    finReg lj2Seg [(10, 0#64), (11, 1#64), (1, rv)] [] 10 = 1#64 ∧
    finReg lj2Seg [(10, 0#64), (11, 1#64), (1, rv)] [] 11 = 1#64 ∧
    finReg lj2Seg [(10, 0#64), (11, 1#64), (1, rv)] [] 1 = rv :=
  ⟨by show 0#64 + 1#64 = _; decide, rfl, rfl⟩

/-- `longjmp`'s `seqz a0,a1` with `a1 = 1`. -/
theorem seqz_step (live : Nat → Prop) (hlive : ∀ p ∈ codeFoot ljCodeBase ljCode, live p.1)
    (old : BitVec 64) : ∀ c : Vsa.Machine.Config, VsaOk live c →
      FootHolds (M := vsaModel live) c [(11, DFrac.own 1, 1#64)] (codeFoot ljCodeBase ljCode)
        [(VsaIris.PC, BitVec.ofNat 64 0x80007074, BitVec.ofNat 64 (0x80007074 + 4)), (10, old, 0#64)]
        [] →
      ∃ (σ' : Vsa.Machine.MState) (i' : Nat) (vm : BitVec 64),
        Vsa.Machine.Step ⟨c.σ, c.tick, c.steps⟩ ⟨σ', i', c.steps + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
        σ'.mem = c.σ.mem ∧
        ReadsLikePost σ' (sigmaPost_alu c.σ (BitVec.ofNat 64 0x80007074) vm Register.x10 0#64) := by
  intro c hok ⟨hRR, hMR, hRW, _⟩
  have hpc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 0x80007074) := by
    have h := hRW _ List.mem_cons_self
    change pcVal c.σ = _ at h
    obtain ⟨w, hw⟩ := hok.good.PC
    unfold pcVal at h
    rw [hw] at h ⊢
    exact congrArg some h
  have h11 : c.σ.regs.get? Register.x11 = some 1#64 :=
    gprGet_eq_of_vsaReg hok (n := 11) (by decide) (by decide) (hRR _ List.mem_cons_self)
  have hload : Code.LongjmpLoaded c.σ.mem := by
    have h := ljCodeLoaded_of (code_present hok _ hMR hlive)
    obtain ⟨b00, b01, b02, b03⟩ := ljCode_at_8000703c h
    obtain ⟨b10, b11, b12, b13⟩ := ljCode_at_80007040 h
    obtain ⟨b20, b21, b22, b23⟩ := ljCode_at_80007044 h
    obtain ⟨b30, b31, b32, b33⟩ := ljCode_at_80007048 h
    obtain ⟨b40, b41, b42, b43⟩ := ljCode_at_8000704c h
    obtain ⟨b50, b51, b52, b53⟩ := ljCode_at_80007050 h
    obtain ⟨b60, b61, b62, b63⟩ := ljCode_at_80007054 h
    obtain ⟨b70, b71, b72, b73⟩ := ljCode_at_80007058 h
    obtain ⟨b80, b81, b82, b83⟩ := ljCode_at_8000705c h
    obtain ⟨b90, b91, b92, b93⟩ := ljCode_at_80007060 h
    obtain ⟨b100, b101, b102, b103⟩ := ljCode_at_80007064 h
    obtain ⟨b110, b111, b112, b113⟩ := ljCode_at_80007068 h
    obtain ⟨b120, b121, b122, b123⟩ := ljCode_at_8000706c h
    obtain ⟨b130, b131, b132, b133⟩ := ljCode_at_80007070 h
    obtain ⟨b140, b141, b142, b143⟩ := ljCode_at_80007074 h
    obtain ⟨b150, b151, b152, b153⟩ := ljCode_at_80007078 h
    obtain ⟨b160, b161, b162, b163⟩ := ljCode_at_8000707c h
    unfold Code.LongjmpLoaded Code.longjmpChunk0 Code.longjmpChunk1
    repeat' apply And.intro
    all_goals assumption
  obtain ⟨vm, hmi⟩ := hok.good.minstret
  obtain ⟨σ', i', hs, hi', hG', hmem', hobs⟩ :=
    site_80007074_jmp c.σ c.tick c.steps (0x80007074#64) vm 1#64 hok.good hpc hmi h11 hload rfl
      hok.tick
  exact ⟨σ', i', vm, hs, hi', hG', hmem', by
    rwa [show zero_extend (m := 64) (bool_to_bit (zopz0zI_u (1#64 : BitVec 64)
      (sign_extend (m := 64) (0x001#12)))) = 0#64 by decide] at hobs⟩

/-- The bytes of `fmt2`. -/
def fmt2Bytes : List (BitVec 8) := [0x72#8, 0x75#8, 0x6e#8, 0x74#8, 0x69#8, 0x6d#8, 0x65#8, 0x20#8, 0x65#8, 0x72#8, 0x72#8, 0x6f#8, 0x72#8, 0x20#8, 0x5b#8, 0x6c#8, 0x69#8, 0x6e#8, 0x65#8, 0x20#8, 0x25#8, 0x64#8, 0x5d#8, 0x3a#8, 0x20#8, 0x25#8, 0x73#8]

theorem fmt2_text : ∀ i (h : i < fmt2Bytes.length),
    rodataDom (0x80019318 + i) ∧ rodataByte (0x80019318 + i) = fmt2Bytes[i] ∧ fmt2Bytes[i] ≠ 0 := by
  decide +kernel

theorem fmt2_nul : rodataDom (0x80019318 + fmt2Bytes.length) ∧
    rodataByte (0x80019318 + fmt2Bytes.length) = 0 := by
  decide +kernel

theorem fmt2_ok {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) {line body : BitVec 64}
    (hs : ∃ t, CStrCov R rd body.toNat t) : FmtArgsOK R rd fmt2 [line, body] := by
  obtain ⟨t, ht⟩ := hs
  refine ⟨fmt2Bytes, [.int, .str], ⟨cstrCov_rodata hro fmt2_text fmt2_nul, by decide +kernel,
    by simp, ?_⟩⟩
  intro i hi hs
  have : i = 1 := by
    have : i < 2 := by simpa using hi
    rcases Nat.lt_or_ge i 1 with h | h
    · have : i = 0 := by omega
      subst this; simp at hs
    · omega
  subst this
  exact ⟨t, ht⟩

/-! ## The rule -/

section Split

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

omit G in
theorem jmpRO_roImg [MachGS hlc GF] [InterpGS GF] (inp : Nat) (jb : Nat → BitVec 8) :
    jmpRO (GF := GF) inp jb ⊢ roImg (InExt (inp + interpJmpOff, interpJmpLen)) jb := by
  unfold jmpRO; exact .rfl

theorem sepL_calleeSaved_drop1 (f : Nat → BitVec 64) :
    sepL (GF := GF) (calleeSaved.drop 1) (fun r => r ↦ᵣ f r) ⊣⊢
      (9 : Nat) ↦ᵣ f 9 ∗ (18 : Nat) ↦ᵣ f 18 ∗ (19 : Nat) ↦ᵣ f 19 ∗ (20 : Nat) ↦ᵣ f 20 ∗
      (21 : Nat) ↦ᵣ f 21 ∗ (22 : Nat) ↦ᵣ f 22 ∗ (23 : Nat) ↦ᵣ f 23 ∗ (24 : Nat) ↦ᵣ f 24 ∗
      (25 : Nat) ↦ᵣ f 25 ∗ (26 : Nat) ↦ᵣ f 26 ∗ (27 : Nat) ↦ᵣ f 27 ∗ emp := by
  show sepL [9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] _ ⊣⊢ _
  simp only [sepL_cons, sepL_nil]
  exact .rfl

theorem sepL_calleeSaved1 (f : Nat → BitVec 64) :
    sepL (GF := GF) (calleeSaved.drop 1) (fun r => r ↦ᵣ f r) ⊣⊢
      (9 : Nat) ↦ᵣ f 9 ∗ sepL (calleeSaved.drop 2) (fun r => r ↦ᵣ f r) := by
  show sepL (9 :: calleeSaved.drop 2) _ ⊣⊢ _
  rw [sepL_cons]
  exact .rfl

end Split

theorem sp224 (s : BitVec 64) : s + sign_extend (m := 64) (0xf20#12) = s - 224#64 := by
  rw [show (sign_extend (m := 64) (0xf20#12) : BitVec 64) = -(224#64) by decide,
    ← BitVec.sub_eq_add_neg]

/-- `runtime_error`'s entry. -/
abbrev rtErrEntry : BitVec 64 := 0x80002da8#64

/-- `struct Interp` in RAM above the HTIF words. -/
structure InpGeom (inp : BitVec 64) : Prop where
  lo : Vsa.Sim.tohostAddr + 16 ≤ inp.toNat
  hi : inp.toNat + 480 ≤ 0x88000000

section Wp

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- **`runtime_error(in, line, fmt, a1, a2)` aborts**, for either WP. Given
the arguments with a `%s`/`%d` format whose `%s` arguments are readable, its
stack (`rtErrNeed` bytes), every callee-saved register, the `jmp_buf`
read-only at `jb` (whose `ra` slot is 4-aligned) and the world, the call never
returns, and its abort branch receives the `longjmp` landing with its whole
stack region, `abortRes s rtErrNeed`, and the format's readable bytes, which
`snprintf` only reads (a caller's owned message buffer rejoins its frame). -/
theorem rtErr_spec (H : NewlibHoles) (live : Nat → Prop) (hlive : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) (N : Vsa.RuntimeRepr.NativeAddrs) (L : DlLayout)
    (Room : RoomPred) (inp s line fmt x1 x2 : BitVec 64) (cs : Nat → BitVec 64)
    (Sro Sown : Nat → Prop) (rd : Nat → BitVec 8) (jb : Nat → BitVec 8) (ρ : Regime)
    (st : Vsa.While.St) (d : Nat) (hs : SpIn s rtErrNeed) (hinp : InpGeom inp)
    (hfmt : FmtArgsOK (fun a => Sro a ∨ Sown a) rd fmt [x1, x2])
    (hjb : (jbWord inp.toNat jb 0).toNat % 4 = 0) :
    ⊢ fnSpecAbort Wp rtErrEntry
      (fun _ => iprop(argsAt [inp, line, fmt, x1, x2] ∗ callFrame s rtErrNeed calleeSaved cs ∗
        readable Sro Sown rd ∗ jmpRO inp.toNat jb ∗ world N L Room inp.toNat ρ st d))
      (fun _ => iprop(False))
      (iprop(abortRes N L Room inp.toNat s rtErrNeed ∗ readable Sro Sown rd)) := by
  have hHA := H.at
  have h1 := hs.lo; have h2 := hs.hi; have h3 := hs.align
  unfold rtErrNeed snprintfNeed tohostAddr at h1
  have hi1 := hinp.lo; have hi2 := hinp.hi
  unfold tohostAddr at hi1
  have hg : Frame224 s := ⟨by unfold tohostAddr; omega, h2, h3⟩
  have hb := frame_sub s hg
  have hcodeL := rtErrCode_text.live hlive
  unfold fnSpecAbort
  iintro !>
  iintro %r %Φ Hpc Hra ⟨Hargs, Hcf, Hrdb, #Hjb, Hw⟩ Hk
  unfold argsAt callFrame VsaIris.sp VsaIris.ra
  simp only [List.zipIdx_cons, List.zipIdx_nil, sepL_cons, sepL_nil, List.length_cons,
    List.length_nil, Nat.add_zero, Nat.reduceAdd]
  have hs224 : (s - 224#64).toNat = s.toNat - 224 := by rw [← sp224]; exact hb
  icases Hargs with ⟨⟨Ha0, Ha1, Ha2, Ha3, Ha4, -⟩, Hargs⟩
  icases Hcf with ⟨Hsp, Hscr, Hsaved, Htmp, #Hgp, #Himg⟩
  ihave ⟨Hs0, Hsaved⟩ := (sepL_calleeSaved cs).1 $$ Hsaved
  ihave ⟨Hs1, Hsaved⟩ := (sepL_calleeSaved1 cs).1 $$ Hsaved
  ihave #Hcode := instrAt_of_binImg rtErrCode_text $$ Himg
  -- the frame: body `[s-224, s-32)`, a gap, and the three spills `[s-24, s)`
  ihave ⟨Hscr, Hfr⟩ := stackScratch_frame (s := s) (f := 224#64) (n := rtErrNeed)
    (by unfold rtErrNeed snprintfNeed; omega) (by decide) $$ Hscr
  rw [hs224]
  ihave ⟨Hbody, Hfr⟩ := blockOwn_split (s.toNat - 224) (224#64 : BitVec 64).toNat 192
    (s.toNat - 32) 32 (by decide) (by omega) (by decide) $$ Hfr
  ihave ⟨Hgap, Hfr⟩ := blockOwn_split (s.toNat - 32) 32 8 (s.toNat - 24) 24 (by omega)
    (by omega) rfl $$ Hfr
  ihave Hfr := blockOwn_range _ _ $$ Hfr
  ihave ⟨%Wf, %hWf, Hfr⟩ := sepL_byteAny_exists _ $$ Hfr
  have hWfm : ∀ a, (∃ q ∈ Wf, q.1 = a) ↔ a ∈ List.range' (s.toNat - 24) 24 := by
    intro a; rw [← hWf]; simp
  -- the prologue
  iapply wp_segW live Wp rtASeg (aL s (cs 8) (cs 9) inp line r) [] 0x80002da8#64
    (codeFoot rtErrCodeBase rtErrCode) Wf 7 (by decide)
    (by change ChainOK _ [2, 8, 9, 10, 11, 1] _; decide)
    (by change KeysOK [2, 8, 9, 10, 11, 1]; decide)
    (by change ∀ k ∈ wrChain rtASeg, k ∈ [2, 8, 9, 10, 11, 1]; decide)
    (fun a ha => by
      rw [a_log, sp_off s hg 208 _ (by decide) (by omega) _ rfl,
        sp_off s hg 200 _ (by decide) (by omega) _ rfl, sp_off s hg 216 _ (by decide) (by omega) _ rfl]
      have : ¬ a ∈ List.range' (s.toNat - 24) 24 := fun h => by
        obtain ⟨q, hq, e⟩ := (hWfm a).2 h
        exact ha q hq e
      rw [List.mem_range'] at this
      simp only [OutL]
      refine ⟨?_, ?_, ?_, trivial⟩ <;>
      · apply Classical.byContradiction; intro hc
        exact this ⟨a - (s.toNat - 24), by omega, by omega⟩)
    (fun c hok ⟨_, hMR, _, _⟩ => a_facts (rtErrCodeLoaded_of (code_present hok _ hMR hcodeL)) hg)
  have hpcA := a_pc s (cs 8) (cs 9) inp line r
  obtain ⟨k2, k8, k9, k10, k11, k1⟩ := a_fin s (cs 8) (cs 9) inp line r
  simp only [aL] at hpcA k2 k8 k9 k10 k11 k1
  simp only [aL, sepL_cons, sepL_nil, hpcA, k2, k8, k9, k10, k11, k1, sp224]
  rw [← instrAt_eq]
  iframe Hpc Hsp Hs0 Hs1 Ha0 Ha1 Hra Hfr Hcode
  iintro Hpc ⟨Hsp, Hs0, Hs1, Ha0, Ha1, Hra, -⟩ Hfr -
  -- open the world: newlib's data and `err_msg`
  unfold world worldE interpCtxE interpCoreE errAny
  icases Hw with ⟨%Hh, %B, Hheap, Hstore, Hcon, Hstd, ⟨⟨%g, Hg, Hfa, Hd, %hdle, Hpad, Herr⟩, Hjb'⟩, %hBH, -⟩
  -- `snprintf(body, 192, fmt, a1, a2)`
  let cs1 : Nat → BitVec 64 := fun q => if q = 8 then inp else if q = 9 then line else cs q
  have hsp1 : SpIn (s - 224#64) snprintfNeed :=
    ⟨by rw [hs224]; unfold snprintfNeed tohostAddr; omega, by rw [hs224]; omega,
      by rw [hs224]; omega⟩
  have hf1 := hHA.snprintf live Wp (s - 224#64) (s - 224#64) 192#64 fmt [x1, x2] cs1 Sro Sown rd
    hlive (by simp) (by decide) (by decide) hfmt hsp1
  unfold snprintfSpec at hf1
  have hjt1 : TextAt rtJalSnprintf1.pc rtJalSnprintf1.code := by decide
  have hj1 : JalExec (vsaModel live) rtJalSnprintf1.pc rtJalSnprintf1.code snprintfEntry :=
    JalSite.exec rtJalSnprintf1_cert live (hjt1.live hlive)
  ihave #Hjal1 := instrAt_of_binImg hjt1 $$ Himg
  ihave #Hf1 := hf1
  iapply wp_callW Wp (v := r) hj1
  iframe Hjal1 Hf1
  rw [show BitVec.ofNat 64 rtJalSnprintf1.pc = 0x80002dc8#64 from rfl,
    show BitVec.ofNat 64 (rtJalSnprintf1.pc + 4) = 0x80002dcc#64 from rfl]
  unfold VsaIris.ra
  iframe Hpc Hra
  isplitl [Ha0 Ha1 Ha2 Ha3 Ha4 Hargs Hbody Hrdb Hstd Hsp Hscr Hs0 Hs1 Hsaved Htmp]
  · unfold argsAt callFrame VsaIris.sp
    simp only [List.cons_append, List.nil_append, List.zipIdx_cons, List.zipIdx_nil, sepL_cons,
      sepL_nil, List.length_cons, List.length_nil, Nat.add_zero, Nat.reduceAdd]
    rw [hs224, show rtErrNeed - (224#64 : BitVec 64).toNat = snprintfNeed from rfl,
      show (192#64 : BitVec 64).toNat = 192 from rfl]
    iframe Ha0 Ha1 Ha2 Ha3 Ha4 Hargs Hbody Hrdb Hstd Hsp Hscr Htmp Hgp Himg
    iapply (sepL_calleeSaved cs1).2
    rw [show cs1 8 = inp from rfl]
    iframe Hs0
    iapply (sepL_calleeSaved1 cs1).2
    rw [show cs1 9 = line from rfl, sepL_congr (l := List.drop 2 calleeSaved)
      (Φ := fun q => q ↦ᵣ cs1 q) (Ψ := fun q => q ↦ᵣ cs q) (fun q hq => by
        have h8 : q ≠ 8 := by intro e; subst e; revert hq; decide
        have h9 : q ≠ 9 := by intro e; subst e; revert hq; decide
        simp [cs1, h8, h9])]
    iframe Hs1 Hsaved
  -- stage `snprintf(err_msg, 256, fmt2, line, body)`
  unfold callFrame VsaIris.sp
  iintro Hpc Hra ⟨Hargs, Hbody, Hrdb, Hstd, ⟨Hsp, Hscr, Hsaved, Htmp, -, -⟩⟩
  ihave ⟨Hs0, Hsaved⟩ := (sepL_calleeSaved cs1).1 $$ Hsaved
  ihave ⟨Hs1, Hsaved⟩ := (sepL_calleeSaved1 cs1).1 $$ Hsaved
  ihave ⟨⟨%a0v, Ha0⟩, Hargs⟩ := clobbered_take (r := 10) (by decide) $$ Hargs
  ihave ⟨⟨%a1v, Ha1⟩, Hargs⟩ := clobbered_take (r := 11) (by decide) $$ Hargs
  ihave ⟨⟨%a2v, Ha2⟩, Hargs⟩ := clobbered_take (r := 12) (by decide) $$ Hargs
  ihave ⟨⟨%a3v, Ha3⟩, Hargs⟩ := clobbered_take (r := 13) (by decide) $$ Hargs
  ihave ⟨⟨%a4v, Ha4⟩, Hargs⟩ := clobbered_take (r := 14) (by decide) $$ Hargs
  iapply wp_segW live Wp rtBSeg (bL a1v a4v (s - 224#64) a3v line a0v inp a2v) [] 0x80002dcc#64
    (codeFoot rtErrCodeBase rtErrCode) [] 5 (by decide)
    (by change ChainOK _ [11, 14, 2, 13, 9, 10, 8, 12] _; decide)
    (by change KeysOK [11, 14, 2, 13, 9, 10, 8, 12]; decide)
    (by change ∀ k ∈ wrChain rtBSeg, k ∈ [11, 14, 2, 13, 9, 10, 8, 12]; decide)
    (fun a _ => trivial)
    (fun c hok ⟨_, hMR, _, _⟩ => b_facts (rtErrCodeLoaded_of (code_present hok _ hMR hcodeL)))
  have hpcB := b_pc a1v a4v (s - 224#64) a3v line a0v inp a2v
  obtain ⟨j11, j14, j2, j13, j9, j10, j8, j12⟩ := b_fin a1v a4v (s - 224#64) a3v line a0v inp a2v
  simp only [bL] at hpcB j11 j14 j2 j13 j9 j10 j8 j12
  simp only [bL, sepL_cons, sepL_nil, hpcB, j11, j14, j2, j13, j9, j10, j8, j12]
  rw [← instrAt_eq]
  rw [show cs1 8 = inp from rfl, show cs1 9 = line from rfl]
  iframe Hpc Ha1 Ha4 Hsp Ha3 Hs1 Ha0 Hs0 Ha2 Hcode
  iintro Hpc ⟨Ha1, Ha4, Hsp, Ha3, Hs1, Ha0, Hs0, Ha2, -⟩ - -
  -- `snprintf(err_msg, 256, "runtime error [line %d]: %s", line, body)`
  unfold cstrBuf
  icases Hbody with ⟨%bimg, Hbody, %hbnul⟩
  have herrp : (inp + sign_extend (m := 64) (0x0e0#12)).toNat = inp.toNat + 224 :=
    addr_off inp _ 224 (by decide) (by omega)
  let Sown2 : Nat → Prop := InExt ((s - 224#64).toNat, (192#64 : BitVec 64).toNat)
  let rd2 : Nat → BitVec 8 := fun a => if rodataDom a then rodataByte a else bimg a
  have hoff2 : ∀ a, Sown2 a → ¬ rodataDom a := fun a ha hr => by
    simp only [Sown2, InExt] at ha; rw [hs224] at ha; unfold rodataDom at hr; simp at ha; omega
  have hfmt2 : FmtArgsOK (fun a => rodataDom a ∨ Sown2 a) rd2 fmt2 [line, s - 224#64] :=
    fmt2_ok (fun a ha => ⟨.inl ha, by simp [rd2, ha]⟩)
      (cstrCov_of_nul (n := 192) (fun i hi => .inr ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩)
        (by
          obtain ⟨k, hk, h0⟩ := hbnul
          refine ⟨k, hk, ?_⟩
          have : ¬ rodataDom ((s - 224#64).toNat + k) :=
            hoff2 _ ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hk _⟩
          show (if rodataDom ((s - 224#64).toNat + k) then _ else _) = _
          rw [ite_cond_eq_false _ _ (eq_false this)]; exact h0))
  have hf2 := hHA.snprintf live Wp (s - 224#64) (inp + sign_extend (m := 64) (0x0e0#12)) 256#64
    fmt2 [line, s - 224#64] cs1 rodataDom Sown2 rd2 hlive (by simp) (by decide) (by decide)
    hfmt2 hsp1
  unfold snprintfSpec at hf2
  have hjt2 : TextAt rtJalSnprintf2.pc rtJalSnprintf2.code := by decide
  have hj2 : JalExec (vsaModel live) rtJalSnprintf2.pc rtJalSnprintf2.code snprintfEntry :=
    JalSite.exec rtJalSnprintf2_cert live (hjt2.live hlive)
  ihave #Hjal2 := instrAt_of_binImg hjt2 $$ Himg
  ihave #Hf2 := hf2
  iapply wp_callW Wp (v := 0x80002dcc#64) hj2
  iframe Hjal2 Hf2
  rw [show BitVec.ofNat 64 rtJalSnprintf2.pc = 0x80002de4#64 from rfl,
    show BitVec.ofNat 64 (rtJalSnprintf2.pc + 4) = 0x80002de8#64 from rfl]
  unfold VsaIris.ra
  iframe Hpc Hra
  isplitl [Ha0 Ha1 Ha2 Ha3 Ha4 Hargs Herr Hbody Hstd Hsp Hscr Hs0 Hs1 Hsaved Htmp]
  · unfold argsAt callFrame VsaIris.sp readable
    simp only [List.cons_append, List.nil_append, List.zipIdx_cons, List.zipIdx_nil, sepL_cons,
      sepL_nil, List.length_cons, List.length_nil, Nat.add_zero, Nat.reduceAdd]
    rw [herrp, show (256#64 : BitVec 64).toNat = 256 from rfl]
    iframe Ha0 Ha1 Ha2 Ha3 Ha4 Hstd Hsp Hscr Htmp Hgp Himg
    isplitl [Hargs]
    · rw [show List.drop 5 argRegs =
        ((((argRegs.erase 10).erase 11).erase 12).erase 13).erase 14 from rfl]
      iexact Hargs
    isplitl [Herr]
    · iapply blockOwn_cast (p := inp.toNat + interpErrOff) (n := interpErrLen)
        (p' := inp.toNat + 224) (n' := 256) (by unfold interpErrOff; omega) rfl $$ Herr
    isplitl [Hbody]
    · isplitr
      · iapply roImg_congr (S := rodataDom) (f := rodataByte) (g := rd2)
          (fun a ha => by simp [rd2, ha])
        iapply binImg_rodata $$ Himg
      · iapply ownSet_congr (S := Sown2) (Φ := fun a => a ↦ₘ bimg a) (Ψ := fun a => a ↦ₘ rd2 a)
          (fun a ha => by simp [rd2, hoff2 a ha]) $$ Hbody
    iapply (sepL_calleeSaved cs1).2
    rw [show cs1 8 = inp from rfl]
    iframe Hs0
    iapply (sepL_calleeSaved1 cs1).2
    rw [show cs1 9 = line from rfl]
    iframe Hs1 Hsaved
  -- `a0 = &in->on_error; a1 = 1; jal longjmp`
  unfold callFrame VsaIris.sp readable
  iintro Hpc Hra ⟨Hargs, Herr, ⟨-, Hbody⟩, Hstd, ⟨Hsp, Hscr, Hsaved, Htmp, -, -⟩⟩
  ihave ⟨Hs0, Hsaved⟩ := (sepL_calleeSaved cs1).1 $$ Hsaved
  ihave ⟨⟨%b0v, Ha0⟩, Hargs⟩ := clobbered_take (r := 10) (by decide) $$ Hargs
  ihave ⟨⟨%b1v, Ha1⟩, Hargs⟩ := clobbered_take (r := 11) (by decide) $$ Hargs
  rw [show cs1 8 = inp from rfl]
  iapply wp_segW live Wp rtCSeg (cL b0v inp b1v) [] 0x80002de8#64
    (codeFoot rtErrCodeBase rtErrCode) [] 1 (by decide)
    (by change ChainOK _ [10, 8, 11] _; decide) (by change KeysOK [10, 8, 11]; decide)
    (by change ∀ k ∈ wrChain rtCSeg, k ∈ [10, 8, 11]; decide)
    (fun a _ => trivial)
    (fun c hok ⟨_, hMR, _, _⟩ => c_facts (rtErrCodeLoaded_of (code_present hok _ hMR hcodeL)))
  have hpcC := c_pc b0v inp b1v
  obtain ⟨m10, m8, m11⟩ := c_fin b0v inp b1v
  simp only [cL] at hpcC m10 m8 m11
  simp only [cL, sepL_cons, sepL_nil, hpcC, m10, m8, m11]
  rw [← instrAt_eq]
  iframe Hpc Ha0 Hs0 Ha1 Hcode
  iintro Hpc ⟨Ha0, Hs0, Ha1, -⟩ - -
  have hjt3 : TextAt rtJalLongjmp.pc rtJalLongjmp.code := by decide
  ihave #Hjal3 := instrAt_of_binImg hjt3 $$ Himg
  iapply wp_jalW Wp (JalSite.exec rtJalLongjmp_cert live (hjt3.live hlive))
  unfold VsaIris.ra
  iframe Hjal3 Hra
  isplitl [Hpc]
  · rw [show BitVec.ofNat 64 rtJalLongjmp.pc = 0x80002df0#64 from rfl]
    iexact Hpc
  rw [show rtJalLongjmp.tgt = 0x8000703c#64 from rfl]
  iintro Hpc Hra
  iapply Wp.lat_intro
  -- `longjmp`: restore `ra`, `s0`–`s11`, `sp` from the `jmp_buf`
  have hjbp : (inp + sign_extend (m := 64) (0x010#12)).toNat = inp.toNat + 16 :=
    addr_off inp _ 16 (by decide) (by omega)
  have hjg : JbGeom (inp + sign_extend (m := 64) (0x010#12)) :=
    ⟨by rw [hjbp]; unfold tohostAddr; omega, by rw [hjbp]; omega⟩
  have hljL := ljCode_text.live hlive
  ihave #Hlj := instrAt_of_binImg ljCode_text $$ Himg
  ihave ⟨H9, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27, -⟩ :=
    (sepL_calleeSaved_drop1 cs1).1 $$ Hsaved
  ihave #Hjbr := jmpRO_roImg (GF := GF) inp.toNat jb $$ Hjb
  ihave #Hjbf := roImg_foot (InExt (inp.toNat + interpJmpOff, interpJmpLen)) jb
    (List.range' (inp + sign_extend (m := 64) (0x010#12)).toNat 112) (fun a ha => by
      rw [List.mem_range', hjbp] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      exact ⟨by unfold interpJmpOff; omega, by unfold interpJmpOff interpJmpLen; omega⟩) $$ Hjbr
  iapply wp_segW live Wp lj1Seg
    (lj1L (inp + sign_extend (m := 64) (0x010#12)) (BitVec.ofNat 64 (rtJalLongjmp.pc + 4)) inp
      (cs1 9) (cs1 18) (cs1 19) (cs1 20) (cs1 21) (cs1 22) (cs1 23) (cs1 24) (cs1 25) (cs1 26)
      (cs1 27) (s - 224#64))
    (lj1Lds (inp + sign_extend (m := 64) (0x010#12)) jb) 0x8000703c#64
    (codeFoot ljCodeBase ljCode ++
      (List.range' (inp + sign_extend (m := 64) (0x010#12)).toNat 112).map
        (fun a => (a, Iris.DFrac.discard, jb a))) [] 13 (by decide)
    (by change ChainOK _ [10, 1, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 2] _; decide)
    (by change KeysOK [10, 1, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 2]; decide)
    (by change ∀ k ∈ wrChain lj1Seg, k ∈ [10, 1, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 2]
        decide)
    (fun a _ => trivial)
    (fun c hok ⟨_, hMR, _, _⟩ => lj1_facts
      (ljCodeLoaded_of (code_present hok _ (fun q hq => hMR q (List.mem_append_left _ hq)) hljL))
      hjg (fun k h1 h2 => hMR (k, Iris.DFrac.discard, jb k) (List.mem_append_right _
        (List.mem_map.mpr ⟨k, by
          rw [List.mem_range']
          exact ⟨k - (inp + sign_extend (m := 64) (0x010#12)).toNat, by omega, by omega⟩, rfl⟩))))
  have hpcJ := lj1_pc (inp + sign_extend (m := 64) (0x010#12)) (BitVec.ofNat 64 (rtJalLongjmp.pc + 4)) inp (cs1 9) (cs1 18) (cs1 19) (cs1 20) (cs1 21) (cs1 22) (cs1 23) (cs1 24) (cs1 25) (cs1 26) (cs1 27) (s - 224#64) jb
  have q1 := lj1_fin_1 (inp + sign_extend (m := 64) (0x010#12)) (BitVec.ofNat 64 (rtJalLongjmp.pc + 4)) inp (cs1 9) (cs1 18) (cs1 19) (cs1 20) (cs1 21) (cs1 22) (cs1 23) (cs1 24) (cs1 25) (cs1 26) (cs1 27) (s - 224#64) jb
  have q8 := lj1_fin_8 (inp + sign_extend (m := 64) (0x010#12)) (BitVec.ofNat 64 (rtJalLongjmp.pc + 4)) inp (cs1 9) (cs1 18) (cs1 19) (cs1 20) (cs1 21) (cs1 22) (cs1 23) (cs1 24) (cs1 25) (cs1 26) (cs1 27) (s - 224#64) jb
  have q9 := lj1_fin_9 (inp + sign_extend (m := 64) (0x010#12)) (BitVec.ofNat 64 (rtJalLongjmp.pc + 4)) inp (cs1 9) (cs1 18) (cs1 19) (cs1 20) (cs1 21) (cs1 22) (cs1 23) (cs1 24) (cs1 25) (cs1 26) (cs1 27) (s - 224#64) jb
  have q18 := lj1_fin_18 (inp + sign_extend (m := 64) (0x010#12)) (BitVec.ofNat 64 (rtJalLongjmp.pc + 4)) inp (cs1 9) (cs1 18) (cs1 19) (cs1 20) (cs1 21) (cs1 22) (cs1 23) (cs1 24) (cs1 25) (cs1 26) (cs1 27) (s - 224#64) jb
  have q19 := lj1_fin_19 (inp + sign_extend (m := 64) (0x010#12)) (BitVec.ofNat 64 (rtJalLongjmp.pc + 4)) inp (cs1 9) (cs1 18) (cs1 19) (cs1 20) (cs1 21) (cs1 22) (cs1 23) (cs1 24) (cs1 25) (cs1 26) (cs1 27) (s - 224#64) jb
  have q20 := lj1_fin_20 (inp + sign_extend (m := 64) (0x010#12)) (BitVec.ofNat 64 (rtJalLongjmp.pc + 4)) inp (cs1 9) (cs1 18) (cs1 19) (cs1 20) (cs1 21) (cs1 22) (cs1 23) (cs1 24) (cs1 25) (cs1 26) (cs1 27) (s - 224#64) jb
  have q21 := lj1_fin_21 (inp + sign_extend (m := 64) (0x010#12)) (BitVec.ofNat 64 (rtJalLongjmp.pc + 4)) inp (cs1 9) (cs1 18) (cs1 19) (cs1 20) (cs1 21) (cs1 22) (cs1 23) (cs1 24) (cs1 25) (cs1 26) (cs1 27) (s - 224#64) jb
  have q22 := lj1_fin_22 (inp + sign_extend (m := 64) (0x010#12)) (BitVec.ofNat 64 (rtJalLongjmp.pc + 4)) inp (cs1 9) (cs1 18) (cs1 19) (cs1 20) (cs1 21) (cs1 22) (cs1 23) (cs1 24) (cs1 25) (cs1 26) (cs1 27) (s - 224#64) jb
  have q23 := lj1_fin_23 (inp + sign_extend (m := 64) (0x010#12)) (BitVec.ofNat 64 (rtJalLongjmp.pc + 4)) inp (cs1 9) (cs1 18) (cs1 19) (cs1 20) (cs1 21) (cs1 22) (cs1 23) (cs1 24) (cs1 25) (cs1 26) (cs1 27) (s - 224#64) jb
  have q24 := lj1_fin_24 (inp + sign_extend (m := 64) (0x010#12)) (BitVec.ofNat 64 (rtJalLongjmp.pc + 4)) inp (cs1 9) (cs1 18) (cs1 19) (cs1 20) (cs1 21) (cs1 22) (cs1 23) (cs1 24) (cs1 25) (cs1 26) (cs1 27) (s - 224#64) jb
  have q25 := lj1_fin_25 (inp + sign_extend (m := 64) (0x010#12)) (BitVec.ofNat 64 (rtJalLongjmp.pc + 4)) inp (cs1 9) (cs1 18) (cs1 19) (cs1 20) (cs1 21) (cs1 22) (cs1 23) (cs1 24) (cs1 25) (cs1 26) (cs1 27) (s - 224#64) jb
  have q26 := lj1_fin_26 (inp + sign_extend (m := 64) (0x010#12)) (BitVec.ofNat 64 (rtJalLongjmp.pc + 4)) inp (cs1 9) (cs1 18) (cs1 19) (cs1 20) (cs1 21) (cs1 22) (cs1 23) (cs1 24) (cs1 25) (cs1 26) (cs1 27) (s - 224#64) jb
  have q27 := lj1_fin_27 (inp + sign_extend (m := 64) (0x010#12)) (BitVec.ofNat 64 (rtJalLongjmp.pc + 4)) inp (cs1 9) (cs1 18) (cs1 19) (cs1 20) (cs1 21) (cs1 22) (cs1 23) (cs1 24) (cs1 25) (cs1 26) (cs1 27) (s - 224#64) jb
  have q2 := lj1_fin_2 (inp + sign_extend (m := 64) (0x010#12)) (BitVec.ofNat 64 (rtJalLongjmp.pc + 4)) inp (cs1 9) (cs1 18) (cs1 19) (cs1 20) (cs1 21) (cs1 22) (cs1 23) (cs1 24) (cs1 25) (cs1 26) (cs1 27) (s - 224#64) jb
  have q10 := lj1_fin_10 (inp + sign_extend (m := 64) (0x010#12)) (BitVec.ofNat 64 (rtJalLongjmp.pc + 4)) inp (cs1 9) (cs1 18) (cs1 19) (cs1 20) (cs1 21) (cs1 22) (cs1 23) (cs1 24) (cs1 25) (cs1 26) (cs1 27) (s - 224#64) jb
  simp only [lj1L] at hpcJ q1 q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q2 q10
  rw [hjbp] at q1 q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q2
  simp only [lj1L, sepL_cons, sepL_nil, hpcJ, q1, q8, q9, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q2, q10]
  iframe Hpc Ha0 Hra Hs0 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hsp
  isplitr
  · iempintro
  isplitr
  · iapply (sepL_append _ _ _).2
    isplitr
    · rw [← instrAt_eq]; iexact Hlj
    iexact Hjbf
  iintro Hpc ⟨Ha0, Hra, Hs0, H9, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27, Hsp, -⟩ - -
  -- `seqz a0,a1` (`a1 = 1`)
  iapply wp_aluA0W Wp 0x80007074 (codeFoot ljCodeBase ljCode) [(11, DFrac.own 1, 1#64)]
    (inp + sign_extend (m := 64) (0x010#12)) 0#64 (seqz_step live hljL _)
  simp only [sepL_cons, sepL_nil]
  rw [← instrAt_eq]
  iframe Hlj Ha0 Ha1
  isplitl [Hpc]
  · iexact Hpc
  iintro Hpc Ha0 ⟨Ha1, -⟩ -
  -- `add a0,a0,a1; ret` to the restored `ra`
  have hjw0 : imgW jb (inp.toNat + 16 + 0) = jbWord inp.toNat jb 0 := rfl
  iapply wp_segW live Wp lj2Seg [(10, 0#64), (11, 1#64), (1, jbWord inp.toNat jb 0)] []
    0x80007078#64 (codeFoot ljCodeBase ljCode) [] 1 (by decide)
    (by change ChainOK _ [10, 11, 1] _; decide) (by change KeysOK [10, 11, 1]; decide)
    (by change ∀ k ∈ wrChain lj2Seg, k ∈ [10, 11, 1]; decide)
    (fun a _ => trivial)
    (fun c hok ⟨_, hMR, _, _⟩ => lj2_facts (ljCodeLoaded_of (code_present hok _ hMR hljL)) hjb)
  obtain ⟨n10, n11, n1⟩ := lj2_fin (jbWord inp.toNat jb 0)
  simp only [sepL_cons, sepL_nil, lj2_pc _ hjb, n10, n11, n1]
  rw [← instrAt_eq, ← hjw0]
  iframe Ha0 Ha1 Hra Hlj
  isplitl [Hpc]
  · iexact Hpc
  iintro Hpc ⟨Ha0, Ha1, Hra, -⟩ - -
  -- the abort: the landing, with `runtime_error`'s whole stack region
  ihave Hk := and_elim_r $$ Hk
  iapply Hk
  iframe Hrdb
  unfold abortRes
  iapply abortAt_intro
  isplitr [Hscr Hbody Hgap Hfr]
  · unfold abortCore landingCore
    ileft
    iexists ρ, st, d, jb
    iframe Hjb
    isplitr [Hpc Hra Hsp Ha0 Ha1 Hargs Htmp Hs0 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27]
    · unfold worldE interpCtxE interpCoreE errStr
      iexists Hh, B
      iframe Hheap Hstore Hcon Hstd Hjb'
      isplitl
      · iexists g
        iframe Hg Hfa Hd Hpad
        isplitl []
        · ipureintro; exact hdle
        unfold cstrBuf
        icases Herr with ⟨%eimg, Herr, %hnul⟩
        iexists eimg
        isplitl [Herr]
        · iapply ownImg_cast (a := (inp + sign_extend (m := 64) (0x0e0#12)).toNat)
            (n := (256#64 : BitVec 64).toNat) (a' := inp.toNat + interpErrOff) (n' := interpErrLen)
            (by rw [herrp]; rfl) rfl $$ Herr
        ipureintro
        obtain ⟨k, hk, h0⟩ := hnul
        exact ⟨k, hk, by rw [← h0, herrp]; rfl⟩
      isplitr
      · ipureintro; exact hBH
      · iexact Himg
    · unfold landingRegs VsaIris.sp VsaIris.ra jbSaved
      simp only [sepL_cons, sepL_nil, jbWord, interpJmpOff, Nat.reduceMul]
      iframe Hpc Hra Hsp Ha0 Htmp Hs0 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27
      iapply clobbered_put (r := 11) (rs := List.drop 1 argRegs) (by decide)
      rw [show (List.drop 1 argRegs).erase 11 = (argRegs.erase 10).erase 11 from rfl]
      iframe Hargs
      iexists _
      iexact Ha1
  · ihave Hfr := blockOwn_of_W Wf (s.toNat - 24) 24 _ hWf $$ Hfr
    ihave Hbody := blockOwn_of_ownImg (s - 224#64).toNat (192#64 : BitVec 64).toNat rd2 $$ Hbody
    ihave Hbody := blockOwn_cast (p := (s - 224#64).toNat) (n := (192#64 : BitVec 64).toNat)
      (p' := s.toNat - 224) (n' := 192) hs224 rfl $$ Hbody
    unfold stackScratch
    rw [hs224]
    ihave Hb := blockOwn_join (s.toNat - 224 - snprintfNeed) snprintfNeed (s.toNat - 224) 192
      (snprintfNeed + 192) (by unfold snprintfNeed; omega) rfl $$ [Hscr Hbody]
    · iframe Hscr Hbody
    ihave Hb := blockOwn_join (s.toNat - 224 - snprintfNeed) (snprintfNeed + 192) (s.toNat - 32) 8
      (snprintfNeed + 200) (by unfold snprintfNeed; omega) rfl $$ [Hb Hgap]
    · iframe Hb Hgap
    ihave Hb := blockOwn_join (s.toNat - 224 - snprintfNeed) (snprintfNeed + 200) (s.toNat - 24) 24
      (snprintfNeed + 224) (by unfold snprintfNeed; omega) rfl $$ [Hb Hfr]
    · iframe Hb Hfr
    iapply blockOwn_cast (by unfold rtErrNeed snprintfNeed; omega)
      (by unfold rtErrNeed snprintfNeed; rfl) $$ Hb

end Wp

end VsaIris.Newlib.RtErr
