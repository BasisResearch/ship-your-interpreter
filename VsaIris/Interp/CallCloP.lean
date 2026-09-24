import VsaIris.Interp.CallCloT

/-!
# The closure call, partial mode (lane E4)

The success path is the Wp-generic layer (`cloBind`, `cloBodyEntry`,
`cloExitN`, `cloExitR`); this file adds the partial-mode pieces:

* `cloAbort`: an abort at `eval_expr`'s lowered `sp` (`abortRes`, E5's
  `ms_callEnvNewP`/`ms_callEnvDefineP` out of memory) with the frame's bytes
  back is the arm's `abortAt Core s n` (`CoreOK`).
* `cloDefineStepP`: the parameter loop's `env_define`, uncounted, out of
  memory through the abort handler `Ab` the loop's resources carry.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Newlib
open Vsa.MemRepr Vsa.Sim Vsa.While
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr VsaIris.VsaHeap

section Partial

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

theorem hoff' {s : BitVec 64} (hfg : EvalFrameG s) (c : Nat) (hc : c < 4096 := by decide) :
    (s + 18446744073709550528#64 + BitVec.ofNat 64 c).toNat = s.toNat - 1088 + c :=
  evalSP_off' hfg c hc

/-- A frame without a slot, and the slot: the frame. -/
theorem frame_of_slot {s : BitVec 64} {a : Nat} (ha1 : s.toNat - 1088 ≤ a)
    (ha2 : a + 24 ≤ s.toNat - 1088 + 1088) :
    ownSet (GF := GF) (fun k => InExt (s.toNat - 1088, 1088) k ∧ ¬ InExt (a, 24) k) byteAny ∗
      blockOwn a 24 ⊢ ownSet (InExt (s.toNat - 1088, 1088)) byteAny := by
  unfold blockOwn
  iintro ⟨HS, HB⟩
  ihave H := ownSet_join (fun k => InExt (s.toNat - 1088, 1088) k ∧ ¬ InExt (a, 24) k) (InExt (a, 24))
    byteAny (fun k h1 h2 => h1.2 h2) $$ [HS HB]
  · iframe HS HB
  iapply ownSet_iff _ (fun k => ⟨fun h => h.elim (·.1) (fun h => by
    simp only [InExt] at h ⊢; omega), fun h => by
    by_cases h' : InExt (a, 24) k
    · exact .inr h'
    · exact .inl ⟨h, h'⟩⟩) $$ H

/-- **An abort at the lowered `sp`** with the frame's bytes back: the arm's
abort (`CoreOK`). -/
theorem cloAbort {N : NativeAddrs} {inp : Nat} {Core : IProp GF}
    (hcore : CoreOK N vsaLayoutP vsaRoomB inp Core) {s : BitVec 64} {n : Nat}
    (hfg : EvalFrameG s) (hsg : StackGeom s n) (hn : 1088 ≤ n) :
    abortRes N vsaLayoutP vsaRoomB inp (s + 18446744073709550528#64) (n - 1088) ∗
      ownSet (InExt (s.toNat - 1088, 1088)) byteAny ⊢ abortAt Core s n := by
  have hsf := hfg.sf
  have h1 := hsg.le; have h2 := hsg.lo
  simp only [Vsa.Sim.LayoutInstance.stackSL] at h2
  unfold abortRes
  iintro ⟨HA, HS⟩
  ihave ⟨HC, Hst⟩ := abortAt_elim _ _ _ $$ HA
  ihave HC := hcore (s + 18446744073709550528#64) (n - 1088) (by rw [hsf]; omega)
    (by rw [hsf]; omega) (by rw [hsf]; have := hfg.hi; omega) $$ HC
  iapply abortAt_intro
  iframe HC
  iapply evalFrame_join hsg.le hn $$ [Hst HS]
  iframe Hst HS

/-- The parameter loop's resources, partial: the image, the frame's binding,
the world at the body's depth, and the abort handler `Ab`. -/
def cloWP (N : NativeAddrs) (inp d : Nat) (out : String) (fa : Nat) (fr : BitVec 64) (Ab : IProp GF)
    (st : Store) (_rest : List (String × Value)) : IProp GF :=
  iprop(□ Newlib.binImg ∗ □ frameAt fa fr.toNat ∗
    world N vsaLayoutP vsaRoomB inp .uncounted ⟨st, out⟩ (d + 1) ∗ Ab)

/-- **`env_define` of one parameter, partial** (`jal env_define` at
`0x80003310`): out of memory, the handler `Ab` takes the arm's abort. -/
theorem cloDefineStepP (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp d : Nat} {out : String} {s fr : BitVec 64} {fa n : Nat} {Core : IProp GF}
    {Ab : IProp GF} (HN : Newlib.NewlibHoles) (hcl : Newlib.CodeLive live)
    (hcore : CoreOK N vsaLayoutP vsaRoomB inp Core)
    (hed : ⊢ envDefineSpec (GF := GF) (wpW (vsaModel live)) N)
    (hab : Ab ∗ abortAt Core s (n + 1088) ⊢ (wpW (vsaModel live)).W Φ)
    (hfg : EvalFrameG s) (hsg : StackGeom s (n + 1088)) (hn1 : envDefineNeed ≤ n)
    (hn2 : Newlib.fwriteNeed + 64 ≤ n) :
    CloDefineStep (wpW (vsaModel live)) Φ N (cloWP N inp d out fa fr Ab) s fr fa n := by
  intro R Mt st x v rest h2 h10 h12
  have hsf := hfg.sf; have hs := hfg.lo; have hs2 := hfg.hi; have hs3 := hfg.al
  have hle := hsg.le; have hlo := hsg.lo
  simp only [Vsa.Sim.LayoutInstance.stackSL] at hlo
  have hsp : EnvSp (R 2) envDefineNeed := by rw [h2]; exact envSp_eval hfg (by decide)
  have hpv : SlotWin (R 12).toNat :=
    ⟨by rw [h12]; omega, by rw [h12]; omega, by rw [h12]; unfold htifLo; omega, by rw [h12]; omega⟩
  unfold cloWP
  rw [← h2]
  iintro ⟨#Hcode, Hms, ⟨#Himg, #Hfr, Hw, Hab⟩, Hval, #Hstr, Hst, Hk⟩
  ihave #Hed := hed
  iapply ms_callEnvDefineP HN hcl (i := 0x80003310)
    (jalx_80003310 live (fun p hp => hlive _ (interp_code_80003310 p hp))) interp_code_80003310
    (by decide) (st := ⟨st, out⟩) (d := d + 1) (fa := fa) (x := x) (v := v) (R := R) (n := n) hsp hpv
    hn1 (by rw [h2, hsf]; omega) (by rw [h2, hsf]; unfold Vsa.Sim.tohostAddr; omega)
    (by rw [h2, hsf]; omega) (by rw [h2, hsf]; omega)
  iframe Hed Hcode Himg Hms Hst Hstr Hval Hw
  isplitl []
  · rw [h10]; iexact Hfr
  isplit
  · iintro %R' %hk Hst Hval Hw Hms
    iapply Hk $$ %R' %hk Hst Hval [Hw Hab] Hms
    iframe Himg Hfr Hw Hab
  · iintro ⟨HA, Hval, HS⟩
    iapply hab
    iframe Hab
    ihave Hsl := valAt_slot N _ v $$ Hval
    rw [h12, h2]
    ihave HS := frame_of_slot (s := s) (a := s.toNat - 1088 + 64) (by omega) (by omega) $$ [HS Hsl]
    · unfold slot24; iframe HS Hsl
    have hca := cloAbort (GF := GF) hcore hfg hsg (by omega)
    rw [show n + 1088 - 1088 = n by omega] at hca
    iapply hca $$ [HA HS]
    iframe HA HS

/-- **`break`/`continue` escaping a body** (`0x8000337c`, status `1`/`2`),
for either WP: `--in->call_depth`, then `runtime_error(in, line,
"'break'/'continue' outside of a loop")`, which aborts. -/
theorem cloExitEsc (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {Core : IProp GF} (hE : ErrEnv N L Room inp live Core) {ρ : Regime} {st : St} {d : Nat}
    {status : Status} (hsc : status = .brk ∨ status = .cont)
    {s sret ret : BitVec 64} {rv R : Nat → BitVec 64} {Mt : Mem} {n : Nat}
    (hfg : EvalFrameG s) (hsg : StackGeom s n) (hn : 1088 + RtErr.rtErrNeed ≤ n) (hinpA : inp % 8 = 0)
    (hat : CloAt R Mt s (BitVec.ofNat 64 inp) sret ret rv) (h10 : R 10 = statusCode status) :
    codeRes ∗ errCtx inp ∗ ms 0x8000337c#64 R (closureS s) Mt ∗
      slot24 (s + 18446744073709550528#64 + 144#64).toNat ∗ world N L Room inp ρ st (d + 1) ∗
      stackScratch (s + 18446744073709550528#64) (n - 1088) ∗ (abortAt Core s n -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  have hsf := hfg.sf; have hs := hfg.lo; have hs2 := hfg.hi; have hs3 := hfg.al
  have hinpG := hE.inpGeom
  have hinpN : (BitVec.ofNat 64 inp).toNat = inp := Nat.mod_eq_of_lt hE.inpLt
  have hi8 : (BitVec.ofNat 64 inp + 8#64).toNat = inp + 8 := by
    have := hinpG.hi; rw [hinpN] at this
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  have hwd := world_depth (GF := GF) N L Room inp ρ st (d + 1)
  rw [show inp + interpDepthOff = inp + 8 from rfl] at hwd
  have hc1 : (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (R 10 + 18446744073709551615#64))).toNat ≤ 1 := by
    rw [h10]; rcases hsc with rfl | rfl <;> decide
  iintro ⟨#Hcode, #HE, Hms, Hsl, Hw, Hst, Hab⟩
  ihave ⟨%M1, Hms, %hM1⟩ := ms_joinSlot144 hfg $$ [Hms Hsl]
  · iframe Hms Hsl
  ihave ⟨%dimg, Hd, %⟨hdv, hdle⟩, Hcl⟩ := hwd $$ Hw
  ihave ⟨%Md, Hd, %hMd⟩ := ownSet_trackedAt _ dimg $$ Hd
  ihave ⟨%M3, Hms, %⟨hM3f, hM3d, hdisj⟩⟩ := ms_join $$ [Hms Hd]
  · iframe Hms Hd
  have hi3 : inp + 8 + 4 ≤ s.toNat - 1088 ∨ s.toNat ≤ inp + 8 := by
    refine Classical.byContradiction fun hc => ?_
    exact hdisj (max (s.toNat - 1088) (inp + 8)) (by simp only [InExt]; omega)
      (by simp only [InExt]; omega)
  have hdep3 : imgLE (imgM M3) (inp + 8) 4 = d + 1 := by
    rw [imgLE_congr (img' := dimg) (fun i hi => (hM3d _ (by simp [InExt]; omega)).trans
      (hMd _ (by simp [InExt]; omega))), hdv]
  have hdl : ldv .lw M3 (BitVec.ofNat 64 inp + 8#64).toNat = BitVec.ofNat 64 (d + 1) := by
    rw [hi8]; exact ldvf_lw_imgLE hdep3 (by unfold maxCallDepth at hdle; omega)
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ []) (F := iprop(codeRes ∗ errCtx inp ∗
      (∀ (d' : Nat) (img' : Nat → BitVec 8), ownImg (InExt (inp + 8, 4)) img' -∗
          ⌜imgLE img' (inp + 8) 4 = d' ∧ d' ≤ maxCallDepth⌝ -∗ world N L Room inp ρ st d') ∗
      stackScratch (s + 18446744073709550528#64) (n - 1088) ∗ (abortAt Core s n -∗ Wp.W Φ)))
  rotate_left
  · rw [hro]; iframe Hcode HE Hcl Hst Hab
    iapply ms_iff (T := fun b => InExt (s.toNat - 1088, 1088) b ∨
      InExt ((BitVec.ofNat 64 inp).toNat + 8, 4) b) (fun k => by rw [hinpN]) $$ Hms
  intro F'
  refine CloX_runX (m := ∅) (dep := d + 1) hlive hsf hs hs2 hs3 hinpG.lo hinpG.hi
    (by rw [hinpN]; omega) (by rw [hinpN]; exact hinpA) hat.s2 hat.sp hdl ?_ ?_ ?_
  rotate_left
  · intro hc; exact absurd hc1 hc
  · intro hc; exact absurd hc1 hc
  intro _
  apply swp_closeRM
  intro R4 Mt4 hR4 hMt4
  unfold F'
  iintro ⟨⟨#Hcode, #HE, Hcl, Hst, Hab⟩, Hms⟩
  ihave ⟨Hms, Hd⟩ := ms_split (S := InExt (s.toNat - 1088, 1088)) (T := InExt (inp + 8, 4))
    (fun a h1 h2 => by simp only [InExt] at h1 h2; omega) $$ [Hms]
  · iapply ms_iff (T := fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (inp + 8, 4) b)
      (fun k => by rw [hinpN]) $$ Hms
  have hdep4 : imgLE (imgM Mt4) (inp + 8) 4 = d := by
    have hv : (BitVec.signExtend 64 (BitVec.extractLsb 31 0
        (BitVec.ofNat 64 (d + 1) + 18446744073709551615#64))).toNat % 2 ^ 32 = d := by
      have e : BitVec.ofNat 64 (d + 1) + 18446744073709551615#64 = BitVec.ofNat 64 d := by
        rw [← idx_succ, BitVec.add_assoc, show (1#64 + 18446744073709551615#64 : BitVec 64) = 0#64 by
          decide, BitVec.add_zero]
      rw [e, sext32_toNat_small (by unfold maxCallDepth at hdle; omega)]
      exact Nat.mod_eq_of_lt (by unfold maxCallDepth at hdle; omega)
    rw [hMt4, imgLE_congr (n := 4) (img' := imgM (writeLog M3 [((BitVec.ofNat 64 inp + 8#64).toNat, 4,
        BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 (d + 1) + 18446744073709551615#64)))]))
      (fun i hi => by
        rw [imgM_store_miss _ _ (by rw [hoff' hfg 1024]; omega),
          imgM_store_miss _ _ (by rw [hoff' hfg 1040]; omega)]),
      hi8, imgLE_store4_hit, hv]
  ihave Hw := Hcl $$ %d %(imgM Mt4) Hd %⟨hdep4, by omega⟩
  ihave #Himg := errCtx_img inp $$ HE
  ihave #Hrd := readable_rodata $$ Himg
  iapply ms_rtErrEval Wp hE (jalx_80003ce8 live (fun p hp => hlive _ (interp_code_80003ce8 p hp)))
    interp_code_80003ce8 (readable_rodata_fmt (fun hro => escape_fmt hro 0#64 0#64)) hsg hn
    (R := R4) (line := R 23)
  iframe Hcode HE Hrd Hms Hst Hw Hab
  ipureintro
  subst hR4
  refine ⟨?_, by ix_reg, by ix_reg, by ix_reg, by ix_reg, by ix_reg; exact hat.sp⟩
  first | (ix_reg; done) | (ix_reg; exact hat.s2)

/-- **The depth error** (`0x80003ca4`, `in->call_depth` past the maximum), for
either WP: the depth word zeroed, `runtime_error(in, line, "stack overflow
…")`, which aborts. -/
theorem cloErrDepth (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {Core : IProp GF} (hE : ErrEnv N L Room inp live Core) {ρ : Regime} {st : St}
    {s aX sret ret line : BitVec 64} {rv R : Nat → BitVec 64} {Mt : Mem} {n dep : Nat}
    (hfg : EvalFrameG s) (hsg : StackGeom s n) (hn : 1088 + RtErr.rtErrNeed ≤ n) (hinpA : inp % 8 = 0)
    (hi3 : inp + 8 + 4 ≤ s.toNat - 1088 ∨ s.toNat ≤ inp + 8)
    (hdp : CloDp R Mt s aX sret (BitVec.ofNat 64 inp) ret line rv dep) :
    codeRes ∗ errCtx inp ∗ ms 0x80003ca4#64 R (cloS s (BitVec.ofNat 64 inp)) Mt ∗
      (∀ (d' : Nat) (img' : Nat → BitVec 8), ownImg (InExt (inp + 8, 4)) img' -∗
          ⌜imgLE img' (inp + 8) 4 = d' ∧ d' ≤ maxCallDepth⌝ -∗ world N L Room inp ρ st d') ∗
      stackScratch (s + 18446744073709550528#64) (n - 1088) ∗ (abortAt Core s n -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  have hsf := hfg.sf; have hs := hfg.lo; have hs2 := hfg.hi; have hs3 := hfg.al
  have hinpG := hE.inpGeom
  have hinpN : (BitVec.ofNat 64 inp).toNat = inp := Nat.mod_eq_of_lt hE.inpLt
  have hi8 : (BitVec.ofNat 64 inp + 8#64).toNat = inp + 8 := by
    have := hinpG.hi; rw [hinpN] at this
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  iintro ⟨#Hcode, #HE, Hms, Hcl, Hst, Hab⟩
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ []) (F := iprop(codeRes ∗ errCtx inp ∗
      (∀ (d' : Nat) (img' : Nat → BitVec 8), ownImg (InExt (inp + 8, 4)) img' -∗
          ⌜imgLE img' (inp + 8) 4 = d' ∧ d' ≤ maxCallDepth⌝ -∗ world N L Room inp ρ st d') ∗
      stackScratch (s + 18446744073709550528#64) (n - 1088) ∗ (abortAt Core s n -∗ Wp.W Φ)))
  rotate_left
  · rw [hro]; iframe Hcode HE Hcl Hst Hab; iexact Hms
  intro F'
  refine CloE_runD (m := ∅) hlive hsf hs hs2 hs3 hinpG.lo hinpG.hi (by rw [hinpN]; omega)
    (by rw [hinpN]; exact hinpA) hdp.s2 hdp.sp ?_
  apply swp_closeRM
  intro R4 Mt4 hR4 hMt4
  unfold F'
  iintro ⟨⟨#Hcode, #HE, Hcl, Hst, Hab⟩, Hms⟩
  ihave ⟨Hms, Hd⟩ := ms_split (S := InExt (s.toNat - 1088, 1088)) (T := InExt (inp + 8, 4))
    (fun a h1 h2 => by simp only [InExt] at h1 h2; omega) $$ [Hms]
  · iapply ms_iff (T := fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (inp + 8, 4) b)
      (fun k => by rw [hinpN]) $$ Hms
  have hdep4 : imgLE (imgM Mt4) (inp + 8) 4 = 0 := by
    rw [hMt4, hi8, imgLE_store4_hit]; rfl
  ihave Hw := Hcl $$ %0 %(imgM Mt4) Hd %⟨hdep4, by unfold maxCallDepth; omega⟩
  ihave #Himg := errCtx_img inp $$ HE
  ihave #Hrd := readable_rodata $$ Himg
  iapply ms_rtErrEval Wp hE (jalx_80003cc4 live (fun p hp => hlive _ (interp_code_80003cc4 p hp)))
    interp_code_80003cc4 (readable_rodata_fmt (fun hro => depth_fmt hro 0#64 0#64)) hsg hn
    (R := R4) (line := line)
  iframe Hcode HE Hrd Hms Hst Hw Hab
  ipureintro
  subst hR4
  refine ⟨?_, by ix_reg; exact hdp.a1, by ix_reg, by ix_reg, by ix_reg, by ix_reg; exact hdp.sp⟩
  first | (ix_reg; done) | (ix_reg; exact hdp.s2)

end Partial

end VsaIris.Interp
