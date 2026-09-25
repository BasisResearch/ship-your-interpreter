import VsaIris.Vsa.Fprintf.InnerLld

/-!
# The inner `_vfprintf_r(reent, fake, P, ap)` for `"<lit>%s>"` (lane N5)

`"<fn %s>"` and `"<native fn %s>"`: the literal `lit` before the `%`, the
string argument `str` (bytes `bs`, read through `strlen`: the hook `hstr`),
then `">"` and the NUL. The run is `vfp_begin`, the literal run
(`vfp_toTerm`), `s_stage`, the print of `lit` and `bs` (`vfp_print`), the
run `">"` (`vfp_toTerm`), and the end with `">"` pending (`vfp_end1`, the
final flush `sbSprint_hook`).
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

local macro_rules | `(tactic| sx_side) => `(tactic| closed_decide)

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- A format byte's image. -/
theorem FmtAt.img {P : Nat} {bs : List (BitVec 8)} (h : FmtAt Dt DA P bs) (i : Nat) (hi : i < bs.length) :
    imgM Dt (P + i) = bs[i] := by
  have e := h.byte i hi
  rw [ldv_lbu] at e
  refine Classical.byContradiction fun hne => zext8_ne hne ?_
  simpa [LeanRV64DExecutable.zero_extend, Sail.BitVec.zeroExtend] using e

/-- The format's literal run as a printable piece. -/
theorem FmtAt.pieceOK {s : BitVec 64} {need : Nat} {Mt : Mem} {f sp : BitVec 64} {P : Nat}
    {bs : List (BitVec 8)} (h : FmtAt Dt DA P bs) (hsp : P + bs.length ≤ sp.toNat - 384) (hf : sp.toNat ≤ f.toNat) :
    PieceOK Dt DA s need Mt f sp (P, bs) := by
  have hlo := h.lo; have hhi := h.hi
  refine ⟨fun i hi => .inl ⟨h.mem i hi, h.img i hi⟩, hlo, by dsimp only; omega, .inl (by dsimp only; omega),
    fun i hi hr => ?_⟩
  unfold SprintReg SfvCallReg LoopReg SfvReg at hr
  dsimp only at hi hr
  omega

theorem vfpInnerS (hlive : ∀ p ∈ stdioText, live p.1) (hlive' : ∀ p ∈ interpText, live p.1)
    (hsub : ∀ p ∈ interpText, p ∈ dataOf Dt DA) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sp f ap str P : BitVec 64} {need : Nat} {pend0 lit bs : List (BitVec 8)}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hf1 : sp.toNat + 592 ≤ f.toNat) (hf2 : f.toNat + 1208 ≤ s.toNat) (hfa : f.toNat % 8 = 0)
    (hap1 : sp.toNat + 592 ≤ ap.toNat) (hap2 : ap.toNat + 8 ≤ s.toNat) (hapa : ap.toNat % 8 = 0)
    (hra : (R 1).toNat % 4 = 0)
    (h2 : R 2 = sp + 592#64) (h10 : R 10 = 0x8001b538#64) (h11 : R 11 = f) (h12 : R 12 = P)
    (h13 : R 13 = ap)
    (hdec : ldv .ld Mt 0x8001b898 = 0x80019770#64) (hdA : 0x80019770 ∈ DA ∧ 0x80019771 ∈ DA)
    (hdv : imgM Dt 0x80019770 = 0x2e#8 ∧ imgM Dt 0x80019771 = 0#8)
    (hF : SbFile Mt f pend0) (hL : LocMb Mt) (hv : ldv .ld Mt ap.toNat = str) (hs0 : str ≠ 0#64)
    (hlit : lit ≠ []) (hlits : ∀ b ∈ lit, b ≠ 0#8 ∧ b ≠ 37#8) (hlitL : lit.length ≤ 16)
    (hP1 : FmtAt Dt DA P.toNat (lit ++ [37#8])) (hPs : SFmt Dt DA (P.toNat + lit.length))
    (hP2 : FmtAt Dt DA (P.toNat + lit.length + 2) ([0x3e#8] ++ [0#8]))
    (hbsL : bs.length < 2 ^ 20)
    (hstrD : ∀ i (h : i < bs.length), str.toNat + i ∈ DA ∧ imgM Dt (str.toNat + i) = bs[i])
    (hstrR : 0x80000000 ≤ str.toNat ∧ str.toNat + bs.length ≤ 0x100000000 ∧
      (str.toNat + bs.length ≤ 0x8001ad00 ∨ 0x8001ad10 ≤ str.toNat) ∧
      ∀ i, i < bs.length → ¬ SprintReg f.toNat sp.toNat (sp.toNat + 224) (str.toNat + i))
    (hstr : ∀ (R0 : Nat → BitVec 64) (Mt0 : Mem), R0 1 = 0x8000cfcc#64 → R0 10 = str →
      (∀ v : Nat → BitVec 64, SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000cfcc#64
        (upd (updAll R0 v [11, 12, 13, 14, 15, 16]) 10 (BitVec.ofNat 64 bs.length)) Mt0) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x80006cf0#64 R0 Mt0)
    (hk : ∀ R' M' out pend', pend0 ++ (lit ++ bs ++ [0x3e#8]) = out ++ pend' → R' 2 = R 2 → R' 1 = R 1 →
      (∀ x ∈ vfpSaved, R' x = R x) → SbFile M' f pend' → LocMb M' → Frame M' Mt (InnerReg f.toNat sp.toNat) →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs out) (R 1) R' M') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a884#64 R Mt := by
  refine vfp_begin hlive hs1 hs2 hs3 hs4 hal hf1 hf2 hfa h2 h10 h11 h12 hdec hdA hdv hF fun R3 Mt3 B => ?_
  have hsp6 : sp.toNat + 600 < 2 ^ 64 := by omega
  have eo : ∀ k : Nat, k ≤ 600 → (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := fun k hk => sp_lit (by omega)
  have hloc3 : LocMb Mt3 := hL.frame B.frame (fun a h1 h2 h => by omega) (fun h => by omega)
  have hF3 : SbFile Mt3 f pend0 := hF.frame_out B.frame (by omega) fun b hb => by omega
  have hap3 : ldv .ld Mt3 (sp.toNat + 24) = ap := B.ap.trans h13
  have hv3 : ldv .ld Mt3 ap.toNat = str := (B.frame.ldv .ld fun j hj h => by simp only [widthOfM] at hj; omega).trans hv
  have hlitn : lit.length ≠ 0 := fun h => hlit (List.length_eq_zero_iff.1 h)
  refine vfp_toTerm hlive (Or.inr rfl) hs1 hs2 hs3 hs4 hal B.loop hloc3 hP1 hlits (by omega)
    fun R4 Mt4 S4 f22 => ?_
  rw [show termPC 37#8 = 0x8000a9fc#64 by decide]
  have hP2lo := hP2.lo; have hP2hi := hP2.hi
  simp only [List.length_append, List.length_singleton] at hP2hi
  have hP1lo := hP1.lo
  have eX : (P + BitVec.ofNat 64 lit.length).toNat = P.toNat + lit.length := toNat_add_lit (by omega)
  have hlitI : litIov P.toNat lit = [(P.toNat, lit)] := by simp [litIov, hlit]
  have hSc : ∀ a, ScanReg sp.toNat a → sp.toNat + 16 ≤ a ∧ a < sp.toNat + 368 ∧
      (a < sp.toNat + 24 ∨ sp.toNat + 32 ≤ a) := fun a h => by unfold ScanReg MbReg at h; omega
  have hP4 : VfpPend R4 Mt4 sp 0x8001b538#64 f (0 + lit.length) [(P.toNat, lit)] := by
    have := S4.pend; rwa [hlitI] at this
  have hap4 : ldv .ld Mt4 (sp + 24#64).toNat = ap := by
    rw [eo 24 (by omega), S4.frame.ldv .ld fun j hj h => by simp only [widthOfM] at hj; have := hSc _ h; omega]
    exact hap3
  have hv4 : ldv .ld Mt4 ap.toNat = str := by
    rw [S4.frame.ldv .ld fun j hj h => by simp only [widthOfM] at hj; have := hSc _ h; omega]; exact hv3
  have hPs' : SFmt Dt DA (P + BitVec.ofNat 64 lit.length).toNat := by rw [eX]; exact hPs
  refine s_stage hlive hs1 hs2 hs3 hs4 hal (by rw [eX]; omega) (by rw [eX]; omega) hap1 hap2 hapa (by simp)
    (by simp [piecesLen]; omega) (by simp [piecesLen]; omega) (by omega) hP4 S4.s9 hPs' hap4 hv4 hs0 hstr
    fun R5 M5 P5 e24 z32 ap5 fr5 => ?_
  have hSR : ∀ n, n ≤ 1 → ∀ a, SReg sp.toNat n a → sp.toNat + 16 ≤ a ∧ a < sp.toNat + 384 :=
    fun n hn a h => by unfold SReg at h; omega
  have hSR1 : ∀ a, SReg sp.toNat [(P.toNat, lit)].length a → sp.toNat + 16 ≤ a ∧ a < sp.toNat + 384 :=
    hSR 1 (by simp)
  have hF5 : SbFile M5 f pend0 := (hF3.frame_out S4.frame (by omega) fun b hb => by have := hSc _ hb; omega).frame_out
    fr5 (by omega) fun b hb => by have := hSR1 _ hb; omega
  have hFlit : FmtAt Dt DA P.toNat lit := ⟨hP1.lo, by have := hP1.hi; simp at this; omega,
    fun i hi => hP1.mem i (by simp; omega), fun i hi => by
      have := hP1.byte i (by simp; omega); rwa [List.getElem_append_left hi] at this⟩
  have hsrcs : ∀ p ∈ [(P.toNat, lit)] ++ [(str.toNat, bs)], PieceOK Dt DA s need M5 f sp p := by
    intro p hp
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hFlit.pieceOK (by omega) (by omega)
    · obtain ⟨r1, r2, r3, r4⟩ := hstrR
      exact ⟨fun i hi => .inl (hstrD i hi), r1, r2, r3, r4⟩
  refine vfp_print hlive hlive' hsub hs1 hs2 hs3 hs4 hal hf1 hf2 hfa P5 e24 (by simp)
    (by simp [piecesLen]; omega) (by simp [piecesLen]; omega) hsrcs z32 hF5
    fun R6 M6 out1 pend1 hrel1 HL6 hSb6 hfr6 => ?_
  have hPr : ∀ a, PrintReg f.toNat sp.toNat a → (sp.toNat - 384 ≤ a ∧ a < sp.toNat + 248) ∨
      (f.toNat ≤ a ∧ a < f.toNat + 1208) ∨ (0x8001bb30 ≤ a ∧ a < 0x8001bb32) ∨
      (0x8001ba08 ≤ a ∧ a < 0x8001ba0c) := fun a h => by
    unfold PrintReg SprintReg SfvCallReg LoopReg SfvReg at h; omega
  have hloc6 : LocMb M6 :=
    ((hloc3.frame S4.frame (fun a h1 h2 h => by have := hSc _ h; omega) (fun h => by have := hSc _ h; omega)).frame
      fr5 (fun a h1 h2 h => by have := hSR1 _ h; omega) (fun h => by have := hSR1 _ h; omega)).frame
      hfr6 (fun a h1 h2 h => by have := hPr _ h; omega) (fun h => by have := hPr _ h; omega)
  have eP' : (P + BitVec.ofNat 64 lit.length + 2#64).toNat = P.toNat + lit.length + 2 := by
    rw [toNat_add_lit (k := 2) (by rw [eX]; omega), eX]
  have hP2' : FmtAt Dt DA (P + BitVec.ofNat 64 lit.length + 2#64).toNat ([0x3e#8] ++ [0#8]) := by
    rw [eP']; exact hP2
  refine vfp_toTerm hlive (Or.inl rfl) hs1 hs2 hs3 hs4 hal HL6 hloc6 hP2' (by simp) (by simp; omega)
    fun R7 M7 S7 f22' => ?_
  rw [show termPC 0#8 = 0x8000aca8#64 by decide]
  have hI7 : litIov (P + BitVec.ofNat 64 lit.length + 2#64).toNat [62#8] =
      [((P + BitVec.ofNat 64 lit.length + 2#64).toNat, [62#8])] := by simp [litIov]
  have hP7 : VfpPend R7 M7 sp 0x8001b538#64 f (0 + lit.length + bs.length + [62#8].length)
      [((P + BitVec.ofNat 64 lit.length + 2#64).toNat, [62#8])] := by
    have := S7.pend; rwa [hI7] at this
  have hSb7 : SbFile M7 f pend1 := hSb6.frame_out S7.frame (by omega) fun b hb => by have := hSc _ hb; omega
  have hS7 : VfpSpills M7 sp R :=
    (((B.spills.frame S4.frame hsp6 fun a h => by have := hSc _ h; omega).frame fr5 hsp6
      fun a h => by have := hSR1 _ h; omega).frame hfr6 hsp6 fun a h => by have := hPr _ h; omega).frame
      S7.frame hsp6 fun a h => by have := hSc _ h; omega
  have hFgt : FmtAt Dt DA (P + BitVec.ofNat 64 lit.length + 2#64).toNat [62#8] := by
    have h1 := hP2'.hi
    simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] at h1
    refine ⟨hP2'.lo, by simp only [List.length_singleton]; omega, fun i hi => hP2'.mem i ?_, fun i hi => ?_⟩
    · simp only [List.length_singleton] at hi; simp only [List.length_append, List.length_singleton]; omega
    · have := hP2'.byte i (by simp only [List.length_singleton] at hi; simp only [List.length_append,
        List.length_singleton]; omega)
      rwa [List.getElem_append_left hi] at this
  have hsp' : 0x80100000 ≤ sp.toNat := by omega
  refine vfp_end1 (Post := fun out M' => ∃ pend', SbOut M7 M' sp f pend1 pend'
      [((P + BitVec.ofNat 64 lit.length + 2#64).toNat, [62#8])] out)
    hlive hs1 hs2 hs3 hs4 hal (by omega) (by omega) hfa (fun b h1 h2 => by unfold outS; omega) (.inr hf1) hP7
    ⟨hSb7.flags, hSb7.flags2, by decide, by decide⟩ hS7 hra (by simp [piecesLen]) (by simp [piecesLen])
    (sbSprint_hook hlive hlive' hsub hs1 hs2 hs3 hs4 hal hf1 hf2 hfa hP7 (by simp) (by simp [piecesLen])
      (by simp [piecesLen]) (fun p hp => by
        simp only [List.mem_singleton] at hp; subst hp; exact hFgt.pieceOK (by simp only [List.length_singleton]; omega) (by omega)) hSb7 (by decide))
    (fun out M' ⟨_, H⟩ => H.endRet hSb7 hsp' (by omega) hf1) fun out2 M8 ⟨pend2, H⟩ R8 e10 e2 e1 ekeep => ?_
  have hst : Frame (writeLog M8 [((sp + 232#64).toNat, 4, 0#64)]) M8
      (fun a => sp.toNat + 232 ≤ a ∧ a < sp.toNat + 236) :=
    Frame.store M8 _ fun b h1 h2 => by rw [eo 232 (by omega)] at h1 h2; exact ⟨h1, h2⟩
  have hSR' : ∀ a, SprintReg f.toNat sp.toNat (sp.toNat + 224) a → (sp.toNat - 384 ≤ a ∧ a < sp.toNat + 248) ∨
      (f.toNat ≤ a ∧ a < f.toNat + 1208) ∨ (0x8001bb30 ≤ a ∧ a < 0x8001bb32) ∨
      (0x8001ba08 ≤ a ∧ a < 0x8001ba0c) := fun a h => by unfold SprintReg SfvCallReg LoopReg SfvReg at h; omega
  have hrel : pend0 ++ (lit ++ bs ++ [0x3e#8]) = (out1 ++ out2) ++ pend2 := by
    have r2 := H.rel
    simp only [piecesBytes, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil] at hrel1 r2
    calc pend0 ++ (lit ++ bs ++ [0x3e#8]) = (pend0 ++ (lit ++ bs)) ++ [0x3e#8] := by simp
      _ = out1 ++ (pend1 ++ [0x3e#8]) := by rw [hrel1]; simp
      _ = (out1 ++ out2) ++ pend2 := by rw [r2]; simp
  rw [String.append_assoc, ← putcs_append]
  refine hk R8 _ (out1 ++ out2) pend2 hrel (e2.trans h2.symm) e1 ekeep
    (H.file.frame_out hst (by omega) fun b hb => by omega)
    (((hloc6.frame S7.frame (fun a h1 h2 h => by have := hSc _ h; omega) (fun h => by have := hSc _ h; omega)).frame
      H.frame (fun a h1 h2 h => by have := hSR' _ h; omega) (fun h => by have := hSR' _ h; omega)).frame
      hst (fun a h1 h2 h => by omega) (fun h => by omega)) ?_
  refine ((((((B.frame.mono fun a h => ?_).trans (S4.frame.mono fun a h => ?_)).trans (fr5.mono fun a h => ?_)).trans
    (hfr6.mono fun a h => ?_)).trans (S7.frame.mono fun a h => ?_)).trans (H.frame.mono fun a h => ?_)).trans
    (hst.mono fun a h => ?_)
  all_goals unfold InnerReg
  · omega
  · have := hSc _ h; omega
  · have := hSR1 _ h; omega
  · have := hPr _ h; omega
  · have := hSc _ h; omega
  · have := hSR' _ h; omega
  · omega

end VsaIris.Sym.Fp
