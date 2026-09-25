import VsaIris.Vsa.Fprintf.Run
import VsaIris.Vsa.Stderr.StrCodeStdio

/-!
# `fprintf(stdout, "%lld", v)` and `fprintf(stdout, "<…%s>", str)` (lane N5)

`fprintf_via` with the inner `_vfprintf_r` run of each format: `vfpInnerLld`
prints `lldBytes v`; `vfpInnerS` prints `lit ++ bs ++ ">"` for a string `bs`
at `str` in the data view, its `strlen` through `strlen_sw`.
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open VsaIris.Inst.Strlen VsaIris.Interp.StrLeaf
open scoped VsaIris.Sym.Stdout

local macro_rules | `(tactic| sx_side) => `(tactic| closed_decide)

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

theorem lldBytes_len (v : BitVec 64) : (lldBytes v).length ≤ 21 := by
  have := digBytes_len (lldMag v).toNat (lldMag v).isLt
  unfold lldBytes; split <;> simp <;> omega

/-- **`fprintf(stdout, "%lld", v)`** prints `lldBytes v`. -/
theorem fprintf_lld (hlive : ∀ p ∈ stdioText, live p.1) (hlive' : ∀ p ∈ interpText, live p.1)
    (hsub : ∀ p ∈ interpText, p ∈ dataOf Dt DA) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64} {need : Nat}
    (hneed : 4000 ≤ need) (hs2 : need ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000) (hs4 : 0x80100000 ≤ s.toNat - need)
    (hal : s.toNat % 16 = 0) (hra : (R 1).toNat % 4 = 0)
    (h2 : R 2 = s) (hstd : R 10 = 0x8001bb20#64) (hfmt : R 11 = 0x800192c0#64)
    (himp : ldv .ld Dt 0x8001b970 = 0x8001b538#64) (hDA : Cover (· ∈ DA) 0x8001b970 0x8001b978)
    (hdec : ldv .ld Mt 0x8001b898 = 0x80019770#64) (hdA : 0x80019770 ∈ DA ∧ 0x80019771 ∈ DA)
    (hdv : imgM Dt 0x80019770 = 0x2e#8 ∧ imgM Dt 0x80019771 = 0#8)
    {o : Bool} (hSo : StdoutSbAt (consoleFlagsV o) Mt) (hbase : ldv .ld Mt 0x8001bb38 ≠ 0#64) (hloc : LocMb Mt)
    (hL : LldFmt Dt DA) (hP1 : FmtAt Dt DA 0x800192c0 [37#8]) (hP2 : FmtAt Dt DA 0x800192c4 [0#8])
    (hk : ∀ R' M', RetOK R R' (BitVec.ofNat 64 (lldBytes (R 12)).length) → Frame M' Mt (FpReg (s.toNat - 80)) →
      ldv .lh M' 0x8001bb30 = 0x200a#64 →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs (lldBytes (R 12))) (R 1) R' M') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x800061c0#64 R Mt := by
  have hl := lldBytes_len (R 12)
  refine fprintf_via hlive hlive' hsub hneed hs2 hs3 hs4 hal hra (by omega) (by omega) h2 hstd himp hDA hdec hdA
    hdv hSo hbase hloc (fun R0 Mt0 G a2 a10 a11 a12 a13 a1 hdec0 hsb hloc0 harg hk0 => ?_) hk
  exact vfpInnerLld hlive hlive' hsub G.hs1 G.hs2 hs3 hs4 G.hal G.hf1 G.hf2 G.hfa G.hap1 G.hap2 G.hapa a1 a2 a10
    a11 (a12.trans hfmt) a13 hdec0 hdA hdv hsb hloc0 harg hL hP1 hP2 hk0

/-- `__sprint_r`'s bytes under `fprintf` lie in the stdout run's footprint. -/
theorem sprintReg_outS {s : BitVec 64} {need sp f a : Nat} (h1 : s.toNat - need + 1024 ≤ sp)
    (h2 : sp + 592 ≤ f) (h3 : f + 1208 ≤ s.toNat) (h : SprintReg f sp (sp + 224) a) : outS s need a := by
  unfold SprintReg SfvCallReg LoopReg SfvReg at h
  unfold outS stdioFoot Stdio.InRange impureW
  omega

/-- **`fprintf(stdout, P, str)`** with `P` the format `lit ++ "%s>"`: prints
`lit ++ bs ++ ">"`, `bs` the string at `str` (in the data view, off the run's
footprint). -/
theorem fprintf_s (hlive : ∀ p ∈ stdioText, live p.1) (hlive' : ∀ p ∈ interpText, live p.1)
    (hsub : ∀ p ∈ interpText, p ∈ dataOf Dt DA) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s P : BitVec 64} {need : Nat} {lit bs : List (BitVec 8)}
    (hneed : 4000 ≤ need) (hs2 : need ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000) (hs4 : 0x80100000 ≤ s.toNat - need)
    (hal : s.toNat % 16 = 0) (hra : (R 1).toNat % 4 = 0)
    (h2 : R 2 = s) (hstd : R 10 = 0x8001bb20#64) (hfmt : R 11 = P)
    (himp : ldv .ld Dt 0x8001b970 = 0x8001b538#64) (hDA : Cover (· ∈ DA) 0x8001b970 0x8001b978)
    (hdec : ldv .ld Mt 0x8001b898 = 0x80019770#64) (hdA : 0x80019770 ∈ DA ∧ 0x80019771 ∈ DA)
    (hdv : imgM Dt 0x80019770 = 0x2e#8 ∧ imgM Dt 0x80019771 = 0#8)
    {o : Bool} (hSo : StdoutSbAt (consoleFlagsV o) Mt) (hbase : ldv .ld Mt 0x8001bb38 ≠ 0#64) (hloc : LocMb Mt)
    (hlit : lit ≠ []) (hlits : ∀ b ∈ lit, b ≠ 0#8 ∧ b ≠ 37#8) (hlitL : lit.length ≤ 16)
    (hP1 : FmtAt Dt DA P.toNat (lit ++ [37#8])) (hPs : SFmt Dt DA (P.toNat + lit.length))
    (hP2 : FmtAt Dt DA (P.toNat + lit.length + 2) ([0x3e#8] ++ [0#8]))
    (hW : StrWin (R 12).toNat bs.length)
    (hstrD : ∀ i (h : i < bs.length), (R 12).toNat + i ∈ DA ∧ imgM Dt ((R 12).toNat + i) = bs[i])
    (hnz : ∀ b ∈ bs, b ≠ 0#8)
    (hnul : (R 12).toNat + bs.length ∈ DA ∧ imgM Dt ((R 12).toNat + bs.length) = 0#8)
    (hoff : ∀ i, i < bs.length → ¬ outS s need ((R 12).toNat + i))
    (hk : ∀ R' M', RetOK R R' (BitVec.ofNat 64 (lit.length + bs.length + 1)) →
      Frame M' Mt (FpReg (s.toNat - 80)) → ldv .lh M' 0x8001bb30 = 0x200a#64 →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs (lit ++ bs ++ [0x3e#8])) (R 1)
        R' M') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x800061c0#64 R Mt := by
  have hW1 := hW.lo; have hW2 := hW.hi; have hW3 := hW.htif
  unfold htifLo at hW3
  -- the string lies below the stack window or above it
  have hbl : bs.length + 32 < 2 ^ 31 := by
    rcases Nat.lt_or_ge ((R 12).toNat) (s.toNat - need) with hlo | hhi
    · refine Nat.lt_of_not_le fun hc => hoff (s.toNat - need - (R 12).toNat) (by omega) ?_
      unfold outS; right; right; omega
    · rcases Nat.eq_zero_or_pos bs.length with h0 | hp
      · omega
      · have := hoff 0 hp
        unfold outS at this
        omega
  have hctx : LCtx live (R 12) 0x8000cfcc#64 bs.length (imgM Dt) :=
    { regions := ⟨hW1, by omega, by omega, by unfold tohostAddr; omega⟩
      str := ⟨fun k hk => by rw [(hstrD k hk).2]; exact hnz _ (List.getElem_mem hk), hnul.2⟩
      retAlign := by decide
      code := fun p hp => hlive p (strCode_stdio p hp) }
  have hsubS : ∀ p ∈ strCode ++ strText (R 12).toNat bs.length (imgM Dt), p ∈ stdioText ++ dataOf Dt DA := by
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact List.mem_append_left _ (strCode_stdio p hp)
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
      rw [List.mem_range] at hk
      refine List.mem_append_right _ (List.mem_map.2 ⟨_, ?_, rfl⟩)
      rcases Nat.lt_or_ge k bs.length with hk' | hk'
      · exact (hstrD k hk').1
      · rw [show k = bs.length by omega]; exact hnul.1
  refine fprintf_via hlive hlive' hsub hneed hs2 hs3 hs4 hal hra (by omega) (by simp; omega) h2 hstd himp hDA
    hdec hdA hdv hSo hbase hloc (fun R0 Mt0 G a2 a10 a11 a12 a13 a1 hdec0 hsb hloc0 harg hk0 => ?_) hk
  have hG1 := G.hs1; have hG2 := G.hf1; have hG3 := G.hf2
  exact vfpInnerS (str := R 12) hlive hlive' hsub G.hs1 G.hs2 hs3 hs4 G.hal G.hf1 G.hf2 G.hfa G.hap1 G.hap2
    G.hapa a1 a2 a10 a11 (a12.trans hfmt) a13 hdec0 hdA hdv hsb hloc0 harg
    (fun h => by rw [h] at hW1; simp at hW1) hlit hlits hlitL hP1 hPs hP2 hbl hstrD
    ⟨hW1, by omega, by omega, fun i hi h => hoff i hi (sprintReg_outS hG1 hG2 hG3 h)⟩
    (fun R1 Mt1 r1 r10 k => strlen_sw hctx hsubS r1 r10 k) hk0

end VsaIris.Sym.Fp
