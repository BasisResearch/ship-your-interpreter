import VsaIris.Vsa.Fprintf.Sbprintf

/-!
# `_vfprintf_r(reent, stdout, fmt, ap)` and `fprintf` (lane N5)

On `stdout` (unbuffered, `__SNBF|__SWR`, `_flags2 = 0`) `_vfprintf_r` takes
the stub lock and then orients the stream: the `ORIENT` test on this route is
at `0x8000af54` (`bltz` → `0x8000a918` when oriented, else `j 0x8000a8fc`).
From `_flags = 0x000a` (`interp_run`'s entry) the block
`0x8000a8fc`–`0x8000a914` stores `_flags2 & ~0x2000 = 0` (the bytes it read:
`Frame.restore`) and `_flags = 0x200a` (`stdoutSb_orient`). Both routes meet
at `0x8000a924` with `stdout` oriented at a memory `Mo` differing from the
entry's at most in `_flags` (`swp_flagsGen`, `vfp_outer_1`); one script
(`vfp_tail`) continues both (`vfp_outer_2`, `vfp_outer_3`). The prologue then
takes the `__sbprintf` branch (`(flags & 0x1a) == 0x0a`, a
descriptor, no `__SNPT`): after the entry (N3's `vfpEntry_run`) and the
stub lock it calls `__sbprintf(reent, stdout, fmt, ap)` (the hook `hS`,
`sbprintf_run`) and returns its count (`vfp_outer`).
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

local macro_rules | `(tactic| sx_side) => `(tactic| closed_decide)

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- The bytes the outer `_vfprintf_r` changes: its frame, `__sbprintf`'s and
the callee frames below, `stdout`'s flags, `errno`. -/
def OuterReg (sp : Nat) (a : Nat) : Prop :=
  (sp - 2288 ≤ a ∧ a < sp + 592) ∨ (0x8001bb30 ≤ a ∧ a < 0x8001bb32) ∨ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c)

/-- `stdout`'s `_flags`, the bytes `ORIENT` changes. -/
abbrev FlagsReg (a : Nat) : Prop := 0x8001bb30 ≤ a ∧ a < 0x8001bb32

/-- A store of the bytes already there. -/
theorem Frame.restore (M : Mem) {Reg : Nat → Prop} {b w : Nat} (v : BitVec 64)
    (hw : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8) (hv : imgLE (imgM M) b w = v.toNat % 2 ^ (8 * w)) :
    Frame (writeLog M [(b, w, v)]) M Reg := fun a _ => by
  by_cases h : b ≤ a ∧ a < b + w
  · exact imgM_store_restore M v hw hv h
  · exact imgM_store_miss M v (by omega)

theorem imgLE4_of_ldv_lw {M : Mem} {a : Nat} (h : ldv .lw M a = 0#64) : imgLE (imgM M) a 4 = 0 := by
  rw [ldv_lw_img] at h
  have hl := imgLE_lt (imgM M) a 4
  generalize imgLE (imgM M) a 4 = x at h hl
  have h3 := congrArg (fun y : BitVec 64 => (y.setWidth 32).toNat) h
  simp only [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.toNat_setWidth,
    BitVec.toNat_signExtend, BitVec.toNat_ofNat] at h3
  split at h3 <;> omega

/-- The memory after `ORIENT`'s stores (`sw 0` to `_flags2`, `sh 0x200a` to `_flags`). -/
abbrev orientMem (M : Mem) : Mem :=
  writeLog (writeLog M [(0x8001bbd0, 4, 0#64)]) [(0x8001bb30, 2, 0x200a#64)]

/-- **`ORIENT` from either orientation**: `_flags2` is rewritten with its
bytes, `_flags` becomes `0x200a`, the other fields are untouched. -/
theorem stdoutSb_orient {fl : BitVec 64} {M : Mem} (h : StdoutSbAt fl M) :
    Frame (orientMem M) M FlagsReg ∧ StdoutSb (orientMem M) := by
  have hF : Frame (orientMem M) M FlagsReg :=
    (Frame.restore M 0#64 (by decide) (by rw [imgLE4_of_ldv_lw h.flags2]; rfl)).snoc fun b h1 h2 => ⟨h1, h2⟩
  have l : ∀ (kd : MKind) (a : Nat), a + widthOfM kd ≤ 0x8001bb30 ∨ 0x8001bb32 ≤ a →
      ldv kd (orientMem M) a = ldv kd M a := fun kd a ha => hF.ldv kd fun j hj h => by
    obtain ⟨h1, h2⟩ := h; omega
  refine ⟨hF, ?_, ?_, (l _ _ (.inr (by decide))).trans h.fdU, (l _ _ (.inr (by decide))).trans h.fd,
    (l _ _ (.inr (by decide))).trans h.flags2, (l _ _ (.inr (by decide))).trans h.cookie,
    (l _ _ (.inr (by decide))).trans h.writer, (l _ _ (.inl (by decide))).trans h.sinit⟩
  · rw [ldv_lhu_hit _ _ rfl]; decide
  · rw [ldv_lh_hit _ _ rfl]; decide

/-- A run state at a memory `Mo` that differs from `M0` at most in `_flags`
and holds the oriented fields. -/
theorem swp_flagsGen {live : Nat → Prop} {text : List (Nat × BitVec 8)} {rs : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {pc : BitVec 64} {R : Nat → BitVec 64} {M0 M : Mem}
    (hF : Frame M M0 FlagsReg) (hS : StdoutSb M)
    (h : ∀ Mo, Frame Mo M0 FlagsReg → StdoutSb Mo → SWP live text rs S Q pc R Mo) :
    SWP live text rs S Q pc R M := h M hF hS

#ix_piece vfp_outer_1 {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sp fmt ap : BitVec 64} {need N : Nat} {bytes : List (BitVec 8)}
    (hs1 : s.toNat - need + 3312 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0) (hra : (R 1).toNat % 4 = 0)
    (h2 : R 2 = sp + 592#64) (h10 : R 10 = 0x8001b538#64) (h11 : R 11 = 0x8001bb20#64) (h12 : R 12 = fmt)
    (h13 : R 13 = ap)
    (hdec : ldv .ld Mt 0x8001b898 = 0x80019770#64) (hdA : 0x80019770 ∈ DA ∧ 0x80019771 ∈ DA)
    (hdv : imgM Dt 0x80019770 = 0x2e#8 ∧ imgM Dt 0x80019771 = 0#8)
    {o : Bool} (hSo : StdoutSbAt (consoleFlagsV o) Mt) (hbase : ldv .ld Mt 0x8001bb38 ≠ 0#64)
    (hS : ∀ (R0 : Nat → BitVec 64) (Mt0 : Mem), R0 2 = sp → R0 10 = 0x8001b538#64 → R0 11 = 0x8001bb20#64 →
      R0 12 = fmt → R0 13 = ap → R0 1 = 0x8000ac24#64 → StdoutSb Mt0 →
      Frame Mt0 Mt (fun a => (sp.toNat ≤ a ∧ a < sp.toNat + 592) ∨ FlagsReg a) →
      (∀ R' M', R' 10 = BitVec.ofNat 64 N → R' 2 = sp → R' 1 = 0x8000ac24#64 → (∀ x ∈ vfpSaved, R' x = R0 x) →
        Frame M' Mt0 (SbpReg (sp.toNat - 1264)) → ldv .lh M' 0x8001bb30 = 0x200a#64 →
        SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs bytes) 0x8000ac24#64 R' M') →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000dda8#64 R0 Mt0)
    (hk : ∀ R' M', R' 10 = BitVec.ofNat 64 N → R' 2 = R 2 → R' 1 = R 1 → (∀ x ∈ vfpSaved, R' x = R x) →
      Frame M' Mt (OuterReg sp.toNat) → ldv .lh M' 0x8001bb30 = 0x200a#64 →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q (t ++ putcs bytes) (R 1) R' M') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a884#64 R Mt by
  have hsp : (sp + 592#64).toNat = sp.toNat + 592 := sp_lit (by omega)
  have hsp' : R 2 - 592#64 = sp := by rw [h2, BitVec.add_sub_cancel]
  refine vfpEntry_run hlive t Mt R s need (by rw [h2, hsp]; omega) (by rw [h2, hsp]; omega) hs3 hs4
    (by rw [h2, hsp]; omega) (R 1) _ _ _ _ rfl h10 h11 h12 h13 hdec hdA hdv fun R1 Mt1 E => ?_
  rw [hsp'] at E
  have hFrE : Frame Mt1 Mt (fun a => sp.toNat ≤ a ∧ a < sp.toNat + 592) := E.frame
  have hl : ∀ (kd : MKind) (a : Nat), a + 8 ≤ sp.toNat ∨ sp.toNat + 592 ≤ a → widthOfM kd ≤ 8 →
      ldv kd Mt1 a = ldv kd Mt a := fun kd a ha hw => hFrE.ldv kd fun j hj h => by omega
  have hb' : (ldv .ld Mt1 0x8001bb38 = 0#64) = False := eq_false (by rw [hl .ld _ (.inl (by omega)) (by decide)]; exact hbase)
  have hSo1 := hSo.frame hFrE fun a h1 h2 h => by omega
  have h8 := E.s0; have h20 := E.s4; have h22 := E.s6; have h2' := E.sp_eq
  have hap := E.ap
  have h2w : PLift (R 2 = sp + 592#64) := ⟨h2⟩
  clear hl hsp' hsp h2
  -- the `ORIENT` test (`0x8000af54`); both routes meet at `0x8000a924` with
  -- `_flags = 0x200a`, the dead `a2`/`a3` apart
  cases o
  case' true =>
    have hSo1 : StdoutSb Mt1 := hSo1
    nf_go 3 [14] hlive using [h2', h8, h20, h10, h11, h22, h12, hSo1.flags, hSo1.flagsU, hSo1.flags2, hSo1.fd,
      hSo1.sinit, hb', BitVec.add_assoc] at 2147526948
    refine swp_flagsGen (Frame.refl _ _) hSo1 fun Mo hFo hSoO => ?_
  case' false =>
    have hSo1 : StdoutSbAt 0x000a#64 Mt1 := hSo1
    nf_go 3 [14] hlive using [h2', h8, h20, h10, h11, h22, h12, hSo1.flags, hSo1.flagsU, hSo1.flags2, hSo1.fd,
      hSo1.sinit, hb', BitVec.add_assoc] at 2147526948
    refine swp_flagsGen (stdoutSb_orient hSo1).1 (stdoutSb_orient hSo1).2 fun Mo hFo hSoO => ?_

set_option hygiene false in
/-- From the rejoin `0x8000a924` (`stdout` oriented at `Mo`, which differs
from `Mt1` at most in `_flags`): the `__sbprintf` branch, the call (`hS`), the
epilogue (`hk`). The same script closes both routes' leftovers. -/
local macro "vfp_tail" : tactic => `(tactic| (
        have lo : ∀ (kd : MKind) (a : Nat), a + widthOfM kd ≤ 0x8001bb30 ∨ 0x8001bb32 ≤ a →
            ldv kd Mo a = ldv kd Mt1 a := fun kd a ha => hFo.ldv kd fun j hj h => by
          obtain ⟨h1, h2⟩ := h; omega
        have hbo : (ldv .ld Mo 0x8001bb38 = 0#64) = False := by rw [lo _ _ (.inr (by decide))]; exact hb'
        nf_go 3 [14] hlive using [h2', h8, h20, h10, h11, h22, h12, hSoO.flags, hSoO.flagsU, hSoO.flags2, hSoO.fd,
          hSoO.sinit, hbo, BitVec.add_assoc] at 2147540392
        have eo : ∀ k : Nat, k ≤ 600 → (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := fun k hk => sp_lit (by omega)
        have hap' : ldv .ld Mo (sp + 24#64).toNat = ap := by
          rw [eo 24 (by omega), lo _ _ (.inr (by omega))]; exact hap.trans h13
        have hFrO : Frame Mo Mt (fun a => (sp.toNat ≤ a ∧ a < sp.toNat + 592) ∨ FlagsReg a) :=
          (hFrE.mono fun a h => .inl h).trans (hFo.mono fun a h => .inr h)
        nx_flat
        refine hS _ _ (f2.trans h2') f10 f11 f12 (f13.trans hap') f1 hSoO hFrO
          fun R2 M2 e10 e2 e1 ek hfr2 hfl2 => ?_
        have hlo : ∀ k, 8 ≤ k → k + 8 ≤ 592 → ldv .ld M2 (sp + BitVec.ofNat 64 k).toNat = ldv .ld Mt1 (sp.toNat + k) :=
          fun k h1 h2 => by
            rw [eo k (by omega), ← lo _ _ (.inr (by omega))]
            exact hfr2.ldv .ld fun j hj h => by simp only [widthOfM] at hj; unfold SbpReg at h; omega
        have l584 := (hlo 584 (by omega) (by omega)).trans E.ra
        have l576 := (hlo 576 (by omega) (by omega)).trans E.s0v
        have l544 := (hlo 544 (by omega) (by omega)).trans E.s4v
        have l528 := (hlo 528 (by omega) (by omega)).trans E.s6v
        nx_run hlive using [e2, e10, l584, l576, l544, l528, BitVec.add_assoc]
        have hst : Frame (writeLog M2 [((sp + 16#64).toNat, 8, BitVec.ofNat 64 N)]) M2
            (fun a => sp.toNat + 16 ≤ a ∧ a < sp.toNat + 24) :=
          Frame.store M2 _ fun b h1 h2 => by rw [eo 16 (by omega)] at h1 h2; exact ⟨h1, h2⟩
        refine hk _ _ (by rsimp) (by rsimp; exact h2w.down.symm) (by rsimp) (fun x hx => ?_) ?_ ?_
        · simp only [vfpSaved, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rsimp <;>
            (rw [ek _ (by decide)]; rsimp; first | rfl | (simp only [f9, f18, f19, f21, f23, f24, f25, f26, f27]; exact E.keep _ (by decide)))

        · refine ((hFrO.mono fun a h => ?_).trans (hfr2.mono fun a h => ?_)).trans (hst.mono fun a h => ?_)
          · unfold OuterReg; omega
          · unfold OuterReg; unfold SbpReg at h
            rcases h with ⟨h1, h2⟩ | h | h
            · exact .inl ⟨by rw [Nat.sub_sub] at h1; exact h1, by omega⟩
            · exact .inr (.inl h)
            · exact .inr (.inr h)
          · unfold OuterReg; omega
        · rw [ldv_lh_miss _ _ (.inl (by rw [eo 16 (by omega)]; omega))]; exact hfl2))

#ix_piece vfp_outer_2 from vfp_outer_1 at 1 by vfp_tail

#ix_piece vfp_outer_3 from vfp_outer_1 at 2 by vfp_tail

/-! **`vfp_outer`**: the outer `_vfprintf_r` on `stdout`, from either orientation. -/
#ix_tree vfp_outer := vfp_outer_1 [vfp_outer_2, vfp_outer_3]

end VsaIris.Sym.Fp
