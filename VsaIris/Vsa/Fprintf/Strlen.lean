import VsaIris.Vsa.Fprintf.Tac
import VsaIris.Interp.StrlenRun

/-!
# H3's `strlen` inside a stdout run (lane N5)

`_vfprintf_r`'s `%s` measures its argument with `strlen` (`0x8000cfc8`). H3
proved `strlen` over a string of any length (`StrlenRun.strlenRunL`), as a
leaf run: its own read-only list (`strCode` and the string's bytes), its own
registers (`sRegs`), no read-only register. `LocalRun.embed` runs a local
run over fewer registers, read-only cells and owned bytes inside one over
more: the extra registers and bytes stay as they were. `strlen_sw` is H3's
run so embedded in a stdout run whose data view holds `strlen`'s code and
the string.
-/

namespace VsaIris

variable {M : MachineModel}

/-- **Embedding a local run** over fewer read-only cells, registers and
owned bytes: the extra registers keep their base values `rvb`, the extra
bytes their base values `mvb`. -/
theorem LocalRun.embed {ro1 ro2 : List (Nat × BitVec 64)} {text1 text2 : List (Nat × BitVec 8)}
    {rs1 rs2 : List Nat} {S1 S2 : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hro : ∀ p ∈ ro1, p ∈ ro2) (ht : ∀ p ∈ text1, p ∈ text2) (hrs : ∀ r ∈ rs1, r ∈ rs2)
    (hS : ∀ a, S1 a → S2 a) (rvb : Nat → BitVec 64) (mvb : Nat → BitVec 8) :
    ∀ n rv mv, LocalRun M ro1 text1 rs1 S1 Q n rv mv → ∀ rv2 mv2, (∀ r ∈ rs1, rv2 r = rv r) →
      (∀ a, S1 a → mv2 a = mv a) → (∀ r ∈ rs2, r ∉ rs1 → rv2 r = rvb r) →
      (∀ a, S2 a → ¬ S1 a → mv2 a = mvb a) →
      LocalRun M ro2 text2 rs2 S2 (fun rv' mv' => ∃ rvq mvq, Q rvq mvq ∧ (∀ r ∈ rs1, rv' r = rvq r) ∧
        (∀ a, S1 a → mv' a = mvq a) ∧ (∀ r ∈ rs2, r ∉ rs1 → rv' r = rvb r) ∧
        (∀ a, S2 a → ¬ S1 a → mv' a = mvb a)) n rv2 mv2
  | 0, rv, mv, h, rv2, mv2, h1, h2, h3, h4 => ⟨rv, mv, h, h1, h2, h3, h4⟩
  | n + 1, rv, mv, h, rv2, mv2, h1, h2, h3, h4 => by
    rcases h with h | ⟨k, hseg⟩
    · exact .inl ⟨rv, mv, h, h1, h2, h3, h4⟩
    · refine .inr ⟨k, fun σ hok hro' hr hm => ?_⟩
      obtain ⟨σ', hreach, hok', hregs, hmem, hout, hK⟩ := hseg σ hok
        ⟨fun p hp => hro'.1 p (hro p hp), fun p hp => hro'.2 p (ht p hp)⟩
        (fun r hr1 => (hr r (hrs r hr1)).trans (h1 r hr1))
        (fun a ha => (hm a (hS a ha)).trans (h2 a ha))
      refine ⟨σ', hreach, hok', fun key hk => hregs key (fun h => hk (hrs key h)),
        fun a ha => hmem a (fun h => ha (hS a h)), hout, ?_⟩
      exact LocalRun.embed hro ht hrs hS rvb mvb n _ _ hK _ _ (fun _ _ => rfl) (fun _ _ => rfl)
        (fun r hr2 hr1 => (hregs r hr1).trans ((hr r hr2).trans (h3 r hr2 hr1)))
        (fun a ha2 ha1 => (hmem a ha1).trans ((hm a ha2).trans (h4 a ha2 ha1)))

end VsaIris

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Inst.Strlen
open VsaIris.Interp.StrLeaf

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}

/-- `strlen`'s registers are a stdout run's. -/
theorem sRegs_sub : ∀ r ∈ sRegs, r ∈ iRegs := by decide

/-- **`strlen(P)`** (`0x80006cf0`) inside a stdout run whose data view holds
`strlen`'s code and the string `[P, P + len]`: back at `r = ra` with `len` in
`a0`, `a1`–`a6` at some values, every other register and every owned byte as
it was. -/
theorem strlen_sw {P r : BitVec 64} {len : Nat} {bv : Nat → BitVec 8} (c : LCtx live P r len bv)
    (hsub : ∀ p ∈ strCode ++ strText P.toNat len bv, p ∈ stdioText ++ dataOf Dt DA)
    {R : Nat → BitVec 64} {Mt : Mem} (h1 : R 1 = r) (h10 : R 10 = P)
    (hk : ∀ v : Nat → BitVec 64, SWPO live (stdioText ++ dataOf Dt DA) iRegs S Q t r
      (upd (updAll R v [11, 12, 13, 14, 15, 16]) 10 (BitVec.ofNat 64 len)) Mt) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs S Q t 0x80006cf0#64 R Mt := by
  obtain ⟨n, hn⟩ := strlenRunL (S := fun _ => False) (Mt := Mt) c h1 h10
  refine ⟨n, fun rv mv hm => ?_⟩
  have hL := LocalRun.embed (M := VsaIris.Inst.vsaModel live) (ro2 := roR) (S1 := fun _ => False) (rs2 := iRegs) (S2 := S)
    (fun p hp => by cases hp) hsub sRegs_sub (fun a (h : False) => h.elim) rv mv n rv mv
    (hn rv mv ⟨hm.pc, fun r hr hne => hm.regs r (sRegs_sub r hr) hne, fun a h => h.elim⟩) rv mv
    (fun _ _ => rfl) (fun _ (h : False) => h.elim) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  refine LocalRun.mono (fun rv' mv' ⟨rvq, mvq, ⟨hpc, hra, ha0⟩, hq1, _, hq3, hq4⟩ => ?_) n rv mv hL
  refine swpo_run (hk rv') ⟨?_, fun x hx hne => ?_, fun a ha => ?_⟩
  · exact (hq1 32 (by decide)).trans hpc
  · simp only [upd_apply, updAll_apply]
    by_cases e10 : x = 10
    · subst e10; rw [if_pos rfl, hq1 10 (by decide), ha0]
    rw [if_neg e10]
    by_cases hx6 : x ∈ [11, 12, 13, 14, 15, 16]
    · rw [if_pos hx6]
    rw [if_neg hx6]
    by_cases e1 : x = 1
    · subst e1; rw [hq1 1 (by decide), hra, h1]
    have hxs : x ∉ sRegs := by
      simp only [sRegs, List.mem_cons, List.not_mem_nil, or_false] at hx6 ⊢
      simp only [VsaIris.PC] at hne; omega
    rw [hq3 x hx hxs, hm.regs x hx hne]
  · rw [hq4 a ha (fun h => h), hm.img a ha]

end VsaIris.Sym.Fp
