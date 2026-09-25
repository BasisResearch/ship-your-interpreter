import VsaIris.Vsa.SymLeaf
import VsaIris.Vsa.Stdout.Tac
import VsaIris.Interp.StrlenRun
import VsaIris.Interp.StrIris

/-!
# `strlen` inside a stdout run (lane N1)

`fputs` calls `strlen` on its string. The string leaves' symbolic run
(`StrLeaf.strlenRunL`: registers `sRegs`, no owned byte, read-only bytes
`strCode` and the string) is spliced into a stdout run by `swpo_leaf`; its
code bytes are part of `stdioText` (`scripts/gen_interp_steps.py --table
stdio`, `STDIO_CODE_ONLY`).
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Inst

theorem strCode_sub_stdio : ∀ q ∈ strCode, q ∈ stdioText := by decide +kernel

/-- The registers after `strlen` returns `len`: `a0`, and `a1`–`a6` at any values. -/
abbrev strlenRegs (R : Nat → BitVec 64) (len : Nat) (v11 v12 v13 v14 v15 v16 : BitVec 64) :
    Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd R 10 (BitVec.ofNat 64 len)) 11 v11) 12 v12) 13 v13) 14 v14) 15 v15)
    16 v16

/-- **`strlen(P)` inside a stdout run**: from its entry, over the string
`[P, P + len]` in the run's data view, it returns `len` in `a0` with `a1`–`a6`
clobbered and everything else unchanged. -/
theorem swpo_strlen {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {t : String}
    {R : Nat → BitVec 64} {Mt : Mem} {P r : BitVec 64} {len : Nat} {bv : Nat → BitVec 8}
    (c : StrLeaf.LCtx live P r len bv) (h1 : R 1 = r) (h10 : R 10 = P)
    (hD : ∀ q ∈ Strlen.strText P.toNat len bv, q ∈ dataOf Dt DA)
    (hk : ∀ v11 v12 v13 v14 v15 v16 : BitVec 64,
      SWPO live (stdioText ++ dataOf Dt DA) iRegs S Q t r (strlenRegs R len v11 v12 v13 v14 v15 v16) Mt) :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs S Q t 0x80006cf0#64 R Mt := by
  refine swpo_leaf (T := strCode ++ Strlen.strText P.toNat len bv) (rs' := sRegs)
    (S' := fun _ => False) (Q1 := StrLeaf.LenEnd r len)
    (fun q hq => ?_) (by decide) (by decide) (fun _ h => h.elim)
    (StrLeaf.strlenRunL c h1 h10) (fun rv mv ⟨e32, e1, e10⟩ hfr hmem => ?_)
  · rcases List.mem_append.mp hq with hq | hq
    · exact List.mem_append_left _ (strCode_sub_stdio q hq)
    · exact List.mem_append_right _ (hD q hq)
  refine swpo_run (hk (rv 11) (rv 12) (rv 13) (rv 14) (rv 15) (rv 16)) ⟨e32, fun x hx hpc => ?_,
    fun a ha => hmem a ha id⟩
  by_cases hs : x ∈ sRegs
  · simp only [sRegs, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hpc
    all_goals simp [upd_apply, e1, e10, h1]
  · rw [hfr x hx hs]
    have : x ≠ 10 ∧ x ≠ 11 ∧ x ≠ 12 ∧ x ≠ 13 ∧ x ≠ 14 ∧ x ≠ 15 ∧ x ≠ 16 := by
      simp only [sRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs; omega
    simp [upd_apply, this]

end VsaIris.Sym
