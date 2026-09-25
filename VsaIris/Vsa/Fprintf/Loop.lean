import VsaIris.Vsa.Fprintf.Lld

/-!
# `_vfprintf_r`'s main loop state (lane N5, shared with N3)

After its `FILE` checks, `_vfprintf_r` (`0x8000a944`) spills the other
callee-saved registers, sets up the `uio` at `sp + 224` (iov array at
`sp + 352`, count at `sp + 232`, residual at `sp + 240`) and enters the main
loop at `0x8000a9b0` with the format pointer in `s8`. `VfpLoop` is the state
at the loop head: every conversion returns there with the iov array empty
(its pieces printed). `vfp_head` is `0x8000a944` → `0x8000a9b0`,
FILE-independent (N3's stderr path and N5's stack `FILE` share it).
-/

namespace VsaIris.Sym.Fp

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

local macro_rules | `(tactic| sx_side) => `(tactic| closed_decide)

variable {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- **The main loop head** `0x8000a9b0` of `_vfprintf_r(reent, f, …)` with
frame `sp`, format pointer `P`, `cnt` bytes counted, the iov array empty. -/
structure VfpLoop (R : Nat → BitVec 64) (Mt : Mem) (sp reent f P : BitVec 64) (cnt : Nat) : Prop where
  spR : R 2 = sp
  s1 : R 9 = 0x8001b798#64
  s2 : R 18 = 16#64
  s3 : R 19 = 37#64
  s5 : R 21 = sp + 352#64
  s7 : R 23 = sp + 352#64
  fmt : R 24 = P
  reent : ldv .ld Mt sp.toNat = reent
  file : ldv .ld Mt (sp + 8#64).toNat = f
  count : ldv .ld Mt (sp + 16#64).toNat = BitVec.ofNat 64 cnt
  base : ldv .ld Mt (sp + 224#64).toNat = sp + 352#64
  iovcnt : ldv .lw Mt (sp + 232#64).toNat = 0#64
  resid : ldv .ld Mt (sp + 240#64).toNat = 0#64

/-- The caller's callee-saved registers `C` in `_vfprintf_r`'s frame (the
epilogue reloads them). -/
structure VfpSpills (Mt : Mem) (sp : BitVec 64) (C : Nat → BitVec 64) : Prop where
  ra : ldv .ld Mt (sp.toNat + 584) = C 1
  s0 : ldv .ld Mt (sp.toNat + 576) = C 8
  s1 : ldv .ld Mt (sp + 568#64).toNat = C 9
  s2 : ldv .ld Mt (sp + 560#64).toNat = C 18
  s3 : ldv .ld Mt (sp + 552#64).toNat = C 19
  s4 : ldv .ld Mt (sp.toNat + 544) = C 20
  s5 : ldv .ld Mt (sp + 536#64).toNat = C 21
  s6 : ldv .ld Mt (sp.toNat + 528) = C 22
  s7 : ldv .ld Mt (sp + 520#64).toNat = C 23
  s8 : ldv .ld Mt (sp + 512#64).toNat = C 24
  s9 : ldv .ld Mt (sp + 504#64).toNat = C 25
  s10 : ldv .ld Mt (sp + 496#64).toNat = C 26
  s11 : ldv .ld Mt (sp + 488#64).toNat = C 27

/-- The bytes `vfp_head` writes: reent/`FILE`/count at `sp`, the zeroed slots
`40`, `72`–`96`, `144`, the `uio` at `224`, and the nine spill slots. The
entry's slots (`ap` at `24`, the decimal point at `56`/`64`, the `mbstate` at
`200`, `ra`/`s0`/`s4`/`s6`) are outside. -/
def HeadReg (sp : Nat) (a : Nat) : Prop :=
  (sp ≤ a ∧ a < sp + 24) ∨ (sp + 40 ≤ a ∧ a < sp + 48) ∨ (sp + 72 ≤ a ∧ a < sp + 104) ∨
    (sp + 144 ≤ a ∧ a < sp + 152) ∨ (sp + 224 ≤ a ∧ a < sp + 248) ∨ (sp + 488 ≤ a ∧ a < sp + 528) ∨
    (sp + 536 ≤ a ∧ a < sp + 544) ∨ (sp + 552 ≤ a ∧ a < sp + 576)

/-- The state `vfp_head` hands the loop: `VfpLoop` (reent `s0`, `FILE` `s4`,
format `s6`), the nine spills, the kept registers, the frame. -/
structure VfpHeadPost (R R' : Nat → BitVec 64) (Mt Mt' : Mem) (sp : BitVec 64) : Prop where
  loop : VfpLoop R' Mt' sp (R 8) (R 20) (R 22) 0
  keep : ∀ x ∈ [1, 8, 20, 22, 25, 26, 27], R' x = R x
  s1 : ldv .ld Mt' (sp + 568#64).toNat = R 9
  s2 : ldv .ld Mt' (sp + 560#64).toNat = R 18
  s3 : ldv .ld Mt' (sp + 552#64).toNat = R 19
  s5 : ldv .ld Mt' (sp + 536#64).toNat = R 21
  s7 : ldv .ld Mt' (sp + 520#64).toNat = R 23
  s8 : ldv .ld Mt' (sp + 512#64).toNat = R 24
  s9 : ldv .ld Mt' (sp + 504#64).toNat = R 25
  s10 : ldv .ld Mt' (sp + 496#64).toNat = R 26
  s11 : ldv .ld Mt' (sp + 488#64).toNat = R 27
  frame : Frame Mt' Mt (HeadReg sp.toNat)

#ix_piece vfpHead_1 {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s sp : BitVec 64} {need : Nat}
    (hs1 : s.toNat - need + 1024 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat) (hs3 : s.toNat ≤ 0x88000000)
    (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (h2 : R 2 = sp) (h3 : R 3 = 0x8001b510#64)
    (hk : ∀ R' Mt', VfpHeadPost R R' Mt Mt' sp →
      SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a9b0#64 R' Mt') :
    SWPO live (stdioText ++ dataOf Dt DA) iRegs (outS s need) Q t 0x8000a944#64 R Mt by
  nf_go 2 [14] hlive using [h2, h3, BitVec.add_assoc] at 2147527088

#ix_piece vfpHead_2 from vfpHead_1 by
  nf_go 1 [14] hlive using [h2, h3, BitVec.add_assoc] at 2147527088

#ix_piece vfpHead_3 from vfpHead_2 by
  refine hk _ _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try rsimp)
  all_goals try (first | exact f2.trans h2 | exact f21 | exact f23 | exact f22)
  all_goals try (nx_mem; done)
  all_goals try (nx_mem; rfl)
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rsimp <;> assumption

#ix_piece vfpHead_4 from vfpHead_3 by
  repeat (refine Frame.snoc ?_ ?_)
  all_goals first | exact Frame.refl _ _ |
    (intro b h1 h2; simp (config := {failIfUnchanged := false}) (disch := omega) only [toNat_add_lit] at h1 h2
     unfold HeadReg; omega)

/-! **`vfp_head`**: `_vfprintf_r`'s head, `0x8000a944` → `0x8000a9b0` (post `VfpHeadPost`). -/
#ix_chain vfp_head := [vfpHead_1, vfpHead_2, vfpHead_3, vfpHead_4]

end VsaIris.Sym.Fp
