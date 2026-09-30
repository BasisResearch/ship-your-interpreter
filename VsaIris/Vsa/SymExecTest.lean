import VsaIris.Interp.SymInterp
import VsaIris.Interp.Case.BinaryAddIntT

/-!
# `symRun_swp` on the interpreter binary

* `BinaryAddIntT_run4_sym`: the landed `#ix_seg` piece `BinaryAddIntT_run4`, same statement,
  re-proved with ONE symbolic run (`ld`, `j`, four `ld`, `mv`, `addi`, stop at the `jr`)
  followed by the landed `jr` step; its memory obligations are decided by `obCheck` from one
  `Geom` fact about the stack pointer.
* `BinaryAddIntT_run2_sym`: `BinaryAddIntT_run2` (data-view AST reads, stack loads, a spill),
  same statement, one symbolic run; all eleven memory obligations decided by `obCheck`.
* `loop_tree`: the loop body at `0x80003224` (`ld`/`sd` with store forwarding, `addi`, `bne`)
  executes in the kernel to a two-leaf tree.
-/

namespace VsaIris.SymExec.Test

open VsaIris VsaIris.Sym VsaIris.Interp VsaIris.SymExec Vsa.Sim Vsa.MemRepr Vsa.Sim.Code
open VsaIris.MallocFast

open VsaIris.SymExec.Interp

/-- `BinaryAddIntT_run4`, re-proved by one symbolic run and the landed `jr` step. All memory
obligations are decided by `obCheck` from one `Geom` fact about the stack pointer. -/
theorem BinaryAddIntT_run4_sym {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s ret v8 v9 v18 v19 : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hal : ret.toNat % 4 = 0)
    (h2 : R 2 = s + 18446744073709550528#64)
    (hRA : ldv .ld Mt (s + 18446744073709550528#64 + 1080#64).toNat = ret)
    (hS0 : ldv .ld Mt (s + 18446744073709550528#64 + 1072#64).toNat = v8)
    (hS1 : ldv .ld Mt (s + 18446744073709550528#64 + 1064#64).toNat = v9)
    (hS2 : ldv .ld Mt (s + 18446744073709550528#64 + 1056#64).toNat = v18)
    (hS3 : ldv .ld Mt (s + 18446744073709550528#64 + 1048#64).toNat = v19)
    (hk : IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q ret
      (upd (upd (upd (upd (upd (upd (upd R 19 v19) 1 ret) 8 v8) 18 v18) 10 (R 9)) 9 v9) 2
        (s + 18446744073709550528#64 + 1088#64)) Mt) :
    IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x800038d8#64 R Mt := by
  refine symRun_auto (cfgI [0x80003404#64]) codeAt_interp hlive (by decide) (by decide)
    [{ atom := .r 2, lo := 0x87800000, hi := 0x88000000 - 1088, amod := 16, sc := [(0, 1088)], dc := [] }]
    9 _ R Mt [] (fun _ h => nomatch h) (fun _ h => nomatch h) ?_ ?_
  · geom_auto [h2, hsf, InExt]
  sym_eval
  simp only [Tree.WP, ObsOK, SOb.den, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, false_implies, implies_true, and_true, regsDen, memDen, SE.den, h2,
    hRA, hS0, hS1, hS2, hS3]
  refine ⟨?_, (step% it 0x80003404) hlive (by simpa [upd] using hal) hk⟩
  and_intros
  sym_dec

/-- Same statement as the landed piece. -/
example : type_of% @BinaryAddIntT_run4_sym = type_of% @BinaryAddIntT_run4 := rfl

/-- `BinaryAddIntT_run2` (AST reads through the data view, stack loads and a spill), re-proved
by one symbolic run. The eleven memory obligations are decided by `obCheck`. -/
theorem BinaryAddIntT_run2_sym {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s aE inp aR w1 kL : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 32 ≤ 0x100000000)
    (hx3 : aX.toNat + 32 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h8 : R 8 = aX) (h2 : R 2 = s + 18446744073709550528#64) (h18 : R 18 = inp)
    (hright : ldv .ld m (aX + 24#64).toNat = aR)
    (hA : ldv .ld Mt (s.toNat - 1088) = aE)
    (hK : ldv .lw Mt (s + 18446744073709550528#64 + 120#64).toNat = kL)
    (hP : ldv .ld Mt (s + 18446744073709550528#64 + 128#64).toNat = w1)
    (hk : IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q (2147497240#64)
      (upd (upd (upd (upd (upd (upd R 12 aR) 13 aE) 16 kL) 10
        (s + 18446744073709550528#64 + 144#64)) 11 inp) 19 w1)
      (writeLog Mt [(s.toNat - 1088, 8, kL)])) :
    IW live m (binView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q (2147497212#64) R Mt := by
  refine symRun_auto (cfgI [0x80003518#64] [.r 8]) codeAt_interp hlive (by decide) (by decide)
    [{ atom := .r 2, lo := 0x87800000, hi := 0x88000000 - 1088, amod := 16, sc := [(0, 1088)],
       dc := [] },
     { atom := .r 8, lo := 0x80000000, hi := 0x100000000 - 32, amod := 1, sc := [],
       dc := [(0, 4), (8, 12), (16, 32)], gap := some (32, 16) }]
    20 _ R Mt [] (fun _ h => nomatch h) (fun _ h => nomatch h) ?_ ?_
  · geom_auto [h2, h8, hsf, InExt, binView]
  sym_eval
  simp only [Tree.WP, ObsOK, SOb.den, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, false_implies, implies_true, and_true, regsDen, memDen, SE.den, h2, h8, h18,
    hsf, hright, hA, hK, hP]
  refine ⟨?_, hk⟩
  and_intros
  sym_dec

example : type_of% @BinaryAddIntT_run2_sym = type_of% @BinaryAddIntT_run2 := rfl

def leafCount : Tree → Nat
  | .leaf _ => 1
  | .br _ _ _ _ t f => leafCount t + leafCount f
  | .jr _ _ => 1

def obsCount : Tree → Nat
  | .leaf s => s.obs.length
  | .br _ _ _ _ t f => obsCount t + obsCount f
  | .jr s _ => s.obs.length

/-- The loop body at `0x80003224`: 12 instructions with three stores, eight loads (forwarded or
disjoint by obligation) and the back-edge `bne`, evaluated in the kernel. -/
theorem loop_tree :
    leafCount (symRun (cfgI [0x800031d8#64]) 13 ⟨0x80003224#64, [], [], []⟩) = 2 ∧
    obsCount (symRun (cfgI [0x800031d8#64]) 13 ⟨0x80003224#64, [], [], []⟩) = 62 := by
  decide +kernel

end VsaIris.SymExec.Test

#print axioms VsaIris.SymExec.symRun_swp
#print axioms VsaIris.SymExec.Interp.codeAt_interp
#print axioms VsaIris.SymExec.Test.BinaryAddIntT_run4_sym
#print axioms VsaIris.SymExec.Test.loop_tree
#print axioms VsaIris.SymExec.Test.BinaryAddIntT_run2_sym
