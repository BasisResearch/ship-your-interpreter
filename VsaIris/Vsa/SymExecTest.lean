import VsaIris.Vsa.SymExec
import VsaIris.Interp.Case.BinaryAddIntT

/-!
# `symRun_swp` on the interpreter binary

* `codeAt_interp`: the interpreter text footprint `interpText` is the fixed image over ten
  address ranges (one kernel evaluation), so every code pin of an `IW` run is supplied by
  `CodeAt` instead of per-pc `interp_at_*` lemmas.
* `BinaryAddIntT_run4_sym`: the landed `#ix_seg` piece `BinaryAddIntT_run4`, same statement,
  re-proved with ONE symbolic run (`ld`, `j`, four `ld`, `mv`, `addi`, stop at the `jr`)
  followed by the landed `jr` step.
* `loop_tree`: the loop body at `0x80003224` (`ld`/`sd` with store forwarding, `addi`, `bne`)
  executes in the kernel to a two-leaf tree.
-/

namespace VsaIris.SymExec.Test

open VsaIris VsaIris.Sym VsaIris.Interp VsaIris.SymExec Vsa.Sim Vsa.MemRepr Vsa.Sim.Code
open VsaIris.MallocFast

/-- Byte function of the loaded binary (text, then read-only data). -/
def binByte (a : Nat) : BitVec 8 :=
  if a < 0x80018be0 then fixedTextByte (a - 0x80000000) else fixedRodataByte (a - 0x80018be0)

/-- `interpText` as ranges of the binary image, in list order. -/
def interpRanges : List (Nat × Nat) :=
  [(0x800027ec, 0x800029fc), (0x80002df4, 0x80004308), (0x800043ec, 0x80004588),
   (0x80004640, 0x80004664), (0x800046a4, 0x80004764), (0x80019f58, 0x80019fdc),
   (0x80019ef8, 0x80019f28), (0x80019370, 0x8001937c), (0x80019f28, 0x80019f58),
   (0x80019fe0, 0x80019ff8)]

theorem interpText_eq : interpText = rangeText binByte interpRanges :=
  eqB_eq (by decide +kernel)

theorem codeAt_interp : CodeAt interpText binByte interpRanges := codeAt_of_eq interpText_eq

/-- Executor configuration for `IW` runs. -/
def cfgI (stops : List (BitVec 64)) : Cfg := ⟨binByte, interpRanges, iRegs, stops⟩

/-- `BinaryAddIntT_run4`, re-proved by one symbolic run and the landed `jr` step. -/
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
  refine symRun_entry (cfgI [0x80003404#64]) codeAt_interp hlive (by decide) (by decide) 9 _ R Mt ?_
  sym_eval
  simp only [Tree.WP, ObsOK, SOb.den, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, false_implies, implies_true, and_true, regsDen, memDen, SE.den, h2,
    hRA, hS0, hS1, hS2, hS3]
  refine ⟨?_, it_80003404 hlive (by simpa [upd] using hal) hk⟩
  and_intros
  all_goals first
    | (intro _; rfl)
    | sx_side
    | (intro b hb; simp only [mem_accAddrs_iff, VsaIris.InExt] at *; sx_addr)

/-- Same statement as the landed piece. -/
example : type_of% @BinaryAddIntT_run4_sym = type_of% @BinaryAddIntT_run4 := rfl

def leafCount : Tree → Nat
  | .leaf _ => 1
  | .br _ _ _ t f => leafCount t + leafCount f

def obsCount : Tree → Nat
  | .leaf s => s.obs.length
  | .br _ _ _ t f => obsCount t + obsCount f

/-- The loop body at `0x80003224`: 12 instructions with three stores, eight loads (forwarded or
disjoint by obligation) and the back-edge `bne`, evaluated in the kernel. -/
theorem loop_tree :
    leafCount (symRun (cfgI [0x800031d8#64]) 13 ⟨0x80003224#64, [], [], []⟩) = 2 ∧
    obsCount (symRun (cfgI [0x800031d8#64]) 13 ⟨0x80003224#64, [], [], []⟩) = 62 := by
  decide +kernel

end VsaIris.SymExec.Test

#print axioms VsaIris.SymExec.symRun_swp
#print axioms VsaIris.SymExec.Test.codeAt_interp
#print axioms VsaIris.SymExec.Test.BinaryAddIntT_run4_sym
#print axioms VsaIris.SymExec.Test.loop_tree
