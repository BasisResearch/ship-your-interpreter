import VsaIris.Interp.SymFront

/-!
# Checks of the extended executor

Each example runs `xrun` across a construct the executor of `SymExec.lean` stops at, and closes
every reached state with the continuation hypothesis; an extra reached state is an unsolved goal.

* `eval`'s expression dispatch (`0x800028fc`) with an unknown tag: the bound check `bltu` forks,
  its fall-through side records `tag <u 6`, and the table load splits the run over the six table
  entries read from `.rodata` (seven reached states).
* The same dispatch with the tag known from the entry memory: the bound check is decided and the
  table entry is a constant, so the run reaches one state.
* `_fputc_r`'s orientation block (`0x80005100`): the flags written by `sh` are read back by `lhu`
  (width-exact forwarding), so the three branches that follow are decided by constants.
-/

namespace VsaIris.SymExec.Front.Test

open VsaIris VsaIris.Sym Vsa.Sim Vsa.MemRepr VsaIris.MallocFast

example {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    {A : BitVec 64} (h10 : R 10 = A) (hlo : 0x80100000 ≤ A.toNat) (hhi : A.toNat + 8 ≤ 0x80200000)
    (hk : ∀ pc R' M', SWP live (interpText ++ dataOf Dt DA) iRegs
      (fun b => A.toNat ≤ b ∧ b < A.toNat + 8) Q pc R' M') :
    IW live Dt DA (fun b => A.toNat ≤ b ∧ b < A.toNat + 8) Q 0x800028fc#64 R Mt := by
  xrun hlive using [h10] at 2147494236 2147494260 2147494288 2147494308 2147494184 2147494216
    2147494316
  all_goals exact hk _ _ _

example {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    {A : BitVec 64} (h10 : R 10 = A) (hlo : 0x80100000 ≤ A.toNat) (hhi : A.toNat + 8 ≤ 0x80200000)
    (hlw : ldv .lw Mt A.toNat = 3#64) (hlwu : ldv .lwu Mt A.toNat = 3#64)
    (hk : ∀ pc R' M', SWP live (interpText ++ dataOf Dt DA) iRegs
      (fun b => A.toNat ≤ b ∧ b < A.toNat + 8) Q pc R' M') :
    IW live Dt DA (fun b => A.toNat ≤ b ∧ b < A.toNat + 8) Q 0x800028fc#64 R Mt := by
  xrun hlive using [h10, hlw, hlwu] at 2147494236 2147494260 2147494288 2147494308 2147494184
    2147494216 2147494316
  exact hk _ _ _

example {live : Nat → Prop} (hlive : ∀ p ∈ stdioText, live p.1) {Dt : Mem} {DA : List Nat}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (h8 : R 8 = 0x8001bb20#64) (h14 : R 14 = 0x000a#64) (h11 : R 11 = 0x2000#64)
    (h15 : R 15 = 0x2000#64) (h12 : R 12 = 0x2000#64)
    (hk : ∀ pc R' M', SWP live (stdioText ++ dataOf Dt DA) iRegs
      (fun b => 0x8001bb30 ≤ b ∧ b < 0x8001bbd4) Q pc R' M') :
    NW live Dt DA (fun b => 0x8001bb30 ≤ b ∧ b < 0x8001bbd4) Q 0x80005100#64 R Mt := by
  xrun hlive using [h8, h14, h11, h15, h12] at 2147504640 2147504424
  exact hk _ _ _

end VsaIris.SymExec.Front.Test
