import VsaIris.Interp.SeqLoopClosure

/-!
# The call arm's argument loop: the statement (lane E4, for lane E6)

INTERP_DESIGN.md §4.3: `EvalArgs` (the `args[32]` fill of `eval_expr`'s call
arm) is a loop lemma, not a spec. This file states it; lane E6 proves it,
lane E4 (the call cases) takes it as a hypothesis.

The loop is `0x800031d8`..`0x80003250` (`interp.c:253-254`):

```
800031d8  blez a5, 80003254          -- argc = 0: no arguments
800031dc  ld   a2,16(s0)             -- args array
   …      a2 = args[i]; a4 = sp+240+24i (spilled at sp+0); a1 = in; a0 = sp+64
80003220  jal  eval_expr             -- the child, into the slot sp+64
   …      copy sp+64..88 to sp+240+24i; i += 1 (sp+16); a5 = argc (sp+24);
          a3 = env (sp+8)
80003250  bne  a6,a5,800031dc
80003254  (the kind dispatch)
```

It starts at the `blez` (`0x800031d8`) with `a6 = 0`, `a5 = argc`, `a3 = env`,
`s0` the call node, `s2 = in` and `sp` lowered by 1088, and it ends at
`0x80003254` with `a5 = argc` (the arity test and the natives read it) and the
callee-saved registers kept. What it writes in `eval_expr`'s frame is the
spill words `sp+0..32`, the child slot `sp+64..88` and the argument array
`sp+240..240+24·argc` (`ArgsScratch`); every other frame byte (the callee's
value at `sp+96`, the spilled registers) is unchanged. The arguments' words
are the values' (`valsImg`: `valImg` of each slot of the reached image,
persistent).

Total mode is the recursor motive of `EvalArgsCost`, partial mode a structural
motive over the argument list (the children through the Löb hypothesis
`evalSpecsP`), with the return/abort continuations an ADDITIVE pair (§10.1).
Both are stated from the loop head's registers and the frame's image, the
shape of `closureSeqT_body` (`SeqLoopClosure.lean`).
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While

/-- `eval_expr`'s frame: the 1088 bytes below the entry `sp`. -/
abbrev evalS (s : BitVec 64) : Nat → Prop := InExt (s.toNat - 1088, 1088)

/-- What the argument loop writes in the frame: the spill words `sp+0..32`,
the child's result slot `sp+64..88`, the argument array `sp+240..`. -/
def ArgsScratch (s : BitVec 64) (argc : Nat) (a : Nat) : Prop :=
  InExt (s.toNat - 1088, 32) a ∨ InExt (s.toNat - 1088 + 64, 24) a ∨
    InExt (s.toNat - 1088 + 240, 24 * argc) a

/-- The bytes a call node's runs read: the tag, the callee pointer, the
argument array pointer and count (not the line field at `+4`), and the
array's pointers. -/
abbrev callView (a arr argc : Nat) : List Nat :=
  accAddrs a 4 ++ accAddrs (a + 8) 20 ++ accAddrs arr (8 * argc)

/-- What a call node gives the runs: its word reads at the node's register
value, its view, its placement, and the argument array's representation. -/
structure CallNode (m : Mem) (P : Nat → Prop) (aX aF arr : BitVec 64) (argc : Nat)
    (args : List Expr) : Prop where
  kind : ldv .lw m aX.toNat = 9#64
  kindu : ldv .lwu m aX.toNat = 9#64
  callee : ldv .ld m (aX + 8#64).toNat = aF
  arrw : ldv .ld m (aX + 16#64).toNat = arr
  cntw : ldv .lw m (aX + 24#64).toNat = BitVec.ofNat 64 argc
  lo : 0x80000000 ≤ aX.toNat
  hi : aX.toNat + 28 ≤ 0x100000000
  off : aX.toNat + 28 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat
  alo : 0x80000000 ≤ arr.toNat
  ahi : arr.toNat + 8 * argc ≤ 0x100000000
  aoff : arr.toNat + 8 * argc ≤ tohostAddr ∨ tohostAddr + 16 ≤ arr.toNat
  small : argc < 2 ^ 31
  len : args.length = argc
  repr : ExprArrayReprWithin m P arr.toNat argc args
  geo : ∀ k, P k → ReadOK k
  view : ∀ a ∈ callView aX.toNat arr.toNat argc, P a ∧ (m[a]?).isSome

/-- The argument loop's head: the registers at `0x800031d8`. -/
structure ArgsHead (R : Nat → BitVec 64) (s aX inp aE : BitVec 64) (argc : Nat) : Prop where
  sp : R 2 = s + 18446744073709550528#64
  s0 : R 8 = aX
  s2 : R 18 = inp
  a3 : R 13 = aE
  a5 : R 15 = BitVec.ofNat 64 argc
  a6 : R 16 = 0#64

/-- The loop's exit facts: the callee-saved registers and `sp` kept, `a5` the
count again, and the frame unchanged outside `ArgsScratch`. -/
structure ArgsExit (R R' : Nat → BitVec 64) (Mt Mt' : Mem) (s : BitVec 64) (argc : Nat) :
    Prop where
  keep : KeepRegs calleeSaved R R'
  a5 : R' 15 = BitVec.ofNat 64 argc
  frame : ∀ a, evalS s a → ¬ ArgsScratch s argc a → imgM Mt' a = imgM Mt a

section Motive

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- The argument values' words in the reached image: the `i`-th value's
three words at `base + 24 i` (persistent: `valImg`). -/
def valsImg (N : Vsa.RuntimeRepr.NativeAddrs) (img : Nat → BitVec 8) (base : Nat) (vs : List Value) :
    IProp GF :=
  sepL vs.zipIdx (fun p => valImg N img (base + 24 * p.2) p.1)

instance (N : Vsa.RuntimeRepr.NativeAddrs) (img : Nat → BitVec 8) (base : Nat) (vs : List Value) :
    Persistent (valsImg (GF := GF) N img base vs) := by
  unfold valsImg; infer_instance

/-- **The argument loop, total mode** (lane E6 proves it; the motive of
`EvalArgsCost`): from the head `0x800031d8` over `eval_expr`'s frame `evalS s`
(tracking memory `Mt`), with the stack below the lowered `sp` covering every
argument's need, the loop evaluates `args` left to right into `sp+240+24i`,
spending the derivation's cost, and hands the continuation the reached state
at `0x80003254`. `F` is the caller's frame. -/
def argsLoopT_body (live : Nat → Prop) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred)
    (inp : Nat) (st : St) (d env : Nat) (args : List Expr) (st' : St) (vs : List Value)
    (n : Nat) (_D : EvalArgsCost st d env args st' vs n) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (k : Nat) (aX aF arr aE s : BitVec 64) (argc : Nat)
    (R : Nat → BitVec 64) (Mt m : Mem) (P : Nat → Prop) (m' : Nat) (F : IProp GF),
    CallNode m P aX aF arr argc args → ArgsHead R s aX (BitVec.ofNat 64 inp) aE argc →
    EvalFrameG s → StackGeom (s + 18446744073709550528#64) m' →
    (∀ a ∈ args, evalNeed a d ≤ m' ∧ a.bodiesBound perCallBudget = true) →
    (F ∗ ms 0x800031d8#64 R (evalS s) Mt ∗ codeRes ∗ roOn P m ∗ □ frameAt env aE.toNat ∗
      stackScratch (s + 18446744073709550528#64) m' ∗ world N L Room inp (.counted (k + n)) st d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem), ⌜ArgsExit R R' Mt Mt' s argc⌝ -∗ F -∗
        valsImg N (imgM Mt') (s.toNat - 1088 + 240) vs -∗
        ms 0x80003254#64 R' (evalS s) Mt' -∗ stackScratch (s + 18446744073709550528#64) m' -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)
      ⊢ (twpW (vsaModel live)).W Φ)

/-- **The argument loop, partial mode** (lane E6 proves it): as
`argsLoopT_body`, outcome-quantified, the children through the Löb hypothesis
`evalSpecsP`. The continuation is an ADDITIVE pair: the return with the
`EvalArgs` derivation, or an abort from a child, which hands back the child's
abort resource re-based to the loop's stack region and the whole frame. -/
def argsLoopP_body (live : Nat → Prop) (N : NativeAddrs) (L : DlLayout) (Room : RoomPred)
    (inp : Nat) (Core : IProp GF) (d env : Nat) (args : List Expr) : Prop :=
  ∀ (Φ : Nat × String → IProp GF) (st : St) (aX aF arr aE s : BitVec 64) (argc : Nat)
    (R : Nat → BitVec 64) (Mt m : Mem) (P : Nat → Prop) (m' : Nat) (F : IProp GF),
    CallNode m P aX aF arr argc args → ArgsHead R s aX (BitVec.ofNat 64 inp) aE argc →
    EvalFrameG s → StackGeom (s + 18446744073709550528#64) m' →
    (∀ a ∈ args, evalNeed a d ≤ m' ∧ a.bodiesBound perCallBudget = true) →
    (F ∗ ms 0x800031d8#64 R (evalS s) Mt ∗ codeRes ∗ roOn P m ∗ □ frameAt env aE.toNat ∗
      stackScratch (s + 18446744073709550528#64) m' ∗ world N L Room inp .uncounted st d ∗
      evalSpecsP (vsaModel live) N L Room inp Core ∗
      ((∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st' : St) (vs : List Value),
        ⌜EvalArgs st d env args st' vs⌝ -∗ ⌜ArgsExit R R' Mt Mt' s argc⌝ -∗ F -∗
        valsImg N (imgM Mt') (s.toNat - 1088 + 240) vs -∗
        ms 0x80003254#64 R' (evalS s) Mt' -∗ stackScratch (s + 18446744073709550528#64) m' -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ) ∧
       (iprop(abortAt Core (s + 18446744073709550528#64) m' ∗ ownSet (evalS s) byteAny) -∗
          F -∗ (wpW (vsaModel live)).W Φ))
      ⊢ (wpW (vsaModel live)).W Φ)

end Motive

end VsaIris.Interp
