import VsaIris.Vsa.ErrnoOwn
import VsaIris.Interp.CallArm
import VsaIris.Interp.SpecValue

/-!
# The call arm's native path: the shared layer (lane E4)

A native call (`interp.c:173-174`) passes `args` by reference: the argument
array `sp+240..` of `eval_expr`'s frame, which the argument loop filled
(E6's `argVals`: each slot's words are its value's). The natives' specs
(H2's `nativePrintSpec`, `nativePrintlnSpec`, `nativeAssertSpec`) take the
array as owned values `valsAt N (sp+240) vs`.

* `valsAt_of_argVals`/`blockOwn_of_valsAt`: the array's bytes with the loop's
  facts are `valsAt`, and `valsAt` gives back the bytes.
* `ms_carveVals`/`ms_uncarveVals`: the array out of, and back into, a run's
  owned frame.
* `NativeEntries`: the concrete entries of the three natives
  (`InterpRunReadyFacts.native_addrs`).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open Vsa.MemRepr Vsa.Sim Vsa.While Vsa.RuntimeRepr

/-- The machine entries of the natives (`InterpRunReadyFacts.native_addrs`,
the fixed image's `native_print`/`native_println`/`native_assert`). -/
structure NativeEntries (N : NativeAddrs) : Prop where
  print : N.print = 0x80002ed4
  println : N.println = 0x80002f7c
  assert : N.assert = 0x80002df4

section Vals

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

omit I in
theorem ms_iff' {pc : BitVec 64} {R : Nat → BitVec 64} {S T : Nat → Prop} {M : Mem}
    (h : ∀ k, S k ↔ T k) : ms (GF := GF) pc R S M ⊢ ms pc R T M := by
  unfold ms
  iintro ⟨Hpc, Hra, Hregs, HS⟩
  iframe Hpc Hra Hregs
  iapply ownSet_iff _ h $$ HS

/-- The argument array's bytes at a tracking memory, with the loop's facts,
are the values. -/
theorem valsAt_of_argVals (N : NativeAddrs) (M : Mem) (base : Nat) :
    ∀ (vs : List Value) (i : Nat),
      ownSet (GF := GF) (InExt (base + 24 * i, 24 * vs.length)) (fun b => b ↦ₘ imgM M b) ∗
        argVals N (imgM M) base i vs ⊢
      sepL (vs.zipIdx i) (fun p => valAt N (base + 24 * p.2) p.1)
  | [], i => by
    iintro -
    simp only [List.zipIdx_nil, sepL_nil]
    iempintro
  | v :: vs, i => by
    simp only [List.zipIdx_cons, sepL_cons, argVals, List.length_cons]
    iintro ⟨HS, #Hv, #Hvs⟩
    ihave ⟨H1, H2⟩ := ownSet_split _ (InExt (base + 24 * i, 24)) _ $$ HS
    ihave H1 := ownSet_iff _ (T := InExt (base + 24 * i, 24))
      (fun a => by simp only [InExt]; omega) $$ H1
    ihave H2 := ownSet_iff _ (T := InExt (base + 24 * (i + 1), 24 * vs.length))
      (fun a => by simp only [InExt]; omega) $$ H2
    isplitl [H1]
    · iapply valAt_of_img N
      iframe Hv H1
    · iapply valsAt_of_argVals N M base vs (i + 1)
      iframe H2 Hvs

/-- The values' bytes, as one block. -/
theorem blockOwn_of_valsAt (N : NativeAddrs) (base : Nat) :
    ∀ (vs : List Value) (i : Nat),
      sepL (GF := GF) (vs.zipIdx i) (fun p => valAt N (base + 24 * p.2) p.1) ⊢
        blockOwn (base + 24 * i) (24 * vs.length)
  | [], i => by
    iintro -
    unfold blockOwn ownSet
    iexists []
    simp only [sepL_nil]
    ipureintro
    refine ⟨⟨List.nodup_nil, fun a => ?_⟩, trivial⟩
    simp [InExt]
  | v :: vs, i => by
    simp only [List.zipIdx_cons, sepL_cons, List.length_cons]
    iintro ⟨Hv, Hvs⟩
    ihave H1 := valAt_slot N _ v $$ Hv
    ihave H2 := blockOwn_of_valsAt N base vs (i + 1) $$ Hvs
    unfold slot24 at *
    iapply blockOwn_join (base + 24 * i) 24 (base + 24 * (i + 1)) (24 * vs.length)
      (24 * (vs.length + 1)) (by omega) (by omega)
    iframe H1 H2

/-- **The argument array out of a run's owned frame**, as the values. -/
theorem ms_carveVals (N : NativeAddrs) {pc : BitVec 64} {R : Nat → BitVec 64} {S : Nat → Prop}
    {M : Mem} {base : Nat} {vs : List Value}
    (hS : ∀ k, InExt (base, 24 * vs.length) k → S k) :
    ms (GF := GF) pc R S M ∗ argVals N (imgM M) base 0 vs ⊢
      ms pc R (fun k => S k ∧ ¬ InExt (base, 24 * vs.length) k) M ∗ valsAt N base vs := by
  have hsl : ∀ k, S k ↔ ((S k ∧ ¬ InExt (base, 24 * vs.length) k) ∨
      InExt (base, 24 * vs.length) k) := fun k => by
    constructor
    · intro h; by_cases h' : InExt (base, 24 * vs.length) k
      · exact .inr h'
      · exact .inl ⟨h, h'⟩
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact hS k h
  iintro ⟨Hms, #Hv⟩
  ihave Hms := ms_iff' hsl $$ Hms
  ihave ⟨Hms, Hslot⟩ := ms_split (fun k h1 h2 => h1.2 h2) $$ Hms
  iframe Hms
  unfold valsAt
  iapply valsAt_of_argVals N M base vs 0
  simp only [Nat.mul_zero, Nat.add_zero]
  iframe Hslot Hv

/-- **And back in**: the run's other bytes unchanged. -/
theorem ms_uncarveVals (N : NativeAddrs) {pc : BitVec 64} {R : Nat → BitVec 64} {S : Nat → Prop}
    {M : Mem} {base : Nat} {vs : List Value}
    (hS : ∀ k, InExt (base, 24 * vs.length) k → S k) :
    ms (GF := GF) pc R (fun k => S k ∧ ¬ InExt (base, 24 * vs.length) k) M ∗ valsAt N base vs ⊢
      ∃ M', ms pc R S M' ∗ ⌜∀ k, S k → ¬ InExt (base, 24 * vs.length) k → imgM M' k = imgM M k⌝ := by
  have hsl : ∀ k, ((S k ∧ ¬ InExt (base, 24 * vs.length) k) ∨ InExt (base, 24 * vs.length) k) ↔
      S k := fun k => by
    constructor
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact hS k h
    · intro h; by_cases h' : InExt (base, 24 * vs.length) k
      · exact .inr h'
      · exact .inl ⟨h, h'⟩
  iintro ⟨Hms, Hvals⟩
  unfold valsAt
  ihave Hb := blockOwn_of_valsAt N base vs 0 $$ Hvals
  simp only [Nat.mul_zero, Nat.add_zero]
  unfold blockOwn
  ihave ⟨%f, Hb⟩ := ownSet_fn _ $$ Hb
  ihave ⟨%Ms, Hb⟩ := ownSet_mem _ f $$ Hb
  ihave ⟨%M', Hms, %⟨h1, -, -⟩⟩ := ms_join $$ [Hms Hb]
  · iframe Hms Hb
  iexists M'
  isplitl
  · iapply ms_iff' hsl $$ Hms
  · ipureintro; exact fun k hk hn => h1 k ⟨hk, hn⟩

/-- **What `value_print` needs of a closure argument, from the store**: a
closure the store owns is displayable (`dispRes`: its object's and its
`EX_FN` node's read geometry and the name's window). Proved for every `N` as
`dispSupply` (`CallClosure.lean`) from the geometry `closOwn` carries. -/
def DispSupply (N : NativeAddrs) : Prop :=
  ∀ (s : Store) (B : List (Nat × Nat)) (ca p : Nat),
    storeRepr (GF := GF) N s B ∗ closAt ca p ⊢ storeRepr N s B ∗ dispRes s (.closure ca)

/-- The arguments' display resources, from the store and their words. -/
theorem dispResL_of_argVals (N : NativeAddrs) (hd : DispSupply (GF := GF) N) (s : Store)
    (B : List (Nat × Nat)) (img : Nat → BitVec 8) (base : Nat) :
    ∀ (vs : List Value) (i : Nat),
      storeRepr (GF := GF) N s B ∗ argVals N img base i vs ⊢ storeRepr N s B ∗ dispResL s vs
  | [], _ => by
    iintro ⟨Hs, -⟩
    iframe Hs
    unfold dispResL; simp only [sepL_nil]; iempintro
  | v :: vs, i => by
    unfold dispResL argVals
    simp only [sepL_cons]
    iintro ⟨Hs, #Hv, #Hvs⟩
    ihave ⟨Hs, #Hd⟩ := (show iprop(storeRepr N s B ∗ valImg N img (base + 24 * i) v) ⊢
        iprop(storeRepr N s B ∗ dispRes s v) from by
      cases v with
      | closure ca =>
        unfold valImg valOf
        iintro ⟨Hs, ⟨-, #Hc⟩⟩
        iapply (hd s B ca _) $$ [Hs Hc]
        iframe Hs Hc
      | _ =>
        iintro ⟨Hs, -⟩
        iframe Hs
        unfold dispRes; iempintro) $$ [Hs Hv]
    · iframe Hs Hv
    ihave ⟨Hs, #Hds⟩ := dispResL_of_argVals N hd s B img base vs (i + 1) $$ [Hs Hvs]
    · iframe Hs Hvs
    iframe Hs Hd
    unfold dispResL at *
    iexact Hds

end Vals

section Out

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable (M : MachineModel) (N : NativeAddrs)

/-- **A printing native** (`native_print`, `native_println`), H2's
`nativePrintSpec`/`nativePrintlnSpec` with the entry, the stack need and the
printed text as parameters: from `o`, the console is `o'`. -/
def natOutSpec (Wp : MachWP (GF := GF) M) (entry : BitVec 64) (need : Nat)
    (sret args s : BitVec 64) (vs : List Value) (st : Store) (o o' : String) : IProp GF :=
  helperSpec M Wp entry callerSaved
    (fun rv => rv 10 = sret ∧ rv 12 = BitVec.ofNat 64 vs.length ∧ rv 13 = args ∧ rv 2 = s)
    iprop(slot24 sret.toNat ∗ ⌜SlotGeom sret ∧ ArgsGeom args vs.length ∧ vs.length < 2 ^ 31⌝ ∗
      valsAt N args.toNat vs ∗ dispResL st vs ∗ Newlib.binImg ∗ Stdio.stdioW ∗ consoleOwn o ∗
      stackAt s need)
    (fun _ => iprop(valAt N sret.toNat .null ∗ valsAt N args.toNat vs ∗ Stdio.stdioW ∗
      consoleOwn o' ∗ stackAt s need))

theorem nativePrintSpec_eq (Wp : MachWP (GF := GF) M) (sret args s : BitVec 64) (vs : List Value)
    (st : Store) (o : String) :
    nativePrintSpec M N Wp sret args s vs st o =
      natOutSpec M N Wp nativePrintPC nativePrintNeed sret args s vs st o (o ++ printArgs st vs) := rfl

theorem nativePrintlnSpec_eq (Wp : MachWP (GF := GF) M) (sret args s : BitVec 64)
    (vs : List Value) (st : Store) (o : String) :
    nativePrintlnSpec M N Wp sret args s vs st o =
      natOutSpec M N Wp nativePrintlnPC nativePrintlnNeed sret args s vs st o
        (o ++ printArgs st vs ++ "\n") := rfl

end Out

section WorldOut

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- **The world, opened for a printing native**: the console, newlib's data
and the binary's image, the store, and the way back with a new console. -/
theorem world_out (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat) (ρ : Regime)
    (st : St) (d : Nat) (hE : ErrnoOwn.ErrnoLend (GF := GF) L Room) :
    world (GF := GF) N L Room inp ρ st d ⊢
      consoleOwn st.out ∗ Stdio.stdioW ∗ Newlib.binImg ∗ ∃ B, storeRepr N st.store B ∗
        (∀ o, consoleOwn o -∗ Stdio.stdioW -∗ storeRepr N st.store B -∗
          world N L Room inp ρ ⟨st.store, o⟩ d) := by
  unfold world worldE
  iintro ⟨%H, %B, Hh, Hs, Hc, Hio, Hi, %hB, #Hb⟩
  ihave ⟨He, Hh⟩ := hE ρ H $$ Hh
  unfold Stdio.stdioW
  iframe Hc Hio He Hb
  iexists B
  iframe Hs
  iintro %o Hc ⟨Hio, He⟩ Hs
  ihave Hh := Hh $$ He
  iexists H, B
  iframe Hh Hs Hc Hio Hi
  ipureintro; exact hB

end WorldOut

end VsaIris.Interp

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While

-- Run N1: copy the callee to `sp+120`, read the line (havoc), the kind test
-- `5` (native), marshal `native(sret, in, argc, args, line)`; stop at the `jalr a6`.
#ix_seg CallN_run1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s w0 w1 w2 : BitVec 64}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aX.toNat) (hx2 : aX.toNat + 28 ≤ 0x100000000)
    (hx3 : aX.toNat + 28 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aX.toNat)
    (h8 : R 8 = aX) (h2 : R 2 = s + 18446744073709550528#64)
    (hW0 : ldv .ld Mt (s + 18446744073709550528#64 + 96#64).toNat = w0)
    (hW1 : ldv .ld Mt (s + 18446744073709550528#64 + 104#64).toNat = w1)
    (hW2 : ldv .ld Mt (s + 18446744073709550528#64 + 112#64).toNat = w2)
    (hK : ldv .lw Mt (s + 18446744073709550528#64 + 96#64).toNat = 5#64) :
    IW live m (callView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x80003254#64 R Mt
  by ix_run hlive using [h8, h2, hW0, hW1, hW2, hK, hsf] at 0x800039f4


-- Run N2: after the native, restore `s7`, the shared epilogue, `ret`.
#ix_seg CallN_run2 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s ret v8 v9 v18 v23 : BitVec 64} {DA : List Nat}
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088)
    (hs : 0x87800000 + 1088 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hal : ret.toNat % 4 = 0)
    (h2 : R 2 = s + 18446744073709550528#64)
    (hRA : ldv .ld Mt (s + 18446744073709550528#64 + 1080#64).toNat = ret)
    (hS0 : ldv .ld Mt (s + 18446744073709550528#64 + 1072#64).toNat = v8)
    (hS1 : ldv .ld Mt (s + 18446744073709550528#64 + 1064#64).toNat = v9)
    (hS2 : ldv .ld Mt (s + 18446744073709550528#64 + 1056#64).toNat = v18)
    (hS7 : ldv .ld Mt (s + 18446744073709550528#64 + 1016#64).toNat = v23) :
    IW live m DA (InExt (s.toNat - 1088, 1088)) Q 0x800039f8#64 R Mt
  by ix_run hlive using [h2, hRA, hS0, hS1, hS2, hS7, hsf, hal]

end VsaIris.Interp
