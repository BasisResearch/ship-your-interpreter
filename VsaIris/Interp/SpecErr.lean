import VsaIris.Interp.SpecValue
import VsaIris.Interp.Arm

/-!
# What an `eval_expr` error arm needs (lane E2): the statements

INTERP_DESIGN.md §4.2, §10 "STATEMENT CHANGES (E2)". An error arm of
`eval_expr` (a type error, a zero divisor, …) calls `runtime_error(in, line,
fmt, a1, a2)` (H5's `RtErr.rtErr_spec`), which never returns: it aborts with
H5's `abortRes` over its own stack. The partial spec `evalSpecP_body Core …`
aborts with `abortAt Core s (evalNeed e d) ∗ slot24 sret`. Three things the
arm needs are not in `evalPre`:

* **`errCtx inp`** (persistent): the binary's `.text`/`.rodata` image
  (`binImg`; `runtime_error`'s `callFrame`, the format strings) and the
  `jmp_buf` read-only at an image whose `ra` word is 4-aligned (`rtErr_spec`'s
  `hjb`). `world` has the `jmp_buf` (`interpCtxE`: `∃ jb, jmpRO inp jb`) but
  not the alignment, and nothing has `binImg`. `interp_run`'s proof (package A)
  has both after its `setjmp` (the saved `ra` is `0x80004428`), so a case of
  the partial recursion takes `errCtx inp` beside the Löb hypothesis.
* **`ErrEnv`** (pure): H5's `NewlibHoles`, the code liveness `rtErr_spec` asks,
  the `struct Interp` geometry (`InpGeom`), and `CoreOK Core`: the landing
  core `Core` of the partial specs absorbs `runtime_error`'s abort core at any
  region inside the stack segment. `abortCore … 0x88000000 0x800000` (the whole
  stack) is such a core (`coreOK_top`).
* **`value_kind_name`** (`0x800029c8`), which the type-error messages call:
  `valueKindNameSpec`, the name's pointer from `CSWTCH.18` (`kindNamePtr`).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

abbrev valueKindNamePC : BitVec 64 := 0x800029c8#64

/-- `value_kind_name`'s names (`CSWTCH.18` at `0x80019f28`): `"null"`,
`"bool"`, `"int"`, `"string"`, `"function"`, `"native function"`. -/
def kindNamePtr : Value → BitVec 64
  | .null => 0x80019018#64
  | .bool _ => 0x800192e8#64
  | .int _ => 0x800192f0#64
  | .str _ => 0x80018ea0#64
  | .closure _ => 0x800192f8#64
  | .native _ => 0x80019308#64

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable (M : MachineModel) (N : NativeAddrs)

/-- `value_kind_name(v)` (`v` by reference: `a0` points at a copy): the
kind's name, a `.rodata` string. It reads the kind word only, so the slot is
lent at its current bytes (`imgM Mt`) and handed back unchanged. -/
def valueKindNameSpec (Wp : MachWP (GF := GF) M) (p : BitVec 64) (Mt : Mem) (v : Value) : IProp GF :=
  helperSpec M Wp valueKindNamePC [10, 14, 15] (fun rv => rv 10 = p)
    iprop(ownSet (InExt (p.toNat, 24)) (fun a => a ↦ₘ imgM Mt a) ∗
      ⌜SlotGeom p ∧ (imgW (imgM Mt) p.toNat).toNat % 2 ^ 32 = valTag v⌝)
    (fun rv' => iprop(ownSet (InExt (p.toNat, 24)) (fun a => a ↦ₘ imgM Mt a) ∗
      ⌜rv' 10 = kindNamePtr v⌝))

/-- The sign class of `strcmp`'s result (newlib's lane-compare tail returns a
multiple of the first difference, so only the sign is the contract: H3's
finding, `Vsa/Sim/StrcmpSpecW.lean`'s sign-class `Q`). The strings are ASCII
(`CStrImg`), so byte order is `String`'s order. -/
structure StrcmpSign (res : BitVec 64) (x y : String) : Prop where
  eq : res = 0#64 ↔ x = y
  lt : res.toInt < 0 ↔ x < y
  gt : 0 < res.toInt ↔ y < x

/-- `strcmp(p, q)` with its result's sign (the ordering comparisons need
more than `strcmpSpecV`'s equality). Callee spec: H3's `strcmp` proof supplies
it. -/
def strcmpOrdSpec (Wp : MachWP (GF := GF) M) : IProp GF :=
  iprop(□ ∀ (p q : BitVec 64) (x y : String),
    helperSpec M Wp strcmpPCV callerSaved (fun rv => rv 10 = p ∧ rv 11 = q)
      iprop(strAt p.toNat x ∗ strAt q.toNat y)
      (fun rv' => iprop(⌜StrcmpSign (rv' 10) x y⌝)))

instance (Wp : MachWP (GF := GF) M) : Persistent (strcmpOrdSpec M Wp) := by
  unfold strcmpOrdSpec; infer_instance

/-- One instance of `strcmpOrdSpec`. -/
theorem strcmpOrdSpec_at {Wp : MachWP (GF := GF) M} (p q : BitVec 64) (x y : String) :
    strcmpOrdSpec M Wp ⊢ helperSpec M Wp strcmpPCV callerSaved (fun rv => rv 10 = p ∧ rv 11 = q)
      iprop(strAt p.toNat x ∗ strAt q.toNat y) (fun rv' => iprop(⌜StrcmpSign (rv' 10) x y⌝)) := by
  unfold strcmpOrdSpec
  iintro #H
  iapply H

/-- The persistent resources of an error arm: the binary's image and the
`jmp_buf` read-only with its `ra` word 4-aligned. -/
def errCtx (inp : Nat) : IProp GF :=
  iprop(binImg ∗ ∃ jb, jmpRO inp jb ∗ ⌜(jbWord inp jb 0).toNat % 4 = 0⌝)

instance (inp : Nat) : Persistent (errCtx (GF := GF) inp) := by
  unfold errCtx; infer_instance

/-- The binary's image, out of the error context. -/
theorem errCtx_img (inp : Nat) : errCtx (GF := GF) inp ⊢ binImg := by
  unfold errCtx; iintro ⟨#H, -⟩; iexact H

/-- `interp_run`'s lowered `sp` (`spEntry - interpRunFrame`): every
`eval_expr`/`exec_stmt` site runs at or below it (`StackGeom.top`). -/
abbrev runSp : BitVec 64 :=
  BitVec.ofNat 64 (Vsa.Sim.LayoutInstance.spEntry - Vsa.Sim.LayoutInstance.interpRunFrame)

theorem runSp_toNat :
    runSp.toNat = Vsa.Sim.LayoutInstance.spEntry - Vsa.Sim.LayoutInstance.interpRunFrame := by
  decide

theorem runTop_eq : Vsa.Sim.LayoutInstance.spEntry - Vsa.Sim.LayoutInstance.interpRunFrame =
    0x87fffc50 := by decide

variable (L : DlLayout) (Room : RoomPred) (inp : Nat)

/-- The landing core `Core` absorbs `runtime_error`'s (and the out-of-memory
exit's) abort core at any region `[sc - nc, sc)` of the stack segment at or
below `interp_run`'s frame (`StackGeom.top`). -/
def CoreOK (Core : IProp GF) : Prop :=
  ∀ (sc : BitVec 64) (nc : Nat), nc ≤ sc.toNat → 0x87800000 ≤ sc.toNat - nc →
    sc.toNat ≤ Vsa.Sim.LayoutInstance.spEntry - Vsa.Sim.LayoutInstance.interpRunFrame →
    abortCore N L Room inp sc nc ⊢ Core

/-- The pure premises of an error arm. -/
structure ErrEnv (live : Nat → Prop) (Core : IProp GF) : Prop where
  newlib : NewlibHoles
  code : CodeLive live
  inpGeom : RtErr.InpGeom (BitVec.ofNat 64 inp)
  inpLt : inp < 2 ^ 64
  core : CoreOK N L Room inp Core

/-- The core over the stack below `interp_run`'s frame absorbs every region
inside it. -/
theorem coreOK_top : CoreOK (GF := GF) N L Room inp
    (abortCore N L Room inp runSp (runSp.toNat - 0x87800000)) := fun sc nc _ h2 h3 =>
  abortCore_mono N L Room inp (by decide) (by decide) (by rw [runSp_toNat, runTop_eq]; omega)
    (by rw [runSp_toNat]; exact h3) (by decide)

end Specs

end VsaIris.Interp
