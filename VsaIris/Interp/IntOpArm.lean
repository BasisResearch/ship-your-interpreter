import VsaIris.Interp.IntRunAdd
import VsaIris.Interp.IntRunMul
import VsaIris.Interp.IntRunDiv
import VsaIris.Interp.IntErrSubMul
import VsaIris.Interp.IntErrDivMod
import VsaIris.Interp.BinPreludeP

/-!
The integer operators' tails, proved once for any `MachWP`, and their total and partial cases.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

def IntOpDesc.add : IntOpDesc :=
  ⟨.add, fun a b => wrap64 (a + b), fun _ _ => True, jal_site% 0x800038d4, IntOp.addRun, epi_800038d8⟩
def IntOpDesc.sub : IntOpDesc :=
  ⟨.sub, fun a b => wrap64 (a - b), fun _ _ => True, jal_site% 0x8000391c, IntOp.subRun, epi_80003920⟩
def IntOpDesc.mul : IntOpDesc :=
  ⟨.mul, fun a b => wrap64 (a * b), fun _ _ => True, jal_site% 0x8000387c, IntOp.mulRun, epi_80003880⟩
def IntOpDesc.div : IntOpDesc :=
  ⟨.div, fun a b => wrap64 (a.tdiv b), fun _ b => b ≠ 0, jal_site% 0x80003828, IntOp.divRun,
    epi_8000382c⟩
def IntOpDesc.mod : IntOpDesc :=
  ⟨.mod, fun a b => wrap64 (a.tmod b), fun _ b => b ≠ 0, jal_site% 0x800037d0, IntOp.modRun,
    epi_800037d4⟩

/-- An integer operator's error block: `value_kind_name` and `rt_err` sites, operator name,
the two type-error paths and the staging segment. -/
structure IntErrDesc (op : BinOp) where
  kn : JalAt valueKindNamePC
  rt : JalAt RtErr.rtErrEntry
  opn : BitVec 64
  name : OpName opn
  errL : BinErrRun op (BitVec.ofNat 64 kn.i) (opnConst opn) opn true errIntL
  errR : BinErrRun op (BitVec.ofNat 64 kn.i) (opnConst opn) opn false errIntR
  rtRun : RtRun (BitVec.ofNat 64 (kn.i + 4)) (BitVec.ofNat 64 rt.i) (opnConst opn)

theorem opnConst_agree {c s : BitVec 64} {Mt M' : Mem} {opn : BitVec 64}
    (_ : ∀ k, InExt (s.toNat - 1088, 1088) k → imgM M' k = imgM Mt k) (h : opnConst c s Mt opn) :
    opnConst c s M' opn := h

def IntErrDesc.sub : IntErrDesc .sub :=
  ⟨jal_site% 0x80003b7c, jal_site% 0x80003b9c, 0x800196e8#64,
    fun hro => rodata_cstrV hro 0x800196e8#64 1 (by decide) (by decide),
    IntOp.subErrL, IntOp.subErrR, IntOp.subRt⟩
def IntErrDesc.mul : IntErrDesc .mul :=
  ⟨jal_site% 0x80003c5c, jal_site% 0x80003c7c, 0x80019418#64,
    fun hro => rodata_cstrV hro 0x80019418#64 1 (by decide) (by decide),
    IntOp.mulErrL, IntOp.mulErrR, IntOp.mulRt⟩
def IntErrDesc.div : IntErrDesc .div :=
  ⟨jal_site% 0x80003f38, jal_site% 0x80003f58, 0x80019420#64,
    fun hro => rodata_cstrV hro 0x80019420#64 1 (by decide) (by decide),
    IntOp.divErrL, IntOp.divErrR, IntOp.divRt⟩
def IntErrDesc.mod : IntErrDesc .mod :=
  ⟨jal_site% 0x80003bf0, jal_site% 0x80003c10, 0x80019440#64,
    fun hro => rodata_cstrV hro 0x80019440#64 2 (by decide) (by decide),
    IntOp.modErrL, IntOp.modErrR, IntOp.modRt⟩

theorem IntOpDesc.sem_triv {D : IntOpDesc} (h : ∀ st a b, binOpSem st D.op (.int a) (.int b) =
    some (.int (D.sem a b))) : ∀ st a b, D.pre a b →
    binOpSem st D.op (.int a) (.int b) = some (.int (D.sem a b)) := fun st a b _ => h st a b

theorem IntOpDesc.sem_guard {D : IntOpDesc} (h : ∀ st a b, b ≠ 0 → binOpSem st D.op (.int a) (.int b) =
    some (.int (D.sem a b))) (hp : ∀ a b, D.pre a b ↔ b ≠ 0) : ∀ st a b, D.pre a b →
    binOpSem st D.op (.int a) (.int b) = some (.int (D.sem a b)) :=
  fun st a b h' => h st a b ((hp a b).1 h')

/-- No fixed-message error for a total operator. -/
theorem IntOpDesc.noZ {D : IntOpDesc} (h : ∀ a b, D.pre a b) (a b : Int) (hp : ¬ D.pre a b) :
    b = 0 ∧ ∃ fmt, ∃ RT : JalAt RtErr.rtErrEntry, ZeroRun D.op (BitVec.ofNat 64 RT.i) fmt ∧
      FmtArgsOK (fun a => rodataDom a ∨ False) rodataByte fmt [0#64, 0#64] :=
  absurd (h a b) hp

theorem IntOpDesc.div_Z (a b : Int) (hp : ¬ IntOpDesc.div.pre a b) :
    b = 0 ∧ ∃ fmt, ∃ RT : JalAt RtErr.rtErrEntry, ZeroRun IntOpDesc.div.op (BitVec.ofNat 64 RT.i) fmt ∧
      FmtArgsOK (fun a => rodataDom a ∨ False) rodataByte fmt [0#64, 0#64] :=
  ⟨Classical.not_not.1 hp, 0x80019428#64, jal_site% 0x80003d14, IntOp.divZero,
    readable_rodata_fmt (fun hro => plain_fmt hro 0x80019428#64 16 (by decide) (by decide) (by decide) _)⟩

theorem IntOpDesc.mod_Z (a b : Int) (hp : ¬ IntOpDesc.mod.pre a b) :
    b = 0 ∧ ∃ fmt, ∃ RT : JalAt RtErr.rtErrEntry, ZeroRun IntOpDesc.mod.op (BitVec.ofNat 64 RT.i) fmt ∧
      FmtArgsOK (fun a => rodataDom a ∨ False) rodataByte fmt [0#64, 0#64] :=
  ⟨Classical.not_not.1 hp, 0x80019448#64, jal_site% 0x80003bc8, IntOp.modZero,
    readable_rodata_fmt (fun hro => plain_fmt hro 0x80019448#64 14 (by decide) (by decide) (by decide) _)⟩

theorem IntOpDesc.div_sem : ∀ st a b, IntOpDesc.div.pre a b →
    binOpSem st IntOpDesc.div.op (.int a) (.int b) = some (.int (IntOpDesc.div.sem a b)) :=
  fun _ _ b h => by simp only [IntOpDesc.div] at h ⊢; simp [binOpSem, h]

theorem IntOpDesc.mod_sem : ∀ st a b, IntOpDesc.mod.pre a b →
    binOpSem st IntOpDesc.mod.op (.int a) (.int b) = some (.int (IntOpDesc.mod.sem a b)) :=
  fun _ _ b h => by simp only [IntOpDesc.mod] at h ⊢; simp [binOpSem, h]

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

theorem intOpTail (D : IntOpDesc) (Wp : MachWP (GF := GF) (vsaModel live))
    (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs}
    (hvi : ⊢ ∀ p n, valueIntSpec (vsaModel live) N Wp p n) {Φ : Nat × String → IProp GF}
    {P : Nat → Prop} {m : Mem} {env : Nat} {aE s ret sret inp aX : BitVec 64} {n : Nat}
    {rv R : Nat → BitVec 64} {Mt : Mem} {a b : Int} {w0 w1 w2 u0 u1 u2 : BitVec 64}
    {Wd K : IProp GF}
    (g : ArmGeo s ret sret n) (hn : BinOpNode m P aX (binOpTok D.op))
    (mid : BinMid s sret inp rv R Mt ret aX (.int a) (.int b) w0 w1 w2 u0 u1 u2)
    (hpre : D.pre a b) (hexit : ExitK Wp Φ N s ret sret rv n (.int (D.sem a b)) Wd K) :
    BinTail Wp Φ N (binArmF N P m env aE s n sret Wd K) R s Mt (.int a) (.int b)
      w0 w1 w2 u0 u1 u2 := by
  refine BinTail.ints fun h1 h2 => ?_
  refine ArmAt.run Wp hn.view (D.run hlive g hn mid h1 h2 hpre) fun R3 Mt3 p3 => ?_
  refine ArmAt.callInt Wp D.vi hlive hvi p3.a0 p3.a1 g.slg fun R4 hk4 => ?_
  have k4 := p3.keep.trans (HiKeep.helperRA hk4 (by decide) (by decide) (BitVec.ofNat 64 (D.vi.i + 4)))
  refine ArmAt.run Wp hn.view (D.epi hlive g (k4.sp.trans mid.r2) (p3.saved mid.saved))
    fun R5 _ p5 => ?_
  exact ArmAt.finish Wp hexit g.sg.le g.need p5.ra
    (p5.keep (fun x hx => (k4.hi x hx).trans (mid.hi x hx)) mid.sp)

theorem intOpT (D : IntOpDesc) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {st st1 st2 : St} {d env : Nat} {l r : Expr} {a b : Int} {nl nr : Nat}
    (Dl : EvalECost st d env l st1 (.int a) nl) (Dr : EvalECost st1 d env r st2 (.int b) nr)
    (D' : EvalECost st d env (.binary D.op l r) st2 (.int (D.sem a b)) (nl + nr))
    (hpre : D.pre a b)
    (hl : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env l st1 (.int a) nl Dl)
    (hr : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st1 d env r st2 (.int b) nr Dr)
    (hvi : ⊢ ∀ p n, valueIntSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p n) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.binary D.op l r) st2
        (.int (D.sem a b)) (nl + nr) D' :=
  binPreludeT hlive Dl Dr D' hl hr fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g hn mid hexit =>
    intOpTail D (twpW _) hlive hvi g hn mid hpre hexit

/-- The partial case of an integer operator: the integer path, the two type errors, and (for a
guarded operator) the fixed-message error `Z` when the guard fails. -/
theorem intOpP (D : IntOpDesc) (E : IntErrDesc D.op) {op : BinOp} (hop : D.op = op)
    (hsem : ∀ st a b, D.pre a b → binOpSem st D.op (.int a) (.int b) = some (.int (D.sem a b)))
    (Z : ∀ a b, ¬ D.pre a b → b = 0 ∧ ∃ fmt, ∃ RT : JalAt RtErr.rtErrEntry,
      ZeroRun D.op (BitVec.ofNat 64 RT.i) fmt ∧
      FmtArgsOK (fun a => rodataDom a ∨ False) rodataByte fmt [0#64, 0#64])
    (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat} {Core : IProp GF}
    {st : St} {d env : Nat} {l r : Expr}
    (hE : ErrEnv (GF := GF) N L Room inp live Core)
    (hvi : ⊢ ∀ p n, valueIntSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p n)
    (hvk : ⊢ ∀ p Mt v, valueKindNameSpec (GF := GF) (vsaModel live) (wpW (vsaModel live)) p Mt v) :
    evalSpecsP (vsaModel live) N L Room inp Core ∗ errCtx inp ⊢
      evalSpecP_body (vsaModel live) N L Room inp Core st d env (.binary op l r) :=
  hop ▸ binPreludeP hlive fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lv rv' _ _ _ g hn mid hexit hab => by
    rcases intRows lv rv' with ⟨a, b, rfl, rfl⟩ | hL | ⟨a, rfl, hR⟩
    · by_cases hp : D.pre a b
      · exact intOpTail D (wpW _) hlive hvi g hn mid hp (hexit _ (hsem _ a b hp))
      · obtain ⟨rfl, fmt, RT, hz, hfmt⟩ := Z a b hp
        exact binZeroArm RT hz hfmt (wpW _) hlive hE g hn mid hab
    · exact binErrArm E.kn E.rt E.errL E.rtRun opnConst_agree E.name (wpW _) hlive hE hvk g hn mid
        hL hab
    · exact binErrArm E.kn E.rt E.errR E.rtRun opnConst_agree E.name (wpW _) hlive hE hvk g hn mid
        ⟨rfl, hR⟩ hab

end

end VsaIris.Interp
