import VsaIris.Interp.Arm3
import VsaIris.Interp.LeafArm
import VsaIris.Interp.SymInterp

/-!
The four literal arms (`int`, `str`, `bool`, `null`): per kind the reflected entry to the
value-constructor call (`LeafEntryRun`) and its epilogue, one Wp-generic tail per kind, and the
total and partial cases.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

/-- State of a literal arm at its value-constructor call. -/
structure LeafReady (rv R : Nat → BitVec 64) (Mt : Mem) (s ret sret : BitVec 64)
    (A : (Nat → BitVec 64) → Prop) : Prop where
  r2 : R 2 = evalSP s
  a0 : R 10 = sret
  a1 : A R
  s3 : R 19 = rv 19
  hi : ∀ x ∈ hiSaved, R x = rv x
  saved : EvalSaved3 Mt s ret (rv 8) (rv 9) (rv 18)

/-- The reflected entry of a literal arm of kind `tag` (payload width `w`) to its call at `pc`;
`A` is the payload register fact. -/
def LeafEntryRun (tag w : Nat) (pc : BitVec 64)
    (A : Mem → BitVec 64 → (Nat → BitVec 64) → Prop) : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {P : Nat → Prop} {aX s ret sret inp aE : BitVec 64} {rv : Nat → BitVec 64}
    {Mt : Mem} {n : Nat},
    ArmGeo s ret sret n → EvalRegs rv sret inp aX aE s → LeafNode m P aX tag w →
    MRun live m (leafView aX.toNat w) (InExt (s.toNat - 1088, 1088)) evalEntryPC pc
      (upd rv 1 ret) Mt (fun R' Mt' => LeafReady rv R' Mt' s ret sret (A m aX))

set_option hygiene false in
macro "leaf_run " pc:num : tactic => `(tactic| (
  intro live hlive m P aX s ret sret inp aE rv Mt n g hr hn Q hk
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs := g.lo; have hs2 := g.hi; have hs3 := g.al
  have hx1 := hn.lo; have hx2 := hn.hi; have hx3 := hn.off
  have hK := hn.kind; have hKu := hn.kindu
  have h10 : upd rv 1 ret 10 = sret := by ix_reg; exact hr.a0
  have h11 : upd rv 1 ret 11 = inp := by ix_reg; exact hr.a1
  have h12 : upd rv 1 ret 12 = aX := by ix_reg; exact hr.a2
  have h13 : upd rv 1 ret 13 = aE := by ix_reg; exact hr.a3
  have h2 : upd rv 1 ret 2 = s := by ix_reg; exact hr.sp
  clear g hn
  unfold evalEntryPC
  sym_run hlive using [h10, h11, h12, h13, h2, hK, hKu, hsf] at $pc
  have hoff := evalSP_off (s := s) hsf (by omega)
  refine hk _ _ ?_
  refine ⟨by ix_reg, by ix_reg; exact hr.a0, by first | exact trivial | ix_reg, by ix_reg,
    fun x hx => ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · simp only [hiSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
  all_goals (ix_fwd using [hoff]; try ix_reg)))

theorem leafRun_int : LeafEntryRun 0 8 0x8000340c#64
    (fun m aX R => R 11 = ldv .ld m (aX + 8#64).toNat) := by leaf_run 0x8000340c
theorem leafRun_str : LeafEntryRun 1 8 0x80003418#64
    (fun m aX R => R 11 = ldv .ld m (aX + 8#64).toNat) := by leaf_run 0x80003418
theorem leafRun_bool : LeafEntryRun 2 4 0x80003424#64
    (fun m aX R => R 11 = ldv .lw m (aX + 8#64).toNat) := by leaf_run 0x80003424
theorem leafRun_null : LeafEntryRun 3 0 0x8000342c#64 (fun _ _ _ => True) := by leaf_run 0x8000342c

theorem epi3_80003410 : EpiRun3 0x80003410#64 := by epi3_run
theorem epi3_8000341c : EpiRun3 0x8000341c#64 := by epi3_run
theorem epi3_80003428 : EpiRun3 0x80003428#64 := by epi3_run
theorem epi3_80003430 : EpiRun3 0x80003430#64 := by epi3_run

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- After a literal's value-constructor call: epilogue and the caller's exit. -/
theorem leafFinish (Wp : MachWP (GF := GF) (vsaModel live)) {entry : BitVec 64} (J : JalAt entry)
    (hlive : ∀ p ∈ interpText, live p.1) (hepi : EpiRun3 (BitVec.ofNat 64 (J.i + 4)))
    {Φ : Nat × String → IProp GF} {N : NativeAddrs} {P : Nat → Prop} {m : Mem} {env : Nat}
    {aE s ret sret : BitVec 64} {n : Nat} {rv R R' : Nat → BitVec 64} {Mt : Mem} {Wd K : IProp GF}
    {DA : List Nat} {v : Value} {A : (Nat → BitVec 64) → Prop} {clob : List Nat}
    (hv : ∀ a ∈ DA, P a ∧ (m[a]?).isSome = true)
    (g : ArmGeo s ret sret n) (p : LeafReady rv R Mt s ret sret A) (hsp : rv 2 = s)
    (hk : ∀ x ∈ fRegs, x ∉ clob → R' x = R x) (hcl : ∀ x ∈ keep3, x ∉ clob)
    (hexit : ExitK Wp Φ N s ret sret rv n v Wd K) :
    ArmAt Wp Φ (evalArmF P m env aE (evalSP s) (n - 1088) (valAt N sret.toNat v) Wd K)
      (BitVec.ofNat 64 (J.i + 4)) (upd R' 1 (BitVec.ofNat 64 (J.i + 4)))
      (InExt (s.toNat - 1088, 1088)) Mt := by
  have kk : ∀ x ∈ keep3, upd R' 1 (BitVec.ofNat 64 (J.i + 4)) x = R x := fun x hx => by
    rw [upd_other _ _ (keep3_ne1 x hx)]; exact hk x (keep3_fRegs x hx) (hcl x hx)
  refine ArmAt.run Wp hv (hepi hlive g ((kk 2 (by decide)).trans p.r2) p.saved) fun R3 _ p3 => ?_
  exact ArmAt.finish Wp hexit g.sg.le g.need p3.ra
    (p3.keep ((kk 19 (by decide)).trans p.s3)
      (fun x hx => (kk x (hi_keep3 x hx)).trans (p.hi x hx)) hsp)

theorem leafIntTail (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} (hvi : ⊢ ∀ p n, valueIntSpec (vsaModel live) N Wp p n)
    {Φ : Nat × String → IProp GF} {P : Nat → Prop} {m : Mem} {env : Nat}
    {aE aX s ret sret inp : BitVec 64} {rv : Nat → BitVec 64} {Mt : Mem} {Wd K : IProp GF}
    {d : Nat} {k : Int}
    (ent : EvalEntry s ret sret aE aX inp rv (evalNeed (.int k) d) (.int k) m P)
    (hexit : ExitK Wp Φ N s ret sret rv (evalNeed (.int k) d) (.int k) Wd K) :
    ArmAt Wp Φ (entryF P m env aE s (evalNeed (.int k) d) sret Wd K) evalEntryPC (upd rv 1 ret)
      (InExt (s.toNat - 1088, 1088)) Mt := by
  obtain ⟨hn, hfv⟩ := leafNode_int ent.repr ent.ok
  have g := ent.geo
  refine ArmAt.run Wp hn.view (leafRun_int hlive g ent.regs hn) fun R1 Mt1 p1 => ?_
  refine ArmAt.callInt Wp (jal_site% 0x8000340c) hlive hvi p1.a0 (p1.a1.symm ▸ hfv) g.slg
    fun R2 hk2 => ?_
  exact leafFinish Wp _ hlive epi3_80003410 hn.view g p1 ent.regs.sp hk2 (by decide) hexit

theorem leafBoolTail (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} (hvb : ⊢ ∀ p b, valueBoolSpec (vsaModel live) N Wp p b)
    {Φ : Nat × String → IProp GF} {P : Nat → Prop} {m : Mem} {env : Nat}
    {aE aX s ret sret inp : BitVec 64} {rv : Nat → BitVec 64} {Mt : Mem} {Wd K : IProp GF}
    {d : Nat} {b : Bool}
    (ent : EvalEntry s ret sret aE aX inp rv (evalNeed (.bool b) d) (.bool b) m P)
    (hexit : ExitK Wp Φ N s ret sret rv (evalNeed (.bool b) d) (.bool b) Wd K) :
    ArmAt Wp Φ (entryF P m env aE s (evalNeed (.bool b) d) sret Wd K) evalEntryPC (upd rv 1 ret)
      (InExt (s.toNat - 1088, 1088)) Mt := by
  obtain ⟨hn, hfv⟩ := leafNode_bool ent.repr ent.ok
  have g := ent.geo
  refine ArmAt.run Wp hn.view (leafRun_bool hlive g ent.regs hn) fun R1 Mt1 p1 => ?_
  refine ArmAt.callBool Wp (jal_site% 0x80003424) hlive hvb p1.a0 p1.a1 g.slg fun R2 hk2 => ?_
  rw [hfv]
  exact leafFinish Wp _ hlive epi3_80003428 hn.view g p1 ent.regs.sp hk2 (by decide) hexit

theorem leafNullTail (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} (hvn : ⊢ ∀ p, valueNullSpec (vsaModel live) N Wp p)
    {Φ : Nat × String → IProp GF} {P : Nat → Prop} {m : Mem} {env : Nat}
    {aE aX s ret sret inp : BitVec 64} {rv : Nat → BitVec 64} {Mt : Mem} {Wd K : IProp GF}
    {d : Nat}
    (ent : EvalEntry s ret sret aE aX inp rv (evalNeed .null d) .null m P)
    (hexit : ExitK Wp Φ N s ret sret rv (evalNeed .null d) .null Wd K) :
    ArmAt Wp Φ (entryF P m env aE s (evalNeed .null d) sret Wd K) evalEntryPC (upd rv 1 ret)
      (InExt (s.toNat - 1088, 1088)) Mt := by
  have hn := leafNode_null ent.repr ent.ok
  have g := ent.geo
  refine ArmAt.run Wp hn.view (leafRun_null hlive g ent.regs hn) fun R1 Mt1 p1 => ?_
  refine ArmAt.callHelper Wp (jal_site% 0x8000342c : JalAt 0x800027ec#64) hlive
    (clob := []) (Out' := fun _ => valAt N sret.toNat .null)
    (Pre := iprop(slot24 sret.toNat ∗ ⌜SlotGeom sret⌝)) (Post := fun _ => valAt N sret.toNat .null)
    (by iintro; ihave H := hvn $$ %sret; unfold valueNullSpec; iexact H)
    (pins := fun rv => rv 10 = sret) p1.a0
    (by iintro ⟨Ho, Hw, HK⟩; iframe Ho Hw HK; ipureintro; exact g.slg) (fun _ => .rfl)
    fun R2 hk2 => ?_
  exact leafFinish Wp _ hlive epi3_80003430 hn.view g p1 ent.regs.sp hk2 (by decide) hexit

theorem leafStrTail (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {N : NativeAddrs} (hvs : ⊢ ∀ p q x, valueStrSpec (vsaModel live) N Wp p q x)
    {Φ : Nat × String → IProp GF} {P : Nat → Prop} {m : Mem} {env : Nat}
    {aE aX s ret sret inp : BitVec 64} {rv : Nat → BitVec 64} {Mt : Mem} {Wd K : IProp GF}
    {d : Nat} {x : String}
    (ent : EvalEntry s ret sret aE aX inp rv (evalNeed (.str x) d) (.str x) m P)
    (hexit : ExitK Wp Φ N s ret sret rv (evalNeed (.str x) d) (.str x) Wd K) :
    ArmAt Wp Φ (entryF P m env aE s (evalNeed (.str x) d) sret Wd K) evalEntryPC (upd rv 1 ret)
      (InExt (s.toNat - 1088, 1088)) Mt := by
  obtain ⟨q, hn, hfs⟩ := leafNode_str ent.repr ent.ok
  have g := ent.geo
  have hqt : (BitVec.ofNat 64 q).toNat = q := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfs.lt]
  refine ArmAt.run Wp hn.view (leafRun_str hlive g ent.regs hn) fun R1 Mt1 p1 => ?_
  unfold ArmAt evalArmF
  iintro ⟨⟨#Hcode, #Hro, #Hfb, Hst, Hslot, Hw, HK⟩, Hms⟩
  ihave #Hs : strAt q x $$ [Hro]
  · iapply strAt_of_cstringWithin hfs.str (sharedWin_of_readOK ent.ok) $$ Hro
  ihave Hvs := hvs $$ %sret %(BitVec.ofNat 64 q) %x
  unfold valueStrSpec
  iapply ms_callHelper Wp ((jal_site% 0x80003418 : JalAt valueStrPC).exec live hlive)
    (jal_site% 0x80003418 : JalAt valueStrPC).mem (jal_site% 0x80003418 : JalAt valueStrPC).al
  iframe Hvs Hcode Hms
  isplitl []
  · ipureintro; exact ⟨p1.a0, p1.a1.trans hfs.ptr⟩
  isplitl [Hslot]
  · iframe Hslot; isplitl []
    · ipureintro; exact ⟨g.slg, by rw [hqt]; exact hfs.ne⟩
    · rw [hqt]; iexact Hs
  iintro %R2 %hk2 Hval Hms
  iapply leafFinish Wp (jal_site% 0x80003418 : JalAt valueStrPC) hlive epi3_8000341c hn.view g p1
    ent.regs.sp hk2 (by decide) hexit
  iframe Hms; unfold evalArmF; iframe Hcode Hro Hfb Hst Hval Hw HK

theorem leafIntT (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {st : St} {d env : Nat} {n : Int}
    (D : EvalECost st d env (.int n) st (.int n) 0)
    (hvi : ⊢ ∀ p n, valueIntSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p n) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.int n) st (.int n) 0 D :=
  evalEntryT hlive D fun _ _ _ _ _ _ _ _ _ _ _ ent => leafIntTail (twpW _) hlive hvi ent evalKT_exit

theorem leafStrT (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {st : St} {d env : Nat} {x : String}
    (D : EvalECost st d env (.str x) st (.str x) 0)
    (hvs : ⊢ ∀ p q x, valueStrSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p q x) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.str x) st (.str x) 0 D :=
  evalEntryT hlive D fun _ _ _ _ _ _ _ _ _ _ _ ent => leafStrTail (twpW _) hlive hvs ent evalKT_exit

theorem leafBoolT (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {st : St} {d env : Nat} {b : Bool}
    (D : EvalECost st d env (.bool b) st (.bool b) 0)
    (hvb : ⊢ ∀ p b, valueBoolSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p b) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env (.bool b) st (.bool b) 0 D :=
  evalEntryT hlive D fun _ _ _ _ _ _ _ _ _ _ _ ent => leafBoolTail (twpW _) hlive hvb ent evalKT_exit

theorem leafNullT (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {st : St} {d env : Nat}
    (D : EvalECost st d env .null st .null 0)
    (hvn : ⊢ ∀ p, valueNullSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p) :
    ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env .null st .null 0 D :=
  evalEntryT hlive D fun _ _ _ _ _ _ _ _ _ _ _ ent => leafNullTail (twpW _) hlive hvn ent evalKT_exit

theorem leafIntP (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {Core : IProp GF} {st : St} {d env : Nat} {n : Int}
    (hvi : ⊢ ∀ p n, valueIntSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p n) :
    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ∗ errCtx inp ⊢
      evalSpecP_body (vsaModel live) N L Room inp Core st d env (.int n) :=
  evalEntryP hlive fun _ _ _ _ _ _ _ _ _ _ ent =>
    leafIntTail (wpW _) hlive hvi ent (evalKP_exit _ (EvalE.int st d env n))

theorem leafStrP (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {Core : IProp GF} {st : St} {d env : Nat} {x : String}
    (hvs : ⊢ ∀ p q x, valueStrSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p q x) :
    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ∗ errCtx inp ⊢
      evalSpecP_body (vsaModel live) N L Room inp Core st d env (.str x) :=
  evalEntryP hlive fun _ _ _ _ _ _ _ _ _ _ ent =>
    leafStrTail (wpW _) hlive hvs ent (evalKP_exit _ (EvalE.str st d env x))

theorem leafBoolP (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {Core : IProp GF} {st : St} {d env : Nat} {b : Bool}
    (hvb : ⊢ ∀ p b, valueBoolSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p b) :
    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ∗ errCtx inp ⊢
      evalSpecP_body (vsaModel live) N L Room inp Core st d env (.bool b) :=
  evalEntryP hlive fun _ _ _ _ _ _ _ _ _ _ ent =>
    leafBoolTail (wpW _) hlive hvb ent (evalKP_exit _ (EvalE.bool st d env b))

theorem leafNullP (hlive : ∀ p ∈ interpText, live p.1) {N : NativeAddrs} {L : DlLayout}
    {Room : RoomPred} {inp : Nat} {Core : IProp GF} {st : St} {d env : Nat}
    (hvn : ⊢ ∀ p, valueNullSpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p) :
    evalSpecsP (GF := GF) (vsaModel live) N L Room inp Core ∗ errCtx inp ⊢
      evalSpecP_body (vsaModel live) N L Room inp Core st d env .null :=
  evalEntryP hlive fun _ _ _ _ _ _ _ _ _ _ ent =>
    leafNullTail (wpW _) hlive hvn ent (evalKP_exit _ (EvalE.null st d env))

end

end VsaIris.Interp
