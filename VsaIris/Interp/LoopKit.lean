import VsaIris.Interp.SpecLoop
import VsaIris.Interp.NewlibCall

/-!
# The loop kit (lane E6): calls and slots shared by the `while`/`for` loops

* `wp_callAbort_laterX`: `wp_callAbort_later` whose `jal` also strips the later
  of one more resource `X` (a loop's own Löb hypothesis: the condition's
  `jal eval_expr` at the head of each iteration pays for the back edge).
* `ms_callEvalPx`: a child call into `eval_expr` from `exec_stmt`'s frame,
  partial mode (`ms_callEvalP` is its twin in `eval_expr`'s frame). On abort
  the child's slot rejoins the frame bytes.
* `ms_truthyCall`: `value_truthy` on a frame slot holding a represented
  value's three words, for either WP (the condition copy at `sp+16`).
* `execSlot`: the geometry of a slot of `exec_stmt`'s frame.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open Vsa.MemRepr Vsa.Sim Vsa.While Vsa.RuntimeRepr

/-! ## Pure geometry -/

/-- A slot of `exec_stmt`'s frame at offset `o` below the lowered `sp`: its
address as a plain sum, and its slot geometry. -/
structure ExecSlot (s : BitVec 64) (o : Nat) : Prop where
  addr : (s + 18446744073709551440#64 + BitVec.ofNat 64 o).toNat = s.toNat - 176 + o
  geo : SlotGeom (s + 18446744073709551440#64 + BitVec.ofNat 64 o)

theorem execSlot {s : BitVec 64} (h : ExecFrameGeom s) {o : Nat} (ho : o + 24 ≤ 176)
    (ho8 : o % 8 = 0) : ExecSlot s o := by
  have h1 := h.sf; have h2 := h.lo; have h3 := h.hi; have h4 := h.al
  have e : (s + 18446744073709551440#64 + BitVec.ofNat 64 o).toNat = s.toNat - 176 + o := by
    rw [BitVec.toNat_add, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨e, ⟨?_, ?_, ?_⟩⟩
  · rw [e]; omega
  · rw [e]; unfold Vsa.Sim.tohostAddr; omega
  · rw [e]; omega

/-- A frame address as a plain sum (the runs' and calls' address side
conditions become linear arithmetic; `ix_fwd using [execSP_off hfg]`). -/
theorem execSP_off {s : BitVec 64} (h : ExecFrameGeom s) (c : Nat) (hc : c < 4096) :
    (s + 18446744073709551440#64 + BitVec.ofNat 64 c).toNat = s.toNat - 176 + c := by
  have h1 := h.sf; have h2 := h.lo; have h3 := h.hi
  rw [BitVec.toNat_add, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

/-- The lowered `sp` of `exec_stmt` is the slot at offset `0`. -/
theorem execSP_toNat {s : BitVec 64} (h : ExecFrameGeom s) :
    (s + 18446744073709551440#64).toNat = s.toNat - 176 := h.sf

/-- A slot inside the frame's scratch words is in the frame. -/
theorem execSlot_in {s : BitVec 64} {o : Nat} (hs : ExecSlot s o) (ho : o + 24 ≤ 176) :
    ∀ b, InExt ((s + 18446744073709551440#64 + BitVec.ofNat 64 o).toNat, 24) b → execS s b := by
  intro b hb; rw [hs.addr] at hb; simp only [InExt] at hb ⊢; omega

/-- A slot inside the scratch words `[sp+16, sp+128)`. -/
theorem execSlot_W {s : BitVec 64} {o : Nat} (hs : ExecSlot s o) (h16 : 16 ≤ o)
    (ho : o + 24 ≤ 128) :
    ∀ b, InExt ((s + 18446744073709551440#64 + BitVec.ofNat 64 o).toNat, 24) b → execW s b := by
  intro b hb; rw [hs.addr] at hb; simp only [InExt] at hb ⊢; omega

/-- Writing a scratch slot leaves the frame outside the scratch words. -/
theorem Untouched.slotWrite {s : BitVec 64} {o : Nat} (hs : ExecSlot s o) (h16 : 16 ≤ o)
    (ho : o + 24 ≤ 128) (Mt : Mem) (w0 w1 w2 : BitVec 64) :
    Untouched (execS s) (execW s) Mt
      (slotWrite Mt (s + 18446744073709551440#64 + BitVec.ofNat 64 o).toNat w0 w1 w2) :=
  fun a _ hw => imgM_slotWrite_out w0 w1 w2 fun hin => hw (execSlot_W hs h16 ho a hin)

/-- A store of `w ≤ 8` bytes at `sp + o` inside the scratch words leaves the rest. -/
theorem Untouched.store {s : BitVec 64} {o w : Nat} (hs : ExecFrameGeom s) (h16 : 16 ≤ o)
    (ho : o + w ≤ 128) (Mt : Mem) (v : BitVec 64) :
    Untouched (execS s) (execW s) Mt
      (writeLog Mt [((s + 18446744073709551440#64 + BitVec.ofNat 64 o).toNat, w, v)]) := by
  have e := (execSlot (o := 0) hs (by omega) rfl).addr
  have e' : (s + 18446744073709551440#64 + BitVec.ofNat 64 o).toNat = s.toNat - 176 + o := by
    have h1 := hs.sf; have h2 := hs.lo; have h3 := hs.hi
    rw [BitVec.toNat_add, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  intro a _ hw
  rw [e']
  refine imgM_store_miss _ _ ?_
  simp only [InExt] at hw
  omega

section Shared

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr
variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The code alone is a run's read-only list with an empty data view. -/
theorem roOwn_code (m : Mem) : codeRes (GF := GF) ⊢ roOwn roR (interpText ++ dataOf m []) := by
  unfold codeRes; simp only [dataOf, List.map_nil, List.append_nil]; exact .rfl

theorem statusRet_brk [InterpGS GF] (N : NativeAddrs) (a : Nat) :
    statusRet (GF := GF) N a .brk = slot24 a := rfl

theorem statusRet_cont [InterpGS GF] (N : NativeAddrs) (a : Nat) :
    statusRet (GF := GF) N a .cont = slot24 a := rfl

/-- The named destructurer of `astSG`. -/
theorem astSG_elim (a : Nat) (sm : Stmt) :
    astSG (GF := GF) a sm ⊢ ∃ (P : Nat → Prop) (m : Mem),
      ⌜StmtReprWithin m P a sm ∧ ∀ k, P k → ReadOK k⌝ ∗ roOn P m := .rfl

/-- A child statement's persistent AST, from the parent's view. -/
theorem astSG_of_view {m : Mem} {P : Nat → Prop} {a : Nat} {sm : Stmt}
    (h : StmtReprWithin m P a sm) (hg : ∀ k, P k → ReadOK k) :
    roOn (GF := GF) P m ⊢ astSG a sm := by
  unfold astSG
  iintro #H
  iexists P, m
  iframe H
  ipureintro; exact ⟨h, hg⟩

end Shared

theorem KeepRegs.calleeSaved_upd {R R' : Nat → BitVec 64} (h : KeepRegs calleeSaved R R')
    {x : Nat} (hx : x ∉ calleeSaved) (w : BitVec 64) : KeepRegs calleeSaved R (upd R' x w) :=
  fun y hy => by
    have hne : y ≠ x := fun e => hx (e ▸ hy)
    rw [upd_apply, ite_eq_right_iff.mpr (fun h => absurd h hne)]; exact h y hy

/-- An `exec_stmt` arm's head registers survive a run that keeps the
callee-saved ones. -/
theorem StmtHead.keep {R R' : Nat → BitVec 64} {s aS inp aRet aEnv : BitVec 64}
    (h : StmtHead R s aS inp aRet aEnv) (hk : KeepRegs calleeSaved R R') :
    StmtHead R' s aS inp aRet aEnv :=
  ⟨(hk 2 (by decide)).trans h.sp, (hk 8 (by decide)).trans h.s0,
    (hk 9 (by decide)).trans h.s1, (hk 18 (by decide)).trans h.s2,
    (hk 19 (by decide)).trans h.s3⟩

theorem KeepRegs.refl' (ks : List Nat) (R : Nat → BitVec 64) : KeepRegs ks R R := fun _ _ => rfl

/-- A register update off the kept list keeps it. -/
theorem KeepRegs.upd_right {ks : List Nat} {R R' : Nat → BitVec 64} (h : KeepRegs ks R R')
    {x : Nat} (hx : x ∉ ks) (w : BitVec 64) : KeepRegs ks R (upd R' x w) :=
  fun y hy => by
    have hne : y ≠ x := fun e => hx (e ▸ hy)
    rw [upd_apply, ite_eq_right_iff.mpr (fun h => absurd h hne)]; exact h y hy

/-- A helper that keeps every body register off its clobber list keeps the
callee-saved ones when none is clobbered. -/
theorem KeepRegs.of_helper {clob : List Nat} {R R' : Nat → BitVec 64}
    (h : ∀ x ∈ fRegs, x ∉ clob → R' x = R x) (hc : ∀ x ∈ calleeSaved, x ∈ fRegs ∧ x ∉ clob) :
    KeepRegs calleeSaved R R' := fun x hx => h x (hc x hx).1 (hc x hx).2

/-- A run's end registers (an `upd` chain off the kept list) keep them. -/
macro "keep_upd" : tactic => `(tactic| ((repeat (apply KeepRegs.upd_right _ (by decide))); exact KeepRegs.refl' _ _))

section Calls

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

omit I in
/-- **Call under a later, with one more later-guarded resource** (partial
mode): the `jal`'s step strips the later of the callee's spec AND of `X`,
which the return continuation receives. A loop's Löb hypothesis rides on the
condition's call this way. -/
theorem wp_callAbort_laterX {M : MachineModel} {Φ : Nat × String → IProp GF} {i : Nat}
    {code : List (BitVec 8)} {entry v : BitVec 64} {P Q : BitVec 64 → IProp GF} {A X : IProp GF}
    (hexec : JalExec M i code entry) :
    instrAt (GF := GF) i code ∗ ▷ fnSpecAbort (wpW M) entry P Q A ∗ ▷ X ∗
      PC ↦ᵣ BitVec.ofNat 64 i ∗ ra ↦ᵣ v ∗ P (BitVec.ofNat 64 (i + 4)) ∗
      ((PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ ra ↦ᵣ BitVec.ofNat 64 (i + 4) -∗
          Q (BitVec.ofNat 64 (i + 4)) -∗ X -∗ mWP M Φ) ∧ (A -∗ mWP M Φ))
    ⊢ mWP M Φ := by
  unfold fnSpecAbort
  refine .trans ?_ (wp_jalW (wpW M) (Φ := Φ) (v := v) hexec)
  iintro ⟨#Hi, Hspec, HX, Hpc, Hra, HP, Hk⟩
  iframe Hi Hpc Hra
  iintro Hpc Hra
  simp only [wpW_lat, wpW_W]
  inext
  iapply Hspec $$ %(BitVec.ofNat 64 (i + 4)) %Φ Hpc Hra HP
  isplit
  · iintro Hpc Hra HQ
    ihave Hk := and_elim_l $$ Hk
    iapply Hk $$ Hpc Hra HQ HX
  · iintro HA
    ihave Hk := and_elim_r $$ Hk
    iapply Hk $$ HA

/-- **A child call into `eval_expr` from `exec_stmt`'s frame, partial mode**,
through the Löb hypothesis; the `jal` also strips the later of `X`. The
return branch is `ms_callEvalT`'s with the child's derivation and `X`. On
abort, the child's slot rejoins the frame bytes `S` and the arm aborts with
the stack below its `sp` and its frame bytes. The continuation pair
`Kret ∧ Kab` is used by both branches and handed on. -/
theorem ms_callEvalPx {Φ : Nat × String → IProp GF} {i : Nat} {code : List (BitVec 8)}
    (hexec : JalExec (vsaModel live) i code evalEntryPC)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {Core : IProp GF} {st : St} {d env : Nat} {e : Expr}
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {slot aC aE s : BitVec 64} {m : Nat}
    {Kret X : IProp GF}
    (hsg : StackGeom s (evalNeed e d)) (hm : evalNeed e d ≤ m) (hms : m ≤ s.toNat)
    (hslg : SlotGeom slot) (hbb : e.bodiesBound perCallBudget = true) :
    ⌜EvalRegs R slot (BitVec.ofNat 64 inp) aC aE s ∧ ∀ b, InExt (slot.toNat, 24) b → S b⌝ ∗
      ▷ evalSpecP_body (vsaModel live) N L Room inp Core st d env e ∗ ▷ X ∗ codeRes ∗
      □ astEG aC.toNat e ∗ □ frameAt env aE.toNat ∗
      ms (BitVec.ofNat 64 i) R S Mt ∗ stackScratch s m ∗ world N L Room inp .uncounted st d ∗
      (Kret ∧ (iprop(abortAt Core s m ∗ ownSet S byteAny) -∗ (wpW (vsaModel live)).W Φ)) ∗
      (∀ (R' : Nat → BitVec 64) (w0 w1 w2 : BitVec 64) (st' : St) (v : Value),
        ⌜EvalE st d env e st' v⌝ -∗ ⌜KeepRegs calleeSaved R R'⌝ -∗ □ valOf N v w0 w1 w2 -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S
          (slotWrite Mt slot.toNat w0 w1 w2) -∗
        stackScratch s m -∗ world N L Room inp .uncounted st' d -∗ X -∗
        (Kret ∧ (iprop(abortAt Core s m ∗ ownSet S byteAny) -∗ (wpW (vsaModel live)).W Φ)) -∗
        (wpW (vsaModel live)).W Φ)
    ⊢ (wpW (vsaModel live)).W Φ := by
  unfold ms evalSpecP_body
  iintro ⟨%⟨hregs, hslot⟩, Hspec, HX, #Hcode, #Hast, #Hfr, ⟨Hpc, Hra, Hregs, HS⟩, Hst, Hw, HK, Hk⟩
  ihave ⟨HS, Hslot⟩ := ownSet_carve_slot hslot $$ HS
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow hms hm $$ Hst
  ihave #Hi := instrAt_of_codeRes hcode $$ Hcode
  ihave Hspec := Hspec $$ %slot %aE %aC %s %R
  simp only [wpW_W]
  iapply wp_callAbort_laterX (X := X) hexec
  iframe Hi Hspec HX Hpc Hra
  isplitl [Hregs Hst Hslot Hw]
  · unfold evalPre
    iframe Hregs Hst Hslot Hw Hcode Hast Hfr
    ipureintro
    exact ⟨hal, hregs, hsg, hslg, hbb⟩
  isplit
  · iintro Hpc Hra ⟨%st', %v, %hE, Hpost⟩ HX
    unfold evalPost
    icases Hpost with ⟨%R', Hregs, %hkeep, Hst, Hval, Hw⟩
    ihave Hst := stackScratch_widen hms hm $$ [Hslack Hst]
    · iframe Hslack Hst
    ihave ⟨%w0, %w1, %w2, #Hv, HS⟩ := ownSet_join_slot hslot $$ [HS Hval]
    · iframe HS Hval
    iapply Hk $$ %R' %w0 %w1 %w2 %st' %v %hE %hkeep Hv [Hpc Hra Hregs HS] Hst Hw HX HK
    rw [regFile_upd_ra]
    simp only [upd_same]
    iframe Hpc Hra Hregs HS
  · iintro ⟨HA, Hslot⟩
    unfold abortAt
    icases HA with ⟨HC, Hst⟩
    ihave Hst := stackScratch_widen hms hm $$ [Hslack Hst]
    · iframe Hslack Hst
    ihave HS := ownSet_unslot hslot $$ [HS Hslot]
    · iframe HS Hslot
    ihave HK := and_elim_r $$ HK
    iapply HK
    iframe HC Hst HS

/-- **`value_truthy` on a slot of the frame bytes**, for either WP: the slot
`p` (inside the owned bytes `S`) holds the three words of a represented
value `v` in the tracking memory's image. The helper leaves the truthiness
bit in `a0`, clobbers `a0`/`a4`/`a5`, and changes no owned byte outside the
slot. -/
theorem ms_truthyCall (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)}
    (hexec : JalExec (vsaModel live) i code valueTruthyPC)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {p : BitVec 64} {v : Value}
    (hS : ∀ k, InExt (p.toNat, 24) k → S k) (hp : R 10 = p) (hslg : SlotGeom p) :
    valueTruthySpec (vsaModel live) N Wp p v ∗ codeRes ∗ ms (BitVec.ofNat 64 i) R S Mt ∗
      □ valImg N (imgM Mt) p.toNat v ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜(∀ x ∈ fRegs, x ∉ [10, 14, 15] → R' x = R x) ∧
          R' 10 = (if v.truthy then 1#64 else 0#64) ∧
          ∀ k, S k → ¬ InExt (p.toNat, 24) k → imgM Mt' k = imgM Mt k⌝ -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt' -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hspec, #Hcode, Hms, #Hv, Hk⟩
  ihave ⟨Hms, Hval⟩ := ms_carveVal N (M := Mt) (a := p.toNat) (b := p.toNat) (img := imgM Mt) hS
    rfl rfl rfl $$ [Hms Hv]
  · iframe Hms Hv
  unfold valueTruthySpec
  iapply ms_callHelper Wp hexec hcode hal
  iframe Hspec Hcode Hms
  isplitl []
  · ipureintro; exact hp
  isplitl [Hval]
  · iframe Hval; ipureintro; exact hslg
  iintro %R' %hkeep ⟨Hval, %hr⟩ Hms
  ihave ⟨%M', Hms, %hag⟩ := ms_uncarveVal N hS $$ [Hms Hval]
  · iframe Hms Hval
  iapply Hk $$ %R' %M' %⟨hkeep, hr, hag⟩ Hms

/-- **A child call into `exec_stmt`, partial mode, whose `jal` also strips
the later of `X`** (`ms_callExecP` with `wp_callAbort_laterX`): the `for`
loop's body call pays its Löb hypothesis (an iteration may have no
condition). -/
theorem ms_callExecPx {Φ : Nat × String → IProp GF} {i : Nat} {code : List (BitVec 8)}
    (hexec : JalExec (vsaModel live) i code execEntryPC)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {Core : IProp GF} {st : St} {d env : Nat} {sm : Stmt}
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {aS aE aRet s : BitVec 64} {m : Nat}
    {Kret X : IProp GF}
    (hsg : StackGeom s (execNeed sm d)) (hm : execNeed sm d ≤ m) (hms : m ≤ s.toNat)
    (hslg : SlotGeom aRet) (hbb : sm.bodiesBound perCallBudget = true) :
    ⌜ExecRegs R (BitVec.ofNat 64 inp) aS aE aRet s⌝ ∗
      ▷ execSpecP_body (vsaModel live) N L Room inp Core st d env sm ∗ ▷ X ∗ codeRes ∗
      □ astSG aS.toNat sm ∗ □ frameAt env aE.toNat ∗
      ms (BitVec.ofNat 64 i) R S Mt ∗ stackScratch s m ∗ slot24 aRet.toNat ∗
      world N L Room inp .uncounted st d ∗
      (Kret ∧ (iprop(abortAt Core s m ∗ slot24 aRet.toNat ∗ ownSet S byteAny) -∗
        (wpW (vsaModel live)).W Φ)) ∗
      (∀ (R' : Nat → BitVec 64) (st' : St) (status : Status), ⌜ExecS st d env sm st' status⌝ -∗
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status⌝ -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗
        stackScratch s m -∗ statusRet N aRet.toNat status -∗
        world N L Room inp .uncounted st' d -∗ X -∗
        (Kret ∧ (iprop(abortAt Core s m ∗ slot24 aRet.toNat ∗ ownSet S byteAny) -∗
          (wpW (vsaModel live)).W Φ)) -∗
        (wpW (vsaModel live)).W Φ)
    ⊢ (wpW (vsaModel live)).W Φ := by
  unfold ms execSpecP_body
  iintro ⟨%hregs, Hspec, HX, #Hcode, #Hast, #Hfr, ⟨Hpc, Hra, Hregs, HS⟩, Hst, Hslot, Hw, HK, Hk⟩
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow hms hm $$ Hst
  ihave #Hi := instrAt_of_codeRes hcode $$ Hcode
  ihave Hspec := Hspec $$ %aS %aE %aRet %s %R
  simp only [wpW_W]
  iapply wp_callAbort_laterX (X := X) hexec
  iframe Hi Hspec HX Hpc Hra
  isplitl [Hregs Hst Hslot Hw]
  · unfold execPre
    iframe Hregs Hst Hslot Hw Hcode Hast Hfr
    ipureintro
    exact ⟨hal, hregs, hsg, hslg, hbb⟩
  isplit
  · iintro Hpc Hra ⟨%st', %status, %hE, Hpost⟩ HX
    unfold execPost
    icases Hpost with ⟨%R', Hregs, %hkeep, Hst, Hret, Hw⟩
    ihave Hst := stackScratch_widen hms hm $$ [Hslack Hst]
    · iframe Hslack Hst
    iapply Hk $$ %R' %st' %status %hE %hkeep [Hpc Hra Hregs HS] Hst Hret Hw HX HK
    rw [regFile_upd_ra]
    simp only [upd_same]
    iframe Hpc Hra Hregs HS
  · iintro ⟨HA, Hslot⟩
    unfold abortAt
    icases HA with ⟨HC, Hst⟩
    ihave Hst := stackScratch_widen hms hm $$ [Hslack Hst]
    · iframe Hslack Hst
    ihave HS := ownSet_forget _ _ $$ HS
    ihave HK := and_elim_r $$ HK
    iapply HK
    iframe HC Hst Hslot HS

/-- Any status's `ret` slot is a slot (the `for` init discards it). -/
theorem statusRet_slot (N : NativeAddrs) (a : Nat) :
    ∀ status, statusRet (GF := GF) N a status ⊢ slot24 a
  | .ret v => valAt_slot N a v
  | .normal | .brk | .cont => .rfl

end Calls

end VsaIris.Interp
