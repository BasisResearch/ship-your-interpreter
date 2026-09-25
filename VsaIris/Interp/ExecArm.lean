import VsaIris.Interp.ExecDisp
import VsaIris.Interp.NewlibCall
import VsaIris.Interp.SymLater
import VsaIris.Interp.SpecValue

/-!
# The exec arm layer (lane E5)

What every `exec_stmt` arm shares, from the dispatch point
(`SpecExecDisp.lean`): the statement node's reads (`StmtNode`, `stmtView`), the
frame geometry, the epilogues.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

/-- The bytes of a statement node a run reads: the tag word and the fields
from `+8` to `+w` (never the line field at `+4`). -/
abbrev stmtView (a w : Nat) : List Nat := accAddrs a 4 ++ accAddrs (a + 8) (w - 8)


/-- What a statement node gives the runs: its tag reads at the node's
register value, its placement (`w` bytes from the node), its view. -/
structure StmtNode (m : Mem) (P : Nat → Prop) (aS : BitVec 64) (tag w : Nat) : Prop where
  kind : ldv .lw m aS.toNat = BitVec.ofNat 64 tag
  kindu : ldv .lwu m aS.toNat = BitVec.ofNat 64 tag
  lo : 0x80000000 ≤ aS.toNat
  hi : aS.toNat + w ≤ 0x100000000
  off : aS.toNat + w ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat
  view : ∀ a ∈ stmtView aS.toNat w, P a ∧ (m[a]?).isSome
  geo : ∀ k, P k → Interp.ReadOK k

/-- A node's facts from its tag read and the reads of its fields `[+8, +w)`
(`w = 4`: the tag alone). -/
theorem stmtNode_of {m : Mem} {P : Nat → Prop} {aS : BitVec 64} {tag w : Nat}
    (hg : ∀ k, P k → Interp.ReadOK k) (ht : read32 m aS.toNat = some tag) (hc : Covers P aS.toNat 4)
    (htag : tag < 2 ^ 31) (hw : w = 4 ∨ 9 ≤ w)
    (hmid : ∀ j, 8 ≤ j → j < w → P (aS.toNat + j) ∧ (m[aS.toNat + j]?).isSome) :
    StmtNode m P aS tag w := by
  have g0 := hg _ (hc 0 (by omega))
  have g3 := hg _ (hc 3 (by omega))
  have hlast : Interp.ReadOK (aS.toNat + (w - 1)) := by
    rcases hw with rfl | hw
    · exact g3
    · exact hg _ (hmid (w - 1) (by omega) (by omega)).1
  refine ⟨ldv_lw_read32 ht htag, ldv_lwu_read32 ht, by simpa using g0.lo, ?_, ?_, ?_, hg⟩
  · have := hlast.hi; omega
  · have h0 := g0.off; have h1 := hlast.off
    simp only [Nat.add_zero] at h0
    unfold Vsa.Sim.tohostAddr at *
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · left; omega
    · -- a byte of the node would sit on the HTIF words
      exfalso
      rcases hw with rfl | hw
      · omega
      have := (hg _ (hmid (2147593472 + 15 - aS.toNat) (by omega) (by omega)).1).off
      unfold Vsa.Sim.tohostAddr at this; omega
    · omega
    · right; omega
  · intro a ha
    simp only [List.mem_append, mem_accAddrs_iff] at ha
    rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨j, rfl⟩ : ∃ j, a = aS.toNat + j := ⟨a - aS.toNat, by omega⟩
      exact ⟨hc j (by omega), isSome_of_readLE ht (by omega)⟩
    · obtain ⟨j, rfl⟩ : ∃ j, a = aS.toNat + j := ⟨a - aS.toNat, by omega⟩
      exact hmid j (by omega) (by omega)

/-- A field word of a placed node. -/
theorem field64 {m : Mem} {aS : BitVec 64} {o p : Nat} (hr : read64 m (aS.toNat + o) = some p)
    (hhi : aS.toNat + o + 8 ≤ 0x100000000) :
    ldv .ld m (aS + BitVec.ofNat 64 o).toNat = BitVec.ofNat 64 p := by
  have e : (aS + BitVec.ofNat 64 o).toNat = aS.toNat + o := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [e]; exact ldv_ld_read64 hr

/-- The bytes of a field read, as the node view's middle. -/
theorem field_mid {m : Mem} {P : Nat → Prop} {a o n v : Nat} (hr : readLE m (a + o) n = some v)
    (hc : Covers P (a + o) n) {j : Nat} (h1 : o ≤ j) (h2 : j < o + n) :
    P (a + j) ∧ (m[a + j]?).isSome := by
  obtain ⟨i, rfl⟩ : ∃ i, j = o + i := ⟨j - o, by omega⟩
  rw [← Nat.add_assoc]
  exact ⟨hc i (by omega), isSome_of_readLE hr (by omega)⟩

section FrameRes

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **Leaving `exec_stmt`'s frame**: the frame bytes rejoin the stack below
the entry `sp`. -/
theorem execFrame_join {s : BitVec 64} {n : Nat} (hn : n ≤ s.toNat) (hf : 176 ≤ n) :
    stackScratch (GF := GF) (execSP s) (n - 176) ∗ ownSet (InExt (s.toNat - 176, 176)) byteAny ⊢
      stackScratch s n := by
  have e : (s - 176#64).toNat = s.toNat - 176 := toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have h := stackScratch_unframe (GF := GF) (s := s) (f := 176#64) (n := n) hn (by simp only [BitVec.toNat_ofNat]; omega)
  rw [e, show (176#64).toNat = 176 from rfl, execSP_eq] at h
  exact h

end FrameRes

section Finish

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

/-- **The end of an exec arm**, for either WP: after the epilogue's `ret`
(the machine state at the return address, `ra` holding it), the frame bytes
rejoin the stack and the dispatch-point continuation takes the rest. -/
theorem execDisp_finish (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {ρ : Regime} {st' : St} {d : Nat} {sm : Stmt} {status : Status} {aRet s ret : BitVec 64}
    {R R' : Nat → BitVec 64} {Mt : Mem} {v8 v9 v18 v19 pc : BitVec 64}
    (hsg : StackGeom s (execNeed sm d)) (hpc : pc = ret) (hra : R' 1 = ret)
    (hret : ExecRet R R' s v8 v9 v18 v19 status) :
    ms pc R' (InExt (s.toNat - 176, 176)) Mt ∗ stackScratch (execSP s) (execNeed sm d - 176) ∗
      statusRet N aRet.toNat status ∗ world N L Room inp ρ st' d ∗
      execDispK (vsaModel live) N L Room inp Wp Φ ρ st' d sm status aRet s R ret v8 v9 v18 v19
    ⊢ Wp.W Φ := by
  obtain ⟨_, hneed⟩ := execFrameGeom_of hsg
  iintro ⟨Hms, Hst, Hret, Hw, HK⟩
  ihave ⟨Hpc, Hra, Hregs, HS⟩ := ms_exit $$ Hms
  ihave Hst := execFrame_join hsg.le hneed $$ [Hst HS]
  · iframe Hst HS
  rw [hpc, hra]
  unfold execDispK
  iapply HK $$ %R' %hret Hpc Hra Hregs Hst Hret Hw

end Finish

/-- A register already holding `v`: the dispatch runs rewrite `a6` this way,
so the jump table's bound check `bltu a6,a5` is decided by the tag. -/
theorem upd_eq_self {R : Nat → BitVec 64} {k : Nat} {v : BitVec 64} (h : R k = v) :
    Sym.upd R k v = R := funext fun r => by
  unfold Sym.upd; split
  · subst r; exact h.symm
  · rfl

/-- The facts of a node whose field `+8` points to a child expression (`expr`,
`ret e`): the node, the field, the child's representation. -/
structure ExprFieldNode (m : Mem) (P : Nat → Prop) (aS : BitVec 64) (tag : Nat) (e : Vsa.While.Expr)
    (p : Nat) : Prop where
  node : StmtNode m P aS tag 16
  field : ldv .ld m (aS + 8#64).toNat = BitVec.ofNat 64 p
  child : ExprReprWithin m P p e
  toNat : (BitVec.ofNat 64 p).toNat = p
  ne : BitVec.ofNat 64 p ≠ 0#64

theorem exprFieldNode_of {m : Mem} {P : Nat → Prop} {aS : BitVec 64} {tag p : Nat} {e : Vsa.While.Expr}
    (hg : ∀ k, P k → Interp.ReadOK k) (ht : read32 m aS.toNat = some tag) (hc : Covers P aS.toNat 4)
    (htag : tag < 2 ^ 31) (hr : read64 m (aS.toNat + 8) = some p) (cr : Covers P (aS.toNat + 8) 8)
    (hne : p ≠ 0) (hx : ExprReprWithin m P p e) : ExprFieldNode m P aS tag e p := by
  have hn := stmtNode_of (w := 16) hg ht hc htag (Or.inr (by decide))
    (fun j h1 h2 => field_mid hr cr h1 (by omega))
  have hl := readLE_lt hr
  have hpt : (BitVec.ofNat 64 p).toNat = p := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl]
  refine ⟨hn, field64 hr (by have := hn.hi; omega), hx, hpt, fun h => hne ?_⟩
  have := congrArg BitVec.toNat h
  rwa [hpt] at this

/-- An `expr e` statement node. -/
theorem exprNode_of {m : Mem} {P : Nat → Prop} {aS : BitVec 64} {e : Vsa.While.Expr}
    (h : StmtReprWithin m P aS.toNat (.expr e)) (hg : ∀ k, P k → Interp.ReadOK k) :
    ∃ p, ExprFieldNode m P aS 0 e p := by
  cases h with
  | expr h0 c0 hr cr hx =>
    refine ⟨_, exprFieldNode_of hg h0 c0 (by decide) hr cr ?_ hx⟩
    have := (hg _ (hx.tagCovers 0 (by decide))).lo
    omega

/-- A `ret e` statement node. -/
theorem retNode_of {m : Mem} {P : Nat → Prop} {aS : BitVec 64} {e : Vsa.While.Expr}
    (h : StmtReprWithin m P aS.toNat (.ret (some e))) (hg : ∀ k, P k → Interp.ReadOK k) :
    ∃ p, ExprFieldNode m P aS 6 e p := by
  cases h with
  | retSome h0 c0 hr cr hne hx => exact ⟨_, exprFieldNode_of hg h0 c0 (by decide) hr cr hne hx⟩

/-- A `ret;` statement node: the tag and the NULL expression field. -/
theorem retNullNode_of {m : Mem} {P : Nat → Prop} {aS : BitVec 64}
    (h : StmtReprWithin m P aS.toNat (.ret none)) (hg : ∀ k, P k → Interp.ReadOK k) :
    StmtNode m P aS 6 16 ∧ ldv .ld m (aS + 8#64).toNat = 0#64 := by
  cases h with
  | retNone h0 c0 hr cr =>
    have hn := stmtNode_of (w := 16) hg h0 c0 (by decide) (Or.inr (by decide))
      (fun j h1 h2 => field_mid hr cr h1 (by omega))
    exact ⟨hn, field64 hr (by have := hn.hi; omega)⟩

/-- The facts of an `if` node: the condition (`+8`), the branches (`+16`,
`+24`; the else pointer is NULL exactly when there is no else branch). -/
structure IfNode (m : Mem) (P : Nat → Prop) (aS : BitVec 64) (c : Vsa.While.Expr)
    (t : Vsa.While.Stmt) (eo : Option Vsa.While.Stmt) (pc pt pe : Nat) : Prop where
  node : StmtNode m P aS 3 32
  cond : ldv .ld m (aS + 8#64).toNat = BitVec.ofNat 64 pc
  condRepr : ExprReprWithin m P pc c
  condNat : (BitVec.ofNat 64 pc).toNat = pc
  condNe : BitVec.ofNat 64 pc ≠ 0#64
  thn : ldv .ld m (aS + 16#64).toNat = BitVec.ofNat 64 pt
  thnRepr : StmtReprWithin m P pt t
  thnNat : (BitVec.ofNat 64 pt).toNat = pt
  els : ldv .ld m (aS + 24#64).toNat = BitVec.ofNat 64 pe
  elsNat : (BitVec.ofNat 64 pe).toNat = pe
  elsRepr : ∀ se, eo = some se → StmtReprWithin m P pe se ∧ BitVec.ofNat 64 pe ≠ 0#64
  elsNone : eo = none → BitVec.ofNat 64 pe = 0#64

theorem ofNat_toNat_of_read {m : Mem} {a p : Nat} (h : read64 m a = some p) :
    (BitVec.ofNat 64 p).toNat = p := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (readLE_lt h)]

theorem ofNat_ne_of_read {m : Mem} {a p : Nat} (h : read64 m a = some p) (hne : p ≠ 0) :
    BitVec.ofNat 64 p ≠ 0#64 := fun e => hne (by
  have := congrArg BitVec.toNat e; rwa [ofNat_toNat_of_read h] at this)

/-- An `if` statement node. -/
theorem ifNode_of {m : Mem} {P : Nat → Prop} {aS : BitVec 64} {c : Vsa.While.Expr}
    {t : Vsa.While.Stmt} {eo : Option Vsa.While.Stmt}
    (h : StmtReprWithin m P aS.toNat (.ifStmt c t eo)) (hg : ∀ k, P k → Interp.ReadOK k) :
    ∃ pc pt pe, IfNode m P aS c t eo pc pt pe := by
  cases h with
  | ifElse h0 c0 hc cc hcr ht ct htr he ce hne her =>
    rename_i pc pt pe _
    have hn := stmtNode_of (w := 32) hg h0 c0 (by decide) (Or.inr (by decide)) (fun j h1 h2 => by
      by_cases j1 : j < 16
      · exact field_mid hc cc h1 (by omega)
      by_cases j2 : j < 24
      · exact field_mid ht ct (by omega) (by omega)
      · exact field_mid he ce (by omega) (by omega))
    have hcne : pc ≠ 0 := by have := (hg _ (hcr.tagCovers 0 (by decide))).lo; omega
    refine ⟨_, _, _, hn, field64 hc (by have := hn.hi; omega), hcr, ofNat_toNat_of_read hc,
      ofNat_ne_of_read hc hcne, field64 ht (by have := hn.hi; omega), htr, ofNat_toNat_of_read ht,
      field64 he (by have := hn.hi; omega), ofNat_toNat_of_read he, ?_, fun h => by cases h⟩
    intro se hse; cases hse; exact ⟨her, ofNat_ne_of_read he hne⟩
  | ifNoElse h0 c0 hc cc hcr ht ct htr he ce =>
    rename_i pc pt
    have hn := stmtNode_of (w := 32) hg h0 c0 (by decide) (Or.inr (by decide)) (fun j h1 h2 => by
      by_cases j1 : j < 16
      · exact field_mid hc cc h1 (by omega)
      by_cases j2 : j < 24
      · exact field_mid ht ct (by omega) (by omega)
      · exact field_mid he ce (by omega) (by omega))
    have hcne : pc ≠ 0 := by have := (hg _ (hcr.tagCovers 0 (by decide))).lo; omega
    refine ⟨_, _, _, hn, field64 hc (by have := hn.hi; omega), hcr, ofNat_toNat_of_read hc,
      ofNat_ne_of_read hc hcne, field64 ht (by have := hn.hi; omega), htr, ofNat_toNat_of_read ht,
      field64 he (by have := hn.hi; omega), ofNat_toNat_of_read he, (fun se h => by cases h),
      fun _ => rfl⟩

/-! ## Child calls from a frame of any size -/

/-- The geometry of a child call from a frame of `f` bytes below `s`: the
child runs at the lowered `sp` `sF` with its budget `nc`, its result slot at
frame offset `o`. (`EvalCallGeom` is the `f = 1088` instance's shape.) -/
structure CallGeomF (s sF : BitVec 64) (f np nc o : Nat) : Prop where
  sp : sF.toNat = s.toNat - f
  slot : (sF + BitVec.ofNat 64 o).toNat = s.toNat - f + o
  child : StackGeom sF nc
  fits : nc ≤ np - f
  below : np - f ≤ sF.toNat
  slotGeom : SlotGeom (sF + BitVec.ofNat 64 o)

theorem callGeomF {s sF : BitVec 64} {f np nc : Nat} (hsg : StackGeom s np)
    (hsF : sF.toNat = s.toNat - f) (hle : nc + f ≤ np)
    {o : Nat} (ho : o + 24 ≤ f) (ho8 : o % 8 = 0) (hf8 : f % 16 = 0) : CallGeomF s sF f np nc o := by
  have h1 := hsg.le; have h2 := hsg.lo; have h3 := hsg.hi; have h4 := hsg.al; have h5 := hsg.top
  simp only [Vsa.Sim.LayoutInstance.stackSL] at h2 h3
  have hsl : (sF + BitVec.ofNat 64 o).toNat = s.toNat - f + o := by
    rw [BitVec.toNat_add, hsF, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨hsF, hsl, ⟨by omega, ?_, ?_, ?_, ?_⟩, by omega, by omega, ⟨?_, ?_, ?_⟩⟩
  · simp only [Vsa.Sim.LayoutInstance.stackSL]; omega
  · simp only [Vsa.Sim.LayoutInstance.stackSL]; omega
  · omega
  · omega
  · rw [hsl]; omega
  · rw [hsl]; unfold Vsa.Sim.tohostAddr; omega
  · rw [hsl]; omega

section FrameF

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **Leaving a frame of `f` bytes**: the frame bytes rejoin the stack below
the entry `sp`. -/
theorem frameF_join {s sF : BitVec 64} {f n : Nat} (hsF : sF = s - BitVec.ofNat 64 f)
    (hn : n ≤ s.toNat) (hf : f ≤ n) :
    stackScratch (GF := GF) sF (n - f) ∗ ownSet (InExt (s.toNat - f, f)) byteAny ⊢
      stackScratch s n := by
  have hf64 : (BitVec.ofNat 64 f).toNat = f := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := s.isLt; omega)
  have e : (s - BitVec.ofNat 64 f).toNat = s.toNat - f := by
    have := toNat_sub_frame (s := s) (f := BitVec.ofNat 64 f) (by rw [hf64]; omega)
    rwa [hf64] at this
  have h := stackScratch_unframe (GF := GF) (s := s) (f := BitVec.ofNat 64 f) (n := n) hn (by omega)
  rw [e, hf64, ← hsF] at h
  exact h

end FrameF

section CallsF

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

/-- **A child call into `eval_expr`, partial mode, from a frame of `f`
bytes** (G's `ms_callEvalP` is the `f = 1088` shape): through the Löb
hypothesis, the `jal` paying the later. On abort the arm rebuilds its frame
(the child's stack, the slack, the frame bytes, the child's slot handed back)
and aborts itself with `abortAt Core s₀ n₀ ∗ Out`. -/
theorem ms_callEvalPF {Φ : Nat × String → IProp GF} {i : Nat} {code : List (BitVec 8)}
    (hexec : JalExec (vsaModel live) i code evalEntryPC)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {Core : IProp GF} {st : St} {d env : Nat} {e : Expr}
    {R : Nat → BitVec 64} {Mt : Mem} {slot aC aE s0 sF : BitVec 64} {f m n0 : Nat}
    {Out Kret : IProp GF} (hsF : sF = s0 - BitVec.ofNat 64 f)
    (hsg : StackGeom sF (evalNeed e d)) (hm : evalNeed e d ≤ m)
    (hms : m ≤ sF.toNat) (hn0 : m + f = n0) (hn0s : n0 ≤ s0.toNat)
    (hslg : SlotGeom slot) (hbb : e.bodiesBound perCallBudget = true) :
    ⌜EvalRegs R slot (BitVec.ofNat 64 inp) aC aE sF ∧
      ∀ b, InExt (slot.toNat, 24) b → InExt (s0.toNat - f, f) b⌝ ∗
      ▷ evalSpecP_body (vsaModel live) N L Room inp Core st d env e ∗ codeRes ∗
      □ astEG aC.toNat e ∗ □ frameAt env aE.toNat ∗
      ms (BitVec.ofNat 64 i) R (InExt (s0.toNat - f, f)) Mt ∗ stackScratch sF m ∗
      world N L Room inp .uncounted st d ∗ Out ∗
      (Kret ∧ (iprop(abortAt Core s0 n0 ∗ Out) -∗ (wpW (vsaModel live)).W Φ)) ∗
      (∀ (R' : Nat → BitVec 64) (w0 w1 w2 : BitVec 64) (st' : St) (v : Value),
        ⌜EvalE st d env e st' v⌝ -∗ ⌜KeepRegs calleeSaved R R'⌝ -∗ □ valOf N v w0 w1 w2 -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4)))
          (InExt (s0.toNat - f, f)) (slotWrite Mt slot.toNat w0 w1 w2) -∗
        stackScratch sF m -∗ world N L Room inp .uncounted st' d -∗ Out -∗
        (Kret ∧ (iprop(abortAt Core s0 n0 ∗ Out) -∗ (wpW (vsaModel live)).W Φ)) -∗
        (wpW (vsaModel live)).W Φ)
    ⊢ (wpW (vsaModel live)).W Φ := by
  unfold ms evalSpecP_body
  iintro ⟨%⟨hregs, hslot⟩, Hspec, #Hcode, #Hast, #Hfr, ⟨Hpc, Hra, Hregs, HS⟩, Hst, Hw, HOut, HK, Hk⟩
  ihave ⟨HS, Hslot⟩ := ownSet_carve_slot hslot $$ HS
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow hms hm $$ Hst
  ihave #Hi := instrAt_of_codeRes hcode $$ Hcode
  ihave Hspec := Hspec $$ %slot %aE %aC %sF %R
  simp only [wpW_W]
  iapply wp_callAbort_later hexec
  iframe Hi Hspec Hpc Hra
  isplitl [Hregs Hst Hslot Hw]
  · unfold evalPre
    iframe Hregs Hst Hslot Hw Hcode Hast Hfr
    ipureintro
    exact ⟨hal, hregs, hsg, hslg, hbb⟩
  isplit
  · iintro Hpc Hra ⟨%st', %v, %hE, Hpost⟩
    unfold evalPost
    icases Hpost with ⟨%R', Hregs, %hkeep, Hst, Hval, Hw⟩
    ihave Hst := stackScratch_widen hms hm $$ [Hslack Hst]
    · iframe Hslack Hst
    ihave ⟨%w0, %w1, %w2, #Hv, HS⟩ := ownSet_join_slot hslot $$ [HS Hval]
    · iframe HS Hval
    iapply Hk $$ %R' %w0 %w1 %w2 %st' %v %hE %hkeep Hv [Hpc Hra Hregs HS] Hst Hw HOut HK
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
    ihave Hst := frameF_join (s := s0) (n := n0) hsF hn0s (by omega) $$ [Hst HS]
    · rw [show n0 - f = m by omega]; iframe Hst HS
    ihave HK := and_elim_r $$ HK
    iapply HK
    iframe HC Hst HOut

end CallsF

/-! ## A value slot outside the frame (the `ret` slot) -/

/-- A doubleword of a tracking memory's image is its load. -/
theorem imgW_eq_ldv (M : Mem) (a : Nat) : imgW (imgM M) a = ldv .ld M a :=
  (ldvf_ld_imgLE rfl).symm

/-- A load reads only its window. -/
theorem ldv_congrW (k : MKind) {Mt Mt' : Mem} {a : Nat}
    (h : ∀ j, j < widthOfM k → imgM Mt (a + j) = imgM Mt' (a + j)) : ldv k Mt a = ldv k Mt' a := by
  unfold ldv bytesAt
  congr 1
  apply List.map_congr_left
  intro j hj
  exact h j (List.mem_range.1 hj)

section Slot

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **A 24-byte slot into a run's owned bytes**, at a tracking memory that
agrees with the old one on them. -/
theorem ms_slotIn {pc : BitVec 64} {R : Nat → BitVec 64} {S : Nat → Prop} {M : Mem} {a : Nat} :
    ms (GF := GF) pc R S M ∗ slot24 a ⊢
      ∃ M', ms pc R (fun x => S x ∨ InExt (a, 24) x) M' ∗
        ⌜(∀ x, S x → imgM M' x = imgM M x) ∧ ∀ x, S x → ¬ InExt (a, 24) x⌝ := by
  iintro ⟨Hms, Hslot⟩
  unfold slot24 blockOwn
  ihave ⟨%f, Hslot⟩ := ownSet_fn _ $$ Hslot
  ihave ⟨%Mt, Hslot⟩ := ownSet_mem _ f $$ Hslot
  ihave ⟨%M', Hms, %⟨h1, -, h3⟩⟩ := ms_join $$ [Hms Hslot]
  · iframe Hms Hslot
  iexists M'
  iframe Hms
  ipureintro; exact ⟨h1, h3⟩

/-- **A represented value out of a run's owned bytes**: the slot's three
words mean `v`. -/
theorem ms_valOut [InterpGS GF] (N : NativeAddrs) {pc : BitVec 64} {R : Nat → BitVec 64}
    {S : Nat → Prop} {M : Mem} {a : Nat} {v : Value} {w0 w1 w2 : BitVec 64}
    (hd : ∀ x, S x → ¬ InExt (a, 24) x) (h0 : ldv .ld M a = w0) (h8 : ldv .ld M (a + 8) = w1)
    (h16 : ldv .ld M (a + 16) = w2) :
    ms (GF := GF) pc R (fun x => S x ∨ InExt (a, 24) x) M ∗ □ valOf N v w0 w1 w2 ⊢
      ms pc R S M ∗ valAt N a v := by
  iintro ⟨Hms, #Hv⟩
  ihave ⟨Hms, Hslot⟩ := ms_split hd $$ Hms
  iframe Hms
  iapply valAt_of_img N
  iframe Hslot
  unfold valImg
  rw [imgW_eq_ldv, imgW_eq_ldv, imgW_eq_ldv, h0, h8, h16]
  iexact Hv

end Slot

/-- Two owned byte ranges that share no byte are apart. -/
theorem slot_apart {a b n : Nat} (hn : 0 < n)
    (h : ∀ x, InExt (b, n) x → ¬ InExt (a, 24) x) : a + 24 ≤ b ∨ b + n ≤ a := by
  by_cases h1 : a + 24 ≤ b
  · exact .inl h1
  by_cases h2 : b + n ≤ a
  · exact .inr h2
  exfalso
  have := h (max a b) (by simp only [InExt]; omega)
  simp only [InExt] at this; omega

/-! ## The two exits every arm ends in -/

/-- The spills survive a store below them. -/
theorem ExecSaved.store {Mt : Mem} {s ret v8 v9 v18 v19 : BitVec 64}
    (h : ExecSaved Mt s ret v8 v9 v18 v19) {a w : Nat} (v : BitVec 64) (_hs : 176 ≤ s.toNat)
    (ha : a + w ≤ s.toNat - 176 + 136 ∨ s.toNat ≤ a) :
    ExecSaved (writeLog Mt [(a, w, v)]) s ret v8 v9 v18 v19 :=
  have e : widthOfM MKind.ld = 8 := rfl
  ⟨by rw [ldv_store_miss .ld Mt v (by omega)]; exact h.ra,
   by rw [ldv_store_miss .ld Mt v (by omega)]; exact h.s0,
   by rw [ldv_store_miss .ld Mt v (by omega)]; exact h.s1,
   by rw [ldv_store_miss .ld Mt v (by omega)]; exact h.s2,
   by rw [ldv_store_miss .ld Mt v (by omega)]; exact h.s3⟩

/-- The spills read through a memory agreeing on the frame. -/
theorem ExecSaved.congr {Mt Mt' : Mem} {s ret v8 v9 v18 v19 : BitVec 64}
    (h : ExecSaved Mt s ret v8 v9 v18 v19)
    (hag : ∀ x, InExt (s.toNat - 176, 176) x → imgM Mt' x = imgM Mt x) :
    ExecSaved Mt' s ret v8 v9 v18 v19 := by
  have c : ∀ o, o + 8 ≤ 176 → ldv .ld Mt' (s.toNat - 176 + o) = ldv .ld Mt (s.toNat - 176 + o) :=
    fun o ho => ldv_congrW .ld fun j hj => hag _ (by
      simp only [InExt]; have : widthOfM MKind.ld = 8 := rfl; omega)
  exact ⟨(c 168 (by decide)).trans h.ra, (c 160 (by decide)).trans h.s0, (c 152 (by decide)).trans h.s1,
    (c 144 (by decide)).trans h.s2, (c 136 (by decide)).trans h.s3⟩

/-- The spills read through a memory agreeing on the top 40 bytes of the
frame (where they live). -/
theorem ExecSaved.congrHi {Mt Mt' : Mem} {s ret v8 v9 v18 v19 : BitVec 64}
    (h : ExecSaved Mt s ret v8 v9 v18 v19)
    (hag : ∀ x, s.toNat - 40 ≤ x → x < s.toNat → imgM Mt' x = imgM Mt x) (hs : 176 ≤ s.toNat) :
    ExecSaved Mt' s ret v8 v9 v18 v19 := by
  have c : ∀ o, 136 ≤ o → o + 8 ≤ 176 →
      ldv .ld Mt' (s.toNat - 176 + o) = ldv .ld Mt (s.toNat - 176 + o) :=
    fun o h1 ho => ldv_congrW .ld fun j hj => hag _ (by omega) (by
      have : widthOfM MKind.ld = 8 := rfl; omega)
  exact ⟨(c 168 (by decide) (by decide)).trans h.ra, (c 160 (by decide) (by decide)).trans h.s0,
    (c 152 (by decide) (by decide)).trans h.s1, (c 144 (by decide) (by decide)).trans h.s2,
    (c 136 (by decide) (by decide)).trans h.s3⟩

/-- Carry `ExecSaved` back through a memory's stores and calls' slot words to
a memory it is known for (`hoff` normalizes the frame addresses). -/
syntax "ix_esaved " term " using " term : tactic
macro_rules
  | `(tactic| ix_esaved $h using $hoff) => `(tactic| (
      (try unfold slotWrite);
      repeat refine ExecSaved.store ?_ _ (by omega) (by first | omega | (rw [($hoff:term)] <;> first | omega | decide));
      exact $h))

#ix_seg ExecEpi_run {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {DA : List Nat} {s ret v8 v9 v18 v19 : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hal : ret.toNat % 4 = 0)
    (h2 : R 2 = s + 18446744073709551440#64)
    (hRA : ldv .ld Mt (s + 18446744073709551440#64 + 168#64).toNat = ret)
    (hS0 : ldv .ld Mt (s + 18446744073709551440#64 + 160#64).toNat = v8)
    (hS1 : ldv .ld Mt (s + 18446744073709551440#64 + 152#64).toNat = v9)
    (hS2 : ldv .ld Mt (s + 18446744073709551440#64 + 144#64).toNat = v18)
    (hS3 : ldv .ld Mt (s + 18446744073709551440#64 + 136#64).toNat = v19) :
    IW live m DA (InExt (s.toNat - 176, 176)) Q 0x8000409c#64 R Mt
  by ix_run hlive using [h2, hRA, hS0, hS1, hS2, hS3, hsf, hal]

#ix_seg ExecRetCopy_run {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {DA : List Nat} {s aRet ret v8 v9 v18 v19 : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hr1 : tohostAddr + 16 ≤ aRet.toNat) (hr2 : aRet.toNat + 24 ≤ 0x100000000) (hr3 : aRet.toNat % 8 = 0)
    (hrd : aRet.toNat + 24 ≤ s.toNat - 176 ∨ s.toNat ≤ aRet.toNat)
    (hal : ret.toNat % 4 = 0)
    (h2 : R 2 = s + 18446744073709551440#64) (h18 : R 18 = aRet)
    (hRA : ldv .ld Mt (s + 18446744073709551440#64 + 168#64).toNat = ret)
    (hS0 : ldv .ld Mt (s + 18446744073709551440#64 + 160#64).toNat = v8)
    (hS1 : ldv .ld Mt (s + 18446744073709551440#64 + 152#64).toNat = v9)
    (hS2 : ldv .ld Mt (s + 18446744073709551440#64 + 144#64).toNat = v18)
    (hS3 : ldv .ld Mt (s + 18446744073709551440#64 + 136#64).toNat = v19) :
    IW live m DA (fun a => InExt (s.toNat - 176, 176) a ∨ InExt (aRet.toNat, 24) a) Q 0x80004138#64 R Mt
  by ix_run hlive using [h2, h18, hRA, hS0, hS1, hS2, hS3, hsf, hal]

#ix_seg ExecEpiRet_run {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {DA : List Nat} {s ret v8 v9 v18 v19 : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hal : ret.toNat % 4 = 0)
    (h2 : R 2 = s + 18446744073709551440#64)
    (hRA : ldv .ld Mt (s + 18446744073709551440#64 + 168#64).toNat = ret)
    (hS0 : ldv .ld Mt (s + 18446744073709551440#64 + 160#64).toNat = v8)
    (hS1 : ldv .ld Mt (s + 18446744073709551440#64 + 152#64).toNat = v9)
    (hS2 : ldv .ld Mt (s + 18446744073709551440#64 + 144#64).toNat = v18)
    (hS3 : ldv .ld Mt (s + 18446744073709551440#64 + 136#64).toNat = v19) :
    IW live m DA (InExt (s.toNat - 176, 176)) Q 0x80004150#64 R Mt
  by ix_run hlive using [h2, hRA, hS0, hS1, hS2, hS3, hsf, hal]

section Exits

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

/-- A register write outside `l` keeps `l`. -/
theorem KeepRegs.upd {l : List Nat} {R R' : Nat → BitVec 64} (h : KeepRegs l R R') {k : Nat}
    (hk : k ∉ l) (v : BitVec 64) : KeepRegs l R (Sym.upd R' k v) := fun x hx => by
  have hne : x ≠ k := fun e => hk (e ▸ hx)
  rw [upd_other _ _ hne]; exact h x hx

/-- `ExecRet` from its fields. -/
theorem execRet_mk {R0 R' : Nat → BitVec 64} {s v8 v9 v18 v19 : BitVec 64} {status : Status}
    (h2 : R' 2 = s) (h8 : R' 8 = v8) (h9 : R' 9 = v9) (h18 : R' 18 = v18) (h19 : R' 19 = v19)
    (hi : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R0 R') (h10 : R' 10 = statusCode status) :
    ExecRet R0 R' s v8 v9 v18 v19 status := ⟨h2, h8, h9, h18, h19, hi, h10⟩

/-- The registers an arm returns with, read off the epilogue's end state
(`hk : KeepRegs [20..27] R0 R` for the arm's registers `R` the end state
updates; the status in `a0` by `rfl` or an assumption). -/
syntax "ix_execRet " term : tactic
macro_rules
  | `(tactic| ix_execRet $hk) => `(tactic| refine execRet_mk (by ix_reg; exact execSP_restore _)
      (by ix_reg) (by ix_reg) (by ix_reg) (by ix_reg)
      (by repeat (first | exact $hk | refine KeepRegs.upd ?_ (by decide) _))
      (by ix_reg; first | rfl | assumption))

/-- **The shared exit `0x8000409c`**, for either WP: the status already in
`a0`, the epilogue restores the spills and returns; the frame rejoins the stack
and the dispatch-point continuation takes the rest. -/
theorem wp_execEpi (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {ρ : Regime} {st' : St} {d : Nat} {sm : Stmt} {status : Status}
    {aRet s ret v8 v9 v18 v19 : BitVec 64} {R0 R : Nat → BitVec 64} {Mt : Mem}
    (hsg : StackGeom s (execNeed sm d)) (hal : ret.toNat % 4 = 0)
    (h2 : R 2 = execSP s) (h10 : R 10 = statusCode status)
    (hsv : ExecSaved Mt s ret v8 v9 v18 v19) (hk : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R0 R) :
    codeRes ∗ ms 0x8000409c#64 R (InExt (s.toNat - 176, 176)) Mt ∗
      stackScratch (execSP s) (execNeed sm d - 176) ∗
      statusRet N aRet.toNat status ∗ world N L Room inp ρ st' d ∗
      execDispK (vsaModel live) N L Room inp Wp Φ ρ st' d sm status aRet s R0 ret v8 v9 v18 v19
    ⊢ Wp.W Φ := by
  obtain ⟨hfg, _⟩ := execFrameGeom_of hsg
  have hoff := execSP_offF (s := s) hfg.sf (by have := hfg.hi; omega)
  iintro ⟨#Hcode, Hms, Hst, Hret, Hw, HK⟩
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ [])
    (F := iprop(stackScratch (execSP s) (execNeed sm d - 176) ∗ statusRet N aRet.toNat status ∗
      world N L Room inp ρ st' d ∗
      execDispK (vsaModel live) N L Room inp Wp Φ ρ st' d sm status aRet s R0 ret v8 v9 v18 v19))
  rotate_left
  · iframe Hms Hst Hret Hw HK
    iapply codeRes_text $$ Hcode
  intro F'
  refine ExecEpi_run (m := ∅) (DA := []) (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19) hlive
    hfg.sf hfg.lo hfg.hi hfg.al hal h2 ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hoff _ (by decide)]; exact hsv.ra
  · rw [hoff _ (by decide)]; exact hsv.s0
  · rw [hoff _ (by decide)]; exact hsv.s1
  · rw [hoff _ (by decide)]; exact hsv.s2
  · rw [hoff _ (by decide)]; exact hsv.s3
  intros
  apply swp_closeRM
  intro R' Mt' hR' _
  have hfin := execDisp_finish (N := N) (L := L) (Room := Room) (inp := inp) Wp
    (Φ := Φ) (ρ := ρ) (st' := st') (d := d) (sm := sm) (status := status) (aRet := aRet) (s := s)
    (ret := ret) (R := R0) (R' := R') (Mt := Mt') (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19)
    (pc := ret) hsg rfl (by subst hR'; ix_reg) (by subst hR'; ix_execRet hk)
  unfold F'
  iintro ⟨⟨Hst, Hret, Hw, HK⟩, Hms⟩
  iapply hfin
  iframe Hms Hst Hret Hw HK

/-- **The `ret` exit `0x80004138`**, for either WP: the value in the frame
slot `sp+16` (its words `w0 w1 w2`, meaning `v`) is copied into the caller's
`ret` slot, the status `3` set and the epilogue run; the continuation gets the
slot as `valAt aRet v`. -/
theorem wp_execRetCopy (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {ρ : Regime} {st' : St} {d : Nat} {sm : Stmt} {v : Value}
    {aRet s ret v8 v9 v18 v19 w0 w1 w2 : BitVec 64} {R0 R : Nat → BitVec 64} {Mt : Mem}
    (hsg : StackGeom s (execNeed sm d)) (hsl : SlotGeom aRet) (hal : ret.toNat % 4 = 0)
    (h2 : R 2 = execSP s) (h18 : R 18 = aRet)
    (hsv : ExecSaved Mt s ret v8 v9 v18 v19) (hk : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R0 R)
    (hw0 : ldv .ld Mt (s.toNat - 176 + 16) = w0) (hw1 : ldv .ld Mt (s.toNat - 176 + 24) = w1)
    (hw2 : ldv .ld Mt (s.toNat - 176 + 32) = w2) :
    codeRes ∗ ms 0x80004138#64 R (InExt (s.toNat - 176, 176)) Mt ∗ slot24 aRet.toNat ∗
      □ valOf N v w0 w1 w2 ∗ stackScratch (execSP s) (execNeed sm d - 176) ∗
      world N L Room inp ρ st' d ∗
      execDispK (vsaModel live) N L Room inp Wp Φ ρ st' d sm (.ret v) aRet s R0 ret v8 v9 v18 v19
    ⊢ Wp.W Φ := by
  obtain ⟨hfg, _⟩ := execFrameGeom_of hsg
  have hoff := execSP_offF (s := s) hfg.sf (by have := hfg.hi; omega)
  iintro ⟨#Hcode, Hms, Hslot, #Hv, Hst, Hw, HK⟩
  ihave ⟨%M2, Hms, %⟨hag, hd⟩⟩ := ms_slotIn $$ [Hms Hslot]
  · iframe Hms Hslot
  have hrd := slot_apart (by decide) hd
  have hsv2 := hsv.congr hag
  have hag8 : ∀ o, o + 8 ≤ 176 → ∀ j, j < 8 → imgM M2 (s.toNat - 176 + o + j) =
      imgM Mt (s.toNat - 176 + o + j) := fun o ho j hj => hag _ (by simp only [InExt]; omega)
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ [])
    (F := iprop(stackScratch (execSP s) (execNeed sm d - 176) ∗ world N L Room inp ρ st' d ∗
      □ valOf N v w0 w1 w2 ∗
      execDispK (vsaModel live) N L Room inp Wp Φ ρ st' d sm (.ret v) aRet s R0 ret v8 v9 v18 v19))
  rotate_left
  · iframe Hms Hst Hw Hv HK
    iapply codeRes_text $$ Hcode
  intro F'
  refine ExecRetCopy_run (m := ∅) (DA := []) (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19) hlive
    hfg.sf hfg.lo hfg.hi hfg.al hsl.lo hsl.hi hsl.al
    (by rcases hrd with h | h; exact .inl h; exact .inr (by omega)) hal h2 h18 ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hoff _ (by decide)]; exact hsv2.ra
  · rw [hoff _ (by decide)]; exact hsv2.s0
  · rw [hoff _ (by decide)]; exact hsv2.s1
  · rw [hoff _ (by decide)]; exact hsv2.s2
  · rw [hoff _ (by decide)]; exact hsv2.s3
  intros
  apply swp_closeRM
  intro R' Mt' hR' hMt'
  have hr8 : (aRet + 8#64).toNat = aRet.toNat + 8 := by
    have := hsl.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hr16 : (aRet + 16#64).toNat = aRet.toNat + 16 := by
    have := hsl.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hsrc : ∀ o, o + 8 ≤ 176 → ldv .ld M2 (s + 18446744073709551440#64 + BitVec.ofNat 64 o).toNat =
      ldv .ld Mt (s.toNat - 176 + o) := fun o ho => by
    rw [hoff _ (by omega), ldv_congrW .ld (hag8 o ho)]
  have h0 : ldv .ld Mt' aRet.toNat = w0 := by
    rw [hMt', hr8, hr16]; ix_fwd; rw [hsrc 16 (by decide), hw0]
  have h8 : ldv .ld Mt' (aRet.toNat + 8) = w1 := by
    rw [hMt', hr8, hr16]; ix_fwd; rw [hsrc 24 (by decide), hw1]
  have h16 : ldv .ld Mt' (aRet.toNat + 16) = w2 := by
    rw [hMt', hr8, hr16]; ix_fwd; rw [hsrc 32 (by decide), hw2]
  have hfin := execDisp_finish (N := N) (L := L) (Room := Room) (inp := inp) Wp
    (Φ := Φ) (ρ := ρ) (st' := st') (d := d) (sm := sm) (status := .ret v) (aRet := aRet) (s := s)
    (ret := ret) (R := R0) (R' := R') (Mt := Mt') (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19)
    (pc := ret) hsg rfl (by subst hR'; ix_reg) (by subst hR'; ix_execRet hk)
  simp only [statusRet] at hfin
  unfold F'
  iintro ⟨⟨Hst, Hw, #Hv, HK⟩, Hms⟩
  ihave ⟨Hms, Hval⟩ := ms_valOut N hd h0 h8 h16 $$ [Hms]
  · iframe Hms Hv
  iapply hfin
  iframe Hms Hst Hw HK Hval

/-- **The `ret` exit without a copy `0x80004150`**, for either WP (a loop
left with a returned value already in the `ret` slot): `li a0,3` and the
epilogue. -/
theorem wp_execEpiRet (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {ρ : Regime} {st' : St} {d : Nat} {sm : Stmt} {v : Value}
    {aRet s ret v8 v9 v18 v19 : BitVec 64} {R0 R : Nat → BitVec 64} {Mt : Mem}
    (hsg : StackGeom s (execNeed sm d)) (hal : ret.toNat % 4 = 0)
    (h2 : R 2 = execSP s)
    (hsv : ExecSaved Mt s ret v8 v9 v18 v19) (hk : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R0 R) :
    codeRes ∗ ms 0x80004150#64 R (InExt (s.toNat - 176, 176)) Mt ∗
      stackScratch (execSP s) (execNeed sm d - 176) ∗
      statusRet N aRet.toNat (.ret v) ∗ world N L Room inp ρ st' d ∗
      execDispK (vsaModel live) N L Room inp Wp Φ ρ st' d sm (.ret v) aRet s R0 ret v8 v9 v18 v19
    ⊢ Wp.W Φ := by
  obtain ⟨hfg, _⟩ := execFrameGeom_of hsg
  have hoff := execSP_offF (s := s) hfg.sf (by have := hfg.hi; omega)
  iintro ⟨#Hcode, Hms, Hst, Hret, Hw, HK⟩
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ [])
    (F := iprop(stackScratch (execSP s) (execNeed sm d - 176) ∗ statusRet N aRet.toNat (.ret v) ∗
      world N L Room inp ρ st' d ∗
      execDispK (vsaModel live) N L Room inp Wp Φ ρ st' d sm (.ret v) aRet s R0 ret v8 v9 v18 v19))
  rotate_left
  · iframe Hms Hst Hret Hw HK
    iapply codeRes_text $$ Hcode
  intro F'
  refine ExecEpiRet_run (m := ∅) (DA := []) (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19) hlive
    hfg.sf hfg.lo hfg.hi hfg.al hal h2 ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hoff _ (by decide)]; exact hsv.ra
  · rw [hoff _ (by decide)]; exact hsv.s0
  · rw [hoff _ (by decide)]; exact hsv.s1
  · rw [hoff _ (by decide)]; exact hsv.s2
  · rw [hoff _ (by decide)]; exact hsv.s3
  intros
  apply swp_closeRM
  intro R' Mt' hR' _
  have hfin := execDisp_finish (N := N) (L := L) (Room := Room) (inp := inp) Wp
    (Φ := Φ) (ρ := ρ) (st' := st') (d := d) (sm := sm) (status := .ret v) (aRet := aRet) (s := s)
    (ret := ret) (R := R0) (R' := R') (Mt := Mt') (v8 := v8) (v9 := v9) (v18 := v18) (v19 := v19)
    (pc := ret) hsg rfl (by subst hR'; ix_reg) (by subst hR'; ix_execRet hk)
  unfold F'
  iintro ⟨⟨Hst, Hret, Hw, HK⟩, Hms⟩
  iapply hfin
  iframe Hms Hst Hret Hw HK

end Exits

section HelperSlot

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs}

/-- **A helper that fills a frame slot**, for either WP (`value_null`,
`value_bool`, … into a slot of the arm's frame): the slot is carved out of
the arm's owned bytes for the call and joined back as three words whose
meaning is `valOf`. -/
theorem ms_callHelperSlot (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)} {entry : BitVec 64}
    (hexec : JalExec (vsaModel live) i code entry)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {clob : List Nat} {pins : (Nat → BitVec 64) → Prop} {v : Value}
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {a : BitVec 64}
    (hS : ∀ b, InExt (a.toNat, 24) b → S b) (hsl : SlotGeom a) :
    ⌜pins R⌝ ∗ helperSpec (vsaModel live) Wp entry clob pins
        iprop(slot24 a.toNat ∗ ⌜SlotGeom a⌝) (fun _ => valAt N a.toNat v) ∗ codeRes ∗
      ms (BitVec.ofNat 64 i) R S Mt ∗
      (∀ (R' : Nat → BitVec 64) (w0 w1 w2 : BitVec 64), ⌜∀ x ∈ fRegs, x ∉ clob → R' x = R x⌝ -∗
        □ valOf N v w0 w1 w2 -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S
          (slotWrite Mt a.toNat w0 w1 w2) -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨%hp, Hspec, #Hcode, Hms, Hk⟩
  unfold ms
  icases Hms with ⟨Hpc, Hra, Hregs, HS⟩
  ihave ⟨HS, Hslot⟩ := ownSet_carve_slot hS $$ HS
  iapply ms_callHelper Wp hexec hcode hal (S := fun b => S b ∧ ¬ InExt (a.toNat, 24) b) (Mt := Mt)
  iframe Hspec Hcode
  isplitl []
  · ipureintro; exact hp
  isplitl [Hpc Hra Hregs HS]
  · unfold ms; iframe Hpc Hra Hregs HS
  isplitl [Hslot]
  · iframe Hslot; ipureintro; exact hsl
  iintro %R' %hk Hval Hms
  unfold ms
  icases Hms with ⟨Hpc, Hra, Hregs, HS⟩
  ihave ⟨%w0, %w1, %w2, #Hv, HS⟩ := ownSet_join_slot hS $$ [HS Hval]
  · iframe HS Hval
  iapply Hk $$ %R' %w0 %w1 %w2 %hk Hv
  iframe Hpc Hra Hregs HS

end HelperSlot

section HelperVal

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs}

omit I in
/-- The run's owned bytes with a slot inside them, rearranged. -/
theorem ms_iffE {pc : BitVec 64} {R : Nat → BitVec 64} {S T : Nat → Prop} {M : Mem}
    (h : ∀ k, S k ↔ T k) : ms (GF := GF) pc R S M ⊢ ms pc R T M := by
  unfold ms
  iintro ⟨Hpc, Hra, Hregs, HS⟩
  iframe Hpc Hra Hregs
  iapply ownSet_iff _ h $$ HS

/-- **A value slot out of a run's owned bytes**: its three words mean `v`. -/
theorem ms_valCarve (N : NativeAddrs) {pc : BitVec 64} {R : Nat → BitVec 64} {S : Nat → Prop}
    {M : Mem} {a : Nat} {v : Value} {w0 w1 w2 : BitVec 64}
    (hS : ∀ b, InExt (a, 24) b → S b)
    (h0 : ldv .ld M a = w0) (h8 : ldv .ld M (a + 8) = w1) (h16 : ldv .ld M (a + 16) = w2) :
    ms (GF := GF) pc R S M ∗ □ valOf N v w0 w1 w2 ⊢
      ms pc R (fun k => S k ∧ ¬ InExt (a, 24) k) M ∗ valAt N a v := by
  have hsl1 : ∀ k, S k ↔ ((S k ∧ ¬ InExt (a, 24) k) ∨ InExt (a, 24) k) := fun k => by
    constructor
    · intro h; by_cases h' : InExt (a, 24) k
      · exact .inr h'
      · exact .inl ⟨h, h'⟩
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact hS k h
  iintro ⟨Hms, #Hv⟩
  ihave Hms := ms_iffE hsl1 $$ Hms
  ihave ⟨Hms, Hslot⟩ := ms_split (fun k h1 h2 => h1.2 h2) $$ Hms
  iframe Hms
  iapply valAt_of_img N (a := a) (v := v) (mv := imgM M) $$ [Hslot]
  iframe Hslot
  unfold valImg
  rw [imgW_eq_ldv, imgW_eq_ldv, imgW_eq_ldv, h0, h8, h16]
  iexact Hv

/-- **And back in**, at a tracking memory agreeing on the run's other bytes. -/
theorem ms_valUncarve (N : NativeAddrs) {pc : BitVec 64} {R : Nat → BitVec 64} {S : Nat → Prop}
    {M : Mem} {a : Nat} {v : Value} (hS : ∀ b, InExt (a, 24) b → S b) :
    ms (GF := GF) pc R (fun k => S k ∧ ¬ InExt (a, 24) k) M ∗ valAt N a v ⊢
      ∃ M', ms pc R S M' ∗ ⌜∀ x, S x → ¬ InExt (a, 24) x → imgM M' x = imgM M x⌝ := by
  have hsl1 : ∀ k, ((S k ∧ ¬ InExt (a, 24) k) ∨ InExt (a, 24) k) ↔ S k := fun k => by
    constructor
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact hS k h
    · intro h; by_cases h' : InExt (a, 24) k
      · exact .inr h'
      · exact .inl ⟨h, h'⟩
  iintro ⟨Hms, Hval⟩
  ihave ⟨%Ms, HsS, -⟩ := valAt_tracked N _ _ $$ Hval
  ihave ⟨%M', Hms, %⟨h1, -, -⟩⟩ := ms_join $$ [Hms HsS]
  · iframe Hms HsS
  iexists M'
  isplitl
  · iapply ms_iffE hsl1 $$ Hms
  · ipureintro; exact fun x hx hn => h1 x ⟨hx, hn⟩

/-- **A helper reading a value in a frame slot**, for either WP
(`value_truthy` on the arm's copy at `sp+16`): the slot's three words `w0 w1
w2` mean `v`; the slot is lent to the helper as `valAt` and handed back, the
arm's other bytes unchanged. -/
theorem ms_callHelperVal (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)} {entry : BitVec 64}
    (hexec : JalExec (vsaModel live) i code entry)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hal : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0)
    {clob : List Nat} {pins : (Nat → BitVec 64) → Prop} {v : Value}
    {Q : (Nat → BitVec 64) → IProp GF}
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} {a w0 w1 w2 : BitVec 64}
    (hS : ∀ b, InExt (a.toNat, 24) b → S b) (hsl : SlotGeom a)
    (h0 : ldv .ld Mt a.toNat = w0) (h8 : ldv .ld Mt (a.toNat + 8) = w1)
    (h16 : ldv .ld Mt (a.toNat + 16) = w2) :
    ⌜pins R⌝ ∗ helperSpec (vsaModel live) Wp entry clob pins
        iprop(valAt N a.toNat v ∗ ⌜SlotGeom a⌝) (fun rv' => iprop(valAt N a.toNat v ∗ Q rv')) ∗
      codeRes ∗ ms (BitVec.ofNat 64 i) R S Mt ∗ □ valOf N v w0 w1 w2 ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem), ⌜∀ x ∈ fRegs, x ∉ clob → R' x = R x⌝ -∗
        ⌜∀ x, S x → ¬ InExt (a.toNat, 24) x → imgM Mt' x = imgM Mt x⌝ -∗ Q R' -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt' -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  have hsl1 : ∀ k, S k ↔ ((S k ∧ ¬ InExt (a.toNat, 24) k) ∨ InExt (a.toNat, 24) k) := fun k => by
    constructor
    · intro h; by_cases h' : InExt (a.toNat, 24) k
      · exact .inr h'
      · exact .inl ⟨h, h'⟩
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact hS k h
  iintro ⟨%hp, Hspec, #Hcode, Hms, #Hv, Hk⟩
  ihave Hms := ms_iffE hsl1 $$ Hms
  ihave ⟨Hms, Hslot⟩ := ms_split (fun k h1 h2 => h1.2 h2) $$ Hms
  ihave Hval := valAt_of_img N (a := a.toNat) (v := v) (mv := imgM Mt) $$ [Hslot]
  · iframe Hslot
    unfold valImg
    rw [imgW_eq_ldv, imgW_eq_ldv, imgW_eq_ldv, h0, h8, h16]
    iexact Hv
  iapply ms_callHelper Wp hexec hcode hal (S := fun k => S k ∧ ¬ InExt (a.toNat, 24) k) (Mt := Mt)
  iframe Hspec Hcode Hms
  isplitl []
  · ipureintro; exact hp
  isplitl [Hval]
  · iframe Hval; ipureintro; exact hsl
  iintro %R' %hk ⟨Hval, HQ⟩ Hms
  ihave ⟨%Ms, HsS, -⟩ := valAt_tracked N _ _ $$ Hval
  ihave ⟨%M', Hms, %⟨h1, -, -⟩⟩ := ms_join $$ [Hms HsS]
  · iframe Hms HsS
  ihave Hms := ms_iffE (fun k => (hsl1 k).symm) $$ Hms
  iapply Hk $$ %R' %M' %hk %(fun x hx hn => h1 x ⟨hx, hn⟩) HQ Hms

end HelperVal

/-! ## The in-frame tail call (the `if` arm's re-dispatch) -/

section Redispatch

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

omit I in
/-- The stack below the lowered `sp` for a child re-dispatched in the frame:
the child's part and the slack between the two budgets. -/
theorem stack_redispatch {s : BitVec 64} {n n' : Nat} (hsg : StackGeom s n) (hle : n' ≤ n)
    (h176 : 176 ≤ n') (hsf : (execSP s).toNat = s.toNat - 176) :
    stackScratch (GF := GF) (execSP s) (n - 176) ⊢
      blockOwn (s.toNat - n) (n - n') ∗ stackScratch (execSP s) (n' - 176) := by
  iintro H
  ihave ⟨H1, H2⟩ := stackScratch_narrow (s := execSP s) (n := n - 176) (m := n' - 176)
    (by rw [hsf]; have := hsg.le; omega) (by omega) $$ H
  rw [hsf, show s.toNat - 176 - (n - 176) = s.toNat - n by have := hsg.le; omega,
    show n - 176 - (n' - 176) = n - n' by omega]
  iframe H1 H2

/-- **The parent's return continuation serves a child re-dispatched in its
frame**: the child returns to the same address with the same spills; its
registers at the dispatch keep the parent's `s4`-`s11`; the slack joins the
child's stack back into the parent's. -/
theorem execDispK_redispatch (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {ρ : Regime} {st' : St} {d : Nat} {sm sm' : Stmt} {status : Status}
    {aRet s ret v8 v9 v18 v19 : BitVec 64} {R R3 : Nat → BitVec 64}
    (hsg : StackGeom s (execNeed sm d)) (hle : execNeed sm' d ≤ execNeed sm d)
    (hk : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R R3) :
    blockOwn (s.toNat - execNeed sm d) (execNeed sm d - execNeed sm' d) ∗
      execDispK (vsaModel live) N L Room inp Wp Φ ρ st' d sm status aRet s R ret v8 v9 v18 v19 ⊢
      execDispK (vsaModel live) N L Room inp Wp Φ ρ st' d sm' status aRet s R3 ret v8 v9 v18 v19 := by
  unfold execDispK
  iintro ⟨Hsl, HK⟩ %R' %hret Hpc Hra Hregs Hst Hret Hw
  ihave Hst := stackScratch_widen hsg.le hle $$ [Hsl Hst]
  · iframe Hsl Hst
  iapply HK $$ %R' %⟨hret.sp, hret.s0, hret.s1, hret.s2, hret.s3,
    fun x hx => (hret.hi x hx).trans (hk x hx), hret.a0⟩ Hpc Hra Hregs Hst Hret Hw

omit I in
/-- The parent's abort takes a re-dispatched child's, the slack joined back. -/
theorem abortAt_redispatch {Core : IProp GF} {s : BitVec 64} {n n' : Nat} (hn : n ≤ s.toNat)
    (hle : n' ≤ n) :
    blockOwn (GF := GF) (s.toNat - n) (n - n') ∗ abortAt Core s n' ⊢ abortAt Core s n := by
  unfold abortAt
  iintro ⟨Hsl, HC, Hst⟩
  iframe HC
  iapply stackScratch_widen hn hle $$ [Hsl Hst]
  iframe Hsl Hst

end Redispatch

section Redispatch2

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

/-- **The in-frame tail call**, for either WP: at the dispatch point with a
child statement `sm'` in `s0` (the parent's frame, spills and return address
kept), the child's dispatch-point spec (`hchild`, instantiated at these
registers and memory) proves the parent's goal; the parent's stack slack and
return continuation are handed through (`stack_redispatch`,
`execDispK_redispatch`). -/
theorem ifRedispatch (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {ρ ρ' : Regime} {st1 st2 : St} {d env : Nat} {sm sm' : Stmt} {status : Status}
    {aS' aE aRet s ret v8 v9 v18 v19 : BitVec 64} {R R4 : Nat → BitVec 64} {M3 : Mem}
    (hsg : StackGeom s (execNeed sm d)) (hle : execNeed sm' d ≤ execNeed sm d)
    (hk : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R R4)
    (hchild : execDispPre N L Room inp ρ st1 d env sm' aS' aE aRet s R4 M3 ret v8 v9 v18 v19 ∗
      execDispK (vsaModel live) N L Room inp Wp Φ ρ' st2 d sm' status aRet s R4 ret v8 v9 v18 v19
      ⊢ Wp.W Φ)
    (hf : DispFacts inp st1 d sm' R4 M3 aS' aE aRet s ret v8 v9 v18 v19) :
    ms execDispPC R4 (InExt (s.toNat - 176, 176)) M3 ∗ codeRes ∗ □ astSG aS'.toNat sm' ∗
      □ frameAt env aE.toNat ∗ stackScratch (execSP s) (execNeed sm d - 176) ∗ slot24 aRet.toNat ∗
      world N L Room inp ρ st1 d ∗
      execDispK (vsaModel live) N L Room inp Wp Φ ρ' st2 d sm status aRet s R ret v8 v9 v18 v19
    ⊢ Wp.W Φ := by
  obtain ⟨hfg, h176⟩ := execFrameGeom_of hf.stack
  iintro ⟨Hms, #Hcode, #Hast, #Hfb, Hst, Hslot, Hw, HK⟩
  ihave ⟨Hsl, Hst⟩ := stack_redispatch hsg hle h176 hfg.sf $$ Hst
  ihave HK := execDispK_redispatch Wp hsg hle hk $$ [Hsl HK]
  · iframe Hsl HK
  iapply hchild
  unfold execDispPre
  iframe Hms Hcode Hast Hfb Hst Hslot Hw HK
  ipureintro; exact hf

/-- The partial continuation pair through an in-frame tail call: the child's
derivations become the parent's (`hE`), the slack joins the child's abort. -/
theorem execDispKP_redispatch {Φ : Nat × String → IProp GF} {Core : IProp GF}
    {st st1 : St} {d env : Nat} {sm sm' : Stmt} {aRet s ret v8 v9 v18 v19 : BitVec 64}
    {R R4 : Nat → BitVec 64}
    (hsg : StackGeom s (execNeed sm d)) (hle : execNeed sm' d ≤ execNeed sm d)
    (hk : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R R4)
    (hE : ∀ st'' status, ExecS st1 d env sm' st'' status → ExecS st d env sm st'' status) :
    blockOwn (GF := GF) (s.toNat - execNeed sm d) (execNeed sm d - execNeed sm' d) ∗
      ((∀ (st'' : St) (status : Status), ⌜ExecS st d env sm st'' status⌝ -∗
        execDispK (vsaModel live) N L Room inp (wpW (vsaModel live)) Φ .uncounted st'' d sm status
          aRet s R ret v8 v9 v18 v19) ∧
       (iprop(abortAt Core s (execNeed sm d) ∗ slot24 aRet.toNat) -∗ (wpW (vsaModel live)).W Φ)) ⊢
      ((∀ (st'' : St) (status : Status), ⌜ExecS st1 d env sm' st'' status⌝ -∗
        execDispK (vsaModel live) N L Room inp (wpW (vsaModel live)) Φ .uncounted st'' d sm' status
          aRet s R4 ret v8 v9 v18 v19) ∧
       (iprop(abortAt Core s (execNeed sm' d) ∗ slot24 aRet.toNat) -∗ (wpW (vsaModel live)).W Φ)) := by
  iintro ⟨Hsl, HK⟩
  isplit
  · iintro %st'' %status %hE'
    ihave HK := and_elim_l $$ HK
    ihave HK := HK $$ %st'' %status %(hE st'' status hE')
    iapply execDispK_redispatch (wpW _) hsg hle hk $$ [Hsl HK]
    iframe Hsl HK
  · iintro ⟨HA, Hslot⟩
    ihave HK := and_elim_r $$ HK
    iapply HK
    iframe Hslot
    iapply abortAt_redispatch hsg.le hle $$ [Hsl HA]
    iframe Hsl HA

end Redispatch2

end VsaIris.Interp
