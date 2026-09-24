import VsaIris.Interp.LoopWhile

/-!
# The `for` loop (lane E6), both modes

INTERP_DESIGN.md §4.3; statements in `SpecLoop.lean` (`execInitT_body`,
`forLoopT_body`, `forCondT_body`, `execStepT_body`, `forLoopP_body`,
`execInitP_body`). `exec_stmt`'s `for` arm after `env_new`:

```
8000423c ld a1,8(s0); mv s3,a0; beqz a1 → 8000426c     init (ExecInit)
80004248 … jal exec_stmt (80004254); j 8000426c
8000426c ld a2,16(s0); beqz a2 → 800042a8              condition (ForCond)
80004274 … jal eval_expr (80004280, slot sp+104)
80004284 copy to sp+16; jal value_truthy (800042a0); beqz a0 → 80004090
800042a8 ld a1,32(s0); … jal exec_stmt (800042b8)       body
800042bc bne a0,1 → 8000425c; li a0,0; j 8000409c       break
8000425c beq a0,3 → 80004150                           return
80004264 ld a2,24(s0); bnez a2 → 800042dc              step (ExecStep)
800042dc … jal eval_expr (800042e8, slot sp+16); j 8000426c
```

The runs' glue is WP-generic (`forStage*`, `forCopy`, `forRoute`, …); the
two modes differ only in the calls.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While

/-- The bytes of a `for` node a run reads: the init, condition, step and body
pointers. -/
abbrev forView (a : Nat) : List Nat := accAddrs (a + 8) 32

#ix_seg ForLoop_runInit {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s pI : BitVec 64}
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 40 ≤ 0x100000000)
    (hx3 : aS.toNat + 40 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (hi : ldv .ld m (aS + 8#64).toNat = pI) :
    IW live m (forView aS.toNat) (execS s) Q 0x8000423c#64 R Mt
  by ix_run hlive using [h8, hi] at 0x80004254 0x8000426c

#ix_seg ForLoop_runInitJoin {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64} :
    IW live m [] (execS s) Q 0x80004258#64 R Mt
  by ix_run hlive at 0x8000426c

#ix_seg ForLoop_runHead {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s pC : BitVec 64}
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 40 ≤ 0x100000000)
    (hx3 : aS.toNat + 40 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (h2 : R 2 = s + 18446744073709551440#64)
    (hc : ldv .ld m (aS + 16#64).toNat = pC) :
    IW live m (forView aS.toNat) (execS s) Q 0x8000426c#64 R Mt
  by ix_run hlive using [h8, h2, hc] at 0x80004280 0x800042a8

#ix_seg ForLoop_runCopy {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (h2 : R 2 = s + 18446744073709551440#64) :
    IW live m [] (execS s) Q 0x80004284#64 R Mt
  by ix_run hlive using [h2, hsf] at 0x800042a0

#ix_seg ForLoop_runBranch {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64} :
    IW live m [] (execS s) Q 0x800042a4#64 R Mt
  by ix_run hlive at 0x800042a8 0x8000409c

#ix_seg ForLoop_runBody {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s pB : BitVec 64}
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 40 ≤ 0x100000000)
    (hx3 : aS.toNat + 40 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (hb : ldv .ld m (aS + 32#64).toNat = pB) :
    IW live m (forView aS.toNat) (execS s) Q 0x800042a8#64 R Mt
  by ix_run hlive using [h8, hb] at 0x800042b8

#ix_seg ForLoop_runRoute {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64} :
    IW live m [] (execS s) Q 0x800042bc#64 R Mt
  by ix_run hlive at 0x8000409c 0x80004150 0x80004264

#ix_seg ForLoop_runStep {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s pE : BitVec 64}
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 40 ≤ 0x100000000)
    (hx3 : aS.toNat + 40 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (h2 : R 2 = s + 18446744073709551440#64)
    (he : ldv .ld m (aS + 24#64).toNat = pE) :
    IW live m (forView aS.toNat) (execS s) Q 0x80004264#64 R Mt
  by ix_run hlive using [h8, h2, he] at 0x800042e8 0x8000426c

#ix_seg ForLoop_runStepJoin {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64} :
    IW live m [] (execS s) Q 0x800042ec#64 R Mt
  by ix_run hlive at 0x8000426c

/-- An optional statement field's pointer: `0` for `none`. -/
def OptS (m : Mem) (P : Nat → Prop) (p : Nat) : Option Stmt → Prop
  | none => p = 0
  | some s => p ≠ 0 ∧ StmtReprWithin m P p s

/-- An optional expression field's pointer: `0` for `none`. -/
def OptE (m : Mem) (P : Nat → Prop) (p : Nat) : Option Expr → Prop
  | none => p = 0
  | some e => p ≠ 0 ∧ ExprReprWithin m P p e

/-- What a `for` node gives the runs: its four pointers, placement and view. -/
structure ForNode (m : Mem) (P : Nat → Prop) (aS pI pC pE pB : BitVec 64) : Prop where
  init : ldv .ld m (aS + 8#64).toNat = pI
  cond : ldv .ld m (aS + 16#64).toNat = pC
  step : ldv .ld m (aS + 24#64).toNat = pE
  body : ldv .ld m (aS + 32#64).toNat = pB
  lo : 0x80000000 ≤ aS.toNat
  hi : aS.toNat + 40 ≤ 0x100000000
  off : aS.toNat + 40 ≤ Vsa.Sim.tohostAddr ∨ Vsa.Sim.tohostAddr + 16 ≤ aS.toNat
  view : ∀ a ∈ forView aS.toNat, P a ∧ (m[a]?).isSome

theorem readLE_of_optS {m : Mem} {P : Nat → Prop} {a : Nat} {o : Option Stmt}
    (h : OptStmtReprWithin m P a o) :
    ∃ p, read64 m a = some p ∧ Covers P a 8 ∧ OptS m P p o := by
  cases h with
  | none h c => exact ⟨0, h, c, rfl⟩
  | some h c hp hs => exact ⟨_, h, c, hp, hs⟩

theorem readLE_of_optE {m : Mem} {P : Nat → Prop} {a : Nat} {o : Option Expr}
    (h : OptExprReprWithin m P a o) :
    ∃ p, read64 m a = some p ∧ Covers P a 8 ∧ OptE m P p o := by
  cases h with
  | none h c => exact ⟨0, h, c, rfl⟩
  | some h c hp he => exact ⟨_, h, c, hp, he⟩

/-- A `for` node's facts, from its representation over a geometric view. -/
theorem forNode_of_repr {m : Mem} {P : Nat → Prop} {aS : BitVec 64} {init : Option Stmt}
    {cnd step : Option Expr} {b : Stmt}
    (h : StmtReprWithin m P aS.toNat (.forStmt init cnd step b)) (hg : ∀ k, P k → ReadOK k) :
    ∃ pi pc pe pb : Nat, ForNode m P aS (BitVec.ofNat 64 pi) (BitVec.ofNat 64 pc)
        (BitVec.ofNat 64 pe) (BitVec.ofNat 64 pb) ∧
      OptS m P pi init ∧ OptE m P pc cnd ∧ OptE m P pe step ∧ StmtReprWithin m P pb b ∧
      pi < 2 ^ 64 ∧ pc < 2 ^ 64 ∧ pe < 2 ^ 64 ∧ pb < 2 ^ 64 := by
  cases h with
  | forS h5 c5 hI hC hE hb cb hrb =>
    rename_i pb
    obtain ⟨pi, hi, ci, oi⟩ := readLE_of_optS hI
    obtain ⟨pc, hc, cc, oc⟩ := readLE_of_optE hC
    obtain ⟨pe, he, ce, oe⟩ := readLE_of_optE hE
    have g0 := hg _ (c5 0 (by omega)); have g3 := hg _ (c5 3 (by omega))
    have g8 := hg _ (ci 0 (by omega)); have g39 := hg _ (cb 7 (by omega))
    have e : ∀ k, k < 40 → (aS + BitVec.ofNat 64 k).toNat = aS.toNat + k := fun k hk => by
      have := g39.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    refine ⟨pi, pc, pe, pb, ⟨?_, ?_, ?_, ?_, g0.lo, ?_, ?_, ?_⟩, oi, oc, oe, hrb,
      readLE_lt hi, readLE_lt hc, readLE_lt he, readLE_lt hb⟩
    · rw [e 8 (by omega)]; exact ldv_ld_read64 hi
    · rw [e 16 (by omega)]; exact ldv_ld_read64 hc
    · rw [e 24 (by omega)]; exact ldv_ld_read64 he
    · rw [e 32 (by omega)]; exact ldv_ld_read64 hb
    · have := g39.hi; simp only [Nat.add_zero] at *; omega
    · have h0 := g0.off; have h3 := g3.off; have h8' := g8.off; have h39 := g39.off
      have h15 := (hg _ (ci 7 (by omega))).off; have h16 := (hg _ (cc 0 (by omega))).off
      have h23 := (hg _ (cc 7 (by omega))).off; have h24 := (hg _ (ce 0 (by omega))).off
      have h31 := (hg _ (ce 7 (by omega))).off; have h32 := (hg _ (cb 0 (by omega))).off
      simp only [Nat.add_zero] at *; omega
    · intro a ha
      simp only [mem_accAddrs_iff] at ha
      by_cases j1 : a < aS.toNat + 16
      · obtain ⟨j, rfl⟩ : ∃ j, a = aS.toNat + 8 + j := ⟨a - (aS.toNat + 8), by omega⟩
        exact ⟨ci j (by omega), isSome_of_readLE hi (by omega)⟩
      by_cases j2 : a < aS.toNat + 24
      · obtain ⟨j, rfl⟩ : ∃ j, a = aS.toNat + 16 + j := ⟨a - (aS.toNat + 16), by omega⟩
        exact ⟨cc j (by omega), isSome_of_readLE hc (by omega)⟩
      by_cases j3 : a < aS.toNat + 32
      · obtain ⟨j, rfl⟩ : ∃ j, a = aS.toNat + 24 + j := ⟨a - (aS.toNat + 24), by omega⟩
        exact ⟨ce j (by omega), isSome_of_readLE he (by omega)⟩
      · obtain ⟨j, rfl⟩ : ∃ j, a = aS.toNat + 32 + j := ⟨a - (aS.toNat + 32), by omega⟩
        exact ⟨cb j (by omega), isSome_of_readLE hb (by omega)⟩

theorem ofNat_toNat_lt {p : Nat} (h : p < 2 ^ 64) : (BitVec.ofNat 64 p).toNat = p := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ofNat_ne_zero {p : Nat} (h : p < 2 ^ 64) (hp : p ≠ 0) : BitVec.ofNat 64 p ≠ 0#64 :=
  fun e => hp (by have := congrArg BitVec.toNat e; rwa [ofNat_toNat_lt h] at this)

/-- Where the `for` loop goes after its body returned `status`: out on
`break` (`a0 = 0`) or a returned value, to the step otherwise. -/
def forNext : Status → BitVec 64
  | .brk => 0x8000409c#64
  | .ret _ => 0x80004150#64
  | _ => 0x80004264#64

/-! ## The runs' glue, for either WP -/

section Glue

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr
variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {inp : Nat}

omit I in
/-- **Init, absent**: `beqz a1` straight to the loop head, the scope in `s3`. -/
theorem forInitNone (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {Φ : Nat × String → IProp GF} {cnd step : Option Expr} {b : Stmt}
    {aS aOuter aRet s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (hh : InitHead R s aS (BitVec.ofNat 64 inp) aRet aOuter) :
    ms 0x8000423c#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.forStmt none cnd step b) ∗
      (∀ R' : Nat → BitVec 64, ⌜KeepRegs initKeep R R' ∧ R' 19 = aOuter⌝ -∗
        ms 0x8000426c#64 R' (execS s) Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, Hk⟩
  ihave ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩ := astSG_elim _ _ $$ Hast
  obtain ⟨pi, pc, pe, pb, hn, hoi, -, -, -, -, -, -, -⟩ := forNode_of_repr hrepr hgeo
  simp only [OptS] at hoi; subst hoi
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(∀ R' : Nat → BitVec 64, ⌜KeepRegs initKeep R R' ∧ R' 19 = aOuter⌝ -∗
        ms 0x8000426c#64 R' (execS s) Mt -∗ Wp.W Φ))
  rotate_left
  · iframe Hdv Hms; iexact Hk
  intro F'
  refine ForLoop_runInit (s := s) hlive hn.lo hn.hi hn.off hh.s0 hn.init ?_ (fun h => absurd rfl h)
  intro _
  intros
  apply swp_closeF
  unfold F'
  iintro ⟨Hk, Hms⟩
  iapply Hk $$ %_ %⟨by keep_upd, by ix_reg; exact hh.a0⟩ Hms

omit I in
/-- **Init, present**: stage the init's `jal exec_stmt` (`0x80004254`) in the
loop scope, the scope in `s3`. -/
theorem forInitStage (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {Φ : Nat × String → IProp GF} {i : Stmt} {cnd step : Option Expr} {b : Stmt}
    {aS aOuter aRet s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (hh : InitHead R s aS (BitVec.ofNat 64 inp) aRet aOuter) :
    ms 0x8000423c#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.forStmt (some i) cnd step b) ∗
      (∀ (R1 : Nat → BitVec 64) (aI : BitVec 64),
        ⌜ExecRegs R1 (BitVec.ofNat 64 inp) aI aOuter aRet (s + 18446744073709551440#64) ∧
          KeepRegs initKeep R R1 ∧ R1 19 = aOuter⌝ -∗
        □ astSG aI.toNat i -∗ ms 0x80004254#64 R1 (execS s) Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, Hk⟩
  ihave ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩ := astSG_elim _ _ $$ Hast
  obtain ⟨pi, pc, pe, pb, hn, ⟨hpi0, hri⟩, -, -, -, hpi, -, -, -⟩ := forNode_of_repr hrepr hgeo
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(roOn P m ∗ (∀ (R1 : Nat → BitVec 64) (aI : BitVec 64),
        ⌜ExecRegs R1 (BitVec.ofNat 64 inp) aI aOuter aRet (s + 18446744073709551440#64) ∧
          KeepRegs initKeep R R1 ∧ R1 19 = aOuter⌝ -∗
        □ astSG aI.toNat i -∗ ms 0x80004254#64 R1 (execS s) Mt -∗ Wp.W Φ)))
  rotate_left
  · iframe Hdv Hms Hro; iexact Hk
  intro F'
  refine ForLoop_runInit (s := s) hlive hn.lo hn.hi hn.off hh.s0 hn.init
    (fun h => absurd (by simpa [upd_apply] using h) (ofNat_ne_zero hpi hpi0)) ?_
  intro _
  intros
  apply swp_closeF
  unfold F'
  iintro ⟨⟨#Hro, Hk⟩, Hms⟩
  iapply Hk $$ %_ %(BitVec.ofNat 64 pi) %⟨⟨by ix_reg; exact hh.s1, by ix_reg, by ix_reg; exact hh.a0,
    by ix_reg; exact hh.s2, by ix_reg; exact hh.sp⟩, by keep_upd, by ix_reg; exact hh.a0⟩ [] Hms
  imodintro; rw [ofNat_toNat_lt hpi]; iapply astSG_of_view hri hgeo $$ Hro

omit I in
/-- **A jump to the loop head** from a call's return (`j 8000426c` after the
init and after the step). -/
theorem forJoin (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {Φ : Nat × String → IProp GF} {j : Nat} (hj : j = 0x80004254 ∨ j = 0x800042e8)
    {s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} :
    ms (BitVec.ofNat 64 (j + 4)) R (execS s) Mt ∗ codeRes ∗
      (ms 0x8000426c#64 R (execS s) Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hms, #Hcode, Hk⟩
  ihave #Hdv := roOwn_code (m := Mt) $$ Hcode
  iapply wp_swpF Wp (F := iprop(ms 0x8000426c#64 R (execS s) Mt -∗ Wp.W Φ))
  rotate_left
  · iframe Hdv Hms; iexact Hk
  intro F'
  rcases hj with rfl | rfl
  · refine ForLoop_runInitJoin hlive ?_
    apply swp_closeF; unfold F'; iintro ⟨Hk, Hms⟩; iapply Hk $$ Hms
  · refine ForLoop_runStepJoin hlive ?_
    apply swp_closeF; unfold F'; iintro ⟨Hk, Hms⟩; iapply Hk $$ Hms

omit I in
/-- **Condition, absent**: `beqz a2` to the body's staging `0x800042a8`. -/
theorem forCondNone (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {Φ : Nat × String → IProp GF} {init : Option Stmt} {step : Option Expr} {b : Stmt}
    {aS aEnv aRet s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (hh : StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv) :
    ms 0x8000426c#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.forStmt init none step b) ∗
      (∀ R' : Nat → BitVec 64, ⌜KeepRegs calleeSaved R R'⌝ -∗
        ms 0x800042a8#64 R' (execS s) Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, Hk⟩
  ihave ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩ := astSG_elim _ _ $$ Hast
  obtain ⟨pi, pc, pe, pb, hn, -, hoc, -, -, -, -, -, -⟩ := forNode_of_repr hrepr hgeo
  simp only [OptE] at hoc; subst hoc
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(∀ R' : Nat → BitVec 64, ⌜KeepRegs calleeSaved R R'⌝ -∗
        ms 0x800042a8#64 R' (execS s) Mt -∗ Wp.W Φ))
  rotate_left
  · iframe Hdv Hms; iexact Hk
  intro F'
  refine ForLoop_runHead (s := s) hlive hn.lo hn.hi hn.off hh.s0 hh.sp hn.cond ?_
    (fun h => absurd rfl h)
  intro _
  intros
  apply swp_closeF
  unfold F'
  iintro ⟨Hk, Hms⟩
  iapply Hk $$ %_ %(by keep_upd) Hms

omit I in
/-- **Condition, present**: stage its `jal eval_expr` (`0x80004280`, slot
`sp+104`). -/
theorem forCondStage (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {Φ : Nat × String → IProp GF} {init : Option Stmt} {c : Expr} {step : Option Expr} {b : Stmt}
    {aS aEnv aRet s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (hh : StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv) :
    ms 0x8000426c#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.forStmt init (some c) step b) ∗
      (∀ (R1 : Nat → BitVec 64) (aC : BitVec 64),
        ⌜EvalRegs R1 (s + 18446744073709551440#64 + 104#64) (BitVec.ofNat 64 inp) aC aEnv
            (s + 18446744073709551440#64) ∧ KeepRegs calleeSaved R R1⌝ -∗
        □ astEG aC.toNat c -∗ ms 0x80004280#64 R1 (execS s) Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, Hk⟩
  ihave ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩ := astSG_elim _ _ $$ Hast
  obtain ⟨pi, pc, pe, pb, hn, -, ⟨hpc0, hrc⟩, -, -, -, hpc, -, -⟩ := forNode_of_repr hrepr hgeo
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(roOn P m ∗ (∀ (R1 : Nat → BitVec 64) (aC : BitVec 64),
        ⌜EvalRegs R1 (s + 18446744073709551440#64 + 104#64) (BitVec.ofNat 64 inp) aC aEnv
            (s + 18446744073709551440#64) ∧ KeepRegs calleeSaved R R1⌝ -∗
        □ astEG aC.toNat c -∗ ms 0x80004280#64 R1 (execS s) Mt -∗ Wp.W Φ)))
  rotate_left
  · iframe Hdv Hms Hro; iexact Hk
  intro F'
  refine ForLoop_runHead (s := s) hlive hn.lo hn.hi hn.off hh.s0 hh.sp hn.cond
    (fun h => absurd (by simpa using h) (ofNat_ne_zero hpc hpc0)) ?_
  intro _
  intros
  apply swp_closeF
  unfold F'
  iintro ⟨⟨#Hro, Hk⟩, Hms⟩
  iapply Hk $$ %_ %(BitVec.ofNat 64 pc) %⟨⟨by ix_reg, by ix_reg; exact hh.s1, by ix_reg,
    by ix_reg; exact hh.s3, by ix_reg; exact hh.sp⟩, by keep_upd⟩ [] Hms
  imodintro; rw [ofNat_toNat_lt hpc]; iapply astEG_of_view hrc hgeo $$ Hro

/-- **The condition's copy and `value_truthy`**: from the condition's return
(its words in `sp+104`, meaning `v`), the copy to `sp+16` and the helper;
the truthiness bit in `a0` at `0x800042a4`. -/
theorem forCopy (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    (htr : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N Wp p v)
    {Φ : Nat × String → IProp GF} {v : Value} {w0 w1 w2 : BitVec 64} {s : BitVec 64}
    {R : Nat → BitVec 64} {Mt : Mem} (hfg : ExecFrameGeom s) (hsp : R 2 = s + 18446744073709551440#64) :
    ms (BitVec.ofNat 64 (0x80004280 + 4)) R (execS s)
        (slotWrite Mt (s + 18446744073709551440#64 + 104#64).toNat w0 w1 w2) ∗ codeRes ∗
      □ valOf N v w0 w1 w2 ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = (if v.truthy then 1#64 else 0#64) ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms 0x800042a4#64 R' (execS s) Mt' -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hms, #Hcode, #Hv, Hk⟩
  have hs104 := execSlot hfg (o := 104) (by omega) rfl
  have hs16 := execSlot hfg (o := 16) (by omega) rfl
  have hoff := execSP_off hfg
  ihave #Hdv := roOwn_code (m := Mt) $$ Hcode
  iapply wp_swpF Wp (F := iprop(codeRes ∗ □ valOf N v w0 w1 w2 ∗ ∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = (if v.truthy then 1#64 else 0#64) ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms 0x800042a4#64 R' (execS s) Mt' -∗ Wp.W Φ))
  rotate_left
  · iframe Hdv Hms Hcode Hv; iexact Hk
  intro F'
  refine ForLoop_runCopy hlive hfg.sf hfg.lo hfg.hi hfg.al hsp ?_
  intros
  apply swp_closeRM
  intro R3 Mt3 hR3 hMt3
  unfold F'
  iintro ⟨⟨#Hcode, #Hv, Hk⟩, Hms⟩
  have e0 : imgW (imgM Mt3) (s + 18446744073709551440#64 + 16#64).toNat = w0 := by
    rw [← ldv_ld_imgW, hMt3]; ix_fwd using [hoff]
  have e8 : imgW (imgM Mt3) ((s + 18446744073709551440#64 + 16#64).toNat + 8) = w1 := by
    rw [← ldv_ld_imgW, hMt3]; ix_fwd using [hoff]
  have e16 : imgW (imgM Mt3) ((s + 18446744073709551440#64 + 16#64).toNat + 16) = w2 := by
    rw [← ldv_ld_imgW, hMt3]; ix_fwd using [hoff]
  ihave Ht := htr $$ %(s + 18446744073709551440#64 + 16#64) %v
  iapply ms_truthyCall Wp (N := N) (R := R3) (Mt := Mt3) (v := v) (i := 0x800042a0)
    (jalx_800042a0 live (fun p hp => hlive _ (interp_code_800042a0 p hp)))
    interp_code_800042a0 (by decide) (execSlot_in hs16 (by omega)) (by rw [hR3]; ix_reg) hs16.geo
  iframe Ht Hcode Hms
  isplitl []
  · imodintro; unfold valImg; rw [e0, e8, e16]; iexact Hv
  iintro %R4 %Mt4 %⟨hkeep4, htr4, hag4⟩ Hms
  iapply Hk $$ %_ %Mt4 %⟨?_, by ix_reg; exact htr4, ?_⟩ Hms
  · refine KeepRegs.upd_right (KeepRegs.trans ?_ (KeepRegs.of_helper hkeep4 (by decide))) (by decide) _
    rw [hR3]; keep_upd
  · refine Untouched.trans (Untouched.slotWrite hs104 (by omega) (by omega) Mt w0 w1 w2) ?_
    refine Untouched.trans ?_
      (fun a ha hw => hag4 a ha fun hin => hw (execSlot_W hs16 (Nat.le_refl _) (by omega) a hin))
    rw [hMt3]
    exact Untouched.trans (Untouched.trans (Untouched.store hfg (o := 16) (Nat.le_refl _) (by omega) _ _)
      (Untouched.store hfg (o := 24) (by omega) (by omega) _ _))
      (Untouched.store hfg (o := 32) (by omega) (by omega) _ _)

omit I in
/-- **The condition's branch**: false leaves normally (`a0 = 0`), true goes
to the body's staging. -/
theorem forBranch (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {Φ : Nat × String → IProp GF} {s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} :
    ms 0x800042a4#64 R (execS s) Mt ∗ codeRes ∗
      ((⌜R 10 = 0#64⌝ -∗ ms 0x8000409c#64 (upd R 10 0#64) (execS s) Mt -∗ Wp.W Φ) ∧
        (⌜R 10 ≠ 0#64⌝ -∗ ms 0x800042a8#64 R (execS s) Mt -∗ Wp.W Φ))
    ⊢ Wp.W Φ := by
  iintro ⟨Hms, #Hcode, Hk⟩
  ihave #Hdv := roOwn_code (m := Mt) $$ Hcode
  by_cases h10 : R 10 = 0#64
  · ihave Hk := and_elim_l $$ Hk
    iapply wp_swpF Wp (F := iprop(⌜R 10 = 0#64⌝ -∗ ms 0x8000409c#64 (upd R 10 0#64) (execS s) Mt -∗ Wp.W Φ))
    rotate_left
    · iframe Hdv Hms; iexact Hk
    intro F'
    refine ForLoop_runBranch hlive ?_ (fun h => absurd h10 h)
    intro _
    intros
    apply swp_closeF
    unfold F'
    iintro ⟨Hk, Hms⟩
    iapply Hk $$ %h10 Hms
  · ihave Hk := and_elim_r $$ Hk
    iapply wp_swpF Wp (F := iprop(⌜R 10 ≠ 0#64⌝ -∗ ms 0x800042a8#64 R (execS s) Mt -∗ Wp.W Φ))
    rotate_left
    · iframe Hdv Hms; iexact Hk
    intro F'
    refine ForLoop_runBranch hlive (fun h => absurd h h10) ?_
    intro _
    intros
    apply swp_closeF
    unfold F'
    iintro ⟨Hk, Hms⟩
    iapply Hk $$ %h10 Hms

omit I in
/-- **The body's staging**: its `jal exec_stmt` (`0x800042b8`) in the loop
scope with the arm's own `ret` slot. -/
theorem forStageBody (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {Φ : Nat × String → IProp GF} {init : Option Stmt} {cnd step : Option Expr} {b : Stmt}
    {aS aEnv aRet s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (hh : StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv) :
    ms 0x800042a8#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.forStmt init cnd step b) ∗
      (∀ (R1 : Nat → BitVec 64) (aB : BitVec 64),
        ⌜ExecRegs R1 (BitVec.ofNat 64 inp) aB aEnv aRet (s + 18446744073709551440#64) ∧
          KeepRegs calleeSaved R R1⌝ -∗
        □ astSG aB.toNat b -∗ ms 0x800042b8#64 R1 (execS s) Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, Hk⟩
  ihave ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩ := astSG_elim _ _ $$ Hast
  obtain ⟨pi, pc, pe, pb, hn, -, -, -, hrb, -, -, -, hpb⟩ := forNode_of_repr hrepr hgeo
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(roOn P m ∗ (∀ (R1 : Nat → BitVec 64) (aB : BitVec 64),
        ⌜ExecRegs R1 (BitVec.ofNat 64 inp) aB aEnv aRet (s + 18446744073709551440#64) ∧
          KeepRegs calleeSaved R R1⌝ -∗
        □ astSG aB.toNat b -∗ ms 0x800042b8#64 R1 (execS s) Mt -∗ Wp.W Φ)))
  rotate_left
  · iframe Hdv Hms Hro; iexact Hk
  intro F'
  refine ForLoop_runBody (s := s) hlive hn.lo hn.hi hn.off hh.s0 hn.body ?_
  intros
  apply swp_closeF
  unfold F'
  iintro ⟨⟨#Hro, Hk⟩, Hms⟩
  iapply Hk $$ %_ %(BitVec.ofNat 64 pb) %⟨⟨by ix_reg; exact hh.s1, by ix_reg, by ix_reg; exact hh.s3,
    by ix_reg; exact hh.s2, by ix_reg; exact hh.sp⟩, by keep_upd⟩ [] Hms
  imodintro; rw [ofNat_toNat_lt hpb]; iapply astSG_of_view hrb hgeo $$ Hro

omit I in
/-- **The status routing** (`bne a0,1`, `beq a0,3`) after the body returned
`status` in `a0`. -/
theorem forRoute (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {Φ : Nat × String → IProp GF} {status : Status} {s : BitVec 64}
    {R : Nat → BitVec 64} {Mt : Mem} (h10 : R 10 = statusCode status) :
    ms (BitVec.ofNat 64 (0x800042b8 + 4)) R (execS s) Mt ∗ codeRes ∗
      (∀ R' : Nat → BitVec 64, ⌜KeepRegs calleeSaved R R' ∧ R' 10 = whileA0 status⌝ -∗
        ms (forNext status) R' (execS s) Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hms, #Hcode, Hk⟩
  ihave #Hdv := roOwn_code (m := Mt) $$ Hcode
  iapply wp_swpF Wp (F := iprop(∀ R' : Nat → BitVec 64,
      ⌜KeepRegs calleeSaved R R' ∧ R' 10 = whileA0 status⌝ -∗
        ms (forNext status) R' (execS s) Mt -∗ Wp.W Φ))
  rotate_left
  · iframe Hdv Hms; iexact Hk
  intro F'
  refine ForLoop_runRoute (s := s) hlive ?_ ?_ ?_
  · intro _ hc3
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc3
    intros
    apply swp_closeF
    unfold F'
    cases status with
    | ret rv =>
      simp only [forNext, whileA0]
      iintro ⟨Hk, Hms⟩
      iapply Hk $$ %_ %⟨by keep_upd, by ix_reg; exact h10⟩ Hms
    | _ => exfalso; rw [h10] at hc3; simp [statusCode] at hc3
  · intro h1 hc3
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc3 h1
    intros
    apply swp_closeF
    unfold F'
    cases status with
    | normal | cont =>
      simp only [forNext, whileA0]
      iintro ⟨Hk, Hms⟩
      iapply Hk $$ %_ %⟨by keep_upd, by ix_reg; exact h10⟩ Hms
    | brk => exfalso; exact h1 h10
    | ret _ => exfalso; exact hc3 h10
  · intro h1
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, Decidable.not_not] at h1
    intros
    apply swp_closeF
    unfold F'
    cases status with
    | brk =>
      simp only [forNext, whileA0]
      iintro ⟨Hk, Hms⟩
      iapply Hk $$ %_ %⟨by keep_upd, by ix_reg⟩ Hms
    | _ => exfalso; rw [h10] at h1; simp [statusCode] at h1

omit I in
/-- **Step, absent**: `bnez a2` falls through to the loop head. -/
theorem forStepNone (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {Φ : Nat × String → IProp GF} {init : Option Stmt} {cnd : Option Expr} {b : Stmt}
    {aS aEnv aRet s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (hh : StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv) :
    ms 0x80004264#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.forStmt init cnd none b) ∗
      (∀ R' : Nat → BitVec 64, ⌜KeepRegs calleeSaved R R'⌝ -∗
        ms 0x8000426c#64 R' (execS s) Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, Hk⟩
  ihave ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩ := astSG_elim _ _ $$ Hast
  obtain ⟨pi, pc, pe, pb, hn, -, -, hoe, -, -, -, -, -⟩ := forNode_of_repr hrepr hgeo
  simp only [OptE] at hoe; subst hoe
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(∀ R' : Nat → BitVec 64, ⌜KeepRegs calleeSaved R R'⌝ -∗
        ms 0x8000426c#64 R' (execS s) Mt -∗ Wp.W Φ))
  rotate_left
  · iframe Hdv Hms; iexact Hk
  intro F'
  refine ForLoop_runStep (s := s) hlive hn.lo hn.hi hn.off hh.s0 hh.sp hn.step
    (fun h => absurd rfl h) ?_
  intro _
  intros
  apply swp_closeF
  unfold F'
  iintro ⟨Hk, Hms⟩
  iapply Hk $$ %_ %(by keep_upd) Hms

omit I in
/-- **Step, present**: stage its `jal eval_expr` (`0x800042e8`, slot
`sp+16`). -/
theorem forStepStage (Wp : MachWP (GF := GF) (vsaModel live)) (hlive : ∀ p ∈ interpText, live p.1)
    {Φ : Nat × String → IProp GF} {init : Option Stmt} {cnd : Option Expr} {e : Expr} {b : Stmt}
    {aS aEnv aRet s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (hh : StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv) :
    ms 0x80004264#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.forStmt init cnd (some e) b) ∗
      (∀ (R1 : Nat → BitVec 64) (aE : BitVec 64),
        ⌜EvalRegs R1 (s + 18446744073709551440#64 + 16#64) (BitVec.ofNat 64 inp) aE aEnv
            (s + 18446744073709551440#64) ∧ KeepRegs calleeSaved R R1⌝ -∗
        □ astEG aE.toNat e -∗ ms 0x800042e8#64 R1 (execS s) Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, Hk⟩
  ihave ⟨%P, %m, %⟨hrepr, hgeo⟩, #Hro⟩ := astSG_elim _ _ $$ Hast
  obtain ⟨pi, pc, pe, pb, hn, -, -, ⟨hpe0, hre⟩, -, -, -, hpe, -⟩ := forNode_of_repr hrepr hgeo
  ihave #Hdv := roOwn_data hn.view $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(roOn P m ∗ (∀ (R1 : Nat → BitVec 64) (aE : BitVec 64),
        ⌜EvalRegs R1 (s + 18446744073709551440#64 + 16#64) (BitVec.ofNat 64 inp) aE aEnv
            (s + 18446744073709551440#64) ∧ KeepRegs calleeSaved R R1⌝ -∗
        □ astEG aE.toNat e -∗ ms 0x800042e8#64 R1 (execS s) Mt -∗ Wp.W Φ)))
  rotate_left
  · iframe Hdv Hms Hro; iexact Hk
  intro F'
  refine ForLoop_runStep (s := s) hlive hn.lo hn.hi hn.off hh.s0 hh.sp hn.step ?_
    (fun h => absurd (by simpa using h) (ofNat_ne_zero hpe hpe0))
  intro _
  intros
  apply swp_closeF
  unfold F'
  iintro ⟨⟨#Hro, Hk⟩, Hms⟩
  iapply Hk $$ %_ %(BitVec.ofNat 64 pe) %⟨⟨by ix_reg, by ix_reg; exact hh.s1, by ix_reg,
    by ix_reg; exact hh.s3, by ix_reg; exact hh.sp⟩, by keep_upd⟩ [] Hms
  imodintro; rw [ofNat_toNat_lt hpe]; iapply astEG_of_view hre hgeo $$ Hro

end Glue

-- @@REST@@
end VsaIris.Interp
