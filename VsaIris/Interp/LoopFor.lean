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

/-! ## Total mode -/

section Total

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr
variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

/-- **The condition's evaluation, total mode**: from the loop head with a
present condition, its derivation `Dc`, the copy and `value_truthy`; the
truthiness bit in `a0` at the branch `0x800042a4`. -/
theorem forCondEvalT (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    {st : St} {d env : Nat} {init : Option Stmt} {c : Expr} {step : Option Expr} {b : Stmt}
    {st' : St} {v : Value} {nc k : Nat}
    (Dc : EvalECost st d env c st' v nc)
    (hc : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env c st' v nc Dc)
    (htr : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p v)
    {aS aEnv aRet s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} {m' : Nat}
    (hh : StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv) (hfg : ExecFrameGeom s)
    (hsg : StackGeom (s + 18446744073709551440#64) m') (hfit : evalNeed c d ≤ m')
    (hcb : c.bodiesBound perCallBudget = true) :
    ms 0x8000426c#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.forStmt init (some c) step b) ∗
      □ frameAt env aEnv.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      world N L Room inp (.counted (k + nc)) st d ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = (if v.truthy then 1#64 else 0#64) ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms 0x800042a4#64 R' (execS s) Mt' -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        world N L Room inp (.counted k) st' d -∗ (twpW (vsaModel live)).W Φ)
    ⊢ (twpW (vsaModel live)).W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hw, Hk⟩
  iapply forCondStage (twpW _) hlive hh
  iframe Hms Hcode Hast
  iintro %R1 %aC %⟨hregs, hk1⟩ #Hac Hms
  ihave Hc := hc
  iapply ms_callEvalT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x80004280)
    (jalx_80004280 live (fun p hp => hlive _ (interp_code_80004280 p hp)))
    interp_code_80004280 (by decide) Dc (k := k) (hsg.narrow hfit) hfit hsg.le
    (execSlot hfg (o := 104) (by omega) rfl).geo hcb
  iframe Hc Hcode Hac Hfr Hms Hst Hw
  isplitl []
  · ipureintro; exact ⟨hregs, execSlot_in (execSlot hfg (o := 104) (by omega) rfl) (by omega)⟩
  iintro %R2 %w0 %w1 %w2 %hk2 #Hv Hms Hst Hw
  iapply forCopy (twpW _) (R := upd R2 1 (BitVec.ofNat 64 (0x80004280 + 4))) hlive htr hfg
    (by ix_reg; rw [keep_reg hk2 (by decide)]; exact hregs.sp)
  iframe Hms Hcode Hv
  iintro %R3 %Mt3 %⟨hk3, h30, hut⟩ Hms
  iapply Hk $$ %R3 %Mt3 %⟨KeepRegs.trans (KeepRegs.trans hk1 (hk2.calleeSaved_upd (by decide) _)) hk3,
    h30, hut⟩ Hms Hst Hw

/-- `ForCond.none`: no condition. -/
theorem forCondT_none (hlive : ∀ p ∈ interpText, live p.1) (st : St) (d env : Nat) :
    forCondT_body (GF := GF) live N L Room inp st d env none st 0 := by
  intro Φ k init step b aS aEnv aRet s R Mt m' hh _ _ _
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hw, Hk⟩
  iapply forCondNone (twpW _) hlive hh
  iframe Hms Hcode Hast
  iintro %R' %hk Hms
  iapply Hk $$ %R' %Mt %⟨hk, Untouched.refl _ _ _⟩ Hms Hst Hw

/-- `ForCond.some`: the condition holds. -/
theorem forCondT_some (hlive : ∀ p ∈ interpText, live p.1)
    {st : St} {d env : Nat} {c : Expr} {st' : St} {v : Value} {nc : Nat}
    (Dc : EvalECost st d env c st' v nc) (hv : v.truthy = true)
    (hc : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env c st' v nc Dc)
    (htr : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p v) :
    forCondT_body (GF := GF) live N L Room inp st d env (some c) st' nc := by
  intro Φ k init step b aS aEnv aRet s R Mt m' hh hfg hsg hfits
  obtain ⟨hfit, hcb⟩ := hfits.cond c rfl
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hw, Hk⟩
  iapply forCondEvalT hlive Dc hc htr hh hfg hsg hfit hcb
  iframe Hms Hcode Hast Hfr Hst Hw
  iintro %R1 %Mt1 %⟨hk1, h10, hut⟩ Hms Hst Hw
  rw [hv] at h10
  iapply forBranch (twpW _) hlive
  iframe Hms Hcode
  isplit
  · iintro %h Hms; exfalso; rw [h10] at h; exact absurd h (by decide)
  · iintro %_ Hms
    iapply Hk $$ %R1 %Mt1 %⟨hk1, hut⟩ Hms Hst Hw

/-- `ExecStep.none`: no step. -/
theorem execStepT_none (hlive : ∀ p ∈ interpText, live p.1) (st : St) (d env : Nat) :
    execStepT_body (GF := GF) live N L Room inp st d env none st 0 := by
  intro Φ k init cnd b aS aEnv aRet s R Mt m' hh _ _ _
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hw, Hk⟩
  iapply forStepNone (twpW _) hlive hh
  iframe Hms Hcode Hast
  iintro %R' %hk Hms
  iapply Hk $$ %R' %Mt %⟨hk, Untouched.refl _ _ _⟩ Hms Hst Hw

/-- `ExecStep.some`: the step expression, its value discarded. -/
theorem execStepT_some (hlive : ∀ p ∈ interpText, live p.1)
    {st : St} {d env : Nat} {e : Expr} {st' : St} {v : Value} {n : Nat}
    (De : EvalECost st d env e st' v n)
    (he : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env e st' v n De) :
    execStepT_body (GF := GF) live N L Room inp st d env (some e) st' n := by
  intro Φ k init cnd b aS aEnv aRet s R Mt m' hh hfg hsg hfits
  obtain ⟨hfit, heb⟩ := hfits.step e rfl
  have hs16 := execSlot hfg (o := 16) (by omega) rfl
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hw, Hk⟩
  iapply forStepStage (twpW _) hlive hh
  iframe Hms Hcode Hast
  iintro %R1 %aE %⟨hregs, hk1⟩ #Hae Hms
  ihave He := he
  iapply ms_callEvalT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x800042e8)
    (jalx_800042e8 live (fun p hp => hlive _ (interp_code_800042e8 p hp)))
    interp_code_800042e8 (by decide) De (k := k) (hsg.narrow hfit) hfit hsg.le hs16.geo heb
  iframe He Hcode Hae Hfr Hms Hst Hw
  isplitl []
  · ipureintro; exact ⟨hregs, execSlot_in hs16 (by omega)⟩
  iintro %R2 %w0 %w1 %w2 %hk2 #_ Hms Hst Hw
  iapply forJoin (twpW _) hlive (.inr rfl)
  iframe Hms Hcode
  iintro Hms
  iapply Hk $$ %_ %_ %⟨KeepRegs.trans hk1 (hk2.calleeSaved_upd (by decide) _),
    Untouched.slotWrite hs16 (Nat.le_refl _) (by omega) Mt w0 w1 w2⟩ Hms Hst Hw

/-- `ExecInit.none`: no init statement. -/
theorem execInitT_none (hlive : ∀ p ∈ interpText, live p.1) (st : St) (d outer : Nat) :
    execInitT_body (GF := GF) live N L Room inp st d outer none st 0 := by
  intro Φ k cnd step b aS aOuter aRet s R Mt m' hh _ _ _ _
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hslot, Hw, Hk⟩
  iapply forInitNone (twpW _) hlive hh
  iframe Hms Hcode Hast
  iintro %R' %hk Hms
  iapply Hk $$ %R' %hk Hms Hst Hslot Hw

/-- `ExecInit.some`: the init statement, its status discarded. -/
theorem execInitT_some (hlive : ∀ p ∈ interpText, live p.1)
    {st : St} {d outer : Nat} {i : Stmt} {st' : St} {status : Status} {n : Nat}
    (Di : ExecSCost st d outer i st' status n)
    (hi : ⊢ execSpecT_body (GF := GF) (vsaModel live) N L Room inp st d outer i st' status n Di) :
    execInitT_body (GF := GF) live N L Room inp st d outer (some i) st' n := by
  intro Φ k cnd step b aS aOuter aRet s R Mt m' hh _ hsg hfits hslg
  obtain ⟨hfit, hib⟩ := hfits i rfl
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hslot, Hw, Hk⟩
  iapply forInitStage (twpW _) hlive hh
  iframe Hms Hcode Hast
  iintro %R1 %aI %⟨hregs, hk1, h19⟩ #Hai Hms
  ihave Hi := hi
  iapply ms_callExecT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x80004254)
    (jalx_80004254 live (fun p hp => hlive _ (interp_code_80004254 p hp)))
    interp_code_80004254 (by decide) Di (k := k) (hsg.narrow hfit) hfit hsg.le hslg hib
  iframe Hi Hcode Hai Hfr Hms Hst Hslot Hw
  isplitl []
  · ipureintro; exact hregs
  iintro %R2 %⟨hk2, -⟩ Hms Hst Hret Hw
  ihave Hslot := statusRet_slot N _ status $$ Hret
  iapply forJoin (twpW _) hlive (.inl rfl)
  iframe Hms Hcode
  iintro Hms
  have hk2c : KeepRegs calleeSaved R1 (upd R2 1 (BitVec.ofNat 64 (0x80004254 + 4))) :=
    hk2.calleeSaved_upd (by decide) _
  iapply Hk $$ %_ %⟨KeepRegs.trans hk1 (KeepRegs.sub hk2c (by decide)),
    (hk2c 19 (by decide)).trans h19⟩ Hms Hst Hslot Hw

/-- **The body, total mode**: from the body's staging `0x800042a8`, the body
through `exec_stmt` (its derivation `Db`) and the status routing. -/
theorem forBodyT (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    {st : St} {d env : Nat} {init : Option Stmt} {cnd step : Option Expr} {b : Stmt} {st' : St}
    {status : Status} {nb k : Nat}
    (Db : ExecSCost st d env b st' status nb)
    (hb : ⊢ execSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env b st' status nb Db)
    {aS aEnv aRet s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} {m' : Nat}
    (hh : StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv)
    (hsg : StackGeom (s + 18446744073709551440#64) m') (hfit : execNeed b d ≤ m')
    (hbb : b.bodiesBound perCallBudget = true) (hslg : SlotGeom aRet) :
    ms 0x800042a8#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.forStmt init cnd step b) ∗
      □ frameAt env aEnv.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 aRet.toNat ∗ world N L Room inp (.counted (k + nb)) st d ∗
      (∀ R' : Nat → BitVec 64, ⌜KeepRegs calleeSaved R R' ∧ R' 10 = whileA0 status⌝ -∗
        ms (forNext status) R' (execS s) Mt -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        statusRet N aRet.toNat status -∗ world N L Room inp (.counted k) st' d -∗
        (twpW (vsaModel live)).W Φ)
    ⊢ (twpW (vsaModel live)).W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hslot, Hw, Hk⟩
  iapply forStageBody (twpW _) hlive hh
  iframe Hms Hcode Hast
  iintro %R1 %aB %⟨hregs, hk1⟩ #Hab Hms
  ihave Hb := hb
  iapply ms_callExecT (N := N) (L := L) (Room := Room) (inp := inp) (i := 0x800042b8)
    (jalx_800042b8 live (fun p hp => hlive _ (interp_code_800042b8 p hp)))
    interp_code_800042b8 (by decide) Db (k := k) (hsg.narrow hfit) hfit hsg.le hslg hbb
  iframe Hb Hcode Hab Hfr Hms Hst Hslot Hw
  isplitl []
  · ipureintro; exact hregs
  iintro %R2 %⟨hk2, h20⟩ Hms Hst Hret Hw
  iapply forRoute (twpW _) (R := upd R2 1 (BitVec.ofNat 64 (0x800042b8 + 4))) hlive
    (by ix_reg; exact h20)
  iframe Hms Hcode
  iintro %R3 %⟨hk3, h30⟩ Hms
  iapply Hk $$ %R3 %⟨KeepRegs.trans (KeepRegs.trans hk1 (hk2.calleeSaved_upd (by decide) _)) hk3,
    h30⟩ Hms Hst Hret Hw

/-- `ForLoop.condFalse`: the condition is false; the loop leaves normally. -/
theorem forLoopT_condFalse (hlive : ∀ p ∈ interpText, live p.1)
    {st : St} {d env : Nat} {c : Expr} {step : Option Expr} {b : Stmt} {st' : St} {v : Value}
    {nc : Nat} (Dc : EvalECost st d env c st' v nc) (hv : v.truthy = false)
    (hc : ⊢ evalSpecT_body (GF := GF) (vsaModel live) N L Room inp st d env c st' v nc Dc)
    (htr : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p v) :
    forLoopT_body (GF := GF) live N L Room inp st d env (some c) step b st' .normal nc := by
  intro Φ k init aS aEnv aRet s R Mt m' hh hfg hsg hfits hslg
  obtain ⟨hfit, hcb⟩ := hfits.cond c rfl
  simp only [loopExit, statusRet_normal]
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hslot, Hw, Hk⟩
  iapply forCondEvalT hlive Dc hc htr hh hfg hsg hfit hcb
  iframe Hms Hcode Hast Hfr Hst Hw
  iintro %R1 %Mt1 %⟨hk1, h10, hut⟩ Hms Hst Hw
  rw [hv] at h10
  iapply forBranch (twpW _) hlive
  iframe Hms Hcode
  isplit
  · iintro %_ Hms
    iapply Hk $$ %_ %Mt1 %⟨hk1.calleeSaved_upd (by decide) _, by ix_reg; rfl, hut⟩ Hms Hst Hslot Hw
  · iintro %h Hms; exfalso; exact h (by simpa using h10)

/-- `ForLoop.bodyBreak`: the body breaks; the loop leaves normally. -/
theorem forLoopT_bodyBreak (hlive : ∀ p ∈ interpText, live p.1)
    {st : St} {d env : Nat} {cnd step : Option Expr} {b : Stmt} {st' st'' : St} {nc nb : Nat}
    (hcond : forCondT_body (GF := GF) live N L Room inp st d env cnd st' nc)
    (Db : ExecSCost st' d env b st'' .brk nb)
    (hb : ⊢ execSpecT_body (GF := GF) (vsaModel live) N L Room inp st' d env b st'' .brk nb Db) :
    forLoopT_body (GF := GF) live N L Room inp st d env cnd step b st'' .normal (nc + nb) := by
  intro Φ k init aS aEnv aRet s R Mt m' hh hfg hsg hfits hslg
  rw [show k + (nc + nb) = k + nb + nc by omega]
  simp only [loopExit, statusRet_normal]
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hslot, Hw, Hk⟩
  iapply hcond Φ (k + nb) init step b aS aEnv aRet s R Mt m' hh hfg hsg hfits
  iframe Hms Hcode Hast Hfr Hst Hw
  iintro %R1 %Mt1 %⟨hk1, hut⟩ Hms Hst Hw
  iapply forBodyT hlive Db hb (hh.keep hk1) hsg hfits.body hfits.bodyB hslg
  iframe Hms Hcode Hast Hfr Hst Hslot Hw
  iintro %R2 %⟨hk2, h20⟩ Hms Hst Hret Hw
  simp only [forNext, whileA0, statusRet_brk]
  iapply Hk $$ %R2 %Mt1 %⟨KeepRegs.trans hk1 hk2, h20, hut⟩ Hms Hst Hret Hw

/-- `ForLoop.bodyRet`: the body returns a value; the loop leaves through the
`ret` epilogue. -/
theorem forLoopT_bodyRet (hlive : ∀ p ∈ interpText, live p.1)
    {st : St} {d env : Nat} {cnd step : Option Expr} {b : Stmt} {st' st'' : St} {rv : Value}
    {nc nb : Nat}
    (hcond : forCondT_body (GF := GF) live N L Room inp st d env cnd st' nc)
    (Db : ExecSCost st' d env b st'' (.ret rv) nb)
    (hb : ⊢ execSpecT_body (GF := GF) (vsaModel live) N L Room inp st' d env b st'' (.ret rv) nb Db) :
    forLoopT_body (GF := GF) live N L Room inp st d env cnd step b st'' (.ret rv) (nc + nb) := by
  intro Φ k init aS aEnv aRet s R Mt m' hh hfg hsg hfits hslg
  rw [show k + (nc + nb) = k + nb + nc by omega]
  simp only [loopExit]
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hslot, Hw, Hk⟩
  iapply hcond Φ (k + nb) init step b aS aEnv aRet s R Mt m' hh hfg hsg hfits
  iframe Hms Hcode Hast Hfr Hst Hw
  iintro %R1 %Mt1 %⟨hk1, hut⟩ Hms Hst Hw
  iapply forBodyT hlive Db hb (hh.keep hk1) hsg hfits.body hfits.bodyB hslg
  iframe Hms Hcode Hast Hfr Hst Hslot Hw
  iintro %R2 %⟨hk2, h20⟩ Hms Hst Hret Hw
  simp only [forNext, whileA0]
  iapply Hk $$ %R2 %Mt1 %⟨KeepRegs.trans hk1 hk2, h20, hut⟩ Hms Hst Hret Hw

/-- `ForLoop.loop`: the body completes normally or continues, the step runs,
and the loop runs again from the head (the motive of the recursive premise). -/
theorem forLoopT_loop (hlive : ∀ p ∈ interpText, live p.1)
    {st : St} {d env : Nat} {cnd step : Option Expr} {b : Stmt} {st₁ st₂ st₃ st₄ : St}
    {status status' : Status} {nc nb ns nr : Nat}
    (hcond : forCondT_body (GF := GF) live N L Room inp st d env cnd st₁ nc)
    (Db : ExecSCost st₁ d env b st₂ status nb) (hst : status = .normal ∨ status = .cont)
    (hb : ⊢ execSpecT_body (GF := GF) (vsaModel live) N L Room inp st₁ d env b st₂ status nb Db)
    (hstep : execStepT_body (GF := GF) live N L Room inp st₂ d env step st₃ ns)
    (hr : forLoopT_body (GF := GF) live N L Room inp st₃ d env cnd step b st₄ status' nr) :
    forLoopT_body (GF := GF) live N L Room inp st d env cnd step b st₄ status'
      (nc + nb + ns + nr) := by
  intro Φ k init aS aEnv aRet s R Mt m' hh hfg hsg hfits hslg
  rw [show k + (nc + nb + ns + nr) = k + nr + ns + nb + nc by omega]
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hslot, Hw, Hk⟩
  iapply hcond Φ (k + nr + ns + nb) init step b aS aEnv aRet s R Mt m' hh hfg hsg hfits
  iframe Hms Hcode Hast Hfr Hst Hw
  iintro %R1 %Mt1 %⟨hk1, hut1⟩ Hms Hst Hw
  iapply forBodyT hlive Db hb (hh.keep hk1) hsg hfits.body hfits.bodyB hslg
  iframe Hms Hcode Hast Hfr Hst Hslot Hw
  iintro %R2 %⟨hk2, -⟩ Hms Hst Hret Hw
  have hh2 := (hh.keep hk1).keep hk2
  rcases hst with rfl | rfl <;>
  · simp only [forNext, statusRet_normal, statusRet_cont]
    iapply hstep Φ (k + nr) init cnd b aS aEnv aRet s R2 Mt1 m' hh2 hfg hsg hfits
    iframe Hms Hcode Hast Hfr Hst Hw
    iintro %R3 %Mt3 %⟨hk3, hut3⟩ Hms Hst Hw
    iapply hr Φ k init aS aEnv aRet s R3 Mt3 m' (hh2.keep hk3) hfg hsg hfits hslg
    iframe Hms Hcode Hast Hfr Hst Hret Hw
    iintro %R4 %Mt4 %⟨hk4, h40, hut4⟩ Hms Hst Hret Hw
    iapply Hk $$ %R4 %Mt4 %⟨KeepRegs.trans (KeepRegs.trans (KeepRegs.trans hk1 hk2) hk3) hk4, h40,
      (hut1.trans hut3).trans hut4⟩ Hms Hst Hret Hw

end Total

/-! ## Partial mode -/

section Partial

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr
variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}

/-- **The condition's evaluation, partial mode** (`forCondEvalT` through the
Löb hypothesis). -/
theorem forCondEvalP (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    (htr : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p v)
    {Core K : IProp GF} {st : St} {d env : Nat} {init : Option Stmt} {c : Expr}
    {step : Option Expr} {b : Stmt}
    {aS aEnv aRet s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} {m' : Nat}
    (hh : StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv) (hfg : ExecFrameGeom s)
    (hsg : StackGeom (s + 18446744073709551440#64) m') (hfit : evalNeed c d ≤ m')
    (hcb : c.bodiesBound perCallBudget = true) :
    ms 0x8000426c#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.forStmt init (some c) step b) ∗
      □ frameAt env aEnv.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      world N L Room inp .uncounted st d ∗ evalSpecsP (vsaModel live) N L Room inp Core ∗
      (K ∧ (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ ownSet (execS s) byteAny) -∗
        (wpW (vsaModel live)).W Φ)) ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st' : St) (v : Value), ⌜EvalE st d env c st' v⌝ -∗
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = (if v.truthy then 1#64 else 0#64) ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms 0x800042a4#64 R' (execS s) Mt' -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        world N L Room inp .uncounted st' d -∗
        (K ∧ (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ ownSet (execS s) byteAny) -∗
          (wpW (vsaModel live)).W Φ)) -∗ (wpW (vsaModel live)).W Φ)
    ⊢ (wpW (vsaModel live)).W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hw, #HE, HK, Hk⟩
  iapply forCondStage (wpW _) hlive hh
  iframe Hms Hcode Hast
  iintro %R1 %aC %⟨hregs, hk1⟩ #Hac Hms
  ihave Hc := evalSpecsP_at (N := N) (L := L) (Room := Room) (inp := inp) Core st d env c $$ HE
  iapply ms_callEvalPx (N := N) (L := L) (Room := Room) (inp := inp) (X := iprop(emp)) (Kret := K)
    (i := 0x80004280) (jalx_80004280 live (fun p hp => hlive _ (interp_code_80004280 p hp)))
    interp_code_80004280 (by decide) (hsg.narrow hfit) hfit hsg.le
    (execSlot hfg (o := 104) (by omega) rfl).geo hcb
  iframe Hc Hcode Hac Hfr Hms Hst Hw HK
  isplitl []
  · ipureintro; exact ⟨hregs, execSlot_in (execSlot hfg (o := 104) (by omega) rfl) (by omega)⟩
  isplitl []
  · inext; iempintro
  iintro %R2 %w0 %w1 %w2 %st' %v %hE %hk2 #Hv Hms Hst Hw - HK
  iapply forCopy (wpW _) (R := upd R2 1 (BitVec.ofNat 64 (0x80004280 + 4))) hlive htr hfg
    (by ix_reg; rw [keep_reg hk2 (by decide)]; exact hregs.sp)
  iframe Hms Hcode Hv
  iintro %R3 %Mt3 %⟨hk3, h30, hut⟩ Hms
  iapply Hk $$ %R3 %Mt3 %st' %v %hE
    %⟨KeepRegs.trans (KeepRegs.trans hk1 (hk2.calleeSaved_upd (by decide) _)) hk3, h30, hut⟩
    Hms Hst Hw HK

/-- **The body, partial mode** (`forBodyT` through the Löb hypothesis); the
body's `jal` also strips the later of `X`. -/
theorem forBodyP (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    {Core K X : IProp GF} {st : St} {d env : Nat} {init : Option Stmt} {cnd step : Option Expr}
    {b : Stmt} {aS aEnv aRet s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} {m' : Nat}
    (hh : StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv)
    (hsg : StackGeom (s + 18446744073709551440#64) m') (hfit : execNeed b d ≤ m')
    (hbb : b.bodiesBound perCallBudget = true) (hslg : SlotGeom aRet) :
    ms 0x800042a8#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.forStmt init cnd step b) ∗
      □ frameAt env aEnv.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 aRet.toNat ∗ world N L Room inp .uncounted st d ∗
      execSpecsP (vsaModel live) N L Room inp Core ∗ ▷ X ∗
      (K ∧ (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
        ownSet (execS s) byteAny) -∗ (wpW (vsaModel live)).W Φ)) ∗
      (∀ (R' : Nat → BitVec 64) (st' : St) (status : Status), ⌜ExecS st d env b st' status⌝ -∗
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = whileA0 status⌝ -∗
        ms (forNext status) R' (execS s) Mt -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        statusRet N aRet.toNat status -∗ world N L Room inp .uncounted st' d -∗ X -∗
        (K ∧ (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
          ownSet (execS s) byteAny) -∗ (wpW (vsaModel live)).W Φ)) -∗ (wpW (vsaModel live)).W Φ)
    ⊢ (wpW (vsaModel live)).W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hslot, Hw, #HS, HX, HK, Hk⟩
  iapply forStageBody (wpW _) hlive hh
  iframe Hms Hcode Hast
  iintro %R1 %aB %⟨hregs, hk1⟩ #Hab Hms
  ihave Hb := execSpecsP_at (N := N) (L := L) (Room := Room) (inp := inp) Core st d env b $$ HS
  iapply ms_callExecPx (N := N) (L := L) (Room := Room) (inp := inp) (Kret := K) (X := X)
    (i := 0x800042b8) (jalx_800042b8 live (fun p hp => hlive _ (interp_code_800042b8 p hp)))
    interp_code_800042b8 (by decide) (hsg.narrow hfit) hfit hsg.le hslg hbb
  iframe Hb HX Hcode Hab Hfr Hms Hst Hslot Hw HK
  isplitl []
  · ipureintro; exact hregs
  iintro %R2 %st' %status %hE %⟨hk2, h20⟩ Hms Hst Hret Hw HX HK
  iapply forRoute (wpW _) (R := upd R2 1 (BitVec.ofNat 64 (0x800042b8 + 4))) hlive
    (by ix_reg; exact h20)
  iframe Hms Hcode
  iintro %R3 %⟨hk3, h30⟩ Hms
  iapply Hk $$ %R3 %st' %status %hE
    %⟨KeepRegs.trans (KeepRegs.trans hk1 (hk2.calleeSaved_upd (by decide) _)) hk3, h30⟩
    Hms Hst Hret Hw HX HK

/-- **The step, partial mode**: from `0x80004264` to the loop head with the
`ExecStep` derivation (the step's value discarded). -/
theorem forStepP (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    {Core K : IProp GF} {st : St} {d env : Nat} {init : Option Stmt} {cnd step : Option Expr}
    {b : Stmt} {aS aEnv aRet s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} {m' : Nat}
    (hh : StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv) (hfg : ExecFrameGeom s)
    (hsg : StackGeom (s + 18446744073709551440#64) m') (hfits : ForFits d cnd step b m') :
    ms 0x80004264#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.forStmt init cnd step b) ∗
      □ frameAt env aEnv.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      world N L Room inp .uncounted st d ∗ evalSpecsP (vsaModel live) N L Room inp Core ∗
      (K ∧ (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ ownSet (execS s) byteAny) -∗
        (wpW (vsaModel live)).W Φ)) ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st' : St), ⌜ExecStep st d env step st'⌝ -∗
        ⌜KeepRegs calleeSaved R R' ∧ Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms 0x8000426c#64 R' (execS s) Mt' -∗ stackScratch (s + 18446744073709551440#64) m' -∗
        world N L Room inp .uncounted st' d -∗
        (K ∧ (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ ownSet (execS s) byteAny) -∗
          (wpW (vsaModel live)).W Φ)) -∗ (wpW (vsaModel live)).W Φ)
    ⊢ (wpW (vsaModel live)).W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hw, #HE, HK, Hk⟩
  cases step with
  | none =>
    iapply forStepNone (wpW _) hlive hh
    iframe Hms Hcode Hast
    iintro %R' %hk Hms
    iapply Hk $$ %R' %Mt %st %(ExecStep.none _ _ _) %⟨hk, Untouched.refl _ _ _⟩ Hms Hst Hw HK
  | some e =>
    obtain ⟨hfit, heb⟩ := hfits.step e rfl
    have hs16 := execSlot hfg (o := 16) (by omega) rfl
    iapply forStepStage (wpW _) hlive hh
    iframe Hms Hcode Hast
    iintro %R1 %aE %⟨hregs, hk1⟩ #Hae Hms
    ihave He := evalSpecsP_at (N := N) (L := L) (Room := Room) (inp := inp) Core st d env e $$ HE
    iapply ms_callEvalPx (N := N) (L := L) (Room := Room) (inp := inp) (X := iprop(emp)) (Kret := K)
      (i := 0x800042e8) (jalx_800042e8 live (fun p hp => hlive _ (interp_code_800042e8 p hp)))
      interp_code_800042e8 (by decide) (hsg.narrow hfit) hfit hsg.le hs16.geo heb
    iframe He Hcode Hae Hfr Hms Hst Hw HK
    isplitl []
    · ipureintro; exact ⟨hregs, execSlot_in hs16 (by omega)⟩
    isplitl []
    · inext; iempintro
    iintro %R2 %w0 %w1 %w2 %st' %v %hE %hk2 #_ Hms Hst Hw - HK
    iapply forJoin (wpW _) hlive (.inr rfl)
    iframe Hms Hcode
    iintro Hms
    iapply Hk $$ %_ %_ %st' %(ExecStep.some _ _ _ _ _ _ hE)
      %⟨KeepRegs.trans hk1 (hk2.calleeSaved_upd (by decide) _),
        Untouched.slotWrite hs16 (Nat.le_refl _) (by omega) Mt w0 w1 w2⟩ Hms Hst Hw HK

/-- `forLoopP_body` as one Iris proposition: the statement Löb is taken over. -/
abbrev forLoopPI (Core : IProp GF) (d env : Nat) (cnd step : Option Expr) (b : Stmt) :
    IProp GF :=
  iprop(∀ (Φ : Nat × String → IProp GF) (st : St) (init : Option Stmt) (aS aEnv aRet s : BitVec 64)
      (R : Nat → BitVec 64) (Mt : Mem) (m' : Nat),
    ⌜StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv ∧ ExecFrameGeom s ∧
      StackGeom (s + 18446744073709551440#64) m' ∧ ForFits d cnd step b m' ∧ SlotGeom aRet⌝ -∗
    (ms 0x8000426c#64 R (execS s) Mt ∗ codeRes ∗ □ astSG aS.toNat (.forStmt init cnd step b) ∗
      □ frameAt env aEnv.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 aRet.toNat ∗ world N L Room inp .uncounted st d ∗
      evalSpecsP (vsaModel live) N L Room inp Core ∗ execSpecsP (vsaModel live) N L Room inp Core ∗
      ((∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st' : St) (status : Status),
        ⌜ForLoop st d env cnd step b st' status⌝ -∗
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms (loopExit status) R' (execS s) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ statusRet N aRet.toNat status -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ) ∧
       (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
          ownSet (execS s) byteAny) -∗ (wpW (vsaModel live)).W Φ))) -∗
    (wpW (vsaModel live)).W Φ)

/-- The loop's exit pair at a head state, as a proposition (what each branch
of an iteration hands on). -/
abbrev forExitK (Core : IProp GF) (Φ : Nat × String → IProp GF) (st : St) (d env : Nat)
    (cnd step : Option Expr) (b : Stmt) (aRet s : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem)
    (m' : Nat) : IProp GF :=
  iprop((∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st' : St) (status : Status),
        ⌜ForLoop st d env cnd step b st' status⌝ -∗
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms (loopExit status) R' (execS s) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ statusRet N aRet.toNat status -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ) ∧
       (iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
          ownSet (execS s) byteAny) -∗ (wpW (vsaModel live)).W Φ))

theorem forExitK_ret {Core : IProp GF} {Φ : Nat × String → IProp GF} {st : St} {d env : Nat}
    {cnd step : Option Expr} {b : Stmt} {aRet s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    {m' : Nat} :
    forExitK (GF := GF) (live := live) (N := N) (L := L) (Room := Room) (inp := inp)
        Core Φ st d env cnd step b aRet s R Mt m' ⊢
      ∀ (R' : Nat → BitVec 64) (Mt' : Mem) (st' : St) (status : Status),
        ⌜ForLoop st d env cnd step b st' status⌝ -∗
        ⌜KeepRegs calleeSaved R R' ∧ R' 10 = statusCode status ∧
          Untouched (execS s) (execW s) Mt Mt'⌝ -∗
        ms (loopExit status) R' (execS s) Mt' -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ statusRet N aRet.toNat status -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ :=
  and_elim_l

theorem forExitK_abort {Core : IProp GF} {Φ : Nat × String → IProp GF} {st : St} {d env : Nat}
    {cnd step : Option Expr} {b : Stmt} {aRet s : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    {m' : Nat} :
    forExitK (GF := GF) (live := live) (N := N) (L := L) (Room := Room) (inp := inp)
        Core Φ st d env cnd step b aRet s R Mt m' ⊢
      iprop(abortAt Core (s + 18446744073709551440#64) m' ∗ slot24 aRet.toNat ∗
          ownSet (execS s) byteAny) -∗ (wpW (vsaModel live)).W Φ :=
  and_elim_r

/-- **One iteration from the body's staging** (partial mode): the body, then
out, or the step and the next iteration through `X` (the Löb hypothesis,
whose later the body's `jal` pays). -/
theorem forFromBodyP (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    {Core : IProp GF} {st st1 : St} {d env : Nat} {init : Option Stmt} {cnd step : Option Expr}
    {b : Stmt} {aS aEnv aRet s : BitVec 64} {R R1 : Nat → BitVec 64} {Mt Mt1 : Mem} {m' : Nat}
    (hfc : ForCond st d env cnd st1) (hk1 : KeepRegs calleeSaved R R1)
    (hut1 : Untouched (execS s) (execW s) Mt Mt1)
    (hh : StmtHead R s aS (BitVec.ofNat 64 inp) aRet aEnv) (hfg : ExecFrameGeom s)
    (hsg : StackGeom (s + 18446744073709551440#64) m') (hfits : ForFits d cnd step b m')
    (hslg : SlotGeom aRet) :
    ms 0x800042a8#64 R1 (execS s) Mt1 ∗ codeRes ∗ □ astSG aS.toNat (.forStmt init cnd step b) ∗
      □ frameAt env aEnv.toNat ∗ stackScratch (s + 18446744073709551440#64) m' ∗
      slot24 aRet.toNat ∗ world N L Room inp .uncounted st1 d ∗
      evalSpecsP (vsaModel live) N L Room inp Core ∗ execSpecsP (vsaModel live) N L Room inp Core ∗
      ▷ forLoopPI (GF := GF) (live := live) (N := N) (L := L) (Room := Room) (inp := inp)
        Core d env cnd step b ∗
      forExitK (GF := GF) (live := live) (N := N) (L := L) (Room := Room) (inp := inp)
        Core Φ st d env cnd step b aRet s R Mt m'
    ⊢ (wpW (vsaModel live)).W Φ := by
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hslot, Hw, #HE, #HS, HX, HK⟩
  have hh1 := hh.keep hk1
  iapply forBodyP (init := init) (cnd := cnd) (step := step)
    (X := forLoopPI (GF := GF) (live := live) (N := N) (L := L) (Room := Room) (inp := inp)
      Core d env cnd step b)
    (K := forExitK (GF := GF) (live := live) (N := N) (L := L) (Room := Room) (inp := inp)
      Core Φ st d env cnd step b aRet s R Mt m')
    hlive hh1 hsg hfits.body hfits.bodyB hslg
  iframe Hms Hcode Hast Hfr Hst Hslot Hw HS HX
  isplitl [HK]
  · isplit
    · iexact HK
    · iapply forExitK_abort $$ HK
  iintro %R2 %st2 %status %hE2 %⟨hk2, h20⟩ Hms Hst Hret Hw HX HK
  cases status with
  | brk =>
    simp only [forNext, whileA0]
    ihave HK := and_elim_l $$ HK
    ihave HK := forExitK_ret $$ HK
    rw [← loopExit_normal, statusRet_brk, ← statusRet_normal (GF := GF) N]
    iapply HK $$ %R2 %Mt1 %st2 %.normal %(ForLoop.bodyBreak _ _ _ _ _ _ _ _ hfc hE2)
      %⟨KeepRegs.trans hk1 hk2, h20, hut1⟩ Hms Hst Hret Hw
  | ret rv =>
    simp only [forNext]
    ihave HK := and_elim_l $$ HK
    ihave HK := forExitK_ret $$ HK
    rw [← loopExit_ret rv]
    iapply HK $$ %R2 %Mt1 %st2 %(.ret rv) %(ForLoop.bodyRet _ _ _ _ _ _ _ _ _ hfc hE2)
      %⟨KeepRegs.trans hk1 hk2, h20, hut1⟩ Hms Hst Hret Hw
  | normal | cont =>
    simp only [forNext, statusRet_normal, statusRet_cont]
    have hh2 := hh1.keep hk2
    ihave HK := and_elim_l $$ HK
    iapply forStepP (K := iprop(slot24 aRet.toNat ∗
        forLoopPI (GF := GF) (live := live) (N := N) (L := L) (Room := Room) (inp := inp)
          Core d env cnd step b ∗
        forExitK (GF := GF) (live := live) (N := N) (L := L) (Room := Room) (inp := inp)
          Core Φ st d env cnd step b aRet s R Mt m'))
      hlive hh2 hfg hsg hfits
    iframe Hms Hcode Hast Hfr Hst Hw HE
    isplitl [HK HX Hret]
    · isplit
      · iframe HK HX Hret
      · iintro ⟨HA, HO⟩
        ihave HK := forExitK_abort $$ HK
        iapply HK $$ [HA Hret HO]
        iframe HA Hret HO
    iintro %R3 %Mt3 %st3 %hS3 %⟨hk3, hut3⟩ Hms Hst Hw HK
    ihave ⟨Hslot, HX, HK⟩ := and_elim_l $$ HK
    iapply HX $$ %Φ %st3 %init %aS %aEnv %aRet %s %R3 %Mt3 %m' %⟨hh2.keep hk3, hfg, hsg, hfits, hslg⟩
    iframe Hms Hcode Hast Hfr Hst Hslot Hw HE HS
    isplit
    · iintro %R4 %Mt4 %st4 %status4 %hL4 %⟨hk4, h40, hut4⟩ Hms Hst Hret Hw
      ihave HK := forExitK_ret $$ HK
      iapply HK $$ %R4 %Mt4 %st4 %status4
        %(ForLoop.loop _ _ _ _ _ _ _ _ _ _ _ _ hfc hE2 (by first | exact .inl rfl | exact .inr rfl) hS3 hL4)
        %⟨KeepRegs.trans (KeepRegs.trans (KeepRegs.trans hk1 hk2) hk3) hk4, h40,
          (hut1.trans hut3).trans hut4⟩ Hms Hst Hret Hw
    · iapply forExitK_abort $$ HK

/-- **The `for` loop, partial mode, by Löb**: one iteration from the head
(the condition: out or on to the body), the rest through `forFromBodyP`. -/
theorem forLoopPI_loeb (hlive : ∀ p ∈ interpText, live p.1)
    (htr : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p v)
    (Core : IProp GF) (d env : Nat) (cnd step : Option Expr) (b : Stmt) :
    ⊢ forLoopPI (GF := GF) (live := live) (N := N) (L := L) (Room := Room) (inp := inp)
        Core d env cnd step b := by
  iapply loeb_wand
  imodintro
  iintro Hlob
  iintro %Φ %st %init %aS %aEnv %aRet %s %R %Mt %m' %⟨hh, hfg, hsg, hfits, hslg⟩
    ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hslot, Hw, #HE, #HS, HK⟩
  cases cnd with
  | none =>
    iapply forCondNone (wpW _) hlive hh
    iframe Hms Hcode Hast
    iintro %R1 %hk1 Hms
    iapply forFromBodyP hlive (ForCond.none _ _ _) hk1 (Untouched.refl _ _ _) hh hfg hsg hfits hslg
    iframe Hms Hcode Hast Hfr Hst Hslot Hw HE HS Hlob
    iexact HK
  | some c =>
    obtain ⟨hfit, hcb⟩ := hfits.cond c rfl
    iapply forCondEvalP (K := iprop(slot24 aRet.toNat ∗
        forExitK (GF := GF) (live := live) (N := N) (L := L) (Room := Room) (inp := inp)
          Core Φ st d env (some c) step b aRet s R Mt m'))
      hlive htr hh hfg hsg hfit hcb
    iframe Hms Hcode Hast Hfr Hst Hw HE
    isplitl [HK Hslot]
    · isplit
      · iframe Hslot HK
      · iintro ⟨HA, HO⟩
        ihave HK := and_elim_r $$ HK
        iapply HK $$ [HA Hslot HO]
        iframe HA Hslot HO
    iintro %R1 %Mt1 %st1 %v %hE1 %⟨hk1, h10, hut1⟩ Hms Hst Hw HK
    ihave ⟨Hslot, HK⟩ := and_elim_l $$ HK
    iapply forBranch (wpW _) hlive
    iframe Hms Hcode
    isplit
    · iintro %h0 Hms
      cases hv : v.truthy with
      | true => exfalso; rw [hv] at h10; rw [h10] at h0; exact absurd h0 (by decide)
      | false =>
        ihave HK := forExitK_ret $$ HK
        rw [← loopExit_normal, ← statusRet_normal (GF := GF) N]
        iapply HK $$ %_ %Mt1 %st1 %.normal %(ForLoop.condFalse _ _ _ _ _ _ _ _ hE1 hv)
          %⟨hk1.calleeSaved_upd (by decide) _, by ix_reg; rfl, hut1⟩ Hms Hst Hslot Hw
    · iintro %h0 Hms
      cases hv : v.truthy with
      | false => exfalso; rw [hv] at h10; exact h0 (by simpa using h10)
      | true =>
        iapply forFromBodyP hlive (ForCond.some _ _ _ _ _ _ hE1 hv) hk1 hut1 hh hfg hsg hfits hslg
        iframe Hms Hcode Hast Hfr Hst Hslot Hw HE HS Hlob
        iexact HK

/-- **The `for` loop, partial mode** (`forLoopP_body`), for every loop. -/
theorem forLoopP_all (hlive : ∀ p ∈ interpText, live p.1)
    (htr : ⊢ ∀ p v, valueTruthySpec (GF := GF) (vsaModel live) N (wpW (vsaModel live)) p v)
    (Core : IProp GF) (d env : Nat) (cnd step : Option Expr) (b : Stmt) :
    forLoopP_body (GF := GF) live N L Room inp Core d env cnd step b := by
  intro Φ st init aS aEnv aRet s R Mt m' hh hfg hsg hfits hslg
  have H := forLoopPI_loeb (L := L) (Room := Room) (inp := inp) hlive htr Core d env cnd step b
  iintro Hpre
  ihave H := H
  iapply H $$ %Φ %st %init %aS %aEnv %aRet %s %R %Mt %m' %⟨hh, hfg, hsg, hfits, hslg⟩ Hpre

/-- **The `for` init, partial mode** (`execInitP_body`), for every init. -/
theorem execInitP_all (hlive : ∀ p ∈ interpText, live p.1) (Core : IProp GF) (d outer : Nat) :
    ∀ init, execInitP_body (GF := GF) live N L Room inp Core d outer init := by
  intro init Φ st cnd step b aS aOuter aRet s R Mt m' hh _ hsg hfits hslg
  iintro ⟨Hms, #Hcode, #Hast, #Hfr, Hst, Hslot, Hw, #HS, HK⟩
  cases init with
  | none =>
    iapply forInitNone (wpW _) hlive hh
    iframe Hms Hcode Hast
    iintro %R' %hk Hms
    ihave HK := and_elim_l $$ HK
    iapply HK $$ %R' %st %(ExecInit.none _ _ _) %hk Hms Hst Hslot Hw
  | some i =>
    obtain ⟨hfit, hib⟩ := hfits i rfl
    iapply forInitStage (wpW _) hlive hh
    iframe Hms Hcode Hast
    iintro %R1 %aI %⟨hregs, hk1, h19⟩ #Hai Hms
    ihave Hi := execSpecsP_at (N := N) (L := L) (Room := Room) (inp := inp) Core st d outer i $$ HS
    iapply ms_callExecP (N := N) (L := L) (Room := Room) (inp := inp)
      (Kret := iprop(∀ (R' : Nat → BitVec 64) (st' : St),
        ⌜ExecInit st d outer (some i) st'⌝ -∗ ⌜KeepRegs initKeep R R' ∧ R' 19 = aOuter⌝ -∗
        ms 0x8000426c#64 R' (execS s) Mt -∗
        stackScratch (s + 18446744073709551440#64) m' -∗ slot24 aRet.toNat -∗
        world N L Room inp .uncounted st' d -∗ (wpW (vsaModel live)).W Φ))
      (i := 0x80004254) (jalx_80004254 live (fun p hp => hlive _ (interp_code_80004254 p hp)))
      interp_code_80004254 (by decide) (hsg.narrow hfit) hfit hsg.le hslg hib
    iframe Hi Hcode Hai Hfr Hms Hst Hslot Hw HK
    isplitl []
    · ipureintro; exact hregs
    iintro %R2 %st' %status %hE %⟨hk2, -⟩ Hms Hst Hret Hw HK
    ihave Hslot := statusRet_slot N _ status $$ Hret
    ihave HK := and_elim_l $$ HK
    iapply forJoin (wpW _) hlive (.inl rfl)
    iframe Hms Hcode
    iintro Hms
    have hk2c : KeepRegs calleeSaved R1 (upd R2 1 (BitVec.ofNat 64 (0x80004254 + 4))) :=
      hk2.calleeSaved_upd (by decide) _
    iapply HK $$ %_ %st' %(ExecInit.some _ _ _ _ _ _ hE)
      %⟨KeepRegs.trans hk1 (KeepRegs.sub hk2c (by decide)), (hk2c 19 (by decide)).trans h19⟩
      Hms Hst Hslot Hw

end Partial

end VsaIris.Interp
