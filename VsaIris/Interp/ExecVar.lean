import VsaIris.Interp.ExecEnv
import VsaIris.Interp.LeafArm
import VsaIris.Interp.ExecOom

/-!
# `exec_stmt`'s `var` arms: runs, node facts, the shared tail (lane E5)

`0x800040d8`: `ld a2,16(s0)` (the initializer), `beqz`; with an initializer the
value is evaluated into the frame slot `sp+104` (`jal eval_expr`,
`0x800040ec`), without one `value_null` fills it (`0x800042fc`..`0x80004304`,
then `j 0x800040f0`). The shared tail `0x800040f0`: the name (`ld a1,8(s0)`),
the copy `sp+104 → sp+16`, `env_define(env, name, sp+16)` (`0x80004114`),
`li a0,0`, the shared exit.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim

/-- The facts of a `var` node: the name (`+8`, a C string) and the initializer
field (`+16`: an expression, or NULL). -/
structure VarNode (m : Mem) (P : Nat → Prop) (aS : BitVec 64) (x : String)
    (eo : Option Vsa.While.Expr) (pn pi : Nat) : Prop where
  node : StmtNode m P aS 1 24
  name : ldv .ld m (aS + 8#64).toNat = BitVec.ofNat 64 pn
  nameStr : CStringWithin m P pn x
  nameNat : (BitVec.ofNat 64 pn).toNat = pn
  init : ldv .ld m (aS + 16#64).toNat = BitVec.ofNat 64 pi
  initRepr : ∀ e, eo = some e → ExprReprWithin m P pi e ∧ BitVec.ofNat 64 pi ≠ 0#64
  initNat : (BitVec.ofNat 64 pi).toNat = pi
  initNone : eo = none → BitVec.ofNat 64 pi = 0#64

/-- A `var` statement node. -/
theorem varNode_of {m : Mem} {P : Nat → Prop} {aS : BitVec 64} {x : String}
    {eo : Option Vsa.While.Expr} (h : StmtReprWithin m P aS.toNat (.varDecl x eo))
    (hg : ∀ k, P k → Interp.ReadOK k) : ∃ pn pi, VarNode m P aS x eo pn pi := by
  cases h with
  | @varInit _ pn pi _ _ h1 c1 hn cn hs hi ci hne hx =>
    have hnd := stmtNode_of (w := 24) hg h1 c1 (by decide) (Or.inr (by decide)) (fun j h1 h2 => by
      by_cases j1 : j < 16
      · exact field_mid hn cn (by omega) (by omega)
      · exact field_mid hi ci (by omega) (by omega))
    refine ⟨pn, pi, hnd, field64 hn (by have := hnd.hi; omega), hs, ofNat_toNat_of_read hn,
      field64 hi (by have := hnd.hi; omega), ?_, ofNat_toNat_of_read hi, fun h => by cases h⟩
    intro e he; cases he; exact ⟨hx, ofNat_ne_of_read hi hne⟩
  | @varNull _ pn _ h1 c1 hn cn hs hi ci =>
    have hnd := stmtNode_of (w := 24) hg h1 c1 (by decide) (Or.inr (by decide)) (fun j h1 h2 => by
      by_cases j1 : j < 16
      · exact field_mid hn cn (by omega) (by omega)
      · exact field_mid hi ci (by omega) (by omega))
    exact ⟨pn, 0, hnd, field64 hn (by have := hnd.hi; omega), hs, ofNat_toNat_of_read hn,
      field64 hi (by have := hnd.hi; omega), (fun _ h => by cases h), rfl, fun _ => rfl⟩

#ix_seg VarArm_run1I {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s aI : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 24 ≤ 0x100000000)
    (hx3 : aS.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (h16 : R 16 = 8#64) (h14 : R 14 = 0x80019fb8#64)
    (h2 : R 2 = s + 18446744073709551440#64)
    (hk : ldv .lw m aS.toNat = 1#64) (hku : ldv .lwu m aS.toNat = 1#64)
    (hi : ldv .ld m (aS + 16#64).toNat = aI) (hi0 : aI ≠ 0#64) :
    IW live m (stmtView aS.toNat 24) (InExt (s.toNat - 176, 176)) Q 0x80004014#64 R Mt
  by rw [← upd_eq_self h16]
     ix_run hlive using [h8, h14, h2, hk, hku, hi, hi0, hsf] at 0x800040ec

#ix_seg VarArm_run1N {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 24 ≤ 0x100000000)
    (hx3 : aS.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (h16 : R 16 = 8#64) (h14 : R 14 = 0x80019fb8#64)
    (h2 : R 2 = s + 18446744073709551440#64)
    (hk : ldv .lw m aS.toNat = 1#64) (hku : ldv .lwu m aS.toNat = 1#64)
    (hi : ldv .ld m (aS + 16#64).toNat = 0#64) :
    IW live m (stmtView aS.toNat 24) (InExt (s.toNat - 176, 176)) Q 0x80004014#64 R Mt
  by rw [← upd_eq_self h16]
     ix_run hlive using [h8, h14, h2, hk, hku, hi, hsf] at 0x80004300

#ix_seg VarArm_runJ {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64} :
    IW live m [] (InExt (s.toNat - 176, 176)) Q 0x80004304#64 R Mt
  by ix_run hlive at 0x800040f0

#ix_seg VarArm_run2 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aS s pn : BitVec 64}
    (hsf : (s + 18446744073709551440#64).toNat = s.toNat - 176)
    (hs : 0x87800000 + 176 ≤ s.toNat) (hs2 : s.toNat ≤ 0x88000000) (hs3 : s.toNat % 16 = 0)
    (hx1 : 0x80000000 ≤ aS.toNat) (hx2 : aS.toNat + 24 ≤ 0x100000000)
    (hx3 : aS.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 16 ≤ aS.toNat)
    (h8 : R 8 = aS) (h2 : R 2 = s + 18446744073709551440#64)
    (hn : ldv .ld m (aS + 8#64).toNat = pn) :
    IW live m (stmtView aS.toNat 24) (InExt (s.toNat - 176, 176)) Q 0x800040f0#64 R Mt
  by ix_run hlive using [h8, h2, hn, hsf] at 0x80004114

#ix_seg VarArm_run3 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64} :
    IW live m [] (InExt (s.toNat - 176, 176)) Q 0x80004118#64 R Mt
  by ix_run hlive at 0x8000409c

section Tail

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr VsaIris.VsaHeap

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {inp : Nat}

/-- **The `var` arms' tail, counted regime, for either WP**: at `0x800040f0`
with the value `v` in the frame slot `sp+104` (its words `w0 w1 w2`), the copy
to `sp+16`, `env_define(env, name, sp+16)`, `li a0,0` and the shared exit;
the world advances to `Store.define`, `defineCost` credits spent. -/
theorem varTail (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {k : Nat} {st : St} {d env : Nat} {x : String}
    {eo : Option Expr} {v : Value}
    {aS aE aRet s ret v8 v9 v18 v19 w0 w1 w2 : BitVec 64} {R0 R : Nat → BitVec 64} {Mt : Mem}
    {P : Nat → Prop} {m : Mem} {pn pi : Nat}
    (hsg : StackGeom s (execNeed (.varDecl x eo) d)) (hal : ret.toNat % 4 = 0)
    (hn : VarNode m P aS x eo pn pi) (hgeo : ∀ k, P k → ReadOK k)
    (h2 : R 2 = execSP s) (h8 : R 8 = aS) (h19 : R 19 = aE)
    (hk : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R0 R) (hsv : ExecSaved Mt s ret v8 v9 v18 v19)
    (hw0 : ldv .ld Mt (s.toNat - 176 + 104) = w0) (hw1 : ldv .ld Mt (s.toNat - 176 + 112) = w1)
    (hw2 : ldv .ld Mt (s.toNat - 176 + 120) = w2) :
    envDefineSpec Wp N ∗ codeRes ∗ roOn P m ∗ □ frameAt env aE.toNat ∗ □ valOf N v w0 w1 w2 ∗
      ms 0x800040f0#64 R (InExt (s.toNat - 176, 176)) Mt ∗
      stackScratch (execSP s) (execNeed (.varDecl x eo) d - 176) ∗ slot24 aRet.toNat ∗
      world N vsaLayoutP vsaRoomB inp (.counted (k + defineCost st.store env x)) st d ∗
      execDispK (vsaModel live) N vsaLayoutP vsaRoomB inp Wp Φ (.counted k)
        ⟨st.store.define env x v, st.out⟩ d (.varDecl x eo) .normal aRet s R0 ret v8 v9 v18 v19
    ⊢ Wp.W Φ := by
  obtain ⟨hfg, hneed⟩ := execFrameGeom_of hsg
  have hoff := execSP_offF (s := s) hfg.sf (by have := hfg.hi; omega)
  have g16 : (execSP s + 16#64).toNat = s.toNat - 176 + 16 := hoff 16 (by decide)
  have hbig : envDefineNeed ≤ execNeed (.varDecl x eo) d - 176 := by
    have := Stmt.stackNeed_ge (.varDecl x eo)
    unfold execNeed stackBudget evalFrame envDefineNeed allocHeadroom
    unfold execFrame at this; omega
  have hle' : execNeed (.varDecl x eo) d - 176 ≤ (execSP s).toNat := by
    rw [hfg.sf]; have := hsg.le; omega
  iintro ⟨#Hed, #Hcode, #Hro, #Hfb, #Hv, Hms, Hst, Hslot, Hw, HK⟩
  ihave #Hstr := strAt_of_cstringWithin hn.nameStr (sharedWin_of_readOK hgeo) $$ Hro
  ihave #Hdv := roOwn_data hn.node.view $$ [Hcode Hro]
  · iframe Hcode Hro
  -- the name, the copy, the arguments
  iapply wp_swpF Wp (F := iprop(envDefineSpec Wp N ∗ frameAt env aE.toNat ∗ valOf N v w0 w1 w2 ∗
      strAt pn x ∗ codeRes ∗ stackScratch (execSP s) (execNeed (.varDecl x eo) d - 176) ∗
      slot24 aRet.toNat ∗ world N vsaLayoutP vsaRoomB inp (.counted (k + defineCost st.store env x)) st d ∗
      execDispK (vsaModel live) N vsaLayoutP vsaRoomB inp Wp Φ (.counted k)
        ⟨st.store.define env x v, st.out⟩ d (.varDecl x eo) .normal aRet s R0 ret v8 v9 v18 v19))
  rotate_left
  · iframe Hdv Hms Hed Hfb Hv Hstr Hcode Hst Hslot Hw HK
  intro F'
  refine VarArm_run2 (pn := BitVec.ofNat 64 pn) hlive hfg.sf hfg.lo hfg.hi hfg.al hn.node.lo
    hn.node.hi hn.node.off h8 h2 hn.name ?_
  intros
  apply swp_closeRM
  intro R2 M2 hR2 hM2
  have hsv2 : ExecSaved M2 s ret v8 v9 v18 v19 := by
    have := hfg.lo; rw [hM2]; ix_esaved hsv using hoff
  have hs0 : ldv .ld M2 (execSP s + 16#64).toNat = w0 := by
    rw [hM2]; ix_fwd; rw [hoff _ (by decide), hw0]
  have hs8 : ldv .ld M2 ((execSP s + 16#64).toNat + 8) = w1 := by
    rw [hM2, g16, show s.toNat - 176 + 16 + 8 = (s + 18446744073709551440#64 + 24#64).toNat by
      rw [hoff 24 (by decide)]]; ix_fwd; rw [hoff _ (by decide), hw1]
  have hs16 : ldv .ld M2 ((execSP s + 16#64).toNat + 16) = w2 := by
    rw [hM2, g16, show s.toNat - 176 + 16 + 16 = (s + 18446744073709551440#64 + 32#64).toNat by
      rw [hoff 32 (by decide)]]; ix_fwd; rw [hoff _ (by decide), hw2]
  have hslotS : ∀ b, InExt ((execSP s + 16#64).toNat, 24) b → InExt (s.toNat - 176, 176) b :=
    fun b hb => by simp only [InExt] at hb ⊢; rw [g16] at hb; omega
  unfold F'
  iintro ⟨⟨#Hed, #Hfb, #Hv, #Hstr, #Hcode, Hst, Hslot, Hw, HK⟩, Hms⟩
  -- the value slot lent to env_define
  ihave ⟨Hms, Hval⟩ := ms_valCarve N hslotS hs0 hs8 hs16 $$ [Hms]
  · iframe Hms Hv
  ihave ⟨Hw, #Hcx⟩ := world_codeX N vsaLayoutP vsaRoomB inp _ st d $$ Hw
  ihave ⟨Hh, Hc, Hio, Hi⟩ := (world_heapStore N inp (.counted (k + defineCost st.store env x)) st d).1 $$ Hw
  have h22 : R2 2 = execSP s := by subst hR2; ix_reg; exact h2
  have h210 : R2 10 = aE := by subst hR2; ix_reg; exact h19
  have h211 : R2 11 = BitVec.ofNat 64 pn := by subst hR2; ix_reg
  have hr12 : R2 12 = execSP s + 16#64 := by subst hR2; ix_reg; try rw [h2]
  ihave ⟨Hsl, Hst⟩ := stackScratch_narrow (s := execSP s) hle' hbig $$ Hst
  have eSt : stackScratch (GF := GF) (execSP s) envDefineNeed ⊢ stackScratch (R2 2) envDefineNeed := by
    rw [h22]
  have eVal : valAt (GF := GF) N (execSP s + 16#64).toNat v ⊢ valAt N (R2 12).toNat v := by
    rw [hr12]
  ihave Hst := eSt $$ Hst
  ihave Hval := eVal $$ Hval
  iapply ms_callEnvDefine (N := N) Wp (i := 0x80004114)
    (jalx_80004114 live (fun p hp => hlive _ (interp_code_80004114 p hp)))
    interp_code_80004114 (by decide) (k := k) (st := st.store) (fa := env) (x := x) (v := v)
    (R := R2)
    ⟨by rw [h22, hfg.sf]; have := hfg.lo; unfold htifLo envDefineNeed allocHeadroom; omega,
      by rw [h22, hfg.sf]; have := hfg.hi; omega, by rw [h22, hfg.sf]; have := hfg.al; omega⟩
    ⟨by rw [hr12, g16]; have := hfg.lo; omega,
      by rw [hr12, g16]; have := hfg.hi; omega,
      by rw [hr12, g16]; have := hfg.lo; unfold htifLo; omega,
      by rw [hr12, g16]; have := hfg.al; omega⟩
  iframe Hed Hcode Hcx Hms Hst Hh Hval
  isplitl []
  · imodintro; rw [h210]; iexact Hfb
  isplitl []
  · imodintro; rw [h211, hn.nameNat]; iexact Hstr
  iintro %R3 %hk3 Hst Hval Hh Hms
  have eSt' : stackScratch (GF := GF) (R2 2) envDefineNeed ⊢ stackScratch (execSP s) envDefineNeed := by
    rw [h22]
  have eVal' : valAt (GF := GF) N (R2 12).toNat v ⊢ valAt N (execSP s + 16#64).toNat v := by
    rw [hr12]
  ihave Hst := eSt' $$ Hst
  ihave Hval := eVal' $$ Hval
  ihave ⟨%M3, Hms, %hag⟩ := ms_valUncarve N hslotS $$ [Hms Hval]
  · iframe Hms Hval
  have hsv3 : ExecSaved M3 s ret v8 v9 v18 v19 := by
    have := hfg.lo
    exact hsv2.congrHi (fun y h1 h2' => hag y (by simp only [InExt]; omega)
      (by simp only [InExt]; rw [g16]; omega)) (by omega)
  ihave Hst := stackScratch_widen (s := execSP s) hle' hbig $$ [Hsl Hst]
  · iframe Hsl Hst
  ihave Hw := (world_heapStore N inp (.counted k) ⟨st.store.define env x v, st.out⟩ d).2 $$ [Hh Hc Hio Hi]
  · iframe Hh Hc Hio Hi
  -- `li a0,0`, the shared exit
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ [])
    (F := iprop(codeRes ∗ stackScratch (execSP s) (execNeed (.varDecl x eo) d - 176) ∗
      slot24 aRet.toNat ∗
      world N vsaLayoutP vsaRoomB inp (.counted k) ⟨st.store.define env x v, st.out⟩ d ∗
      execDispK (vsaModel live) N vsaLayoutP vsaRoomB inp Wp Φ (.counted k)
        ⟨st.store.define env x v, st.out⟩ d (.varDecl x eo) .normal aRet s R0 ret v8 v9 v18 v19))
  rotate_left
  · iframe Hms Hcode Hst Hslot Hw HK
    iapply codeRes_text $$ Hcode
  intro F'
  refine VarArm_run3 (m := ∅) (s := s) hlive ?_
  intros
  apply swp_closeRM
  intro R4 M4 hR4 hM4
  have hk3' : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R (upd R3 1 (BitVec.ofNat 64 (0x80004114 + 4))) := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (ix_reg; rw [hk3 _ (by decide) (by decide)]; subst hR2; ix_reg)
  have hepi := wp_execEpi (N := N) (L := vsaLayoutP) (Room := vsaRoomB) (inp := inp) hlive Wp
    (Φ := Φ) (ρ := .counted k) (st' := ⟨st.store.define env x v, st.out⟩) (d := d)
    (sm := .varDecl x eo) (status := .normal) (aRet := aRet) (s := s) (ret := ret) (v8 := v8)
    (v9 := v9) (v18 := v18) (v19 := v19) (R0 := R0) (R := R4) (Mt := M4) hsg hal
    (by subst hR4; ix_reg; rw [hk3 2 (by decide) (by decide)]; exact h22) (by subst hR4; ix_reg; rfl)
    (by rw [hM4]; exact hsv3)
    (KeepRegs.trans hk (by subst hR4; repeat (first | exact hk3' | refine KeepRegs.upd ?_ (by decide) _)))
  simp only [statusRet] at hepi
  unfold F'
  iintro ⟨⟨#Hcode, Hst, Hslot, Hw, HK⟩, Hms⟩
  iapply hepi
  iframe Hcode Hms Hst Hslot Hw HK

end Tail

section TailP

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.While Vsa.RuntimeRepr VsaIris.VsaHeap

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs} {inp : Nat}

omit I in
/-- The frame bytes whole again from a lent slot's bytes. -/
theorem ownSet_unslotAny {S : Nat → Prop} {a : Nat} (h : ∀ b, InExt (a, 24) b → S b) :
    ownSet (GF := GF) (fun b => S b ∧ ¬ InExt (a, 24) b) byteAny ∗ slot24 a ⊢ ownSet S byteAny := by
  unfold slot24 blockOwn
  iintro ⟨H1, H2⟩
  ihave H := ownSet_join _ _ _ (fun b (hb : S b ∧ ¬ InExt (a, 24) b) h2 => hb.2 h2) $$ [H1 H2]
  · iframe H1 H2
  iapply ownSet_iff _ (fun b => ⟨fun hb => hb.elim (·.1) (h b), fun hb => by
    by_cases hs : InExt (a, 24) b
    · exact .inr hs
    · exact .inl ⟨hb, hs⟩⟩) $$ H

/-- **The `var` arms' tail, partial mode**: `varTail` in the uncounted regime;
out of memory (`env_define`'s array growth), the arm aborts through `CoreOK`
with its frame (the lent value slot back in it). -/
theorem varTailP (hlive : ∀ p ∈ interpText, live p.1) (HN : Newlib.NewlibHoles)
    (hcl : Newlib.CodeLive live) {Core : IProp GF} (hcore : CoreOK N vsaLayoutP vsaRoomB inp Core)
    {Φ : Nat × String → IProp GF} {st : St} {d env : Nat} {x : String}
    {eo : Option Expr} {v : Value}
    {aS aE aRet s ret v8 v9 v18 v19 w0 w1 w2 : BitVec 64} {R0 R : Nat → BitVec 64} {Mt : Mem}
    {P : Nat → Prop} {m : Mem} {pn pi : Nat}
    (hsg : StackGeom s (execNeed (.varDecl x eo) d)) (hal : ret.toNat % 4 = 0)
    (hn : VarNode m P aS x eo pn pi) (hgeo : ∀ k, P k → ReadOK k)
    (h2 : R 2 = execSP s) (h8 : R 8 = aS) (h19 : R 19 = aE)
    (hk : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R0 R) (hsv : ExecSaved Mt s ret v8 v9 v18 v19)
    (hw0 : ldv .ld Mt (s.toNat - 176 + 104) = w0) (hw1 : ldv .ld Mt (s.toNat - 176 + 112) = w1)
    (hw2 : ldv .ld Mt (s.toNat - 176 + 120) = w2) :
    envDefineSpec (wpW (vsaModel live)) N ∗ codeRes ∗ Newlib.binImg ∗ roOn P m ∗
      □ frameAt env aE.toNat ∗ □ valOf N v w0 w1 w2 ∗
      ms 0x800040f0#64 R (InExt (s.toNat - 176, 176)) Mt ∗
      stackScratch (execSP s) (execNeed (.varDecl x eo) d - 176) ∗ slot24 aRet.toNat ∗
      world N vsaLayoutP vsaRoomB inp .uncounted st d ∗
      (execDispK (vsaModel live) N vsaLayoutP vsaRoomB inp (wpW (vsaModel live)) Φ .uncounted
          ⟨st.store.define env x v, st.out⟩ d (.varDecl x eo) .normal aRet s R0 ret v8 v9 v18 v19 ∧
        (iprop(abortAt Core s (execNeed (.varDecl x eo) d) ∗ slot24 aRet.toNat) -∗
          (wpW (vsaModel live)).W Φ))
    ⊢ (wpW (vsaModel live)).W Φ := by
  obtain ⟨hfg, hneed⟩ := execFrameGeom_of hsg
  have hoff := execSP_offF (s := s) hfg.sf (by have := hfg.hi; omega)
  have g16 : (execSP s + 16#64).toNat = s.toNat - 176 + 16 := hoff 16 (by decide)
  have hbig : envDefineNeed ≤ execNeed (.varDecl x eo) d - 176 := by
    have := Stmt.stackNeed_ge (.varDecl x eo)
    unfold execNeed stackBudget evalFrame envDefineNeed allocHeadroom
    unfold execFrame at this; omega
  have hle' : execNeed (.varDecl x eo) d - 176 ≤ (execSP s).toNat := by
    rw [hfg.sf]; have := hsg.le; omega
  iintro ⟨#Hed, #Hcode, #Himg, #Hro, #Hfb, #Hv, Hms, Hst, Hslot, Hw, HK⟩
  ihave #Hstr := strAt_of_cstringWithin hn.nameStr (sharedWin_of_readOK hgeo) $$ Hro
  ihave #Hdv := roOwn_data hn.node.view $$ [Hcode Hro]
  · iframe Hcode Hro
  -- the name, the copy, the arguments
  iapply wp_swpF (wpW _) (F := iprop(envDefineSpec (wpW (vsaModel live)) N ∗ Newlib.binImg ∗
      frameAt env aE.toNat ∗ valOf N v w0 w1 w2 ∗
      strAt pn x ∗ codeRes ∗ stackScratch (execSP s) (execNeed (.varDecl x eo) d - 176) ∗
      slot24 aRet.toNat ∗ world N vsaLayoutP vsaRoomB inp .uncounted st d ∗
      (execDispK (vsaModel live) N vsaLayoutP vsaRoomB inp (wpW (vsaModel live)) Φ .uncounted
          ⟨st.store.define env x v, st.out⟩ d (.varDecl x eo) .normal aRet s R0 ret v8 v9 v18 v19 ∧
        (iprop(abortAt Core s (execNeed (.varDecl x eo) d) ∗ slot24 aRet.toNat) -∗
          (wpW (vsaModel live)).W Φ))))
  rotate_left
  · iframe Hdv Hms Hed Himg Hfb Hv Hstr Hcode Hst Hslot Hw HK
  intro F'
  refine VarArm_run2 (pn := BitVec.ofNat 64 pn) hlive hfg.sf hfg.lo hfg.hi hfg.al hn.node.lo
    hn.node.hi hn.node.off h8 h2 hn.name ?_
  intros
  apply swp_closeRM
  intro R2 M2 hR2 hM2
  have hsv2 : ExecSaved M2 s ret v8 v9 v18 v19 := by
    have := hfg.lo; rw [hM2]; ix_esaved hsv using hoff
  have hs0 : ldv .ld M2 (execSP s + 16#64).toNat = w0 := by
    rw [hM2]; ix_fwd; rw [hoff _ (by decide), hw0]
  have hs8 : ldv .ld M2 ((execSP s + 16#64).toNat + 8) = w1 := by
    rw [hM2, g16, show s.toNat - 176 + 16 + 8 = (s + 18446744073709551440#64 + 24#64).toNat by
      rw [hoff 24 (by decide)]]; ix_fwd; rw [hoff _ (by decide), hw1]
  have hs16 : ldv .ld M2 ((execSP s + 16#64).toNat + 16) = w2 := by
    rw [hM2, g16, show s.toNat - 176 + 16 + 16 = (s + 18446744073709551440#64 + 32#64).toNat by
      rw [hoff 32 (by decide)]]; ix_fwd; rw [hoff _ (by decide), hw2]
  have hslotS : ∀ b, InExt ((execSP s + 16#64).toNat, 24) b → InExt (s.toNat - 176, 176) b :=
    fun b hb => by simp only [InExt] at hb ⊢; rw [g16] at hb; omega
  unfold F'
  iintro ⟨⟨#Hed, #Himg, #Hfb, #Hv, #Hstr, #Hcode, Hst, Hslot, Hw, HK⟩, Hms⟩
  ihave ⟨Hms, Hval⟩ := ms_valCarve N hslotS hs0 hs8 hs16 $$ [Hms]
  · iframe Hms Hv
  have h22 : R2 2 = execSP s := by subst hR2; ix_reg; exact h2
  have h210 : R2 10 = aE := by subst hR2; ix_reg; exact h19
  have h211 : R2 11 = BitVec.ofNat 64 pn := by subst hR2; ix_reg
  have hr12 : R2 12 = execSP s + 16#64 := by subst hR2; ix_reg; try rw [h2]
  have eSt : stackScratch (GF := GF) (execSP s) (execNeed (.varDecl x eo) d - 176) ⊢
      stackScratch (R2 2) (execNeed (.varDecl x eo) d - 176) := by rw [h22]
  have eVal : valAt (GF := GF) N (execSP s + 16#64).toNat v ⊢ valAt N (R2 12).toNat v := by
    rw [hr12]
  ihave Hst := eSt $$ Hst
  ihave Hval := eVal $$ Hval
  iapply ms_callEnvDefineP (N := N) HN hcl (i := 0x80004114)
    (jalx_80004114 live (fun p hp => hlive _ (interp_code_80004114 p hp)))
    interp_code_80004114 (by decide) (st := st) (d := d) (fa := env) (x := x) (v := v)
    (R := R2) (n := execNeed (.varDecl x eo) d - 176)
    ⟨by rw [h22, hfg.sf]; have := hfg.lo; unfold htifLo envDefineNeed allocHeadroom; omega,
      by rw [h22, hfg.sf]; have := hfg.hi; omega, by rw [h22, hfg.sf]; have := hfg.al; omega⟩
    ⟨by rw [hr12, g16]; have := hfg.lo; omega,
      by rw [hr12, g16]; have := hfg.hi; omega,
      by rw [hr12, g16]; have := hfg.lo; unfold htifLo; omega,
      by rw [hr12, g16]; have := hfg.al; omega⟩
    hbig (by rw [h22]; exact hle')
    (by rw [h22, hfg.sf]; have := hsg.lo; simp only [Vsa.Sim.LayoutInstance.stackSL] at this;
        omega)
    (by rw [h22, hfg.sf]; have := Stmt.stackNeed_ge (.varDecl x eo); have := hsg.le
        unfold execNeed stackBudget evalFrame Newlib.fwriteNeed at *; unfold execFrame at *; omega)
    (by rw [h22, hfg.sf]; have := hfg.hi; omega)
  iframe Hed Hcode Himg Hms Hst Hw Hval
  isplitl []
  · imodintro; rw [h210]; iexact Hfb
  isplitl []
  · imodintro; rw [h211, hn.nameNat]; iexact Hstr
  isplit
  rotate_left
  · -- out of memory: the arm aborts with its frame
    iintro ⟨HA, Hval, HS⟩
    ihave HK := and_elim_r $$ HK
    iapply HK
    iframe Hslot
    unfold abortRes
    ihave ⟨HC, Hst⟩ := abortAt_elim _ _ _ $$ HA
    ihave HC := hcore (R2 2) (execNeed (.varDecl x eo) d - 176) (by rw [h22]; exact hle')
      (by rw [h22, hfg.sf]; have := hsg.lo; simp only [Vsa.Sim.LayoutInstance.stackSL] at this; omega)
      (by rw [h22, hfg.sf]; have := hsg.top; omega) $$ HC
    iapply abortAt_intro
    iframe HC
    ihave Hval := valAt_slot $$ Hval
    rw [hr12] at *
    ihave HS := ownSet_unslotAny hslotS $$ [HS Hval]
    · iframe HS Hval
    rw [h22]
    iapply execFrame_join hsg.le hneed $$ [Hst HS]
    iframe Hst HS
  iintro %R3 %hk3 Hst Hval Hw Hms
  have eSt' : stackScratch (GF := GF) (R2 2) (execNeed (.varDecl x eo) d - 176) ⊢
      stackScratch (execSP s) (execNeed (.varDecl x eo) d - 176) := by rw [h22]
  have eVal' : valAt (GF := GF) N (R2 12).toNat v ⊢ valAt N (execSP s + 16#64).toNat v := by
    rw [hr12]
  ihave Hst := eSt' $$ Hst
  ihave Hval := eVal' $$ Hval
  ihave ⟨%M3, Hms, %hag⟩ := ms_valUncarve N hslotS $$ [Hms Hval]
  · iframe Hms Hval
  have hsv3 : ExecSaved M3 s ret v8 v9 v18 v19 := by
    have := hfg.lo
    exact hsv2.congrHi (fun y h1 h2' => hag y (by simp only [InExt]; omega)
      (by simp only [InExt]; rw [g16]; omega)) (by omega)
  ihave HK := and_elim_l $$ HK
  -- `li a0,0`, the shared exit
  iapply wp_swpF (wpW _) (text := interpText ++ dataOf ∅ [])
    (F := iprop(codeRes ∗ stackScratch (execSP s) (execNeed (.varDecl x eo) d - 176) ∗
      slot24 aRet.toNat ∗
      world N vsaLayoutP vsaRoomB inp .uncounted ⟨st.store.define env x v, st.out⟩ d ∗
      execDispK (vsaModel live) N vsaLayoutP vsaRoomB inp (wpW (vsaModel live)) Φ .uncounted
        ⟨st.store.define env x v, st.out⟩ d (.varDecl x eo) .normal aRet s R0 ret v8 v9 v18 v19))
  rotate_left
  · iframe Hms Hcode Hst Hslot Hw HK
    iapply codeRes_text $$ Hcode
  intro F'
  refine VarArm_run3 (m := ∅) (s := s) hlive ?_
  intros
  apply swp_closeRM
  intro R4 M4 hR4 hM4
  have hk3' : KeepRegs [20, 21, 22, 23, 24, 25, 26, 27] R (upd R3 1 (BitVec.ofNat 64 (0x80004114 + 4))) := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (ix_reg; rw [hk3 _ (by decide) (by decide)]; subst hR2; ix_reg)
  have hepi := wp_execEpi (N := N) (L := vsaLayoutP) (Room := vsaRoomB) (inp := inp) hlive (wpW _)
    (Φ := Φ) (ρ := .uncounted) (st' := ⟨st.store.define env x v, st.out⟩) (d := d)
    (sm := .varDecl x eo) (status := .normal) (aRet := aRet) (s := s) (ret := ret) (v8 := v8)
    (v9 := v9) (v18 := v18) (v19 := v19) (R0 := R0) (R := R4) (Mt := M4) hsg hal
    (by subst hR4; ix_reg; rw [hk3 2 (by decide) (by decide)]; exact h22) (by subst hR4; ix_reg; rfl)
    (by rw [hM4]; exact hsv3)
    (KeepRegs.trans hk (by subst hR4; repeat (first | exact hk3' | refine KeepRegs.upd ?_ (by decide) _)))
  simp only [statusRet] at hepi
  unfold F'
  iintro ⟨⟨#Hcode, Hst, Hslot, Hw, HK⟩, Hms⟩
  iapply hepi
  iframe Hcode Hms Hst Hslot Hw HK

end TailP

end VsaIris.Interp
