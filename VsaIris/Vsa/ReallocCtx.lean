import VsaIris.Vsa.FreeRunAll
import VsaIris.Vsa.AllocSltu
import VsaIris.Vsa.HeapRealloc

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

structure RB where
  p : Nat
  nOld : Nat
  old : Nat → BitVec 8

structure RRet (C : MCtx) (B : RB) (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  regs : MRegs C R
  fresh : FreshAt C.H (R 10).toNat C.n.toNat
  align : (R 10).toNat % 16 = 0
  heap : ∃ top brkv chunks bins,
    PHeapAt Mt (((R 10).toNat, C.n.toNat) :: C.H) top brkv chunks bins ∧
      top ≤ C.top0 + physSize C.n.toNat
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  data : ∀ k, k < B.nOld → Mt[(R 10).toNat + k]? = some (B.old (B.p + k))

structure RNull (C : MCtx) (B : RB) (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  regs : MRegs C R
  a0 : R 10 = 0
  heap : ∃ top brkv chunks bins, PHeapAt Mt ((B.p, B.nOld) :: C.H) top brkv chunks bins
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  data : ∀ k, k < B.nOld → Mt[B.p + k]? = some (B.old (B.p + k))
  starved : Starved C.top0 C.n.toNat

structure ROK (C : MCtx) (B : RB) : Prop extends WOK C where
  spA : SpOKA C.s
  deep : ∀ a, C.s.toNat - allocHeadroom ≤ a → a < C.s.toNat → C.S a
  ok : ∀ R Mt, RRet C B R Mt → AW C.live C.S C.Q C.r R Mt
  null : ∀ R Mt, RNull C B R Mt → AW C.live C.S C.Q C.r R Mt

theorem ROK.stack {C : MCtx} {B : RB} (O : ROK C B) {a w : Nat} (h1 : C.s.toNat - mHead ≤ a)
    (h2 : a + w ≤ C.s.toNat) : ∀ b ∈ accAddrs a w, C.S b := O.toWOK.stack h1 h2

theorem ROK.foot {C : MCtx} {B : RB} (O : ROK C B) {a w : Nat}
    (h : ∀ k, k < w → vsaFoot C.H (a + k)) : ∀ b ∈ accAddrs a w, C.S b := O.toWOK.foot h

macro_rules
  | `(tactic| sx_side) => `(tactic| (refine VsaIris.VsaHeap.ROK.stack ‹VsaIris.VsaHeap.ROK _ _› ?_ ?_ <;> ((try unfold VsaIris.VsaHeap.mHead) ; sx_addr)))

macro_rules
  | `(tactic| sx_side) => `(tactic| (refine VsaIris.VsaHeap.ROK.foot ‹VsaIris.VsaHeap.ROK _ _› (fun k hk => Or.inl ?_); unfold VsaIris.VsaHeap.allocGlobal VsaIris.VsaHeap.InRange; omega))

structure REntry (C : MCtx) (B : RB) (R : Nat → BitVec 64) : Prop where
  ra : R 1 = C.r
  sp : R 2 = C.s
  a0 : R 10 = reentV
  a1 : (R 11).toNat = B.p
  a2 : R 12 = C.n
  s0 : R 8 = C.rv0 8
  s1 : R 9 = C.rv0 9
  s2 : R 18 = C.rv0 18
  s3 : R 19 = C.rv0 19

structure RFrame (C : MCtx) (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  sp : R 2 = C.s + 18446744073709551552#64
  s0 : read64 Mt (C.s.toNat - 64 + 48) = some (C.rv0 8).toNat
  s1 : read64 Mt (C.s.toNat - 64 + 40) = some (C.rv0 9).toNat
  ra : read64 Mt (C.s.toNat - 64 + 56) = some C.r.toNat
  s2 : R 18 = C.rv0 18
  s3 : R 19 = C.rv0 19

theorem RFrame.of_regs {C : MCtx} {R R' : Nat → BitVec 64} {Mt : Mem} (F : RFrame C R Mt)
    (h2 : R' 2 = R 2) (h18 : R' 18 = R 18) (h19 : R' 19 = R 19) : RFrame C R' Mt :=
  ⟨h2.trans F.sp, F.s0, F.s1, F.ra, h18.trans F.s2, h19.trans F.s3⟩

theorem RFrame.store {C : MCtx} {R : Nat → BitVec 64} {Mt : Mem} (F : RFrame C R Mt)
    {a w : Nat} {v : BitVec 64} (h : a + w ≤ C.s.toNat - 64 + 40 ∨ C.s.toNat - 64 + 64 ≤ a) :
    RFrame C R (writeLog Mt [(a, w, v)]) where
  sp := F.sp
  s0 := by rw [read64_store_miss _ _ (by omega)]; exact F.s0
  s1 := by rw [read64_store_miss _ _ (by omega)]; exact F.s1
  ra := by rw [read64_store_miss _ _ (by omega)]; exact F.ra
  s2 := F.s2
  s3 := F.s3

structure RHeap (C : MCtx) (B : RB) (Mt : Mem) (brkv : Nat) (chunks : List Chunk)
    (bins : Nat → List Nat) : Prop where
  heap : PHeapAt Mt ((B.p, B.nOld) :: C.H) C.top0 brkv chunks bins
  starts : Starts ((B.p, B.nOld) :: C.H)
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  disj : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  disjD : ∀ a, C.s.toNat - allocHeadroom ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  frame : ∀ a, ¬ MWin C.H C.s a → Mt[a]? = C.Mt0[a]?
  blk : ∀ k, k < B.nOld → vsaFoot C.H (B.p + k)
  data : ∀ k, k < B.nOld → Mt[B.p + k]? = some (B.old (B.p + k))
  grow : B.nOld < C.n.toNat

theorem RHeap.store_stack {C : MCtx} {B : RB} {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (Hp : RHeap C B Mt brkv chunks bins) {a w : Nat} {v : BitVec 64}
    (h1 : C.s.toNat - mHead ≤ a) (h2 : a + w ≤ C.s.toNat) :
    RHeap C B (writeLog Mt [(a, w, v)]) brkv chunks bins where
  heap := Hp.heap.transport_read fun x hx => by
    have hd := Hp.disj x
    have ho : OutL [(a, w, v)] x := ⟨Classical.byContradiction fun hc => by
      simp only at hc
      exact hd (by omega) (by omega) (vsaFoot_of_cons hx.1), trivial⟩
    rw [writeLog_out _ _ _ ho]
  starts := Hp.starts
  pres := pres_store Hp.pres
  disj := Hp.disj
  disjD := Hp.disjD
  frame := frame_store (win_stack h1 h2) Hp.frame
  blk := Hp.blk
  grow := Hp.grow
  data := fun k hk => by
    have hd := Hp.disj (B.p + k)
    have ho : OutL [(a, w, v)] (B.p + k) := ⟨Classical.byContradiction fun hc => by
      simp only at hc
      exact hd (by omega) (by omega) (Hp.blk k hk), trivial⟩
    rw [writeLog_out _ _ _ ho]; exact Hp.data k hk

theorem RHeap.store_errno {C : MCtx} {B : RB} {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (Hp : RHeap C B Mt brkv chunks bins) {v : BitVec 64} :
    RHeap C B (writeLog Mt [(0x8001b538, 4, v)]) brkv chunks bins where
  heap := Hp.heap.transport_read fun x hx => by
    have ho : OutL [(0x8001b538, 4, v)] x := ⟨Classical.byContradiction fun hc => by
      simp only at hc
      exact hx.2.1 ⟨by omega, by omega⟩, trivial⟩
    rw [writeLog_out _ _ _ ho]
  starts := Hp.starts
  pres := pres_store Hp.pres
  disj := Hp.disj
  disjD := Hp.disjD
  frame := frame_store (fun b h1 h2 => .inl (.inl (.inr (.inl ⟨h1, h2⟩)))) Hp.frame
  blk := Hp.blk
  grow := Hp.grow
  data := fun k hk => by
    have hb := Hp.heap.heap.heap.live (B.p, B.nOld) List.mem_cons_self
    obtain ⟨c, hc, _, h1, h2⟩ := hb
    have := Hp.heap.heap.heap.walk.chunk_bounds c hc
    unfold heapStart at this
    simp only at h1 h2
    have ho : OutL [(0x8001b538, 4, v)] (B.p + k) := ⟨by simp only; omega, trivial⟩
    rw [writeLog_out _ _ _ ho]; exact Hp.data k hk

theorem repi_core {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {pc1 pc2 pc3 pc4 pc5 pc6 : BitVec 64}
    (st1 : ∀ {R : Nat → BitVec 64} {Mt : Mem},
      LdOK ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8 →
      (∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x038#12)).toNat 8, C.S b) →
      AW C.live C.S C.Q pc2 (upd R 1 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x038#12)).toNat)) Mt →
      AW C.live C.S C.Q pc1 R Mt)
    (st2 : ∀ {R : Nat → BitVec 64} {Mt : Mem},
      LdOK ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8 →
      (∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x030#12)).toNat 8, C.S b) →
      AW C.live C.S C.Q pc3 (upd R 8 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x030#12)).toNat)) Mt →
      AW C.live C.S C.Q pc2 R Mt)
    (st3 : ∀ {R : Nat → BitVec 64} {Mt : Mem},
      LdOK ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8 →
      (∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8, C.S b) →
      AW C.live C.S C.Q pc4 (upd R 9 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x028#12)).toNat)) Mt →
      AW C.live C.S C.Q pc3 R Mt)
    (st4 : ∀ {R : Nat → BitVec 64} {Mt : Mem},
      AW C.live C.S C.Q pc5 (upd R 10 ((R 13) + sign_extend (m := 64) (0x000#12))) Mt →
      AW C.live C.S C.Q pc4 R Mt)
    (st5 : ∀ {R : Nat → BitVec 64} {Mt : Mem},
      AW C.live C.S C.Q pc6 (upd R 2 ((R 2) + sign_extend (m := 64) (0x040#12))) Mt →
      AW C.live C.S C.Q pc5 R Mt)
    (st6 : ∀ {R : Nat → BitVec 64} {Mt : Mem}, (R 1).toNat % 4 = 0 →
      AW C.live C.S C.Q (R 1) R Mt → AW C.live C.S C.Q pc6 R Mt)
    (F : RFrame C R Mt)
    (hfin : ∀ R' : Nat → BitVec 64, MRegs C R' → R' 10 = R 13 → AW C.live C.S C.Q C.r R' Mt) :
    AW C.live C.S C.Q pc1 R Mt := by
  have hlo := O.sp.lo; have hhi := O.sp.hi
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2 := F.sp
  have e56 : (R 2 + sign_extend (m := 64) (0x038#12)).toNat = C.s.toNat - 64 + 56 := by rw [hs2]; sx_addr
  have e48 : (R 2 + sign_extend (m := 64) (0x030#12)).toNat = C.s.toNat - 64 + 48 := by rw [hs2]; sx_addr
  have e40 : (R 2 + sign_extend (m := 64) (0x028#12)).toNat = C.s.toNat - 64 + 40 := by rw [hs2]; sx_addr
  refine st1 (by rw [e56]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by rw [e56]; exact O.stack (by unfold mHead; omega) (by omega)) ?_
  refine st2 (by rw [upd_other _ _ (by decide), e48]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by rw [upd_other _ _ (by decide), e48]; exact O.stack (by unfold mHead; omega) (by omega)) ?_
  refine st3 (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [e40]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by carry_norm [e40]; exact O.stack (by unfold mHead; omega) (by omega)) ?_
  refine st4 ?_
  refine st5 ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [e56, e48, e40, ldv_ld F.ra, ldv_ld F.s0, ldv_ld F.s1]
  refine st6 (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact O.ral) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  have hs64 : R 2 + sign_extend (m := 64) (0x040#12) = C.s := by
    apply BitVec.eq_of_toNat_eq; rw [hs2]; sx_addr
  refine hfin _ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ <;> try carry_close [hs64, F.s2, F.s3]
  sx_norm

theorem repi {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem} (F : RFrame C R Mt)
    (hfin : ∀ R' : Nat → BitVec 64, MRegs C R' → R' 10 = R 13 → AW C.live C.S C.Q C.r R' Mt) :
    AW C.live C.S C.Q 0x8000544c#64 R Mt :=
  repi_core O ((step% st 0x8000544c) O.live) ((step% st 0x80005450) O.live) ((step% st 0x80005454) O.live) ((step% st 0x80005458) O.live)
    ((step% st 0x8000545c) O.live) ((step% st 0x80005460) O.live) F hfin

theorem repi0 {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem} (F : RFrame C R Mt)
    (hfin : ∀ R' : Nat → BitVec 64, MRegs C R' → R' 10 = R 13 → AW C.live C.S C.Q C.r R' Mt) :
    AW C.live C.S C.Q 0x800054c4#64 R Mt :=
  repi_core O ((step% st 0x800054c4) O.live) ((step% st 0x800054c8) O.live) ((step% st 0x800054cc) O.live) ((step% st 0x800054d0) O.live)
    ((step% st 0x800054d4) O.live) ((step% st 0x800054d8) O.live) F hfin

end VsaIris.VsaHeap
