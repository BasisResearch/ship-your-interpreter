import Vsa.Sim.HelperCall
import Vsa.Sim.rows.EvalChildArmRet
import Vsa.Sim.rows.ExecRecRows
import Vsa.Sim.rows.ExecDispatchRows

/-!
# `RetSlotCopy` — the `ret e` arm's resume on the layer

After the child returns at `0x80004138`, the arm copies the three result
words from `esp+16` into the caller's retslot (`s2`) and runs the status-3
epilogue at `0x80004150`.  Everything is on the layer except one named
premise: the returned string payload (if any) lies outside the retslot
window, so the byte copy cannot corrupt it (`PayloadOffWindow`).
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

#derive_case retSlotCopySeg chain
  [(0x80004138#64, 0x01013683#32),
   (0x8000413c#64, 0x01813703#32),
   (0x80004140#64, 0x02013783#32),
   (0x80004144#64, 0x00d93023#32),
   (0x80004148#64, 0x00e93423#32),
   (0x8000414c#64, 0x00f93823#32)]

/-- The three result words read by the copy. -/
def retSlotLds (m : Mem) (esp : BitVec 64) : List (List (BitVec 8)) :=
  [EvalChildArm.wordLds8 m (esp.toNat + 16), EvalChildArm.wordLds8 m (esp.toNat + 24),
   EvalChildArm.wordLds8 m (esp.toNat + 32)]

/-- The copy's reflected write log: three stores into the retslot. -/
theorem retSlotCopy_log_eq (a0 esp ra s0 s1 s2 s3 : BitVec 64) (m : Mem) :
    writeLog m (evalBlocks retSlotCopySeg (SegEvalState.init
      (TruthyCopy.routeL a0 esp ra s0 s1 s2 s3) (retSlotLds m esp))).log =
    writeMap8 (writeMap8 (writeMap8 m
      (s2 + sign_extend (m := 64) (0x000#12)).toNat
      (sdData_val (bytesVal MKind.ld (EvalChildArm.wordLds8 m (esp.toNat + 16)))))
      (s2 + sign_extend (m := 64) (0x008#12)).toNat
      (sdData_val (bytesVal MKind.ld (EvalChildArm.wordLds8 m (esp.toNat + 24)))))
      (s2 + sign_extend (m := 64) (0x010#12)).toNat
      (sdData_val (bytesVal MKind.ld (EvalChildArm.wordLds8 m (esp.toNat + 32)))) := rfl

private theorem addr_off (b : BitVec 64) (off : BitVec 12) (n : Nat) (hn : n ≤ 32)
    (hb : b.toNat + n < 2 ^ 64)
    (hoff : (sign_extend (m := 64) off : BitVec 64) = BitVec.ofNat 64 n) :
    (b + sign_extend (m := 64) off).toNat = b.toNat + n := by
  rw [hoff, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The copy fills the retslot with the result words, byte for byte. -/
theorem retSlotCopy_total (a0 esp ra s0 s1 s2 s3 : BitVec 64) (m : Mem)
    (hslot : s2.toNat + 24 ≤ 0x100000000) :
    ∀ j, j < 24 →
      (writeLog m (evalBlocks retSlotCopySeg (SegEvalState.init
        (TruthyCopy.routeL a0 esp ra s0 s1 s2 s3) (retSlotLds m esp))).log)[s2.toNat + j]? =
        some ((m[esp.toNat + 16 + j]?).getD 0) := by
  have hn0 := addr_off s2 0x000#12 0 (by omega) (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have hn8 := addr_off s2 0x008#12 8 (by omega) (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have hn16 := addr_off s2 0x010#12 16 (by omega) (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  let k0 := (m[esp.toNat + 16]?).getD 0
  let k1 := (m[esp.toNat + 16 + 1]?).getD 0
  let k2 := (m[esp.toNat + 16 + 2]?).getD 0
  let k3 := (m[esp.toNat + 16 + 3]?).getD 0
  let k4 := (m[esp.toNat + 16 + 4]?).getD 0
  let k5 := (m[esp.toNat + 16 + 5]?).getD 0
  let k6 := (m[esp.toNat + 16 + 6]?).getD 0
  let k7 := (m[esp.toNat + 16 + 7]?).getD 0
  let p0 := (m[esp.toNat + 24]?).getD 0
  let p1 := (m[esp.toNat + 24 + 1]?).getD 0
  let p2 := (m[esp.toNat + 24 + 2]?).getD 0
  let p3 := (m[esp.toNat + 24 + 3]?).getD 0
  let p4 := (m[esp.toNat + 24 + 4]?).getD 0
  let p5 := (m[esp.toNat + 24 + 5]?).getD 0
  let p6 := (m[esp.toNat + 24 + 6]?).getD 0
  let p7 := (m[esp.toNat + 24 + 7]?).getD 0
  let q0 := (m[esp.toNat + 32]?).getD 0
  let q1 := (m[esp.toNat + 32 + 1]?).getD 0
  let q2 := (m[esp.toNat + 32 + 2]?).getD 0
  let q3 := (m[esp.toNat + 32 + 3]?).getD 0
  let q4 := (m[esp.toNat + 32 + 4]?).getD 0
  let q5 := (m[esp.toNat + 32 + 5]?).getD 0
  let q6 := (m[esp.toNat + 32 + 6]?).getD 0
  let q7 := (m[esp.toNat + 32 + 7]?).getD 0
  obtain ⟨eK0, eK1, eK2, eK3, eK4, eK5, eK6, eK7⟩ := TruthyCopy.sdData_sext_bytes k0 k1 k2 k3 k4 k5 k6 k7
  obtain ⟨eP0, eP1, eP2, eP3, eP4, eP5, eP6, eP7⟩ := TruthyCopy.sdData_sext_bytes p0 p1 p2 p3 p4 p5 p6 p7
  obtain ⟨eQ0, eQ1, eQ2, eQ3, eQ4, eQ5, eQ6, eQ7⟩ := TruthyCopy.sdData_sext_bytes q0 q1 q2 q3 q4 q5 q6 q7
  intro j hj
  rw [retSlotCopy_log_eq, hn0, hn8, hn16]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨
      j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨
      j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨
      j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 from by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [EvalChildArm.wordLds8, bytesVal, List.getD_cons_zero,
      List.getD_cons_succ, Nat.add_zero]
  · rw [getElem_writeMap8_disjoint _ (s2.toNat + 16) _ _ (by omega),
      getElem_writeMap8_disjoint _ (s2.toNat + 8) _ _ (by omega),
      getElem_writeMap8_0, eK0]
  · rw [getElem_writeMap8_disjoint _ (s2.toNat + 16) _ _ (by omega),
      getElem_writeMap8_disjoint _ (s2.toNat + 8) _ _ (by omega),
      getElem_writeMap8_1, eK1]
  · rw [getElem_writeMap8_disjoint _ (s2.toNat + 16) _ _ (by omega),
      getElem_writeMap8_disjoint _ (s2.toNat + 8) _ _ (by omega),
      getElem_writeMap8_2, eK2]
  · rw [getElem_writeMap8_disjoint _ (s2.toNat + 16) _ _ (by omega),
      getElem_writeMap8_disjoint _ (s2.toNat + 8) _ _ (by omega),
      getElem_writeMap8_3, eK3]
  · rw [getElem_writeMap8_disjoint _ (s2.toNat + 16) _ _ (by omega),
      getElem_writeMap8_disjoint _ (s2.toNat + 8) _ _ (by omega),
      getElem_writeMap8_4, eK4]
  · rw [getElem_writeMap8_disjoint _ (s2.toNat + 16) _ _ (by omega),
      getElem_writeMap8_disjoint _ (s2.toNat + 8) _ _ (by omega),
      getElem_writeMap8_5, eK5]
  · rw [getElem_writeMap8_disjoint _ (s2.toNat + 16) _ _ (by omega),
      getElem_writeMap8_disjoint _ (s2.toNat + 8) _ _ (by omega),
      getElem_writeMap8_6, eK6]
  · rw [getElem_writeMap8_disjoint _ (s2.toNat + 16) _ _ (by omega),
      getElem_writeMap8_disjoint _ (s2.toNat + 8) _ _ (by omega),
      getElem_writeMap8_7, eK7]
  · rw [getElem_writeMap8_disjoint _ (s2.toNat + 16) _ _ (by omega), getElem_writeMap8_0, eP0]
  · rw [getElem_writeMap8_disjoint _ (s2.toNat + 16) _ _ (by omega), getElem_writeMap8_1, eP1]
  · rw [getElem_writeMap8_disjoint _ (s2.toNat + 16) _ _ (by omega), getElem_writeMap8_2, eP2]
  · rw [getElem_writeMap8_disjoint _ (s2.toNat + 16) _ _ (by omega), getElem_writeMap8_3, eP3]
  · rw [getElem_writeMap8_disjoint _ (s2.toNat + 16) _ _ (by omega), getElem_writeMap8_4, eP4]
  · rw [getElem_writeMap8_disjoint _ (s2.toNat + 16) _ _ (by omega), getElem_writeMap8_5, eP5]
  · rw [getElem_writeMap8_disjoint _ (s2.toNat + 16) _ _ (by omega), getElem_writeMap8_6, eP6]
  · rw [getElem_writeMap8_disjoint _ (s2.toNat + 16) _ _ (by omega), getElem_writeMap8_7, eP7]
  · rw [getElem_writeMap8_0, eQ0]
  · rw [getElem_writeMap8_1, eQ1]
  · rw [getElem_writeMap8_2, eQ2]
  · rw [getElem_writeMap8_3, eQ3]
  · rw [getElem_writeMap8_4, eQ4]
  · rw [getElem_writeMap8_5, eQ5]
  · rw [getElem_writeMap8_6, eQ6]
  · rw [getElem_writeMap8_7, eQ7]

/-- The copy changes only the retslot window. -/
theorem retSlotCopy_frame (a0 esp ra s0 s1 s2 s3 : BitVec 64) (m : Mem)
    (hslot : s2.toNat + 24 ≤ 0x100000000) :
    ∀ k, ¬ (s2.toNat ≤ k ∧ k < s2.toNat + 24) →
      (writeLog m (evalBlocks retSlotCopySeg (SegEvalState.init
        (TruthyCopy.routeL a0 esp ra s0 s1 s2 s3) (retSlotLds m esp))).log)[k]? = m[k]? := by
  intro k hk
  have hn0 := addr_off s2 0x000#12 0 (by omega) (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have hn8 := addr_off s2 0x008#12 8 (by omega) (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have hn16 := addr_off s2 0x010#12 16 (by omega) (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  rw [retSlotCopy_log_eq, hn0, hn8, hn16]
  rw [getElem_writeMap8_disjoint _ (s2.toNat + 16) k _ (by omega),
    getElem_writeMap8_disjoint _ (s2.toNat + 8) k _ (by omega),
    getElem_writeMap8_disjoint _ (s2.toNat + 0) k _ (by omega)]

/-- The copy preserves memory presence. -/
theorem retSlotCopy_memExtends (a0 esp ra s0 s1 s2 s3 : BitVec 64) (m : Mem) :
    MemExtends m (writeLog m (evalBlocks retSlotCopySeg (SegEvalState.init
      (TruthyCopy.routeL a0 esp ra s0 s1 s2 s3) (retSlotLds m esp))).log) := by
  rw [retSlotCopy_log_eq]
  exact ((memExtends_writeMap8 m _ _).trans (memExtends_writeMap8 _ _ _)).trans
    (memExtends_writeMap8 _ _ _)

/-- The copy's chain facts: three in-frame loads, three retslot stores. -/
theorem retSlotCopy_facts (m : Mem) (SL : StackLayout) (sp esp a0 ra s0 s1 aRet s3 : BitVec 64)
    (hcode : Exec_stmtLoaded m)
    (hlo : SL.lo ≤ esp.toNat) (hhi : esp.toNat + 40 ≤ SL.hi)
    (hram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000)
    (hwin : tohostAddr + 16 ≤ SL.lo) (halign : esp.toNat % 16 = 0)
    (hslot : RetSlotGeom SL sp aRet) :
    ChainFacts m m (TruthyCopy.routeL a0 esp ra s0 s1 aRet s3) (retSlotLds m esp)
      retSlotCopySeg := by
  have hhi32 : esp.toNat + 40 ≤ 0x100000000 := Nat.le_trans hhi hram.2
  have htohost : tohostAddr + 16 ≤ esp.toNat := Nat.le_trans hwin hlo
  have hslot24 : aRet.toNat + 24 ≤ 0x100000000 := hslot.ram.2
  have ha16 := addr_off esp 0x010#12 16 (by omega) (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have ha24 := addr_off esp 0x018#12 24 (by omega) (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have ha32 := addr_off esp 0x020#12 32 (by omega) (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have hr0 := addr_off aRet 0x000#12 0 (by omega) (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have hr8 := addr_off aRet 0x008#12 8 (by omega) (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have hr16 := addr_off aRet 0x010#12 16 (by omega) (by omega) (by apply BitVec.eq_of_toNat_eq; decide)
  have hal := hslot.align
  have hwinR := hslot.win
  have hramR := hslot.ram
  unfold retSlotCopySeg ChainFacts
  chain_facts hcode with "Vsa.Sim.Code.exec_stmt_at_"
  · change ((0x80000000 ≤ (esp + sign_extend (m := 64) (0x010#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000 ∧
      ((esp + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (esp + sign_extend (m := 64) (0x010#12)).toNat)) ∧
      LPins8 m (esp + sign_extend (m := 64) (0x010#12)).toNat
        (EvalChildArm.wordLds8 m (esp.toNat + 16)))
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [ha16]; omega
    · rw [ha16]; omega
    · right; rw [ha16]; omega
    · rw [ha16]
      simp only [EvalChildArm.wordLds8, LPins8, List.getD_cons_zero, List.getD_cons_succ]
      trivial
  · change ((0x80000000 ≤ (esp + sign_extend (m := 64) (0x018#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ 0x100000000 ∧
      ((esp + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (esp + sign_extend (m := 64) (0x018#12)).toNat)) ∧
      LPins8 m (esp + sign_extend (m := 64) (0x018#12)).toNat
        (EvalChildArm.wordLds8 m (esp.toNat + 24)))
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [ha24]; omega
    · rw [ha24]; omega
    · right; rw [ha24]; omega
    · rw [ha24]
      simp only [EvalChildArm.wordLds8, LPins8, List.getD_cons_zero, List.getD_cons_succ]
      trivial
  · change ((0x80000000 ≤ (esp + sign_extend (m := 64) (0x020#12)).toNat ∧
      (esp + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ 0x100000000 ∧
      ((esp + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (esp + sign_extend (m := 64) (0x020#12)).toNat)) ∧
      LPins8 m (esp + sign_extend (m := 64) (0x020#12)).toNat
        (EvalChildArm.wordLds8 m (esp.toNat + 32)))
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [ha32]; omega
    · rw [ha32]; omega
    · right; rw [ha32]; omega
    · rw [ha32]
      simp only [EvalChildArm.wordLds8, LPins8, List.getD_cons_zero, List.getD_cons_succ]
      trivial
  · change (0x80000000 ≤ (aRet + sign_extend (m := 64) (0x000#12)).toNat ∧
      (aRet + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (aRet + sign_extend (m := 64) (0x000#12)).toNat ∧
      (aRet + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hr0] <;> omega
  · change (0x80000000 ≤ (aRet + sign_extend (m := 64) (0x008#12)).toNat ∧
      (aRet + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (aRet + sign_extend (m := 64) (0x008#12)).toNat ∧
      (aRet + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hr8] <;> omega
  · change (0x80000000 ≤ (aRet + sign_extend (m := 64) (0x010#12)).toNat ∧
      (aRet + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (aRet + sign_extend (m := 64) (0x010#12)).toNat ∧
      (aRet + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hr16] <;> omega

/-! ## The named premise -/

/-! ## The resume -/

/-- From a route-ready state at the copy head (`0x80004138`, the result in
the sub-result slot at `esp+16`): copy the result into the retslot and run
the status-3 epilogue.  The parent's frame facts may be taken at any earlier
memory that agrees on the saved registers; the store facts are those of the
exit state.  Shared by the value return (from the child's widened exit) and
the null return (from the `value_null` bridge). -/
theorem retSlotResume {s : Stmt}
    {g gC : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc φf' φc' : Addr → Nat}
    {st st' : Vsa.While.St} {d : Nat} {env : Addr} {v : Value}
    {sp r aInterp aStmt aEnv aRet a0 ra : BitVec 64} {m0 mF mX : Mem}
    {out : Array String} {cfgX : Config}
    (F : FrameFacts s g N A SL φf φc st d env sp r aInterp aStmt aEnv aRet gC mF)
    (hag : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat) mF mX)
    (hcodeX : Exec_stmtLoaded mX)
    (hR : TruthyCopy.RouteReady gC 0x80004138#64 a0 (sp - 176#64) ra
      aStmt aInterp aRet aEnv mX out cfgX)
    (hpf : PhiExtends φf φf' st.store.frames.size)
    (hpc : PhiExtends φc φc' st.store.closures.size)
    (hSurv : ∀ m' : Mem, (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → mX[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st'.store)
    (hv : ∃ φcv, PhiExtends φc φcv st.store.closures.size ∧
      ValueRepr mX N φcv ((sp - 176#64).toNat + 16) v)
    (hpay : PayloadOffWindow mX ((sp - 176#64).toNat + 16) aRet.toNat v)
    (hext : MemExtends m0 mX)
    (hframe0 : ∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ mX[a]? = m0[a]?)
    (hout : String.join out.toList = st'.out) :
    ∃ cfgD : Config, Steps cfgX cfgD ∧
      ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st' (.ret v) sp r aRet m0 cfgD := by
  obtain ⟨h176, hesp, hSLlo, hSLhi, hal⟩ := F.geom
  have hram := F.stack_ram
  have hwin := F.stack_win
  have hslot := F.ground.aret
  have hslotRam := hslot.ram
  have hslotSL := hslot.inSL
  have hslotScr := hslot.scribble_disjoint
  have hslot24 : aRet.toNat + 24 ≤ 0x100000000 := hslotRam.2
  obtain ⟨v8, hr8, hg8⟩ := F.saved_s0
  obtain ⟨v9, hr9, hg9⟩ := F.saved_s1
  obtain ⟨v18, hr18, hg18⟩ := F.saved_s2
  obtain ⟨v19, hr19, hg19⟩ := F.saved_s3
  obtain ⟨hraX, hs0X, hs1X, hs2X, hs3X⟩ := ScaffoldRows.initSomeReturn_saved_reads
    (by omega) hag F.saved_ra hr8 hr9 hr18 hr19
  -- the copy
  obtain ⟨cfgR, hsR, hHead⟩ :=
    TruthyCopy.route_of_ready retSlotCopySeg 0x80004150#64 (retSlotLds mX (sp - 176#64))
      hR
      (by change ChainOK 0x80004138#64 [10, 2, 1, 8, 9, 18, 19] retSlotCopySeg; decide) rfl
      (by change WrChainAvoids TruthyCopy.abiButS0 retSlotCopySeg; decide)
      (retSlotCopy_facts mX SL sp (sp - 176#64) _ _ aStmt aInterp aRet aEnv hcodeX
        (by rw [hesp]; omega) (by rw [hesp]; omega) hram hwin (by rw [hesp]; omega) hslot)
  have hmR := hHead.mem
  have hcopyT := retSlotCopy_total a0 (sp - 176#64) ra aStmt aInterp aRet aEnv mX hslot24
  have hframeR := retSlotCopy_frame a0 (sp - 176#64) ra aStmt aInterp aRet aEnv mX hslot24
  have hextR := retSlotCopy_memExtends a0 (sp - 176#64) ra aStmt aInterp aRet aEnv mX
  rw [← hmR] at hcopyT hframeR hextR
  -- code survives: the whole stack is disjoint from the static image
  have hcodeR : Exec_stmtLoaded cfgR.σ.mem := by
    have himg := F.ground.eval_call.image.stack_disjoint
      (lo := 0x80003fe0) (hi := 0x80004308) (by decide) (by decide)
    apply loaded_exec_stmt_agreeP mX cfgR.σ.mem _ hcodeX
    intro a ha
    exact (hframeR a (by intro hr; rcases himg with hd | hd <;> omega)).symm
  have hspR : cfgR.σ.regs.get? Register.x2 = some (sp - 176#64) :=
    gholds_lookup (n := 2) _ hHead.regs (by rfl)
  -- the epilogue
  have hpre : ExecRetEpiloguePre (sp - 176#64) r v8 v9 v18 v19 cfgR := by
    refine ⟨hHead.good, hHead.tick, hHead.pc, hHead.minstret, hspR, hcodeR, ?_, ?_, ?_, ?_,
      F.ra_align, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hesp]; omega
    · rw [hesp]; omega
    · rw [hesp]; have := tohostAddr_val; omega
    · rw [hesp]; omega
    · rw [hesp, show sp.toNat - 176 + 168 = sp.toNat - 8 by omega]
      rw [read64_agreeP (P := fun k => ¬ (aRet.toNat ≤ k ∧ k < aRet.toNat + 24))
        (fun k hk => (hframeR k hk).symm) (fun k _ => by omega)] at hraX
      exact hraX
    · rw [hesp, show sp.toNat - 176 + 160 = sp.toNat - 16 by omega]
      rw [read64_agreeP (P := fun k => ¬ (aRet.toNat ≤ k ∧ k < aRet.toNat + 24))
        (fun k hk => (hframeR k hk).symm) (fun k _ => by omega)] at hs0X
      exact hs0X
    · rw [hesp, show sp.toNat - 176 + 152 = sp.toNat - 24 by omega]
      rw [read64_agreeP (P := fun k => ¬ (aRet.toNat ≤ k ∧ k < aRet.toNat + 24))
        (fun k hk => (hframeR k hk).symm) (fun k _ => by omega)] at hs1X
      exact hs1X
    · rw [hesp, show sp.toNat - 176 + 144 = sp.toNat - 32 by omega]
      rw [read64_agreeP (P := fun k => ¬ (aRet.toNat ≤ k ∧ k < aRet.toNat + 24))
        (fun k hk => (hframeR k hk).symm) (fun k _ => by omega)] at hs2X
      exact hs2X
    · rw [hesp, show sp.toNat - 176 + 136 = sp.toNat - 40 by omega]
      rw [read64_agreeP (P := fun k => ¬ (aRet.toNat ≤ k ∧ k < aRet.toNat + 24))
        (fun k hk => (hframeR k hk).symm) (fun k _ => by omega)] at hs3X
      exact hs3X
  obtain ⟨cD, hp, htail⟩ := execRetEpilogue_run hpre
  have hmD : cD.σ.mem = cfgR.σ.mem := hp.mem
  have hspD : cD.σ.regs.get? Register.x2 = some sp := by
    simpa only [BitVec.sub_add_cancel] using hp.sp
  have hOutsideSL : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → cfgR.σ.mem[k]? = mX[k]? :=
    fun k hk => hframeR k (by intro hr; exact hk ⟨by omega, by omega⟩)
  refine ⟨cD, hsR.trans htail.steps, ?_, ?_, φf', φc', hpf, hpc, ?_⟩
  · exact
      { good := hp.good
        tick := hp.tick
        pc := by
          simpa only [show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64
            from by decide, BitVec.add_zero] using hp.pc
        a0 := hp.status
        ra := hp.ra
        spReg := hspD
        minstret := hp.minstret
        store := ⟨φf', φc', hpf, hpc, by
          rw [hmD]; exact hSurv _ (fun k hk => (hOutsideSL k hk).symm)⟩
        out := by
          change String.join cD.σ.sailOutput.toList = st'.out
          rw [hp.output, hHead.out]
          exact hout
        retval := by
          intro value hvalue
          cases hvalue
          obtain ⟨φcv, hcv, hvX⟩ := hv
          refine ⟨φcv, hcv, ?_⟩
          rw [hmD]
          exact valueRepr_copy_total_exact hcopyT (hpay.covered hframeR) hvX
        frame := by
          intro R hR
          by_cases h2 : R = Register.x2
          · subst R; exact hspD.trans F.parentSp.symm
          by_cases h8 : R = Register.x8
          · subst R; exact hp.s0.trans hg8.symm
          by_cases h9 : R = Register.x9
          · subst R; exact hp.s1.trans hg9.symm
          by_cases h18 : R = Register.x18
          · subst R; exact hp.s2.trans hg18.symm
          by_cases h19 : R = Register.x19
          · subst R; exact hp.s3.trans hg19.symm
          have hkeep : execRetEpilogueKeep R = true := by
            simp [execRetEpilogueKeep, hR.1, h2, h8, h9, h18, h19]
          have hP : TruthyCopy.abiButS0 R = true := by
            have h8' : (Register.x8 == R) = false := beq_eq_false_iff_ne.mpr (Ne.symm h8)
            unfold TruthyCopy.abiButS0; rw [hR.1, h8']; rfl
          have hg : gC R = g R := by
            rcases F.frame R hR with hs | heq
            · rcases hs with hs | hs | hs | hs | hs
              · exact False.elim (h8 hs)
              · exact False.elim (h9 hs)
              · exact False.elim (h18 hs)
              · exact False.elim (h19 hs)
              · exact False.elim (h2 hs)
            · exact heq
          exact (htail.frame.regs.eq R hkeep).trans ((hHead.frame R hP).trans hg)
        memFrame := by
          intro a hstk hA
          rw [hmD]
          by_cases hr : aRet.toNat ≤ a ∧ a < aRet.toNat + 24
          · exact Or.inl hr
          · right
            rw [hframeR a hr]
            rcases hframe0 a hstk hA with hs | heq
            · exact absurd hs hr
            · exact heq }
  · rw [hmD]
    exact hext.trans hextR
  · intro m' hag'
    rw [hmD] at hag'
    exact hSurv m' (fun k hk => (hOutsideSL k hk).symm.trans (hag' k hk))

#print axioms retSlotResume

/-- From the child's widened exit: copy the result into the retslot and run
the status-3 epilogue.  The payload premise is the only residual. -/
theorem retResume_of_payload
    {g gC : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {st st' : Vsa.While.St} {d : Nat} {env : Addr} {e : Expr} {v : Value}
    {sp r aInterp aStmt aEnv aRet aC : BitVec 64} {m0 mC : Mem}
    (hCarrier : stmtRetArm.Carrier (.ret (some e)) e g N A SL φf φc st d env
      sp r aInterp aStmt aEnv aRet m0 gC aC mC)
    (hpay : ∀ cfg : Config,
      EvalExitD gC N A SL φf φc st.store.frames.size st.store.closures.size st' v
        (sp - 176#64) stmtRetArm.retPC (stmtRetArm.sret (sp - 176#64)) mC cfg →
      PayloadOffWindow cfg.σ.mem (stmtRetArm.sret (sp - 176#64)).toNat aRet.toNat v) :
    Triple
      (EvalExitD gC N A SL φf φc st.store.frames.size st.store.closures.size st' v
        (sp - 176#64) stmtRetArm.retPC (stmtRetArm.sret (sp - 176#64)) mC)
      (ExecExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st' (.ret v) sp r aRet m0) := by
  intro cfgX hExit
  obtain ⟨φf', φc', hpf, hpc, hSurv, hKit⟩ :=
    stmtRetArm.exitKit_at_exit stmtRetArm_cert hCarrier cfgX hExit
  obtain ⟨h176, hesp, hsret, hroom, hSLhi, hal⟩ := hCarrier.geom stmtRetArm_cert
  have hoff : stmtRetArm.sretOff = 16 := rfl
  rw [hoff] at hsret
  have hsrc : (stmtRetArm.sret (sp - 176#64)).toNat = (sp - 176#64).toNat + 16 := by
    rw [hsret, hesp]
  -- saved registers survive the child
  have hag : AgreeP (fun k => sp.toNat - 40 ≤ k ∧ k < sp.toNat) mC cfgX.σ.mem := by
    intro k hk
    rcases hExit.1.memFrame k (by rw [hesp]; intro hs; omega)
        (by rcases hCarrier.ground.arena_stack with hd | hd <;> omega) with hr | heq
    · rw [hsret] at hr
      omega
    · exact heq.symm
  have hRR := stmtRetArm.routeReady_of_exit stmtRetArm_cert hCarrier cfgX hExit
  rw [show stmtRetArm.retPC = 0x80004138#64 from by decide] at hRR
  have hframe0 : ∀ a, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (aRet.toNat ≤ a ∧ a < aRet.toNat + 24) ∨ cfgX.σ.mem[a]? = m0[a]? := by
    intro a hstk hA
    rcases hExit.1.memFrame a (by rw [hesp]; intro hs; exact hstk ⟨hs.1, by omega⟩) hA
      with hs | heq
    · exfalso
      rw [hsret] at hs
      exact hstk ⟨by omega, by omega⟩
    · exact Or.inr (heq.trans (hCarrier.mem_frame a hstk))
  exact retSlotResume hCarrier.frameFacts hag hKit.code hRR hpf hpc hSurv
    (hsrc ▸ hExit.1.result) (hsrc ▸ hpay cfgX hExit)
    (hCarrier.mem_extends.trans hExit.2.1) hframe0 hKit.out

/-- `hSRet` reduces to the payload premise. -/
theorem retResumeResid_of_payload {st st' : Vsa.While.St} {d : Nat} {env : Addr} {e : Expr}
    {v : Value}
    (hpay : ∀ (g gC : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (sp r aInterp aStmt aEnv aRet aC : BitVec 64) (m0 mC : Mem),
      stmtRetArm.Carrier (.ret (some e)) e g N A SL φf φc st d env
        sp r aInterp aStmt aEnv aRet m0 gC aC mC →
      ∀ cfg : Config,
      EvalExitD gC N A SL φf φc st.store.frames.size st.store.closures.size st' v
        (sp - 176#64) stmtRetArm.retPC (stmtRetArm.sret (sp - 176#64)) mC cfg →
      PayloadOffWindow cfg.σ.mem (stmtRetArm.sret (sp - 176#64)).toNat aRet.toNat v) :
    Rows.RetResumeResid st st' d env e v :=
  fun g N A SL φf φc sp r aInterp aStmt aEnv aRet m0 gC aC mC hCarrier =>
    retResume_of_payload hCarrier
      (hpay g gC N A SL φf φc sp r aInterp aStmt aEnv aRet aC m0 mC hCarrier)

#print axioms retResume_of_payload
#print axioms retResumeResid_of_payload

end Vsa.Sim
