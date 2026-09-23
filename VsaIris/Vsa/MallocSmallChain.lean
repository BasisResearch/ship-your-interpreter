import VsaIris.Vsa.MallocSmallSegs
import VsaIris.Vsa.MallocFastChain

/-!
# Chaining the small requests' path; `malloc`'s top-split run for every request

Requests `n ≤ 23` run `segProB`, the lock call at `0x800047cc`, `segBinsB`, and
then the larger requests' stages from the top-size tests on (`st6`), with the
prologue log `proLogB` (no saved `nb`) and `nbN n = 32`. `fast_run_all` joins
both paths at the entry wrapper (`st0`); `mallocRoomRun_fast` is the resulting
`MallocRoomRun` for the fast heap.
-/

namespace VsaIris.MallocFast

open Vsa.Sim Vsa.MemRepr Vsa.Sim.DlHeap VsaIris.Inst VsaIris.VsaHeap
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Iris

/-- The small requests' prologue stores: `s0` and `ra`. -/
abbrev proLogB (s s0v r : BitVec 64) : List WEntry :=
  [(s.toNat - 96 + 80, 8, s0v), (s.toNat - 96 + 88, 8, r)]

theorem proLog_B {s : BitVec 64} (hs : SpGeom s) (s0v r : BitVec 64) :
    ProLog s s0v r (proLogB s s0v r) := by
  have := hs.lo; unfold tohostAddr at this
  refine ⟨fun a ha => ?_, fun M => ?_, fun M => ?_⟩
  · simp only [OutL]
    refine ⟨?_, ?_, trivial⟩ <;>
    · refine Classical.byContradiction fun hc => ?_
      exact ha (a - (s.toNat - 96)) (by omega) (by omega)
  · exact read64_of_writeLog_at _ _ 0 _ _ rfl (by simp only [List.drop, OutLRange, and_true]; omega)
  · exact read64_of_writeLog_at _ _ 1 _ _ rfl (by simp only [List.drop, OutLRange, and_true])

theorem proB_log {s s0 r n a0 a4 a5 : BitVec 64} (hs : SpGeom s) :
    (segOut segProB (proL s s0 r n a0 a4 a5) []).log = proLogB s s0 r := by
  have h96 := sp96 hs
  have := hs.hi
  simp only [segOut, segProB, evalBlocks, evalBlock, SegEvalState.init, wlogM, wentryM, widthOfM,
    eaddrM]
  seg_norm
  simp only [List.nil_append, List.append_nil]
  have e := fun (imm : BitVec 12) (c : Nat) (hc : (sign_extend (m := 64) imm : BitVec 64).toNat = c)
      (hcl : c ≤ 96) => add_imm (s + sign_extend (m := 64) (0xfa0#12)) imm c hc (by rw [h96]; omega)
  rw [e (0x050#12) 80 (by decide) (by omega), e (0x058#12) 88 (by decide) (by omega), h96]

theorem proB_sp (s s0 r n a0 a4 a5 : BitVec 64) :
    finReg segProB (proL s s0 r n a0 a4 a5) [] 2 = spN s := by
  simp only [finReg, segOut, segProB, evalBlocks_regs, runChain, SegEvalState.init]
  seg_norm

theorem binsB_a4 (sp a0 a1 a2 a3 a4 a5 a6 a7 t4 : BitVec 64) (f : Nat → BitVec 8) :
    finReg segBinsB (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLdsB f) 14 = BitVec.ofNat 64 32 := by
  simp only [finReg, segOut, segBinsB, evalBlocks_regs, runChain, SegEvalState.init]
  seg_norm
  decide

theorem binsB_a6 (sp a0 a1 a2 a3 a4 a5 a6 a7 t4 : BitVec 64) (f : Nat → BitVec 8) :
    finReg segBinsB (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLdsB f) 16 = 0x8001ad10#64 := by
  simp only [finReg, segOut, segBinsB, evalBlocks_regs, runChain, SegEvalState.init]
  seg_norm
  decide

theorem binsB_sp (sp a0 a1 a2 a3 a4 a5 a6 a7 t4 : BitVec 64) (f : Nat → BitVec 8) :
    finReg segBinsB (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLdsB f) 2 = sp := by
  simp only [finReg, segOut, segBinsB, evalBlocks_regs, runChain, SegEvalState.init]
  seg_norm

section StagesB

variable {live : Nat → Prop} {maxReq headroom : Nat} {H : List (Nat × Nat)} {n s r : BitVec 64}
  {saved : List (Nat × BitVec 64)} {rv0 : Nat → BitVec 64} {mv0 : Nat → BitVec 8} {k : Nat}
  {m1 : Mem} {top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}

/-- Stage 5 of a small request: back from the lock hook, at bin 4. -/
theorem stB5 (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    (hB : n.toNat ≤ 23) {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : StPost s rv0 (MtP m1 s headroom mv0 (proLogB s (rv0 8) r)) (mallocBytes vsaLayout H s headroom)
      0x800047d0#64 rv mv) :
    LocalRun (vsaModel live) roR pathText mRegs (mallocBytes vsaLayout H s headroom)
      (MallocRoomEnd vsaLayout (vsaRoomFast maxReq) H n r s saved k) 6 rv mv := by
  have hglobS : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → mallocBytes vsaLayout H s headroom a :=
    fun a h1 h2 => .inr (.inl (.inl ⟨h1, h2⟩))
  have hb := C.binsImg (proLog_B C.sp.geom (rv0 8) r) h.img
  have hnb : nbN n = 32 := by simp only [nbN]; omega
  refine seg_step segBinsB (binsL (spN s) (rv 10) (rv 11) (rv 12) (rv 13) (rv 14) (rv 15) (rv 16)
      (rv 17) (rv 29)) (binsLdsB mv) 0x800047d0#64 (avLD mv ++ []) []
    21 rfl (by change ChainOK _ [2, 10, 11, 12, 13, 14, 15, 16, 17, 29] _; decide)
    (by change KeysOK [2, 10, 11, 12, 13, 14, 15, 16, 17, 29]; decide)
    (by change ∀ x ∈ wrChain segBinsB, x ∈ [2, 10, 11, 12, 13, 14, 15, 16, 17, 29]; decide)
    (fun a _ => by show OutL [] a; trivial) C.text
    (fun c _ hcode hLD => binsB_facts hcode (avLD_pin hLD) hb)
    (by decide) h.pc ?_ ?_ (fun p hp => by cases hp) h.img ?_
  · intro p hp
    simp only [binsL, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact .inl ⟨by dsimp only; decide, h.sp⟩
    all_goals exact .inl ⟨by dsimp only; decide, rfl⟩
  · intro p hp
    rw [List.append_nil] at hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    rw [List.mem_range] at hj
    exact ⟨hglobS _ (by omega) (by omega), rfl⟩
  · intro rv' mv' hpc hL hU hI
    refine st6 C (proLog_B C.sp.geom (rv0 8) r) ⟨hpc, ?_, ?_, ?_,
      h.keep.step fun q hq => hU q ?_ ?_ ?_, fun a ha => ?_⟩
    · rw [hL (2, spN s) (by simp [binsL]), binsB_sp]
    · rw [hL (14, rv 14) (by simp [binsL]), binsB_a4, hnb]
    · rw [hL (16, rv 16) (by simp [binsL]), binsB_a6]
    · rcases hq with rfl | rfl | rfl <;> decide
    · rcases hq with rfl | rfl | rfl <;> decide
    · exact not_pin (by rcases hq with rfl | rfl | rfl <;> simp [binsL])
    · rw [hI a ha, show (segOut segBinsB (binsL (spN s) (rv 10) (rv 11) (rv 12) (rv 13) (rv 14)
        (rv 15) (rv 16) (rv 17) (rv 29)) (binsLdsB mv)).log = [] from rfl, writeLog_nil']

/-- Stage 2 of a small request: at the `jal __malloc_lock` at `0x800047cc`. -/
theorem stB2 (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    (hB : n.toNat ≤ 23) {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : StPost s rv0 (MtP m1 s headroom mv0 (proLogB s (rv0 8) r)) (mallocBytes vsaLayout H s headroom)
      0x800047cc#64 rv mv) :
    LocalRun (vsaModel live) roR pathText mRegs (mallocBytes vsaLayout H s headroom)
      (MallocRoomEnd vsaLayout (vsaRoomFast maxReq) H n r s saved k) 9 rv mv :=
  lock_call C.text 0x800047cc _ (jal_exec_800047cc live fun p hp => C.text (p.1, p.2.2)
    (jal_code jal_bytes_800047cc p hp)) (jal_code jal_bytes_800047cc) (by decide)
    (fun _ _ h' => stB5 C hB h') h

/-- Stage 1 of a small request: in `_malloc_r`, at the prologue. -/
theorem stB1 (C : FastIn live maxReq headroom H n s r saved rv0 mv0 k m1 top brkv chunks bins)
    (hB : n.toNat ≤ 23) {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (h : St1 s r n rv0 (Mt0 m1 s headroom mv0) (mallocBytes vsaLayout H s headroom) rv mv) :
    LocalRun (vsaModel live) roR pathText mRegs (mallocBytes vsaLayout H s headroom)
      (MallocRoomEnd vsaLayout (vsaRoomFast maxReq) H n r s saved k) 10 rv mv := by
  have h96 := C.sp96
  have hle := C.sp.geom.lo; have hhi := C.sp.geom.hi
  unfold tohostAddr at hle
  refine seg_step segProB (proL s (rv 8) (rv 1) (rv 11) (rv 10) (rv 14) (rv 15)) [] 0x800047a8#64 []
    (wordW mv (s.toNat - 96 + 80) ++ wordW mv (s.toNat - 96 + 88)) 8 rfl
    (by change ChainOK _ [2, 8, 1, 11, 10, 14, 15] _; decide)
    (by change KeysOK [2, 8, 1, 11, 10, 14, 15]; decide)
    (by change ∀ x ∈ wrChain segProB, x ∈ [2, 8, 1, 11, 10, 14, 15]; decide) ?_ C.text
    (fun c _ hcode _ => proB_facts hcode C.sp.geom (h.a1 ▸ hB))
    (by decide) h.pc ?_ (fun p hp => by cases hp) ?_ h.img ?_
  · intro a ha
    rw [proB_log C.sp.geom]
    have cw : ∀ b, (∀ p ∈ wordW mv b, p ∈ wordW mv (s.toNat - 96 + 80) ++
        wordW mv (s.toNat - 96 + 88)) → a < b ∨ b + 8 ≤ a := fun b hb => by
      refine Classical.byContradiction fun hc => ?_
      obtain ⟨p, hp, hpa⟩ := mem_wordW (f := mv) (a := b) (b := a) (by omega) (by omega)
      exact ha p (hb p hp) hpa
    simp only [OutL]
    refine ⟨cw _ fun p hp => ?_, cw _ fun p hp => ?_, trivial⟩
    · exact List.mem_append_left _ hp
    · exact List.mem_append_right _ hp
  · intro p hp
    simp only [proL, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact .inl ⟨by dsimp only; decide, h.sp⟩
    all_goals exact .inl ⟨by dsimp only; decide, rfl⟩
  · intro p hp
    have hw : ∀ o, o + 8 ≤ 96 → ∀ p ∈ wordW mv (s.toNat - 96 + o),
        mallocBytes vsaLayout H s headroom p.1 ∧ mv p.1 = p.2 := fun o ho p hp => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
      rw [List.mem_range] at hj
      refine ⟨?_, rfl⟩
      rw [Nat.add_assoc]; exact C.frame_owned (j := o + j) (by omega)
    rcases List.mem_append.mp hp with hp | hp
    · exact hw 80 (by omega) p hp
    · exact hw 88 (by omega) p hp
  · intro rv' mv' hpc hL hU hI
    refine stB2 C hB ⟨hpc, ?_, h.keep.step fun q hq => hU q ?_ ?_ ?_, fun a ha => ?_⟩
    · rw [hL (2, s) (by simp [proL]), proB_sp]
    · rcases hq with rfl | rfl | rfl <;> decide
    · rcases hq with rfl | rfl | rfl <;> decide
    · exact not_pin (by rcases hq with rfl | rfl | rfl <;> simp [proL])
    · rw [hI a ha, proB_log C.sp.geom, h.s0, h.ra]

end StagesB

/-- **The top-split run.** A request of at most `maxReq ≤ 487` bytes from a
fast heap with a credit left runs `malloc` to the return, carving the block
off the top: requests `n ≤ 23` through `segProB`/`segBinsB`, larger ones
through `segPro`/`segBins`. -/
theorem fast_run {live : Nat → Prop} {maxReq headroom : Nat} (hmax : maxReq ≤ 487)
    (htext : ∀ p ∈ pathText, live p.1)
    (H : List (Nat × Nat)) (n s r : BitVec 64) (saved : List (Nat × BitVec 64))
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) (k : Nat)
    (hkeys : saved.map Prod.fst = vsaSaved) (hn : n.toNat ≤ maxReq)
    (hsp : SpOKFast headroom s) (hral : r.toNat % 4 = 0)
    (hE : EntryRegs rv mallocEntryBV r n s saved)
    (hroom : vsaRoomFast maxReq mv H (k + 1))
    (hdisj : ∀ a, stackWin s headroom a → ¬ heapFoot vsaLayout H a) :
    LocalRun (vsaModel live) roR pathText mRegs (mallocBytes vsaLayout H s headroom)
      (MallocRoomEnd vsaLayout (vsaRoomFast maxReq) H n r s saved k) 11 rv mv := by
  obtain ⟨m1, top, brkv, chunks, bins, himg, hfast⟩ := hroom
  have C : FastIn live maxReq headroom H n s r saved rv mv k m1 top brkv chunks bins :=
    ⟨htext, hmax, hsp, hral, hn, hkeys, hE, hfast, himg, hdisj⟩
  refine st0 C (fun h => ?_) fun a ha => ?_
  · rcases Nat.lt_or_ge n.toNat 24 with hB | hA
    · exact stB1 C (by omega) h
    · exact st1 C hA h
  unfold imgM
  rw [stackBase_get]
  by_cases hw : s.toNat - headroom ≤ a ∧ a < s.toNat - headroom + headroom
  · rw [ite_eq_left hw]; rfl
  · rw [ite_eq_right hw]
    rcases ha with ha | ha
    · exact absurd ⟨ha.1, ha.2⟩ hw
    · rw [himg a ha]; rfl

/-- **`MallocRoomRun` for the fast heap.** With the path's code live, every
request of at most `maxReq ≤ 487` bytes is served from the top chunk. -/
theorem mallocRoomRun_fast {live : Nat → Prop} {maxReq headroom : Nat} (hmax : maxReq ≤ 487)
    (htext : ∀ p ∈ pathText, live p.1) :
    MallocRoomRun (vsaModel live) vsaLayout (vsaRoomFast maxReq) maxReq (SpOKFast headroom)
      mallocEntryBV gpV vsaClob vsaSaved headroom pathText :=
  fun H n s r saved rv mv k hkeys hn hsp hral hE _ hroom hdisj =>
    ⟨11, fast_run hmax htext H n s r saved rv mv k hkeys hn hsp hral hE hroom hdisj⟩

/-- **`DlMallocRoomImpl` for the fast heap**: `mallocRoomSpec` holds of the
binary's `malloc` for every heap in the fast shape with credits left. -/
theorem vsaDlMallocRoomImpl_fast {live : Nat → Prop} {maxReq headroom : Nat} (hmax : maxReq ≤ 487)
    (htext : ∀ p ∈ pathText, live p.1) :
    DlMallocRoomImpl (vsaModel live) vsaLayout (vsaRoomFast maxReq) maxReq (SpOKFast headroom)
      mallocEntryBV gpV vsaClob vsaSaved headroom pathText :=
  dlMallocRoomImpl_of_run (mallocRoomRun_fast hmax htext) shapeLocal_vsaLayout (roomLocal_fast maxReq)
    vsaAllocRegs_nodup

end VsaIris.MallocFast
