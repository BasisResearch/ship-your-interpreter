import VsaIris.Vsa.MallocTop
import VsaIris.Vsa.HeapGrow
import VsaIris.Vsa.Sbrk

/-!
# `malloc_extend_top`

`0x80004a48` is reached when no bin serves the request and the top chunk is
smaller than `nb + MINSIZE`. The code asks `_sbrk_r` for `nb + MINSIZE`
rounded up to a page (`sbReq`), spilling its live registers around the call.

From the page-aligned, contiguous break `PHeapAt` fixes, `sbrk` either fails
(the arena is exhausted: `Starved`) or returns exactly the old break, and the
top grows in place (`0x80004f70`). The foreign-`sbrk` paths (a non-contiguous
break, the fencepost of the old top, the `_free_r` call at `0x80005004`) are
refuted by `HeapAt.sbrk_base` and the page alignment.

* `ext_call`: the entry through the `_sbrk_r` call (`sbrk_r_run`), to the
  join `0x80004a8c` with the spills and the call's effects named (`ExtCall`).
* `ext_grow`: the success arm, through the statistics words and the top's new
  header (`PHeapAt.topGrow`), into the top split (`top_split`).
* `ext_null`: the failure arm, through the unlock to the NULL return.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- `malloc_extend_top`'s `sbrk` increment: the chunk plus `MINSIZE`, rounded
up to a page. -/
def sbReq (nb : Nat) : Nat := (nb + 4127) / 4096 * 4096

/-- The words the `_sbrk_r` call may change outside the stack window:
`brk.0`, `errno` and the reentrancy structure's `_errno`. -/
def SbrkG (a : Nat) : Prop :=
  (brkAddr ≤ a ∧ a < brkAddr + 8) ∨ (0x8001ba08 ≤ a ∧ a < 0x8001ba0c) ∨
    (0x8001b538 ≤ a ∧ a < 0x8001b53c)

/-- **Back from `_sbrk_r`** (`0x80004a8c`): the frame, the five spills
(`sbReq nb`, the top's size, `nb`, the top, `__malloc_av_`), the break `brk'`,
and the memory the heap `Mt`'s everywhere off the stack window and the words
the call may write. -/
structure ExtCall (C : MCtx) (Mt : Mem) (nb topsz brk' : Nat) (R : Nat → BitVec 64)
    (M : Mem) : Prop where
  frame : MFrame C R M
  s0 : R 8 = reentV
  sb : read64 M (C.s.toNat - 96 + 8) = some (sbReq nb)
  t1 : read64 M (C.s.toNat - 96 + 16) = some topsz
  a4 : read64 M (C.s.toNat - 96 + 24) = some nb
  a5 : read64 M (C.s.toNat - 96 + 32) = some C.top0
  a6 : read64 M (C.s.toNat - 96 + 40) = some 0x8001ad10
  brk : read64 M brkAddr = some brk'
  agree : ∀ a : Nat, ¬ (C.s.toNat - mHead ≤ a ∧ a < C.s.toNat) → ¬ SbrkG a → M[a]? = Mt[a]?
  pres : ∀ a : Nat, (Mt[a]?).isSome → (M[a]?).isSome

/-- The spills `malloc_extend_top` leaves around its `_sbrk_r` call. -/
structure ExtSpills (C : MCtx) (Mt Mp : Mem) (nb topsz : Nat) : Prop where
  sb : read64 Mp (C.s.toNat - 96 + 8) = some (sbReq nb)
  t1 : read64 Mp (C.s.toNat - 96 + 16) = some topsz
  a4 : read64 Mp (C.s.toNat - 96 + 24) = some nb
  a5 : read64 Mp (C.s.toNat - 96 + 32) = some C.top0
  a6 : read64 Mp (C.s.toNat - 96 + 40) = some 0x8001ad10
  agree : ∀ a : Nat, ¬ (C.s.toNat - 96 + 8 ≤ a ∧ a < C.s.toNat - 96 + 48) → Mp[a]? = Mt[a]?
  pres : ∀ a : Nat, (Mt[a]?).isSome → (Mp[a]?).isSome

/-- `ExtCall` from the spills and the call's `SbrkPost`. -/
theorem ExtCall.of_post {C : MCtx} (O : MOK C) {R Rc R' : Nat → BitVec 64} {Mt Mp M : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    {nb topsz brk' : Nat} (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins) (h8 : R 8 = reentV)
    (hc2 : Rc 2 = R 2) (hc8 : Rc 8 = R 8) (hc9 : Rc 9 = R 9) (hc18 : Rc 18 = R 18)
    (hc19 : Rc 19 = R 19) (Sp : ExtSpills C Mt Mp nb topsz) (P : SbrkPost Rc R' Mp M brk') :
    ExtCall C Mt nb topsz brk' R' M := by
  have hlo := O.sp.lo; have hhi := O.sp.hi
  unfold mHead Vsa.Sim.tohostAddr at hlo
  obtain ⟨hgo1, hgo2⟩ := Hp.glob_off
  unfold mHead at hgo1 hgo2
  have hs2 : (Rc 2).toNat = C.s.toNat - 96 := by rw [hc2, F.sp]; sx_addr
  have hslot : ∀ o, o + 8 ≤ 96 → read64 M (C.s.toNat - 96 + o) = read64 Mp (C.s.toNat - 96 + o) :=
    fun o ho => read64_keep fun k hk => P.agree _ (by
      unfold SbrkW brkAddr; rw [hs2]; omega)
  have hkeep : ∀ o, o + 8 ≤ 96 → (o + 8 ≤ 8 ∨ 48 ≤ o) →
      read64 Mp (C.s.toNat - 96 + o) = read64 Mt (C.s.toNat - 96 + o) :=
    fun o ho ho' => read64_keep fun k hk => Sp.agree _ (by omega)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, P.brk, ?_, ?_⟩
  · rw [P.regs 2 (by decide) (by decide) (by decide), hc2]; exact F.sp
  · rw [hslot 80 (by omega), hkeep 80 (by omega) (by omega)]; exact F.s0
  · rw [hslot 88 (by omega), hkeep 88 (by omega) (by omega)]; exact F.ra
  · rw [P.regs 9 (by decide) (by decide) (by decide), hc9]; exact F.s1
  · rw [P.regs 18 (by decide) (by decide) (by decide), hc18]; exact F.s2
  · rw [P.regs 19 (by decide) (by decide) (by decide), hc19]; exact F.s3
  · rw [P.regs 8 (by decide) (by decide) (by decide), hc8]; exact h8
  · rw [hslot 8 (by omega)]; exact Sp.sb
  · rw [hslot 16 (by omega)]; exact Sp.t1
  · rw [hslot 24 (by omega)]; exact Sp.a4
  · rw [hslot 32 (by omega)]; exact Sp.a5
  · rw [hslot 40 (by omega)]; exact Sp.a6
  · intro a hw hg
    unfold SbrkG at hg
    unfold mHead at hw
    rw [P.agree a (by unfold SbrkW; rw [hs2]; omega), Sp.agree a (by omega)]
  · exact fun a h => P.pres a (Sp.pres a h)

/-- The `_sbrk_r` call itself, from its entry with the spills in place. -/
theorem ext_sbrk {C : MCtx} (O : MOK C) {R Rc : Nat → BitVec 64} {Mt Mp : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb topsz sb : Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins) (h8 : R 8 = reentV)
    (hc2 : Rc 2 = R 2) (hc8 : Rc 8 = R 8) (hc9 : Rc 9 = R 9) (hc18 : Rc 18 = R 18)
    (hc19 : Rc 19 = R 19) (hc1 : Rc 1 = 0x80004a8c#64) (Sp : ExtSpills C Mt Mp nb topsz)
    (Pre : SbrkPre C.S Rc Mp brkv sb)
    (hok : brkv + sb ≤ heapEnd → ∀ R' M, ExtCall C Mt nb topsz (brkv + sb) R' M →
      R' 10 = BitVec.ofNat 64 brkv → AW C.live C.S C.Q 0x80004a8c#64 R' M)
    (hfail : heapEnd < brkv + sb → ∀ R' M, ExtCall C Mt nb topsz brkv R' M →
      R' 10 = 18446744073709551615#64 → AW C.live C.S C.Q 0x80004a8c#64 R' M) :
    AW C.live C.S C.Q 0x8000696c#64 Rc Mp :=
  sbrk_r_run O.live Pre
    (fun hle R' M P' h10 => hc1 ▸ hok hle R' M
      (ExtCall.of_post O F Hp h8 hc2 hc8 hc9 hc18 hc19 Sp P') h10)
    (fun hlt R' M P' h10 => hc1 ▸ hfail hlt R' M
      (ExtCall.of_post O F Hp h8 hc2 hc8 hc9 hc18 hc19 Sp P') h10)

/-- The call's setup: from `0x80004a48` to `_sbrk_r`'s entry, the increment
formed and the live registers spilled. -/
theorem ext_setup {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb idx : Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins)
    (G : LRRegs nb idx R) (T : TopRegs nb C.top0 (brkv - C.top0) R) (h8 : R 8 = reentV)
    (hnb31 : nb < 2 ^ 31)
    (hok : brkv + sbReq nb ≤ heapEnd → ∀ R' M, ExtCall C Mt nb (brkv - C.top0) (brkv + sbReq nb) R' M →
      R' 10 = BitVec.ofNat 64 brkv → AW C.live C.S C.Q 0x80004a8c#64 R' M)
    (hfail : heapEnd < brkv + sbReq nb → ∀ R' M, ExtCall C Mt nb (brkv - C.top0) brkv R' M →
      R' 10 = 18446744073709551615#64 → AW C.live C.S C.Q 0x80004a8c#64 R' M) :
    AW C.live C.S C.Q 0x80004a48#64 R Mt := by
  have HH := Hp.heap.heap.heap
  have ha4 := T.a4; have ha5 := T.a5; have ht1 := T.t1; have ha6 := G.a6
  have hs2 := F.sp
  have hlo := O.sp.lo; have hhi := O.sp.hi
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hsal := O.sp.align
  have hs2n : (R 2).toNat = C.s.toNat - 96 := by rw [hs2]; sx_addr
  obtain ⟨hgo1, hgo2⟩ := Hp.glob_off
  unfold mHead at hgo1 hgo2
  sx_run [2] O.live
  simp (disch := decide) only [ldv_at HH.top_pad, ldv_at HH.sbrk_base]
  sx_run [30] O.live at 0x80004a58
  refine st_80004a58 O.live (fun h => absurd h (by sx_norm; unfold heapStart; decide)) (fun _ => ?_)
  sx_run [30] O.live at 0x8000696c
  have hbrk := HH.brk; have hbrkle := HH.brk_le; have hstart := HH.walk.le
  have htle := HH.top_le
  unfold heapStart at hstart; unfold heapEnd at hbrkle
  have hSB : (R 14 + 4127#64 &&& 18446744073709547520#64).toNat = sbReq nb := by
    rw [show (18446744073709547520#64 : BitVec 64) = BitVec.allOnes 64 <<< 12 by decide,
      and_high_toNat _ 12 (by decide), BitVec.toNat_add, ha4]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt (by omega)]
    rfl
  have hsbl : sbReq nb ≤ nb + 4127 := by unfold sbReq; omega
  refine ext_sbrk O F Hp h8 ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hok hfail <;>
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  all_goals try (simp (disch := sx_addr) only [read64_hit_eq, read64_miss])
  · rw [hSB]
  · rw [ht1]
  · rw [ha4]
  · rw [ha5]
  · rw [ha6]; rfl
  · intro a ha
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;>
      simp only [OutL, and_true] <;> sx_addr
  · intro a h
    exact writeLog_present _ _ _ (writeLog_present _ _ _ (writeLog_present _ _ _
      (writeLog_present _ _ _ (writeLog_present _ _ _ h))))
  · exact hSB
  · unfold sbReq; omega
  · unfold brkAddr
    simp (disch := sx_addr) only [read64_miss]
    exact hbrk
  · omega
  · unfold heapEnd; omega
  · unfold Vsa.Sim.tohostAddr; omega
  · omega
  · omega
  · decide
  · omega
  · omega
  · intro a ha
    unfold SbrkW brkAddr at ha
    refine O.own a ?_
    rcases ha with h | h | h | h
    · exact .inr ⟨by unfold mHead; omega, by omega⟩
    all_goals exact .inl (.inl (by unfold allocGlobal InRange; omega))

/-- The second statistics word (`0x80004bd4`). -/
theorem ext_stats2 {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {M : Mem}
    (hk : ∀ R' M', (∀ x, x ≠ 15 → R' x = R x) →
      (∀ a : Nat, ¬ (0x8001b998 ≤ a ∧ a < 0x8001b9a0) → M'[a]? = M[a]?) →
      (∀ a : Nat, (M[a]?).isSome → (M'[a]?).isSome) → AW C.live C.S C.Q 0x80004be0#64 R' M') :
    AW C.live C.S C.Q 0x80004bd4#64 R M := by
  refine st_80004bd4 O.live (by sx_norm; sx_side) ?_
  refine st_80004bd8 O.live (fun _ => hk _ _ (fun x hx => upd_other _ _ hx) (fun _ _ => rfl)
    (fun _ h => h)) (fun _ => ?_)
  refine st_80004bdc O.live (by sx_norm; sx_side) ?_
  sx_norm
  refine hk _ _ (fun x hx => upd_other _ _ hx) (fun a ha => ?_) (fun a h => writeLog_present _ _ _ h)
  rw [writeLog_out _ _ _ (by simp only [OutL, and_true]; omega)]

/-- **The statistics words** (`0x80004bc8`): `__malloc_max_sbrked_mem` and
`__malloc_max_total_mem` rise to the arena size in `a3`. Either word may or
may not be written; nothing else changes but `a5`. -/
theorem ext_stats {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {M : Mem}
    (hms : (read64 M maxSbrkedAddr).isSome)
    (hk : ∀ R' M', (∀ x, x ≠ 15 → R' x = R x) →
      (∀ a : Nat, ¬ (0x8001b998 ≤ a ∧ a < 0x8001b9a8) → M'[a]? = M[a]?) →
      (read64 M' maxSbrkedAddr).isSome → (∀ a : Nat, (M[a]?).isSome → (M'[a]?).isSome) →
      AW C.live C.S C.Q 0x80004be0#64 R' M') :
    AW C.live C.S C.Q 0x80004bc8#64 R M := by
  unfold maxSbrkedAddr at hms hk
  refine st_80004bc8 O.live (by sx_norm; sx_side) ?_
  refine st_80004bcc O.live (fun _ => ?_) (fun _ => ?_)
  · refine ext_stats2 O fun R' M' hR hM hP => hk R' M' (fun x hx => by
      rw [hR x hx, upd_other _ _ hx]) (fun a ha => hM a (by omega)) ?_ hP
    rw [read64_keep fun k hk => hM _ (by omega)]; exact hms
  · refine st_80004bd0 O.live (by sx_norm; sx_side) ?_
    sx_norm
    refine ext_stats2 O fun R' M' hR hM hP => hk R' M' (fun x hx => by
      rw [hR x hx, upd_other _ _ hx]) (fun a ha => ?_) ?_ (fun a h => hP a (writeLog_present _ _ _ h))
    · rw [hM a (by omega), writeLog_out _ _ _ (by simp only [OutL, and_true]; omega)]
    · rw [read64_keep fun k hk => hM _ (by omega), read64_store_hit]; rfl

/-- **Into the split** (`0x80004be0`): the grown top, its header in `a2`,
measured against the request and split (`top_split`). -/
theorem ext_top {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {M : Mem}
    {brk' : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb : Nat}
    (F : MFrame C R M) (Hp : MHeap C M brk' chunks bins) (hnb : NbOK C.n nb) (hnb31 : nb < 2 ^ 31)
    (h28 : (R 28).toNat = C.top0) (h12 : (R 12).toNat = brk' - C.top0 + 1)
    (h14 : (R 14).toNat = nb) (h16 : R 16 = 0x8001ad10#64) (hroom : C.top0 + nb + 32 ≤ brk') :
    AW C.live C.S C.Q 0x80004be0#64 R M := by
  have HH := Hp.heap.heap.heap
  have hbrkle := HH.brk_le; have hstart := HH.walk.le; have htle := HH.top_le
  have hts := HH.top_size
  unfold heapStart at hstart; unfold heapEnd at hbrkle
  have hnb16 := hnb.al
  sx_run [8] O.live at 0x80004e18
  have hA : ((R 12 &&& 18446744073709551612#64)).toNat = brk' - C.top0 := by
    rw [toNat_and_m4, h12]; omega
  have hsub : ((R 12 &&& 18446744073709551612#64) - R 14).toInt = ((brk' - C.top0 - nb : Nat) : Int) :=
    sub_toInt hA h14 (by omega) (by omega)
  refine st_80004e18 O.live (fun _ => ?k) (fun hc => absurd ?e hc)
  case e =>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [sltiV_eq_zero, hsub, show ((32#64 : BitVec 64)).toInt = (32 : Int) by decide]
    omega
  refine top_split O (F.of_regs ?_ ?_ ?_ ?_) Hp ⟨?_, ?_, ?_, ?_⟩ hnb hroom <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact h28
  · exact h14
  · rw [BitVec.toNat_sub, hA, h14]; omega
  · exact h16

/-- **The top grows in place** (`0x80004a8c`, `sbrk` succeeded): reload the
spills, add the increment to `mallinfo`, check the break is contiguous and
page-aligned, write the top's new header, update the statistics, and split
the grown top. -/
theorem ext_grow {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt M : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb : Nat}
    (Hp : MHeap C Mt brkv chunks bins) (hnb : NbOK C.n nb) (hnb31 : nb < 2 ^ 31)
    (hsmall : brkv - C.top0 < nb + 32) (hle : brkv + sbReq nb ≤ heapEnd)
    (E : ExtCall C Mt nb (brkv - C.top0) (brkv + sbReq nb) R M)
    (h10 : R 10 = BitVec.ofNat 64 brkv) :
    AW C.live C.S C.Q 0x80004a8c#64 R M := by
  have HH := Hp.heap.heap.heap
  have hlo := O.sp.lo; have hhi := O.sp.hi
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hsal := O.sp.align
  have hs2 := E.frame.sp
  have hs2n : (R 2).toNat = C.s.toNat - 96 := by rw [hs2]; sx_addr
  obtain ⟨hgo1, hgo2⟩ := Hp.glob_off
  unfold mHead at hgo1 hgo2
  have hbrkle := HH.brk_le; have hstart := HH.walk.le; have htle := HH.top_le
  have hpage := Hp.heap.brk_page
  unfold heapStart at hstart; unfold heapEnd at hbrkle hle
  have hsbl : sbReq nb ≤ nb + 4127 := by unfold sbReq; omega
  have hsbg : nb + 32 ≤ sbReq nb := by unfold sbReq; omega
  have hsb16 : sbReq nb % 4096 = 0 := by unfold sbReq; omega
  -- reload the spills
  rw [← upd_self_eq h10]
  sx_run [8] O.live at 0x80004aa4
  simp (disch := sx_addr) only [ldv_at E.sb, ldv_at E.t1, ldv_at E.a4, ldv_at E.a5, ldv_at E.a6]
  sx_run [8] O.live at 0x80004abc
  -- words the call left alone read as in the heap `Mt`
  have hkeep : ∀ a, (∀ k, k < 8 → vsaFoot C.H (a + k)) → (∀ k, k < 8 → ¬ SbrkG (a + k)) →
      read64 M a = read64 Mt a := fun a hf hg => read64_keep fun k hk =>
    E.agree _ (fun hw => Hp.disj _ hw.1 hw.2 (hf k hk)) (hg k hk)
  have hglob : ∀ a, (∀ k, k < 8 → allocGlobal (a + k)) → (∀ k, k < 8 → ¬ SbrkG (a + k)) →
      read64 M a = read64 Mt a := fun a hg hs => hkeep a (fun k hk => .inl (hg k hk)) hs
  obtain ⟨mi, hmi⟩ := Option.isSome_iff_exists.1 HH.mallinfo
  have hmiM : read64 M mallinfoAddr = some mi := by
    rw [hglob _ (fun k hk => by unfold mallinfoAddr allocGlobal InRange; omega)
      (fun k hk => by unfold mallinfoAddr SbrkG brkAddr; omega)]; exact hmi
  have htopM : read64 M topAddr = some C.top0 := by
    rw [hglob _ (fun k hk => by unfold topAddr avAddr allocGlobal InRange; omega)
      (fun k hk => by unfold topAddr avAddr SbrkG brkAddr; omega)]; exact HH.top_ptr
  unfold mallinfoAddr at hmiM
  sx_run [1] O.live
  simp (disch := sx_addr) only [ldv_at hmiM]
  sx_run [8] O.live at 0x80004f78
  unfold topAddr avAddr at htopM
  sx_run [1] O.live
  simp (disch := sx_addr) only [ldv_at htopM]
  sx_run [2] O.live at 0x80004f84
  have hhd := foot_header Hp.heap.heap (.inl rfl)
  have htop16 := HH.aligned.2
  have hroom0 := Hp.heap.heap.top_room
  have hoffH := Hp.off_stack hhd
  unfold mHead at hoffH
  refine st_80004f84 O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot_at hhd _ (by sx_addr)
  sx_norm
  refine st_80004f88 O.live ?_
  have hmsM : (read64 M maxSbrkedAddr).isSome := by
    rw [hglob _ (fun k hk => by unfold maxSbrkedAddr allocGlobal InRange; omega)
      (fun k hk => by unfold maxSbrkedAddr SbrkG brkAddr; omega)]; exact HH.max_sbrked
  refine ext_stats O ?_ (fun R' M' hR hM hms' hP => ?_)
  · unfold maxSbrkedAddr at hmsM ⊢
    simp (disch := sx_addr) only [read64_miss]
    exact hmsM
  -- the frame and the grown heap after the statistics
  have hT8 : (BitVec.ofNat 64 C.top0 + 8#64).toNat = C.top0 + 8 := by sx_addr
  rw [hT8] at hM hP
  have hts := HH.top_size
  have hv : (BitVec.ofNat 64 (brkv - C.top0) + BitVec.ofNat 64 (sbReq nb) ||| 1#64).toNat =
      brkv + sbReq nb - C.top0 + 1 := or1_toNat (by sx_addr) (by omega)
  have hM' : ∀ a : Nat, ¬ (0x8001b998 ≤ a ∧ a < 0x8001b9a8) → ¬ (0x8001ba18 ≤ a ∧ a < 0x8001ba20) →
      ¬ (C.top0 + 8 ≤ a ∧ a < C.top0 + 16) → M'[a]? = M[a]? := by
    intro a h1 h2 h3
    rw [hM a h1, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  have hslot : ∀ o, 16 ≤ o → o + 8 ≤ 96 → read64 M' (C.s.toNat - 96 + o) = read64 M (C.s.toNat - 96 + o) :=
    fun o h1 h2 => read64_keep fun k hk => hM' _ (by omega) (by omega) (by omega)
  have F' : MFrame C R' M' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hR 2 (by decide)]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact E.frame.sp
    · rw [hslot 80 (by omega) (by omega)]; exact E.frame.s0
    · rw [hslot 88 (by omega) (by omega)]; exact E.frame.ra
    · rw [hR 9 (by decide)]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact E.frame.s1
    · rw [hR 18 (by decide)]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact E.frame.s2
    · rw [hR 19 (by decide)]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact E.frame.s3
  have hgw : ∀ a, 0x8001b998 ≤ a ∧ a < 0x8001b9a8 ∨ 0x8001ba18 ≤ a ∧ a < 0x8001ba20 → allocGlobal a := by
    intro a h; unfold allocGlobal InRange; omega
  have Hp' : MHeap C M' (brkv + sbReq nb) chunks bins := by
    refine ⟨Hp.heap.topGrow (m' := M') (by omega) (by unfold heapEnd; omega) (by omega) ?_ ?_ ?_ hms' ?_,
      fun a ha => hP a (writeLog_present _ _ _ (writeLog_present _ _ _ (E.pres a (Hp.pres a ha)))),
      Hp.disj, fun a ha => ?_⟩
    · rw [read64_keep fun k hk => hM' _ (by unfold brkAddr; omega) (by unfold brkAddr; omega)
        (by unfold brkAddr; omega)]
      exact E.brk
    · rw [read64_keep fun k hk => hM _ (by omega), read64_store_hit, hv]
    · rw [read64_keep fun k hk => hM _ (by unfold mallinfoAddr; omega)]
      unfold mallinfoAddr
      rw [read64_store_miss _ _ (by omega), read64_store_hit]; rfl
    · intro a hf hg
      unfold GrowW at hg
      rw [hM' a (by unfold brkAddr topPadAddr at hg; omega) (by unfold mallinfoAddr at hg; omega)
        (by omega)]
      exact E.agree a (fun hw => Hp.disj a hw.1 hw.2 hf) (by unfold SbrkG brkAddr; unfold brkAddr topPadAddr at hg; omega)
    · have hnf : ¬ vsaFoot C.H a := fun h => ha (.inl h)
      have hng : ¬ allocGlobal a := fun h => hnf (.inl h)
      rw [hM' a (fun h => hng (hgw a (.inl h))) (fun h => hng (hgw a (.inr h)))
        (fun h => hnf (hhd (a - (C.top0 + 8)) (by omega) |> fun h' => by
          rwa [show C.top0 + 8 + (a - (C.top0 + 8)) = a by omega] at h'))]
      rw [E.agree a (fun hw => ha (.inr hw)) (fun hs => hng (by
        unfold SbrkG brkAddr at hs; unfold allocGlobal InRange; omega))]
      exact Hp.frame a ha
  refine ext_top O F' Hp' hnb hnb31 ?_ ?_ ?_ ?_ (by omega) <;>
    rw [hR _ (by decide)] <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  all_goals first | sx_addr | (rw [hv]; omega)

/-- **The NULL return after a failed extension** (`0x80004e1c`): unlock and
return NULL, the heap in shape at the same live blocks. -/
theorem null_tail {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {M : Mem}
    {brk' : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (F : MFrame C R M) (Hp : MHeap C M brk' chunks bins) (hst : Starved C.top0 C.n.toNat) :
    AW C.live C.S C.Q 0x80004e1c#64 R M := by
  sx_run [8] O.live at 0x8000484c
  exact epi_8000484c O (F.of_regs (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]))
    (O.fin_null (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; decide)
      ⟨_, _, _, _, Hp.heap⟩ Hp.pres Hp.frame hst)

/-- **`sbrk` failed** (`0x80004a8c`, `a0 = -1`): the top still cannot hold the
request, so unlock and return NULL. The arena is exhausted (`Starved`). -/
theorem ext_null {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt M : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb : Nat}
    (Hp : MHeap C Mt brkv chunks bins) (hnb : NbOK C.n nb) (hnb31 : nb < 2 ^ 31)
    (hsmall : brkv - C.top0 < nb + 32) (hlt : heapEnd < brkv + sbReq nb)
    (E : ExtCall C Mt nb (brkv - C.top0) brkv R M)
    (h10 : R 10 = 18446744073709551615#64) :
    AW C.live C.S C.Q 0x80004a8c#64 R M := by
  have HH := Hp.heap.heap.heap
  have hlo := O.sp.lo; have hhi := O.sp.hi
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hsal := O.sp.align
  have hs2 := E.frame.sp
  have hs2n : (R 2).toNat = C.s.toNat - 96 := by rw [hs2]; sx_addr
  obtain ⟨hgo1, hgo2⟩ := Hp.glob_off
  unfold mHead at hgo1 hgo2
  have hbrkle := HH.brk_le; have hstart := HH.walk.le; have htle := HH.top_le
  unfold heapStart at hstart; unfold heapEnd at hbrkle hlt
  have hsbl : sbReq nb ≤ nb + 4127 := by unfold sbReq; omega
  have hP : nb = physSize C.n.toNat := hnb.eq
  -- the heap is the entry heap: `sbrk` failed and left the break alone
  have Hp' : MHeap C M brkv chunks bins := by
    refine ⟨Hp.heap.transport_read fun a ha => ?_, fun a ha => E.pres a (Hp.pres a ha), Hp.disj,
      fun a ha => ?_⟩
    · obtain ⟨hf, hn1, hn2⟩ := ha
      by_cases hb : brkAddr ≤ a ∧ a < brkAddr + 8
      · have := bytes_of_read64_eq HH.brk E.brk (a - brkAddr) (by omega)
        rw [show brkAddr + (a - brkAddr) = a by omega] at this
        exact this.symm
      · exact (E.agree a (fun hw => Hp.disj a hw.1 hw.2 hf) (by
          unfold SbrkG; unfold InRange at hn1 hn2; omega)).symm
    · have hng : ¬ allocGlobal a := fun h => ha (.inl (.inl h))
      rw [E.agree a (fun hw => ha (.inr hw)) (fun hs => hng (by
        unfold SbrkG brkAddr at hs; unfold allocGlobal InRange; omega))]
      exact Hp.frame a ha
  have hst : Starved C.top0 C.n.toNat := by
    unfold Starved extendSlack heapEnd; rw [← hP]; omega
  rw [← upd_self_eq h10]
  sx_run [8] O.live at 0x80004aa4
  simp (disch := sx_addr) only [ldv_at E.sb, ldv_at E.t1, ldv_at E.a4, ldv_at E.a5, ldv_at E.a6]
  sx_run [8] O.live at 0x80004e00
  have HH' := Hp'.heap.heap.heap
  have htp := HH'.top_ptr
  unfold topAddr avAddr at htp
  sx_run [1] O.live
  simp (disch := sx_addr) only [ldv_at htp]
  have hhd := foot_header Hp'.heap.heap (.inl rfl)
  have htop16 := HH.aligned.2
  have hroom0 := Hp.heap.heap.top_room
  have hts := HH.top_size
  refine st_80004e04 O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot_at hhd _ (by sx_addr)
  sx_norm
  simp (disch := sx_addr) only [ldv_at HH'.top_header]
  sx_run [3] O.live at 0x80004e10
  have hA : ((BitVec.ofNat 64 (brkv - C.top0 + 1)) &&& 18446744073709551612#64).toNat = brkv - C.top0 := by
    rw [toNat_and_m4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hN : (BitVec.ofNat 64 nb).toNat = nb := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have F' : MFrame C R M := E.frame
  refine st_80004e10 O.live (fun _ => null_tail O (F'.of_regs ?_ ?_ ?_ ?_) Hp' hst) (fun hge => ?_)
  rotate_left 4
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hge
    rw [hA, hN] at hge
    have hsub : ((BitVec.ofNat 64 (brkv - C.top0 + 1) &&& 18446744073709551612#64) -
        BitVec.ofNat 64 nb).toInt = ((brkv - C.top0 - nb : Nat) : Int) :=
      sub_toInt hA hN (by omega) (by omega)
    refine st_80004e14 O.live ?_
    refine st_80004e18 O.live (fun hc => absurd hc ?_) (fun _ => null_tail O (F'.of_regs ?_ ?_ ?_ ?_) Hp' hst)
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      rw [sltiV_eq_zero, hsub,
        show (sign_extend (m := 64) (0x020#12) : BitVec 64).toInt = (32 : Int) by decide]
      omega
    all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]

/-- **`malloc_extend_top`** (`0x80004a48`): grow the top by `sbrk` and split
it, or return NULL when the arena is exhausted. -/
theorem extend_top {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb idx : Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins)
    (G : LRRegs nb idx R) (T : TopRegs nb C.top0 (brkv - C.top0) R) (h8 : R 8 = reentV)
    (hnb : NbOK C.n nb) (hnb31 : nb < 2 ^ 31) (hsmall : brkv - C.top0 < nb + 32) :
    AW C.live C.S C.Q 0x80004a48#64 R Mt :=
  ext_setup O F Hp G T h8 hnb31
    (fun hle _ _ E h10 => ext_grow O Hp hnb hnb31 hsmall hle E h10)
    (fun hlt _ _ E h10 => ext_null O Hp hnb hnb31 hsmall hlt E h10)

end VsaIris.VsaHeap
