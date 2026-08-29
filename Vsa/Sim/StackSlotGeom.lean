import Vsa.Sim.EvalSimCommon

/-!
# `StackSlotGeom` — precomputed per-slot geometry facts (Phase-0 omega-hog kill)

The binop value-arm rows (`blockC_mul`, `blockC_div`, and the Phase-4 clones) pass,
at EVERY load/store site, four geometry side-conditions about the spill address
`sp.toNat - K`:

* `lo`  : `0x80000000 ≤ sp.toNat - K`               (RAM lower bound)
* `hi`  : `sp.toNat - K + w ≤ 0x100000000`           (RAM upper bound)
* `ht`  : `… ≤ tohostAddr ∨ tohostAddr + 8 ≤ …`       (htif disjointness — right disjunct)
* `al`  : `(sp.toNat - K) % align = 0`               (alignment)

In the hand rows these were re-`omega`'d at every site (`(by rw [haddrK]; omega)`),
paying omega's fixed per-invocation + full-local-context cost ~76×/30× per row
(≈46s of `blockC_mul`'s 60s, ≈28s of `blockC_div`'s 36s — MEASURED).

Every one of those facts is a function of `sp.toNat`, `SL`, and the constant `K`
against a FIXED, small bundle of stack-window bounds (`StackBounds`).  This file
factors them out: `StackBounds` packs the bounds once; `slotGeom8`/`slotGeom4`
prove the whole four-tuple for a slot in ONE `omega` over the tiny `StackBounds`
context (not the row's 40+-hypothesis body).  The row extracts `StackBounds`
once, precomputes `have geoK := slotGeom8 hSB K …` per distinct offset, and each
site consumes `geoK.lo/.hi/.ht/.al` by projection — ZERO omega at the callsite.

`NO sorry/axiom/native_decide/bv_decide`.
-/

open Vsa
open Vsa.Alloc

namespace Vsa.Sim

/-- The fixed, small bundle of stack-window bounds every spill-slot geometry fact
needs.  Extracted ONCE from the row's precondition; consumed by `slotGeom4/8`. -/
structure StackBounds (sp : BitVec 64) (SL : StackLayout) : Prop where
  /-- `sp` is at least `1088` above `SL.lo` (the frame size). -/
  SLloSp : SL.lo + 1088 ≤ sp.toNat
  /-- `SL.lo` is in RAM. -/
  SLlo : 0x80000000 ≤ SL.lo
  /-- `SL.lo` is safely above the htif window. -/
  SLwin : tohostAddr + 16 ≤ SL.lo
  /-- `sp` is 8-aligned. -/
  sp8 : sp.toNat % 8 = 0
  /-- `sp` is within RAM. -/
  sphiRam : sp.toNat ≤ 0x100000000

/-- The geometry facts for the 8-aligned stack slot at `sp.toNat - K`, exposed for
BOTH a 4-byte and an 8-byte access (the same `haddrK`-normalised slot is read at
either width across sites), plus both alignments.  Every field is a projection —
no omega at the callsite. -/
structure SlotGeom (sp : BitVec 64) (K : Nat) : Prop where
  lo  : 0x80000000 ≤ sp.toNat - K
  hi4 : sp.toNat - K + 4 ≤ 0x100000000
  hi8 : sp.toNat - K + 8 ≤ 0x100000000
  ht4 : sp.toNat - K + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ sp.toNat - K
  ht8 : sp.toNat - K + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ sp.toNat - K
  win : tohostAddr + 16 ≤ sp.toNat - K
  al4 : (sp.toNat - K) % 4 = 0
  al8 : (sp.toNat - K) % 8 = 0

/-- Build all geometry facts for an 8-aligned stack slot `sp.toNat - K` from
`StackBounds`.  The `omega` runs against the FIVE `StackBounds` fields + the two
ground side-hypotheses (`K ≤ 1088`, `K % 8 = 0`) only — a tiny context, so it is
fast; paid ONCE per distinct `K` `have` in the row, not per site. -/
theorem slotGeom8 {sp : BitVec 64} {SL : StackLayout} (hSB : StackBounds sp SL)
    (K : Nat) (hKlo : 8 ≤ K) (hK : K ≤ 1088) (hKal : K % 8 = 0) :
    SlotGeom sp K := by
  obtain ⟨hSLloSp, hSLlo, hSLwin, hsp8, hsphiRam⟩ := hSB
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hsp : 1088 ≤ sp.toNat := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · exact Or.inr (by omega)
  · exact Or.inr (by omega)
  · omega
  · omega
  · omega

/-- The three MUL/DIV store slots' disjointness from a single static region
`[rlo, rhi)` (code / value_int / __muldi3), packaged so the row adds ONE
hypothesis instead of nine `have`s (per the elab-wall context-bloat law).
Built from the row's single per-region `hStk : sp.toNat ≤ rlo ∨ rhi ≤ SL.lo`. -/
structure StoreRegionDis (sp : BitVec 64) (SL : StackLayout) (rlo rhi : Nat) : Prop where
  d848 : (sp.toNat - 848) + 8 ≤ rlo ∨ rhi ≤ (sp.toNat - 848)
  d840 : (sp.toNat - 840) + 8 ≤ rlo ∨ rhi ≤ (sp.toNat - 840)
  d832 : (sp.toNat - 832) + 8 ≤ rlo ∨ rhi ≤ (sp.toNat - 832)

/-- Build `StoreRegionDis` from the stack-vs-region hypothesis `hStk` and
`StackBounds`.  All three `omega`s run against the tiny bundle context (paid
ONCE), not the row's 40+-hyp body. -/
theorem storeRegionDis {sp : BitVec 64} {SL : StackLayout} (hSB : StackBounds sp SL)
    (rlo rhi : Nat) (hStk : sp.toNat ≤ rlo ∨ rhi ≤ SL.lo) :
    StoreRegionDis sp SL rlo rhi := by
  obtain ⟨hSLloSp, hSLlo, hSLwin, hsp8, hsphiRam⟩ := hSB
  refine ⟨?_, ?_, ?_⟩ <;> (rcases hStk with h | h <;> omega)

/-- All the scalar `sp`/`SL` arithmetic facts the row needs, bundled so the row
computes them via ONE small-context lemma call (each `omega` paid here, over the
tiny `StackBounds` context) instead of ~10 `by omega`s in the row's 60-hyp body
(each of which the elab-wall memo shows costs ~0.5–0.9s from context size alone). -/
structure SpArith (sp : BitVec 64) (SL : StackLayout) : Prop where
  sp1088 : 1088 ≤ sp.toNat
  spLo : 0x80000000 ≤ sp.toNat
  spHtif : tohostAddr + 16 + 1088 ≤ sp.toNat
  SLlo40 : SL.lo ≤ sp.toNat - 40
  SLlo32 : SL.lo ≤ sp.toNat - 32
  e968 : sp.toNat - 968 + 8 = sp.toNat - 960
  s3win : ∀ k, k < 8 → sp.toNat - 40 ≤ sp.toNat - 40 + k ∧ sp.toNat - 40 + k < sp.toNat - 32

theorem spArith {sp : BitVec 64} {SL : StackLayout} (hSB : StackBounds sp SL) :
    SpArith sp SL := by
  obtain ⟨hSLloSp, hSLlo, hSLwin, hsp8, hsphiRam⟩ := hSB
  rw [show tohostAddr = 0x8001ad00 from rfl] at hSLwin
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · rw [show tohostAddr = 0x8001ad00 from rfl]; omega
  · omega
  · omega
  · omega
  · intro k hk; omega

/-- The five arm `hnXX` v2-relative address normalisations (`sp-K = (sp-1088)+off`),
bundled; `hspsub : (sp-1088#64).toNat = sp.toNat - 1088` supplied by the caller. -/
theorem armNorms {sp : BitVec 64} (hsp1088 : 1088 ≤ sp.toNat)
    (hspsub : (sp - 1088#64).toNat = sp.toNat - 1088) :
    (sp.toNat - 944 = (sp - 1088#64).toNat + 0x90)
    ∧ (sp.toNat - 936 = (sp - 1088#64).toNat + 0x98)
    ∧ (sp.toNat - 928 = (sp - 1088#64).toNat + 0xa0)
    ∧ (sp.toNat - 848 = (sp - 1088#64).toNat + 0xf0)
    ∧ (sp.toNat - 832 = (sp - 1088#64).toNat + 0x100) := by
  rw [hspsub]; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Split a little-endian 4-byte reconstruction equal to a small token `t < 256`
into its byte values (`b0 = t`, `b1=b2=b3=0`).  Derived once in a small context so
the row's op-token `hobv` is a projection, not a 4-way `omega` in the 40-hyp body. -/
theorem word32_split {b0 b1 b2 b3 : BitVec 8} {t : Nat} (ht : t < 256)
    (hrec : b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) = t) :
    b0.toNat = t ∧ b1.toNat = 0 ∧ b2.toNat = 0 ∧ b3.toNat = 0 := by
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- A `k` at or above `sp-40` is outside the dispatch write window `[sp-1088, sp-1088+264)`
(the `divDispatch` top-slot / s3-slot restore agreement; `264 < 1048`). -/
theorem notInDispWin_of_above {sp lo k : Nat} (hsp : 1088 ≤ sp) (hlo : sp - 824 ≤ lo) (hk : lo ≤ k) :
    ¬ (sp - 1088 ≤ k ∧ k < sp - 1088 + 0x108) := by omega

/-- `sret` box disjoint from a `k` outside `[SL.lo, SL.hi)` when `sret ∈ [SL.lo,SL.hi)`
(the `hSLfin` StoreRepr agreement). -/
theorem notInSret_of_notInSL {SL : StackLayout} {sret k : Nat}
    (hin : SL.lo ≤ sret ∧ sret + 24 ≤ SL.hi) (hk : ¬ (SL.lo ≤ k ∧ k < SL.hi)) :
    ¬ (sret ≤ k ∧ k < sret + 24) := by omega

/-- The four `FrameBundle`-geometry facts for the frame base `sp-1088`
(`lo/hi/htif/al` of `sp.toNat - 1088`), derived once from `StackBounds`. -/
theorem frameBaseGeom {sp : BitVec 64} {SL : StackLayout} (hSB : StackBounds sp SL) :
    (0x80000000 ≤ sp.toNat - 1088)
    ∧ (sp.toNat - 1088 + 0x108 ≤ 0x100000000)
    ∧ (tohostAddr + 16 ≤ sp.toNat - 1088)
    ∧ ((sp.toNat - 1088) % 8 = 0) := by
  obtain ⟨hSLloSp, hSLlo, hSLwin, hsp8, hsphiRam⟩ := hSB
  rw [show tohostAddr = 0x8001ad00 from rfl] at hSLwin ⊢
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The eight `sp-936+i = sp-944+8+i` byte-index equalities the arm's right-payload
`rpb` pins need (`sp-936` reindexed as `sp-944+8`), derived once (`936 ≤ sp`). -/
theorem rpbShift {sp : BitVec 64} (h : 944 ≤ sp.toNat) :
    (sp.toNat - 936 = sp.toNat - 944 + 8)
    ∧ (sp.toNat - 936 + 1 = sp.toNat - 944 + 8 + 1)
    ∧ (sp.toNat - 936 + 2 = sp.toNat - 944 + 8 + 2)
    ∧ (sp.toNat - 936 + 3 = sp.toNat - 944 + 8 + 3)
    ∧ (sp.toNat - 936 + 4 = sp.toNat - 944 + 8 + 4)
    ∧ (sp.toNat - 936 + 5 = sp.toNat - 944 + 8 + 5)
    ∧ (sp.toNat - 936 + 6 = sp.toNat - 944 + 8 + 6)
    ∧ (sp.toNat - 936 + 7 = sp.toNat - 944 + 8 + 7) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The four callee-saved restore slots `sp-{8,16,24,32}` all lie in the top
window `[sp-32, sp)` — the `read64_agreeP` window-membership the epilogue reads
need.  Derived once; each of the eight `⟨by omega, by omega⟩`s becomes a projection. -/
theorem topSlotWin {sp : BitVec 64} (h : 32 ≤ sp.toNat) :
    (∀ k, k < 8 → sp.toNat - 32 ≤ sp.toNat - 8 + k ∧ sp.toNat - 8 + k < sp.toNat)
    ∧ (∀ k, k < 8 → sp.toNat - 32 ≤ sp.toNat - 16 + k ∧ sp.toNat - 16 + k < sp.toNat)
    ∧ (∀ k, k < 8 → sp.toNat - 32 ≤ sp.toNat - 24 + k ∧ sp.toNat - 24 + k < sp.toNat)
    ∧ (∀ k, k < 8 → sp.toNat - 32 ≤ sp.toNat - 32 + k ∧ sp.toNat - 32 + k < sp.toNat) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro k hk; omega)

/-- Store-slot ⊂ `[SL.lo, SL.hi)` disjointness from a `k` OUTSIDE the stack window.
Used by every `getElem_writeMap8_disjoint … (by omega)` whose `k` satisfies
`¬(SL.lo ≤ k ∧ k < SL.hi)` (the `StoreRepr`/mem-frame agreement proofs).  The
`omega` is compiled into the olean ONCE; each site is a projection-free `exact`. -/
theorem slotDisj_of_notInSL {SL : StackLayout} {s k : Nat}
    (hs : SL.lo ≤ s ∧ s + 8 ≤ SL.hi) (hk : ¬ (SL.lo ≤ k ∧ k < SL.hi)) :
    k < s ∨ s + 8 ≤ k := by omega

/-- Disjointness of a store slot `s` from a `k` INSIDE a static region `[rlo,rhi)`
(the `loaded_eval_expr_agreeP` / `Value_intLoaded` code-byte iterators, whose `k`
ranges over `[rlo,rhi)`), given the slot-vs-region disjointness `hs`. -/
theorem slotDisj_of_inRegion {s k rlo rhi : Nat}
    (hs : s + 8 ≤ rlo ∨ rhi ≤ s) (hk : rlo ≤ k ∧ k < rhi) :
    k < s ∨ s + 8 ≤ k := by omega

/-- The `sret` box `[sret, sret+24)` is disjoint from a `k` in a static region
`[rlo,rhi)` disjoint from it (the `value_int` box's `hmemframevi` restore, whose
`k` ranges over the code region). -/
theorem notInSret_of_inRegion {sret k rlo rhi : Nat}
    (hs : sret + 24 ≤ rlo ∨ rhi ≤ sret) (hk : rlo ≤ k ∧ k < rhi) :
    ¬ (sret ≤ k ∧ k < sret + 24) := by omega

/-- The `sret` box disjoint from a `k` in the stack window `[SL.lo, SL.hi)` when
`sret` is outside the frame below `sp` (the `hsretStk` disjunction `sret+24 ≤ SL.lo
∨ sp ≤ sret`, combined with the concrete `k`-window `[lo, hi)` ⊆ frame). -/
theorem notInSret_of_window {sret k lo hi : Nat}
    (hs : sret + 24 ≤ lo ∨ hi ≤ sret) (hk : lo ≤ k ∧ k < hi) :
    ¬ (sret ≤ k ∧ k < sret + 24) := by omega

/-- `sret` box disjoint from a `k` in a frame sub-window `[lo,hi) ⊆ [SL.lo, sp)`,
using the `hsretStk` disjunction (`sret+24 ≤ SL.lo ∨ sp ≤ sret`).  Used by the s3
restore + top-window `hmemframevi` sites. -/
theorem notInSret_of_frameWin {sret SLlo sp lo hi k : Nat}
    (hsret : sret + 24 ≤ SLlo ∨ sp ≤ sret)
    (hlo : SLlo ≤ lo) (hhi : hi ≤ sp) (hk : lo ≤ k ∧ k < hi) :
    ¬ (sret ≤ k ∧ k < sret + 24) := by omega

/-- The `[SL.lo, sp)`-window variant (the `hmemframe`/`MemFrame` agreement, whose
`a` is outside `[SL.lo, sp.toNat)`).  Store slot `s = sp-K ⊂ [SL.lo, sp.toNat)`. -/
theorem slotDisj_of_notInStack {SL : StackLayout} {sp : BitVec 64} {s a : Nat}
    (hs : SL.lo ≤ s ∧ s + 8 ≤ sp.toNat) (ha : ¬ (SL.lo ≤ a ∧ a < sp.toNat)) :
    a < s ∨ s + 8 ≤ a := by omega

/-- The `k` variant for a `k` in the TOP window `[sp-32, sp)` (the callee-saved
restore-slot agreement, `hAgTop`): the store slot `s = sp-K` with `K ≥ 40` lies
strictly below `sp-32`, so `s + 8 ≤ k`.  Needs `s + 8 ≤ sp-32`. -/
theorem slotDisj_of_topWin {sp : BitVec 64} {s k : Nat}
    (hs : s + 8 ≤ sp.toNat - 32) (hk : sp.toNat - 32 ≤ k ∧ k < sp.toNat) :
    k < s ∨ s + 8 ≤ k := Or.inr (by omega)

/-- Inter-slot disjointness of the `s3` restore slot `sp-40` from a store slot
`sp-K` (`K ∈ {832,840,848}`, all `> 48`): `sp-40 + 8 = sp-32 ≤ sp-K` fails; rather
`sp-40 ≥ sp-K + 8` since `K ≥ 48`.  Provable from `48 ≤ K ≤ sp.toNat`. -/
theorem s3Disj_store {sp : BitVec 64} (K : Nat) (hKlo : 48 ≤ K) (hKsp : K ≤ sp.toNat) :
    (sp.toNat - 40) + 8 ≤ sp.toNat - K ∨ (sp.toNat - K) + 8 ≤ sp.toNat - 40 :=
  Or.inr (by omega)

/-- ALL the store-slot / s3-slot in-window facts the row's per-`k` mem-frame
disjointness proofs need, packed in ONE structure so the row adds exactly ONE
hypothesis (context-bloat law: every extra `have` slows every remaining omega in
the 60-hyp body).  Store slots `sp-{848,840,832}`; s3 slot `sp-40`. -/
structure SlotWindows (sp : BitVec 64) (SL : StackLayout) : Prop where
  inSL848 : SL.lo ≤ sp.toNat - 848 ∧ sp.toNat - 848 + 8 ≤ SL.hi
  inSL840 : SL.lo ≤ sp.toNat - 840 ∧ sp.toNat - 840 + 8 ≤ SL.hi
  inSL832 : SL.lo ≤ sp.toNat - 832 ∧ sp.toNat - 832 + 8 ≤ SL.hi
  inStk848 : SL.lo ≤ sp.toNat - 848 ∧ sp.toNat - 848 + 8 ≤ sp.toNat
  inStk840 : SL.lo ≤ sp.toNat - 840 ∧ sp.toNat - 840 + 8 ≤ sp.toNat
  inStk832 : SL.lo ≤ sp.toNat - 832 ∧ sp.toNat - 832 + 8 ≤ sp.toNat
  top848 : sp.toNat - 848 + 8 ≤ sp.toNat - 32
  top840 : sp.toNat - 840 + 8 ≤ sp.toNat - 32
  top832 : sp.toNat - 832 + 8 ≤ sp.toNat - 32
  s3d848 : (sp.toNat - 40) + 8 ≤ sp.toNat - 848 ∨ (sp.toNat - 848) + 8 ≤ sp.toNat - 40
  s3d840 : (sp.toNat - 40) + 8 ≤ sp.toNat - 840 ∨ (sp.toNat - 840) + 8 ≤ sp.toNat - 40
  s3d832 : (sp.toNat - 40) + 8 ≤ sp.toNat - 832 ∨ (sp.toNat - 832) + 8 ≤ sp.toNat - 40

/-- Build `SlotWindows` from `StackBounds` + the top-window bound `sp ≤ SL.hi`.
Every field is one `omega`, all paid ONCE (in this tiny context), not per site. -/
theorem slotWindows {sp : BitVec 64} {SL : StackLayout} (hSB : StackBounds sp SL)
    (hspSLhi : sp.toNat ≤ SL.hi) : SlotWindows sp SL := by
  obtain ⟨hSLloSp, hSLlo, hSLwin, hsp8, hsphiRam⟩ := hSB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by omega, by omega⟩
  · exact ⟨by omega, by omega⟩
  · exact ⟨by omega, by omega⟩
  · exact ⟨by omega, by omega⟩
  · exact ⟨by omega, by omega⟩
  · exact ⟨by omega, by omega⟩
  · omega
  · omega
  · omega
  · exact Or.inr (by omega)
  · exact Or.inr (by omega)
  · exact Or.inr (by omega)

/-- The bundle of `aExpr`-relative bounds (from the row precondition) needed for
the two operand-fetch sites `aExpr+8` (op token) and `aExpr+4` (left-operand ptr). -/
structure ExprBounds (aExpr : BitVec 64) : Prop where
  al : aExpr.toNat % 4 = 0
  lo : 0x80000000 ≤ aExpr.toNat
  hi : aExpr.toNat + 16 ≤ 0x100000000
  win : tohostAddr + 8 ≤ aExpr.toNat

/-- The four geometry facts for a 4-byte read at `aExpr.toNat + off`, `off ≤ 12`,
`off % 4 = 0`.  Omega runs against the tiny `ExprBounds` context only. -/
theorem exprGeom4 {aExpr : BitVec 64} (hEB : ExprBounds aExpr)
    (off : Nat) (hoff : off ≤ 12) (hoal : off % 4 = 0) :
    (0x80000000 ≤ aExpr.toNat + off)
    ∧ (aExpr.toNat + off + 4 ≤ 0x100000000)
    ∧ (aExpr.toNat + off + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ aExpr.toNat + off)
    ∧ ((aExpr.toNat + off) % 4 = 0) := by
  obtain ⟨hal, hlo, hhi, hwin⟩ := hEB
  have htoh : tohostAddr = 0x8001ad00 := rfl
  exact ⟨by omega, by omega, Or.inr (by omega), by omega⟩

end Vsa.Sim
