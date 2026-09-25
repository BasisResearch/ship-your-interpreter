import Vsa.Sim.NativeNameAudit.Memory
import Vsa.Sim.InitialSnapshotFacts
import Vsa.Sim.ExitRuntimeDataTransport

/-! Scratch initial admission for the binding-name candidate. All reads are
proved from the finite initial overlay. This file makes no execution claim. -/

open LeanRV64DExecutable Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.While

namespace Vsa.Sim.NativeNameAudit

open Vsa.Sim.OutputAliasLoaded Vsa.Sim.LayoutInstance

local macro "native_read" : tactic =>
  `(tactic| (simp only [read32, read64, readLE, nativeName_lookup]; decide))
local macro "native_byte" : tactic =>
  `(tactic| (rw [nativeName_lookup]; decide))
local macro "outside_log" : tactic =>
  `(tactic| (simp only [nativeNameLog, OutL, and_true]; omega))

theorem nativeName_agree : AgreeP (OutL nativeNameLog) snapshotMem nativeNameMem :=
  fun a ha => (writeLog_out snapshotMem nativeNameLog a ha).symm

theorem nativeName_names : read64 nativeNameMem 0x81000008 = some 0x81000040 := by
  native_read
theorem nativeName_values : read64 nativeNameMem 0x81000010 = some 0x81000080 := by
  native_read
theorem nativeName_capacity : read32 nativeNameMem 0x81000004 = some 8 := by
  native_read

theorem nativeName_printCString : CString nativeNameMem 0x81000200 "print" := by
  apply cstring_agreeP nativeName_agree snapshot_storeFacts.view.printName
  intro k hk
  change k ≤ 5 at hk
  outside_log

theorem nativeName_valueNameCString : CString nativeNameMem 0x81000210 "println" := by
  apply cstring_agreeP nativeName_agree snapshot_storeFacts.view.printlnName
  intro k hk
  change k ≤ 7 at hk
  outside_log

theorem nativeName_assertCString : CString nativeNameMem 0x81000220 "assert" := by
  apply cstring_agreeP nativeName_agree snapshot_storeFacts.view.assertName
  intro k hk
  change k ≤ 6 at hk
  outside_log

theorem nativeName_bindingCString : CString nativeNameMem 0x8001bb91 "println" := by
  refine ⟨['p', 'r', 'i', 'n', 't', 'l', 'n'], ?_, rfl⟩
  refine CStr.cons (b := 112#8) (by native_byte) (by decide) (by decide) ?_
  refine CStr.cons (b := 114#8) (by native_byte) (by decide) (by decide) ?_
  refine CStr.cons (b := 105#8) (by native_byte) (by decide) (by decide) ?_
  refine CStr.cons (b := 110#8) (by native_byte) (by decide) (by decide) ?_
  refine CStr.cons (b := 116#8) (by native_byte) (by decide) (by decide) ?_
  refine CStr.cons (b := 108#8) (by native_byte) (by decide) (by decide) ?_
  refine CStr.cons (b := 110#8) (by native_byte) (by decide) (by decide) ?_
  exact CStr.nil (by native_byte)

theorem nativeName_frame :
    FrameRepr nativeNameMem Nfixed phif phic 0x81000000 globalFrame := by
  refine ⟨by native_read, ⟨8, nativeName_capacity, by decide⟩,
    ⟨0x81000040, 0x81000080, nativeName_names, nativeName_values, ?_⟩,
    by change read64 nativeNameMem 0x81000018 = some 0; native_read⟩
  intro i hi
  change i < 3 at hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · exact ⟨⟨0x81000200, by native_read, nativeName_printCString⟩,
      by native_read, ⟨0x81000200, by native_read, nativeName_printCString⟩,
      by native_read⟩
  · exact ⟨⟨0x8001bb91, by native_read, nativeName_bindingCString⟩,
      by native_read, ⟨0x81000210, by native_read, nativeName_valueNameCString⟩,
      by native_read⟩
  · exact ⟨⟨0x81000220, by native_read, nativeName_assertCString⟩,
      by native_read, ⟨0x81000220, by native_read, nativeName_assertCString⟩,
      by native_read⟩

def NativeNameStoreFoot (k : Nat) : Prop :=
  StorePage k ∨ (0x8001bb91 ≤ k ∧ k < 0x8001bb99)

/-- Generic FrameRepr transport, instantiated with both real CString supports. -/
theorem nativeName_frame_transport {m' : Mem}
    (ha : AgreeP NativeNameStoreFoot nativeNameMem m') :
    FrameRepr m' Nfixed phif phic 0x81000000 globalFrame := by
  apply frameRepr_agreeP ha ?_ ?_ ?_ ?_ nativeName_frame
  · intro k hk
    left
    unfold envHeader at hk
    unfold StorePage
    omega
  · intro pn pv hn hv i hi
    have hn' := Option.some.inj (hn.symm.trans nativeName_names)
    have hv' := Option.some.inj (hv.symm.trans nativeName_values)
    subst pn; subst pv
    change i < 3 at hi
    constructor
    · intro k hk; left; unfold StorePage; omega
    · intro k hk; left; unfold valHeader at hk; unfold StorePage; omega
  · intro pn pv hn hv i hi q hq k hk
    have hn' := Option.some.inj (hn.symm.trans nativeName_names)
    have hv' := Option.some.inj (hv.symm.trans nativeName_values)
    subst pn; subst pv
    change i < 3 at hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hc with rfl | rfl | rfl
    · have hr : read64 nativeNameMem 0x81000040 = some 0x81000200 := by native_read
      have heq := Option.some.inj (hq.symm.trans hr)
      subst q
      simp only [globalFrame, List.getElem_cons_zero] at hk
      change k ≤ 5 at hk
      left
      unfold StorePage
      omega
    · have hr : read64 nativeNameMem 0x81000048 = some 0x8001bb91 := by native_read
      have heq := Option.some.inj (hq.symm.trans hr)
      subst q
      simp only [globalFrame, List.getElem_cons_zero, List.getElem_cons_succ] at hk
      change k ≤ 7 at hk
      right
      omega
    · have hr : read64 nativeNameMem 0x81000050 = some 0x81000220 := by native_read
      have heq := Option.some.inj (hq.symm.trans hr)
      subst q
      simp only [globalFrame, List.getElem_cons_zero, List.getElem_cons_succ] at hk
      change k ≤ 6 at hk
      left
      unfold StorePage
      omega
  · intro pn pv hn hv i hi
    have hn' := Option.some.inj (hn.symm.trans nativeName_names)
    have hv' := Option.some.inj (hv.symm.trans nativeName_values)
    subst pn; subst pv
    change i < 3 at hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hc with rfl | rfl | rfl
    · intro q hq k hk
      have hr : read64 nativeNameMem 0x81000088 = some 0x81000200 := by native_read
      have heq := Option.some.inj (hq.symm.trans hr)
      subst q
      change k ≤ 5 at hk
      left
      unfold StorePage
      omega
    · intro q hq k hk
      have hr : read64 nativeNameMem 0x810000a0 = some 0x81000210 := by native_read
      have heq := Option.some.inj (hq.symm.trans hr)
      subst q
      change k ≤ 7 at hk
      left
      unfold StorePage
      omega
    · intro q hq k hk
      have hr : read64 nativeNameMem 0x810000b8 = some 0x81000220 := by native_read
      have heq := Option.some.inj (hq.symm.trans hr)
      subst q
      change k ≤ 6 at hk
      left
      unfold StorePage
      omega

/-- Reuse all memory-independent store geometry from the original witness. -/
theorem nativeName_store_of_frame {m : Mem}
    (hf : FrameRepr m Nfixed phif phic 0x81000000 globalFrame) :
    StoreRepr m Nfixed arena phif phic initSt.store :=
  { snapshot_storeFacts.store with
    frames := by
      intro fa hfa
      change fa < 1 at hfa
      have hz : fa = 0 := by omega
      subst fa
      exact hf
    closures := by
      intro ca hca
      change ca < 0 at hca
      omega }

theorem nativeName_store : StoreRepr nativeNameMem Nfixed arena phif phic initSt.store :=
  nativeName_store_of_frame nativeName_frame

theorem nativeName_store_survives : ∀ m' : Mem,
    (∀ k, ¬ interpRunWriteFootprint fixedInp k → nativeNameMem[k]? = m'[k]?) →
    StoreRepr m' Nfixed arena phif phic initSt.store := by
  intro m' hag
  apply nativeName_store_of_frame
  apply nativeName_frame_transport
  intro k hk
  apply hag
  change ¬ ((0x87800000 ≤ k ∧ k < 0x88000000) ∨
    (0x87fffe10 + 16 ≤ k ∧ k < 0x87fffe10 + 128))
  unfold NativeNameStoreFoot StorePage at hk
  omega

theorem nativeName_low_unchanged (a : Nat) (hhi : a < 0x8001bb91) :
    nativeNameMem[a]? = snapshotMem[a]? := by
  apply writeLog_out
  outside_log

theorem nativeName_text : Code.FixedTextLoaded nativeNameMem :=
  snapshot_text.transport (fun a _ hhi => nativeName_low_unchanged a (by omega))

theorem nativeName_rodata : Code.FixedRodataLoaded nativeNameMem :=
  snapshot_rodata.transport (fun a _ hhi => nativeName_low_unchanged a (by omega))

theorem nativeName_statics : Code.ImageStaticsLoaded nativeNameMem := by
  simpa (disch := decide) only [Code.ImageStaticsLoaded, Code.imgLldFmt,
    Code.imgDecPointStr, Code.imgParseSlotD, Code.imgParseSlotL, Code.imgFnSlot,
    Code.imgDecPointPtr, Code.imgMbCurMax, Code.imgImpurePtr, nativeName_low_unchanged]
    using snapshot_statics

/-- The broad ConsoleFoot is not assumed unchanged. Every actual field is
read from the finite snapshot; only the existential buffer byte changes. -/
theorem nativeName_console : ConsoleBoot nativeNameMem where
  impure := by native_read
  stdout := by native_read
  sinit := by native_read
  cursor := by native_read
  readCount := by native_read
  writeCount := by native_read
  flags := by native_read
  flag0 := by native_byte
  flag1 := by native_byte
  fd := by native_read
  base := by native_read
  bufSize := by native_read
  lineBufSize := by native_read
  cookie := by native_read
  writer := by native_read
  lock := by native_read
  lockMode := by native_read
  bufferByte := ⟨0x6e#8, by native_byte⟩

theorem nativeName_exitRuntime : ExitRuntimeData nativeNameMem := by
  apply snapshot_exitRuntime.transport
  intro a ha
  obtain ⟨r, hr, hlo, hhi⟩ := ha
  have bounds : ∀ r ∈ exitRuntimeExtraRegions,
      r.1 + r.2 ≤ 0x8001bb91 ∨
      (0x8001bb98 ≤ r.1 ∧ r.1 + r.2 ≤ 0x81000048) := by decide
  have hb := bounds r hr
  apply nativeName_agree
  outside_log

theorem nativeName_stack_unchanged (a : Nat)
    (hlo : stackSL.lo ≤ a) (hhi : a < stackSL.hi) :
    nativeNameMem[a]? = snapshotMem[a]? := by
  apply writeLog_out
  change 0x87800000 ≤ a at hlo
  change a < 0x88000000 at hhi
  outside_log

theorem nativeName_mainRa : read64 nativeNameMem 0x87fffff8 = some 0x80000038 := by
  native_read
theorem nativeName_globals : read64 nativeNameMem interpObject = some 0x81000000 := by
  native_read
theorem nativeName_depth : read32 nativeNameMem (interpObject + 8) = some 0 := by
  native_read

theorem nativeName_stackBytes : ∀ k, stackSL.lo ≤ k → k < stackSL.hi →
    ∃ b : BitVec 8, nativeNameMem[k]? = some b := by
  intro k hlo hhi
  rw [nativeName_stack_unchanged k hlo hhi]
  exact snapshot_stackBytes k hlo hhi

theorem nativeName_memoryFacts : SnapshotMemoryFacts nativeNameMem where
  mainRa := nativeName_mainRa
  text := nativeName_text
  rodata := nativeName_rodata
  statics := nativeName_statics
  console := nativeName_console
  exitRuntime := nativeName_exitRuntime
  globals := nativeName_globals
  depth := nativeName_depth
  stackBytes := nativeName_stackBytes
  store := nativeName_store
  storeSurvives := nativeName_store_survives

theorem nativeName_physicalFacts :
    InterpRunPhysicalFacts nativeNameConfig 0x82000000 2 fixedInp
      Nfixed arena phif phic 0 := nativeName_memoryFacts.physicalFacts

#print axioms nativeName_frame
#print axioms nativeName_frame_transport
#print axioms nativeName_store_survives
#print axioms nativeName_console
#print axioms nativeName_exitRuntime
#print axioms nativeName_physicalFacts

end Vsa.Sim.NativeNameAudit
