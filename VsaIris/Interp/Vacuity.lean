import VsaIris.Interp.Boundary
import Vsa.Sim.NativeNameAudit.ControlLoaded

/-!
# Vacuity check: every §3 predicate is inhabited at the control program

The predicates of `Repr.lean` are only worth proving over if they are
SATISFIABLE together at a real initial memory. The control program of
`Vsa/Sim/NativeNameAudit/Control*` supplies one: a concrete machine memory
`Control.heapMem`, a checked `Loaded interpRunLayout nativeNameProgram
heapConfig`, and the initial store `initSt` with its global frame and three
native bindings.

Everything below is derived from ONE boundary resource — the bytes adequacy
hands the client (`[∗map] k ↦ v ∈ imgMap (memImg heapMem) l, k ↦ₘ v`, carved
by `Boundary.lean`) — plus the two freshly allocated `InterpGS` ghost maps.
Nothing is assumed about the machine beyond what the control files prove.

Scope: `strAt`, `astE`/`astS`/`astSs`, `valOf`/`valAt`, `frameBody`/
`frameOwn`, `storeRepr` (closures empty), `interpCore`/`interpCtxPre`. The
`heapRes`/`world` layer needs `isHeap` at the interpreter control's dlmalloc
heap, which is H4's `AllocLedger` work, not R's.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProofMode Iris.BI.BigSepM
open VsaIris
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr
open Vsa.Sim.NativeNameAudit Vsa.Sim.NativeNameAudit.Control
open Vsa.Sim.OutputAliasLoaded Vsa.Sim.LayoutInstance

/-! ## The control program's concrete geometry -/

/-- The global frame's `Env` struct, names array and values array, as they sit
in `Control.alloc` (`Vsa/Sim/NativeNameAudit/ControlLedger.lean:11`). -/
def ctlGeom : FrameGeom where
  e := 0x81000000
  cap := 8
  pn := 0x81000040
  pv := 0x81000100
  par := 0
  sblk := (0x81000000, 32)
  nblk := (0x81000040, 64)
  vblk := (0x81000100, 192)

theorem ctlGeom_blocks :
    ctlGeom.blocks = [(0x81000000, 32), (0x81000040, 64), (0x81000100, 192)] := rfl

/-- The control store is one frame with the three native bindings. -/
theorem ctl_store : Vsa.While.initSt.store = ⟨#[globalFrame], #[]⟩ := rfl

theorem ctl_frameRepr : FrameRepr heapMem Nfixed phif phic ctlGeom.e globalFrame :=
  heapStoreFacts.frame

theorem ctl_frameReads : FrameReads heapMem Nfixed phif phic ctlGeom.e globalFrame :=
  FrameReads.of_frameRepr ctl_frameRepr

/-- `Control.shared` covers the three binding names and the AST page. -/
theorem ctl_shared_name (p len : Nat)
    (h : (p = 0x81000200 ∧ len = 5) ∨ (p = 0x81000210 ∧ len = 7) ∨
      (p = 0x81000220 ∧ len = 6)) : ∀ j, j ≤ len → Control.shared (p + j) := by
  intro j hj
  unfold Control.shared
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨by omega, by omega⟩
  · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))

/-- Extents laid out in order are disjoint. -/
theorem extDisj_of_le {b b' : Nat × Nat} (h : b.1 + b.2 ≤ b'.1) : ExtDisj b b' := by
  intro a ha ha'
  unfold InExt at ha ha'
  omega

/-- The three block extents of the global frame are pairwise disjoint. -/
theorem ctlGeom_disjoint : ctlGeom.blocks.Pairwise ExtDisj := by
  rw [ctlGeom_blocks]
  refine List.Pairwise.cons (fun b hb => ?_)
    (List.Pairwise.cons (fun b hb => ?_)
      (List.Pairwise.cons (fun b hb => absurd hb (by simp)) List.Pairwise.nil))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> exact extDisj_of_le (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    exact extDisj_of_le (by decide)

theorem ctl_var0 {h} : globalFrame.vars[0]'h = ("print", Value.native .print) := rfl
theorem ctl_var1 {h} : globalFrame.vars[1]'h = ("println", Value.native .println) := rfl
theorem ctl_var2 {h} : globalFrame.vars[2]'h = ("assert", Value.native .assert) := rfl

/-- **The boundary data for the global frame**, all of it checked against the
control memory. -/
theorem ctl_frameBridge :
    FrameBridge Control.shared heapMem Nfixed phic ctlGeom globalFrame (memImg heapMem) where
  e_ne := by decide
  sblk := by exact ⟨by decide, by decide⟩
  cap := heapStoreFacts.capacity
  names := heapStoreFacts.names
  vals := heapStoreFacts.values
  parent := heapStoreFacts.parent
  count_le := by decide
  empty := by intro h; exact absurd h (by decide)
  arrays := by intro _; exact ⟨rfl, by decide, rfl, by decide⟩
  disjoint := ctlGeom_disjoint
  agree := fun _ _ => rfl
  nameShared := by
    intro i hi q hq j hj
    have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by
      have : i < 3 := hi
      omega
    rcases hi3 with rfl | rfl | rfl
    · have : q = 0x81000200 := Option.some.inj (hq.symm.trans heapStoreFacts.names0)
      subst this
      rw [ctl_var0] at hj
      exact ctl_shared_name _ 5 (Or.inl ⟨rfl, rfl⟩) j (Nat.le_trans hj (by decide))
    · have : q = 0x81000210 := Option.some.inj (hq.symm.trans heapStoreFacts.names1)
      subst this
      rw [ctl_var1] at hj
      exact ctl_shared_name _ 7 (Or.inr (Or.inl ⟨rfl, rfl⟩)) j (Nat.le_trans hj (by decide))
    · have : q = 0x81000220 := Option.some.inj (hq.symm.trans heapStoreFacts.names2)
      subst this
      rw [ctl_var2] at hj
      exact ctl_shared_name _ 6 (Or.inr (Or.inr ⟨rfl, rfl⟩)) j (Nat.le_trans hj (by decide))
  payloadShared := by
    intro i hi t ht p hp j hj
    have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by
      have : i < 3 := hi
      omega
    rcases hi3 with rfl | rfl | rfl
    · rw [ctl_var0] at ht
      have hts : t = "print" := by simpa [payloadStr, nativeName] using ht.symm
      have : p = 0x81000200 := Option.some.inj (hp.symm.trans heapStoreFacts.name0)
      subst this; subst hts
      exact ctl_shared_name _ 5 (Or.inl ⟨rfl, rfl⟩) j (Nat.le_trans hj (by decide))
    · rw [ctl_var1] at ht
      have hts : t = "println" := by simpa [payloadStr, nativeName] using ht.symm
      have : p = 0x81000210 := Option.some.inj (hp.symm.trans heapStoreFacts.name1)
      subst this; subst hts
      exact ctl_shared_name _ 7 (Or.inr (Or.inl ⟨rfl, rfl⟩)) j (Nat.le_trans hj (by decide))
    · rw [ctl_var2] at ht
      have hts : t = "assert" := by simpa [payloadStr, nativeName] using ht.symm
      have : p = 0x81000220 := Option.some.inj (hp.symm.trans heapStoreFacts.name2)
      subst this; subst hts
      exact ctl_shared_name _ 6 (Or.inr (Or.inr ⟨rfl, rfl⟩)) j (Nat.le_trans hj (by decide))

/-! ## The predicates, at the control program -/

/-- The bytes the store owns exclusively: the frame's three blocks. -/
def ctlOwnedAddrs : List Nat := blockAddrs ctlGeom.blocks

/-- The immutable bytes: the three binding names and the AST page. Exactly
`Control.shared` (`Vsa/Sim/NativeNameAudit/ControlLedger.lean:29`). -/
def ctlSharedExts : List (Nat × Nat) :=
  [(0x81000200, 6), (0x81000210, 8), (0x81000220, 7), (0x82000000, 0x100)]

def ctlSharedAddrs : List Nat := blockAddrs ctlSharedExts

theorem ctlSharedAddrs_mem (a : Nat) : a ∈ ctlSharedAddrs ↔ Control.shared a := by
  rw [ctlSharedAddrs, mem_blockAddrs]
  unfold BlocksCover ctlSharedExts Control.shared AstPage InExt
  constructor
  · rintro ⟨b, hb, hlo, hhi⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp at hlo hhi <;> omega
  · intro h
    rcases h with h | h | h | h
    · exact ⟨(0x81000200, 6), by simp, by omega, by omega⟩
    · exact ⟨(0x81000210, 8), by simp, by omega, by omega⟩
    · exact ⟨(0x81000220, 7), by simp, by omega, by omega⟩
    · exact ⟨(0x82000000, 0x100), by simp, by omega, by omega⟩

theorem ctlSharedExts_disjoint : ctlSharedExts.Pairwise ExtDisj := by
  unfold ctlSharedExts
  refine List.Pairwise.cons (fun b hb => ?_) (List.Pairwise.cons (fun b hb => ?_)
    (List.Pairwise.cons (fun b hb => ?_)
      (List.Pairwise.cons (fun b hb => absurd hb (by simp)) List.Pairwise.nil)))
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  · rcases hb with rfl | rfl | rfl <;> exact extDisj_of_le (by decide)
  · rcases hb with rfl | rfl <;> exact extDisj_of_le (by decide)
  · subst hb; exact extDisj_of_le (by decide)

theorem ctlOwnedAddrs_nodup : ctlOwnedAddrs.Nodup := blockAddrs_nodup ctlGeom_disjoint
theorem ctlSharedAddrs_nodup : ctlSharedAddrs.Nodup := blockAddrs_nodup ctlSharedExts_disjoint

/-- The control's shared view (heap names and the AST page) is window-safe. -/
theorem ctl_sharedWin : SharedWin Control.shared := by
  intro k hk
  unfold Control.shared AstPage at hk
  unfold htifLo
  omega

section Vac

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

omit I in
/-- One of the control's C strings, out of the shared view. -/
theorem ctl_strAt_print : roOn (GF := GF) Control.shared heapMem ⊢ strAt 0x81000200 "print" :=
  strAt_of_cstringWithin ⟨heapStoreFacts.printName,
    fun j hj => ctl_shared_name _ 5 (Or.inl ⟨rfl, rfl⟩) j (Nat.le_trans hj (by decide))⟩ ctl_sharedWin

omit I in
theorem ctl_strAt_println : roOn (GF := GF) Control.shared heapMem ⊢ strAt 0x81000210 "println" :=
  strAt_of_cstringWithin ⟨heapStoreFacts.printlnName,
    fun j hj => ctl_shared_name _ 7 (Or.inr (Or.inl ⟨rfl, rfl⟩)) j (Nat.le_trans hj (by decide))⟩ ctl_sharedWin

omit I in
theorem ctl_strAt_assert : roOn (GF := GF) Control.shared heapMem ⊢ strAt 0x81000220 "assert" :=
  strAt_of_cstringWithin ⟨heapStoreFacts.assertName,
    fun j hj => ctl_shared_name _ 6 (Or.inr (Or.inr ⟨rfl, rfl⟩)) j (Nat.le_trans hj (by decide))⟩ ctl_sharedWin

omit I in
/-- **The control program's AST**, persistent. -/
theorem ctl_astSs : roOn (GF := GF) Control.shared heapMem ⊢
    astSs 0x82000000 2 nativeNameProgram :=
  astSs_of_programRepr (heapAstReads.programWithin.mono (Q := Control.shared)
    (fun _ hk => show Control.shared _ from Or.inr (Or.inr (Or.inr hk))))

omit I in
/-- The first statement of the control program, persistent. -/
theorem ctl_astS : roOn (GF := GF) Control.shared heapMem ⊢
    astS 0x82000020 Vsa.While.LoadedOutputAlias.printLine :=
  astS_of_stmtRepr (heapAstReads.stmtWithin.mono (Q := Control.shared)
    (fun _ hk => show Control.shared _ from Or.inr (Or.inr (Or.inr hk))))

/-- The global frame binds only natives, so no closure fragment is needed. -/
theorem ctl_closSupply : ⊢ closSupplyL (GF := GF) phic (globalFrame.vars.map Prod.snd) := by
  unfold closSupplyL
  imodintro
  iintro %v %hv
  iapply closSupply_of_ne ?_
  simp only [globalFrame, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hv
  rcases hv with rfl | rfl | rfl <;> (intro ca h; exact absurd h (by simp))

/-- **The global frame's body**, exclusive over its three blocks. -/
theorem ctl_frameBody :
    roOn (GF := GF) Control.shared heapMem ∗ ownImg (BlocksCover ctlGeom.blocks) (memImg heapMem)
      ⊢ frameBody Nfixed globalFrame ctlGeom := by
  iintro ⟨#H, Hown⟩
  iapply frameBody_of_frameRepr ctl_frameReads ctl_frameBridge ctl_sharedWin $$ [H Hown]
  iframe H Hown
  isplitl []
  · iapply ctl_closSupply
  · rw [show globalFrame.parent = none from rfl]
    iapply parentSupply_none

/-- **The whole control store**, over the two freshly allocated ghost maps. -/
theorem ctl_storeRepr :
    ghost_map_auth (GF := GF) I.frameName (DFrac.own 1) (∅ : NatMap Nat) ∗
      ghost_map_auth I.closName (DFrac.own 1) (∅ : NatMap Nat) ∗
      roOn Control.shared heapMem ∗ ownImg (BlocksCover ctlGeom.blocks) (memImg heapMem) ⊢
      |==> (storeRepr Nfixed Vsa.While.initSt.store ctlGeom.blocks ∗ frameAt 0 ctlGeom.e) := by
  change _ ⊢ iprop(|==> (storeRepr Nfixed Vsa.While.initSt.store
      (([] : List (Nat × Nat)) ++ ctlGeom.blocks) ∗
    frameAt (⟨#[], #[]⟩ : Vsa.While.Store).frames.size ctlGeom.e))
  iintro ⟨Hf, Hc, #H, Hown⟩
  ihave Hempty := storeRepr_empty (N := Nfixed) (GF := GF) $$ [Hf Hc]
  · iframe Hf Hc
  ihave Hbody := ctl_frameBody (GF := GF) $$ [H Hown]
  · iframe H Hown
  iapply storeRepr_allocFrame (N := Nfixed) (s := ⟨#[], #[]⟩) (B := [])
    (s' := Vsa.While.initSt.store) (f := globalFrame) (Gm := ctlGeom) (by rfl) (by rfl)
    ⟨fun fa h => by
      have : fa = 0 := by change fa < 1 at h; omega
      subst this
      exact (show Vsa.Sim.FrameNamesUnique globalFrame.vars by
        unfold Vsa.Sim.FrameNamesUnique; simp [globalFrame]),
     fun fa h p hp => by
      have : fa = 0 := by change fa < 1 at h; omega
      subst this
      exact absurd hp (show globalFrame.parent ≠ some p by simp [globalFrame])⟩
  iframe Hempty Hbody

/-! ### The interpreter context -/

/-- `struct Interp`'s five windows at `fixedInp` (`interp.h`). -/
def ctlInp : Nat := 0x87fffe10

def ctlInterpExts : List (Nat × Nat) :=
  [(ctlInp, 8), (ctlInp + interpDepthOff, 4), (ctlInp + interpDepthOff + 4, 4),
    (ctlInp + interpJmpOff, interpJmpLen), (ctlInp + interpErrOff, interpErrLen)]

theorem ctl_globals : imgLE (memImg heapMem) ctlInp 8 = 0x81000000 := by
  have h := heapPhysicalFacts.globals
  unfold heapConfig at h
  rw [physicalConfig_mem] at h
  exact readLE_memImg (n := 8) (a := ctlInp) h

theorem ctl_depth : imgLE (memImg heapMem) (ctlInp + interpDepthOff) 4 = 0 := by
  have h := heapPhysicalFacts.call_depth
  unfold heapConfig at h
  rw [physicalConfig_mem] at h
  exact readLE_memImg (n := 4) (a := ctlInp + interpDepthOff) h

/-- **The interpreter context at `interp_run`'s entry**, before `setjmp`. -/
theorem ctl_interpCtxPre :
    ownImg (GF := GF) (InExt (ctlInp, 8)) (memImg heapMem) ∗
      ownImg (InExt (ctlInp + interpDepthOff, 4)) (memImg heapMem) ∗
      ownImg (InExt (ctlInp + interpDepthOff + 4, 4)) (memImg heapMem) ∗
      ownImg (InExt (ctlInp + interpJmpOff, interpJmpLen)) (memImg heapMem) ∗
      ownImg (InExt (ctlInp + interpErrOff, interpErrLen)) (memImg heapMem) ∗
      frameAt 0 0x81000000 ⊢ |==> interpCtxPre ctlInp 0 := by
  iintro ⟨Hg, Hd, Hp, Hj, He, #Hf⟩
  imod wordRO_of_ownImg ctl_globals $$ Hg with Hg
  imodintro
  unfold interpCtxPre interpCore
  isplitl [Hg Hd Hp He]
  · iexists 0x81000000
    iframe Hg Hf
    isplitl [Hd]
    · iapply wordAt_of_ownImg ctl_depth $$ Hd
    isplitl [Hp]
    · iapply blockOwn_of_ownImg _ _ _ $$ Hp
    · iapply blockOwn_of_ownImg _ _ _ $$ He
  · iapply blockOwn_of_ownImg _ _ _ $$ Hj

/-! ### One represented value -/

theorem ctl_valueRepr : ValueRepr heapMem Nfixed phic 0x81000100 (.native .print) :=
  ⟨heapStoreFacts.tag0, ⟨0x81000200, heapStoreFacts.name0, heapStoreFacts.printName⟩,
    heapStoreFacts.function0⟩

theorem ctl_payloadShared :
    PayloadShared Control.shared heapMem 0x81000100 (.native .print) := by
  intro t ht p hp j hj
  have hts : t = "print" := by simpa [payloadStr, nativeName] using ht.symm
  have : p = 0x81000200 := Option.some.inj (hp.symm.trans heapStoreFacts.name0)
  subst this; subst hts
  exact ctl_shared_name _ 5 (Or.inl ⟨rfl, rfl⟩) j (Nat.le_trans hj (by decide))

/-- **The first binding's value slot**, exclusive, with its persistent name. -/
theorem ctl_valAt :
    roOn (GF := GF) Control.shared heapMem ∗
      ownImg (InExt (0x81000100, 24)) (memImg heapMem) ⊢
      valAt Nfixed 0x81000100 (.native .print) := by
  iintro ⟨#H, Hown⟩
  iapply valAt_of_valueWordRepr ctl_valueRepr ctl_payloadShared (fun _ _ => rfl) ctl_sharedWin $$ [H Hown]
  iframe H Hown
  iapply closSupply_of_ne (fun ca h => by exact absurd h (by simp))

/-! ## The check

Every §3 predicate above, from ONE boundary resource: the bytes adequacy hands
the client over two disjoint address lists, plus the two freshly allocated
`InterpGS` ghost maps. Nothing else is assumed. -/

theorem ctl_predicates_inhabited :
    ghost_map_auth (GF := GF) I.frameName (DFrac.own 1) (∅ : NatMap Nat) ∗
      ghost_map_auth I.closName (DFrac.own 1) (∅ : NatMap Nat) ∗
      ([∗map] k ↦ v ∈ imgMap (memImg heapMem) ctlOwnedAddrs, iprop(k ↦ₘ v)) ∗
      ([∗map] k ↦ v ∈ imgMap (memImg heapMem) ctlSharedAddrs, iprop(k ↦ₘ v)) ⊢
      |==> (storeRepr Nfixed Vsa.While.initSt.store ctlGeom.blocks ∗ frameAt 0 ctlGeom.e ∗
        astSs 0x82000000 2 nativeNameProgram ∗
        astS 0x82000020 Vsa.While.LoadedOutputAlias.printLine ∗
        strAt 0x81000200 "print" ∗ strAt 0x81000210 "println" ∗
        strAt 0x81000220 "assert") := by
  iintro ⟨Hf, Hc, Hown, Hsh⟩
  imod roOn_of_memMap (m := heapMem) ctlSharedAddrs_nodup ctlSharedAddrs_mem
    (fun k b _ hb => memImg_eq hb) $$ Hsh with #H
  ihave Hown := ownImg_of_memMap (S := BlocksCover ctlGeom.blocks) ctlOwnedAddrs_nodup
    (fun a => mem_blockAddrs) $$ Hown
  imod ctl_storeRepr $$ [Hf Hc H Hown] with ⟨Hs, #He⟩
  · iframe Hf Hc H Hown
  imodintro
  iframe Hs He
  isplitl []
  · iapply ctl_astSs $$ H
  isplitl []
  · iapply ctl_astS $$ H
  isplitl []
  · iapply ctl_strAt_print $$ H
  isplitl []
  · iapply ctl_strAt_println $$ H
  · iapply ctl_strAt_assert $$ H

end Vac

#print axioms ctl_frameBridge
#print axioms ctl_storeRepr
#print axioms ctl_interpCtxPre
#print axioms ctl_valAt
#print axioms ctl_predicates_inhabited

end VsaIris.Interp
