import Vsa.Sim.EnvSetScanStart
import Vsa.Sim.EnvSetHitReconstruct
import Vsa.Sim.EnvSetPrologueHead

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (Config Steps)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While

namespace Vsa.Sim

/-- Per-frame concrete layout facts for the recursive `env_set` scan.  The hit
field contains only byte/decode, layout, footprint, and source-value facts. -/
structure EnvSetFrameFacts
    (name valuePtr sp ret r8 r9 r18 r19 r20 r21 : BitVec 64)
    (nameStr : String) (newValue : Value) (N : NativeAddrs) (A : Arena)
    (φf φc : Addr → Nat) (m : Mem) (store : Store)
    (a : Addr) (f : Vsa.While.Frame) (pn : Nat) : Prop where
  addrSmall : φf a < 2^64
  addrLo : 0x80000000 ≤ φf a
  addrHi : φf a + 32 ≤ 0x100000000
  addrWin : tohostAddr + 8 ≤ φf a
  addrAlign : φf a % 8 = 0
  countSmall : f.vars.length < 2^31
  pnSmall : pn < 2^64
  pnRead : read64 m (φf a + 8) = some pn
  names : EnvSetScan.ScanNames m pn name nameStr f
  hit : ∀ i, (hi : i < f.vars.length) → ∀ oldValue,
    f.vars[i] = (nameStr, oldValue) →
    ∃ pv w0 w1 w2 : BitVec 64, ∃ slot : Nat,
      ChainFacts m m
        (envSetHitLoadLiveL (BitVec.ofNat 64 (φf a)) valuePtr
          (BitVec.ofNat 64 i) sp)
        (envSetHitLds pv w0 w1 w2) envSetHitLoadSeg ∧
      EnvSetHitSuffixFacts m pv (BitVec.ofNat 64 i) w0 w1 w2 sp ∧
      (envSetHitDst pv (BitVec.ofNat 64 i) +
        Functions.sign_extend (m := 64) (0x000#12)).toNat = slot ∧
      (envSetHitDst pv (BitVec.ofNat 64 i) +
        Functions.sign_extend (m := 64) (0x008#12)).toNat = slot + 8 ∧
      (envSetHitDst pv (BitVec.ofNat 64 i) +
        Functions.sign_extend (m := 64) (0x010#12)).toNat = slot + 16 ∧
      TargetFrameOutsideSetSlot m N φf φc (φf a) slot f i ∧
      StoreSetFootprint m
        (EnvSetValueTower m slot (envSetWordBytes w0)
          (envSetWordBytes w1) (envSetWordBytes w2))
        N φf φc store a slot ∧
      LPins8 m valuePtr.toNat (envSetWordBytes w0) ∧
      LPins8 m (valuePtr.toNat + 8) (envSetWordBytes w1) ∧
      LPins8 m (valuePtr.toNat + 16) (envSetWordBytes w2) ∧
      (∀ (p : Nat) (s : String), read64 m (valuePtr.toNat + 8) = some p →
        ∀ k, k ≤ s.length → OutsideSetSlot slot (p + k)) ∧
      ValueRepr m N φc valuePtr.toNat newValue ∧
      ChainFacts
        (EnvSetValueTower m slot (envSetWordBytes w0)
          (envSetWordBytes w1) (envSetWordBytes w2))
        (EnvSetValueTower m slot (envSetWordBytes w0)
          (envSetWordBytes w1) (envSetWordBytes w2))
        (envSetReturnL sp) (envSetReturnLds ret r8 r9 r18 r19 r20 r21)
        envSetReturnSeg ∧
      (∀ pvNat, read64 m (φf a + 16) = some pvNat → slot = pvNat + 24 * i)

def EnvSetChainFacts
    (name valuePtr sp ret r8 r9 r18 r19 r20 r21 : BitVec 64)
    (nameStr : String) (newValue : Value) (N : NativeAddrs) (A : Arena)
    (φf φc : Addr → Nat) (m : Mem) (store : Store) : Prop :=
  ∀ a f, store.frames[a]? = some f →
    ∃ pn, EnvSetFrameFacts name valuePtr sp ret r8 r9 r18 r19 r20 r21
      nameStr newValue N A φf φc m store a f pn

/-- A path-indexed semantic target drives the actual parent-chain scan, exact
three-word update, store reconstruction, and concrete `env_set` return. -/
theorem env_set_target_from_parent_head
    (store store' : Store) (start target : Addr) (nameStr : String)
    (newValue : Value) (bridge : AssignStoreBridge store store' start nameStr newValue)
    (selectedFrame : Vsa.While.Frame) (oldValue : Value)
    (beforeVars afterVars : List (String × Value))
    (name valuePtr sp ret r8 r9 r18 r19 r20 r21 : BitVec 64)
    (N : NativeAddrs) (A : Arena) (φf φc : Addr → Nat) (m : Mem)
    (hStore : StoreRepr m N A φf φc store)
    (hFacts : EnvSetChainFacts name valuePtr sp ret r8 r9 r18 r19 r20 r21
      nameStr newValue N A φf φc m store)
    (hTargetFrame : store.frames[target]? = some selectedFrame)
    (hSplit : selectedFrame.vars = beforeVars ++ (nameStr, oldValue) :: afterVars)
    (hUpdate : selectedFrame.vars.map (replaceBindingValue nameStr newValue) =
      beforeVars ++ (nameStr, newValue) :: afterVars)
    (hTargetFirst : FirstMatch selectedFrame.vars nameStr oldValue)
    (hResult : store' = { store with frames := store.frames.modify target fun current =>
      { current with vars := current.vars.map (replaceBindingValue nameStr newValue) } })
    (hret : BitVec.update (ret + Functions.sign_extend (m := 64) (0x000#12))
      0 0#1 = ret) :
    ∀ gas a,
      SetTarget store nameStr gas a target selectedFrame oldValue →
      ∀ frame, store.frames[a]? = some frame →
      ∀ g c scanRa out0,
        SetParentHeadSt g (BitVec.ofNat 64 (φf a)) name valuePtr scanRa sp
          a frame N φf φc out0 m c →
        ∃ c', Steps c c' ∧
          EnvSetReturnExactPost sp ret r8 r9 r18 r19 r20 r21 c'.σ.mem out0 c' ∧
          StoreSetAdvance N A φf φc store store' start nameStr newValue
            bridge target c'.σ.mem := by
  intro gas a hPath
  induction hPath with
  | @hit gas a frame old hframe hFirst =>
      intro currentFrame hframe' g c scanRa out0 hHead
      have hfeq : currentFrame = frame := by
        rw [hframe] at hframe'
        exact Option.some.inj hframe'.symm
      subst currentFrame
      obtain ⟨pn, hF⟩ := hFacts a frame hframe
      have hEnvNat : (BitVec.ofNat 64 (φf a)).toNat = φf a := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hF.addrSmall]
      obtain ⟨cScan, gScan, hsStart, hScan, houtStart⟩ :=
        env_set_parent_scan_start g (BitVec.ofNat 64 (φf a)) name valuePtr scanRa sp
          a frame nameStr pn out0 c hHead hF.names
          (by simpa [hEnvNat] using hF.pnRead)
          (by obtain ⟨i, hi, _, _⟩ := hFirst.index; omega)
          hF.countSmall hF.pnSmall hF.addrSmall
          (by simpa [hEnvNat] using hF.addrLo)
          (by simpa [hEnvNat] using hF.addrHi)
          (by simpa [hEnvNat] using hF.addrWin)
          (by simpa [hEnvNat] using hF.addrAlign)
      obtain ⟨cHit, i, hi, hsHit, hHit, hPair, houtHit⟩ :=
        EnvSetScan.scan_to_hit gScan (BitVec.ofNat 64 (φf a)) name valuePtr
          (BitVec.ofNat 64 frame.vars.length) (BitVec.ofNat 64 pn) scanRa sp
          frame nameStr old N φf φc m cScan hScan hFirst
      obtain ⟨pv, w0, w1, w2, slot, hLoad, hSuffix, h0, h8, h16,
        hShell, hFoot, hld0, hld1, hld2, hPayload, hValue, hReturn, hSlot⟩ :=
        hF.hit i hi old hPair
      have hout0 : cHit.σ.sailOutput = out0 := by
        exact houtHit.trans (houtStart.trans hHead.output)
      have hPre := setHitAt_to_hitLoad_pre pv w0 w1 w2 out0 hHit hout0
        (by simpa [hHit.mem] using hLoad)
      have hSemantic : ∃ (foundFrame : Vsa.While.Frame) (oldValue : Value)
          (before after : List (String × Value)),
        store.frames[a]? = some foundFrame ∧
        foundFrame.vars = before ++ (nameStr, oldValue) :: after ∧
        foundFrame.vars.map (replaceBindingValue nameStr newValue) =
          before ++ (nameStr, newValue) :: after ∧
        store' = { store with frames := store.frames.modify a (fun current =>
          { current with vars := current.vars.map (replaceBindingValue nameStr newValue) }) } :=
        ⟨frame, old, beforeVars, afterVars, hframe, hSplit, hUpdate, hResult⟩
      have hFrameRepr : FrameRepr m N φf φc (φf a) frame := by
        obtain ⟨ha, heq⟩ := Array.getElem?_eq_some_iff.mp hframe
        simpa only [heq] using hStore.frames a ha
      have hUnique : FrameNamesUnique frame.vars := by
        obtain ⟨ha, heq⟩ := Array.getElem?_eq_some_iff.mp hframe
        rw [← heq]
        exact bridge.before.unique a ha
      have hAdv : ∀ c1,
          EnvSetHitTowerPost (envSetHitDst pv (BitVec.ofNat 64 i)) w0 w1 w2 sp
            slot m out0 c1 →
          StoreSetAdvance N A φf φc store store' start nameStr newValue
            bridge a c1.σ.mem := by
        intro c1 hc1
        exact envSetHitTower_storeAdvance hc1 hStore hSemantic hframe hFrameRepr hi
          (by simpa using congrArg Prod.fst hPair) hUnique hSlot hShell hFoot
          hld0 hld1 hld2 hPayload hValue
      obtain ⟨c', hsTail, hPost, hAdvance⟩ :=
        env_set_hit_return_advance (N := N) (A := A) (φf := φf) (φc := φc)
          (store := store) (store' := store') (start := start) (target := a)
          (x := nameStr) (v := newValue) (bridge := bridge)
          (BitVec.ofNat 64 (φf a)) valuePtr (BitVec.ofNat 64 i)
          pv w0 w1 w2 sp slot ret r8 r9 r18 r19 r20 r21 m out0
          hSuffix h0 h8 h16 hReturn hret hAdv cHit hPre
      have hPost' : EnvSetReturnExactPost sp ret r8 r9 r18 r19 r20 r21
          c'.σ.mem out0 c' := by
        simpa [hPost.mem] using hPost
      exact ⟨c', (hsStart.trans hsHit).trans hsTail, hPost', hAdvance⟩
  | @parent gas a frame parent target terminalFrame old
      hframe hMiss hParent hTail ih =>
      intro currentFrame hframe' g c scanRa out0 hHead
      have hfeq : currentFrame = frame := by
        rw [hframe] at hframe'
        exact Option.some.inj hframe'.symm
      subst currentFrame
      obtain ⟨pn, hF⟩ := hFacts a frame hframe
      have hEnvNat : (BitVec.ofNat 64 (φf a)).toNat = φf a := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hF.addrSmall]
      obtain ⟨parentFrame, hParentFrameGet⟩ := hTail.headFrame
      obtain ⟨hpb, hpe⟩ := Array.getElem?_eq_some_iff.mp hParentFrameGet
      have hParentRepr : FrameRepr m N φf φc (φf parent) parentFrame := by
        simpa only [hpe] using hStore.frames parent hpb
      obtain ⟨_parentPn, hPF⟩ := hFacts parent parentFrame hParentFrameGet
      by_cases hEmpty : frame.vars.length = 0
      · obtain ⟨cMiss, gMiss, hsMiss, hMissSt, houtMiss⟩ :=
          env_set_parent_empty g (BitVec.ofNat 64 (φf a)) name valuePtr scanRa sp
            a frame nameStr pn out0 c hHead hF.names hEmpty hF.pnSmall hF.addrSmall
            (by simpa [hEnvNat] using hF.addrLo)
            (by simpa [hEnvNat] using hF.addrHi)
            (by simpa [hEnvNat] using hF.addrWin)
            (by simpa [hEnvNat] using hF.addrAlign)
        have hChainMiss := EnvSetScan.scanMiss_to_chain hMissSt
          (houtMiss.trans hHead.output) hMiss
        obtain ⟨cParent, gParent, hsParent, hParentHead⟩ :=
          env_set_parent_step gMiss (BitVec.ofNat 64 (φf a)) name valuePtr
            (0#64) (BitVec.ofNat 64 pn) scanRa sp frame parentFrame nameStr parent
            N φf φc out0 m cMiss hChainMiss hParent hParentRepr
            (by simpa [hEnvNat] using hF.addrLo)
            (by simpa [hEnvNat] using hF.addrHi)
            (by right; simpa [hEnvNat] using hF.addrWin)
            (by simpa [hEnvNat] using hF.addrAlign) hPF.addrSmall
        obtain ⟨c', hsTail, hPost, hAdvance⟩ :=
          ih hTargetFrame hSplit hUpdate hTargetFirst hResult
            parentFrame hParentFrameGet gParent cParent scanRa out0 hParentHead
        exact ⟨c', (hsMiss.trans hsParent).trans hsTail, hPost, hAdvance⟩
      · have hPos := Nat.pos_of_ne_zero hEmpty
        obtain ⟨cScan, gScan, hsStart, hScan, houtStart⟩ :=
          env_set_parent_scan_start g (BitVec.ofNat 64 (φf a)) name valuePtr scanRa sp
            a frame nameStr pn out0 c hHead hF.names
            (by simpa [hEnvNat] using hF.pnRead) hPos hF.countSmall hF.pnSmall
            hF.addrSmall (by simpa [hEnvNat] using hF.addrLo)
            (by simpa [hEnvNat] using hF.addrHi)
            (by simpa [hEnvNat] using hF.addrWin)
            (by simpa [hEnvNat] using hF.addrAlign)
        obtain ⟨cMiss, gMiss, hsScan, hMissSt, houtScan⟩ :=
          EnvSetScan.scan_to_miss gScan (BitVec.ofNat 64 (φf a)) name valuePtr
            (BitVec.ofNat 64 frame.vars.length) (BitVec.ofNat 64 pn) scanRa sp
            frame nameStr N φf φc m cScan hScan hPos hMiss
        have hChainMiss := EnvSetScan.scanMiss_to_chain hMissSt
          (houtScan.trans (houtStart.trans hHead.output)) hMiss
        obtain ⟨cParent, gParent, hsParent, hParentHead⟩ :=
          env_set_parent_step gMiss (BitVec.ofNat 64 (φf a)) name valuePtr
            (BitVec.ofNat 64 frame.vars.length) (BitVec.ofNat 64 pn)
            (0x80002d38#64) sp frame parentFrame nameStr parent N φf φc out0 m
            cMiss hChainMiss hParent hParentRepr
            (by simpa [hEnvNat] using hF.addrLo)
            (by simpa [hEnvNat] using hF.addrHi)
            (by right; simpa [hEnvNat] using hF.addrWin)
            (by simpa [hEnvNat] using hF.addrAlign) hPF.addrSmall
        obtain ⟨c', hsTail, hPost, hAdvance⟩ :=
          ih hTargetFrame hSplit hUpdate hTargetFirst hResult
            parentFrame hParentFrameGet gParent cParent (0x80002d38#64) out0 hParentHead
        exact ⟨c', ((hsStart.trans hsScan).trans hsParent).trans hsTail,
          hPost, hAdvance⟩

/-- Full non-null `env_set` entry.  The prologue spill is threaded into the
layout facts; `AssignStoreBridge.selected` supplies the exact recursive target. -/
theorem env_set_from_entry
    (store store' : Store) (start : Addr) (nameStr : String) (newValue : Value)
    (bridge : AssignStoreBridge store store' start nameStr newValue)
    (name valuePtr sp0 r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (N : NativeAddrs) (A : Arena) (φf φc : Addr → Nat) (m0 : Mem)
    (c : Config) (len pn : Nat)
    (hEntry : SetPrologueHeadSt (BitVec.ofNat 64 (φf start)) name valuePtr
      sp0 r0 r8 r9 r18 r19 r20 r21 len pn m0 c)
    (hStoreSurv : ∀ m,
      (∀ k, ¬ ((sp0 - 64#64).toNat ≤ k ∧
        k < (sp0 - 64#64).toNat + 64) → m[k]? = m0[k]?) →
      StoreRepr m N A φf φc store)
    (hFactsSurv : ∀ m,
      (∀ k, ¬ ((sp0 - 64#64).toNat ≤ k ∧
        k < (sp0 - 64#64).toNat + 64) → m[k]? = m0[k]?) →
      EnvSetChainFacts name valuePtr (sp0 - 64#64) r0 r8 r9 r18 r19 r20 r21
        nameStr newValue N A φf φc m store)
    (hStrcmpSurv : ∀ m,
      (∀ k, ¬ ((sp0 - 64#64).toNat ≤ k ∧
        k < (sp0 - 64#64).toNat + 64) → m[k]? = m0[k]?) →
      Vsa.Sim.Code.StrcmpLoaded m)
    (hret : BitVec.update (r0 + Functions.sign_extend (m := 64) (0x000#12))
      0 0#1 = r0) :
    ∃ (c' : Config) (m9 : Mem), Steps c c' ∧
      EnvSetReturnExactPost (sp0 - 64#64) r0 r8 r9 r18 r19 r20 r21
        c'.σ.mem c.σ.sailOutput c' ∧
      (∃ target, StoreSetAdvance N A φf φc store store' start nameStr newValue
        bridge target c'.σ.mem) ∧
      (∀ k, ¬ ((sp0 - 64#64).toNat ≤ k ∧
        k < (sp0 - 64#64).toNat + 64) → m9[k]? = m0[k]?) := by
  obtain ⟨target, targetFrame, oldValue, beforeVars, afterVars,
    hPath, hTargetFrame, hTargetFirst, hSplit, hUpdate, hResult⟩ := bridge.selected
  obtain ⟨cHead, hsHead, hHead⟩ :=
    env_set_prologue_head (BitVec.ofNat 64 (φf start)) name valuePtr sp0 r0
      r8 r9 r18 r19 r20 r21 len pn m0 c hEntry
  obtain ⟨m9, hmem9, hcode9, hs56, hs48, hs40, hs32, hs24, hs16, hs8,
    houtside⟩ := hHead.mem
  have hStore9 := hStoreSurv m9 houtside
  have hFacts9 := hFactsSurv m9 houtside
  obtain ⟨rootFrame, hRootFrame⟩ := hPath.headFrame
  obtain ⟨hrootBound, hrootElem⟩ := Array.getElem?_eq_some_iff.mp hRootFrame
  have hRootRepr : FrameRepr m9 N φf φc (φf start) rootFrame := by
    simpa only [hrootElem] using hStore9.frames start hrootBound
  obtain ⟨_rootPn, hRootFacts⟩ := hFacts9 start rootFrame hRootFrame
  have hRootHead : SetParentHeadSt (fun R => cHead.σ.regs.get? R)
      (BitVec.ofNat 64 (φf start)) name valuePtr r0 (sp0 - 64#64)
      start rootFrame N φf φc c.σ.sailOutput m9 cHead :=
    { good := hHead.good
      loadedSet := by rw [hmem9]; exact hcode9
      loadedStrcmp := by rw [hmem9]; exact hStrcmpSurv m9 houtside
      mem := hmem9
      pc := hHead.pc
      env4 := hHead.env4
      parent_eq := rfl
      name3 := hHead.name3
      value5 := hHead.out5
      ra := hHead.ra
      sp2 := hHead.sp
      minstret := hHead.minstret
      tick := hHead.tick
      output := hHead.output
      frame := hRootRepr
      ghost := fun _ _ => rfl }
  obtain ⟨c', hsTail, hPost, hAdvance⟩ :=
    env_set_target_from_parent_head store store' start target nameStr newValue bridge
      targetFrame oldValue beforeVars afterVars name valuePtr (sp0 - 64#64) r0
      r8 r9 r18 r19 r20 r21 N A φf φc m9 hStore9 hFacts9 hTargetFrame
      hSplit hUpdate hTargetFirst hResult hret store.frames.size start hPath
      rootFrame hRootFrame (fun R => cHead.σ.regs.get? R) cHead r0 c.σ.sailOutput
      hRootHead
  exact ⟨c', m9, hsHead.trans hsTail, hPost, ⟨target, hAdvance⟩, houtside⟩

#print axioms env_set_target_from_parent_head
#print axioms env_set_from_entry

end Vsa.Sim
