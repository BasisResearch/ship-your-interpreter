import Vsa.Sim.rows.EnvDefineUpdateExact
import Vsa.Sim.BridgeSegFramed

/-!
# `EnvDefineTailFramed` — keep-set-framed update block and epilogue of `env_define`

The landed rows `updateStoreLiveRow` (`rows/EnvDefineUpdateExact.lean`) and
`envDefineEpilogueRow` (`rows/EnvDefineEpilogueCore.lean`) export only the
registers their segs write, so the untouched `gp`/`tp`/`s7`–`s11`, the result
register `a0`, and the console output are lost after a scan hit.  This file
lands ONE generic keep-set-framed seg row over a register ghost
(`segRowKeepGhost`, `frame_of_wrChain_avoids` on a `decide`d `WrChainAvoids`)
and instantiates it for both segs, then re-composes the landed
scan-hit ⟶ update ⟶ epilogue path with the frame retained:

* `KeepGhost P g outp c` — the registers selected by `P` equal the ghost `g`
  and the output is `outp`;
* `EnvDefineTailKeep`/`EnvDefineTailKeepSp` — the keep predicates
  (`x3`, `x4`, `x10`, `x23`–`x27`; the update block also keeps `x2`);
* `updateStoreLiveRowKeep`, `envDefineEpilogueRowKeep` — the framed rows;
* `envDefineUpdateFromHitKeep`, `envDefineUpdateFromHitKeep_of_heap_owned`,
  `EnvDefineUpdatePost.restoreKeep` — the landed update/epilogue compositions
  with `KeepGhost` carried.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.MemRepr
open Vsa.RuntimeRepr
open Vsa.Logic (Triple)

namespace Vsa.Sim

/-- What a keep-set-framed row carries besides its seg outcome: the registers
selected by `P` equal a ghost, and the console output is a constant. -/
structure KeepGhost (P : Register → Bool) (g : (R : Register) → Option (RegisterType R))
    (outp : Array String) (c : Config) : Prop where
  keep : ∀ R, P R = true → c.σ.regs.get? R = g R
  out : c.σ.sailOutput = outp

theorem KeepGhost.mono {P Q : Register → Bool}
    {g : (R : Register) → Option (RegisterType R)} {outp : Array String} {c : Config}
    (hPQ : ∀ R, Q R = true → P R = true) (h : KeepGhost P g outp c) : KeepGhost Q g outp c :=
  ⟨fun R hR => h.keep R (hPQ R hR), h.out⟩

/-- **The generic keep-set framed seg row over a ghost.**  `segToTriple` plus the
`P`-frame (`frame_of_wrChain_avoids`, two `decide`s) and output preservation. -/
theorem segRowKeepGhost (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 : BitVec 64) (m0 : Mem) (P : Register → Bool)
    (g : (R : Register) → Option (RegisterType R)) (outp : Array String)
    (Q : Config → Prop)
    (hwf : ChainOK pc0 (keysG L) bs)
    (hnoise : ∀ rr ∈ noiseRegs, P rr = false) (havoid : WrChainAvoids P bs)
    (hpost : ∀ (σ' : MState) (i' u' : Nat), GoodState σ' → i' < 2 →
      σ'.mem = writeLog m0 (evalBlocks bs (SegEvalState.init L lds)).log →
      σ'.regs.get? Register.PC = some (evalBlocksPC pc0 (SegEvalState.init L lds) bs) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      GHolds σ' (evalBlocks bs (SegEvalState.init L lds)).regs → Q ⟨σ', i', u'⟩) :
    Triple (fun c => SegPre bs L lds pc0 m0 c ∧ KeepGhost P g outp c)
      (fun c => Q c ∧ KeepGhost P g outp c) := by
  intro c ⟨hpre, hk⟩
  obtain ⟨hG, hmem, hpc, ⟨vm, hmi⟩, hL, hkeys, hfacts, htick⟩ := hpre
  obtain ⟨σ', i', hs, hi', hG', hmem', hout, hpc', hmi', hregs, hframe⟩ :=
    segEval_sound bs c.σ c.tick c.steps pc0 vm L lds hG hpc hmi hL hkeys hfacts hwf htick
  rw [hmem] at hmem'
  refine ⟨⟨σ', i', c.steps + evalBlocksFuel bs⟩, hs,
    hpost σ' i' _ hG' hi' hmem' hpc' hmi' hregs, ?_, hout.trans hk.out⟩
  intro R hR
  exact (frame_of_wrChain_avoids hnoise havoid hframe R hR).trans (hk.keep R hR)

#print axioms segRowKeepGhost

/-- ABI registers `env_define`'s update block and epilogue never write, plus the
result register: `gp`, `tp`, `a0`, `s7`–`s11`. -/
def EnvDefineTailKeep (R : Register) : Bool :=
  R == Register.x3 || R == Register.x4 || R == Register.x10 || R == Register.x23 ||
    R == Register.x24 || R == Register.x25 || R == Register.x26 || R == Register.x27

/-- The update block additionally keeps `sp`. -/
def EnvDefineTailKeepSp (R : Register) : Bool :=
  EnvDefineTailKeep R || R == Register.x2

theorem EnvDefineTailKeep.sp {R : Register} (h : EnvDefineTailKeep R = true) :
    EnvDefineTailKeepSp R = true := by
  simp [EnvDefineTailKeepSp, h]

/-- The framed update block row: `updateStoreLiveRow` keeping `sp`, `gp`, `tp`,
`a0`, `s7`–`s11` and the output. -/
theorem updateStoreLiveRowKeep (env src idx : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem)
    (g : (R : Register) → Option (RegisterType R)) (outp : Array String) :
    Triple
      (fun c => SegPre updateStoreSeg (updateStoreL env src idx) lds 0x80002ac0#64 m0 c ∧
        KeepGhost EnvDefineTailKeepSp g outp c)
      (fun c => UpdateStoreLivePost env src idx lds m0 c ∧
        KeepGhost EnvDefineTailKeepSp g outp c) := by
  apply segRowKeepGhost updateStoreSeg (updateStoreL env src idx) lds 0x80002ac0#64 m0
    EnvDefineTailKeepSp g outp (UpdateStoreLivePost env src idx lds m0)
    (by show ChainOK 0x80002ac0#64 [20, 21, 8] updateStoreSeg; decide)
    (by show ∀ rr ∈ noiseRegs, EnvDefineTailKeepSp rr = false; decide)
    (by show WrChainAvoids EnvDefineTailKeepSp updateStoreSeg; decide)
  intro σ' i' u' hG' hi' hmem' hpc' _ hregs'
  refine ⟨hG', hmem', ?_, hregs', hi'⟩
  rw [hpc']; rfl

/-- The framed epilogue row: `envDefineEpilogueRow` keeping `gp`, `tp`, `a0`,
`s7`–`s11` and the output. -/
theorem envDefineEpilogueRowKeep (sp : BitVec 64) (lds : List (List (BitVec 8))) (m0 : Mem)
    (g : (R : Register) → Option (RegisterType R)) (outp : Array String) :
    Triple
      (fun c => SegPre envDefineEpilogueSeg (envDefineEpilogueL sp) lds 0x80002aec#64 m0 c ∧
        KeepGhost EnvDefineTailKeep g outp c)
      (fun c => EnvDefineEpiloguePost sp lds m0 c ∧ KeepGhost EnvDefineTailKeep g outp c) := by
  apply segRowKeepGhost envDefineEpilogueSeg (envDefineEpilogueL sp) lds 0x80002aec#64 m0
    EnvDefineTailKeep g outp (EnvDefineEpiloguePost sp lds m0)
    (by show ChainOK 0x80002aec#64 [2] envDefineEpilogueSeg; decide)
    (by show ∀ rr ∈ noiseRegs, EnvDefineTailKeep rr = false; decide)
    (by show WrChainAvoids EnvDefineTailKeep envDefineEpilogueSeg; decide)
  intro σ' i' u' hG' hi' hmem' hpc' _ hregs'
  exact ⟨hG', hmem', hpc', hregs', hi'⟩

#print axioms updateStoreLiveRowKeep
#print axioms envDefineEpilogueRowKeep

/-- The same update endpoint retains exact copied bytes and its caller frame. -/
structure EnvDefineCopiedKeptUpdatePost
    (saved g : (R : Register) → Option (RegisterType R))
    (env src dst sp : BitVec 64) (idx : Nat) (m : Mem)
    (N : NativeAddrs) (phiC : Vsa.While.Addr → Nat) (v : Vsa.While.Value)
    (out : Array String) (c : Config) : Prop where
  copy : EnvDefineCopiedUpdatePost saved env src dst sp idx m N phiC v c
  kept : KeepGhost EnvDefineTailKeepSp g out c

/-- `envDefineUpdateFromHit` with the keep-set frame carried through the update
block. -/
theorem envDefineUpdateFromHitCopiedKeep
    (saved : (R : Register) → Option (RegisterType R))
    (env name src count cursor sp vals dst : BitVec 64) (idx : Nat)
    (m0 : Mem) (N : NativeAddrs) (φc : Vsa.While.Addr → Nat)
    (v : Vsa.While.Value) (A : Arena)
    (g : (R : Register) → Option (RegisterType R)) (outp : Array String)
    (hcode : Vsa.Sim.Code.Env_defineLoaded m0)
    (hword : ValueWordRepr m0 N φc src.toNat v)
    (hgeom : EnvDefineUpdateGeom env src vals dst idx m0)
    (hpayload : ValuePayloadCovered
      (fun a => a < dst.toNat ∨ dst.toNat + 24 ≤ a) m0 src.toNat v)
    (hdstArena : A.contains dst.toNat 24)
    (harenaStack : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo) :
    Triple
      (fun c => EnvDefineUpdateHitPre saved env name src count cursor sp idx m0 c ∧
        KeepGhost EnvDefineTailKeepSp g outp c)
      (EnvDefineCopiedKeptUpdatePost saved g env src dst sp idx m0 N φc v outp) := by
  intro c ⟨h, hk⟩
  obtain ⟨cmp, hp, hsaved⟩ := h
  obtain ⟨hgood, hmemRaw, hpc, hregs, htick⟩ := hp
  have hmem : c.σ.mem = m0 := by
    simpa [envDefineScanHitSeg, evalBlocks, SegEvalState.init, writeLog] using hmemRaw
  obtain ⟨lds, hfacts, hevidence⟩ :=
    updateStoreFacts env src vals dst idx m0 N φc v hcode hword hgeom
  obtain ⟨hvals, d0, d1, d2, h0, h1, h2, hw0, hw1, hw2,
    hpin0, hpin1, hpin2⟩ := hevidence
  have reg (n : Nat) (w : BitVec 64)
      (hl : lookupG n (evalBlocks envDefineScanHitSeg
        (SegEvalState.init
          (envDefineScanLiveL cmp (BitVec.ofNat 64 idx) cursor count
            env name src sp) [])).regs = some w) :
      gprGet c.σ n = some w :=
    gholds_lookup _ hregs hl
  have hL : GHolds c.σ (updateStoreL env src (BitVec.ofNat 64 idx)) := by
    exact ⟨by simpa [gprGet] using reg 20 env (by rfl),
      by simpa [gprGet] using reg 21 src (by rfl),
      by simpa [gprGet] using reg 8 (BitVec.ofNat 64 idx) (by rfl), trivial⟩
  have hpre : SegPre updateStoreSeg
      (updateStoreL env src (BitVec.ofNat 64 idx)) lds 0x80002ac0#64 m0 c :=
    ⟨hgood, hmem, hpc, hgood.minstret, hL,
      (by show KeysOK [20, 21, 8]; decide),
      (by rw [hmem]; exact hfacts), htick⟩
  have hsp : c.σ.regs.get? Register.x2 = some sp := by
    simpa [gprGet] using reg 2 sp (by rfl)
  obtain ⟨c', hs, hp', hk'⟩ :=
    updateStoreLiveRowKeep env src (BitVec.ofNat 64 idx) lds m0 g outp c ⟨hpre, hk⟩
  have hsp' : c'.σ.regs.get? Register.x2 = some sp := by
    rw [hk'.keep Register.x2 (by decide), ← hk.keep Register.x2 (by decide)]
    exact hsp
  have hrepr : ValueWordRepr c'.σ.mem N φc dst.toNat v :=
    updateStoreValueWordRepr env src vals dst idx lds m0 c' N φc v hp'
      hvals hgeom hpin0 hpin1 hpin2 hpayload hword
  have hmemTower : c'.σ.mem = UpdateValueTower m0 dst.toNat
      (lds.getD 1 []) (lds.getD 2 []) (lds.getD 3 []) := by
    rw [hp'.2.1, updateStoreLog env src vals dst idx lds m0 hvals hgeom]
    rfl
  have hsaved' : EnvDefineSavedSpillFrame sp saved c' := by
    apply hsaved.of_arena_frame A hdstArena harenaStack harenaCode
    intro a ha
    rw [hmemTower, hmem]
    exact updateValueTowerOutside m0 dst.toNat a
      (lds.getD 1 []) (lds.getD 2 []) (lds.getD 3 []) ha
  refine ⟨c', hs, ⟨⟨lds, hp', hrepr, hsaved', hsp', hmemTower⟩, ?_⟩, hk'⟩
  intro k hk
  rw [hmemTower]
  exact updateValueTowerCopy m0 src.toNat dst.toNat
    (lds.getD 1 []) (lds.getD 2 []) (lds.getD 3 []) hpin0 hpin1 hpin2 k hk

/-- `envDefineUpdateFromHit` with the keep-set frame carried through the update
block. -/
theorem envDefineUpdateFromHitKeep
    (saved : (R : Register) → Option (RegisterType R))
    (env name src count cursor sp vals dst : BitVec 64) (idx : Nat)
    (m0 : Mem) (N : NativeAddrs) (φc : Vsa.While.Addr → Nat)
    (v : Vsa.While.Value) (A : Arena)
    (g : (R : Register) → Option (RegisterType R)) (outp : Array String)
    (hcode : Vsa.Sim.Code.Env_defineLoaded m0)
    (hword : ValueWordRepr m0 N φc src.toNat v)
    (hgeom : EnvDefineUpdateGeom env src vals dst idx m0)
    (hpayload : ValuePayloadCovered
      (fun a => a < dst.toNat ∨ dst.toNat + 24 ≤ a) m0 src.toNat v)
    (hdstArena : A.contains dst.toNat 24)
    (harenaStack : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo) :
    Triple
      (fun c => EnvDefineUpdateHitPre saved env name src count cursor sp idx m0 c ∧
        KeepGhost EnvDefineTailKeepSp g outp c)
      (fun c => EnvDefineUpdatePost saved env src dst sp idx m0 N φc v c ∧
        KeepGhost EnvDefineTailKeepSp g outp c) := by
  intro c entry
  obtain ⟨after, steps, post⟩ := envDefineUpdateFromHitCopiedKeep saved env name src count
    cursor sp vals dst idx m0 N φc v A g outp hcode hword hgeom hpayload
    hdstArena harenaStack harenaCode c entry
  exact ⟨after, steps, post.copy.update, post.kept⟩

#print axioms envDefineUpdateFromHitCopiedKeep

/-- `envDefineUpdateFromHit_of_heap_owned` with the keep-set frame carried. -/
theorem envDefineUpdateFromHitKeep_of_heap_owned
    (saved : (R : Register) → Option (RegisterType R))
    (env name src count cursor sp valsBV dst : BitVec 64) (idx : Nat)
    (m0 : Mem) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (v : Vsa.While.Value) (A : Arena) (exts : List Extent)
    (store : Vsa.While.Store) (target : Vsa.While.Addr)
    (g : (R : Register) → Option (RegisterType R)) (outp : Array String)
    (htarget : target < store.frames.size)
    (hidx : idx < store.frames[target].vars.length)
    (hvals : read64 m0 (φf target + 16) = some valsBV.toNat)
    (hdst : dst.toNat = valsBV.toNat + 24 * idx)
    (howned : StoreHeapOwned m0 φf φc exts store)
    (hsrcOwned : ValueHeapOwned m0 exts src.toNat v)
    (hcode : Vsa.Sim.Code.Env_defineLoaded m0)
    (hword : ValueWordRepr m0 N φc src.toNat v)
    (hgeom : EnvDefineUpdateGeom env src valsBV dst idx m0)
    (hdstArena : A.contains dst.toNat 24)
    (harenaStack : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo) :
    Triple
      (fun c => EnvDefineUpdateHitPre saved env name src count cursor sp idx m0 c ∧
        KeepGhost EnvDefineTailKeepSp g outp c)
      (fun c => EnvDefineUpdatePost saved env src dst sp idx m0 N φc v c ∧
        KeepGhost EnvDefineTailKeepSp g outp c) := by
  apply envDefineUpdateFromHitKeep saved env name src count cursor sp valsBV dst idx
    m0 N φc v A g outp hcode hword hgeom
  · have hp := howned.valuePayloadOutsideSet htarget hidx hvals hsrcOwned
    simpa [SetOutside, hdst] using hp
  · exact hdstArena
  · exact harenaStack
  · exact harenaCode

/-- `EnvDefineUpdatePost.restore` with the keep-set frame carried through the
epilogue (`sp` is rebased by the epilogue and drops out of the keep set). -/
theorem EnvDefineUpdatePost.restoreKeep
    {saved : (R : Register) → Option (RegisterType R)}
    {env src dst sp : BitVec 64} {idx : Nat} {m0 : Mem}
    {N : NativeAddrs} {phiC : Vsa.While.Addr → Nat} {v : Vsa.While.Value} {c : Config}
    {g : (R : Register) → Option (RegisterType R)} {outp : Array String}
    (hp : EnvDefineUpdatePost saved env src dst sp idx m0 N phiC v c)
    (hk : KeepGhost EnvDefineTailKeepSp g outp c) :
    ∃ after, Steps c after ∧ EnvDefineEpilogueExactPost sp saved c.σ.mem after ∧
      KeepGhost EnvDefineTailKeep g outp after := by
  obtain ⟨_ldsUpdate, hrow, _hword, hsaved, hsp, _hmemTower⟩ := hp
  obtain ⟨hgood, _hmem, hpc, _hregs, htick⟩ := hrow
  obtain ⟨lds, hfacts, hvalues⟩ := hsaved.chainFacts
  have hpre : SegPre envDefineEpilogueSeg (envDefineEpilogueL sp) lds
      0x80002aec#64 c.σ.mem c :=
    ⟨hgood, rfl, hpc, hgood.minstret, ⟨hsp, trivial⟩,
      (by show KeysOK [2]; decide), hfacts, htick⟩
  obtain ⟨c', hs, hpost, hk'⟩ := envDefineEpilogueRowKeep sp lds c.σ.mem g outp c
    ⟨hpre, hk.mono (fun R hR => EnvDefineTailKeep.sp hR)⟩
  exact ⟨c', hs, envDefineEpilogueExact_of_post sp saved lds c.σ.mem c' hvalues hpost, hk'⟩

#print axioms envDefineUpdateFromHitKeep_of_heap_owned
#print axioms EnvDefineUpdatePost.restoreKeep

end Vsa.Sim
