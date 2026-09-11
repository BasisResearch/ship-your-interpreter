import Vsa.Sim.rows.EnvDefineGrowLane
import Vsa.Sim.AllocCapacity

/-!
# `EnvDefineMissHead` — the non-empty miss: cap dispatch arms to the return

`envDefineMissLane` (`rows/EnvDefineContractUpdate.lean`) parks a miss on a
non-empty frame at the cap dispatch (`EnvDefineMissReady`): the append arm
(`0x80002b1c`, `count < cap`) or the grow arm (`0x80002b90`, `count = cap`,
`a5 = cap`).  This module turns each arm into the lanes' entry data —
`EnvDefineMissFacts` at the scanned memory from the scan facts,
`EnvDefineMissRegs` from the framed dispatch post — and composes
`envDefineAppendLane` / `envDefineGrowLane ≫ envDefineAppendLane` to
`EnvDefineReturnState`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.MemRepr Vsa.RuntimeRepr
open Vsa.Alloc (AbiPreserved StackLayout StackOK MallocContract ExtDisjoint)
open Vsa.Sim.Code (Env_defineLoaded FixedTextLoaded)
open Vsa.While (Addr Value)

namespace Vsa.Sim

/-! ## 1. The arms of the miss dispatch, named -/

/-- The append arm of `EnvDefineMissCapResult` (`count < cap`, parked at
`0x80002b1c`). -/
inductive EnvDefineAppendArmReady
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent) (outp : Array String)
    (saved gm : (R : Register) → Option (RegisterType R))
    (env count pn sp : BitVec 64) (f : Vsa.While.Frame)
    (m0 : Mem) (c : Config) : Prop where
  | intro (cap i : Nat) (lds : List (List (BitVec 8)))
      (room : f.vars.length < cap)
      (index : i + 1 = f.vars.length)
      (post : EnvDefineCapFramedPost M exts outp gm (BitVec.ofNat 64 (i + 1))
        (pn + BitVec.ofNat 64 (8 * (i + 1))) sp envDefineCapAppendSeg
        0x80002b1c#64 env count lds m0 c)
      (saved : EnvDefineSavedSpillFrame sp saved c)
      (cap_read : read32 m0 (env.toNat + 4) = some cap)
      (a5 : c.σ.regs.get? Register.x15 = some (BitVec.ofNat 64 cap))

/-- The grow arm of `EnvDefineMissCapResult` (`count = cap`, parked at
`0x80002b90`). -/
inductive EnvDefineGrowArmReady
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent) (outp : Array String)
    (saved gm : (R : Register) → Option (RegisterType R))
    (env count pn sp : BitVec 64) (f : Vsa.While.Frame)
    (m0 : Mem) (c : Config) : Prop where
  | intro (cap i : Nat) (lds : List (List (BitVec 8)))
      (full : f.vars.length = cap)
      (index : i + 1 = f.vars.length)
      (post : EnvDefineCapFramedPost M exts outp gm (BitVec.ofNat 64 (i + 1))
        (pn + BitVec.ofNat 64 (8 * (i + 1))) sp envDefineCapGrowSeg
        0x80002b90#64 env count lds m0 c)
      (saved : EnvDefineSavedSpillFrame sp saved c)
      (cap_read : read32 m0 (env.toNat + 4) = some cap)
      (a5 : c.σ.regs.get? Register.x15 = some (BitVec.ofNat 64 cap))

/-- The cap dispatch selects exactly one arm. -/
theorem EnvDefineMissCapResult.arms
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {exts : List Extent} {outp : Array String}
    {saved gm : (R : Register) → Option (RegisterType R)}
    {env count pn sp : BitVec 64} {f : Vsa.While.Frame} {m0 : Mem} {c : Config}
    (h : EnvDefineMissCapResult M exts outp saved gm env count pn sp f m0 c) :
    EnvDefineAppendArmReady M exts outp saved gm env count pn sp f m0 c ∨
      EnvDefineGrowArmReady M exts outp saved gm env count pn sp f m0 c := by
  obtain ⟨cap, h⟩ := h
  rcases h with ⟨h1, i, lds, hi, hpost, hsaved, hcap, ha5⟩ |
      ⟨h1, i, lds, hi, hpost, hsaved, hcap, ha5⟩
  · exact Or.inl ⟨cap, i, lds, h1, hi, hpost, hsaved, hcap, ha5⟩
  · exact Or.inr ⟨cap, i, lds, h1, hi, hpost, hsaved, hcap, ha5⟩

/-! ## 2. The lanes' entry data from the scan facts -/

/-- **The miss facts at the scanned memory** from the scan facts, the entry
facts and both ledgers. -/
theorem envDefineMissFacts_of_scan
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (v8 v9 v18 v19 v20 v21 v22 : BitVec 64) (pn : Nat)
    (gm : (R : Register) → Option (RegisterType R))
    (hE : EnvDefineMem N A SL φf φc st env x v aEnv aName pv esp m)
    (L : EnvDefineUpdateLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (LM : EnvDefineMissLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (Sf : EnvDefineScanFacts g N A SL φf φc st env x v esp aEnv aName pv r m exts
      v8 v9 v18 v19 v20 v21 v22 pn gm)
    (hmiss : ∀ j (hj : j < (st.store.frames[env]'Sf.env_lt).vars.length),
      ((st.store.frames[env]'Sf.env_lt).vars[j]'hj).1 ≠ x)
    (cap : Nat)
    (hcap : read32 (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) (φf env + 4) =
      some cap) :
    EnvDefineMissFacts g N A SL φf φc st env x v esp aEnv aName pv r m exts
      (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) cap := by
  have hsp1 := hE.stack.1
  have hsp2 := hE.stack.2.1
  have hAstack := hE.arena_stack
  have henvLt := Sf.env_lt
  obtain ⟨henvArena, _⟩ := hE.store.frames_arena env henvLt
  unfold Arena.contains at henvArena
  have hAg : AgreeP (fun a => a < esp.toNat - 64 ∨ esp.toNat ≤ a) m
      (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) :=
    fun a ha => (Sf.mem_agree a ha).symm
  have hrec : ∀ k, φf env ≤ k → k < φf env + 32 → (k < esp.toNat - 64 ∨ esp.toNat ≤ k) := by
    intro k hk1 hk2
    rcases hAstack with hA | hA
    · left; omega
    · right; omega
  exact
    { ra_align := Sf.ra_align
      g_sp := Sf.g_sp
      env_lt := henvLt
      env_addr := Sf.env_addr
      text := Sf.text0
      store := Sf.store0
      owned := Sf.owned0
      word := Sf.word0
      cap_read := hcap
      names_align := fun pn' h => LM.names_aligned pn' (by
        rw [read64_agreeP hAg (fun k hk => hrec _ (by omega) (by omega))]; exact h)
      vals_align := fun pv' h => L.arrays_aligned pv' (by
        rw [read64_agreeP hAg (fun k hk => hrec _ (by omega) (by omega))]; exact h)
      miss := hmiss
      mem_agree := fun k _ hkS => Sf.mem_agree k (by omega)
      mem_extends := Sf.mem_extends }

/-- **The machine side at a cap-dispatch arm** from the framed dispatch post,
the saved spill image and the scan facts. -/
theorem envDefineMissRegs_of_arm
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (v8 v9 v18 v19 v20 v21 v22 : BitVec 64) (pn : Nat)
    (gm : (R : Register) → Option (RegisterType R))
    (Sf : EnvDefineScanFacts g N A SL φf φc st env x v esp aEnv aName pv r m exts
      v8 v9 v18 v19 v20 v21 v22 pn gm)
    {idx cursor : BitVec 64} {seg : List BBlock} {pc : BitVec 64}
    {lds : List (List (BitVec 8))} {c : Config}
    (hpost : EnvDefineCapFramedPost M exts out gm idx cursor (esp - 64#64) seg pc aEnv
      (BitVec.ofNat 64 (st.store.frames[env]'Sf.env_lt).vars.length) lds
      (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) c)
    (hsaved : EnvDefineSavedSpillFrame (esp - 64#64) (envDefineSaved g r) c) :
    EnvDefineMissRegs g A SL st env esp aEnv aName pv r out M exts
      (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) Sf.env_lt c := by
  obtain ⟨⟨hG, hmem, _, _, htick⟩, hframe⟩ := hpost
  have abi : ∀ R, AbiPreserved R = true → R ≠ Register.x8 → R ≠ Register.x9 →
      c.σ.regs.get? R = gm R := fun R hR h8 h9 =>
    (hframe.abi R hR).trans (envDefineScanGhost_ne gm idx cursor h8 h9)
  exact
    { good := hG
      tick := htick
      mem := hmem
      out := hframe.out
      minstret := hG.minstret
      sp := (abi _ (by decide) (by decide) (by decide)).trans Sf.gm_sp
      gp := hframe.gp
      s2 := (abi _ (by decide) (by decide) (by decide)).trans Sf.gm_s2
      s3 := (abi _ (by decide) (by decide) (by decide)).trans Sf.gm_s3
      s4 := (abi _ (by decide) (by decide) (by decide)).trans Sf.gm_s4
      s5 := (abi _ (by decide) (by decide) (by decide)).trans Sf.gm_s5
      rest := fun R hA hRes h2 => by
        obtain ⟨_, hK, h8, h9, h22⟩ := envDefineRest_facts R hA hRes h2
        exact (abi R hA h8 h9).trans (Sf.gm_keep R hK h22)
      saved := hsaved
      stack := hframe.stack
      ainv := hframe.ainv }

/-! ## 3. The grow lane's entry, named -/

/-- **The grow lane's entry data**: the miss facts and registers at the
memory `mA` over the live extents `extsA`, the full frame, the array reads,
the request bound, the arm kind and the names array in `s6`. -/
inductive EnvDefineGrowEntry (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (extsA : List Extent) (mA : Mem)
    (c : Config) : Prop where
  | intro (cap pn pvals : Nat)
      (facts : EnvDefineMissFacts g N A SL φf φc st env x v esp aEnv aName pv r m extsA mA cap)
      (regs : EnvDefineMissRegs g A SL st env esp aEnv aName pv r out M extsA mA facts.env_lt c)
      (full : (st.store.frames[env]'facts.env_lt).vars.length = cap)
      (names : read64 mA (φf env + 8) = some pn)
      (values : read64 mA (φf env + 16) = some pvals)
      (req : 48 * cap ≤ maxReq)
      (kind : EnvDefineGrowKind cap c)
      (s6 : c.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 pn))

/-- **The grow lane from its entry to the return state**: `envDefineGrowLane`
to the append head, then `envDefineAppendLane`. -/
theorem envDefineGrowEntry_run
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts extsA : List Extent) (mA : Mem)
    (hE : EnvDefineMem N A SL φf φc st env x v aEnv aName pv esp m)
    (L : EnvDefineUpdateLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (LM : EnvDefineMissLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (budget : ResourceBudget A maxReq extsA 3)
    (reserve : AllocationReserve A mA extsA maxReq 3) :
    Triple (EnvDefineGrowEntry g N A SL φf φc st env x v esp aEnv aName pv r m out M extsA mA)
      (EnvDefineReturnState g N A SL φf φc st env x v esp r m out) := by
  intro c0 E
  obtain ⟨cap, pn, pvals, F, R, hfull, hpn, hpvals, hreq, K, hs6⟩ := E
  obtain ⟨c1, extsA', mA', cap', hs1, H⟩ :=
    envDefineGrowLane (credits := 1) g N A SL φf φc st env x v esp aEnv aName pv r m out M exts extsA mA
      cap pn pvals c0 hE L LM F R hfull hpn hpvals hreq K hs6 budget reserve
  obtain ⟨c2, hs2, hret⟩ :=
    envDefineAppendLane g N A SL φf φc st env x v esp aEnv aName pv r m out M exts extsA' mA'
      cap' hE L LM H.budget H.reserve c1 H.head
  exact ⟨c2, hs1.trans hs2, hret⟩

/-! ## 4. The arms to the return state -/

/-- **The non-empty miss lane from the cap dispatch.**  The append arm is the
append head; the grow arm is the grow entry (`EnvDefineGrowKind.grow`, the
frame full, `a5 = cap`, `s6 = names`). -/
theorem envDefineMissReady_run
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (hE : EnvDefineMem N A SL φf φc st env x v aEnv aName pv esp m)
    (L : EnvDefineUpdateLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (LM : EnvDefineMissLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts) :
    Triple
      (fun c => ∃ (v8 v9 v18 v19 v20 v21 v22 : BitVec 64) (pn : Nat)
        (gm : (R : Register) → Option (RegisterType R)),
        EnvDefineMissReady g N A SL φf φc st env x v esp aEnv aName pv r m out M exts
          v8 v9 v18 v19 v20 v21 v22 pn gm c)
      (EnvDefineReturnState g N A SL φf φc st env x v esp r m out) := by
  intro c ⟨v8, v9, v18, v19, v20, v21, v22, pn, gm, R⟩
  have Sf := R.facts
  have scannedReserve := LM.reserve_after_spills hE.stack Sf.mem_agree
  have henvLt := Sf.env_lt
  have hAhi := L.alloc.arena_ram.2
  obtain ⟨hcountR, ⟨cap, hcapR, hcaple⟩, ⟨pn', pvals, hpn', hpvals, _⟩, _⟩ :=
    Sf.store0.frames env henvLt
  have hpnEq : pn' = pn := Option.some.inj (hpn'.symm.trans Sf.pn_read)
  subst pn'
  have hcapSigned : cap < 2^31 := by
    obtain ⟨alloc, shared, readable, writes, hheap, _, _, _⟩ := Sf.owned0
    exact (hheap.store.frames env henvLt).capSigned hheap.ledger hcapR hAhi
  have F := envDefineMissFacts_of_scan g N A SL φf φc st env x v esp aEnv aName pv r m M exts
    v8 v9 v18 v19 v20 v21 v22 pn gm hE L LM Sf R.miss cap hcapR
  have hsp1 := hE.stack.1
  have hAstack := hE.arena_stack
  obtain ⟨henvArena, _⟩ := hE.store.frames_arena env henvLt
  unfold Arena.contains at henvArena
  have hAg : AgreeP (fun a => a < esp.toNat - 64 ∨ esp.toNat ≤ a) m
      (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) :=
    fun a ha => (Sf.mem_agree a ha).symm
  have hrec : ∀ k, φf env ≤ k → k < φf env + 32 → (k < esp.toNat - 64 ∨ esp.toNat ≤ k) := by
    intro k hk1 hk2
    rcases hAstack with hA | hA
    · left; omega
    · right; omega
  have hcapM : read32 m (φf env + 4) = some cap := by
    rw [read32_agreeP hAg (fun k hk => hrec _ (by omega) (by omega))]; exact hcapR
  rcases R.cap.arms with ⟨cap', i, lds, hroom, hidx, hpost, hsaved, hcapArm, ha5⟩ |
      ⟨cap', i, lds, hfull, hidx, hpost, hsaved, hcapArm, ha5⟩
  · have hcapEq : cap' = cap := by
      rw [Sf.env_addr] at hcapArm
      exact Option.some.inj (hcapArm.symm.trans hcapR)
    subst hcapEq
    have Rg := envDefineMissRegs_of_arm g N A SL φf φc st env x v esp aEnv aName pv r m out M
      exts v8 v9 v18 v19 v20 v21 v22 pn gm Sf hpost hsaved
    exact envDefineAppendLane g N A SL φf φc st env x v esp aEnv aName pv r m out M exts exts
      _ cap' hE L LM (LM.budget.mono (by decide : 1 ≤ 3))
        (scannedReserve.mono (by decide : 1 ≤ 3)) c ⟨F, Rg, hpost.1.2.2.1, hroom⟩
  · have hcapEq : cap' = cap := by
      rw [Sf.env_addr] at hcapArm
      exact Option.some.inj (hcapArm.symm.trans hcapR)
    subst hcapEq
    have Rg := envDefineMissRegs_of_arm g N A SL φf φc st env x v esp aEnv aName pv r m out M
      exts v8 v9 v18 v19 v20 v21 v22 pn gm Sf hpost hsaved
    have hpos : 0 < cap' := by omega
    have hs6 : c.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 pn) :=
      (hpost.2.abi _ (by decide)).trans
        ((envDefineScanGhost_ne gm _ _ (by decide) (by decide)).trans Sf.gm_s6)
    exact envDefineGrowEntry_run g N A SL φf φc st env x v esp aEnv aName pv r m out M exts exts
      _ hE L LM LM.budget scannedReserve c
        ⟨cap', pn, pvals, F, Rg, hfull, Sf.pn_read, hpvals, LM.grow_req cap' hcapM,
        .grow hpos hpost.1.2.2.1 ha5, hs6⟩

#print axioms EnvDefineMissCapResult.arms
#print axioms envDefineMissFacts_of_scan
#print axioms envDefineMissRegs_of_arm
#print axioms envDefineGrowEntry_run
#print axioms envDefineMissReady_run

end Vsa.Sim
