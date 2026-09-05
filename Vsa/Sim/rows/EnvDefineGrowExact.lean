import Vsa.Sim.rows.EnvDefineAppendExact
import Vsa.Sim.EnvDefBridges4
import Vsa.Sim.EnvGetSpec7

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.MemRepr
open Vsa.RuntimeRepr
open Vsa.Logic (Triple)

namespace Vsa.Sim

@[simp] private theorem growLine0 : mkLine 0x80002bc0#64 0x008a3783#32 =
    ⟨0x80002bc0#64, 0x008a3783#32, 0x83#8, 0x37#8, 0x8a#8, 0x00#8,
      .ld, 15, 20, 0, 0x008#12⟩ := by rfl

@[simp] private theorem growLine1 : mkLine 0x80002bc4#64 0x00aa3823#32 =
    ⟨0x80002bc4#64, 0x00aa3823#32, 0x23#8, 0x38#8, 0xaa#8, 0x00#8,
      .sd, 0, 20, 10, 0x010#12⟩ := by rfl

/-- The grow rejoin row with the live helper stack pointer retained. -/
theorem appendHeadRowSp (env valsNew sp : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) :
    Triple
      (fun c => SegPre appendHeadSeg (appendHeadL env valsNew) lds
          0x80002bc0#64 m0 c ∧ c.σ.regs.get? Register.x2 = some sp)
      (fun c => AppendHeadPost env valsNew lds m0 c ∧
        c.σ.regs.get? Register.x2 = some sp ∧ c.tick < 2) := by
  intro c ⟨hpre, hsp⟩
  obtain ⟨hG, hmem, hpc, ⟨vm, hmi⟩, hL, hkeys, hfacts, htick⟩ := hpre
  obtain ⟨σ', i', hs, hi', hG', hmem', _hout, hpc', _hmi', _hregs', hframe⟩ :=
    segEval_sound appendHeadSeg c.σ c.tick c.steps 0x80002bc0#64 vm
      (appendHeadL env valsNew) lds hG hpc hmi hL hkeys hfacts
      (by show ChainOK 0x80002bc0#64 [20, 10] appendHeadSeg; decide) htick
  rw [hmem] at hmem'
  refine ⟨⟨σ', i', c.steps + evalBlocksFuel appendHeadSeg⟩, hs,
    ⟨⟨hG', hmem', ?_⟩, ?_, hi'⟩⟩
  · rw [hpc']; rfl
  · exact (hframe Register.x2 (by decide) (by decide)).trans hsp

/-- The grow rejoin performs exactly `env->vals := valsNew`. -/
theorem appendHeadLogExact (env valsNew : BitVec 64)
    (lds : List (List (BitVec 8)))
    (henvHi : env.toNat + 24 ≤ 2^64) :
    (evalBlocks appendHeadSeg
      (SegEvalState.init (appendHeadL env valsNew) lds)).log =
      [(env.toNat + 16, 8, valsNew)] := by
  simp [appendHeadSeg, evalBlocks, evalBlock, SegEvalState.init, wlogM,
    wentryM, widthOfM, runGM, stepGM, wvalM, srcVal, lookupG,
    eaddrM, mkLine, decodeM]
  constructor
  · simp [appendHeadL, lookupG, eraseG]
    have h16 : (sign_extend (m := 64) (16#12) : BitVec 64).toNat = 16 := by decide
    rw [h16, Nat.mod_eq_of_lt (by omega)]
  · simp [appendHeadL, lookupG, eraseG]

/-- Exact grow-rejoin memory image. -/
theorem appendHeadMemoryExact (env valsNew : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem)
    (henvHi : env.toNat + 24 ≤ 2^64) :
    writeLog m0 (evalBlocks appendHeadSeg
      (SegEvalState.init (appendHeadL env valsNew) lds)).log =
      writeMap8 m0 (env.toNat + 16) (sdData_val valsNew) := by
  rw [appendHeadLogExact env valsNew lds henvHi]
  rfl

/-- Arena geometry proves the grow rejoin cannot disturb code or saved spills. -/
structure AppendHeadPublicFrame
    (sp env valsNew : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Mem) : Prop where
  code : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 →
    (writeLog m0 (evalBlocks appendHeadSeg
      (SegEvalState.init (appendHeadL env valsNew) lds)).log)[a]? = m0[a]?
  spills : ∀ a, sp.toNat ≤ a → a < sp.toNat + 64 →
    (writeLog m0 (evalBlocks appendHeadSeg
      (SegEvalState.init (appendHeadL env valsNew) lds)).log)[a]? = m0[a]?

/-- Exact load/store geometry for the four-instruction grow rejoin. -/
structure AppendHeadGeom (env names valsNew : BitVec 64) (m : Mem) : Prop where
  namesRead : read64 m (env.toNat + 8) = some names.toNat
  namesNonzero : names ≠ 0#64
  valsNonzero : valsNew ≠ 0#64
  envHi64 : env.toNat + 24 ≤ 2^64
  namesLo : 0x80000000 ≤ env.toNat + 8
  namesHi : env.toNat + 16 ≤ 0x100000000
  namesHtif : env.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 8 ≤ env.toNat + 8
  namesAlign : (env.toNat + 8) % 8 = 0
  valsLo : 0x80000000 ≤ env.toNat + 16
  valsHi : env.toNat + 24 ≤ 0x100000000
  valsHtif : tohostAddr + 16 ≤ env.toNat + 16
  valsAlign : (env.toNat + 16) % 8 = 0

private theorem appendHeadMemFactsLd
    {m : Mem} {L : GRegs} {a : MInstr} {bs : List (BitVec 8)}
    (base : Nat) (hk : a.kind = .ld) (hea : (eaddrM a L).toNat = base)
    (hlo : 0x80000000 ≤ base) (hhi : base + 8 ≤ 0x100000000)
    (hht : base + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ base)
    (hal : base % 8 = 0) (hp : LPins8 m base bs) : MemFacts m L bs a := by
  unfold MemFacts
  rw [hk, hea]
  exact ⟨⟨hlo, hhi, hht, hal⟩, hp⟩

private theorem appendHeadMemFactsSd
    {m : Mem} {L : GRegs} {a : MInstr} {bs : List (BitVec 8)}
    (base : Nat) (hk : a.kind = .sd) (hea : (eaddrM a L).toNat = base)
    (hlo : 0x80000000 ≤ base) (hhi : base + 8 ≤ 0x100000000)
    (hht : tohostAddr + 16 ≤ base) (hal : base % 8 = 0) :
    MemFacts m L bs a := by
  unfold MemFacts
  rw [hk, hea]
  exact ⟨hlo, hhi, hht, hal⟩

/-- The current names field and non-NULL realloc results generate every
non-computable fact required by `appendHeadSeg`. -/
theorem appendHeadFacts
    (env names valsNew : BitVec 64) (m : Mem)
    (hcode : Vsa.Sim.Code.Env_defineLoaded m)
    (hgeom : AppendHeadGeom env names valsNew m) :
    ∃ lds, ChainFacts m m (appendHeadL env valsNew) lds appendHeadSeg := by
  obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,h0,h1,h2,h3,h4,h5,h6,h7,hval⟩ :=
    read64_bytes_eg4 m (env.toNat + 8) names.toNat hgeom.namesRead
  let lds := [[b0,b1,b2,b3,b4,b5,b6,b7]]
  have hp : LPins8 m (env.toNat + 8) [b0,b1,b2,b3,b4,b5,b6,b7] :=
    ⟨lpin_of_present h0, lpin_of_present h1, lpin_of_present h2,
      lpin_of_present h3, lpin_of_present h4, lpin_of_present h5,
      lpin_of_present h6, lpin_of_present h7⟩
  have hloaded : bytesVal .ld [b0,b1,b2,b3,b4,b5,b6,b7] = names := by
    simpa using ld_value_eq_read64 m (env.toNat + 8) names.toNat
      b0 b1 b2 b3 b4 b5 b6 b7 hgeom.namesRead h0 h1 h2 h3 h4 h5 h6 h7
  have hloaded' :
      sign_extend (m := 64)
        (b7 +++ b6 +++ b5 +++ b4 +++ b3 +++ b2 +++ b1 +++ b0) = names := by
    simpa [bytesVal] using hloaded
  have hloadedNZ :
      sign_extend (m := 64)
        (b7 +++ b6 +++ b5 +++ b4 +++ b3 +++ b2 +++ b1 +++ b0) ≠ 0#64 := by
    rw [hloaded']
    exact hgeom.namesNonzero
  have henvHi := hgeom.envHi64
  refine ⟨lds, ?_⟩
  chain_facts hcode with "Vsa.Sim.Code.env_define_at_"
  · refine appendHeadMemFactsLd (env.toNat + 8) (by rfl) ?_
      hgeom.namesLo hgeom.namesHi hgeom.namesHtif hgeom.namesAlign ?_
    · simp [growLine0, eaddrM, appendHeadL, srcVal, lookupG]
      rw [show (sign_extend (m := 64) (8#12) : BitVec 64).toNat = 8 by decide,
        Nat.mod_eq_of_lt (by omega)]
    · simpa [lds] using hp
  · refine appendHeadMemFactsSd (env.toNat + 16) (by rfl) ?_
      hgeom.valsLo hgeom.valsHi hgeom.valsHtif hgeom.valsAlign
    simp [growLine0, growLine1, eaddrM, stepGM, wvalM, bytesVal,
      appendHeadL, srcVal, lookupG, eraseG, lds]
    rw [show (sign_extend (m := 64) (16#12) : BitVec 64).toNat = 16 by decide,
      Nat.mod_eq_of_lt (by omega)]
  · simpa [growLine0, growLine1, runGM, stepGM, wvalM, bytesVal, appendHeadL,
      srcVal, lookupG, eraseG, lds, guardB] using hloadedNZ
  · simp [growLine0, growLine1, runGM, stepGM, wvalM, bytesVal, appendHeadL,
      srcVal, lookupG, eraseG, lds, guardB, hgeom.valsNonzero]

theorem appendHeadPublicFrame
    (A : Arena) (env valsNew sp : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem)
    (henvHi : env.toNat + 24 ≤ 2^64)
    (henvA : A.contains (env.toNat + 16) 8)
    (harenaStack : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo) :
    AppendHeadPublicFrame sp env valsNew lds m0 := by
  refine ⟨?_, ?_⟩
  · intro a ha0 ha1
    rw [appendHeadMemoryExact env valsNew lds m0 henvHi,
      getElem_writeMap8_disjoint]
    rcases henvA with ⟨hlo, hhi⟩
    rcases harenaCode with h | h <;> omega
  · intro a ha0 ha1
    rw [appendHeadMemoryExact env valsNew lds m0 henvHi,
      getElem_writeMap8_disjoint]
    rcases henvA with ⟨hlo, hhi⟩
    rcases harenaStack with h | h <;> omega

/-- Explicit bounded-request elimination of realloc's NULL branch. -/
theorem reallocGrowSuccess_of_bounded
    {A : Arena} {SL : Vsa.Alloc.StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat}
    {AInv : Vsa.Machine.MState → List Extent → Prop}
    {privFoot : Nat → Prop}
    (RO : ReallocOps A SL gpv headroom maxReq AInv privFoot)
    (g : (R : Register) → Option (RegisterType R))
    (exts : List Extent) (pOld nOld nNew : Nat) (sp r : BitVec 64)
    (m0 : Mem) (c : Config) (hle : nNew ≤ maxReq)
    (h : ReallocPost gpv sp r g c ∧
      ReallocGrowResult A SL privFoot AInv exts pOld nOld nNew sp m0 c.σ) :
    ∃ pNew,
      c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 pNew) ∧
      pNew ≠ 0 ∧ pNew % 16 = 0 ∧ A.contains pNew nNew ∧
      (∀ e ∈ exts, e ≠ (pOld, nOld) →
        Vsa.Alloc.ExtDisjoint (pNew, nNew) e) ∧
      ReallocCopies m0 c.σ.mem pOld pNew nOld ∧
      AInv c.σ ((pNew, nNew) :: exts.erase (pOld, nOld)) ∧
      HeapPublicFrame privFoot SL sp [(pOld, nOld), (pNew, nNew)] m0 c.σ.mem :=
  RO.nonNullGrow_of_bounded c.σ exts pOld nOld nNew sp m0 hle h.2

/-- Exact public-memory geometry needed after the second realloc. -/
structure AppendHeadReallocPublic
    (privFoot : Nat → Prop) (SL : Vsa.Alloc.StackLayout)
    (sp : BitVec 64) (pOld nOld pNew nNew env : Nat) : Prop where
  names : ∀ k, k < 8 →
    ¬ privFoot (env + 8 + k) ∧
    ¬ (SL.lo ≤ env + 8 + k ∧ env + 8 + k < sp.toNat) ∧
    (∀ e ∈ [(pOld, nOld), (pNew, nNew)],
      env + 8 + k < e.1 ∨ e.1 + e.2 ≤ env + 8 + k)
  code : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 →
    ¬ privFoot a ∧
    ¬ (SL.lo ≤ a ∧ a < sp.toNat) ∧
    (∀ e ∈ [(pOld, nOld), (pNew, nNew)], a < e.1 ∨ e.1 + e.2 ≤ a)

/-- Public windows needed between the first and second realloc calls. -/
structure NamesReallocPublic
    (privFoot : Nat → Prop) (SL : Vsa.Alloc.StackLayout)
    (sp : BitVec 64) (pOld nOld pNew nNew env : Nat) : Prop where
  cap : ∀ k, k < 4 →
    ¬ privFoot (env + 4 + k) ∧
    ¬ (SL.lo ≤ env + 4 + k ∧ env + 4 + k < sp.toNat) ∧
    (∀ e ∈ [(pOld, nOld), (pNew, nNew)],
      env + 4 + k < e.1 ∨ e.1 + e.2 ≤ env + 4 + k)
  vals : ∀ k, k < 8 →
    ¬ privFoot (env + 16 + k) ∧
    ¬ (SL.lo ≤ env + 16 + k ∧ env + 16 + k < sp.toNat) ∧
    (∀ e ∈ [(pOld, nOld), (pNew, nNew)],
      env + 16 + k < e.1 ∨ e.1 + e.2 ≤ env + 16 + k)
  code : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 →
    ¬ privFoot a ∧
    ¬ (SL.lo ≤ a ∧ a < sp.toNat) ∧
    (∀ e ∈ [(pOld, nOld), (pNew, nNew)], a < e.1 ∨ e.1 + e.2 ≤ a)

/-- The first bounded realloc produces the exact carrier consumed by the
finite names-to-values staging lane. -/
theorem growEnvEntry_of_realloc
    {A : Arena} {SL : Vsa.Alloc.StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat}
    {AInv : Vsa.Machine.MState → List Extent → Prop}
    {privFoot : Nat → Prop}
    (RO : ReallocOps A SL gpv headroom maxReq AInv privFoot)
    (g saved : (R : Register) → Option (RegisterType R))
    (exts : List Extent) (pOld nOld nNew pValsOld capw : Nat)
    (sp env : BitVec 64) (m0 : Mem)
    (hle : nNew ≤ maxReq) (hnGrow : nOld < nNew)
    (hstack : Vsa.Alloc.StackOK SL sp headroom)
    (henvReg : g Register.x20 = some env)
    (hcode : Vsa.Sim.Code.Env_defineLoaded m0)
    (hcap : read32 m0 (env.toNat + 4) = some capw)
    (hvals : read64 m0 (env.toNat + 16) = some pValsOld)
    (hgeom : ∀ pNew,
      NamesReallocPublic privFoot SL sp pOld nOld pNew nNew env.toNat)
    (hArenaHi : A.hi ≤ 2^64) :
    Triple
      (fun c => (ReallocPost gpv sp 0x80002ba4#64 g c ∧
        ReallocGrowResult A SL privFoot AInv exts pOld nOld nNew sp m0 c.σ) ∧
        EnvDefineSavedSpillFrame sp saved c)
      (fun c => ∃ pNew,
        (GrowEnvEntry SL gpv headroom AInv
          ((pNew, nNew) :: exts.erase (pOld, nOld)) sp g env
          (BitVec.ofNat 64 pNew) pValsOld capw c.σ.mem c ∧
         EnvDefineSavedSpillFrame sp saved c) ∧
        pNew ≠ 0 ∧ A.contains pNew nNew) := by
  intro c h
  have hr := h.1
  obtain ⟨pNew, hx10, hpNew, _halign, hpArena, _hdis, _hcopy, hAInv, hframe⟩ :=
    reallocGrowSuccess_of_bounded RO g exts pOld nOld nNew sp 0x80002ba4#64 m0 c hle hr
  have hnNewPos : 0 < nNew := by omega
  have hpNewLt : pNew < 2^64 := by
    have := hpArena.2
    omega
  have hpublic := hgeom pNew
  have hloaded : Vsa.Sim.Code.Env_defineLoaded c.σ.mem := by
    apply loaded_envdef_of_agree m0 c.σ.mem _ hcode
    intro a ha0 ha1
    obtain ⟨hpriv, hstk, hext⟩ := hpublic.code a ha0 ha1
    exact hframe a hpriv hstk hext
  have hcap' : read32 c.σ.mem (env.toNat + 4) = some capw := by
    have hagree : AgreeP (fun a => env.toNat + 4 ≤ a ∧ a < env.toNat + 8)
        c.σ.mem m0 := by
      intro a ha
      have hk : a = env.toNat + 4 + (a - (env.toNat + 4)) := by omega
      have hklt : a - (env.toNat + 4) < 4 := by omega
      obtain ⟨hpriv, hstk, hext⟩ := hpublic.cap _ hklt
      rw [← hk] at hpriv hstk hext
      exact hframe a hpriv hstk hext
    rw [read32_agreeP hagree (by intro k hk; omega)]
    exact hcap
  have hvals' : read64 c.σ.mem (env.toNat + 16) = some pValsOld := by
    have hagree : AgreeP (fun a => env.toNat + 16 ≤ a ∧ a < env.toNat + 24)
        c.σ.mem m0 := by
      intro a ha
      have hk : a = env.toNat + 16 + (a - (env.toNat + 16)) := by omega
      have hklt : a - (env.toNat + 16) < 8 := by omega
      obtain ⟨hpriv, hstk, hext⟩ := hpublic.vals _ hklt
      rw [← hk] at hpriv hstk hext
      exact hframe a hpriv hstk hext
    rw [read64_agreeP hagree (by intro k hk; omega)]
    exact hvals
  have hx20 : c.σ.regs.get? Register.x20 = some env := by
    rw [hr.1.2.2.2.2.2 Register.x20 (by decide)]
    exact henvReg
  have hspills : EnvDefineSpillFrame sp g c := by
    obtain ⟨lds, himage, _hvalues⟩ := h.2
    exact ⟨lds, himage⟩
  refine ⟨c, .refl c, pNew, ⟨?_, h.2⟩, hpNew, hpArena⟩
  exact
    { good := hr.1.1
      loadedD := hloaded
      memEq := rfl
      pc := hr.1.2.2.1
      s4 := hx20
      namesRes := by simpa [Nat.mod_eq_of_lt hpNewLt] using hx10
      minstret := hr.1.1.minstret
      tick := hr.1.2.1
      capEq := hcap'
      valsEq := hvals'
      frame := ⟨hr.1.2.2.2.1, hstack, hr.1.2.2.2.2.1,
        hr.1.2.2.2.2.2, hAInv, hr.1.2.1, hspills⟩ }

/-- The values-pointer tie required by the finite names-to-values lane follows
directly from `read64`; it is not a residual oracle. -/
theorem namesToValsPointerTie
    (s4Ptr : BitVec 64) (pValsOld : Nat) :
    ∀ (m : Mem), read64 m (s4Ptr.toNat + 16) = some pValsOld →
      ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8),
        m[s4Ptr.toNat + 16]? = some b0 → m[s4Ptr.toNat + 17]? = some b1 →
        m[s4Ptr.toNat + 18]? = some b2 → m[s4Ptr.toNat + 19]? = some b3 →
        m[s4Ptr.toNat + 20]? = some b4 → m[s4Ptr.toNat + 21]? = some b5 →
        m[s4Ptr.toNat + 22]? = some b6 → m[s4Ptr.toNat + 23]? = some b7 →
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 pValsOld := by
  intro m hread b0 b1 b2 b3 b4 b5 b6 b7 h0 h1 h2 h3 h4 h5 h6 h7
  exact ld_value_eq_read64 m (s4Ptr.toNat + 16) pValsOld
    b0 b1 b2 b3 b4 b5 b6 b7 hread h0 h1 h2 h3 h4 h5 h6 h7

/-- The second realloc size is exactly the reflected `cap * 24` computation. -/
theorem namesToValsSizeTie (capw nValsNew : Nat)
    (hcap : capw < 2^31) (hn : nValsNew = 24 * capw) :
    ∀ (c0 c1 c2 c3 : BitVec 8),
      c0.toNat + 256 * (c1.toNat + 256 * (c2.toNat + 256 * c3.toNat)) = capw →
      shift_bits_left
        ((shift_bits_left
            (sign_extend (m := 64) ((((c3.append c2).append c1).append c0) : BitVec (8 * 4)))
            (Sail.BitVec.extractLsb (0x01#6) 5 0)) +
          sign_extend (m := 64) ((((c3.append c2).append c1).append c0) : BitVec (8 * 4)))
        (Sail.BitVec.extractLsb (0x03#6) 5 0) = BitVec.ofNat 64 nValsNew := by
  intro c0 c1 c2 c3 hrec
  rw [sext_count_eg7 c0 c1 c2 c3 capw hcap hrec, hn]
  exact stride_24 capw (by omega)

/-- The finite names-to-values lane, with its read ties and address arithmetic
derived internally. The saved spill carrier is transported through its sole
`env->names` write. -/
theorem namesToVals_of_growEntry
    (SL : Vsa.Alloc.StackLayout) (gpv : BitVec 64) (headroom : Nat)
    {AInv : Vsa.Machine.MState → List Extent → Prop}
    (extsV : List Extent) (sp : BitVec 64)
    (g gV saved : (R : Register) → Option (RegisterType R))
    (env pNamesNew : BitVec 64) (pValsOld nValsNew capw : Nat) (mN : Mem)
    (hcapSmall : capw < 2^31) (hnVals : nValsNew = 24 * capw)
    (hgVtie : ∀ R, Vsa.Alloc.AbiPreserved R = true →
      R ≠ Register.x15 → R ≠ Register.x10 → R ≠ Register.x11 →
      R ≠ Register.x1 → gV R = g R)
    (henvHi : env.toNat + 24 ≤ 2^64)
    (hnlo : 0x80000000 ≤ env.toNat + 8)
    (hnhiram : env.toNat + 16 ≤ 0x100000000)
    (hnhiwin : tohostAddr + 16 ≤ env.toNat + 8)
    (hnalign : (env.toNat + 8) % 8 = 0)
    (hclo : 0x80000000 ≤ env.toNat + 4)
    (hchiram : env.toNat + 8 ≤ 0x100000000)
    (hchtif : env.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ env.toNat + 4)
    (hcalign : (env.toNat + 4) % 4 = 0)
    (hvlo : 0x80000000 ≤ env.toNat + 16)
    (hvhiram : env.toNat + 24 ≤ 0x100000000)
    (hvhtif : env.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 8 ≤ env.toNat + 16)
    (hvalign : (env.toNat + 16) % 8 = 0)
    (hnamesCode : env.toNat + 16 ≤ 0x80002a5c ∨
      0x80002c10 ≤ env.toNat + 8)
    (hnamesSpill : env.toNat + 16 ≤ sp.toNat ∨
      sp.toNat + 64 ≤ env.toNat + 8)
    (hAInvStableNames : ∀ (σa σb : Vsa.Machine.MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a : Nat, (a < env.toNat + 8 ∨ env.toNat + 16 ≤ a) →
        σa.mem[a]? = σb.mem[a]?) →
      AInv σa extsV → AInv σb extsV) :
    Triple
      (fun c => GrowEnvEntry SL gpv headroom AInv extsV sp g env pNamesNew
          pValsOld capw mN c ∧ EnvDefineSavedSpillFrame sp saved c)
      (fun c => ReallocPre SL gpv headroom AInv extsV pValsOld nValsNew sp
          0x80002bc0#64 (writeMap8 mN (env.toNat + 8) (sdData_val pNamesNew)) gV c ∧
        EnvDefineSavedSpillFrame sp saved c) := by
  intro c h
  have hcapAddr :
      (env + sign_extend (m := 64) (0x004#12)).toNat = env.toNat + 4 := by
    apply off_pos_eg6 env 0x004#12 4 (by decide)
    omega
  have hvalsAddr :
      (env + sign_extend (m := 64) (0x010#12)).toNat = env.toNat + 16 := by
    apply off_pos_eg6 env 0x010#12 16 (by decide)
    omega
  have hnamesAddr :
      (env + sign_extend (m := 64) (0x008#12)).toNat = env.toNat + 8 := by
    apply off_pos_eg6 env 0x008#12 8 (by decide)
    omega
  obtain ⟨c', hs, hpre⟩ :=
    bridgeNamesToVals_closed SL gpv headroom extsV sp g gV env pNamesNew
      pValsOld nValsNew capw mN (namesToValsPointerTie env pValsOld)
      (namesToValsSizeTie capw nValsNew hcapSmall hnVals) hgVtie
      hcapAddr hvalsAddr hnamesAddr hnlo hnhiram hnhiwin hnalign
      hclo hchiram hchtif hcalign hvlo hvhiram hvhtif hvalign
      hnamesCode hAInvStableNames c h.1
  have hpre' := hpre
  obtain ⟨_hgood, _htick, _hpc, _hx10, _hx11, _hra, _hral,
    _hsp, _hstack, _hgp, _habi, _hAInv, hmem⟩ := hpre
  have hsaved' : EnvDefineSavedSpillFrame sp saved c' := by
    apply h.2.of_interval_agree
    · intro a ha0 ha1
      rw [hmem, h.1.memEq]
      exact getElem_writeMap8_disjoint mN (env.toNat + 8) a
        (sdData_val pNamesNew) (by rcases hnamesCode with h | h <;> omega)
    · intro a ha0 ha1
      rw [hmem, h.1.memEq]
      exact getElem_writeMap8_disjoint mN (env.toNat + 8) a
        (sdData_val pNamesNew) (by rcases hnamesSpill with h | h <;> omega)
  exact ⟨c', hs, hpre', hsaved'⟩

/-- Bounded realloc preserves the value-related outer spill image. The
allocator frame and arena separation discharge both code and stack windows. -/
theorem reallocGrowSaved
    {A : Arena} {SL : Vsa.Alloc.StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat}
    {AInv : Vsa.Machine.MState → List Extent → Prop}
    {privFoot : Nat → Prop}
    (RO : ReallocOps A SL gpv headroom maxReq AInv privFoot)
    (g saved : (R : Register) → Option (RegisterType R))
    (exts : List Extent) (pOld nOld nNew : Nat) (sp r : BitVec 64) (m0 : Mem)
    (hle : nNew ≤ maxReq) (hlt : nOld < nNew) (hpOld : pOld ≠ 0)
    (hmem : (pOld, nOld) ∈ exts) (hOldArena : A.contains pOld nOld)
    (hArenaSpill : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo)
    (hArenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo)
    (hPrivCode : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 → ¬ privFoot a)
    (hPrivSpill : ∀ a, sp.toNat ≤ a → a < sp.toNat + 64 → ¬ privFoot a)
    (hCodeStack : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 →
      ¬ (SL.lo ≤ a ∧ a < sp.toNat)) :
    Triple
      (fun c => ReallocPre SL gpv headroom AInv exts pOld nNew sp r m0 g c ∧
        EnvDefineSavedSpillFrame sp saved c)
      (fun c => (ReallocPost gpv sp r g c ∧
        ReallocGrowResult A SL privFoot AInv exts pOld nOld nNew sp m0 c.σ) ∧
        EnvDefineSavedSpillFrame sp saved c) := by
  intro c h
  have hmem0 : c.σ.mem = m0 := h.1.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨c', hs, hpost, hresult⟩ :=
    RO.grow g exts pOld nOld nNew sp r m0 hle hlt hpOld hmem c h.1
  obtain ⟨pNew, _hx10, _hnz, _halign, hNewArena, _hdis, _hcopy, _hAInv, hpublic⟩ :=
    RO.nonNullGrow_of_bounded c'.σ exts pOld nOld nNew sp m0 hle hresult
  have hsaved' : EnvDefineSavedSpillFrame sp saved c' := by
    apply h.2.of_interval_agree
    · intro a ha0 ha1
      have houtOld : a < pOld ∨ pOld + nOld ≤ a := by
        rcases hOldArena with ⟨hlo, hhi⟩
        rcases hArenaCode with hbefore | hafter <;> omega
      have houtNew : a < pNew ∨ pNew + nNew ≤ a := by
        rcases hNewArena with ⟨hlo, hhi⟩
        rcases hArenaCode with hbefore | hafter <;> omega
      exact (hpublic a (hPrivCode a ha0 ha1) (hCodeStack a ha0 ha1)
        (by intro e he; simp only [List.mem_cons] at he
            rcases he with rfl | rfl | h <;> simp_all)).trans
        (congrArg (fun m => m[a]?) hmem0.symm)
    · intro a ha0 ha1
      have houtOld : a < pOld ∨ pOld + nOld ≤ a := by
        rcases hOldArena with ⟨hlo, hhi⟩
        rcases hArenaSpill with hbefore | hafter <;> omega
      have houtNew : a < pNew ∨ pNew + nNew ≤ a := by
        rcases hNewArena with ⟨hlo, hhi⟩
        rcases hArenaSpill with hbefore | hafter <;> omega
      exact (hpublic a (hPrivSpill a ha0 ha1) (by omega)
        (by intro e he; simp only [List.mem_cons] at he
            rcases he with rfl | rfl | h <;> simp_all)).trans
        (congrArg (fun m => m[a]?) hmem0.symm)
  exact ⟨c', hs, ⟨hpost, hresult⟩, hsaved'⟩

/-- A bounded second realloc lands directly in the reflected grow rejoin.
The only extra assumptions are numeric access geometry and public-footprint
separation; success, the returned pointer, code survival, and the names-field
readback are derived from `ReallocOps`. -/
theorem appendHeadSegPre_of_realloc
    {A : Arena} {SL : Vsa.Alloc.StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat}
    {AInv : Vsa.Machine.MState → List Extent → Prop}
    {privFoot : Nat → Prop}
    (RO : ReallocOps A SL gpv headroom maxReq AInv privFoot)
    (g : (R : Register) → Option (RegisterType R))
    (saved : (R : Register) → Option (RegisterType R))
    (exts : List Extent) (pOld nOld nNew : Nat) (sp : BitVec 64)
    (env names : BitVec 64) (m0 : Mem)
    (hle : nNew ≤ maxReq)
    (hnGrow : nOld < nNew)
    (henvReg : g Register.x20 = some env)
    (hcode : Vsa.Sim.Code.Env_defineLoaded m0)
    (hnamesRead : read64 m0 (env.toNat + 8) = some names.toNat)
    (hnamesNonzero : names ≠ 0#64)
    (hgeom : ∀ pNew,
      AppendHeadReallocPublic privFoot SL sp pOld nOld pNew nNew env.toNat)
    (hArenaHi : A.hi ≤ 2^64)
    (henvHi : env.toNat + 24 ≤ 2^64)
    (hnamesLo : 0x80000000 ≤ env.toNat + 8)
    (hnamesHi : env.toNat + 16 ≤ 0x100000000)
    (hnamesHtif : env.toNat + 16 ≤ tohostAddr ∨
      tohostAddr + 8 ≤ env.toNat + 8)
    (hnamesAlign : (env.toNat + 8) % 8 = 0)
    (hvalsLo : 0x80000000 ≤ env.toNat + 16)
    (hvalsHi : env.toNat + 24 ≤ 0x100000000)
    (hvalsHtif : tohostAddr + 16 ≤ env.toNat + 16)
    (hvalsAlign : (env.toNat + 16) % 8 = 0) :
    Triple
      (fun c => (ReallocPost gpv sp 0x80002bc0#64 g c ∧
        ReallocGrowResult A SL privFoot AInv exts pOld nOld nNew sp m0 c.σ) ∧
        EnvDefineSavedSpillFrame sp saved c)
      (fun c => ∃ valsNew lds,
        SegPre appendHeadSeg (appendHeadL env valsNew) lds
          0x80002bc0#64 c.σ.mem c ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        EnvDefineSavedSpillFrame sp saved c ∧
        valsNew ≠ 0#64 ∧ A.contains valsNew.toNat nNew) := by
  intro c h
  have hr := h.1
  obtain ⟨pNew, hx10, hpNew, _halign, hpArena, _hdis, _hcopy, _hAInv, hframe⟩ :=
    reallocGrowSuccess_of_bounded RO g exts pOld nOld nNew sp 0x80002bc0#64 m0 c hle hr
  have hpublic := hgeom pNew
  have hloaded : Vsa.Sim.Code.Env_defineLoaded c.σ.mem := by
    apply loaded_envdef_of_agree m0 c.σ.mem _ hcode
    intro a ha0 ha1
    obtain ⟨hpriv, hstack, hext⟩ := hpublic.code a ha0 ha1
    exact hframe a hpriv hstack hext
  have hnamesRead' : read64 c.σ.mem (env.toNat + 8) = some names.toNat := by
    have hagree : AgreeP (fun a => env.toNat + 8 ≤ a ∧ a < env.toNat + 16)
        c.σ.mem m0 := by
      intro a ha
      have hk : a = env.toNat + 8 + (a - (env.toNat + 8)) := by omega
      have hklt : a - (env.toNat + 8) < 8 := by omega
      obtain ⟨hpriv, hstack, hext⟩ := hpublic.names _ hklt
      rw [← hk] at hpriv hstack hext
      exact hframe a hpriv hstack hext
    rw [read64_agreeP hagree (by intro k hk; omega)]
    exact hnamesRead
  let valsNew := BitVec.ofNat 64 pNew
  have hnNewPos : 0 < nNew := by omega
  have hpNewLt : pNew < 2^64 := by
    have := hpArena.2
    omega
  have hvalsNZ : valsNew ≠ 0#64 := by
    intro hz
    have := congrArg BitVec.toNat hz
    simp [valsNew, Nat.mod_eq_of_lt hpNewLt] at this
    exact hpNew this
  have hentryGeom : AppendHeadGeom env names valsNew c.σ.mem :=
    ⟨hnamesRead', hnamesNonzero, hvalsNZ, henvHi, hnamesLo, hnamesHi,
      hnamesHtif, hnamesAlign, hvalsLo, hvalsHi, hvalsHtif, hvalsAlign⟩
  obtain ⟨lds, hfacts⟩ := appendHeadFacts env names valsNew c.σ.mem hloaded hentryGeom
  have hx20 : c.σ.regs.get? Register.x20 = some env := by
    rw [hr.1.2.2.2.2.2 Register.x20 (by decide)]
    exact henvReg
  have hGH : GHolds c.σ (appendHeadL env valsNew) := by
    exact ⟨hx20, hx10, trivial⟩
  refine ⟨c, .refl c, valsNew, lds, ?_, hr.1.2.2.2.1, h.2, hvalsNZ, ?_⟩
  · exact ⟨hr.1.1, rfl, hr.1.2.2.1, hr.1.1.minstret, hGH,
      (by show KeysOK [20, 10]; decide), hfacts, hr.1.2.1⟩
  · simpa [valsNew, Nat.mod_eq_of_lt hpNewLt] using hpArena

/-- Successful grow rejoin parked at the ordinary append head, with the outer
saved spill image preserved. -/
structure EnvDefineGrowRejoinReady
    (saved : (R : Register) → Option (RegisterType R))
    (env valsNew sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Mem) (c : Config) : Prop where
  row : AppendHeadPost env valsNew lds m0 c
  spReg : c.σ.regs.get? Register.x2 = some sp
  savedSpills : EnvDefineSavedSpillFrame sp saved c
  tick : c.tick < 2

theorem envDefineGrowRejoin
    (saved : (R : Register) → Option (RegisterType R))
    (A : Arena) (env valsNew sp : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem)
    (henvHi : env.toNat + 24 ≤ 2^64)
    (henvA : A.contains (env.toNat + 16) 8)
    (harenaStack : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo) :
    Triple
      (fun c => SegPre appendHeadSeg (appendHeadL env valsNew) lds
          0x80002bc0#64 m0 c ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        EnvDefineSavedSpillFrame sp saved c)
      (EnvDefineGrowRejoinReady saved env valsNew sp lds m0) := by
  intro c ⟨hpre, hsp, hsaved⟩
  have hpublic := appendHeadPublicFrame A env valsNew sp lds m0 henvHi henvA
    harenaStack harenaCode
  obtain ⟨c', hs, hrow, hsp', htick⟩ :=
    appendHeadRowSp env valsNew sp lds m0 c ⟨hpre, hsp⟩
  have hsaved' : EnvDefineSavedSpillFrame sp saved c' := by
    apply hsaved.of_interval_agree
    · intro a ha0 ha1
      rw [hrow.2.1, hpre.2.1]
      exact hpublic.code a ha0 ha1
    · intro a ha0 ha1
      rw [hrow.2.1, hpre.2.1]
      exact hpublic.spills a ha0 ha1
  exact ⟨c', hs, hrow, hsp', hsaved', htick⟩

/-- The bounded second realloc and the four reflected rejoin instructions form
one closed grow suffix. No post-realloc entry `Triple` is supplied by callers. -/
theorem envDefineGrowRejoin_of_realloc
    {A : Arena} {SL : Vsa.Alloc.StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat}
    {AInv : Vsa.Machine.MState → List Extent → Prop}
    {privFoot : Nat → Prop}
    (RO : ReallocOps A SL gpv headroom maxReq AInv privFoot)
    (g saved : (R : Register) → Option (RegisterType R))
    (exts : List Extent) (pOld nOld nNew : Nat) (sp : BitVec 64)
    (env names : BitVec 64) (m0 : Mem)
    (hle : nNew ≤ maxReq) (hnGrow : nOld < nNew)
    (henvReg : g Register.x20 = some env)
    (hcode : Vsa.Sim.Code.Env_defineLoaded m0)
    (hnamesRead : read64 m0 (env.toNat + 8) = some names.toNat)
    (hnamesNonzero : names ≠ 0#64)
    (hgeom : ∀ pNew,
      AppendHeadReallocPublic privFoot SL sp pOld nOld pNew nNew env.toNat)
    (hArenaHi : A.hi ≤ 2^64)
    (henvHi : env.toNat + 24 ≤ 2^64)
    (hnamesLo : 0x80000000 ≤ env.toNat + 8)
    (hnamesHi : env.toNat + 16 ≤ 0x100000000)
    (hnamesHtif : env.toNat + 16 ≤ tohostAddr ∨
      tohostAddr + 8 ≤ env.toNat + 8)
    (hnamesAlign : (env.toNat + 8) % 8 = 0)
    (hvalsLo : 0x80000000 ≤ env.toNat + 16)
    (hvalsHi : env.toNat + 24 ≤ 0x100000000)
    (hvalsHtif : tohostAddr + 16 ≤ env.toNat + 16)
    (hvalsAlign : (env.toNat + 16) % 8 = 0)
    (henvA : A.contains (env.toNat + 16) 8)
    (harenaStack : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo) :
    Triple
      (fun c => (ReallocPost gpv sp 0x80002bc0#64 g c ∧
        ReallocGrowResult A SL privFoot AInv exts pOld nOld nNew sp m0 c.σ) ∧
        EnvDefineSavedSpillFrame sp saved c)
      (fun c => ∃ valsNew lds m,
        EnvDefineGrowRejoinReady saved env valsNew sp lds m c ∧
        valsNew ≠ 0#64 ∧ A.contains valsNew.toNat nNew) := by
  intro c h
  obtain ⟨c1, hs1, valsNew, lds, hpre, hsp, hsaved, hnz, hvalsA⟩ :=
    appendHeadSegPre_of_realloc RO g saved exts pOld nOld nNew sp env names m0
      hle hnGrow henvReg hcode hnamesRead hnamesNonzero hgeom hArenaHi henvHi
      hnamesLo hnamesHi hnamesHtif hnamesAlign hvalsLo hvalsHi hvalsHtif
      hvalsAlign c h
  obtain ⟨c2, hs2, hready⟩ :=
    envDefineGrowRejoin saved A env valsNew sp lds c1.σ.mem henvHi henvA
      harenaStack harenaCode c1 ⟨hpre, hsp, hsaved⟩
  exact ⟨c2, hs1.trans hs2, valsNew, lds, c1.σ.mem, hready, hnz, hvalsA⟩

/-- Static layout and arithmetic facts for the complete two-realloc grow lane. -/
structure EnvDefineGrowClosedGeom
    (A : Arena) (SL : Vsa.Alloc.StackLayout)
    (AInv : Vsa.Machine.MState → List Extent → Prop) (privFoot : Nat → Prop)
    (exts : List Extent) (pNamesOld nNamesOld nNamesNew : Nat)
    (pValsOld nValsOld nValsNew capw : Nat) (sp env : BitVec 64)
    (g gV : (R : Register) → Option (RegisterType R)) (m0 : Mem) : Prop where
  stack : Vsa.Alloc.StackOK SL sp 0
  envReg : g Register.x20 = some env
  code : Vsa.Sim.Code.Env_defineLoaded m0
  capRead : read32 m0 (env.toNat + 4) = some capw
  valsRead : read64 m0 (env.toNat + 16) = some pValsOld
  namesPublic : ∀ pNew,
    NamesReallocPublic privFoot SL sp pNamesOld nNamesOld pNew nNamesNew env.toNat
  arenaHi : A.hi ≤ 2^64
  capSmall : capw < 2^31
  valsSize : nValsNew = 24 * capw
  ghost : ∀ R, Vsa.Alloc.AbiPreserved R = true →
    R ≠ Register.x15 → R ≠ Register.x10 → R ≠ Register.x11 →
    R ≠ Register.x1 → gV R = g R
  envHi : env.toNat + 24 ≤ 2^64
  namesLo : 0x80000000 ≤ env.toNat + 8
  namesHi : env.toNat + 16 ≤ 0x100000000
  namesHtif : tohostAddr + 16 ≤ env.toNat + 8
  namesAlign : (env.toNat + 8) % 8 = 0
  capLo : 0x80000000 ≤ env.toNat + 4
  capHi : env.toNat + 8 ≤ 0x100000000
  capHtif : env.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ env.toNat + 4
  capAlign : (env.toNat + 4) % 4 = 0
  valsLo : 0x80000000 ≤ env.toNat + 16
  valsHi : env.toNat + 24 ≤ 0x100000000
  valsHtif : env.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 8 ≤ env.toNat + 16
  valsAlign : (env.toNat + 16) % 8 = 0
  namesCode : env.toNat + 16 ≤ 0x80002a5c ∨ 0x80002c10 ≤ env.toNat + 8
  namesSpill : env.toNat + 16 ≤ sp.toNat ∨ sp.toNat + 64 ≤ env.toNat + 8
  ainvNames : ∀ pNew (σa σb : Vsa.Machine.MState),
    σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
    (∀ a, (a < env.toNat + 8 ∨ env.toNat + 16 ≤ a) →
      σa.mem[a]? = σb.mem[a]?) →
    AInv σa ((pNew, nNamesNew) :: exts.erase (pNamesOld, nNamesOld)) →
    AInv σb ((pNew, nNamesNew) :: exts.erase (pNamesOld, nNamesOld))
  valsNonzero : pValsOld ≠ 0
  valsMember : ∀ pNew,
    (pValsOld, nValsOld) ∈ ((pNew, nNamesNew) :: exts.erase (pNamesOld, nNamesOld))
  valsArena : A.contains pValsOld nValsOld
  arenaSpill : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo
  arenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo
  privCode : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 → ¬ privFoot a
  privSpill : ∀ a, sp.toNat ≤ a → a < sp.toNat + 64 → ¬ privFoot a
  codeStack : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 →
    ¬ (SL.lo ≤ a ∧ a < sp.toNat)
  appendPublic : ∀ pNew,
    AppendHeadReallocPublic privFoot SL sp pValsOld nValsOld pNew nValsNew env.toNat
  envFieldArena : A.contains (env.toNat + 16) 8

/-- Complete grow lane from the first realloc return through the second
realloc and reflected append-head rejoin. -/
theorem envDefineGrowClosed
    {A : Arena} {SL : Vsa.Alloc.StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat}
    {AInv : Vsa.Machine.MState → List Extent → Prop}
    {privFoot : Nat → Prop}
    (RO : ReallocOps A SL gpv headroom maxReq AInv privFoot)
    (g gV saved : (R : Register) → Option (RegisterType R))
    (exts : List Extent) (pNamesOld nNamesOld nNamesNew : Nat)
    (pValsOld nValsOld nValsNew capw : Nat) (sp env : BitVec 64) (m0 : Mem)
    (hleNames : nNamesNew ≤ maxReq) (hltNames : nNamesOld < nNamesNew)
    (hleVals : nValsNew ≤ maxReq) (hltVals : nValsOld < nValsNew)
    (G : EnvDefineGrowClosedGeom A SL AInv privFoot exts pNamesOld
      nNamesOld nNamesNew pValsOld nValsOld nValsNew capw sp env g gV m0)
    (hstack : Vsa.Alloc.StackOK SL sp headroom) :
    Triple
      (fun c => (ReallocPost gpv sp 0x80002ba4#64 g c ∧
        ReallocGrowResult A SL privFoot AInv exts pNamesOld nNamesOld
          nNamesNew sp m0 c.σ) ∧ EnvDefineSavedSpillFrame sp saved c)
      (fun c => ∃ valsNew lds m,
        EnvDefineGrowRejoinReady saved env valsNew sp lds m c ∧
        valsNew ≠ 0#64 ∧ A.contains valsNew.toNat nValsNew) := by
  intro c h
  obtain ⟨c1, hs1, pNamesNew, hentry, hpNames, hpNamesArena⟩ :=
    growEnvEntry_of_realloc RO g saved exts pNamesOld nNamesOld nNamesNew
      pValsOld capw sp env m0 hleNames hltNames hstack G.envReg G.code
      G.capRead G.valsRead G.namesPublic G.arenaHi c h
  let extsV := (pNamesNew, nNamesNew) :: exts.erase (pNamesOld, nNamesOld)
  let pNamesBV := BitVec.ofNat 64 pNamesNew
  obtain ⟨c2, hs2, hpreVals, hsaved2⟩ :=
    namesToVals_of_growEntry SL gpv headroom extsV sp g gV saved env pNamesBV
      pValsOld nValsNew capw c1.σ.mem G.capSmall G.valsSize G.ghost G.envHi
      G.namesLo G.namesHi G.namesHtif G.namesAlign G.capLo G.capHi G.capHtif
      G.capAlign G.valsLo G.valsHi G.valsHtif G.valsAlign G.namesCode
      G.namesSpill (G.ainvNames pNamesNew) c1 hentry
  have hpNamesLt : pNamesNew < 2^64 := by
    have hn : 0 < nNamesNew := by omega
    have := hpNamesArena.2
    have := G.arenaHi
    omega
  let mVals := writeMap8 c1.σ.mem (env.toNat + 8) (sdData_val pNamesBV)
  have hcodeV : Vsa.Sim.Code.Env_defineLoaded mVals := by
    exact loaded_envdef_writeMap8 c1.σ.mem (env.toNat + 8)
      (sdData_val pNamesBV) G.namesCode hentry.1.loadedD
  have hnamesReadV : read64 mVals (env.toNat + 8) = some pNamesBV.toNat := by
    rw [read64_writeMap8, sdData_toNat]
  have hnamesNZ : pNamesBV ≠ 0#64 := by
    intro hz
    have hz' := congrArg BitVec.toNat hz
    simp [pNamesBV, Nat.mod_eq_of_lt hpNamesLt] at hz'
    exact hpNames hz'
  have hgVenv : gV Register.x20 = some env := by
    rw [G.ghost Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact G.envReg
  obtain ⟨c3, hs3, hpostVals, hsaved3⟩ :=
    reallocGrowSaved RO gV saved extsV pValsOld nValsOld nValsNew sp
      0x80002bc0#64 mVals hleVals hltVals G.valsNonzero
      (G.valsMember pNamesNew) G.valsArena G.arenaSpill G.arenaCode
      G.privCode G.privSpill G.codeStack c2 ⟨hpreVals, hsaved2⟩
  obtain ⟨c4, hs4, valsNew, lds, m, hready, hnz, hvalsArena⟩ :=
    envDefineGrowRejoin_of_realloc RO gV saved extsV pValsOld nValsOld
      nValsNew sp env pNamesBV mVals hleVals hltVals hgVenv hcodeV
      hnamesReadV hnamesNZ G.appendPublic G.arenaHi G.envHi G.namesLo
      G.namesHi (Or.inr (by have := G.namesHtif; omega)) G.namesAlign
      G.valsLo G.valsHi (by have := G.namesHtif; omega) G.valsAlign
      G.envFieldArena G.arenaSpill G.arenaCode
      c3 ⟨hpostVals, hsaved3⟩
  exact ⟨c4, hs1.trans (hs2.trans (hs3.trans hs4)), valsNew, lds, m,
    hready, hnz, hvalsArena⟩

#print axioms appendHeadRowSp
#print axioms appendHeadLogExact
#print axioms appendHeadMemoryExact
#print axioms appendHeadFacts
#print axioms reallocGrowSuccess_of_bounded
#print axioms growEnvEntry_of_realloc
#print axioms namesToValsPointerTie
#print axioms namesToValsSizeTie
#print axioms namesToVals_of_growEntry
#print axioms appendHeadSegPre_of_realloc
#print axioms envDefineGrowRejoin
#print axioms envDefineGrowRejoin_of_realloc
#print axioms envDefineGrowClosed

end Vsa.Sim
