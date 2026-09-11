import Vsa.Sim.rows.EnvDefineDispatchExact
import Vsa.Sim.rows.EnvDefineAppendPrefix
import Vsa.Sim.EnvDefCompose
import Vsa.Sim.EnvDefComposeFacts
import Vsa.Sim.ValueWordRepr
import Vsa.Sim.StrcpySpec
import Vsa.Sim.rows.StrcpyContractInhab
import Vsa.Sim.AllocSuccessAdapters

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)
open Vsa.Alloc
open Vsa.MemRepr
open Vsa.RuntimeRepr

namespace Vsa.Sim

/-- The concrete strlen-entry prefix preserves the independent outer spill
snapshot because it does not write memory. -/
theorem bridgeStrlenPreSaved_closed
    (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List Extent → Prop) (exts : List Extent)
    (sp : BitVec 64)
    (gm saved : (R : Register) → Option (RegisterType R))
    (namePtr : BitVec 64) (nameStr : String) (m0 : Mem)
    (hAInvStable : ∀ (σa σb : MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a : Nat, σa.mem[a]? = σb.mem[a]?) →
      AInv σa exts → AInv σb exts) :
    Triple
      (fun c => AppendStrlenEntry SL gpv headroom AInv exts sp gm
          namePtr nameStr m0 c ∧ EnvDefineSavedSpillFrame sp saved c)
      (fun c => strlen_pre namePtr 0x80002b24#64 nameStr m0 c ∧
        EnvDefFrameSaved SL gpv headroom AInv exts sp gm saved c) := by
  intro c ⟨hentry, hsaved⟩
  obtain ⟨c', hs, hpre, hframe⟩ :=
    bridgeStrlenPre_closed SL gpv headroom AInv exts sp gm namePtr nameStr m0
      hAInvStable c hentry
  have hsaved' : EnvDefineSavedSpillFrame sp saved c' := by
    apply hsaved.of_mem_eq
    exact hpre.2.2.1.trans hentry.2.2.2.1.symm
  exact ⟨c', hs, hpre, hframe, hsaved'⟩

/-- The strlen-to-malloc staging prefix likewise preserves the independent
saved spill snapshot. -/
theorem bridgeMallocPreSaved_closed
    {A : Vsa.RuntimeRepr.Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (sp : BitVec 64)
    (gm g' saved : (R : Register) → Option (RegisterType R))
    (nameStr : String) (m0 : Mem)
    (hg'x8 : g' Register.x8 = some (BitVec.ofNat 64 (nameStr.length + 1)))
    (hg'other : ∀ R, AbiPreserved R = true → R ≠ Register.x8 → g' R = gm R)
    (hAInvStable : ∀ (σa σb : MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a : Nat, σa.mem[a]? = σb.mem[a]?) →
      M.AInv σa exts → M.AInv σb exts)
    (hloaded : ∀ mem : Mem, Vsa.Sim.Code.StrlenLoaded mem →
      Vsa.Sim.Code.Env_defineLoaded mem)
    (hstrlenLoaded : Vsa.Sim.Code.StrlenLoaded m0) :
    Triple
      (fun c => strlen_post 0x80002b24#64 nameStr m0 c ∧
        EnvDefFrameSaved SL gpv headroom M.AInv exts sp gm saved c)
      (fun c => EnvDefMallocPre M g' exts (nameStr.length + 1)
          sp 0x80002b30#64 m0 c ∧
        EnvDefineSavedSpillFrame sp saved c) := by
  intro c ⟨hpost, hframe, hsaved⟩
  obtain ⟨c', hs, hpre⟩ :=
    bridgeMallocPre_closed SL gpv headroom M.AInv exts sp gm g' nameStr m0
      hg'x8 hg'other hAInvStable hloaded hstrlenLoaded c ⟨hpost, hframe⟩
  rcases hpre with ⟨hG, htick, hpc, hx10, hra, hralign, hsp, hstack,
    hgp, habi, hainv, hmem⟩
  have hsaved' : EnvDefineSavedSpillFrame sp saved c' := by
    apply hsaved.of_mem_eq
    exact hmem.trans hpost.mem_eq.symm
  exact ⟨c', hs,
    ⟨hG, htick, hpc, hx10, hra, hralign, hsp, hstack, hgp, habi, hainv, hmem⟩,
    hsaved'⟩

/-- The allocator's public-memory contract transports the outer saved spill
image through the concrete malloc call. -/
theorem envDefMallocSaved
    {A : Vsa.RuntimeRepr.Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (g saved : (R : Register) → Option (RegisterType R))
    (exts : List Extent) (n : Nat) (sp r : BitVec 64) (m0 : Mem)
    (hn : n ≤ maxReq)
    (hPrivCode : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 → ¬ M.privFoot a)
    (hPrivSpill : ∀ a, sp.toNat ≤ a → a < sp.toNat + 64 → ¬ M.privFoot a)
    (hCodeStack : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 →
      ¬ (SL.lo ≤ a ∧ a < sp.toNat)) :
    Triple
      (fun c => EnvDefMallocPre M g exts n sp r m0 c ∧
        EnvDefineSavedSpillFrame sp saved c)
      (fun c => EnvDefMallocPost M g exts n sp r m0 c ∧
        EnvDefineSavedSpillFrame sp saved c) := by
  intro c ⟨hpre, hsaved⟩
  obtain ⟨c', hs, hpost⟩ := M.spec g exts n sp r m0 hn c hpre
  have hmem0 : c.σ.mem = m0 := hpre.mem_eq
  rcases hpost with ⟨hgood, htick, hpc, hsp, hgp, habi, hresult, hpublic⟩
  have hsaved' : EnvDefineSavedSpillFrame sp saved c' := by
    apply hsaved.of_interval_agree
    · intro a ha0 ha1
      exact (hpublic a (hPrivCode a ha0 ha1) (hCodeStack a ha0 ha1)).trans
        (congrArg (fun m => m[a]?) hmem0.symm)
    · intro a ha0 ha1
      exact (hpublic a (hPrivSpill a ha0 ha1) (by omega)).trans
        (congrArg (fun m => m[a]?) hmem0.symm)
  exact ⟨c', hs,
    ⟨hgood, htick, hpc, hsp, hgp, habi, hresult, hpublic⟩, hsaved'⟩

/-- The successful allocator result, public-memory frame, and saved spill image.
The failure-aware `envDefMallocSaved` does not supply success by itself. -/
def EnvDefMallocSuccessSaved
    {A : Vsa.RuntimeRepr.Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (g saved : (R : Register) → Option (RegisterType R))
    (exts : List Extent) (n : Nat) (sp r : BitVec 64) (m0 : Mem)
    (c : Config) : Prop :=
  ∃ ptr : Nat,
    GoodState c.σ ∧ c.tick < 2 ∧
    c.σ.regs.get? Register.PC = some r ∧
    c.σ.regs.get? Register.x2 = some sp ∧
    StackOK SL sp headroom ∧
    c.σ.regs.get? Register.x3 = some gpv ∧
    (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
    c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 ptr) ∧
    ptr ≠ 0 ∧ ptr % 16 = 0 ∧ A.contains ptr n ∧
    (∀ e ∈ exts, ExtDisjoint (ptr, n) e) ∧
    M.AInv c.σ ((ptr, n) :: exts) ∧
    (∀ a, ¬ M.privFoot a → ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
      c.σ.mem[a]? = m0[a]?) ∧
    EnvDefineSavedSpillFrame sp saved c

theorem envDefMallocSuccessSaved_of_post
    {A : Vsa.RuntimeRepr.Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (g saved : (R : Register) → Option (RegisterType R))
    (exts : List Extent) (n : Nat) (sp r : BitVec 64) (m0 : Mem)
    {credits : Nat} {out : Array String} (hstack : StackOK SL sp headroom) :
    Triple
      (fun c => MallocSuccessExit A SL gpv maxReq credits M.AInv M.privFoot
          g exts n sp r m0 out c ∧
        EnvDefineSavedSpillFrame sp saved c)
      (EnvDefMallocSuccessSaved M g saved exts n sp r m0) := by
  intro c ⟨hpost, hsaved⟩
  obtain ⟨p, hp⟩ := hpost.allocated
  exact ⟨c, Vsa.Machine.Steps.refl c,
    p, hpost.returned.good, hpost.returned.tick, hpost.returned.pc,
    hpost.returned.sp, hstack, hpost.returned.gp, hpost.returned.frame,
    hp.pointer.register, hp.pointer.nonzero, hp.pointer.aligned,
    hp.pointer.arena, hp.disjoint, hp.ainv,
    (fun a hpriv hstack => hp.mem_frame a hpriv hstack (by simp)), hsaved⟩

/-- The b30..b40 staging deliberately reseats s1/x9 to the fresh copy
destination. -/
def envDefineMemcpyGhost
    (g : (R : Register) → Option (RegisterType R)) (copy : BitVec 64) :
    (R : Register) → Option (RegisterType R) :=
  fun R => if h : R = Register.x9 then some (h ▸ copy) else g R

@[simp] theorem envDefineMemcpyGhost_x9
    (g : (R : Register) → Option (RegisterType R)) (copy : BitVec 64) :
    envDefineMemcpyGhost g copy Register.x9 = some copy := by
  simp [envDefineMemcpyGhost]

theorem envDefineMemcpyGhost_ne
    (g : (R : Register) → Option (RegisterType R)) (copy : BitVec 64)
    {R : Register} (h : R ≠ Register.x9) :
    envDefineMemcpyGhost g copy R = g R := by
  simp [envDefineMemcpyGhost, h]

/-- Semantic content needed by memcpy at the state produced by the exact
b30..b40 machine run. -/
structure EnvDefineMemcpyContent
    {A : Vsa.RuntimeRepr.Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (exts : List Extent) (p n : Nat) (sp name : BitVec 64)
    (bs : Nat → BitVec 8) (σ : MState) : Prop where
  loaded : Vsa.Sim.Code.MemcpyLoaded σ.mem
  regions : Regions (BitVec.ofNat 64 p) name n
  npos : 0 < n
  meminv : MemInv (BitVec.ofNat 64 p) name n bs 0 σ.mem σ.mem

/-- The fixed heap placement facts needed at the env_define memcpy boundary. -/
structure EnvDefineMemcpyArenaGeom (A : Vsa.RuntimeRepr.Arena) : Prop where
  ramLo : 0x80000000 ≤ A.lo
  ramHi : A.hi ≤ 0x100000000
  htif : tohostAddr + 16 ≤ A.lo
  code : A.hi ≤ 0x80006bc8 ∨ 0x80006cf0 ≤ A.lo

/-- `MemcpyLoaded` transfers through agreement on the exact helper image. -/
theorem memcpyLoaded_of_agree (m m' : Mem)
    (hagree : ∀ a, 0x80006bc8 ≤ a → a < 0x80006cf0 → m'[a]? = m[a]?)
    (h : Vsa.Sim.Code.MemcpyLoaded m) : Vsa.Sim.Code.MemcpyLoaded m' := by
  obtain ⟨c0, c1, c2, c3, c4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Vsa.Sim.Code.memcpyChunk0] at c0 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.memcpyChunk1] at c1 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.memcpyChunk2] at c2 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.memcpyChunk3] at c3 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.memcpyChunk4] at c4 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])

/-- The memcpy boundary facts are consequences of the allocator ledger,
the represented source string, and fixed image geometry. -/
theorem envDefineMemcpyContent_of_public
    {A : Vsa.RuntimeRepr.Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (exts : List Extent) (p n len : Nat) (sp name : BitVec 64)
    (bs : Nat → BitVec 8) (m0 : Mem) (σ : MState)
    (hn : n = len + 1) (hstr : StrBytes m0 name len bs)
    (hname : (name.toNat, n) ∈ exts)
    (harena : HeapArena A exts) (hgeom : EnvDefineMemcpyArenaGeom A)
    (hstack : StackOK SL sp headroom)
    (harenaStack : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo)
    (hloaded : Vsa.Sim.Code.MemcpyLoaded m0)
    (hPrivCode : ∀ a, 0x80006bc8 ≤ a → a < 0x80006cf0 →
      ¬ M.privFoot a)
    (hCodeStack : ∀ a, 0x80006bc8 ≤ a → a < 0x80006cf0 →
      ¬ (SL.lo ≤ a ∧ a < sp.toNat))
    (hpArena : A.contains p n)
    (hpFresh : ∀ e ∈ exts, ExtDisjoint (p, n) e)
    (hainv : M.AInv σ ((p, n) :: exts))
    (hpublic : ∀ a, ¬ M.privFoot a →
      ¬ (SL.lo ≤ a ∧ a < sp.toNat) → σ.mem[a]? = m0[a]?) :
    EnvDefineMemcpyContent M exts p n sp name bs σ := by
  have hnpos : 0 < n := by omega
  obtain ⟨hpLo, hpHi⟩ := hpArena
  obtain ⟨_hNamePos, hNameArena⟩ := harena.1 _ hname
  obtain ⟨hsLo, hsHi⟩ := hNameArena
  have hpLt : p < 2^64 := by
    have := hgeom.ramHi
    omega
  have hpNat : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpLt]
  have hsourceStack : ∀ k, k < n →
      ¬ (SL.lo ≤ name.toNat + k ∧ name.toNat + k < sp.toNat) := by
    intro k hk hs
    rcases harenaStack with hbefore | hafter
    · omega
    · have hspHi := hstack.2.1
      omega
  have hsourcePriv : ∀ k, k < n → ¬ M.privFoot (name.toNat + k) := by
    intro k hk
    exact M.privFoot_disjoint σ ((p, n) :: exts) hainv
      (name.toNat, n) (by simp [hname]) k hk
  have hsource : ∀ k, k < n → σ.mem[name.toNat + k]? = some (bs k) := by
    intro k hk
    rw [hpublic _ (hsourcePriv k hk) (hsourceStack k hk)]
    by_cases hkl : k < len
    · exact (hstr.chars k hkl).1
    · have hkeq : k = len := by omega
      subst k
      exact hstr.nul
  refine ⟨?_, ?_, hnpos, ?_⟩
  · apply memcpyLoaded_of_agree m0 σ.mem
    · intro a ha0 ha1
      exact hpublic a (hPrivCode a ha0 ha1) (hCodeStack a ha0 ha1)
    · exact hloaded
  · refine {
      dst_nowrap := ?_, src_nowrap := ?_, disjoint := ?_,
      code_disjoint := ?_, dst_lo := ?_, dst_hi := ?_,
      src_lo := ?_, src_hi := ?_, dst_win := ?_, src_win := ?_ }
    · simp only [hpNat]
      have := hgeom.ramHi; omega
    · have := hgeom.ramHi; omega
    · simpa only [hpNat] using hpFresh (name.toNat, n) hname
    · rcases hgeom.code with hbefore | hafter
      · left; simpa only [hpNat] using (show p + n ≤ 0x80006bc8 by omega)
      · right; simpa only [hpNat] using (show 0x80006cf0 ≤ p by omega)
    · rw [hpNat]
      exact Nat.le_trans hgeom.ramLo hpLo
    · rw [hpNat]
      exact Nat.le_trans hpHi hgeom.ramHi
    · calc
        0x80000000 ≤ A.lo := hgeom.ramLo
        _ ≤ name.toNat := hsLo
    · calc
        name.toNat + n ≤ A.hi := hsHi
        _ ≤ 0x100000000 := hgeom.ramHi
    · rw [hpNat]
      exact Nat.le_trans hgeom.htif hpLo
    · calc
        tohostAddr + 16 ≤ A.lo := hgeom.htif
        _ ≤ name.toNat := hsLo
  · refine ⟨?_, ?_, ?_⟩
    · intro k hk
      omega
    · intro a ha
      rfl
    · intro k _hk0 hk
      exact hsource k hk
private theorem envDefineMemcpyB30Line :
    mkLine 0x80002b30#64 0x00050493#32 =
      ⟨0x80002b30#64, 0x00050493#32, 0x93#8, 0x04#8, 0x05#8, 0x00#8,
        .addi, 9, 10, 0, 0x000#12⟩ := by rfl

private theorem envDefineMemcpyB38Line :
    mkLine 0x80002b38#64 0x00040613#32 =
      ⟨0x80002b38#64, 0x00040613#32, 0x13#8, 0x06#8, 0x04#8, 0x00#8,
        .addi, 12, 8, 0, 0x000#12⟩ := by rfl

private theorem envDefineMemcpyB3cLine :
    mkLine 0x80002b3c#64 0x00090593#32 =
      ⟨0x80002b3c#64, 0x00090593#32, 0x93#8, 0x05#8, 0x09#8, 0x00#8,
        .addi, 11, 18, 0, 0x000#12⟩ := by rfl

/-- Exact malloc-success to memcpy-entry bridge.  All machine transitions are
the reflected b30..b40 rows; `content` contains only the memcpy callee's memory
and region preconditions. -/
theorem envDefineMallocToMemcpy
    {A : Vsa.RuntimeRepr.Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (g saved : (R : Register) → Option (RegisterType R))
    (exts : List Extent) (n : Nat) (sp env name src : BitVec 64)
    (m0 : Mem)
    (bs : Nat → BitVec 8)
    (hg8 : g Register.x8 = some (BitVec.ofNat 64 n))
    (hg18 : g Register.x18 = some name)
    (hg20 : g Register.x20 = some env)
    (hg21 : g Register.x21 = some src)
    (hnpos : 0 < n)
    (hArenaHi : A.hi ≤ 2^64)
    (hAInvStable : ∀ (p : Nat) (sigmaa sigmab : MState),
      sigmaa.regs.get? Register.x3 = sigmab.regs.get? Register.x3 →
      (∀ a : Nat, sigmaa.mem[a]? = sigmab.mem[a]?) →
      M.AInv sigmaa ((p, n) :: exts) → M.AInv sigmab ((p, n) :: exts))
    (hEnvLoaded : ∀ c, EnvDefMallocSuccessSaved M g saved exts n sp
      0x80002b30#64 m0 c → Vsa.Sim.Code.Env_defineLoaded c.σ.mem)
    (content : ∀ (p : Nat) (σ2 : MState),
      A.contains p n →
      (∀ e ∈ exts, ExtDisjoint (p, n) e) →
      M.AInv σ2 ((p, n) :: exts) →
      (∀ a, ¬ M.privFoot a → ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
        σ2.mem[a]? = m0[a]?) →
      σ2.regs.get? Register.PC = some 0x80006bc8#64 →
      σ2.regs.get? Register.x10 = some (BitVec.ofNat 64 p) →
      σ2.regs.get? Register.x11 = some name →
      σ2.regs.get? Register.x12 = some (BitVec.ofNat 64 n) →
      EnvDefineMemcpyContent M exts p n sp name bs σ2) :
    Triple
      (EnvDefMallocSuccessSaved M g saved exts n sp 0x80002b30#64 m0)
      (fun c => ∃ p g0,
        PreDispatch g0 0x80002b44#64
          (BitVec.ofNat 64 p) name n c.σ.mem bs c ∧
        EnvDefFrameSaved SL gpv headroom M.AInv ((p, n) :: exts) sp
          g0 saved c ∧
        g0 Register.x20 = some env ∧ g0 Register.x21 = some src ∧
        g0 Register.x9 = some (BitVec.ofNat 64 p) ∧
        A.contains p n ∧ (∀ e ∈ exts, ExtDisjoint (p, n) e)) := by
  intro c h
  have hloaded := hEnvLoaded c h
  obtain ⟨p, hG, htick, hpc, hsp, hstack, hgp, habi, ha0, hp, _halign,
    harena, hfresh, hainv, hpublic, hsaved⟩ := h
  have hpLt : p < 2^64 := by
    change A.lo ≤ p ∧ p + n ≤ A.hi at harena
    omega
  have hcopy : BitVec.ofNat 64 p ≠ 0#64 := by
    intro hz
    have := congrArg BitVec.toNat hz
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpLt] at this
    exact hp this
  have hx8 : c.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 n) := by
    rw [habi Register.x8 (by decide), hg8]
  have hx18 : c.σ.regs.get? Register.x18 = some name := by
    rw [habi Register.x18 (by decide), hg18]
  have hL : GHolds c.σ
      (envDefineMemcpyArgL (BitVec.ofNat 64 p) (BitVec.ofNat 64 n) name) :=
    ⟨ha0, hx8, hx18, trivial⟩
  have hfacts : ChainFacts c.σ.mem c.σ.mem
      (envDefineMemcpyArgL (BitVec.ofNat 64 p) (BitVec.ofNat 64 n) name) []
      envDefineMemcpyArgSeg := by
    chain_facts hloaded with "Vsa.Sim.Code.env_define_at_"
    · change guardB bop.BEQ (BitVec.ofNat 64 p) 0#64 = false
      simp [guardB, hcopy]
  obtain ⟨vmi, hmi⟩ := hG.minstret
  obtain ⟨σ2, i2, hs, hi2, hG2, hpc2, hra2, hmi2, hregs2, hmem2, habi2⟩ :=
    envDefineMemcpyCallRun c.σ c.tick c.steps vmi (BitVec.ofNat 64 p)
      (BitVec.ofNat 64 n) name c.σ.mem hG hpc hmi rfl hL hfacts hloaded htick
  have hzero : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by decide
  have hx10L : lookupG 10 (evalBlocks envDefineMemcpyArgSeg
      (SegEvalState.init
        (envDefineMemcpyArgL (BitVec.ofNat 64 p) (BitVec.ofNat 64 n) name) [])).regs
      = some (BitVec.ofNat 64 p) := by
    simp [envDefineMemcpyArgSeg, evalBlocks, evalBlock, SegEvalState.init,
      envDefineMemcpyB30Line, envDefineMemcpyB38Line,
      envDefineMemcpyB3cLine, runGM, stepGM, envDefineMemcpyArgL, srcVal,
      stepLdsM, ldsRunM, wvalM, List.headD, List.tail, lookupG, eraseG,
      hzero]
  have hx10 : σ2.regs.get? Register.x10 = some (BitVec.ofNat 64 p) := by
    simpa [gprGet] using gholds_lookup _ hregs2 hx10L
  have hx11 : σ2.regs.get? Register.x11 = some name := by
    simpa [gprGet] using gholds_lookup _ hregs2 (by
      simp [envDefineMemcpyArgSeg, evalBlocks, evalBlock, SegEvalState.init,
        envDefineMemcpyB30Line, envDefineMemcpyB38Line,
        envDefineMemcpyB3cLine, runGM, stepGM, envDefineMemcpyArgL, srcVal,
        stepLdsM, ldsRunM, wvalM, List.headD, List.tail, lookupG, eraseG,
        hzero] :
        lookupG 11 (evalBlocks envDefineMemcpyArgSeg
          (SegEvalState.init (envDefineMemcpyArgL (BitVec.ofNat 64 p)
            (BitVec.ofNat 64 n) name) [])).regs = some name)
  have hx12 : σ2.regs.get? Register.x12 = some (BitVec.ofNat 64 n) := by
    simpa [gprGet] using gholds_lookup _ hregs2 (by
      simp [envDefineMemcpyArgSeg, evalBlocks, evalBlock, SegEvalState.init,
        envDefineMemcpyB30Line, envDefineMemcpyB38Line,
        envDefineMemcpyB3cLine, runGM, stepGM, envDefineMemcpyArgL, srcVal,
        stepLdsM, ldsRunM, wvalM, List.headD, List.tail, lookupG, eraseG,
        hzero] :
        lookupG 12 (evalBlocks envDefineMemcpyArgSeg
          (SegEvalState.init (envDefineMemcpyArgL (BitVec.ofNat 64 p)
            (BitVec.ofNat 64 n) name) [])).regs = some (BitVec.ofNat 64 n))
  have hpublic2 : ∀ a, ¬ M.privFoot a →
      ¬ (SL.lo ≤ a ∧ a < sp.toNat) → σ2.mem[a]? = m0[a]? := by
    intro a haPriv haStack
    rw [hmem2]
    exact hpublic a haPriv haStack
  have hainv2 : M.AInv σ2 ((p, n) :: exts) := by
    apply hAInvStable p c.σ σ2
    · rw [habi2 Register.x3 (by decide)]
    · intro a
      exact congrArg (fun m => m[a]?) hmem2.symm
    · exact hainv
  have hct := content p σ2 harena hfresh hainv2 hpublic2 hpc2 hx10 hx11 hx12
  obtain ⟨hMemcpyLoaded, hregions, hnpos', hmeminv⟩ := hct
  let c2 : Config := ⟨σ2, i2, c.steps + evalBlocksFuel envDefineMemcpyArgSeg + 1⟩
  let g0 : (R : Register) → Option (RegisterType R) := fun R => σ2.regs.get? R
  have hsaved2 : EnvDefineSavedSpillFrame sp saved c2 := by
    apply hsaved.of_mem_eq
    exact hmem2
  have hspill2 : EnvDefineSpillFrame sp g0 c2 := by
    obtain ⟨lds, himage, _hvalues⟩ := hsaved2
    exact ⟨lds, himage⟩
  have hx20 : σ2.regs.get? Register.x20 = some env := by
    rw [habi2 Register.x20 (by decide), habi Register.x20 (by decide), hg20]
  have hx21 : σ2.regs.get? Register.x21 = some src := by
    rw [habi2 Register.x21 (by decide), habi Register.x21 (by decide), hg21]
  have hx9 : σ2.regs.get? Register.x9 = some (BitVec.ofNat 64 p) := by
    simpa [gprGet] using gholds_lookup _ hregs2 (by
      simp [envDefineMemcpyArgSeg, evalBlocks, evalBlock, SegEvalState.init,
        envDefineMemcpyB30Line, envDefineMemcpyB38Line, envDefineMemcpyB3cLine,
        runGM, stepGM, envDefineMemcpyArgL, srcVal, stepLdsM, ldsRunM, wvalM,
        lookupG, eraseG, hzero] : lookupG 9 (evalBlocks envDefineMemcpyArgSeg
          (SegEvalState.init (envDefineMemcpyArgL (BitVec.ofNat 64 p)
            (BitVec.ofNat 64 n) name) [])).regs = some (BitVec.ofNat 64 p))
  refine ⟨c2, hs, p, g0, ?_, ?_, ?_, ?_, ?_, harena, hfresh⟩
  · exact ⟨hG2, hMemcpyLoaded, hpc2, hx10, hx11, hx12, hra2, hmi2,
      hi2, hregions, hnpos', hmeminv, fun R _ => rfl⟩
  · have hsp2 : σ2.regs.get? Register.x2 = some sp := by
      rw [habi2 Register.x2 (by decide), hsp]
    have hgp2 : σ2.regs.get? Register.x3 = some gpv := by
      rw [habi2 Register.x3 (by decide), hgp]
    change EnvDefFrame SL gpv headroom M.AInv ((p, n) :: exts) sp
        g0 c2 ∧ EnvDefineSavedSpillFrame sp saved c2
    refine ⟨?_, hsaved2⟩
    exact ⟨by simpa [c2] using hsp2, hstack, by simpa [c2] using hgp2,
      (fun _ _ => rfl), by simpa [c2] using hainv2, hi2, hspill2⟩
  · simpa [g0] using hx20
  · simpa [g0] using hx21
  · simpa [g0] using hx9

/-- Closed malloc-to-memcpy entry.  The former content callback is instantiated
from the represented CString, allocator public frame, and fixed geometry. -/
theorem envDefineMallocToMemcpy_closed
    {A : Vsa.RuntimeRepr.Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (g saved : (R : Register) → Option (RegisterType R))
    (exts : List Extent) (n len : Nat) (sp env name src : BitVec 64)
    (m0 : Mem) (nameStr : String) (bs : Nat → BitVec 8)
    (hg8 : g Register.x8 = some (BitVec.ofNat 64 n))
    (hg18 : g Register.x18 = some name)
    (hg20 : g Register.x20 = some env)
    (hg21 : g Register.x21 = some src)
    (hn : n = len + 1) (hlen : len = nameStr.length)
    (hstr : StrBytes m0 name len bs)
    (hcstr : CString m0 name.toNat nameStr)
    (hname : (name.toNat, n) ∈ exts)
    (harena : HeapArena A exts) (hgeom : EnvDefineMemcpyArenaGeom A)
    (hstack : StackOK SL sp headroom)
    (harenaStack : A.hi ≤ SL.lo ∨ SL.hi ≤ A.lo)
    (hEnvLoaded : Vsa.Sim.Code.Env_defineLoaded m0)
    (hMemcpyLoaded : Vsa.Sim.Code.MemcpyLoaded m0)
    (hPrivEnv : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 →
      ¬ M.privFoot a)
    (hEnvStack : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 →
      ¬ (SL.lo ≤ a ∧ a < sp.toNat))
    (hPrivMemcpy : ∀ a, 0x80006bc8 ≤ a → a < 0x80006cf0 →
      ¬ M.privFoot a)
    (hMemcpyStack : ∀ a, 0x80006bc8 ≤ a → a < 0x80006cf0 →
      ¬ (SL.lo ≤ a ∧ a < sp.toNat))
    (hAInvStable : ∀ (p : Nat) (sigmaa sigmab : MState),
      sigmaa.regs.get? Register.x3 = sigmab.regs.get? Register.x3 →
      (∀ a : Nat, sigmaa.mem[a]? = sigmab.mem[a]?) →
      M.AInv sigmaa ((p, n) :: exts) → M.AInv sigmab ((p, n) :: exts)) :
    Triple
      (EnvDefMallocSuccessSaved M g saved exts n sp 0x80002b30#64 m0)
      (fun c => ∃ p g0,
        PreDispatch g0 0x80002b44#64
          (BitVec.ofNat 64 p) name n c.σ.mem bs c ∧
        EnvDefFrameSaved SL gpv headroom M.AInv ((p, n) :: exts) sp
          g0 saved c ∧
        g0 Register.x20 = some env ∧ g0 Register.x21 = some src ∧
        g0 Register.x9 = some (BitVec.ofNat 64 p) ∧
        A.contains p n ∧ (∀ e ∈ exts, ExtDisjoint (p, n) e) ∧
        StrBytes c.σ.mem name len bs ∧ CString c.σ.mem name.toNat nameStr) := by
  have hbase := envDefineMallocToMemcpy M g saved exts n sp env name src m0 bs
      hg8 hg18 hg20 hg21 (by omega) (by have := hgeom.ramHi; omega)
      hAInvStable
      (by
        intro c h
        obtain ⟨p, _hG, _htick, _hpc, _hsp, _hstack, _hgp, _habi, _ha0,
          _hp, _halign, _harena, _hfresh, _hainv, hpublic, _hsaved⟩ := h
        apply envDefineLoaded_of_agree m0 c.σ.mem
        · intro a ha0 ha1
          exact hpublic a (hPrivEnv a ha0 ha1) (hEnvStack a ha0 ha1)
        · exact hEnvLoaded)
      (by
        intro p σ hpArena hpFresh hainv hpublic _hpc _ha0 _ha1 _ha2
        exact envDefineMemcpyContent_of_public M exts p n len sp name bs m0 σ
          hn hstr hname harena hgeom hstack harenaStack hMemcpyLoaded
          hPrivMemcpy hMemcpyStack hpArena hpFresh hainv hpublic)
  refine hbase.conseq (fun _ h => h) ?_
  intro c h
  obtain ⟨p, g0, hpre, hframe, hx20, hx21, hx9, hpArena, hfresh⟩ := h
  have hstr' : StrBytes c.σ.mem name len bs := by
    refine ⟨?_, ?_, hstr.bs_nul⟩
    · intro k hk
      exact ⟨hpre.meminv.src_intact k (by omega) (by omega),
        (hstr.chars k hk).2⟩
    · exact hpre.meminv.src_intact len (by omega) (by omega)
  have hcstr' : CString c.σ.mem name.toNat nameStr := by
    apply cstring_shift_copy hcstr
    intro k hk
    rw [hpre.meminv.src_intact k (by omega) (by omega)]
    by_cases hkl : k < len
    · exact (hstr.chars k hkl).1.symm
    · have hkeq : k = len := by omega
      subst k
      exact hstr.nul.symm
  exact ⟨p, g0, hpre, hframe, hx20, hx21, hx9, hpArena, hfresh,
    hstr', hcstr'⟩

/-- The exact copied-byte post reconstructs the copied C string, including
its terminating NUL. -/
theorem envDefineMemcpyPostCString
    (g' : (R : Register) → Option (RegisterType R))
    (p n len : Nat) (name : BitVec 64) (nameStr : String)
    (m0 : Mem) (bs : Nat → BitVec 8) (c : Config)
    (hn : n = len + 1) (hlen : len = nameStr.length)
    (hcstr : CString m0 name.toNat nameStr)
    (hstr : StrBytes m0 name len bs)
    (h : memcpy_bytepath_post g' 0x80002b44#64
      (BitVec.ofNat 64 p) n m0 bs c) :
    CString c.σ.mem (BitVec.ofNat 64 p).toNat nameStr := by
  apply cstring_shift_copy hcstr
  intro k hk
  rw [h.copied (k := k) (by omega)]
  by_cases hkl : k < len
  · exact (hstr.chars k hkl).1.symm
  · have hkeq : k = len := by omega
    subst k
    exact hstr.nul.symm

/-- The six concrete load-byte vectors consumed by the append store block. -/
def appendStoreLds
    (c0 c1 c2 c3
     n0 n1 n2 n3 n4 n5 n6 n7
     v0 v1 v2 v3 v4 v5 v6 v7
     s00 s01 s02 s03 s04 s05 s06 s07
     s10 s11 s12 s13 s14 s15 s16 s17
     s20 s21 s22 s23 s24 s25 s26 s27 : BitVec 8) :
    List (List (BitVec 8)) :=
  [[c0, c1, c2, c3],
   [n0, n1, n2, n3, n4, n5, n6, n7],
   [v0, v1, v2, v3, v4, v5, v6, v7],
   [s00, s01, s02, s03, s04, s05, s06, s07],
   [s10, s11, s12, s13, s14, s15, s16, s17],
   [s20, s21, s22, s23, s24, s25, s26, s27]]

private theorem appendMemFactsLw
    {m : Mem} {L : GRegs} {a : MInstr} {bs : List (BitVec 8)}
    (base : Nat) (hk : a.kind = .lw) (hea : (eaddrM a L).toNat = base)
    (hlo : 0x80000000 ≤ base) (hhi : base + 4 ≤ 0x100000000)
    (hht : base + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ base)
    (hal : base % 4 = 0) (hp : LPins4 m base bs) : MemFacts m L bs a := by
  unfold MemFacts
  rw [hk, hea]
  exact ⟨⟨hlo, hhi, hht⟩, hp⟩

private theorem appendMemFactsLd
    {m : Mem} {L : GRegs} {a : MInstr} {bs : List (BitVec 8)}
    (base : Nat) (hk : a.kind = .ld) (hea : (eaddrM a L).toNat = base)
    (hlo : 0x80000000 ≤ base) (hhi : base + 8 ≤ 0x100000000)
    (hht : base + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ base)
    (hal : base % 8 = 0) (hp : LPins8 m base bs) : MemFacts m L bs a := by
  unfold MemFacts
  rw [hk, hea]
  exact ⟨⟨hlo, hhi, hht⟩, hp⟩

private theorem appendMemFactsSd
    {m : Mem} {L : GRegs} {a : MInstr} {bs : List (BitVec 8)}
    (base : Nat) (hk : a.kind = .sd) (hea : (eaddrM a L).toNat = base)
    (hlo : 0x80000000 ≤ base) (hhi : base + 8 ≤ 0x100000000)
    (hht : tohostAddr + 16 ≤ base) (hal : base % 8 = 0) :
    MemFacts m L bs a := by
  unfold MemFacts
  rw [hk, hea]
  exact ⟨hlo, hhi, hht, hal⟩

private theorem appendMemFactsSw
    {m : Mem} {L : GRegs} {a : MInstr} {bs : List (BitVec 8)}
    (base : Nat) (hk : a.kind = .sw) (hea : (eaddrM a L).toNat = base)
    (hlo : 0x80000000 ≤ base) (hhi : base + 4 ≤ 0x100000000)
    (hht : tohostAddr + 16 ≤ base) (hal : base % 4 = 0) :
    MemFacts m L bs a := by
  unfold MemFacts
  rw [hk, hea]
  exact ⟨hlo, hhi, hht, hal⟩

/-- Address facts for the exact six-load/five-store append block.  Each range
is a represented arena range; the structure contains no execution premise. -/
structure AppendStoreFactsGeom
    (env src : BitVec 64) (count names vals : Nat) : Prop where
  envLo : 0x80000000 ≤ env.toNat
  envHi : env.toNat + 24 ≤ 0x100000000
  envHtif : tohostAddr + 16 ≤ env.toNat
  envAlign : env.toNat % 8 = 0
  srcLo : 0x80000000 ≤ src.toNat
  srcHi : src.toNat + 24 ≤ 0x100000000
  srcHtif : tohostAddr + 16 ≤ src.toNat
  srcAlign : src.toNat % 8 = 0
  nameLo : 0x80000000 ≤ names + 8 * count
  nameHi : names + 8 * count + 8 ≤ 0x100000000
  nameHtif : tohostAddr + 16 ≤ names + 8 * count
  nameAlign : (names + 8 * count) % 8 = 0
  valsLo : 0x80000000 ≤ vals + 24 * count
  valsHi : vals + 24 * count + 24 ≤ 0x100000000
  valsHtif : tohostAddr + 16 ≤ vals + 24 * count
  valsAlign : (vals + 24 * count) % 8 = 0
  countNext32 : count + 1 < 2^31

@[simp] private theorem appLine0 : mkLine 0x80002b44#64 0x000a2783#32 =
    ⟨0x80002b44#64, 0x000a2783#32, 0x83#8, 0x27#8, 0x0a#8, 0x00#8,
      .lw, 15, 20, 0, 0x000#12⟩ := by rfl
@[simp] private theorem appLine1 : mkLine 0x80002b48#64 0x008a3603#32 =
    ⟨0x80002b48#64, 0x008a3603#32, 0x03#8, 0x36#8, 0x8a#8, 0x00#8,
      .ld, 12, 20, 0, 0x008#12⟩ := by rfl
@[simp] private theorem appLine2 : mkLine 0x80002b4c#64 0x010a3703#32 =
    ⟨0x80002b4c#64, 0x010a3703#32, 0x03#8, 0x37#8, 0x0a#8, 0x01#8,
      .ld, 14, 20, 0, 0x010#12⟩ := by rfl
@[simp] private theorem appLine3 : mkLine 0x80002b50#64 0x00179693#32 =
    ⟨0x80002b50#64, 0x00179693#32, 0x93#8, 0x96#8, 0x17#8, 0x00#8,
      .slli, 13, 15, 0, 0x001#12⟩ := by rfl
@[simp] private theorem appLine4 : mkLine 0x80002b54#64 0x00379893#32 =
    ⟨0x80002b54#64, 0x00379893#32, 0x93#8, 0x98#8, 0x37#8, 0x00#8,
      .slli, 17, 15, 0, 0x003#12⟩ := by rfl
@[simp] private theorem appLine5 : mkLine 0x80002b58#64 0x00f686b3#32 =
    ⟨0x80002b58#64, 0x00f686b3#32, 0xb3#8, 0x86#8, 0xf6#8, 0x00#8,
      .add, 13, 13, 15, 0x000#12⟩ := by rfl
@[simp] private theorem appLine6 : mkLine 0x80002b5c#64 0x000ab803#32 =
    ⟨0x80002b5c#64, 0x000ab803#32, 0x03#8, 0xb8#8, 0x0a#8, 0x00#8,
      .ld, 16, 21, 0, 0x000#12⟩ := by rfl
@[simp] private theorem appLine7 : mkLine 0x80002b60#64 0x008ab503#32 =
    ⟨0x80002b60#64, 0x008ab503#32, 0x03#8, 0xb5#8, 0x8a#8, 0x00#8,
      .ld, 10, 21, 0, 0x008#12⟩ := by rfl
@[simp] private theorem appLine8 : mkLine 0x80002b64#64 0x010ab583#32 =
    ⟨0x80002b64#64, 0x010ab583#32, 0x83#8, 0xb5#8, 0x0a#8, 0x01#8,
      .ld, 11, 21, 0, 0x010#12⟩ := by rfl
@[simp] private theorem appLine9 : mkLine 0x80002b68#64 0x01160633#32 =
    ⟨0x80002b68#64, 0x01160633#32, 0x33#8, 0x06#8, 0x16#8, 0x01#8,
      .add, 12, 12, 17, 0x000#12⟩ := by rfl
@[simp] private theorem appLine10 : mkLine 0x80002b6c#64 0x00369693#32 =
    ⟨0x80002b6c#64, 0x00369693#32, 0x93#8, 0x96#8, 0x36#8, 0x00#8,
      .slli, 13, 13, 0, 0x003#12⟩ := by rfl
@[simp] private theorem appLine11 : mkLine 0x80002b70#64 0x00963023#32 =
    ⟨0x80002b70#64, 0x00963023#32, 0x23#8, 0x30#8, 0x96#8, 0x00#8,
      .sd, 0, 12, 9, 0x000#12⟩ := by rfl
@[simp] private theorem appLine12 : mkLine 0x80002b74#64 0x00d70733#32 =
    ⟨0x80002b74#64, 0x00d70733#32, 0x33#8, 0x07#8, 0xd7#8, 0x00#8,
      .add, 14, 14, 13, 0x000#12⟩ := by rfl
@[simp] private theorem appLine13 : mkLine 0x80002b78#64 0x0017879b#32 =
    ⟨0x80002b78#64, 0x0017879b#32, 0x9b#8, 0x87#8, 0x17#8, 0x00#8,
      .addiw, 15, 15, 0, 0x001#12⟩ := by rfl
@[simp] private theorem appLine14 : mkLine 0x80002b7c#64 0x01073023#32 =
    ⟨0x80002b7c#64, 0x01073023#32, 0x23#8, 0x30#8, 0x07#8, 0x01#8,
      .sd, 0, 14, 16, 0x000#12⟩ := by rfl
@[simp] private theorem appLine15 : mkLine 0x80002b80#64 0x00a73423#32 =
    ⟨0x80002b80#64, 0x00a73423#32, 0x23#8, 0x34#8, 0xa7#8, 0x00#8,
      .sd, 0, 14, 10, 0x008#12⟩ := by rfl
@[simp] private theorem appLine16 : mkLine 0x80002b84#64 0x00b73823#32 =
    ⟨0x80002b84#64, 0x00b73823#32, 0x23#8, 0x38#8, 0xb7#8, 0x00#8,
      .sd, 0, 14, 11, 0x010#12⟩ := by rfl
@[simp] private theorem appLine17 : mkLine 0x80002b88#64 0x00fa2023#32 =
    ⟨0x80002b88#64, 0x00fa2023#32, 0x23#8, 0x20#8, 0xfa#8, 0x00#8,
      .sw, 0, 20, 15, 0x000#12⟩ := by rfl

/-- All six load lists and all exact machine-side facts for the append block. -/
theorem appendStoreFacts
    (env src copied : BitVec 64) (count names vals : Nat) (m : Mem)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (v : Vsa.While.Value)
    (hcode : Vsa.Sim.Code.Env_defineLoaded m)
    (hcount : read32 m env.toNat = some count)
    (hnames : read64 m (env.toNat + 8) = some names)
    (hvals : read64 m (env.toNat + 16) = some vals)
    (hword : ValueWordRepr m N φc src.toNat v)
    (hgeom : AppendStoreFactsGeom env src count names vals) :
    ∃ lds,
      ChainFacts m m (appendStoreL env src copied) lds appendStoreSeg ∧
      bytesVal .lw (lds.getD 0 []) = BitVec.ofNat 64 count ∧
      bytesVal .ld (lds.getD 1 []) = BitVec.ofNat 64 names ∧
      bytesVal .ld (lds.getD 2 []) = BitVec.ofNat 64 vals ∧
      LPins8 m src.toNat (lds.getD 3 []) ∧
      LPins8 m (src.toNat + 8) (lds.getD 4 []) ∧
      LPins8 m (src.toNat + 16) (lds.getD 5 []) := by
  obtain ⟨c0,c1,c2,c3,hc0,hc1,hc2,hc3,hcountRec⟩ :=
    read32_bytes_ed m env.toNat count hcount
  obtain ⟨n0,n1,n2,n3,n4,n5,n6,n7,hn0,hn1,hn2,hn3,hn4,hn5,hn6,hn7,_⟩ :=
    read64_bytes_eg4 m (env.toNat + 8) names hnames
  obtain ⟨v0,v1,v2,v3,v4,v5,v6,v7,hv0,hv1,hv2,hv3,hv4,hv5,hv6,hv7,_⟩ :=
    read64_bytes_eg4 m (env.toNat + 16) vals hvals
  obtain ⟨_, d0, d1, d2, hd0, hd1, hd2⟩ := hword
  obtain ⟨s00,s01,s02,s03,s04,s05,s06,s07,hs00,hs01,hs02,hs03,hs04,hs05,hs06,hs07,_⟩ :=
    read64_bytes_eg4 m src.toNat d0.toNat hd0
  obtain ⟨s10,s11,s12,s13,s14,s15,s16,s17,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,_⟩ :=
    read64_bytes_eg4 m (src.toNat + 8) d1.toNat hd1
  obtain ⟨s20,s21,s22,s23,s24,s25,s26,s27,hs20,hs21,hs22,hs23,hs24,hs25,hs26,hs27,_⟩ :=
    read64_bytes_eg4 m (src.toNat + 16) d2.toNat hd2
  let lds := appendStoreLds c0 c1 c2 c3 n0 n1 n2 n3 n4 n5 n6 n7
    v0 v1 v2 v3 v4 v5 v6 v7 s00 s01 s02 s03 s04 s05 s06 s07
    s10 s11 s12 s13 s14 s15 s16 s17 s20 s21 s22 s23 s24 s25 s26 s27
  have hpc : LPins4 m env.toNat [c0,c1,c2,c3] :=
    ⟨lpin_of_present hc0, lpin_of_present hc1, lpin_of_present hc2,
      lpin_of_present hc3⟩
  have hpn : LPins8 m (env.toNat + 8) [n0,n1,n2,n3,n4,n5,n6,n7] :=
    ⟨lpin_of_present hn0, lpin_of_present hn1, lpin_of_present hn2,
      lpin_of_present hn3, lpin_of_present hn4, lpin_of_present hn5,
      lpin_of_present hn6, lpin_of_present hn7⟩
  have hpv : LPins8 m (env.toNat + 16) [v0,v1,v2,v3,v4,v5,v6,v7] :=
    ⟨lpin_of_present hv0, lpin_of_present hv1, lpin_of_present hv2,
      lpin_of_present hv3, lpin_of_present hv4, lpin_of_present hv5,
      lpin_of_present hv6, lpin_of_present hv7⟩
  have hp0 : LPins8 m src.toNat [s00,s01,s02,s03,s04,s05,s06,s07] :=
    ⟨lpin_of_present hs00, lpin_of_present hs01, lpin_of_present hs02,
      lpin_of_present hs03, lpin_of_present hs04, lpin_of_present hs05,
      lpin_of_present hs06, lpin_of_present hs07⟩
  have hp1 : LPins8 m (src.toNat + 8) [s10,s11,s12,s13,s14,s15,s16,s17] :=
    ⟨lpin_of_present hs10, lpin_of_present hs11, lpin_of_present hs12,
      lpin_of_present hs13, lpin_of_present hs14, lpin_of_present hs15,
      lpin_of_present hs16, lpin_of_present hs17⟩
  have hp2 : LPins8 m (src.toNat + 16) [s20,s21,s22,s23,s24,s25,s26,s27] :=
    ⟨lpin_of_present hs20, lpin_of_present hs21, lpin_of_present hs22,
      lpin_of_present hs23, lpin_of_present hs24, lpin_of_present hs25,
      lpin_of_present hs26, lpin_of_present hs27⟩
  have hcword : bytesVal .lw [c0,c1,c2,c3] = BitVec.ofNat 64 count := by
    simpa [bytesVal] using sext_count_ed c0 c1 c2 c3 count
      (by have := hgeom.countNext32; omega) hcountRec
  have hnword : bytesVal .ld [n0,n1,n2,n3,n4,n5,n6,n7] = BitVec.ofNat 64 names := by
    simpa using ld_value_eq_read64 m (env.toNat + 8) names
      n0 n1 n2 n3 n4 n5 n6 n7 hnames hn0 hn1 hn2 hn3 hn4 hn5 hn6 hn7
  have hvword : bytesVal .ld [v0,v1,v2,v3,v4,v5,v6,v7] = BitVec.ofNat 64 vals := by
    simpa using ld_value_eq_read64 m (env.toNat + 16) vals
      v0 v1 v2 v3 v4 v5 v6 v7 hvals hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7
  have hcount64 : count < 2^64 := by have := hgeom.countNext32; omega
  have hnames64 : names < 2^64 := by have := hgeom.nameHi; omega
  have hvals64 : vals < 2^64 := by have := hgeom.valsHi; omega
  have hstride8 : shift_bits_left (BitVec.ofNat 64 count)
      (Sail.BitVec.extractLsb (3#6) 5 0) = BitVec.ofNat 64 (8 * count) := by
    rw [shl3_lit]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hcount64, show (2 : Nat) ^ 3 = 8 by decide,
      Nat.mod_eq_of_lt (by have := hgeom.nameHi; omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := hgeom.nameHi; omega)]
    omega
  have hstride24 : shift_bits_left
      (shift_bits_left (BitVec.ofNat 64 count)
          (Sail.BitVec.extractLsb (1#6) 5 0) + BitVec.ofNat 64 count)
        (Sail.BitVec.extractLsb (3#6) 5 0) = BitVec.ofNat 64 (24 * count) :=
    stride_24 count (by have := hgeom.countNext32; omega)
  have hnameAddr : BitVec.ofNat 64 names + BitVec.ofNat 64 (8 * count) =
      BitVec.ofNat 64 (names + 8 * count) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnames64,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hgeom.nameHi; omega),
      Nat.mod_eq_of_lt (by have := hgeom.nameHi; omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := hgeom.nameHi; omega)]
  have hvalsAddr : BitVec.ofNat 64 vals + BitVec.ofNat 64 (24 * count) =
      BitVec.ofNat 64 (vals + 24 * count) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvals64,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hgeom.valsHi; omega),
      Nat.mod_eq_of_lt (by have := hgeom.valsHi; omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := hgeom.valsHi; omega)]
  have himm0 : (sign_extend (m := 64) (0#12) : BitVec 64).toNat = 0 := by decide
  have himm8 : (sign_extend (m := 64) (8#12) : BitVec 64).toNat = 8 := by decide
  have himm16 : (sign_extend (m := 64) (16#12) : BitVec 64).toNat = 16 := by decide
  have henv0lt : env.toNat < 2^64 := env.isLt
  have henv8lt : env.toNat + 8 < 2^64 := by have := hgeom.envHi; omega
  have henv16lt : env.toNat + 16 < 2^64 := by have := hgeom.envHi; omega
  have hsrc0lt : src.toNat < 2^64 := src.isLt
  have hsrc8lt : src.toNat + 8 < 2^64 := by have := hgeom.srcHi; omega
  have hsrc16lt : src.toNat + 16 < 2^64 := by have := hgeom.srcHi; omega
  have hnameSlotLt : names + 8 * count < 2^64 := by have := hgeom.nameHi; omega
  have hvalsSlotLt : vals + 24 * count < 2^64 := by have := hgeom.valsHi; omega
  have hvalsSlot8Lt : vals + 24 * count + 8 < 2^64 := by
    have := hgeom.valsHi; omega
  have hvalsSlot16Lt : vals + 24 * count + 16 < 2^64 := by
    have := hgeom.valsHi; omega
  refine ⟨lds, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · chain_facts hcode with "Vsa.Sim.Code.env_define_at_"
    · refine appendMemFactsLw env.toNat (by rfl) ?_ hgeom.envLo
        (by have := hgeom.envHi; omega)
        (by right; have := hgeom.envHtif; omega)
        (by have := hgeom.envAlign; omega) ?_
      · simp [eaddrM, appendStoreL, srcVal, lookupG, himm0,
          Nat.mod_eq_of_lt henv0lt]
      · simpa [lds, appendStoreLds] using hpc
    · refine appendMemFactsLd (env.toNat + 8) (by rfl) ?_
        (by have := hgeom.envLo; omega) (by have := hgeom.envHi; omega)
        (by right; have := hgeom.envHtif; omega)
        (by have := hgeom.envAlign; omega) ?_
      · simp [appendStoreSeg, eaddrM, appendStoreL, appendStoreLds, lds,
          stepMemM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, himm8,
          Nat.mod_eq_of_lt henv8lt]
      · simpa [lds, appendStoreLds] using hpn
    · refine appendMemFactsLd (env.toNat + 16) (by rfl) ?_
        (by have := hgeom.envLo; omega) (by have := hgeom.envHi; omega)
        (by right; have := hgeom.envHtif; omega)
        (by have := hgeom.envAlign; omega) ?_
      · simp [appendStoreSeg, eaddrM, appendStoreL, appendStoreLds, lds,
          stepMemM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG, himm16,
          Nat.mod_eq_of_lt henv16lt]
      · simpa [lds, appendStoreLds] using hpv
    · refine appendMemFactsLd src.toNat (by rfl) ?_ hgeom.srcLo
        (by have := hgeom.srcHi; omega)
        (by right; have := hgeom.srcHtif; omega) hgeom.srcAlign ?_
      · simp [appendStoreSeg, eaddrM, appendStoreL, appendStoreLds, lds,
          stepMemM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG,
          shamtOf, himm0, Nat.mod_eq_of_lt hsrc0lt]
      · simpa [lds, appendStoreLds] using hp0
    · refine appendMemFactsLd (src.toNat + 8) (by rfl) ?_
        (by have := hgeom.srcLo; omega) (by have := hgeom.srcHi; omega)
        (by right; have := hgeom.srcHtif; omega)
        (by have := hgeom.srcAlign; omega) ?_
      · simp [appendStoreSeg, eaddrM, appendStoreL, appendStoreLds, lds,
          stepMemM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG,
          shamtOf, himm8, Nat.mod_eq_of_lt hsrc8lt]
      · simpa [lds, appendStoreLds] using hp1
    · refine appendMemFactsLd (src.toNat + 16) (by rfl) ?_
        (by have := hgeom.srcLo; omega) (by have := hgeom.srcHi; omega)
        (by right; have := hgeom.srcHtif; omega)
        (by have := hgeom.srcAlign; omega) ?_
      · simp [appendStoreSeg, eaddrM, appendStoreL, appendStoreLds, lds,
          stepMemM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG,
          shamtOf, himm16, Nat.mod_eq_of_lt hsrc16lt]
      · simpa [lds, appendStoreLds] using hp2
    · refine appendMemFactsSd (names + 8 * count) (by rfl) ?_ hgeom.nameLo
        hgeom.nameHi hgeom.nameHtif hgeom.nameAlign
      simp [appendStoreSeg, eaddrM, appendStoreL, appendStoreLds, lds,
        stepMemM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG,
        shamtOf, hcword, hnword, hvword, hstride8, hnameAddr, himm0,
        Nat.mod_eq_of_lt hnameSlotLt]
    · refine appendMemFactsSd (vals + 24 * count) (by rfl) ?_ hgeom.valsLo
        (by have := hgeom.valsHi; omega) hgeom.valsHtif hgeom.valsAlign
      simp [appendStoreSeg, eaddrM, appendStoreL, appendStoreLds, lds,
        stepMemM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG,
        shamtOf, hcword, hnword, hvword, hstride24, hvalsAddr, himm0,
        Nat.mod_eq_of_lt hvalsSlotLt]
    · refine appendMemFactsSd (vals + 24 * count + 8) (by rfl) ?_
        (by have := hgeom.valsLo; omega) (by have := hgeom.valsHi; omega)
        (by have := hgeom.valsHtif; omega) (by have := hgeom.valsAlign; omega)
      simp [appendStoreSeg, eaddrM, appendStoreL, appendStoreLds, lds,
        stepMemM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG,
        shamtOf, hcword, hnword, hvword, hstride24, hvalsAddr, himm8,
        Nat.mod_eq_of_lt hvalsSlot8Lt]
    · refine appendMemFactsSd (vals + 24 * count + 16) (by rfl) ?_
        (by have := hgeom.valsLo; omega) hgeom.valsHi
        (by have := hgeom.valsHtif; omega) (by have := hgeom.valsAlign; omega)
      simp [appendStoreSeg, eaddrM, appendStoreL, appendStoreLds, lds,
        stepMemM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG,
        shamtOf, hcword, hnword, hvword, hstride24, hvalsAddr, himm16,
        Nat.mod_eq_of_lt hvalsSlot16Lt]
    · refine appendMemFactsSw env.toNat (by rfl) ?_ hgeom.envLo
        (by have := hgeom.envHi; omega) hgeom.envHtif
        (by have := hgeom.envAlign; omega)
      simp [appendStoreSeg, eaddrM, appendStoreL, appendStoreLds, lds,
        stepMemM, stepGM, stepLdsM, wvalM, srcVal, lookupG, eraseG,
        shamtOf, hcword, hnword, hvword, hstride24, hvalsAddr, himm0,
        Nat.mod_eq_of_lt henv0lt]
  · simpa [lds, appendStoreLds] using hcword
  · simpa [lds, appendStoreLds] using hnword
  · simpa [lds, appendStoreLds] using hvword
  · simpa [lds, appendStoreLds] using hp0
  · simpa [lds, appendStoreLds] using hp1
  · simpa [lds, appendStoreLds] using hp2

/-- The memcpy return and the retained helper frame marshal directly into the
exact append-block `SegPre`. -/
theorem appendSegPre_of_memcpy
    {SL : StackLayout} {gpv : BitVec 64} {headroom : Nat}
    {AInv : MState → List Extent → Prop} {exts : List Extent}
    (sp env src copied : BitVec 64)
    (g0 saved g' : (R : Register) → Option (RegisterType R))
    (n : Nat) (mEntry : Mem) (bs : Nat → BitVec 8) (c : Config)
    (lds : List (List (BitVec 8)))
    (hbyte : memcpy_bytepath_post g' 0x80002b44#64 copied n mEntry bs c)
    (hframe : EnvDefFrameSaved SL gpv headroom AInv exts sp g0 saved c)
    (hx20 : g0 Register.x20 = some env)
    (hx21 : g0 Register.x21 = some src)
    (hx9 : g0 Register.x9 = some copied)
    (hfacts : ChainFacts c.σ.mem c.σ.mem (appendStoreL env src copied) lds
      appendStoreSeg) :
    SegPre appendStoreSeg (appendStoreL env src copied) lds
        0x80002b44#64 c.σ.mem c ∧
      c.σ.regs.get? Register.x2 = some sp ∧
      EnvDefineSavedSpillFrame sp saved c := by
  obtain ⟨hgood, hpc, _ha0, _hra, _hcopy, _hout, htick, _hregs⟩ := hbyte
  obtain ⟨⟨hsp, _hstack, _hgp, habi, _hainv, _htickF, _hspill⟩, hsaved⟩ :=
    hframe
  have hx20' : c.σ.regs.get? Register.x20 = some env := by
    rw [habi Register.x20 (by decide), hx20]
  have hx21' : c.σ.regs.get? Register.x21 = some src := by
    rw [habi Register.x21 (by decide), hx21]
  have hx9' : c.σ.regs.get? Register.x9 = some copied := by
    rw [habi Register.x9 (by decide), hx9]
  have hholds : GHolds c.σ (appendStoreL env src copied) :=
    ⟨by simpa [gprGet] using hx20', by simpa [gprGet] using hx21',
      by simpa [gprGet] using hx9', trivial⟩
  exact ⟨⟨hgood, rfl, hpc, hgood.minstret, hholds,
    (by show KeysOK [20, 21, 9]; decide), hfacts, htick⟩, hsp, hsaved⟩

/-- The exact memcpy return, append stores, readback reconstruction, and shared
epilogue form one closed append suffix. -/
theorem envDefineAppendStoreEpilogue_of_memcpy
    {SL : StackLayout} {gpv : BitVec 64} {headroom : Nat}
    {AInv : MState → List Extent → Prop} {exts : List Extent}
    (A : Arena) (sp env src copied : BitVec 64)
    (g0 saved g' : (R : Register) → Option (RegisterType R))
    (n : Nat) (mEntry : Mem) (bs : Nat → BitVec 8) (c : Config)
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (store : Vsa.While.Store) (target : Vsa.While.Addr)
    (parent : Option Vsa.While.Addr)
    (vars : List (String × Vsa.While.Value))
    (name : String) (v : Vsa.While.Value) (cap names vals : Nat)
    (hbyte : memcpy_bytepath_post g' 0x80002b44#64 copied n mEntry bs c)
    (hhelper : EnvDefFrameSaved SL gpv headroom AInv exts sp g0 saved c)
    (hx20 : g0 Register.x20 = some env)
    (hx21 : g0 Register.x21 = some src)
    (hx9 : g0 Register.x9 = some copied)
    (hframe : FrameRepr c.σ.mem N φf φc env.toNat ⟨parent, vars⟩)
    (henv : env.toNat = φf target)
    (hget : store.frames[target]? = some ⟨parent, vars⟩)
    (hstore : StoreRepr c.σ.mem N A φf φc store)
    (howned : StoreHeapOwned c.σ.mem φf φc exts store)
    (habsent : vars.any (·.1 == name) = false)
    (hcap : read32 c.σ.mem (env.toNat + 4) = some cap)
    (happendArm : vars.length < cap)
    (hnamesMem : read64 c.σ.mem (env.toNat + 8) = some names)
    (hvalsMem : read64 c.σ.mem (env.toNat + 16) = some vals)
    (hword : ValueWordRepr c.σ.mem N φc src.toNat v)
    (hcopied : CString c.σ.mem copied.toNat name)
    (hfp : EnvDefineAppendFootprint c.σ.mem env.toNat names vals vars.length
      copied.toNat src.toNat vars name v)
    (hgeom : AppendStoreFactsGeom env src vars.length names vals)
    (hnameA : A.contains (names + 8 * vars.length) 8)
    (hvalsA : A.contains (vals + 24 * vars.length) 24)
    (henvA : A.contains env.toNat 4)
    (harenaStack : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo) :
    ∃ c', Vsa.Machine.Steps c c' ∧ ∃ m,
      EnvDefineEpilogueExactPost sp saved m c' ∧
      FrameRepr c'.σ.mem N φf φc env.toNat
        ⟨parent, vars ++ [(name, v)]⟩ ∧
      StoreDefineAdvance N A φf φc store target name v c'.σ.mem := by
  obtain ⟨_spillLds, himage, _hspillVals⟩ := hhelper.2
  obtain ⟨lds, hfacts, hcountWord, hnamesWord, hvalsWord, hp0, hp1, hp2⟩ :=
    appendStoreFacts env src copied vars.length names vals c.σ.mem N φc v
      himage.1 hframe.1 hnamesMem hvalsMem hword hgeom
  have hpre := appendSegPre_of_memcpy sp env src copied g0 saved g' n mEntry bs c
    lds hbyte hhelper hx20 hx21 hx9 hfacts
  obtain ⟨c1, hs1, hready⟩ := envDefineAppendStore saved env src copied sp lds
    c.σ.mem N φf φc parent vars name v cap names vals A hnameA hvalsA henvA
    harenaStack harenaCode hframe hcap happendArm hnamesMem hvalsMem hcountWord
    hnamesWord hvalsWord hp0 hp1 hp2 hword hcopied hfp
    hgeom.countNext32 (by have := hgeom.nameHi; omega)
    (by have := hgeom.valsHi; omega)
    (by have := hgeom.envHi; omega) c hpre
  obtain ⟨htargetBound, htarget⟩ := Array.getElem?_eq_some_iff.mp hget
  have htargetEq : store.frames[target] = ⟨parent, vars⟩ := htarget
  have hag : AgreeP (AppendUntouched env.toNat names vals vars.length)
      c.σ.mem c1.σ.mem := by
    rw [hready.row.2.1]
    rw [appendStoreLogExact env src copied lds vars.length names vals hcountWord
      hnamesWord hvalsWord hgeom.countNext32
      (by have := hgeom.nameHi; omega) (by have := hgeom.valsHi; omega)
      (by have := hgeom.envHi; omega)]
    exact appendStoreTowerAgree c.σ.mem env.toNat names vals vars.length copied
      (bytesVal .ld (lds.getD 3 [])) (bytesVal .ld (lds.getD 4 []))
      (bytesVal .ld (lds.getD 5 []))
  have hcap' : read32 c.σ.mem (φf target + 4) = some cap := by
    rw [← henv]
    exact hcap
  have hnames' : read64 c.σ.mem (φf target + 8) = some names := by
    rw [← henv]
    exact hnamesMem
  have hvals' : read64 c.σ.mem (φf target + 16) = some vals := by
    rw [← henv]
    exact hvalsMem
  have hfoot0 := StoreAppendFootprint.of_heap_owned (N := N) htargetBound howned hcap' hnames'
    hvals' (by simpa [htargetEq] using happendArm)
    (by simpa [henv, htargetEq] using hag)
  have hfoot : StoreAppendFootprint c.σ.mem c1.σ.mem N φf φc store target
      env.toNat names vals vars.length := by
    simpa [henv, htargetEq] using hfoot0
  have hnew : FrameRepr c1.σ.mem N φf φc (φf target)
      ⟨parent, vars ++ [(name, v)]⟩ := by
    rw [← henv]
    exact hready.readback.frame
  have hadv1 : StoreDefineAdvance N A φf φc store target name v c1.σ.mem :=
    storeDefineAdvance_of_append hstore hget habsent hnew hag hfoot
  obtain ⟨epiLds, hepiFacts, hepiValues⟩ := hready.savedSpills.chainFacts
  have hepiPre : SegPre envDefineEpilogueSeg (envDefineEpilogueL sp) epiLds
      0x80002aec#64 c1.σ.mem c1 :=
    ⟨hready.row.1, rfl, hready.row.2.2, hready.row.1.minstret,
      ⟨hready.spReg, trivial⟩, (by show KeysOK [2]; decide), hepiFacts,
      hready.tick⟩
  obtain ⟨c2, hs2, hepiPost⟩ :=
    envDefineEpilogueRow sp epiLds c1.σ.mem c1 hepiPre
  have hepi := envDefineEpilogueExact_of_post sp saved epiLds c1.σ.mem c2
    hepiValues hepiPost
  have hframe2 : FrameRepr c2.σ.mem N φf φc env.toNat
      ⟨parent, vars ++ [(name, v)]⟩ := by
    rw [hepi.mem]
    exact hready.readback.frame
  refine ⟨c2, hs1.trans hs2, c1.σ.mem, hepi, hframe2, ?_⟩
  rw [hepi.mem]
  exact hadv1

/-- Execute the proved byte-route memcpy summary while retaining the helper
frame, saved caller image, and append registers. -/
theorem envDefineMemcpyCallSaved
    {A : Vsa.RuntimeRepr.Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (saved : (R : Register) → Option (RegisterType R))
    (exts : List Extent) (n len : Nat) (sp env name src : BitVec 64)
    (nameStr : String) (bs : Nat → BitVec 8)
    (hn : n = len + 1) (hlen : len = nameStr.length)
    (hroute : ∀ p, (name.toNat ^^^ p) % 8 ≠ 0 ∨ n < 8)
    (hArenaHi : A.hi ≤ 2^64)
    (harenaSpill : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo)
    (hAInvStableFoot : ∀ (p : Nat) (sigmaa sigmab : MState),
      sigmaa.regs.get? Register.x3 = sigmab.regs.get? Register.x3 →
      (∀ a : Nat, (a < p ∨ p + n ≤ a) →
        sigmaa.mem[a]? = sigmab.mem[a]?) →
      M.AInv sigmaa ((p, n) :: exts) → M.AInv sigmab ((p, n) :: exts)) :
    Triple
      (fun c => ∃ p g0,
        PreDispatch g0 0x80002b44#64 (BitVec.ofNat 64 p) name n
          c.σ.mem bs c ∧
        EnvDefFrameSaved SL gpv headroom M.AInv ((p, n) :: exts) sp
          g0 saved c ∧
        g0 Register.x20 = some env ∧ g0 Register.x21 = some src ∧
        g0 Register.x9 = some (BitVec.ofNat 64 p) ∧
        A.contains p n ∧ (∀ e ∈ exts, ExtDisjoint (p, n) e) ∧
        StrBytes c.σ.mem name len bs ∧ CString c.σ.mem name.toNat nameStr)
      (fun c => ∃ p g0 mEntry g',
        memcpy_bytepath_post g' 0x80002b44#64 (BitVec.ofNat 64 p) n
          mEntry bs c ∧
        EnvDefFrameSaved SL gpv headroom M.AInv ((p, n) :: exts) sp
          g0 saved c ∧
        g0 Register.x20 = some env ∧ g0 Register.x21 = some src ∧
        g0 Register.x9 = some (BitVec.ofNat 64 p) ∧
        StrBytes mEntry name len bs ∧
        CString c.σ.mem (BitVec.ofNat 64 p).toNat nameStr) := by
  intro c h
  obtain ⟨p, g0, hpre, hframe, hx20, hx21, hx9, hpArena, _hfresh,
    hstr, hcstr⟩ := h
  have hpLt : p < 2^64 := by
    change A.lo ≤ p ∧ p + n ≤ A.hi at hpArena
    have := hpre.npos
    omega
  have hpNat : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpLt]
  have hroute' : (name.toNat ^^^ (BitVec.ofNat 64 p).toNat) % 8 ≠ 0 ∨ n < 8 := by
    rw [hpNat]
    exact hroute p
  have hpArena' : A.contains (BitVec.ofNat 64 p).toNat n := by
    rw [hpNat]
    exact hpArena
  let mEntry := c.σ.mem
  obtain ⟨c', hs, hpost, hframe'⟩ :=
    envDefMemcpyFramedSaved A SL gpv headroom M.AInv ((p, n) :: exts)
      sp g0 saved 0x80002b44#64 (BitVec.ofNat 64 p) name n mEntry bs
      (by decide) hroute' hpArena' harenaSpill harenaCode
      (by
        intro σa σb hgp hmem hinv
        apply hAInvStableFoot p σa σb hgp
        · intro a ha
          apply hmem a
          simpa only [hpNat] using ha
        · exact hinv)
      c ⟨by simpa [mEntry] using hpre, hframe⟩
  obtain ⟨g', hbyte⟩ := hpost
  have hcstrEntry : CString mEntry name.toNat nameStr := by
    simpa [mEntry] using hcstr
  have hcopied := envDefineMemcpyPostCString g' p n len name nameStr mEntry bs c'
    hn hlen hcstrEntry hstr hbyte
  exact ⟨c', hs, p, g0, mEntry, g', hbyte, hframe', hx20, hx21, hx9,
    hstr, hcopied⟩

end Vsa.Sim
