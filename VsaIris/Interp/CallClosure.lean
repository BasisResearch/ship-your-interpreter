import VsaIris.Interp.CallNativeSeg
import VsaIris.Interp.CallPrefixP
import VsaIris.Interp.SymInterp

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Newlib
open Vsa.MemRepr Vsa.Sim Vsa.While
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.RuntimeRepr

section Defs

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

structure CloFactsE (s : Store) (ca p : Nat) (cd : ClosureData) (q e : Nat) (img : Nat → BitVec 8)
    (P : Nat → Prop) (m : Mem) : Prop where
  lookup : s.closures[ca]? = some cd
  fn : imgLE img p 8 = q
  env : imgLE img (p + 8) 8 = e
  objOK : ∀ k, InExt (p, 16) k → ReadOK k
  repr : ExprReprWithin m P q (.fn cd.name cd.params cd.body)
  geo : ∀ k, P k → ReadOK k
  win : SharedWin P

def CloRes (s : Store) (ca p : Nat) : IProp GF :=
  iprop(∃ (cd : ClosureData) (q e : Nat) (img : Nat → BitVec 8) (P : Nat → Prop) (m : Mem),
    ⌜CloFactsE s ca p cd q e img P m⌝ ∗ roImg (InExt (p, 16)) img ∗ roOn P m ∗ frameAt cd.env e)

instance (s : Store) (ca p : Nat) : Persistent (CloRes (GF := GF) s ca p) := by
  unfold CloRes; infer_instance

def CloSupply (N : NativeAddrs) : Prop :=
  ∀ (s : Store) (B : List (Nat × Nat)) (ca p : Nat),
    storeRepr (GF := GF) N s B ∗ closAt ca p ⊢ storeRepr N s B ∗ CloRes s ca p

theorem dispSupply_of_cloSupply {N : NativeAddrs} (h : CloSupply (GF := GF) N) :
    DispSupply (GF := GF) N := by
  intro s B ca p
  iintro ⟨Hs, #Hc⟩
  ihave ⟨Hs, #Hr⟩ := h s B ca p $$ [$]
  iframe Hs
  unfold CloRes
  icases Hr with ⟨%cd, %q, %e, %img, %P, %m, %hf, #Himg, #Hro, -⟩
  unfold dispRes
  iexists cd, p, q, img, P, m
  iframe Hc Himg Hro
  ipureintro
  exact ⟨hf.lookup, hf.fn, hf.objOK, hf.repr, hf.geo, hf.win⟩

theorem cloSupply {N : NativeAddrs} : CloSupply (GF := GF) N := by
  intro s B ca p
  iintro ⟨Hs, #Hat⟩
  ihave ⟨⟨Hs, -⟩, %hlt⟩ := keep_pure (storeRepr_closAt (GF := GF) N (s := s) (B := B)
    (ca := ca) (p := p)) $$ [$]
  obtain ⟨cd, hcd⟩ : ∃ cd, s.closures[ca]? = some cd :=
    ⟨s.closures[ca], Array.getElem?_eq_getElem hlt⟩
  have h' : s.closures.toList[ca]? = some cd := by rw [Array.getElem?_toList]; exact hcd
  have hg := closuresOwn_get (GF := GF) 0 s.closures.toList ca cd h'
  rw [Nat.zero_add] at hg
  unfold storeRepr
  icases Hs with ⟨%mf, %mc, %Bs, Hf, Hc, %hpure, Hfr, #Hcl⟩
  ihave #Ho := hg $$ Hcl
  isplitl [Hf Hc Hfr]
  · iexists mf, mc, Bs
    iframe Hf Hc Hfr Hcl
    ipureintro; exact hpure
  unfold closOwn CloRes astEG
  icases Ho with ⟨%p', %q, %e, %img, #Hat', %hobj, #Hro, ⟨%P, %m, %⟨hrepr, hgeo⟩, #HroP⟩, #Henv⟩
  ihave %hpp := closAt_agree ca p p' $$ [$]
  subst hpp
  iexists cd, q, e, img, P, m
  iframe Hro HroP Henv
  ipureintro
  exact ⟨hcd, hobj.fn, hobj.env, hobj.objOK, hrepr, hgeo,
    fun k hk => ⟨(hgeo k hk).lo, (hgeo k hk).win.1, (hgeo k hk).win.2⟩⟩

end Defs

section Views

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem roOwn_roImg {img : Nat → BitVec 8} {p n : Nat} :
    codeRes (GF := GF) ∗ roImg (InExt (p, n)) img ⊢
      ∃ Dt : Mem, roOwn roR (interpText ++ dataOf Dt (accAddrs p n)) ∗
        ⌜∀ k, p ≤ k → k < p + n → imgM Dt k = img k⌝ := by
  iintro ⟨#Hc, #H1⟩
  obtain ⟨Dt, hDt⟩ := exists_mem_img img (accAddrs p n)
  have hc : ∀ k, p ≤ k → k < p + n → imgM Dt k = img k := fun k h1 h2 =>
    hDt k (mem_accAddrs_iff.2 ⟨h1, h2⟩)
  iexists Dt
  isplitl
  · unfold codeRes roOwn at *
    icases Hc with ⟨#Hgp, #Htx⟩
    iframe Hgp
    iapply (sepL_append _ _ _).2
    iframe Htx
    unfold dataOf
    rw [sepL_map]
    iapply sepL_of_persistent (roImg (InExt (p, n)) img) _ _ (fun k hk => by
      obtain ⟨h1, h2⟩ := mem_accAddrs_iff.1 hk
      rw [hc k h1 h2]
      unfold roImg
      iintro #H
      iapply H $$ %k %(show InExt (p, n) k by simp [InExt]; omega)) $$ H1
  · ipureintro; exact hc

end Views

section World

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

theorem world_depth (N : NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat) (ρ : Regime)
    (st : St) (d : Nat) :
    world (GF := GF) N L Room inp ρ st d ⊢
      ∃ img : Nat → BitVec 8, ownImg (InExt (inp + interpDepthOff, 4)) img ∗
        ⌜imgLE img (inp + interpDepthOff) 4 = d ∧ d ≤ maxCallDepth⌝ ∗
        (∀ (d' : Nat) (img' : Nat → BitVec 8), ownImg (InExt (inp + interpDepthOff, 4)) img' -∗
          ⌜imgLE img' (inp + interpDepthOff) 4 = d' ∧ d' ≤ maxCallDepth⌝ -∗
          world N L Room inp ρ st d') := by
  unfold world worldE interpCtxE interpCoreE wordAt
  iintro ⟨%H, %B, Hh, Hs, Hc, Hio, ⟨⟨%g, Hg, Hfa, ⟨%img, Hd, %hd⟩, %hdle, Hpad, He⟩, Hjb⟩, %hB, #Hb⟩
  iexists img
  iframe Hd
  isplitl []
  · ipureintro; exact ⟨hd, hdle⟩
  iintro %d' %img' Hd %⟨hd', hdle'⟩
  iexists H, B
  iframe Hh Hs Hc Hio Hjb
  isplitl [Hg Hfa Hd Hpad He]
  · iexists g
    iframe Hg Hfa Hpad He
    isplitl [Hd]
    · iexists img'
      iframe Hd
      ipureintro; exact hd'
    · ipureintro; exact hdle'
  · iframe Hb; ipureintro; exact hB

end World

end VsaIris.Interp

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast
open Vsa.MemRepr Vsa.Sim Vsa.While

theorem ldvf_lw_eq_small {f : Nat → BitVec 8} {a k j : Nat} (h : imgLE f a 4 = k) (hj : j < 2 ^ 31)
    (he : ldvf .lw f a = BitVec.ofNat 64 j) : k = j := by
  by_cases hk : k < 2 ^ 31
  · rw [ldvf_lw_imgLE h hk] at he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  · exfalso
    have hw := toNat_append4 f a
    rw [h] at hw
    have hk32 : k < 2 ^ 32 := by have := imgLE_lt f a 4; omega
    have := congrArg BitVec.toNat he
    simp only [ldvf, bytesAt4, bytesVal, widthOfM, List.getD_cons_zero, List.getD_cons_succ,
      LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend] at this
    have hmsb : ((((f (a + 3)).append (f (a + 2))).append (f (a + 1))).append (f a) :
        BitVec (8 * 4)).msb = true := by
      rw [BitVec.msb_eq_decide]; simp only [decide_eq_true_eq]; omega
    rw [hmsb] at this
    simp only [ite_true, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
    rw [hw] at this
    omega

theorem paramsRepr_length {m : Mem} {P : Nat → Prop} :
    ∀ {a n : Nat} {ps : List String}, ParamsReprWithin m P a n ps → ps.length = n
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ _ _ hrest => by simp [paramsRepr_length hrest]

theorem sext32_toNat_small {a : Nat} (h : a < 2 ^ 31) :
    (BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.ofNat 64 a))).toNat = a := by
  have hi := VsaIris.Interp.sext32_ofNat_toInt h
  rw [BitVec.toInt_eq_toNat_cond] at hi
  split at hi <;> omega

abbrev fnView (q : Nat) : List Nat := accAddrs (q + 8) 20 ++ accAddrs (q + 32) 8

structure FnNode (m : Mem) (P : Nat → Prop) (q : BitVec 64) (paramc : Nat) (prm bod nam : BitVec 64) :
    Prop where
  pcr : imgLE (imgM m) (q + 24#64).toNat 4 = paramc
  prm : ldv .ld m (q + 16#64).toNat = prm
  bod : ldv .ld m (q + 32#64).toNat = bod
  nam : ldv .ld m (q + 8#64).toNat = nam
  lo : 0x80000000 ≤ q.toNat
  hi : q.toNat + 40 ≤ 0x100000000
  off : q.toNat + 40 ≤ tohostAddr ∨ tohostAddr + 16 ≤ q.toNat
  view : ∀ a ∈ fnView q.toNat, P a ∧ (m[a]?).isSome

theorem readLE_imgM {m : Mem} {a n v : Nat} (h : readLE m a n = some v) : imgLE (imgM m) a n = v := by
  have := readLE_of_img (m := m) (img := imgM m) (a := a) (n := n) (fun i hi => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (isSome_of_readLE h hi)
    rw [hb]; simp [imgM, hb])
  rw [this] at h; cases h; rfl

theorem fnNode_of {m : Mem} {P : Nat → Prop} {q : BitVec 64} {name : Option String}
    {ps : List String} {ss : List Stmt}
    (h : ExprReprWithin m P q.toNat (.fn name ps ss)) (hg : ∀ k, P k → ReadOK k) :
    ∃ prm bod nam : Nat, FnNode m P q ps.length (BitVec.ofNat 64 prm) (BitVec.ofNat 64 bod)
        (BitVec.ofNat 64 nam) ∧ prm < 2 ^ 64 ∧ bod < 2 ^ 64 ∧ nam < 2 ^ 64 ∧
      ParamsReprWithin m P prm ps.length ps ∧ StmtReprWithin m P bod (.block ss) ∧
      (name = none ∧ nam = 0 ∨ ∃ x, name = some x ∧ nam ≠ 0 ∧ CStringWithin m P nam x) := by
  have core : ∀ (nam prm pc bod : Nat), read32 m q.toNat = some 10 → Covers P q.toNat 4 →
      read64 m (q.toNat + 8) = some nam → Covers P (q.toNat + 8) 8 →
      read64 m (q.toNat + 16) = some prm → Covers P (q.toNat + 16) 8 →
      read32 m (q.toNat + 24) = some pc → Covers P (q.toNat + 24) 4 →
      ParamsReprWithin m P prm pc ps →
      read64 m (q.toNat + 32) = some bod → Covers P (q.toNat + 32) 8 →
      StmtReprWithin m P bod (.block ss) →
      FnNode m P q ps.length (BitVec.ofNat 64 prm) (BitVec.ofNat 64 bod) (BitVec.ofNat 64 nam) ∧
        prm < 2 ^ 64 ∧ bod < 2 ^ 64 ∧ nam < 2 ^ 64 ∧ ParamsReprWithin m P prm ps.length ps := by
    intro nam prm pc bod hk ck hn cn hp cp hc cc hps hb cb _
    have hlen := paramsRepr_length hps
    subst hlen
    have g0 := hg _ (ck 0 (by omega)); have g39 := hg _ (cb 7 (by omega))
    have e : ∀ c, c ≤ 32 → (q + BitVec.ofNat 64 c).toNat = q.toNat + c := fun c hc => by
      have := g39.hi; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    refine ⟨⟨?_, ?_, ?_, ?_, g0.lo, ?_, ?_, ?_⟩, readLE_lt hp, readLE_lt hb, readLE_lt hn, hps⟩
    · rw [e 24 (by omega)]; exact readLE_imgM hc
    · rw [e 16 (by omega)]; exact ldv_ld_read64 hp
    · rw [e 32 (by omega)]; exact ldv_ld_read64 hb
    · rw [e 8 (by omega)]; exact ldv_ld_read64 hn
    · have := g39.hi; omega
    · have h0 := g0.off; have h8 := (hg _ (cn 0 (by omega))).off; have h15 := (hg _ (cn 7 (by omega))).off
      have h16 := (hg _ (cp 0 (by omega))).off; have h23 := (hg _ (cp 7 (by omega))).off
      have h24 := (hg _ (cc 0 (by omega))).off; have h27 := (hg _ (cc 3 (by omega))).off
      have h32 := (hg _ (cb 0 (by omega))).off; have h39 := g39.off
      have h3 := (hg _ (ck 3 (by omega))).off
      simp only [Nat.add_zero] at *; omega
    · intro a ha
      simp only [List.mem_append, mem_accAddrs_iff] at ha
      rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · by_cases j1 : a < q.toNat + 16
        · obtain ⟨j, rfl⟩ : ∃ j, a = q.toNat + 8 + j := ⟨a - (q.toNat + 8), by omega⟩
          exact ⟨cn j (by omega), isSome_of_readLE hn (by omega)⟩
        · by_cases j2 : a < q.toNat + 24
          · obtain ⟨j, rfl⟩ : ∃ j, a = q.toNat + 16 + j := ⟨a - (q.toNat + 16), by omega⟩
            exact ⟨cp j (by omega), isSome_of_readLE hp (by omega)⟩
          · obtain ⟨j, rfl⟩ : ∃ j, a = q.toNat + 24 + j := ⟨a - (q.toNat + 24), by omega⟩
            exact ⟨cc j (by omega), isSome_of_readLE hc (by omega)⟩
      · obtain ⟨j, rfl⟩ : ∃ j, a = q.toNat + 32 + j := ⟨a - (q.toNat + 32), by omega⟩
        exact ⟨cb j (by omega), isSome_of_readLE hb (by omega)⟩
  cases h with
  | fnNamed hk ck hn cn hne hstr hp cp hc cc hps hb cb hbody =>
    rename_i nam prm pc bod x
    obtain ⟨f, h1, h2, h3, h4⟩ := core nam prm pc bod hk ck hn cn hp cp hc cc hps hb cb hbody
    exact ⟨prm, bod, nam, f, h1, h2, h3, h4, hbody, .inr ⟨x, rfl, hne, hstr⟩⟩
  | fnAnon hk ck hn cn hp cp hc cc hps hb cb hbody =>
    rename_i prm pc bod
    obtain ⟨f, h1, h2, h3, h4⟩ := core 0 prm pc bod hk ck hn cn hp cp hc cc hps hb cb hbody
    exact ⟨prm, bod, 0, f, h1, h2, h3, h4, hbody, .inl ⟨rfl, rfl⟩⟩

#ix_seg CallK_runA {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {aX s w0 w1 w2 : BitVec 64} (hfg : EvalFrameG s) (hx : RamWin aX.toNat 28)
    (h8 : R 8 = aX) (h2 : R 2 = s + 18446744073709550528#64)
    (hW0 : ldv .ld Mt (s.toNat - 1088 + 96) = w0) (hW1 : ldv .ld Mt (s.toNat - 1088 + 104) = w1)
    (hW2 : ldv .ld Mt (s.toNat - 1088 + 112) = w2) (hK : ldv .lw Mt (s.toNat - 1088 + 96) = 4#64) :
    IW live m (callView aX.toNat) (InExt (s.toNat - 1088, 1088)) Q 0x80003254#64 R Mt
  by with_frame with_geom sym_run hlive using [h8, h2, hW0, hW1, hW2, hK, hfg.sf] at 0x80003288

#ix_seg CallK_runB {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Dt Mt : Mem} {R : Nat → BitVec 64}
    {s cp q : BitVec 64} (hfg : EvalFrameG s) (hc : RamWin cp.toNat 16)
    (h13 : R 13 = cp) (h2 : R 2 = s + 18446744073709550528#64) (hq : ldv .ld Dt cp.toNat = q) :
    IW live Dt (accAddrs cp.toNat 16) (InExt (s.toNat - 1088, 1088)) Q 0x80003288#64 R Mt
  by with_geom sym_run hlive using [h13, h2, hq, hfg.sf] at 0x80003294

#ix_seg CallK_runC {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Dt Mt : Mem} {R : Nat → BitVec 64}
    {s q inp pv : BitVec 64} {dep : Nat} (hfg : EvalFrameG s) (hq : RamWin q.toNat 40)
    (hig : Newlib.RtErr.InpGeom inp)
    (hi3 : inp.toNat + 12 ≤ s.toNat - 1088 ∨ s.toNat ≤ inp.toNat + 8) (hia : inp.toNat % 8 = 0)
    (h14 : R 14 = q) (h18 : R 18 = inp) (h2 : R 2 = s + 18446744073709550528#64)
    (hpc : ldv .lw Dt (q + 24#64).toNat = pv)
    (hdep : ldv .lw Mt (inp + 8#64).toNat = BitVec.ofNat 64 dep) :
    IW live Dt (accAddrs (q.toNat + 24) 4)
      (fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (inp.toNat + 8, 4) b) Q 0x80003294#64 R Mt
  by with_geom sym_run hlive using [h14, h18, h2, hpc, hdep, hfg.sf] at 0x80003d60 0x80003ca4 0x800032b4

#ix_seg CallK_runD {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {Dt Mt : Mem} {R : Nat → BitVec 64}
    {s cp e inp : BitVec 64} (hfg : EvalFrameG s) (hc : RamWin cp.toNat 16)
    (h13 : R 13 = cp) (h2 : R 2 = s + 18446744073709550528#64)
    (he : ldv .ld Dt (cp + 8#64).toNat = e) :
    IW live Dt (accAddrs cp.toNat 16)
      (fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (inp.toNat + 8, 4) b) Q 0x800032b4#64 R Mt
  by with_geom sym_run hlive using [h13, h2, he, hfg.sf] at 0x800032bc

end VsaIris.Interp

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Newlib
open Vsa.MemRepr Vsa.Sim Vsa.While
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris.Inst Vsa.RuntimeRepr

abbrev cloS (s inp : BitVec 64) : Nat → Prop :=
  fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (inp.toNat + 8, 4) b

structure CloHd (R1 : Nat → BitVec 64) (Mt1 Mt : Mem) (s aX sret inp ret e q line : BitVec 64)
    (rv : Nat → BitVec 64) (argc dep : Nat) : Prop where
  a0 : R1 10 = e
  sp : R1 2 = s + 18446744073709550528#64
  s0 : R1 8 = aX
  s1 : R1 9 = sret
  s2 : R1 18 = inp
  s5 : R1 21 = q
  s7 : R1 23 = line
  keep : ∀ x ∈ [19, 20, 22, 24, 25, 26, 27], R1 x = rv x
  saved : CallSaved Mt1 s ret (rv 8) (rv 9) (rv 18)
  s3m : ldv .ld Mt1 (s.toNat - 1088 + 1048) = rv 19
  s5m : ldv .ld Mt1 (s.toNat - 1088 + 1032) = rv 21
  s7m : ldv .ld Mt1 (s.toNat - 1088 + 1016) = rv 23
  argcm : ldv .ld Mt1 (s.toNat - 1088) = BitVec.ofNat 64 argc
  depth : imgLE (imgM Mt1) (inp.toNat + 8) 4 = dep + 1
  args : ∀ a, InExt (argsBase s, 24 * argc) a → imgM Mt1 a = imgM Mt a

structure CloAr (R1 : Nat → BitVec 64) (Mt1 Mt : Mem) (s aX sret inp ret q line : BitVec 64)
    (rv : Nat → BitVec 64) (argc dep : Nat) : Prop where
  sp : R1 2 = s + 18446744073709550528#64
  s0 : R1 8 = aX
  s1 : R1 9 = sret
  s2 : R1 18 = inp
  s5 : R1 21 = q
  s7 : R1 23 = line
  a5 : R1 15 = BitVec.ofNat 64 argc
  keep : ∀ x ∈ [19, 20, 22, 24, 25, 26, 27], R1 x = rv x
  saved : CallSaved Mt1 s ret (rv 8) (rv 9) (rv 18)
  s5m : ldv .ld Mt1 (s.toNat - 1088 + 1032) = rv 21
  s7m : ldv .ld Mt1 (s.toNat - 1088 + 1016) = rv 23
  depth : imgLE (imgM Mt1) (inp.toNat + 8) 4 = dep
  args : ∀ a, InExt (argsBase s, 24 * argc) a → imgM Mt1 a = imgM Mt a

structure CloDp (R1 : Nat → BitVec 64) (Mt1 : Mem) (s aX sret inp ret line : BitVec 64)
    (rv : Nat → BitVec 64) (dep : Nat) : Prop where
  sp : R1 2 = s + 18446744073709550528#64
  s0 : R1 8 = aX
  s1 : R1 9 = sret
  s2 : R1 18 = inp
  a1 : R1 11 = line
  s7 : R1 23 = line
  keep : ∀ x ∈ [20, 22, 24, 25, 26, 27], R1 x = rv x
  saved : CallSaved Mt1 s ret (rv 8) (rv 9) (rv 18)
  s3m : ldv .ld Mt1 (s.toNat - 1088 + 1048) = rv 19
  s5m : ldv .ld Mt1 (s.toNat - 1088 + 1032) = rv 21
  s7m : ldv .ld Mt1 (s.toNat - 1088 + 1016) = rv 23
  depth : imgLE (imgM Mt1) (inp.toNat + 8) 4 = dep + 1

section Exits

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]
variable (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF)

def CloHeadK (cd : ClosureData) (Mt : Mem) (s aX sret inp ret e q : BitVec 64)
    (rv : Nat → BitVec 64) (argc dep : Nat) : IProp GF :=
  iprop((∀ (R1 : Nat → BitVec 64) (Mt1 : Mem) (line : BitVec 64),
      ⌜cd.params.length = argc ∧ dep + 1 ≤ maxCallDepth ∧
        CloHd R1 Mt1 Mt s aX sret inp ret e q line rv argc dep⌝ -∗
      ms 0x800032bc#64 R1 (cloS s inp) Mt1 -∗ Wp.W Φ) ∧
    (∀ (R1 : Nat → BitVec 64) (Mt1 : Mem) (line : BitVec 64),
      ⌜cd.params.length ≠ argc ∧ CloAr R1 Mt1 Mt s aX sret inp ret q line rv argc dep⌝ -∗
      ms 0x80003d60#64 R1 (cloS s inp) Mt1 -∗ Wp.W Φ) ∧
    (∀ (R1 : Nat → BitVec 64) (Mt1 : Mem) (line : BitVec 64),
      ⌜maxCallDepth < dep + 1 ∧ CloDp R1 Mt1 s aX sret inp ret line rv dep⌝ -∗
      ms 0x80003ca4#64 R1 (cloS s inp) Mt1 -∗ Wp.W Φ))

end Exits

end VsaIris.Interp
