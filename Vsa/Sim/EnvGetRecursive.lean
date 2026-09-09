import Vsa.Sim.EnvGetChain
import Vsa.Sim.EnvGetPrologueHead
import Vsa.Sim.EnvGetSpec8
import Vsa.Sim.StoreInvariant

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- Geometry needed only after a successful name scan.  These are concrete
readability and separation facts; no lookup result is assumed here. -/
structure EnvGetHitGeom
    (env out sp ret r8 r9 r18 r19 r20 r21 : BitVec 64) (i : Nat)
    (f : Vsa.While.Frame) (m0 : Mem) (pv w0 w1 w2 : Nat) : Prop where
  pv_eq : read64 m0 (env.toNat + 16) = some pv
  srcW0 : read64 m0 (pv + 24 * i) = some w0
  srcW1 : read64 m0 (pv + 24 * i + 8) = some w1
  srcW2 : read64 m0 (pv + 24 * i + 16) = some w2
  envLo : 0x80000000 ≤ env.toNat + 16
  envHi : env.toNat + 24 ≤ 0x100000000
  envWin : env.toNat + 24 ≤ tohostAddr ∨ tohostAddr + 8 ≤ env.toNat + 16
  envAlign : (env.toNat + 16) % 8 = 0
  envNoWrap : env.toNat + 24 < 2^64
  outLo : 0x80000000 ≤ out.toNat
  outHi : out.toNat + 24 ≤ 0x100000000
  outWin : tohostAddr + 16 ≤ out.toNat
  outAlign : out.toNat % 8 = 0
  outCode : out.toNat + 24 ≤ 0x80002c10 ∨ 0x80002cdc ≤ out.toNat
  slotRa : read64 m0 (sp.toNat + 56) = some ret.toNat
  slotS0 : read64 m0 (sp.toNat + 48) = some r8.toNat
  slotS1 : read64 m0 (sp.toNat + 40) = some r9.toNat
  slotS2 : read64 m0 (sp.toNat + 32) = some r18.toNat
  slotS3 : read64 m0 (sp.toNat + 24) = some r19.toNat
  slotS4 : read64 m0 (sp.toNat + 16) = some r20.toNat
  slotS5 : read64 m0 (sp.toNat + 8) = some r21.toNat
  spLo : 0x80000000 ≤ sp.toNat + 8
  spHi : sp.toNat + 64 ≤ 0x100000000
  spWin : tohostAddr + 16 ≤ sp.toNat + 8
  spAlign : sp.toNat % 8 = 0
  spNoWrap : sp.toNat + 64 < 2^64
  srcLo : 0x80000000 ≤ pv + 24 * i
  srcHi : pv + 24 * i + 24 ≤ 0x100000000
  srcWin : tohostAddr + 16 ≤ pv + 24 * i
  srcAlign : (pv + 24 * i) % 8 = 0
  srcNoWrap : pv + 24 * i + 24 < 2^64
  pvNoWrap : pv + 24 * i < 2^64
  src_out_disjoint : pv + 24 * i + 24 ≤ out.toNat ∨ out.toNat + 24 ≤ pv + 24 * i
  out_spill_disjoint : out.toNat + 24 ≤ sp.toNat + 8 ∨ sp.toNat + 64 ≤ out.toNat
  payDisj : ∀ (hi : i < f.vars.length) (p : Nat) (s : String),
    read64 m0 (pv + 24 * i + 8) = some p →
    ValuePayload (f.vars[i]'hi).2 s → ∀ k, k ≤ s.length → p + k < out.toNat ∨ out.toNat + 24 ≤ p + k
  retAlign : ret.toNat % 4 = 0
  indexSmall : i < 2^32

/-- Exact successful return of `env_get`, starting after its prologue. -/
structure EnvGetValuePost
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat)
    (out sp ret r8 r9 r18 r19 r20 r21 : BitVec 64)
    (out0 : Array String) (v : Value) (m0 : Mem) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some ret
  found : c.σ.regs.get? Register.x10 = some (1#64 : BitVec 64)
  ra : c.σ.regs.get? Register.x1 = some ret
  sp : c.σ.regs.get? Register.x2 = some (sp + 64#64)
  s0 : c.σ.regs.get? Register.x8 = some r8
  s1 : c.σ.regs.get? Register.x9 = some r9
  s2 : c.σ.regs.get? Register.x18 = some r18
  s3 : c.σ.regs.get? Register.x19 = some r19
  s4 : c.σ.regs.get? Register.x20 = some r20
  s5 : c.σ.regs.get? Register.x21 = some r21
  output : c.σ.sailOutput = out0
  mem : ∃ m' w0 w1 w2, c.σ.mem = m' ∧ Env_getLoaded m' ∧
    ValueRepr m' N φc out.toNat v ∧
    read64 m' out.toNat = some w0 ∧
    read64 m' (out.toNat + 8) = some w1 ∧
    read64 m' (out.toNat + 16) = some w2 ∧
    ∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 24) → m'[a]? = m0[a]?

theorem EnvGetValuePost.output_trans
    {N : NativeAddrs} {φc : Vsa.While.Addr → Nat}
    {out sp ret r8 r9 r18 r19 r20 r21 : BitVec 64}
    {out0 out1 : Array String} {v : Value} {m0 : Mem} {c : Config}
    (h : EnvGetValuePost N φc out sp ret r8 r9 r18 r19 r20 r21 out0 v m0 c)
    (heq : out0 = out1) :
    EnvGetValuePost N φc out sp ret r8 r9 r18 r19 r20 r21 out1 v m0 c :=
  { good := h.good, tick := h.tick, pc := h.pc, found := h.found, ra := h.ra,
    sp := h.sp, s0 := h.s0, s1 := h.s1, s2 := h.s2, s3 := h.s3,
    s4 := h.s4, s5 := h.s5, output := h.output.trans heq, mem := h.mem }

/-- A semantic first match drives the actual strcmp scan and the actual
twenty-one-instruction copy/restore tail. -/
theorem env_get_scan_to_value
    (g : (R : Register) → Option (RegisterType R))
    (env name out count pn scanRa sp ret r8 r9 r18 r19 r20 r21 : BitVec 64)
    (f : Vsa.While.Frame) (nameStr : String) (v : Value)
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat) (m0 : Mem) (c : Config)
    (hSt : ScanSt g (0x80002c60#64) env name out count pn scanRa sp 0
      f nameStr N φf φc m0 c)
    (hFirst : FirstMatch f.vars nameStr v)
    (hGeom : ∀ i, (hi : i < f.vars.length) → f.vars[i] = (nameStr, v) →
      ∃ pv w0 w1 w2,
        EnvGetHitGeom env out sp ret r8 r9 r18 r19 r20 r21 i f m0 pv w0 w1 w2) :
    ∃ c', Steps c c' ∧
      EnvGetValuePost N φc out sp ret r8 r9 r18 r19 r20 r21 c.σ.sailOutput v m0 c' := by
  obtain ⟨iw, hiw, hpair, hbefore⟩ := hFirst.index
  have h0lt : 0 < f.vars.length := Nat.lt_of_le_of_lt (Nat.zero_le iw) hiw
  obtain ⟨c1, hs1, hnext, hout1⟩ :=
    scan_iter_from_c60 g env name out count pn scanRa sp 0 f nameStr N φf φc m0 c
      hSt (by intro j _ hj; omega) h0lt
  obtain ⟨cHit, iHit, hsHit, hHit, houtHit⟩ :
      ∃ cHit iHit, Steps c cHit ∧ HitAt env out sp iHit f nameStr m0 cHit ∧
        cHit.σ.sailOutput = c.σ.sailOutput := by
    rcases hnext with hnext | hhit
    · obtain ⟨g1, hSt1, hmiss1⟩ := hnext
      have h1le : 1 ≤ iw := by
        cases iw with
        | zero =>
          have heq : f.vars[0].1 = nameStr := by
            simpa using congrArg Prod.fst hpair
          exact (hmiss1 0 hiw (by omega) heq).elim
        | succ iw => omega
      obtain ⟨cHit, iHit, hs2, hHit, hout2⟩ :=
        scan_from_c5c_to_hit env name out count pn sp f nameStr N φf φc m0
          iw hiw (by simpa using congrArg Prod.fst hpair) iw g1 1 c1 hSt1 hmiss1 h1le (by omega)
      exact ⟨cHit, iHit, hs1.trans hs2, hHit, hout2.trans hout1⟩
    · exact ⟨c1, 0, hs1, hhit, hout1⟩
  have hiEq : iHit = iw := by
    have hnlt : ¬ iHit < iw := fun hlt =>
      (hbefore iHit hlt) (by simpa using hHit.hit)
    have hngt : ¬ iw < iHit := fun hgt =>
      (hHit.firstMatch iw hiw hgt) (by simpa using congrArg Prod.fst hpair)
    omega
  subst iHit
  obtain ⟨pv, w0, w1, w2, hG⟩ := hGeom iw hiw hpair
  let hTail : HitTailSt (cHit.σ.regs.get?) env out sp ret ret r8 r9 r18 r19 r20 r21
      iw pv w0 w1 w2 f N φf φc m0 cHit :=
    { good := hHit.good, loadedG := by rw [hHit.mem]; exact hSt.mem ▸ hSt.loadedG,
      mem := hHit.mem, pc := hHit.pc, env4 := hHit.env4, idx0 := hHit.idx0,
      out5 := hHit.out5, sp2 := hHit.sp2, minstret := hHit.minstret, tick := hHit.tick,
      frame := hSt.frame, ilt := hiw, ismall := hG.indexSmall, pv_eq := hG.pv_eq,
      srcW0 := hG.srcW0, srcW1 := hG.srcW1, srcW2 := hG.srcW2,
      envLo := hG.envLo, envHi := hG.envHi, envWin := hG.envWin,
      envAlign := hG.envAlign, envNoWrap := hG.envNoWrap,
      outLo := hG.outLo, outHi := hG.outHi, outWin := hG.outWin,
      outAlign := hG.outAlign, outCode := hG.outCode,
      slotRa := hG.slotRa, slotS0 := hG.slotS0, slotS1 := hG.slotS1,
      slotS2 := hG.slotS2, slotS3 := hG.slotS3, slotS4 := hG.slotS4,
      slotS5 := hG.slotS5, rr_eq := rfl,
      spLo := hG.spLo, spHi := hG.spHi, spWin := hG.spWin,
      spAlign := hG.spAlign, spNoWrap := hG.spNoWrap,
      srcLo := hG.srcLo, srcHi := hG.srcHi, srcWin := hG.srcWin,
      srcAlign := hG.srcAlign, srcNoWrap := hG.srcNoWrap, pvNoWrap := hG.pvNoWrap,
      src_out_disjoint := hG.src_out_disjoint,
      out_spill_disjoint := hG.out_spill_disjoint, payDisj := hG.payDisj hiw,
      rAlign := hG.retAlign }
  obtain ⟨c', m', hsTail, hGood, hTick, hpc, hfound, hra, hsp, hs0, hs1r,
    hs2r, hs3r, hs4r, hs5r, hmem, hloaded, hvalue, hw0, hw1, hw2, hframe, houtTail⟩ :=
    env_get_hit_tail (cHit.σ.regs.get?) env out sp ret ret r8 r9 r18 r19 r20 r21
      iw pv w0 w1 w2 f N φf φc m0 cHit hiw hTail
  refine ⟨c', hsHit.trans hsTail,
    { good := hGood, tick := hTick, pc := hpc, found := hfound, ra := hra, sp := hsp,
      s0 := hs0, s1 := hs1r, s2 := hs2r, s3 := hs3r, s4 := hs4r, s5 := hs5r,
      output := houtTail.trans houtHit,
      mem := ⟨m', w0, w1, w2, hmem, hloaded, ?_, hw0, hw1, hw2, hframe⟩ }⟩
  simpa [hpair] using hvalue

/-- Continue a concrete scan at the test point until the semantic full-frame
miss reaches the parent-load point.  This direct induction retains output;
the older generic loop triple intentionally did not expose that frame. -/
theorem env_get_scan_from_test_to_miss
    (env name out count pn sp : BitVec 64)
    (f : Vsa.While.Frame) (nameStr : String)
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat) (m0 : Mem)
    (hMiss : FrameMiss f.vars nameStr) :
    ∀ fuel g i c,
      ScanSt g scanTestPC env name out count pn (0x80002c6c#64) sp i
        f nameStr N φf φc m0 c →
      (∀ j, (hj : j < f.vars.length) → j < i → f.vars[j].1 ≠ nameStr) →
      i ≤ f.vars.length → f.vars.length - i ≤ fuel →
      ∃ c' g', Steps c c' ∧
        ScanMissSt g' env name out count pn (0x80002c6c#64) sp
          f nameStr N φf φc m0 c' ∧
        c'.σ.sailOutput = c.σ.sailOutput := by
  intro fuel
  induction fuel with
  | zero =>
      intro g i c hSt hbefore hle hfuel
      have hie : i = f.vars.length := by omega
      obtain ⟨c', hs, _hall, hMissSt, hout⟩ :=
        scan_head_exit g env name out count pn (0x80002c6c#64) sp i
          f nameStr N φf φc m0 c hSt hbefore hie
          (by rw [← hSt.count_eq]; exact count.isLt)
      exact ⟨c', g, hs, hMissSt, hout⟩
  | succ fuel ih =>
      intro g i c hSt hbefore hle hfuel
      by_cases hie : i = f.vars.length
      · obtain ⟨c', hs, _hall, hMissSt, hout⟩ :=
          scan_head_exit g env name out count pn (0x80002c6c#64) sp i
            f nameStr N φf φc m0 c hSt hbefore hie
            (by rw [← hSt.count_eq]; exact count.isLt)
        exact ⟨c', g, hs, hMissSt, hout⟩
      · have hilt : i < f.vars.length := by omega
        obtain ⟨c1, hs1, hnext, hout1⟩ :=
          scan_iter_hit g env name out count pn (0x80002c6c#64) sp i
            f nameStr N φf φc m0 c hSt hbefore hilt rfl
        rcases hnext with hnext | hhit
        · obtain ⟨g1, hSt1, hbefore1⟩ := hnext
          obtain ⟨c', g', hs2, hMissSt, hout2⟩ :=
            ih g1 (i + 1) c1 hSt1 hbefore1 (by omega) (by omega)
          exact ⟨c', g', hs1.trans hs2, hMissSt, hout2.trans hout1⟩
        · exact (hMiss (f.vars[i]) (List.getElem_mem hhit.ilt) hhit.hit).elim

/-- A semantic full-frame miss drives the actual strcmp loop to its concrete
parent-load program point. -/
theorem env_get_scan_to_miss
    (g : (R : Register) → Option (RegisterType R))
    (env name out count pn scanRa sp : BitVec 64)
    (f : Vsa.While.Frame) (nameStr : String)
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat) (m0 : Mem) (c : Config)
    (hSt : ScanSt g (0x80002c60#64) env name out count pn scanRa sp 0
      f nameStr N φf φc m0 c)
    (hPos : 0 < f.vars.length)
    (hMiss : FrameMiss f.vars nameStr) :
    ∃ c' g', Steps c c' ∧
      ScanMissSt g' env name out count pn (0x80002c6c#64) sp
        f nameStr N φf φc m0 c' ∧
      c'.σ.sailOutput = c.σ.sailOutput := by
  obtain ⟨c1, hs1, hnext, hout1⟩ :=
    scan_iter_from_c60 g env name out count pn scanRa sp 0 f nameStr N φf φc m0 c
      hSt (by intro j _ hj; omega) hPos
  rcases hnext with hnext | hhit
  · obtain ⟨g1, hSt1, hbefore⟩ := hnext
    obtain ⟨c2, g2, hs2, hMissSt, hout2⟩ :=
      env_get_scan_from_test_to_miss env name out count pn sp f nameStr N φf φc m0
        hMiss f.vars.length g1 1 c1 hSt1 hbefore (by omega) (by omega)
    exact ⟨c2, g2, hs1.trans hs2, hMissSt, hout2.trans hout1⟩
  · exact (hMiss (f.vars[0]) (List.getElem_mem hhit.ilt) hhit.hit).elim

/-! ## Recursive parent-chain composition -/

/-- Concrete layout facts for one represented frame in a parent chain.  The
names pointer is explicit.  The successful-tail facts remain indexed by the
actual first-match slot and value. -/
structure EnvGetFrameFacts
    (name out sp ret r8 r9 r18 r19 r20 r21 : BitVec 64)
    (nameStr : String) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (a : Vsa.While.Addr) (f : Vsa.While.Frame) (pn : Nat) : Prop where
  addrSmall : φf a < 2^64
  addrLo : 0x80000000 ≤ φf a
  addrHi : φf a + 32 ≤ 0x100000000
  addrWin : tohostAddr + 8 ≤ φf a
  addrAlign : φf a % 8 = 0
  countSmall : f.vars.length < 2^31
  pnSmall : pn < 2^64
  pnRead : read64 m0 (φf a + 8) = some pn
  names : ScanNames m0 pn name nameStr f
  hit : ∀ i, (hi : i < f.vars.length) → ∀ value,
    f.vars[i] = (nameStr, value) →
    ∃ pv w0 w1 w2,
      EnvGetHitGeom (BitVec.ofNat 64 (φf a)) out sp ret r8 r9 r18 r19 r20 r21
        i f m0 pv w0 w1 w2

/-- Every semantic frame on the lookup path has a concrete machine layout. -/
def EnvGetChainFacts
    (name out sp ret r8 r9 r18 r19 r20 r21 : BitVec 64)
    (nameStr : String) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (m0 : Mem) (s : Store) : Prop :=
  ∀ a f, s.frames[a]? = some f →
    ∃ pn, EnvGetFrameFacts name out sp ret r8 r9 r18 r19 r20 r21
      nameStr N φf φc m0 a f pn

theorem LookupChain.headFrame {s : Store} {x : String} {gas : Nat} {a : Addr}
    {v : Value} (h : LookupChain s x gas a v) :
    ∃ f, s.frames[a]? = some f := by
  cases h with
  | hit hframe _ => exact ⟨_, hframe⟩
  | parent hframe _ _ _ => exact ⟨_, hframe⟩

/-- Starting at a verified parent-chain head (`c40`), a semantic lookup chain
drives the concrete machine through every missed frame and returns its exact
semantic value.  Parent descent uses the two decoded backedge instructions;
each nonempty frame uses the verified strcmp loop. -/
theorem env_get_lookup_from_parent_head
    (s : Store) (name out sp ret r8 r9 r18 r19 r20 r21 : BitVec 64)
    (nameStr : String) (N : NativeAddrs) (A : Arena)
    (φf φc : Vsa.While.Addr → Nat) (m0 : Mem)
    (hStore : StoreRepr m0 N A φf φc s)
    (hFacts : EnvGetChainFacts name out sp ret r8 r9 r18 r19 r20 r21
      nameStr N φf φc m0 s) :
    ∀ gas a v, LookupChain s nameStr gas a v →
      ∀ f, s.frames[a]? = some f → ∀ g c scanRa,
        ParentHeadSt g (BitVec.ofNat 64 (φf a)) name out scanRa sp a f
          N φf φc m0 c →
        ∃ c', Steps c c' ∧
          EnvGetValuePost N φc out sp ret r8 r9 r18 r19 r20 r21
            c.σ.sailOutput v m0 c' := by
  intro gas a v hChain
  induction hChain with
  | @hit gas a frame value hframe hFirst =>
      intro f hframe' g c scanRa hHead
      have hfeq : frame = f := by rw [hframe] at hframe'; exact Option.some.inj hframe'
      subst f
      obtain ⟨pn, hF⟩ := hFacts a frame hframe
      have hEnvNat : (BitVec.ofNat 64 (φf a)).toNat = φf a := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hF.addrSmall]
      obtain ⟨cScan, gScan, hsStart, hScan, houtStart⟩ :=
        env_get_parent_scan_start g (BitVec.ofNat 64 (φf a)) name out scanRa sp a frame
          nameStr pn N φf φc m0 c hHead hF.names
          (by simpa [hEnvNat] using hF.pnRead)
          (by obtain ⟨i, hi, _, _⟩ := hFirst.index; omega)
          hF.countSmall hF.pnSmall hF.addrSmall
          (by simpa [hEnvNat] using hF.addrLo)
          (by simpa [hEnvNat] using hF.addrHi)
          (by simpa [hEnvNat] using hF.addrWin)
          (by simpa [hEnvNat] using hF.addrAlign)
      obtain ⟨c', hsHit, hPost⟩ :=
        env_get_scan_to_value gScan (BitVec.ofNat 64 (φf a)) name out
          (BitVec.ofNat 64 frame.vars.length) (BitVec.ofNat 64 pn) scanRa sp
          ret r8 r9 r18 r19 r20 r21 frame nameStr value N φf φc m0 cScan
          hScan hFirst (by
            intro i hi hpair
            exact hF.hit i hi value hpair)
      exact ⟨c', hsStart.trans hsHit, hPost.output_trans houtStart⟩
  | @parent gas a frame parent value hframe hMiss hParent hTail ih =>
      intro f hframe' g c scanRa hHead
      have hfeq : frame = f := by rw [hframe] at hframe'; exact Option.some.inj hframe'
      subst f
      obtain ⟨pn, hF⟩ := hFacts a frame hframe
      have hEnvNat : (BitVec.ofNat 64 (φf a)).toNat = φf a := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hF.addrSmall]
      obtain ⟨parentFrame, hParentFrameGet⟩ := hTail.headFrame
      obtain ⟨hParentBound, hParentElem⟩ := Array.getElem?_eq_some_iff.mp hParentFrameGet
      have hParentRepr : FrameRepr m0 N φf φc (φf parent) parentFrame := by
        have h := hStore.frames parent hParentBound
        simpa only [hParentElem] using h
      obtain ⟨parentPn, hPF⟩ := hFacts parent parentFrame hParentFrameGet
      by_cases hEmpty : frame.vars.length = 0
      · obtain ⟨cMiss, gMiss, hsMiss, hMissSt, houtMiss⟩ :=
          env_get_parent_empty g (BitVec.ofNat 64 (φf a)) name out scanRa sp a frame
            nameStr pn N φf φc m0 c hHead hF.names hEmpty hF.pnSmall hF.addrSmall
            (by simpa [hEnvNat] using hF.addrLo)
            (by simpa [hEnvNat] using hF.addrHi)
            (by simpa [hEnvNat] using hF.addrWin)
            (by simpa [hEnvNat] using hF.addrAlign)
        obtain ⟨cParent, gParent, hsParent, hParentHead, houtParent⟩ :=
          env_get_parent_step gMiss (BitVec.ofNat 64 (φf a)) name out (0#64)
            (BitVec.ofNat 64 pn) scanRa sp frame parentFrame nameStr parent N φf φc m0
            cMiss hMissSt hParent hParentRepr
            (by simpa [hEnvNat] using hF.addrLo)
            (by simpa [hEnvNat] using hF.addrHi)
            (by right; simpa [hEnvNat] using hF.addrWin)
            (by simpa [hEnvNat] using hF.addrAlign) hPF.addrSmall
        obtain ⟨c', hsTail, hPost⟩ :=
          ih parentFrame hParentFrameGet gParent cParent scanRa hParentHead
        exact ⟨c', (hsMiss.trans hsParent).trans hsTail,
          hPost.output_trans (houtParent.trans houtMiss)⟩
      · have hPos : 0 < frame.vars.length := Nat.pos_of_ne_zero hEmpty
        obtain ⟨cScan, gScan, hsStart, hScan, houtStart⟩ :=
          env_get_parent_scan_start g (BitVec.ofNat 64 (φf a)) name out scanRa sp a frame
            nameStr pn N φf φc m0 c hHead hF.names
            (by simpa [hEnvNat] using hF.pnRead) hPos hF.countSmall hF.pnSmall
            hF.addrSmall
            (by simpa [hEnvNat] using hF.addrLo)
            (by simpa [hEnvNat] using hF.addrHi)
            (by simpa [hEnvNat] using hF.addrWin)
            (by simpa [hEnvNat] using hF.addrAlign)
        obtain ⟨cMiss, gMiss, hsScan, hMissSt, houtScan⟩ :=
          env_get_scan_to_miss gScan (BitVec.ofNat 64 (φf a)) name out
            (BitVec.ofNat 64 frame.vars.length) (BitVec.ofNat 64 pn) scanRa sp
            frame nameStr N φf φc m0 cScan hScan hPos hMiss
        obtain ⟨cParent, gParent, hsParent, hParentHead, houtParent⟩ :=
          env_get_parent_step gMiss (BitVec.ofNat 64 (φf a)) name out
            (BitVec.ofNat 64 frame.vars.length) (BitVec.ofNat 64 pn) (0x80002c6c#64) sp
            frame parentFrame nameStr parent N φf φc m0 cMiss hMissSt hParent
            hParentRepr
            (by simpa [hEnvNat] using hF.addrLo)
            (by simpa [hEnvNat] using hF.addrHi)
            (by right; simpa [hEnvNat] using hF.addrWin)
            (by simpa [hEnvNat] using hF.addrAlign) hPF.addrSmall
        obtain ⟨c', hsTail, hPost⟩ :=
          ih parentFrame hParentFrameGet gParent cParent (0x80002c6c#64) hParentHead
        exact ⟨c', ((hsStart.trans hsScan).trans hsParent).trans hsTail,
          hPost.output_trans (houtParent.trans (houtScan.trans houtStart))⟩

/-- Full env_get entry bridge.  The first twelve instructions are independent
of the root-frame count.  The semantic LookupChain then selects the zero or
nonzero root branch at c40 and drives every recursive parent frame. -/
theorem env_get_lookup_from_entry
    (s : Store) (a : Vsa.While.Addr) (v : Value)
    (name out sp0 r0 r8 r9 r18 r19 r20 r21 : BitVec 64)
    (nameStr : String) (N : NativeAddrs) (A : Arena)
    (φf φc : Vsa.While.Addr → Nat) (m0 : Mem) (c : Config)
    (len pn : Nat)
    (hChain : LookupChain s nameStr s.frames.size a v)
    (hEntry : PrologueHeadSt (BitVec.ofNat 64 (φf a)) name out sp0 r0
      r8 r9 r18 r19 r20 r21 len pn m0 c)
    (hStoreSurv : ∀ m',
      (∀ k, ¬ ((sp0 - 64#64).toNat ≤ k ∧
        k < (sp0 - 64#64).toNat + 64) → m'[k]? = m0[k]?) →
      StoreRepr m' N A φf φc s)
    (hFactsSurv : ∀ m',
      (∀ k, ¬ ((sp0 - 64#64).toNat ≤ k ∧
        k < (sp0 - 64#64).toNat + 64) → m'[k]? = m0[k]?) →
      EnvGetChainFacts name out (sp0 - 64#64) r0 r8 r9 r18 r19 r20 r21
        nameStr N φf φc m' s)
    (hStrcmpSurv : ∀ m',
      (∀ k, ¬ ((sp0 - 64#64).toNat ≤ k ∧
        k < (sp0 - 64#64).toNat + 64) → m'[k]? = m0[k]?) →
      StrcmpLoaded m') :
    ∃ c' m9, Steps c c' ∧
      EnvGetValuePost N φc out (sp0 - 64#64) r0 r8 r9 r18 r19 r20 r21
        c.σ.sailOutput v m9 c' ∧
      (∀ k, ¬ ((sp0 - 64#64).toNat ≤ k ∧
        k < (sp0 - 64#64).toNat + 64) → m9[k]? = m0[k]?) := by
  obtain ⟨c40, hsHead, hHead⟩ :=
    env_get_prologue_head (BitVec.ofNat 64 (φf a)) name out sp0 r0
      r8 r9 r18 r19 r20 r21 len pn m0 c hEntry
  obtain ⟨m9, hmem9, hcode9, hs56, hs48, hs40, hs32, hs24, hs16, hs8,
    houtside⟩ := hHead.mem
  have hStore9 : StoreRepr m9 N A φf φc s := hStoreSurv m9 houtside
  have hFacts9 := hFactsSurv m9 houtside
  obtain ⟨frame, hframeGet⟩ := hChain.headFrame
  obtain ⟨hbound, helem⟩ := Array.getElem?_eq_some_iff.mp hframeGet
  have hFrame9 : FrameRepr m9 N φf φc (φf a) frame := by
    have h := hStore9.frames a hbound
    simpa only [helem] using h
  have hAddrSmall : φf a < 2^64 := by
    obtain ⟨_, hF⟩ := hFacts9 a frame hframeGet
    exact hF.addrSmall
  have hParentHead : ParentHeadSt (fun R => c40.σ.regs.get? R)
      (BitVec.ofNat 64 (φf a)) name out r0 (sp0 - 64#64) a frame
      N φf φc m9 c40 :=
    { good := hHead.good, loadedG := by rw [hmem9]; exact hcode9,
      loadedS := by rw [hmem9]; exact hStrcmpSurv m9 houtside,
      mem := hmem9, pc := hHead.pc, env4 := hHead.env4, parent_eq := rfl,
      name3 := hHead.name3, out5 := hHead.out5, ra := hHead.ra,
      sp2 := hHead.sp, minstret := hHead.minstret, tick := hHead.tick,
      frame := hFrame9, ghost := fun _ _ => rfl }
  obtain ⟨c', hsTail, hPost⟩ :=
    env_get_lookup_from_parent_head s name out (sp0 - 64#64) r0
      r8 r9 r18 r19 r20 r21 nameStr N A φf φc m9 hStore9 hFacts9
      s.frames.size a v hChain frame hframeGet (fun R => c40.σ.regs.get? R)
      c40 r0 hParentHead
  exact ⟨c', m9, hsHead.trans hsTail, hPost.output_trans hHead.output, houtside⟩

#print axioms env_get_scan_to_value
#print axioms env_get_scan_to_miss
#print axioms env_get_lookup_from_parent_head
#print axioms env_get_lookup_from_entry

end Vsa.Sim
