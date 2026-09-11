import Vsa.Sim.ValueEqualSpec4
import Vsa.Sim.MemPresence

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine Vsa.While Vsa.Sim.Code

namespace Vsa.Sim

/-- String operands and read geometry for the equality helper's actual memory. -/
structure ValueEqualStringDataAt (bufa bufb sp : BitVec 64) (sa sb : String)
    (m : Mem) (pa pb : Nat) (csa csb : List Char) : Prop where
  leftPointer : read64 m (bufa.toNat + 8) = some pa
  rightPointer : read64 m (bufb.toNat + 8) = some pb
  leftString : CStr m pa csa
  rightString : CStr m pb csb
  leftValue : sa = String.ofList csa
  rightValue : sb = String.ofList csb
  leftRegion : StrcmpWSlack (BitVec.ofNat 64 pa) csa.length
  rightRegion : StrcmpWSlack (BitVec.ofNat 64 pb) csb.length
  stack : VEStrRegions sp pa pb csa.length csb.length

/-- Select both payloads and their geometry together at the call memory. -/
structure ValueEqualStringData (bufa bufb sp : BitVec 64) (sa sb : String)
    (m : Mem) : Prop where
  selected : ∃ pa pb csa csb, ValueEqualStringDataAt bufa bufb sp sa sb m pa pb csa csb

/-- Equality returns its computed result and preserves existing memory keys. -/
structure ValueEqualPostPresent
    (g : (R : Register) → Option (RegisterType R)) (r sp : BitVec 64)
    (va vb : Value) (m0 : Mem) (o : Array String) (c : Config) : Prop where
  post : ve_str_post g r sp va vb m0 o c
  presence : MemExtends m0 c.σ.mem

/-- The string handler retains its actual spill through the comparison call. -/
theorem ve_str_handler_memory
    (g : (R : Register) → Option (RegisterType R)) (bufa bufb r sp : BitVec 64)
    (sa sb : String) (pa' pb' : Nat) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) (σ : MState) (i : Nat) (steps0 : Nat)
    (hsteps0 : Steps c ⟨σ, i, steps0⟩) (hi : i < 2)
    (hG : GoodState σ) (hmem : σ.mem = m0) (hout : σ.sailOutput = o) (hloaded : Value_equalLoaded m0)
    (hstrc : StrcmpLoaded m0) (hmask : MaskPinned m0)
    (hpc : σ.regs.get? Register.PC = some (0x800028c4#64 : BitVec 64))
    (ha0 : σ.regs.get? Register.x10 = some bufa) (ha1 : σ.regs.get? Register.x11 = some bufb)
    (hra : σ.regs.get? Register.x1 = some r) (hsp : σ.regs.get? Register.x2 = some sp)
    (vmi : BitVec 64) (hmi : σ.regs.get? Register.minstret = some vmi)
    (hrega : VERegion bufa) (hregb : VERegion bufb)
    (hralign : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0)
    (hraln4 : r.toNat % 4 = 0)
    (hframe : ∀ R : Register, NotWrittenVE R → σ.regs.get? R = g R)
    (hpa : read64 m0 (bufa.toNat + 8) = some pa') (hpb : read64 m0 (bufb.toNat + 8) = some pb')
    (hca : CStr m0 pa' csa) (hcb : CStr m0 pb' csb)
    (hsa : sa = String.ofList csa) (hsb : sb = String.ofList csb)
    (hbra : StrcmpRegion (BitVec.ofNat 64 pa') csa.length)
    (hbrb : StrcmpRegion (BitVec.ofNat 64 pb') csb.length)
    (hwra : StrcmpWSlack (BitVec.ofNat 64 pa') csa.length)
    (hwrb : StrcmpWSlack (BitVec.ofNat 64 pb') csb.length)
    (hSR : VEStrRegions sp pa' pb' csa.length csb.length) :
    ∃ c', Steps c c' ∧ VeStrPostMemory g r sp (.str sa) (.str sb) m0
      (writeMap8 m0 ((sp - 16#64).toNat + 8) (sdData_val r)) o c' := by
  -- the str frame at the handler entry (`NotWrittenVEStr ⊆ NotWrittenVE`)
  have hframestr : ∀ R : Register, NotWrittenVEStr R → σ.regs.get? R = g R :=
    fun R hR => hframe R (notWrittenVE_of_str hR)
  -- run through the strcmp call to `0x800028d8`
  obtain ⟨c6, m1, x, hs6, hG6, htick6, hpc6, hra6, hx10_6, hbridge, hsp6, hmem6, hout6, _hmemframe6,
    hframeStr6, hm1def, hloaded1⟩ :=
    ve_str_reaches_result_cond g bufa bufb r sp sa sb pa' pb' csa csb m0 o c σ i steps0
      hsteps0 hi hG hmem hout hloaded hstrc hmask hpc ha0 ha1 hra hsp vmi hmi hrega hregb hraln4
      hframe hpa hpb hca hcb hsa hsb hbra hbrb hwra hwrb hSR
  -- run the epilogue (minstret at c6 comes from `GoodState`)
  obtain ⟨vmi6, hmi6⟩ := hG6.minstret
  obtain ⟨c', hs', hpost'⟩ :=
    ve_str_epilogue_memory g r sp x (.str sa) (.str sb) m0 m1 o c6 htick6 hG6 hloaded1 hmem6 hout6
      hpc6 hra6 hx10_6 hsp6 vmi6 hmi6 hframeStr6 hbridge
      hSR.sp16 hSR.win_lo hSR.win_hi hSR.win_htif hSR.win_align hralign (by decide) (by decide)
      hm1def
  exact ⟨c', hs6.trans hs', hm1def ▸ hpost'⟩


/-- String equality accepts either pointer alignment and retains the exact final memory. -/
theorem value_equal_spec_str_memory
    (g : (R : Register) → Option (RegisterType R)) (bufa bufb r sp : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (sa sb : String)
    (pa' pb' : Nat) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config)
    (hpre : ve_pre g bufa bufb r N φc (.str sa) (.str sb) m0 o c)
    (hsp : c.σ.regs.get? Register.x2 = some sp)
    (hstrc : StrcmpLoaded m0) (hmask : MaskPinned m0)
    (hraln4 : r.toNat % 4 = 0)
    -- the two string payloads (matching `ValueRepr .str`)
    (hpa : read64 m0 (bufa.toNat + 8) = some pa') (hpb : read64 m0 (bufb.toNat + 8) = some pb')
    (hca : CStr m0 pa' csa) (hcb : CStr m0 pb' csb)
    (hsa : sa = String.ofList csa) (hsb : sb = String.ofList csb)
    (hbra : StrcmpRegion (BitVec.ofNat 64 pa') csa.length)
    (hbrb : StrcmpRegion (BitVec.ofNat 64 pb') csb.length)
    (hwra : StrcmpWSlack (BitVec.ofNat 64 pa') csa.length)
    (hwrb : StrcmpWSlack (BitVec.ofNat 64 pb') csb.length)
    (hSR : VEStrRegions sp pa' pb' csa.length csb.length) :
    ∃ c', Steps c c' ∧ VeStrPostMemory g r sp (.str sa) (.str sb) m0
      (writeMap8 m0 ((sp - 16#64).toNat + 8) (sdData_val r)) o c' := by
  obtain ⟨hG, hloaded, hjt, hmem, hout, hpc, ha0, ha1, hra, ⟨vmi, hmi⟩, htick,
    hra', hrb', hrega, hregb, hrettgt, hframe⟩ := hpre
  -- dispatch to the handler at `0x800028c4` (`handlerAddr (.str _)`)
  obtain ⟨σd, idd, hstepsd, hidd, hGd, hmemd, houtd, hpcd, ha0d, ha1d, hrad, ⟨vmid, hmid⟩, hframed⟩ :=
    ve_to_handler g bufa bufb r N φc (.str sa) (.str sb) m0 o c rfl hG hloaded hjt
      hmem hout hpc ha0 ha1 hra vmi hmi htick hra' hrb' hrega hregb hframe
  rw [show handlerAddr (Value.str sa) = 0x800028c4#64 from rfl] at hpcd
  -- `x2 = sp` survives the dispatch (`x2 ∈ NotWrittenVE`, tied to `g`)
  have hspd : σd.regs.get? Register.x2 = some sp := by
    rw [hframed Register.x2 (by decide)]
    have := hframe Register.x2 (by decide); rw [hsp] at this; exact this.symm
  -- run the handler from `0x800028c4`
  exact ve_str_handler_memory g bufa bufb r sp sa sb pa' pb' csa csb m0 o c σd idd
    (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) hstepsd hidd hGd hmemd houtd (hmem ▸ hloaded)
    hstrc hmask hpcd ha0d ha1d hrad hspd vmid hmid hrega hregb hrettgt hraln4 hframed
    hpa hpb hca hcb hsa hsb hbra hbrb hwra hwrb hSR


/-- Execute equality with operand-local identity and retain memory presence. -/
theorem value_equal_spec_present
    (g : (R : Register) → Option (RegisterType R)) (bufa bufb r sp : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (va vb : Value)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config)
    (hIdentity : ValueEqualityIdentity N φc va vb)
    (hpre : ve_pre g bufa bufb r N φc va vb m0 o c)
    (hsp : c.σ.regs.get? Register.x2 = some sp)
    (hstrc : StrcmpLoaded m0) (hmask : MaskPinned m0) (hraln4 : r.toNat % 4 = 0)
    (hstrwit : ∀ sa sb, va = .str sa → vb = .str sb →
      ValueEqualStringData bufa bufb sp sa sb m0) :
    ∃ c', Steps c c' ∧ ValueEqualPostPresent g r sp va vb m0 o c' := by
  by_cases hstr : ∃ sa sb, va = .str sa ∧ vb = .str sb
  · obtain ⟨sa, sb, hva, hvb⟩ := hstr
    subst hva; subst hvb
    obtain ⟨pa', pb', csa, csb, data⟩ := (hstrwit sa sb rfl rfl).selected
    obtain ⟨after, steps, result⟩ := value_equal_spec_str_memory g bufa bufb r sp
      N φc sa sb pa' pb' csa csb m0 o c hpre hsp hstrc hmask hraln4
      data.leftPointer data.rightPointer data.leftString data.rightString
      data.leftValue data.rightValue data.leftRegion.toRegion data.rightRegion.toRegion
      data.leftRegion data.rightRegion data.stack
    exact ⟨after, steps, result.post, result.memory ▸ memExtends_writeMap8 m0 _ _⟩
  · -- non-`str`: use `value_equal_spec_nonstr`, weaken `mem = m0` to the window form
    have hnotstr : ∀ sa sb, ¬ (va = .str sa ∧ vb = .str sb) :=
      fun sa sb ⟨h1, h2⟩ => hstr ⟨sa, sb, h1, h2⟩
    -- `g x2 = sp` from the entry frame (`x2 ∈ NotWrittenVE`)
    have hgx2 : g Register.x2 = some sp := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hframe0⟩ := hpre
      have := hframe0 Register.x2 (by decide); rw [hsp] at this; exact this.symm
    obtain ⟨c', hs', hG', hpc', ha0', hra', ⟨w, hmi'⟩, htick', hmem', hout', hframe'⟩ :=
      value_equal_spec_nonstr_identity g bufa bufb r N φc va vb m0 o hIdentity hnotstr c hpre
    -- `x2` is untouched by the non-`str` handlers: `x2 = g x2 = sp`
    have hsp' : c'.σ.regs.get? Register.x2 = some sp := by
      rw [hframe' Register.x2 (by decide), hgx2]
    refine ⟨c', hs', ⟨hG', hpc', ha0', hra', hsp', ⟨w, hmi'⟩, htick', hout', ?_,
      fun R hR => hframe' R (notWrittenVE_of_str hR)⟩, ?_⟩
    · intro a _; rw [hmem']
    · rw [hmem']; exact MemExtends.refl m0

#print axioms ve_str_handler_memory
#print axioms value_equal_spec_str_memory
#print axioms value_equal_spec_present

end Vsa.Sim
