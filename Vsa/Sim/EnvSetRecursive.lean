import Vsa.Sim.EnvSetScanIter
import Vsa.Sim.EnvSetChain
import Vsa.Sim.StoreInvariant

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (Config Steps)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim
namespace EnvSetScan

/-- A semantic first match drives the actual `strcmp` loop to the update block.
The returned index is the semantic first-match index. -/
theorem scan_to_hit
    (g : (R : Register) → Option (RegisterType R))
    (env name valuePtr count pn scanRa sp : BitVec 64)
    (f : Vsa.While.Frame) (nameStr : String) (oldValue : Value)
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat) (m0 : Mem) (c : Config)
    (hSt : ScanSt g (0x80002d2c#64) env name valuePtr count pn scanRa sp 0
      f nameStr N φf φc m0 c)
    (hFirst : FirstMatch f.vars nameStr oldValue) :
    ∃ c' i, ∃ hi : i < f.vars.length,
      Steps c c' ∧ SetHitAt env valuePtr sp i f nameStr m0 c' ∧
      f.vars[i]'hi = (nameStr, oldValue) ∧ c'.σ.sailOutput = c.σ.sailOutput := by
  obtain ⟨iw, hiw, hpair, hbefore⟩ := hFirst.index
  have hPos : 0 < f.vars.length := Nat.lt_of_le_of_lt (Nat.zero_le iw) hiw
  obtain ⟨c1, hs1, hnext, hout1⟩ :=
    set_scan_iter_from_d2c g env name valuePtr count pn scanRa sp 0
      f nameStr N φf φc m0 c hSt (by intro j _ hj; omega) hPos
  obtain ⟨cHit, iHit, hsHit, hHit, houtHit⟩ :
      ∃ cHit iHit, Steps c cHit ∧ SetHitAt env valuePtr sp iHit f nameStr m0 cHit ∧
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
        set_scan_from_d28_to_hit env name valuePtr count pn sp f nameStr N φf φc m0
          iw hiw (by simpa using congrArg Prod.fst hpair) iw g1 1 c1
          hSt1 hmiss1 h1le (by omega)
      exact ⟨cHit, iHit, hs1.trans hs2, hHit, hout2.trans hout1⟩
    · exact ⟨c1, 0, hs1, hhit, hout1⟩
  have hiEq : iHit = iw := by
    have hnlt : ¬ iHit < iw := fun hlt =>
      (hbefore iHit hlt) (by simpa using hHit.hit)
    have hngt : ¬ iw < iHit := fun hgt =>
      (hHit.firstMatch iw hiw hgt) (by simpa using congrArg Prod.fst hpair)
    omega
  subst iHit
  exact ⟨cHit, iw, hiw, hsHit, hHit, hpair, houtHit⟩

/-- Continue at the loop test until a semantic full-frame miss reaches the
parent-load point. -/
theorem scan_from_test_to_miss
    (env name valuePtr count pn sp : BitVec 64)
    (f : Vsa.While.Frame) (nameStr : String)
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat) (m0 : Mem)
    (hMiss : FrameMiss f.vars nameStr) :
    ∀ fuel g i c,
      ScanSt g setScanTestPC env name valuePtr count pn (0x80002d38#64) sp i
        f nameStr N φf φc m0 c →
      (∀ j, (hj : j < f.vars.length) → j < i → f.vars[j].1 ≠ nameStr) →
      i ≤ f.vars.length → f.vars.length - i ≤ fuel →
      ∃ c' g', Steps c c' ∧
        ScanMissSt g' env name valuePtr count pn (0x80002d38#64) sp
          f nameStr N φf φc m0 c' ∧
        c'.σ.sailOutput = c.σ.sailOutput := by
  intro fuel
  induction fuel with
  | zero =>
      intro g i c hSt hbefore hle hfuel
      have hie : i = f.vars.length := by omega
      obtain ⟨c', hs, _hall, hMissSt, hout⟩ :=
        scan_head_exit g env name valuePtr count pn (0x80002d38#64) sp i
          f nameStr N φf φc m0 c hSt hbefore hie
          (by rw [← hSt.count_eq]; exact count.isLt)
      exact ⟨c', g, hs, hMissSt, hout⟩
  | succ fuel ih =>
      intro g i c hSt hbefore hle hfuel
      by_cases hie : i = f.vars.length
      · obtain ⟨c', hs, _hall, hMissSt, hout⟩ :=
          scan_head_exit g env name valuePtr count pn (0x80002d38#64) sp i
            f nameStr N φf φc m0 c hSt hbefore hie
            (by rw [← hSt.count_eq]; exact count.isLt)
        exact ⟨c', g, hs, hMissSt, hout⟩
      · have hilt : i < f.vars.length := by omega
        obtain ⟨c1, hs1, hnext, hout1⟩ :=
          set_scan_iter_hit g env name valuePtr count pn (0x80002d38#64) sp i
            f nameStr N φf φc m0 c hSt hbefore hilt rfl
        rcases hnext with hnext | hhit
        · obtain ⟨g1, hSt1, hbefore1⟩ := hnext
          obtain ⟨c', g', hs2, hMissSt, hout2⟩ :=
            ih g1 (i + 1) c1 hSt1 hbefore1 (by omega) (by omega)
          exact ⟨c', g', hs1.trans hs2, hMissSt, hout2.trans hout1⟩
        · exact (hMiss (f.vars[i]) (List.getElem_mem hhit.ilt) hhit.hit).elim

/-- A semantic full-frame miss drives the actual `strcmp` loop to `d90`. -/
theorem scan_to_miss
    (g : (R : Register) → Option (RegisterType R))
    (env name valuePtr count pn scanRa sp : BitVec 64)
    (f : Vsa.While.Frame) (nameStr : String)
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat) (m0 : Mem) (c : Config)
    (hSt : ScanSt g (0x80002d2c#64) env name valuePtr count pn scanRa sp 0
      f nameStr N φf φc m0 c)
    (hPos : 0 < f.vars.length)
    (hMiss : FrameMiss f.vars nameStr) :
    ∃ c' g', Steps c c' ∧
      ScanMissSt g' env name valuePtr count pn (0x80002d38#64) sp
        f nameStr N φf φc m0 c' ∧
      c'.σ.sailOutput = c.σ.sailOutput := by
  obtain ⟨c1, hs1, hnext, hout1⟩ :=
    set_scan_iter_from_d2c g env name valuePtr count pn scanRa sp 0
      f nameStr N φf φc m0 c hSt (by intro j _ hj; omega) hPos
  rcases hnext with hnext | hhit
  · obtain ⟨g1, hSt1, hbefore⟩ := hnext
    obtain ⟨c2, g2, hs2, hMissSt, hout2⟩ :=
      scan_from_test_to_miss env name valuePtr count pn sp f nameStr N φf φc m0
        hMiss f.vars.length g1 1 c1 hSt1 hbefore (by omega) (by omega)
    exact ⟨c2, g2, hs1.trans hs2, hMissSt, hout2.trans hout1⟩
  · exact (hMiss (f.vars[0]) (List.getElem_mem hhit.ilt) hhit.hit).elim

/-- Convert the scan-local carrier to the chain carrier without losing output. -/
theorem scanMiss_to_chain
    {g : (R : Register) → Option (RegisterType R)}
    {env name valuePtr count pn r sp : BitVec 64}
    {f : Vsa.While.Frame} {nameStr : String} {N : NativeAddrs}
    {φf φc : Vsa.While.Addr → Nat} {out0 : Array String} {m0 : Mem} {c : Config}
    (h : ScanMissSt g env name valuePtr count pn r sp f nameStr N φf φc m0 c)
    (hout : c.σ.sailOutput = out0) (hMiss : FrameMiss f.vars nameStr) :
    Vsa.Sim.SetScanMissSt g env name valuePtr count pn r sp
      f nameStr N φf φc out0 m0 c := by
  let hnames : Vsa.Sim.ScanNames m0 pn.toNat name nameStr f :=
    { maskPinned := h.names.maskPinned, nameCStr := h.names.nameCStr,
      nameRegB := h.names.nameRegB, nameRegW := h.names.nameRegW,
      bindPtr := h.names.bindPtr, bindRegB := h.names.bindRegB,
      bindRegW := h.names.bindRegW, slotLo := h.names.slotLo,
      slotHi := h.names.slotHi, slotHtif := h.names.slotHtif,
      slotAlign := h.names.slotAlign }
  refine
    { good := h.good
      loadedSet := h.loadedG
      loadedStrcmp := h.loadedS
      mem := h.mem
      pc := h.pc
      env4 := h.env4
      name3 := h.name3
      value5 := h.out5
      count2 := h.count2
      ra := h.ra
      sp2 := h.sp2
      minstret := h.minstret
      tick := h.tick
      output := hout
      frame := h.frame
      names := hnames
      count_eq := h.count_eq
      frame_miss := hMiss
      ghost := h.ghost }

#print axioms scan_to_hit
#print axioms scan_to_miss
#print axioms scanMiss_to_chain

end EnvSetScan
end Vsa.Sim
