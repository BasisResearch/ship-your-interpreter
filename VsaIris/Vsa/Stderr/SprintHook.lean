import VsaIris.Vsa.Stderr.SprintErr
import VsaIris.Vsa.Fprintf.Print

/-!
# `stderr`'s flush as `vfp_printH`'s hook (lane N3)

N5's `vfp_printH` takes the `__sprint_r(reent, f, sp + 224)` call as a hook.
On `stderr` with one staged piece `bs` it is `sprintErr_run` (nonempty) or
`__sprint_r`'s early return (empty: the residual is 0, `0x8000e8d4`): either
way the continuation gets `out = bs` and `SprintPost`.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio
open scoped VsaIris.Sym.Stdout

#ix_piece sprintErr0_01 {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) (t : String) (Mt : Mem) (R : Nat → BitVec 64)
    (s : BitVec 64) (need : Nat) (ra sp : BitVec 64)
    (hs1 : s.toNat - need + 256 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat)
    (hs3 : s.toNat ≤ 0x88000000) (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hra : ra.toNat % 4 = 0) (h1 : R 1 = ra) (h2 : R 2 = sp) (h12 : R 12 = sp + 224#64)
    (hres : ldv .ld Mt (sp + 240#64).toNat = 0#64)
    (hflU : ldv .lhu Mt 0x8001bbe8 = 0x201a#64) (hfl : ldv .lh Mt 0x8001bbe8 = 0x201a#64)
    (hfin : ∀ R' Mt', RetOK R R' 0#64 → SprintPost Mt Mt' sp →
      SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DA)) iRegs
      (outS s need) Q t ra R' Mt') :
    SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DA)) iRegs (outS s need) Q t
      0x8000e8cc#64 R Mt by
  nx_run hlive using [h1, h2, h12, hres, BitVec.add_assoc, BitVec.reduceAdd]
  refine hfin _ _ (retOK_of ?_ ?_) ⟨fun a ha1 ha2 ha3 ha4 => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · ret_keep
  · exact imgM_store_miss _ _ (by nx_fdisch)
  all_goals (nx_mem; try decide)
  all_goals first | exact hflU | exact hfl | exact hres

/-! **`sprintErr0_run`**: `__sprint_r` with a zero residual returns at once. -/
#ix_chain sprintErr0_run := [sprintErr0_01]

/-- **`stderr`'s flush, as `vfp_printH`'s hook**: one staged piece `bs`
(possibly empty) at `p` in the data view. -/
theorem sprintErr_hook {live : Nat → Prop} {Dt : Mem} {DA : List Nat}
    {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hlive : ∀ p ∈ stdioText, live p.1) {t : String} {Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64} {need : Nat} {sp p : BitVec 64} {bs : List (BitVec 8)}
    (hs1 : s.toNat - need + 256 ≤ sp.toNat) (hs2 : sp.toNat + 592 ≤ s.toNat)
    (hs3 : s.toNat ≤ 0x88000000) (hs4 : 0x80100000 ≤ s.toNat - need) (hal : sp.toNat % 16 = 0)
    (hk : bs.length < 2 ^ 30)
    (h1 : R 1 = 0x8000b8d4#64) (h2 : R 2 = sp) (h10 : R 10 = 0x8001b538#64)
    (h11 : R 11 = 0x8001bbd8#64) (h12 : R 12 = sp + 224#64)
    (hres : ldv .ld Mt (sp + 240#64).toNat = BitVec.ofNat 64 bs.length)
    (hiov : ldv .ld Mt (sp + 224#64).toNat = sp + 352#64)
    (hp : ldv .ld Mt (sp + 352#64).toNat = p) (hk0 : ldv .ld Mt (sp + 360#64).toNat = BitVec.ofNat 64 bs.length)
    (hp1 : 0x80000000 ≤ p.toNat) (hp2 : p.toNat + bs.length ≤ 0x100000000)
    (hp3 : p.toNat + bs.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ p.toNat)
    (hpd : ∀ i, i < bs.length → (p.toNat + i < sp.toNat - 256 ∨ sp.toNat ≤ p.toNat + i) ∧
      ¬ stdioFoot (p.toNat + i) ∧ (p.toNat + i < 0x8001ba08 ∨ 0x8001ba0c ≤ p.toNat + i))
    (hpsrc : ∀ i (h : i < bs.length), p.toNat + i ∈ DA ∧ imgM Dt (p.toNat + i) = bs[i])
    (hflU : ldv .lhu Mt 0x8001bbe8 = 0x201a#64) (hfl : ldv .lh Mt 0x8001bbe8 = 0x201a#64)
    (hfd : ldv .lh Mt 0x8001bbea = 2#64) (hbase : ldv .ld Mt 0x8001bbf0 = 0x8001bc4f#64)
    (hwr : ldv .ld Mt 0x8001bc18 = 0x8000efd4#64) (hck : ldv .ld Mt 0x8001bc08 = 0x8001bbd8#64)
    (hfin : ∀ R' M' out, RetOK R R' 0#64 → (out = bs ∧ SprintPost Mt M' sp) →
      SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DA)) iRegs
      (outS s need) Q (t ++ putcs out) 0x8000b8d4#64 R' M') :
    SWPO live (stdioText ++ dataOf Dt (accAddrs 0x8001b970 8 ++ DA)) iRegs (outS s need) Q t
      0x8000e8cc#64 R Mt := by
  by_cases hb : bs.length = 0
  · have e : bs = [] := List.eq_nil_of_length_eq_zero hb
    subst e
    refine sprintErr0_run hlive t Mt R s need _ sp hs1 hs2 hs3 hs4 hal (by decide) h1 h2 h12
      (by rw [hres]; rfl) hflU hfl fun R' M' hr hP => ?_
    have := hfin R' M' [] hr ⟨rfl, hP⟩
    simpa [putcs] using this
  · exact sprintErr_run hlive t Mt R s need _ sp p bs hs1 hs2 hs3 hs4 hal (by decide) hk
      (by omega) (by simp only [eq_iff_iff, iff_false]; intro h
                     have := congrArg BitVec.toNat h; simp at this; omega)
      h1 h2 h10 h11 h12 hres hiov hp hk0 hp1 hp2 hp3 hpd hpsrc hfl hfd hbase hwr hck
      fun R' M' hr hP => hfin R' M' bs hr ⟨rfl, hP⟩

/-- **The loop's frame slots survive the flush** (`vfp_printH`'s `hPR`). -/
theorem SprintPost.printRet {Mt M' : Mem} {sp : BitVec 64} (h : SprintPost Mt M' sp)
    (hsp1 : 0x80100000 ≤ sp.toNat) (hsp2 : sp.toNat + 592 ≤ 0x88000000) :
    Fp.PrintRet Mt M' sp := by
  have F : Fp.Frame M' Mt (fun a => (sp.toNat - 256 ≤ a ∧ a < sp.toNat) ∨
      (sp.toNat + 232 ≤ a ∧ a < sp.toNat + 248) ∨ (0x8001bbe8 ≤ a ∧ a < 0x8001bbea) ∨
      Stdio.errnoFoot a) := fun a ha => by
    simp only [not_or] at ha
    exact h.frame a ha.1 ha.2.1 ha.2.2.1 ha.2.2.2
  have T : ∀ k : Nat, k + 8 ≤ 232 → ldv .ld M' (sp + BitVec.ofNat 64 k).toNat =
      ldv .ld Mt (sp + BitVec.ofNat 64 k).toNat := fun k hk => F.ldv _ fun j hj => by
    simp only [widthOfM, Stdio.errnoFoot, Stdio.InRange] at hj ⊢
    rw [toNat_add_lit (by omega)]; omega
  exact ⟨by simpa using T 0 (by omega), T 8 (by omega), T 16 (by omega), T 32 (by omega),
    T 224 (by omega), h.res⟩

end VsaIris.Sym
