import VsaIris.Vsa.SnpTac
import VsaIris.Interp.ProofArith

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open Vsa.MemRepr

theorem udiv_nw {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1)
    {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (n d r : BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) (hd : d ≠ 0#64) (h10 : R 10 = n) (h11 : R 11 = d) (hr : R 1 = r)
    (hal : r.toNat % 4 = 0)
    (hk : ∀ R', (R' 10).toNat = n.toNat / d.toNat → (R' 11).toNat = n.toNat % d.toNat →
      DivKeep R' R → SnpW live Dt DA S Q r R' Mt) :
    SnpW live Dt DA S Q 0x800046ac#64 R Mt :=
  swp_host_out (fun p hp => List.mem_append_left _ (arith_snp p hp))
    (udivH (fun p hp => hlive _ (arith_snp p hp)) n d r R Mt hd h10 h11 hr hal
      fun R' h1 h2 h3 => swp_host_in (hk R' h1 h2 h3))

theorem umod_nw {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1)
    {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (n d r : BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) (hd : d ≠ 0#64) (h10 : R 10 = n) (h11 : R 11 = d) (hr : R 1 = r)
    (hal : r.toNat % 4 = 0)
    (hk : ∀ R', (R' 10).toNat = n.toNat % d.toNat →
      (∀ z, z ≠ 1 → z ≠ 5 → z ≠ 10 → z ≠ 11 → z ≠ 12 → z ≠ 13 → R' z = R z) →
      SnpW live Dt DA S Q r R' Mt) :
    SnpW live Dt DA S Q 0x800046f4#64 R Mt :=
  swp_host_out (fun p hp => List.mem_append_left _ (arith_snp p hp))
    (umodH (fun p hp => hlive _ (arith_snp p hp)) n d r R Mt hd h10 h11 hr hal
      fun R' h1 h2 => swp_host_in (hk R' h1 h2))

end VsaIris.Interp
