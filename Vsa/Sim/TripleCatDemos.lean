import Vsa.Sim.TripleCat
import Vsa.Sim.DeriveCallSeg
import Vsa.Sim.EnvDefBridges3
import Vsa.Sim.rows.ArmPostGeom

/-!
# `TripleCatDemos` — landed adapters re-expressed through the `TripleCat` calculus

This file is the MEASURED requirement of the `TripleCat` task: it re-expresses landed
consequence adapters as `Triple.dimap` one-liners and a landed adapter PAIR as a single
`PredIso` + transport, proving the SAME statements as the originals WITHOUT editing them.

Each `_dimap` theorem below states the landed adapter's conclusion verbatim and proves it
by a single `Triple.dimap` (or `PredIso.transportPre`) application, replacing the
hand-written `Triple.conseq …` / adapter-pair boilerplate.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa Vsa.RuntimeRepr Vsa.MemRepr Vsa.Alloc Vsa.Sim.Code
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic

namespace Vsa.Sim

/-! ## Demo 1 — `callSegConseq` re-expressed as `callSeg` + `Triple.dimap`

`DeriveCallSeg.callSegConseq` glues a callee contract stated over its own boundaries
`C_in`/`C_out` into the prefix/suffix seams via a hand-written `Triple.conseq callee hin
hout`.  That inner `conseq` IS the profunctor action on the callee: `Triple.dimap hin
hout callee`.  Same statement, dimap in the seam. -/
theorem callSegConseq_dimap {P Mid1 Mid2 Q C_in C_out : Config → Prop}
    (pre : Triple P Mid1) (callee : Triple C_in C_out) (suf : Triple Mid2 Q)
    (hin : ∀ c, Mid1 c → C_in c) (hout : ∀ c, C_out c → Mid2 c) :
    Triple P Q :=
  callSeg pre (Triple.dimap hin hout callee) suf

/-! ## Demo 2 — `bridgeNamesToVals_wired` re-expressed as `Triple.dimap`

The landed `EnvDefBridges3.bridgeNamesToVals_wired` is
`Triple.conseq (bridgeNamesToVals_closed …) hEntry (fun _ h => h)` — a precondition
pullback along `hEntry` with the postcondition left alone.  That is exactly
`Triple.lmap hEntry (core)` (i.e. `dimap hEntry (Ent.refl _) core`).  We restate the
adapter's full conclusion and prove it with `Triple.lmap`. -/
theorem bridgeNamesToVals_wired_dimap
    (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    {AInv : MState → List Extent → Prop} {Src : Config → Prop}
    (extsV : List Extent) (spN : BitVec 64)
    (gN gV : (R : Register) → Option (RegisterType R))
    (s4Ptr pNamesNew : BitVec 64) (pValsOld nValsNew : Nat) (capw : Nat)
    (mN : Vsa.MemRepr.Mem)
    (hEntry : ∀ c, Src c →
      GrowEnvEntry SL gpv headroom AInv extsV spN gN s4Ptr pNamesNew pValsOld capw mN c)
    (hpTie : ∀ (m : Vsa.MemRepr.Mem), read64 m (s4Ptr.toNat + 16) = some pValsOld →
      ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8),
        m[s4Ptr.toNat + 16]? = some b0 → m[s4Ptr.toNat + 17]? = some b1 →
        m[s4Ptr.toNat + 18]? = some b2 → m[s4Ptr.toNat + 19]? = some b3 →
        m[s4Ptr.toNat + 20]? = some b4 → m[s4Ptr.toNat + 21]? = some b5 →
        m[s4Ptr.toNat + 22]? = some b6 → m[s4Ptr.toNat + 23]? = some b7 →
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 pValsOld)
    (hnTie : ∀ (c0 c1 c2 c3 : BitVec 8),
        c0.toNat + 256 * (c1.toNat + 256 * (c2.toNat + 256 * c3.toNat)) = capw →
        shift_bits_left
          ((shift_bits_left
              (sign_extend (m := 64) ((((c3.append c2).append c1).append c0) : BitVec (8 * 4)))
              (Sail.BitVec.extractLsb (0x01#6) 5 0))
            + sign_extend (m := 64) ((((c3.append c2).append c1).append c0) : BitVec (8 * 4)))
          (Sail.BitVec.extractLsb (0x03#6) 5 0) = BitVec.ofNat 64 nValsNew)
    (hgVtie : ∀ R, AbiPreserved R = true → R ≠ Register.x15 → R ≠ Register.x10 →
      R ≠ Register.x11 → R ≠ Register.x1 → gV R = gN R)
    (hcapAddr : (s4Ptr + sign_extend (m := 64) (0x004#12)).toNat = s4Ptr.toNat + 4)
    (hvalsAddr : (s4Ptr + sign_extend (m := 64) (0x010#12)).toNat = s4Ptr.toNat + 16)
    (hnamesAddr : (s4Ptr + sign_extend (m := 64) (0x008#12)).toNat = s4Ptr.toNat + 8)
    (hnlo : 0x80000000 ≤ s4Ptr.toNat + 8) (hnhiram : s4Ptr.toNat + 8 + 8 ≤ 0x100000000)
    (hnhiwin : tohostAddr + 16 ≤ s4Ptr.toNat + 8) (hnalign : (s4Ptr.toNat + 8) % 8 = 0)
    (hclo : 0x80000000 ≤ s4Ptr.toNat + 4) (hchiram : s4Ptr.toNat + 4 + 4 ≤ 0x100000000)
    (hchtif : s4Ptr.toNat + 4 + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ s4Ptr.toNat + 4)
    (hcalign : (s4Ptr.toNat + 4) % 4 = 0)
    (hvlo : 0x80000000 ≤ s4Ptr.toNat + 16) (hvhiram : s4Ptr.toNat + 16 + 8 ≤ 0x100000000)
    (hvhtif : s4Ptr.toNat + 16 + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ s4Ptr.toNat + 16)
    (hvalign : (s4Ptr.toNat + 16) % 8 = 0)
    (hnamesCode : s4Ptr.toNat + 8 + 8 ≤ 0x80002a5c ∨ 0x80002c10 ≤ s4Ptr.toNat + 8)
    (hAInvStableNames : ∀ (σa σb : MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a : Nat, (a < s4Ptr.toNat + 8 ∨ s4Ptr.toNat + 8 + 8 ≤ a) → σa.mem[a]? = σb.mem[a]?) →
      AInv σa extsV → AInv σb extsV) :
    Triple Src
      (ReallocPre SL gpv headroom AInv extsV pValsOld nValsNew spN
        (0x80002bc0#64 : BitVec 64)
        (writeMap8 mN (s4Ptr.toNat + 8) (sdData_val pNamesNew)) gV) :=
  Triple.lmap hEntry
    (bridgeNamesToVals_closed SL gpv headroom extsV spN gN gV
      s4Ptr pNamesNew pValsOld nValsNew capw mN hpTie hnTie hgVtie hcapAddr hvalsAddr hnamesAddr
      hnlo hnhiram hnhiwin hnalign hclo hchiram hchtif hcalign hvlo hvhiram hvhtif hvalign
      hnamesCode hAInvStableNames)

/-! ## Demo 3 — the `LtResid ↔ ArmPostGeomV` adapter PAIR as one `PredIso` + transport

`ArmPostGeom.armPostGeomV_of_ltResid` and `ltResid_of_armPostGeomV` are a landed adapter
PAIR (`X_of_Y` + `Y_of_X`).  They are exactly the two directions of an iso of predicates.
`ltResid_armPostGeomV_iso` bundles them into ONE `PredIso`; the parameters
`(gpre,N,A,SL,sp,r,sret,aExpr,Wl)` are fixed and the predicates range over the config
`c'`.  `transportLtResid` then re-expresses any `Triple` whose precondition is `LtResid`
in terms of `ArmPostGeomV` via `PredIso.transportPre` — replacing a hand `Triple.conseq …
(fun c h => armPostGeomV_of_ltResid h) …`. -/

/-- The landed adapter pair, bundled as one iso of predicates. -/
theorem ltResid_armPostGeomV_iso
    (gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (sp r sret aExpr Wl : BitVec 64) :
    PredIso (fun c' => LtResid gpre N A SL sp r sret aExpr Wl c')
      (fun c' => ArmPostGeomV gpre N A SL 20 LtSlotPinned Value_boolLoaded
        0x800027f8 0x8000280c 4 sp r sret aExpr Wl c') :=
  ⟨fun _ h => armPostGeomV_of_ltResid h, fun _ h => ltResid_of_armPostGeomV h⟩

/-- Transport a `Triple` off `LtResid` onto `ArmPostGeomV` via the iso — one
`transportPre`, no per-site `conseq`.  (`R` is any postcondition.) -/
theorem transportLtResid
    {gpre : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout}
    {sp r sret aExpr Wl : BitVec 64} {R : Config → Prop}
    (t : Triple (fun c' => LtResid gpre N A SL sp r sret aExpr Wl c') R) :
    Triple (fun c' => ArmPostGeomV gpre N A SL 20 LtSlotPinned Value_boolLoaded
        0x800027f8 0x8000280c 4 sp r sret aExpr Wl c') R :=
  (ltResid_armPostGeomV_iso gpre N A SL sp r sret aExpr Wl).transportPre t

#print axioms callSegConseq_dimap
#print axioms bridgeNamesToVals_wired_dimap
#print axioms ltResid_armPostGeomV_iso
#print axioms transportLtResid

end Vsa.Sim
