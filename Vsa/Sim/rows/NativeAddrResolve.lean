import Vsa.Sim.EvalCallNative3
import Vsa.Sim.BridgeSeg

/-!
# `NativeAddrResolve` — the `jalr a6` native-address resolution layer (wave 41)

Task `#26 nativeArmSplice`, abstraction (2) of the observation
`native-call-segentry-wrapper` (`experiments/observations.md` 2026-09-01): the
small reusable lemmas that resolve the EX_CALL native arm's **indirect
`jalr a6`** (`0x800039f4`) to the native's entry `N.addr f`.

Three layers, each reusable on its own:

1. **`ValueRepr (.native f)` destructurers** — `ValueRepr`'s `.native` case is
   an anonymous ∧/∃ tower (`Vsa/RuntimeRepr.lean:86`); per CLAUDE.md R6 these
   are THE named destructurers to consume it through (the fn-ptr word, the kind
   word, the name string).  The fn-ptr word `read64 m (a+16) = some (N.addr f)`
   is what pins `a6` (loaded at `0x8000325c` from the staged `fv` word2).
2. **`jalrStep_of_obs`** — the INDIRECT-call twin of `BridgeSeg.jalStep_of_obs`,
   done ONCE: build a `JalStep tgt link` from the raw `jalr` observation
   (`sigmaPost_jalr … Register.x1 link`, the exact output of `stepObs_jalr`).
   Any future indirect-call seam (function-pointer dispatch) reuses this.
3. **`nativeJalrStep`** — the concrete `0x800039f4` seam: from a state parked at
   the arm's `jalr` with `a6 = a6v` (4-aligned), one `JalStep a6v 0x800039f8`.
   The three natives differ ONLY in `a6v` (`= N.addr .assert/.print/.println`,
   supplied by destructurer (1) through the staged-`fv` readback).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr

namespace Vsa.Sim

/-! ## §1. `ValueRepr (.native f)` — the named destructurers (CLAUDE.md R6) -/

/-- **The native fn-ptr word off `ValueRepr`** — a `.native f` Value's third
word (`*(a+16)`) is the native's machine entry `N.addr f`.  This is the fact
that resolves the `jalr a6` target: `a6` is loaded (via the `sp+112` staging)
from exactly this word. -/
theorem nativeAddr_of_valueRepr {m : Mem} {N : NativeAddrs} {φc : Vsa.While.Addr → Nat}
    {a : Nat} {f : Vsa.While.NativeFn}
    (h : ValueRepr m N φc a (.native f)) :
    read64 m (a + 16) = some (N.addr f) :=
  h.2.2

/-- **The native kind word off `ValueRepr`** — a `.native f` Value's kind word
is `5` (`VAL_NATIVE`).  This is the witness for the TAKEN `beq a4,a2` at
`0x8000327c` (the native-arm dispatch guard `kind == 5`). -/
theorem nativeKind_of_valueRepr {m : Mem} {N : NativeAddrs} {φc : Vsa.While.Addr → Nat}
    {a : Nat} {f : Vsa.While.NativeFn}
    (h : ValueRepr m N φc a (.native f)) :
    read32 m a = some 5 :=
  h.1

/-- **The native name string off `ValueRepr`** — the payload pointer (`*(a+8)`)
is a C string of the native's name (completing the R6 destructurer set for the
`.native` tower). -/
theorem nativeName_of_valueRepr {m : Mem} {N : NativeAddrs} {φc : Vsa.While.Addr → Nat}
    {a : Nat} {f : Vsa.While.NativeFn}
    (h : ValueRepr m N φc a (.native f)) :
    ∃ p, read64 m (a + 8) = some p ∧ CString m p (nativeName f) :=
  h.2.1

/-! ## §2. `jalrStep_of_obs` — the indirect-call `JalStep` glue (done ONCE)

The `jal` seam glue is `BridgeSeg.jalStep_of_obs` (over `sigmaPost_jal`); an
INDIRECT call (`jalr rd=x1`) lands the same `JalStep` shape — one linking step
to a computed target — but from a `sigmaPost_jalr` observation.  Mirrors
`jalStep_of_obs` field-for-field with the `obs_jalr_*` consumers
(`SnprintfSitesRet5.lean`). -/

theorem jalrStep_of_obs {σp σ2 : MState} {ip up i2 : Nat}
    {jalrPC vm tgt link : BitVec 64}
    (hstep : Step ⟨σp, ip, up⟩ ⟨σ2, i2, up + 1⟩) (hi2 : i2 < 2) (hG2 : GoodState σ2)
    (hmem : σ2.mem = σp.mem)
    (hobs : ReadsLikePost σ2 (sigmaPost_jalr σp jalrPC vm tgt Register.x1 link)) :
    JalStep tgt link σp ip up := by
  refine ⟨σ2, i2, hstep, hi2, hG2, hmem, ?_, ?_, ?_, ?_, ?_⟩
  · exact obs_jalr_pc hobs
  · exact obs_jalr_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact obs_jalr_minstret hobs
  · -- nonRa: every GPR n ∈ 1..31, n ≠ 1 survives (dispatch on n).
    intro n hn1 hn31 hne w hw
    match n, hn1, hn31, hne, hw with
    | 0, h, _, _, _ => exact absurd h (by omega)
    | 1, _, _, hne, _ => exact absurd rfl hne
    | 2, _, _, _, hw => exact obs_jalr_other hobs Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 3, _, _, _, hw => exact obs_jalr_other hobs Register.x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 4, _, _, _, hw => exact obs_jalr_other hobs Register.x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 5, _, _, _, hw => exact obs_jalr_other hobs Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 6, _, _, _, hw => exact obs_jalr_other hobs Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 7, _, _, _, hw => exact obs_jalr_other hobs Register.x7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 8, _, _, _, hw => exact obs_jalr_other hobs Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 9, _, _, _, hw => exact obs_jalr_other hobs Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 10, _, _, _, hw => exact obs_jalr_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 11, _, _, _, hw => exact obs_jalr_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 12, _, _, _, hw => exact obs_jalr_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 13, _, _, _, hw => exact obs_jalr_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 14, _, _, _, hw => exact obs_jalr_other hobs Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 15, _, _, _, hw => exact obs_jalr_other hobs Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 16, _, _, _, hw => exact obs_jalr_other hobs Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 17, _, _, _, hw => exact obs_jalr_other hobs Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 18, _, _, _, hw => exact obs_jalr_other hobs Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 19, _, _, _, hw => exact obs_jalr_other hobs Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 20, _, _, _, hw => exact obs_jalr_other hobs Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 21, _, _, _, hw => exact obs_jalr_other hobs Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 22, _, _, _, hw => exact obs_jalr_other hobs Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 23, _, _, _, hw => exact obs_jalr_other hobs Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 24, _, _, _, hw => exact obs_jalr_other hobs Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 25, _, _, _, hw => exact obs_jalr_other hobs Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 26, _, _, _, hw => exact obs_jalr_other hobs Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 27, _, _, _, hw => exact obs_jalr_other hobs Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 28, _, _, _, hw => exact obs_jalr_other hobs Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 29, _, _, _, hw => exact obs_jalr_other hobs Register.x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 30, _, _, _, hw => exact obs_jalr_other hobs Register.x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 31, _, _, _, hw => exact obs_jalr_other hobs Register.x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | k+32, _, h, _, _ => exact absurd h (by omega)
  · -- ABI frame: any callee-saved R avoids x1 + the control/noise registers.
    intro R hR
    exact (hobs.1 R (abiPreserved_ne hR (by decide)) (abiPreserved_ne hR (by decide))
        (abiPreserved_ne hR (by decide))).trans
      (get?_sigmaPost_jalr σp jalrPC vm tgt Register.x1 link R
        (abiPreserved_ne hR (by decide)) (abiPreserved_ne hR (by decide))
        (abiPreserved_ne hR (by decide)) (abiPreserved_ne hR (by decide))
        (abiPreserved_ne hR (by decide)))

/-! ## §3. The concrete `0x800039f4` seam -/

/-- **The native `jalr a6` seam** (`0x800039f4`, shared by assert/print/
println): from a state parked at the arm's `jalr` with `a6 = a6v` (a 4-aligned
native code entry) and `eval_expr`'s code loaded, one `JalStep a6v 0x800039f8`
— the machine lands at the native's entry with the link `ra = 0x800039f8` and
every marshalled register surviving.  The per-native `a6v = N.addr f` value
enters through `nativeAddr_of_valueRepr` upstream (the staged-`fv` readback). -/
theorem nativeJalrStep (σ : MState) (i u : Nat) (vm a6v : BitVec 64)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some (0x800039f4#64 : BitVec 64))
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hx16 : σ.regs.get? Register.x16 = some a6v)
    (hload : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (halign : a6v.toNat % 4 = 0)
    (hi : i < 2) :
    JalStep a6v (0x800039f8#64) σ i u := by
  have hupd : BitVec.update (a6v + sign_extend (m := 64) (0x000#12)) 0 0#1 = a6v :=
    jalr_native_target a6v halign
  obtain ⟨σ2, i2, hstep, hi2, hG2, hmem2, hobs⟩ :=
    site_800039f4_nw σ i u (0x800039f4#64) vm a6v hG hpc hmi hx16 hload rfl
      (by rw [hupd]; exact halign) hi
  rw [hupd] at hobs
  rw [show BitVec.addInt (0x800039f4#64) 4 = (0x800039f8#64 : BitVec 64) from by decide] at hobs
  exact jalrStep_of_obs hstep hi2 hG2 hmem2 hobs

#print axioms nativeAddr_of_valueRepr
#print axioms nativeKind_of_valueRepr
#print axioms nativeName_of_valueRepr
#print axioms jalrStep_of_obs
#print axioms nativeJalrStep

end Vsa.Sim
