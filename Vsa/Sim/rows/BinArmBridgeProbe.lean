import Vsa.Sim.rows.BinArmBridge

/-!
# `BinArmBridgeProbe` — composition sanity check for `blockA_binaryArm`

Shows that the bridge output connects to `blockB_binary` (the two-operand head
that every `eval<Op>Sim` starts from): composing `blockA_binaryArm ≫ blockB_binary`
for `.add` yields `Triple (EvalEntry (.binary .add el er)) (TwoSubReturn …)`,
confirming the `ArmEntryK`-∃ entry the case theorems consume is now PRODUCED from
the `EvalEntry` recursor premise.  The bridge's existential ghosts
(`gpre`/`aEnvReg`/`v8`/`v9`/`v18`/`v19`) are unpacked and fed as `blockB_binary`'s
parameters — the seam is `rfl`-tight (no re-derivation).

This does NOT close `hBinary` (the op×kind dispatcher + `AddResid`/`g`-bridge
row-residuals + str-arms remain — see the ledger); it only demonstrates the
entry linkage.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- **Probe**: `blockA_binaryArm ≫ blockB_binary` at `.add`, int operands.  From the
`EvalEntry` recursor-premise entry (the `.binary .add` node) to `TwoSubReturn` at
`0x8000351c` — i.e. the entry factored OUT of `evalAddSim` is now supplied by the
bridge.  All the residuals `blockB_binary` needs beyond the bridge output are the
two `EvalIH` sub-derivations + the left-value survival closure (both threaded
straight through). -/
theorem binArm_add_entry_connects
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (a b : Int)
    (sp r sret aEnv aExpr aLOp aROp : BitVec 64)
    (m0 : Mem)
    (hX : BinArmExtras g N A SL .add el er sp r sret aExpr aLOp aROp m0)
    (hIHl : EvalIH st d env el st' (.int a))
    (hIHr : EvalIH st' d env er st'' (.int b))
    (hVlSurv : ∀ (φ : Addr → Nat) (m m' : Mem),
      ValueRepr m N φ (sp.toNat - 968) (.int a) →
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat - 1080) → ¬ (A.lo ≤ k ∧ k < A.hi) →
        ¬ ((sp.toNat - 944) ≤ k ∧ k < (sp.toNat - 944) + 24) → m[k]? = m'[k]?) →
      ValueRepr m' N φ (sp.toNat - 968) (.int a)) :
    Triple
      (fun c => EvalEntry g N A SL φf φc st d env (.binary .add el er) sp r sret aEnv aExpr m0 c)
      (fun c => ∃ gpre v8 v9 v18,
        TwoSubReturn gpre N A SL φf φc st.store.frames.size st.store.closures.size
          st' st'' (.int a) (.int b) sp r sret v8 v9 v18 m0 c) := by
  -- block A: the bridge produces the `blockB_binary` entry from `EvalEntry`.
  have hA := blockA_binaryArm g N A SL φf φc st d env .add el er sp r sret aEnv aExpr aLOp aROp m0 hX
  -- compose: for each entry config, run the bridge, unpack its ∃-ghosts, then run
  -- `blockB_binary` with those ghosts as its parameters.
  intro c hc
  obtain ⟨c1, hs1, gpre, aEnvReg, v8, v9, v18, v19, ment, hEntryB⟩ := hA c hc
  obtain ⟨c2, hs2, hTS⟩ :=
    blockB_binary g gpre N A SL φf φc st st' st'' d env .add el er (.int a) (.int b)
      sp r sret aExpr aEnv aLOp aROp aEnvReg v8 v9 v18 v19 c1.σ.sailOutput m0 hIHl hIHr hVlSurv
      c1 ⟨ment, hEntryB⟩
  exact ⟨c2, hs1.trans hs2, gpre, v8, v9, v18, hTS⟩

end Vsa.Sim
