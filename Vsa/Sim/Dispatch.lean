import Vsa.Elf
import Vsa.Sim.InitValues

/-!
# Layer-0 lemma: `dispatchInterrupt` returns `none` on a fresh-ish machine

This is the first Layer-0 symbolic-execution lemma of PLAN-InterpSim.md
(§Layer 0 item 1). It discharges the interrupt-dispatch check that every
`try_step` performs before fetching an instruction.

`dispatchInterrupt Privilege.Machine` walks `getPendingSet`, which computes

  * `pending_m = mip &&& (mie &&& ~mideleg)`
  * `pending_s = mip &&& (mie &&& mideleg)`

The crucial semantic fact is that `init_model` leaves `mie = 0`. With
`mie = 0`, both `pending_m` and `pending_s` are `0` no matter what `mip`,
`mideleg`, or `mstatus` hold, so `getPendingSet` returns `none` and hence
`dispatchInterrupt` returns `none`.

The computation only *reads* registers (no writes), so the final state is
syntactically the input state `σ`.

Read footprint discovered on this path (each needs a `get?` hypothesis or
`readReg` throws `Unreachable`):

  * `misa`         — read by `currentlyEnabled Ext_S`; its S bit is **1** at
                     init (`initMisa = 0x800000000034112f`, bit 18 set), so
                     `Ext_S` is *enabled*. This is why `mideleg` and `sig_seip`
                     *are* read on this path (unlike the pre-reset seed value,
                     which had S=0).
  * `mip`          — read by `read_mip IncludePlatformInterrupts`
  * `sig_meip`     — read by `external_interrupts_pending` (folded into `mip`)
  * `sig_seip`     — read by `external_interrupts_pending` because `Ext_S` is
                     enabled (folded into `mip`)
  * `mie`          — pinned to `0`; this is what makes the pending sets vanish
  * `mideleg`      — read by `getPendingSet` because `Ext_S` is enabled; its
                     value is irrelevant since `mie = 0` zeroes both
                     `pending_m = mip &&& (0 &&& ~mideleg)` and
                     `pending_s = mip &&& (0 &&& mideleg)`
  * `mstatus`      — read to compute the `mIE`/`sIE` gates

`cur_privilege` is **not** read on this path. The values of `mip`,
`sig_meip`, `sig_seip`, `mideleg`, and `mstatus` are all irrelevant
(universally quantified); only `misa` (pinned to its init value, S bit set)
and `mie` (pinned to `0`) matter — `mie = 0` makes both pending sets vanish
regardless of the S-delegation path.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-- `dispatchInterrupt Machine` yields `none` and leaves the state untouched,
given that `misa = initMisa` (so `Ext_S` is enabled) and `mie = 0` (as
`init_model` establishes) and that the registers on the read path are present.
`mie = 0` zeroes both `pending_m` and `pending_s` regardless of the `Ext_S`
S-delegation path, so `mideleg`/`sig_seip` values stay universally quantified. -/
theorem Vsa.Sim.dispatch_none
    (σ : SequentialState RegisterType trivialChoiceSource)
    (vmip : RegisterType Register.mip)
    (vmeip : RegisterType Register.sig_meip)
    (vseip : RegisterType Register.sig_seip)
    (vmideleg : RegisterType Register.mideleg)
    (vmstatus : RegisterType Register.mstatus)
    (hmisa : σ.regs.get? Register.misa =
      some ((Vsa.Sim.initMisa) : RegisterType Register.misa))
    (hmie : σ.regs.get? Register.mie =
      some ((BitVec.zero 64) : RegisterType Register.mie))
    (hmip : σ.regs.get? Register.mip = some vmip)
    (hmeip : σ.regs.get? Register.sig_meip = some vmeip)
    (hseip : σ.regs.get? Register.sig_seip = some vseip)
    (hmideleg : σ.regs.get? Register.mideleg = some vmideleg)
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus) :
    (dispatchInterrupt Privilege.Machine).run σ = .ok none σ := by
  simp only [dispatchInterrupt, getPendingSet, read_mip, external_interrupts_pending]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    currentlyEnabled, hartSupports, get, getThe, MonadStateOf.get, EStateM.get,
    readReg, _get_Misa_S, Vsa.Sim.initMisa, findPendingInterrupt]
  -- Both pending sets are `0#64` (`mie = 0` zeroes them), so `¬ 0#64 = zeros`
  -- is false and both `if`s take the else-branch: `getPendingSet` returns
  -- `none`.
  have hz : (0#64 : BitVec 64) = zeros (n := 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  simp [hz, EStateM.pure, and_false]
