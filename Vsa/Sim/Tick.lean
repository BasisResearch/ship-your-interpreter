import Vsa.Elf
import Vsa.Sim.InitValues
import Vsa.Sim.StateNF

/-!
# Layer-0 characterization of `tick_clock`

`Vsa.stepOnce` (`Vsa/Elf.lean`) calls `tick_clock ()` every
`plat_insns_per_tick = 2` retired instructions, so every step-characterization
lemma must splice the tick in. This module characterizes `tick_clock` once, on
the pinned M-mode control state, so the `stepOnce` lemmas can reuse it instead
of re-unfolding the platform clock path (`Platform.lean:535`).

`tick_clock` does three things:
1. `should_inc_mcycle cur_privilege` — with `mcountinhibit`/`mcyclecfg` pinned
   to their init `0` values this is `true` (mirror of
   `should_inc_minstret_machine` in `Vsa/Sim/Hooks.lean`), so `mcycle += 1`.
2. `mtime += 1`.
3. `clint_dispatch false` — writes the MTI bit of `mip` from
   `mtimecmp ≤u mtime` (`updateSubrange mip 7 7 (bool_to_bit (mtimecmp ≤u mtime))`,
   reading the *original* `mip`); the `Sstc` sub-timer branch is dead
   (`menvcfg.STCE = 0`), the print is off, and the trailing
   `csr_name_write_callback "mip" (read_mip …)` branch is **read-only**.

## The conditional callback branch

`clint_dispatch` ends with

```
if old_mip != new_mip || false then csr_name_write_callback "mip" (read_mip …)
else pure ()
```

The guard is `vmip`-dependent and hence undecidable, but both arms are the
identity on state, so we never case-split on the guard's *value*: we `split`
the `if` and discharge the then-arm with `mip_write_callback_noop` and the
else-arm with `rfl`. `mip_write_callback_noop` proves the then-arm read-only by
composing `read_mip_run` (which reduces `read_mip IncludePlatformInterrupts` —
reads `mip`, `sig_meip`, `misa` via `currentlyEnabled Ext_S`, and `sig_seip`)
with `csr_map_mip_eq` (`csr_name_map_backwards "mip" = pure 0x344#12`, proved by
`rfl` at the term level — the `.run`-applied form provokes a `whnf` blowup on
the 268-arm string match, but the plain equation reduces fine).

## Register writes

`writeReg r v = modify (regs := regs.insert r v)`, so the final state is the
ordered insert chain `mcycle`, `mtime`, `mip`. Reads back through the chain use
`Std.ExtDHashMap.get?_insert` with the *inserted-key `==` queried-key* order
(the `dite` condition is `(insertedReg == queriedReg)`) resolved by `decide`.
Increments land as `BitVec.addInt _ 1` (the model's form).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- `currentlyEnabled Ext_S = true` given `misa = initMisa` (S-bit set): reads
`misa` and the pure `currentlyEnabled Ext_Zicsr`, leaving state fixed. -/
theorem currentlyEnabled_S
    (τ : SequentialState RegisterType trivialChoiceSource)
    (hmisa : τ.regs.get? Register.misa = some initMisa) :
    (currentlyEnabled extension.Ext_S).run τ = .ok true τ := by
  have hbit : BitVec.extractLsb 18 18 initMisa = 1#1 := by decide
  simp only [currentlyEnabled, hartSupports, _get_Misa_S]
  simp [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    readReg, get, getThe, MonadStateOf.get, EStateM.get, hmisa, hbit]

/-- `currentlyEnabled Ext_Sstc = true` (pure `hartSupports`; no register read).
Justifies collapsing the Sstc guard in `clint_dispatch`. -/
theorem currentlyEnabled_Sstc
    (τ : SequentialState RegisterType trivialChoiceSource) :
    (currentlyEnabled extension.Ext_Sstc).run τ = .ok true τ := by
  simp only [currentlyEnabled, hartSupports]
  simp [simp_sail, EStateM.run, pure, EStateM.pure]

/-- `csr_name_map_backwards "mip"` is the pure lookup `pure 0x344#12`. Proved by
`rfl` on the *plain* action — the `.run`-applied form triggers a `whnf` timeout
on the 268-arm string match, but the definitional equation reduces cheaply. -/
theorem csr_map_mip_eq :
    csr_name_map_backwards "mip" = (pure 0x344#12 : SailM (BitVec 12)) := by
  unfold csr_name_map_backwards; rfl

/-- `read_mip IncludePlatformInterrupts` reads `mip`, `sig_meip`, `misa` (via
`currentlyEnabled Ext_S`) and `sig_seip`, returning the OR of `mip` with the
external-interrupt pending bits, leaving state fixed. -/
theorem read_mip_run
    (τ : SequentialState RegisterType trivialChoiceSource)
    (vmip : BitVec 64)
    (hmip : τ.regs.get? Register.mip = some vmip)
    (vmeip : BitVec 1) (hmeip : τ.regs.get? Register.sig_meip = some vmeip)
    (vseip : BitVec 1) (hseip : τ.regs.get? Register.sig_seip = some vseip)
    (hmisa : τ.regs.get? Register.misa = some initMisa) :
    (read_mip XipReadType.IncludePlatformInterrupts).run τ
      = .ok (Mk_Minterrupts (vmip ||| (_update_Minterrupts_SEI
          (_update_Minterrupts_MEI (Mk_Minterrupts zeros) vmeip) vseip))) τ := by
  have hS : (currentlyEnabled extension.Ext_S) τ = .ok true τ :=
    currentlyEnabled_S τ hmisa
  simp only [read_mip, external_interrupts_pending, bind, Bind.bind, EStateM.bind,
    EStateM.run, PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    pure, EStateM.pure, hmip, hmeip, hseip, hS, if_pos]

/-- The trailing `csr_name_write_callback "mip" (read_mip …)` of `clint_dispatch`
is read-only: `read_mip` reads registers but `csr_name_map_backwards "mip"`
reads none and `csr_full_write_callback = ()`, so the whole call is the identity
on state. Only requires the read registers be present (`mip` arbitrary). -/
theorem mip_write_callback_noop
    (τ : SequentialState RegisterType trivialChoiceSource)
    (vmip : BitVec 64)
    (hmip : τ.regs.get? Register.mip = some vmip)
    (hmeip : ∃ v, τ.regs.get? Register.sig_meip = some v)
    (hseip : ∃ v, τ.regs.get? Register.sig_seip = some v)
    (hmisa : τ.regs.get? Register.misa = some initMisa) :
    ((read_mip XipReadType.IncludePlatformInterrupts) >>=
        fun v => csr_name_write_callback "mip" v).run τ
      = .ok () τ := by
  obtain ⟨vmeip, hmeip⟩ := hmeip
  obtain ⟨vseip, hseip⟩ := hseip
  have hrm := read_mip_run τ vmip hmip vmeip hmeip vseip hseip hmisa
  simp only [EStateM.run] at hrm
  simp only [csr_name_write_callback, csr_full_write_callback, csr_map_mip_eq,
    bind, Bind.bind, EStateM.bind, EStateM.run, pure, EStateM.pure, hrm]

/-- `clint_dispatch false` on the pinned control state: writes exactly the MTI
bit of `mip` (`updateSubrange vmip 7 7 (bool_to_bit (mtimecmp ≤u mtime))`,
reading the original `mip`). The `Sstc` branch is dead (`menvcfg.STCE = 0`), the
print is off, and the callback branch is read-only (both `if` arms leave the
post-write state fixed, so no case-split on the guard's value). -/
theorem clint_dispatch_false_char
    (σ : SequentialState RegisterType trivialChoiceSource)
    (vmip vmtime vmtimecmp : BitVec 64)
    (hmip : σ.regs.get? Register.mip = some vmip)
    (hmtime : σ.regs.get? Register.mtime = some vmtime)
    (hmtimecmp : σ.regs.get? Register.mtimecmp = some vmtimecmp)
    (hmenvcfg : σ.regs.get? Register.menvcfg = some (0#64))
    (hmisa : σ.regs.get? Register.misa = some initMisa)
    (hmeip : ∃ v, σ.regs.get? Register.sig_meip = some v)
    (hseip : ∃ v, σ.regs.get? Register.sig_seip = some v) :
    (clint_dispatch false).run σ
      = .ok () {σ with regs :=
          σ.regs.insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp vmtime)))} := by
  -- read old mip / mtimecmp / mtime, then write the MTI bit of mip
  simp only [clint_dispatch, bind, Bind.bind, EStateM.bind, EStateM.run,
    PreSail.readReg, PreSail.writeReg, get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    pure, EStateM.pure, hmip, hmtime, hmtimecmp]
  -- currentlyEnabled Ext_Sstc = true on the post-write state (reads no register)
  simp only [show ∀ τ, currentlyEnabled extension.Ext_Sstc τ = EStateM.Result.ok true τ from
    fun τ => currentlyEnabled_Sstc τ]
  -- menvcfg read from post-write state (mip ≠ menvcfg); STCE = 0 kills the Sstc write
  simp only [Std.ExtDHashMap.get?_insert, show (mip == menvcfg) = false from by decide,
    dif_neg, reduceCtorEq, not_false_eq_true, hmenvcfg,
    Bool.true_and, _get_MEnvcfg_STCE]
  simp only [show (Sail.BitVec.extractLsb (0#64) 63 63 == 1#1) = false from by decide,
    if_false, Bool.false_eq_true, EStateM.pure]
  -- print off ⇒ else branch; the callback then reads mip back from the post-write state
  simp only [get_config_print_clint, Bool.false_eq_true, if_false,
    EStateM.bind, EStateM.pure, EStateM.get,
    Std.ExtDHashMap.get?_insert_self]
  -- the callback fires iff mip changed; both `if` arms leave the state fixed
  have hmip' : ({σ with regs := σ.regs.insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp vmtime)))} : SequentialState RegisterType trivialChoiceSource).regs.get? Register.mip
      = some (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp vmtime))) := by
    show (σ.regs.insert Register.mip _).get? Register.mip = _
    rw [Std.ExtDHashMap.get?_insert_self]
  have hmeip' : ∃ v, ({σ with regs := σ.regs.insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp vmtime)))} : SequentialState RegisterType trivialChoiceSource).regs.get? Register.sig_meip = some v := by
    obtain ⟨v, hv⟩ := hmeip
    refine ⟨v, ?_⟩
    show (σ.regs.insert Register.mip _).get? Register.sig_meip = _
    rw [Std.ExtDHashMap.get?_insert]; simp [hv]
  have hseip' : ∃ v, ({σ with regs := σ.regs.insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp vmtime)))} : SequentialState RegisterType trivialChoiceSource).regs.get? Register.sig_seip = some v := by
    obtain ⟨v, hv⟩ := hseip
    refine ⟨v, ?_⟩
    show (σ.regs.insert Register.mip _).get? Register.sig_seip = _
    rw [Std.ExtDHashMap.get?_insert]; simp [hv]
  have hmisa' : ({σ with regs := σ.regs.insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp vmtime)))} : SequentialState RegisterType trivialChoiceSource).regs.get? Register.misa = some initMisa := by
    show (σ.regs.insert Register.mip _).get? Register.misa = _
    rw [Std.ExtDHashMap.get?_insert]; simp [hmisa]
  have hcb := mip_write_callback_noop _ _ hmip' hmeip' hseip' hmisa'
  simp only [bind, Bind.bind, EStateM.bind, EStateM.run] at hcb
  split
  · exact hcb
  · rfl

/-- `should_inc_mcycle Machine = true` given `mcountinhibit = 0#32`,
`mcyclecfg = 0#64` (the pinned init values). Mirror of
`should_inc_minstret_machine`. -/
theorem should_inc_mcycle_machine
    (σ : SequentialState RegisterType trivialChoiceSource)
    (hmci : σ.regs.get? Register.mcountinhibit = some (0#32 : RegisterType Register.mcountinhibit))
    (hmcc : σ.regs.get? Register.mcyclecfg = some (0#64 : RegisterType Register.mcyclecfg)) :
    (should_inc_mcycle Privilege.Machine).run σ = .ok true σ := by
  simp only [should_inc_mcycle, counter_priv_filter_bit, _get_Counterin_CY,
    _get_CountSmcntrpmf_MINH]
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    readReg, get, getThe, MonadStateOf.get, EStateM.get]

/-- Full characterization of `tick_clock ()` on the pinned M-mode control state:
`mcycle += 1`, `mtime += 1`, then the MTI bit of `mip` set from
`mtimecmp ≤u (mtime + 1)`. The final state is the ordered insert chain
`mcycle`, `mtime`, `mip` (increments as `BitVec.addInt _ 1`). Composes
`should_inc_mcycle_machine` (⇒ `mcycle` is written) and
`clint_dispatch_false_char` on the post-`mtime`-write state (whose `mtime` is
`vmtime + 1`, so the MTI comparison uses `vmtime + 1`). -/
theorem tick_clock_char
    (σ : SequentialState RegisterType trivialChoiceSource)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64)
    (hpriv : σ.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hmci : σ.regs.get? Register.mcountinhibit = some (0#32 : RegisterType Register.mcountinhibit))
    (hmcc : σ.regs.get? Register.mcyclecfg = some (0#64 : RegisterType Register.mcyclecfg))
    (hmenvcfg : σ.regs.get? Register.menvcfg = some (0#64))
    (hmisa : σ.regs.get? Register.misa = some initMisa)
    (hmip : σ.regs.get? Register.mip = some vmip)
    (hmtime : σ.regs.get? Register.mtime = some vmtime)
    (hmtimecmp : σ.regs.get? Register.mtimecmp = some vmtimecmp)
    (hmcycle : σ.regs.get? Register.mcycle = some vmcycle)
    (hmeip : ∃ v, σ.regs.get? Register.sig_meip = some v)
    (hseip : ∃ v, σ.regs.get? Register.sig_seip = some v) :
    (tick_clock ()).run σ
      = .ok () {σ with regs := (((σ.regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert Register.mtime (BitVec.addInt vmtime 1)).insert Register.mip (Sail.BitVec.updateSubrange vmip 7 7 (bool_to_bit (zopz0zIzJ_u vmtimecmp (BitVec.addInt vmtime 1)))))} := by
  have hinc := should_inc_mcycle_machine σ hmci hmcc
  simp only [EStateM.run] at hinc
  -- read cur_privilege, should_inc_mcycle ⇒ mcycle += 1, then mtime += 1
  simp only [tick_clock, bind, Bind.bind, EStateM.bind, EStateM.run,
    PreSail.readReg, PreSail.writeReg, get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    pure, EStateM.pure, hpriv, hinc, if_true]
  -- read mcycle (for the increment) then mtime from the two-insert state
  simp only [hmcycle, EStateM.pure, Std.ExtDHashMap.get?_insert, hmtime]
  -- clint_dispatch false on the state after the mcycle+mtime writes
  have hcd := clint_dispatch_false_char ({σ with regs := (σ.regs.insert Register.mcycle (BitVec.addInt vmcycle 1)).insert Register.mtime (BitVec.addInt vmtime 1)} : SequentialState RegisterType trivialChoiceSource) vmip (BitVec.addInt vmtime 1) vmtimecmp ?hmipτ ?hmtimeτ ?hmtimecmpτ ?hmenvτ ?hmisaτ ?hmeipτ ?hseipτ
  case hmipτ =>
    show ((σ.regs.insert Register.mcycle _).insert Register.mtime _).get? Register.mip = _
    simp only [Std.ExtDHashMap.get?_insert, show (mtime == mip) = false from by decide,
      show (mcycle == mip) = false from by decide, dif_neg, reduceCtorEq,
      not_false_eq_true, hmip]
  case hmtimeτ =>
    show ((σ.regs.insert Register.mcycle _).insert Register.mtime _).get? Register.mtime = _
    rw [Std.ExtDHashMap.get?_insert_self]
  case hmtimecmpτ =>
    show ((σ.regs.insert Register.mcycle _).insert Register.mtime _).get? Register.mtimecmp = _
    simp only [Std.ExtDHashMap.get?_insert, show (mtime == mtimecmp) = false from by decide,
      show (mcycle == mtimecmp) = false from by decide, dif_neg, reduceCtorEq,
      not_false_eq_true, hmtimecmp]
  case hmenvτ =>
    show ((σ.regs.insert Register.mcycle _).insert Register.mtime _).get? Register.menvcfg = _
    simp only [Std.ExtDHashMap.get?_insert, show (mtime == menvcfg) = false from by decide,
      show (mcycle == menvcfg) = false from by decide, dif_neg, reduceCtorEq,
      not_false_eq_true, hmenvcfg]
  case hmisaτ =>
    show ((σ.regs.insert Register.mcycle _).insert Register.mtime _).get? Register.misa = _
    simp only [Std.ExtDHashMap.get?_insert, show (mtime == misa) = false from by decide,
      show (mcycle == misa) = false from by decide, dif_neg, reduceCtorEq,
      not_false_eq_true, hmisa]
  case hmeipτ =>
    obtain ⟨v, hv⟩ := hmeip
    refine ⟨v, ?_⟩
    show ((σ.regs.insert Register.mcycle _).insert Register.mtime _).get? Register.sig_meip = _
    simp only [Std.ExtDHashMap.get?_insert, show (mtime == sig_meip) = false from by decide,
      show (mcycle == sig_meip) = false from by decide, dif_neg, reduceCtorEq,
      not_false_eq_true, hv]
  case hseipτ =>
    obtain ⟨v, hv⟩ := hseip
    refine ⟨v, ?_⟩
    show ((σ.regs.insert Register.mcycle _).insert Register.mtime _).get? Register.sig_seip = _
    simp only [Std.ExtDHashMap.get?_insert, show (mtime == sig_seip) = false from by decide,
      show (mcycle == sig_seip) = false from by decide, dif_neg, reduceCtorEq,
      not_false_eq_true, hv]
  simp only [EStateM.run] at hcd
  exact hcd

end Vsa.Sim
