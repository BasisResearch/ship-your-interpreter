# M1 init footprint — register writes during `Vsa.setupElf`

Scope: the **executable** model `riscv-lean/Lean_RV64D_executable/` (the one `Vsa.Elf`
uses via `open LeanRV64DExecutable`). The non-executable `Lean_RV64D/` model is
similar but differs (see "Executable vs non-executable" below); all file:line
citations are the executable tree unless noted.

`setupElf` (`Vsa/Elf.lean:66`) runs, in program order:

```
sail_model_init ()          -- LeanRV64DExecutable.lean:211
initializeRegisters elf     -- lean_emulator/LeanRiscv.lean:87
init_model ""               -- LeanRV64DExecutable/Model.lean:211  → reset ()  (Model.lean:204)
cycle_count ()              -- Sail/ConcurrencyInterfaceV1.lean:285  (no register write)
writeReg PC (e_entry)       -- Vsa/Elf.lean:72
```

`init_model ""` first `assert (← config_is_valid ())` (no register writes; returns
`true` for the default config, `ValidateConfig.lean:1308`), then calls `reset ()`,
which runs `reset_sys (); reset_vmem (); reset_elp (); ext_reset ()`
(`Model.lean:204`). `ext_reset` is a pure no-op (`StepExt.lean:209`), `cycle_count`
only bumps the non-register `cycleCount` field, `initialize_registers ()` inside
`sail_model_init` (line 315) is `()` — a no-op (`LeanRV64DExecutable.lean:208`).

Because of the phase order, **every register `reset_sys`/`reset_tvecs`/`reset_pmp`
reads was already written by `initializeRegisters`** (which runs before
`init_model`), so no read throws. See "Surprises" for the fragility this implies.

Config resolution: `undefined_*` are **not** nondeterministic here — `SailM` uses
`trivialChoiceSource` (`Defs.lean:1632`) whose `choose` returns `0`/`false`/`""`
for every primitive (`Sail/ConcurrencyInterfaceV1.lean:14-25`). So
`undefined_bitvector n = (0 : BitVec n)` (line 156), `undefined_bool () = false`
(141), `undefined_bit () = 0#1` (138), `undefined_vector n a = Vector.replicate n a`
(159). Every `undefined_*` register below is therefore a **concrete zero/false**
value (structs are the all-zero struct).

---

## 1. Register → final value → write site(s)

Writes are listed in program order; the **final** value is the last write. Notation:
`smi` = `sail_model_init` (LeanRV64DExecutable.lean), `ir` = `initializeRegisters`
(lean_emulator/LeanRiscv.lean), `rs` = `reset_sys` (SysControl.lean), plus the
named reset helper.

### Priority registers (GoodState invariant)

| Register | Final value (Lean expr) | Write site(s) |
|---|---|---|
| `cur_privilege` | `Privilege.Machine` | ir writes `undefined_Privilege ()` (=`.User`, first ctor) `LeanRiscv.lean:142`; **rs overwrites** → `Machine` `SysControl.lean:719` |
| `misa` | `smi` seed then **`reset_misa` overwrites** bits per `hartSupports`: `_update_Misa_MXL (Mk_Misa 0) (architecture_bits_forwards RV64)` with bits set A=1,C=1,B=1,M=1,U=1,S=1,V=1,F=1,D=1 (and E=0, bit8 = ¬E =1). See note. | smi `LeanRV64DExecutable.lean:213`; **final** = `reset_misa` `SysControl.lean:688-713` (called from rs:724) |
| `mstatus` | smi seed `_update_Mstatus_UXL (_update_Mstatus_SXL (Mk_Mstatus 0) uxl) sxl` with `sxl=sxl=architecture_bits_forwards RV64` (since xlen=64, S and U supported), then **rs clears bit 3 (MIE) and bit 17 (MPRV)** via `updateSubrange … 0#1` | smi `LeanRV64DExecutable.lean:214`; rs `SysControl.lean:720-721` |
| `mstatush` | **register does not exist** in this model (RV64 folds it into `mstatus`); the SXL/UXL/`mstatush` write-callback is a no-op | — |
| `mie` | `Mk_Minterrupts 0` (`undefined_Minterrupts () = 0`) | ir `LeanRiscv.lean:144` |
| `mip` | `Mk_Minterrupts 0` | ir `LeanRiscv.lean:145` |
| `mideleg` | `Mk_Minterrupts 0` | ir `LeanRiscv.lean:147` |
| `medeleg` | `Mk_Medeleg 0` | ir `LeanRiscv.lean:146` |
| `mseccfg` | smi `legalize_mseccfg (Mk_Seccfg 0) 0`, then **rs clears bits 8,9 and (Zicfilp⇒) bit 10** to 0 | smi `LeanRV64DExecutable.lean:236`; rs `SysControl.lean:731-737` (Zicfilp=`true`, so bit-10 branch taken) |
| `satp` | `(0 : BitVec 64)` | ir `LeanRiscv.lean:249` |
| `hart_state` | `HART_ACTIVE ()` | smi `LeanRV64DExecutable.lean:314`; also rs-sibling `reset` `Model.lean:205` |
| `htif_done` | `false` (smi `false`; ir `undefined_bool ()=false`) | smi `LeanRV64DExecutable.lean:248`; ir `LeanRiscv.lean:245` |
| `htif_exit_code` | `(0 : BitVec 64)` | smi `:249`; ir `LeanRiscv.lean:246` |
| `htif_cmd_write` | `(0 : BitVec 1)` | smi `:250`; ir `LeanRiscv.lean:247` |
| `htif_payload_writes` | `(0 : BitVec 4)` | smi `:251`; ir `LeanRiscv.lean:248` |
| `htif_tohost` | **ELF-dependent**: `BitVec.ofNat 64 tohost_addr` (`.tohost` section addr) | smi `0` `:247`, ir `LeanRiscv.lean:100` |
| `htif_tohost_base` | **ELF-dependent**: `some (trunc 64 tohost_addr)` via `enable_htif` | smi `none` `:246`; ir/enable_htif `LeanRiscv.lean:101`, `Platform.lean:209` |
| `pmpcfg_n` | `Vector.replicate 64 (Pmpcfg_ent 0)` then **`reset_pmp` sets A=OFF (bits) and L=0 on indices 0..62** (loop `[0:63)`, index 63 left as 0) | ir `LeanRiscv.lean:169`; rs/`reset_pmp` `PmpControl.lean:348-359` |
| `pmpaddr_n` | `Vector.replicate 64 (0 : BitVec 64)` (untouched by reset_pmp) | ir `LeanRiscv.lean:170` |
| `mtimecmp` | `(0 : BitVec 64)` | ir `LeanRiscv.lean:243` |
| `mtime` | `(0 : BitVec 64)` | ir `LeanRiscv.lean:157` |
| `mcycle` | `(0 : BitVec 64)` | ir `LeanRiscv.lean:156` |
| `minstret` | `(0 : BitVec 64)` | ir `LeanRiscv.lean:158` |
| `minstret_increment` | `false` (`undefined_bool`) | ir `LeanRiscv.lean:159` |
| `nextPC` | smi none; ir `0`; **rs sets `pc_reset_address` (=0)** | ir `LeanRiscv.lean:110` (=0); rs `SysControl.lean:727` (= `pc_reset_address` = 0) |
| `PC` | **ELF-dependent, final = `(elf.file_header.e_entry : UInt64).toBitVec`** (setupElf re-writes it after reset zeroed it) | ir `:99`; rs sets to `pc_reset_address`=0 `SysControl.lean:726`; **setupElf overwrites** `Vsa/Elf.lean:72` |

### Other registers written during init

| Register | Final value | Site |
|---|---|---|
| `fp_rounding_global` | `fp_rounding_default` | smi `:212` |
| `hstateen0..3` | `Mk_Hstateen* 0` | smi `:223-226` |
| `mstateen0..3` | `0` (smi `Mk_Mstateen* 0`; **`reset_stateen` overwrites → `zeros 64`**) | smi `:227-230`; `reset_stateen` `StateenRegs.lean:641-644` (via rs:738) |
| `sstateen0..3` | `Mk_Sstateen* 0` (BitVec 32) | smi `:231-234` |
| `senvcfg` | `legalize_senvcfg (Mk_SEnvcfg 0) 0` | smi `:235` |
| `menvcfg` | `legalize_menvcfg (Mk_MEnvcfg 0) 0` | smi `:237` |
| `mvendorid` | `to_bits_checked (l:=32) 0` = `0` | smi `:238` |
| `mimpid`,`marchid`,`mhartid` | `to_bits_checked (l:=64) 0` = `0` | smi `:239-241` |
| `mconfigptr` | `(0 : BitVec 64)` | smi `:242` |
| `sig_meip`,`sig_seip` | `0#1` | smi `:243-244` |
| `pc_reset_address` | `(0 : BitVec 64)` | smi `:245` |
| `pma_regions` | 3-element `List PMA_Region` literal (CLINT/IO/MainMemory, all fields concrete) | smi `:252-312` |
| `tlb` | `Vector.replicate (2^6) none` (smi `vectorInit none`; `reset_TLB` rewrites same) | smi `:313`; `reset_TLB` `VmemTlb.lean:248` (via reset_vmem `Vmem.lean:539`) |
| `x1..x31` | `(0 : BitVec 64)` each | ir `LeanRiscv.lean:111-141` |
| `cur_inst` | `(0 : BitVec 64)` | ir `LeanRiscv.lean:143` |
| `mtvec` | ir `undefined_Mtvec ()=0`; **`reset_tvecs` sets bits[1:0]=TV_Direct** (direct mode supported) | ir `:148`; `reset_tvecs` `SysExceptions.lean:265-269` (via rs:722) |
| `stvec` | ir `0`; **`reset_tvecs` sets bits[1:0]=TV_Direct** | ir `:160`; `reset_tvecs` `SysExceptions.lean:277-280` |
| `mcause` | ir `undefined_Mcause ()=0`; **rs overwrites `zeros 64`** | ir `:149`; rs `SysControl.lean:728` |
| `mepc`,`mtval`,`mscratch` | `(0 : BitVec 64)` | ir `:150-152` |
| `scounteren`,`mcounteren` | `Mk_Counteren 0` | ir `:153-154` |
| `mcountinhibit` | `Mk_Counterin 0` | ir `:155` |
| `sscratch`,`sepc`,`stval` | `(0 : BitVec 64)` | ir `:161-164` |
| `scause` | `Mk_Mcause 0` | ir `:163` |
| `tselect` | `(0 : BitVec 64)` | ir `:165` |
| `vstart` | ir `0` (16b); **rs `zeros 64`** | ir `:166`; rs `SysControl.lean:739` |
| `vl` | ir `0`; **rs `zeros 64`** | ir `:167`; rs `SysControl.lean:740` |
| `vtype` | ir `undefined_Vtype ()=0`; **rs sets vill bit (msb=1), rest 0** | ir `:168`; rs `SysControl.lean:743-749` |
| `vcsr` | ir `undefined_Vcsr ()=0`; **rs clears bits [2:0]=0** | ir `:203`; rs `SysControl.lean:741-742` |
| `vr0..vr31` | `(0 : BitVec 65536)` | ir `:171-202` |
| `f0..f31` | `(0 : BitVec 64)` | ir `:208-239` |
| `fcsr` | `Mk_Fcsr 0` | ir `:240` |
| `mcyclecfg`,`minstretcfg` | `Mk_CountSmcntrpmf 0` | ir `:241-242` |
| `stimecmp` | `(0 : BitVec 64)` | ir `:244` |
| `elp` | `landing_pad_bits_backwards NO_LP_EXPECTED` | `reset_elp` `ZicfilpRegs.lean:249` (via reset:208) |
| `rvfi_instruction` | `undefined_RVFI_DII_Instruction_Packet ()` (zero struct) | ir `:103` |
| `rvfi_inst_data`,`rvfi_pc_data`,`rvfi_int_data`,`rvfi_mem_data` | zero structs | ir `:104-108` |
| `rvfi_int_data_present`,`rvfi_mem_data_present` | `false` | ir `:107,109` |

Note on `misa`: the prior experiment value
`_update_Misa_MXL (Mk_Misa (BitVec.zero 64)) (architecture_bits_forwards RV64)` is
only the **`sail_model_init` seed** (line 213 — verified identical). It is **not**
the value after init: `reset_misa` (`SysControl.lean:688-713`, run from
`reset_sys:724`) read-modify-writes ~13 subranges from `hartSupports`
(`PlatformConfig.lean:1533`), turning on A/M/F/D/C/B/S/U/V bits and bit 8.
Similarly `cur_privilege = Machine` (verified `SysControl.lean:719`) and the
`mseccfg` seed `Mk_Seccfg 0` (verified `:236`) match, but `mseccfg`'s **final**
value has bits 8/9/10 cleared by `reset_sys`.

---

## 2. Hot-path registers NOT written during init

Only **two** registers in the `Register` enum (`Defs.lean:1247-1426`, 109 ctors)
are never written by the init sequence:

- **`mhpmcounter`** — its only writers are the Zihpm CSR handlers
  (`ZicsrInsts.lean:5397,5406`), read-modify-write. In `LeanRiscv.lean:205` the
  init write is **commented out**.
- **`mhpmevent`** — same; init write commented out at `LeanRiscv.lean:204`,
  writers only at `ZicsrInsts.lean:5451,5464`.

A `readReg mhpmevent`/`readReg mhpmcounter` on the post-init state throws
(`σ.regs.get? = none`). This is only reachable via `hpmcounter`/`mhpmevent` CSR
access — **not** on the fetch/decode/ADDI/dispatchInterrupt/pmpCheck hot path, so
it does not block the M1 ADDI proof, but any GoodState invariant that quantifies
over "all registers defined" must exclude these two (or the proof must show the
WHILE program never touches those CSRs).

Everything else on the hot path is written: `try_step` reads
`cur_privilege, hart_state, minstret_increment, PC` (`Step.lean:398-457`);
`should_inc_minstret/mcycle` read `mcountinhibit, minstretcfg, mcyclecfg`
(`Platform.lean:527-533`); `dispatchInterrupt→getPendingSet` reads
`mip/mie/mideleg/medeleg/mstatus` (`SysControl.lean:510,533`); `pmpCheck` reads
`pmpcfg_n/pmpaddr_n/mseccfg` (`PmpControl.lean:294`); ADDI (`execute_ITYPE`,
`InstsEnd.lean:6809`) reads `x1..x31` via `rX` (`Regs.lean:615`, x0→`zero_reg`) and
writes via `wX` (`Regs.lean:653`, x0→no-op). All of these are initialized.

---

## 3. Config constants

| Constant | Value | file:line |
|---|---|---|
| `plat_insns_per_tick` | `2` (`nat1`) | `PlatformConfig.lean:2722` |
| `xlen` | `64` | `Xlen.lean:204` |
| `get_config_print_instr ()` | `false` | `Prelude.lean:212` |
| `get_config_rvfi ()` | **not defined** in exec model; RVFI gated by other means. `get_config_print_*` all `false`: `print_clint:215, print_exception:218, print_interrupt:221, print_htif:224, print_pma:227, print_pmp:230` | `Prelude.lean` |
| `get_config_print_platform` | **does not exist** in this model (no such symbol) | — |
| `get_config_use_abi_names ()` | `false` | `Prelude.lean:236` |
| `base_E_enabled` | `false` | `PlatformConfig.lean:702` |
| `vector_support_level` | `Full` (⇒ `hartSupports Ext_V = true`) | `Vlen.lean:212` |
| `sys_enable_experimental_extensions ()` | `false` | `RiscvExtrasExecutable.lean:43` |
| `plat_mtvec_direct_mode_supported` | `true` (⇒ tvecs reset to TV_Direct) | `PlatformConfig.lean:206` |
| `hartSupports` true for | M,A,F,D,B,V,S,U,Zicfilp,Zicsr,Zicntr,Zihpm,… (see `PlatformConfig.lean:1533`); false for H,Zmmul,Zaamo,Zalrsc,Zfinx,Zdinx,Zba,Zbb,Zbs,Zhinx | `PlatformConfig.lean:1533-1612` |

`get_config_rvfi`: the task named this, but the executable model has no
`get_config_rvfi`; only the non-executable `Lean_RV64D/Prelude.lean:233` defines it
(`false`). `init_model ""` means the **default (empty) config**: the assert message
branch `if config_filename == "" then "Default config"` (`Model.lean:213`); no file
is read — all config comes from the compiled-in constants above.

---

## 4. Surprises relevant to symbolic execution

1. **`misa` / `mseccfg` / `mstatus` finals differ from the `sail_model_init`
   seeds.** `reset_misa` (`SysControl.lean:688`) rewrites `misa` from `hartSupports`;
   `reset_sys` clears `mstatus` bits 3,17 and `mseccfg` bits 8,9,10. Any invariant
   using the E1i seed values for `misa`/`mseccfg` is describing the pre-`reset()`
   state, not the post-`setupElf` state. Only `cur_privilege=Machine` is
   seed-and-final consistent.

2. **Double initialization / write-ordering matters.** Many registers are written
   twice (`sail_model_init` then `initializeRegisters`, or `initializeRegisters`
   then `reset_sys`). `initializeRegisters` runs **between** `sail_model_init` and
   `init_model`, which is *not* the reference emulator's own `my_main` ordering but
   matches `runElf64` (`LeanRiscv.lean:280-283`). The final value is always the last
   write in this fixed order — deterministic, but you must model all three phases.

3. **`reset_sys`/`reset_tvecs`/`reset_pmp` read registers they don't initialize**
   (`mstatus, mseccfg, mtvec, stvec, vcsr, vtype, pmpcfg_n`). This only works
   because `initializeRegisters` pre-populated them. If a symbolic-execution proof
   reorders or drops `initializeRegisters`, these reads become `none` and throw.
   `reset_pmp` iterates indices **0..62 only** (loop `[0:63)`), so `pmpcfg_n[63]`
   keeps its `initializeRegisters` value (A/L bits **not** forced OFF).

4. **`undefined_*` is fully concrete here.** With `trivialChoiceSource`, every
   `undefined_bitvector/bool/bit/vector` is a definite zero/false/replicate — there
   is **no** nondeterminism to quantify over. Symbolic execution can treat all ir
   writes as literal zeros. (This is config-specific: a non-trivial `ChoiceSource`
   would make these registers genuinely arbitrary.)

5. **ELF-dependent writes:** only `PC` (=`e_entry`), `htif_tohost` and
   `htif_tohost_base` (=`.tohost` section address). If the ELF lacks a `.tohost`
   section, `initializeRegisters` **panics** (`LeanRiscv.lean:96`). Everything else
   is ELF-independent.

6. **`mhpmcounter`/`mhpmevent` unwritten** (§2) — the only `get? = none` registers.

7. **`nextPC` ends at 0, `PC` ends at `e_entry`.** `reset_sys` sets both to
   `pc_reset_address` (=0), then `setupElf` re-writes only `PC`. So immediately
   post-init `nextPC = 0 ≠ PC`; `try_step`/`tick_pc` reconcile them on the first
   step. Don't assume `nextPC = PC` at the initial state.

### Executable vs non-executable (both trees exist; Vsa uses the executable one)
The non-executable `Lean_RV64D/LeanRV64D.lean:384` `sail_model_init` additionally
writes `ssp` (line 487) and its `initialize_registers` (line 306) is a large
function writing `mhpmevent`, `mhpmcounter`, `srmcfg`, etc. (lines 380-382). The
**executable** `sail_model_init` writes neither `ssp` (not even a register in the
exec `Register` enum) nor calls a real `initialize_registers` — its line 315
`initialize_registers ()` is the no-op `()` from `LeanRV64DExecutable.lean:208`.
The two `mhpm*` registers therefore end up written in the non-exec model but
**unwritten** in the exec model that `Vsa` actually runs.
