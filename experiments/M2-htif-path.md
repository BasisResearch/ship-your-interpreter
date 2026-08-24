# M2 — HTIF store path (SD/SW hitting the `tohost` mailbox, M-mode / Bare / aligned)

Model root: `riscv-lean/Lean_RV64D_executable/LeanRV64DExecutable/`
PreSail library: `riscv-lean/lean-sail/Sail/ConcurrencyInterfaceV1.lean`
Companion (READ path): `experiments/M1-fetch-path.md`. Gotchas: `experiments/M1-proof-gotchas.md`.

Fixed conditions ("HTIF hot path"), all discharged by `Vsa.Sim.GoodState`
(`Vsa/Sim/GoodState.lean:36`) plus the store-specific facts:

- `cur_privilege = Machine`; `mstatus.MPRV = 0` (`initMstatus = 0x0000000a00000000`,
  bit 17 clear, `Vsa/Sim/InitValues.lean:37`) ⇒ `effectivePrivilege (Store Data) … = Machine`
  (SysControl.lean:214, guard `bne … InstructionFetch && MPRV==1` = false).
- Translation is **Bare** by privilege (`translationMode Machine = Bare`, Vmem.lean:366) ⇒
  `do_split_access = false`, no page-crossing split (VmemUtils.lean:353–354).
- `htif_tohost_base = some 0x8001ad00` = `Vsa.Sim.tohostAddr` (`InitValues.lean:56`),
  register `htif_tohost` present (GoodState pins its value but the store overwrites it).
- The `tohost` store is the **8-byte, 8-aligned** store the C runtime emits
  (`sd rs2, tohost`): `paddr == base`, `width == 8`, `tmod(paddr,8)=0`.
- HTIF window `[0x8001ad00, 0x8001ad08)` lies **inside** the RAM PMA region
  `[0x80000000,0x100000000)` (`initPmaRegions`, Hooks.lean:206) which is `writable = true`
  — HTIF is an in-RAM mailbox, so `pmaCheck (Store Data)` passes on the RAM region and then
  `within_mmio_writable` re-routes the actual effect to `htif_store` (Mem.lean:559).
- `get_config_print_htif () = false` (Prelude.lean:224), `get_config_print_pma/pmp () = false`,
  `get_config_rvfi () = false` — every `print_endline` inside `htif_store`/`pmaCheck` is dead,
  and (critically) `print_endline` is the **no-op** `fun _ => ()` (Sail.lean:11), NOT the
  `sailOutput` push. Only `print_effect` (via `plat_term_write`) mutates `sailOutput`.

Under these, an 8-byte `tohost` store takes the single-iteration write loop
(`split_misaligned = (1,8)`, N=1) → MMIO branch → `htif_store` → command dispatch.

---

## The chain (numbered, 5 points each)

### 1. `execute_STORE (imm rs2 rs1 width) : SailM ExecutionResult` — InstsEnd.lean:6582
1. The SD/SW execute clause (dispatched at InstsEnd.lean:7046; SD = `STORE(imm,rs2,rs1,8)`,
   SW = width 4). `offset := sign_extend imm`.
2. Reads GPR **`rs2`** via `rX_bits rs2` (6585) for the store data; `rs1` read later inside
   `vmem_write`→`get_transformed_data_addr`→`ext_data_get_addr`. No reg writes here.
3. Branches: `assert (width ≤ xlen_bytes)` (6584, `8 ≤ 8` ✓). `data := extractLsb (rX_bits rs2) (width*8-1) 0`
   — for SD this is the full 64-bit `rs2`. Then match on `vmem_write …`:
   `.Ok _ ⇒ RETIRE_SUCCESS` (6587), `.Err e ⇒ e` (6588). Console-putchar and exit **both**
   return `RETIRE_SUCCESS` (the store "succeeds", `Ok true`).
4. **SailM** (plain `do`).
5. Delegates the effective-address + write to `vmem_write` (#2). Access type is
   `Store Data` (`MemoryAccessType.Store`, Defs.lean:211; `.Data` payload), `aq=rl=res=false`.

   Beyond the write, the execute clause needs: (a) effective-address computation
   `rs1 + sign_extend(imm)` (inside `get_transformed_data_addr`, VmemUtils.lean:421 →
   `ext_data_get_addr` adds base+offset, then `transform_effective_address` = identity in
   M-mode); (b) the width assert (compile-time true for 8); (c) misalignment check happens in
   `vmem_write_addr` (#3), passing for the 8-aligned tohost address.

### 2. `vmem_write (rs_addr offset width data access aq rl res) : SailM (Result Bool ExecutionResult)` — VmemUtils.lean:442
1. Compute the virtual address then delegate to `vmem_write_addr`.
2. No direct reg read/write; `get_transformed_data_addr` reads **`rs1`** (base GPR) and
   (via `effectivePrivilege` in `transform_effective_address`) **`mstatus`,`cur_privilege`**.
3. `get_transformed_data_addr rs1 offset (Store Data) width` (444) ⇒ `.Ext_DataAddr_OK vaddr`
   on the hot path (`ext_data_get_addr` never errors for a plain store; `.Ext_DataAddr_Error`
   throws at 446). `vaddr = rs1 + offset = 0x8001ad00`.
4. **SailME** (`SailME.run do`). One throw (447), not taken.
5. Delegates to `vmem_write_addr` (#3).

### 3. `vmem_write_addr (vaddr width data access aq rl res) : SailM (Result Bool ExecutionResult)` — VmemUtils.lean:336
1. Alignment check, page-split logic, translate, EA, write.
2. Reads **`mstatus`,`cur_privilege`** (352, via `effectivePrivilege`; again 383 in the
   reservation branch, not taken). No writes here (delegates).
3. Branches:
   - 337 `is_aligned_vaddr vaddr 8`: `tmod(0x8001ad00,8)=0` ⇒ **aligned** ⇒ skip the
     `plat_misaligned_exception` throw block (338–347). (For a *misaligned* store this is
     where `E_SAMO_Addr_Align`/`E_SAMO_Access_Fault` would fire — but tohost is 8-aligned.)
   - 351 `split_on_page_boundary` ⇒ `(in_page_bytes=8, next_page_bytes=0)` (intra-page).
   - 353–354 `do_split_access = (bne (translationMode Machine) Bare) && (next>0)` = `false && _`
     = **false** ⇒ both split blocks (355–366, 406–417) are `pure write_success` no-ops.
   - 367–370 `access_width := width = 8` (not split).
   - 371–405 the main block: `translateAddr vaddr (Store Data)` ⇒ `.Ok (paddr, PBMT_PMA, _)`
     with `paddr = 0x8001ad00` (Bare); `res=false` ⇒ skip reservation branch (379–388);
     `mem_write_ea paddr 8 …` ⇒ `.Ok ()` (#4); then
     `write_value := extractLsb data (8*8-1) 0 = data`;
     `mem_write_value paddr 8 data (Store Data) PBMT_PMA false false false` ⇒ `.Ok true` (#5).
   - 418 `pure (Ok true)`.
4. **SailME** (`SailME.run do`). Throws: misalignment (342/345), translate-err (374), EA-err
   (393), write-err (401), reservation-fault (386) — **none reachable** on the hot path.
5. Delegates translate to `translateAddr` (Vmem.lean:499, same Bare lemma as fetch, #M1-4),
   EA to `mem_write_ea` (#4), the value write to `mem_write_value` (#5).

### 4. `mem_write_ea (paddr width access pbmt aq rl con) : SailM (Result Unit (physaddr × ExceptionType))` — Mem.lean:495
1. "Write effective address" announce: PMA/PMP-check + `write_ram_ea` (a pure no-op).
2. Reads **`mstatus`,`cur_privilege`** (496 via `effectivePrivilege`), **`pma_regions`**
   (via `check_pma_with_pmp_priority`→`pmaCheck`, #6), **`pmpcfg_n`,`pmpaddr_n`** only if
   `pmaCheck` failed (not reached). No writes (`write_ram_ea` = `()`).
3. `check_pma_with_pmp_priority (Store Data) PBMT_PMA Machine paddr 8 false` ⇒
   `.Ok {splittable=CannotSplit, granule_size_exp=0}` (RAM region writable; aligned ⇒
   `mag_pma_check = Ok(CannotSplit,0)`, Pma.lean:389). `split_misaligned = (1,8)` (N=1).
   Loop (509–527, `untilFuelM fuel:=1`) runs once: `pmpCheck paddr 8 (Store Data) Machine ⇒ none`
   (M-mode allow, PmpControl.lean) ⇒ `write_ram_ea = ()`; `offset==last` ⇒ finished.
4. **SailME** (`SailME.run do`). Throws: PMA-err (500), pmpCheck-err (516) — not reached.
5. `pure (Ok ())`. (This is announce-only; the byte effect is in #5. `write_ram_ea` never
   writes state.)

### 5. `mem_write_value → …_meta → …_priv_meta → checked_mem_write` — Mem.lean:606→600→584→532
1. `mem_write_value` (606) → `mem_write_value_meta` (600, adds `default_meta`) →
   `mem_write_value_priv_meta` (584, resolves priv, calls `checked_mem_write`, then fires
   `mem_write_callback` — a no-op) → `checked_mem_write` (532) does the checked, split write.
2. `mem_write_value_meta` reads **`mstatus`,`cur_privilege`** (601). `checked_mem_write` reads
   **`pma_regions`** (via `check_pma_with_pmp_priority`), **`pmpcfg_n`,`pmpaddr_n`** (pmpCheck),
   `htif_tohost_base` (via `within_mmio_writable`→`within_htif_writable`), plus everything
   `htif_store` touches (#7). Writes: **all state mutation is inside `htif_store`** for the
   tohost address.
3. `checked_mem_write` branches (width=8, aligned, Machine):
   - 534 `check_pma_with_pmp_priority (Store Data) … ⇒ .Ok {CannotSplit,0}`.
   - 538 `split_misaligned = (1,8)` ⇒ N=1 (single loop iteration).
   - loop 546–579: 552 `pmpCheck paddr 8 (Store Data) Machine ⇒ none`;
     `write_value := extractLsb data … = data`;
     **559 `within_mmio_writable paddr 8`** — for tohost this is **`true`** (address in the
     HTIF window) ⇒ take the MMIO branch 562 `mmio_write paddr 8 data` (#6→#7); the
     `write_ram` else-branch (567) is **not** taken (that is the branch for an ordinary
     RAM `sd`, which pushes bytes via `writeBytes`, ConcurrencyInterfaceV1.lean:200).
     `.Ok v ⇒ write_success && v`.
   - 580 `pure (Ok write_success)` = `Ok true`.
4. `mem_write_value*` are plain **SailM** `do`; `checked_mem_write` is **SailME** (`SailME.run`,
   throws at 536, 553, 564 — none reached).
5. `mmio_write` (#6) dispatches to `htif_store` (#7).
   `mem_write_callback` (Callbacks.lean, no-op) and `write_ram_ea` never touch `sailOutput`.

### 6. `mmio_write (paddr width data) : SailM (Result Bool (physaddr × ExceptionType))` — Platform.lean:726
1. MMIO write dispatcher (CLINT / SIG / HTIF).
2. Reads region-config constants + **`htif_tohost_base`** (via `within_htif_writable`, 735).
3. 727 `within_clint ⇒ false` (tohost ∉ CLINT); 731 `within_sig ⇒ false`;
   735 `within_htif_writable paddr 8 ⇒ true` ⇒ **`htif_store paddr 8 data`** (736).
   Else-branch (737, `E_SAMO_Access_Fault`) not taken.
4. **SailM** (plain `do`).
5. Delegates to `htif_store` (#7).

### 7. `htif_store (addr width data) : SailM (Result Bool (physaddr × ExceptionType))` — Platform.lean:614
1. The HTIF device store: latch `tohost`, then — when a command is complete — dispatch it
   (console putchar / syscall exit). **This is the heart of M2.**
2. **Reads**: `htif_tohost_base` (624), `htif_payload_writes` (632/640/641/650/651/657/658),
   `htif_cmd_write` (656), `htif_tohost` (639/642/649/653/661).
   **Writes**: `htif_cmd_write` (631/652), `htif_payload_writes` (632/640/641/650/651),
   `htif_tohost` (633/642/653), and on dispatch `htif_done` (675), `htif_exit_code` (676);
   plus `plat_term_write` → **`sailOutput`** for the console command, and `reset_htif` (690)
   zeroes `htif_cmd_write`/`htif_payload_writes`/`htif_tohost` on the term path.
3. Branches — two phases:

   **Phase A (latch), width=8, paddr==base (628–633):**
   ```
   writeReg htif_cmd_write 1#1
   writeReg htif_payload_writes (htif_payload_writes + 1)
   writeReg htif_tohost (zero_extend data)        -- 64-bit ⇒ = data
   ```
   (The 4-byte low/high sub-word branches 636–653 are for `sw`; the tohost store the C
   runtime emits is the 8-byte one, so Phase A is the single `writeReg htif_tohost data`.)

   **Phase B (dispatch), guard 656–658:**
   `(htif_cmd_write==1 && payload_writes>0) || payload_writes>2`. After Phase A,
   `htif_cmd_write=1` and `payload_writes ≥ 1 > 0` ⇒ guard **true** ⇒ enter dispatch.
   `cmd := Mk_htif_cmd htif_tohost = data`. Match `_get_htif_cmd_device cmd = data[63:56]`
   (Platform.lean:558):

   **(a) Console putchar** — `device = 0x01`, term branch (678–690):
   match `_get_htif_cmd_cmd cmd = data[55:48]` (Platform.lean:548):
   `0x00 ⇒ ()`; `0x01 ⇒ plat_term_write (data[47:0][7:0])` (688) — writes the byte to console;
   default ⇒ `print_effect "Unknown term cmd: …"`. Then `reset_htif ()` (690).

   **(b) Exit** — `device = 0x00`, syscall-proxy branch (663–677):
   `if (_get_htif_cmd_payload cmd)[0] == 1` (672, payload = `data[47:0]`, bit 0):
   ```
   writeReg htif_done true                                       (675)
   writeReg htif_exit_code ((zero_extend (payload) : BitVec 64) >>> 1)   (676)
   ```
   else `()`. (No `reset_htif` on the exit branch.)

   `_ ⇒ print_effect "htif-???? cmd: …"` (691) for other devices (not on our path).
4. **SailME** (`SailME.run do`). Its one throw is the 4-byte-mismatch `E_SAMO_Access_Fault`
   (655), only reachable for a `sw` to an address that is neither `base` nor `base+4`; the
   8-byte tohost store never reaches it.
5. `pure (Ok true)` (693). State mutation: `writeReg` = `modify {σ with regs := σ.regs.insert …}`
   (ConcurrencyInterfaceV1.lean:169); `plat_term_write c = print_effect "{Char.ofNat c.toNat}"`
   → `modify {σ with sailOutput := σ.sailOutput.push str}` (ConcurrencyInterfaceV1.lean:293).

### 8. `plat_term_write (c : BitVec 8) : SailM Unit` — RiscvExtrasExecutable.lean:32
1. The console-output primitive: turn the byte into a 1-char string and push it.
2. No reg access.
3. Straight-line: `print_effect s!"{Char.ofNat c.toNat}"`.
4. **SailM** (= `PreSailM`).
5. **THE sailOutput append**: `print_effect str` (ConcurrencyInterfaceV1.lean:293) =
   `modify fun s => { s with sailOutput := s.sailOutput.push str }`. `sailOutput : Array String`
   (ConcurrencyInterfaceV1.lean:107). **Granularity: one `Array String` element per console
   `putchar` = per byte** (a single-character `String`). `Machine.output σ = String.join
   σ.sailOutput.toList` (Vsa/Machine.lean:36) concatenates them, so per-byte push, per-byte
   growth of the joined output.

---

## PMA/PMP re-check on the store path (vs fetch)

**Yes — the store re-runs the same PMA and PMP checks as the fetch path, twice** (once in
`mem_write_ea` #4, once in `checked_mem_write` #5), via the *identical* callees:

- `check_pma_with_pmp_priority` (Mem.lean:391) → `pmaCheck` (Mem.lean:254) → `pmpCheck`
  (PmpControl.lean:294). Same functions as fetch's `checked_mem_read` (M1 #7–#9).
- **`pmpCheck` is reusable verbatim**: `Vsa.Sim.pmp_allows` (Pmp.lean:114) is proved for
  *arbitrary `access`* (`access : MemoryAccessType mem_payload`), Machine priv, reset PMP ⇒
  `pure none`. It applies to `Store Data` with no change. **This is the single biggest reuse.**
- **`pmaCheck` differs by access type**: the fetch lemma `pmaCheck_ram_exec` (Hooks.lean:193)
  hard-codes `InstructionFetch ()` and checks `attributes.executable`. For the store we need a
  **`Store Data` variant** that checks `attributes.writable` (Mem.lean:278–281) — same RAM
  region (`initPmaRegions`, writable=true), width 8, `mag_pma_check` via `is_aligned_paddr`
  ⇒ `Ok(CannotSplit,0)`. Structurally the same proof, different `canAccess` arm.
- **Region membership differs from fetch**: fetch used `within_mmio_readable = false` to take
  the RAM read branch. The tohost store uses `within_mmio_writable = **true**` (it IS in the
  HTIF window) to take the MMIO/`htif_store` branch. So a **new** `within_mmio_writable`
  characterization lemma is needed (the mirror of `within_mmio_readable_ram_false`
  Hooks.lean:151, but proving `= true` for the tohost address; see Proof plan L2).
  Note `pmaCheck` still runs on the RAM region because the HTIF window lives *inside* RAM
  address space — MMIO routing is a *separate* dispatch in `checked_mem_write:559`, not a PMA
  region.

## What the SW/SD execute clause needs beyond the write

1. **Effective address** = `rX_bits rs1 + sign_extend imm` (execute_STORE:6583 + `ext_data_get_addr`).
   For the tohost store the source is set up so EA = `0x8001ad00`.
2. **Width assert** `width ≤ xlen_bytes` (6584) — compile-time true for 8.
3. **Data extraction** `extractLsb (rX_bits rs2) (width*8-1) 0` (6585) — full 64-bit `rs2` for SD.
4. **Misalignment check** in `vmem_write_addr:337` (`is_aligned_vaddr vaddr 8`) — passes for the
   8-aligned tohost address; the C runtime always stores 64-bit aligned to `tohost`, so
   `plat_misaligned_exception` (VmemUtils.lean:210) is never consulted.
5. **No page split** (Bare ⇒ `do_split_access=false`), **no reservation** (`res=false`).

## Second `htif_done` read in `stepOnce` after an exit store

Trace (`Vsa/Elf.lean:80` `stepOnce i used`):
1. Entry `readReg htif_done` (81): at the start of the step that *executes* the exit store,
   `htif_done` is still `false` (GoodState) ⇒ take the else branch, run `try_step used true`
   (84). Inside `try_step`, the exit `sd` executes → `htif_store` → `writeReg htif_done true`
   (Platform.lean:675) + `htif_exit_code := payload>>1` (676).
2. `if stepped then cycle_count ()` (85) — bookkeeping, no `htif_done` change.
3. **Second `readReg htif_done` (86)**: now `true` ⇒
   `pure (.inl (some (BitVec.toNat (← readReg htif_exit_code)), used + 1))` (87). So
   `stepOnce` returns `.inl (some e, used+1)` where `e = BitVec.toNat htif_exit_code`.
4. In `Vsa/Machine.lean`, `Machine.Halted.mk` (Machine.lean:48–51) fires: its premise is
   `(stepOnce i u).run σ = .ok (.inl (some e, n)) σ'`, which is exactly the shape returned.
   So **`Halted.mk` is the constructor**, with `e` the decoded exit code and `σ'` the post-store
   state (whose `output` is the completed console output). `Step.mk` (Machine.lean:41) does NOT
   fire (it needs `.inr`), consistent with `Step.not_halted`.
   (Note: the exit store's `htif_done := true` happens in the *same* `stepOnce` that executes
   the store — the second read at line 86 catches it, so halting is detected on step `used+1`,
   not deferred to the next entry-check at line 81.)

## How `Machine.output` grows

`Machine.output σ = String.join σ.sailOutput.toList` (Vsa/Machine.lean:36).
`sailOutput : Array String` grows by **one element per console `putchar`** (per byte):
`plat_term_write c` pushes the single-character string `s!"{Char.ofNat c.toNat}"`
(RiscvExtrasExecutable.lean:33 → `print_effect` push, ConcurrencyInterfaceV1.lean:294).
**Granularity: per byte, not per line** — the WHILE runtime calls the HTIF term device once per
character, so a newline is just another 1-char push. `String.join` concatenates in array order,
so `output` after the store = `old_output ++ String.singleton c`.

---

## The exact bit-level HTIF command encodings

`htif_tohost` is a 64-bit command word (`Mk_htif_cmd`, Platform.lean:545, identity). Field layout
(Platform.lean:548/558/568):

| Field | Bits | Extractor |
|---|---|---|
| `device` | `[63:56]` | `_get_htif_cmd_device` (Platform.lean:558) |
| `cmd`    | `[55:48]` | `_get_htif_cmd_cmd` (Platform.lean:548) |
| `payload`| `[47:0]`  | `_get_htif_cmd_payload` (Platform.lean:568) |

### (a) Console putchar of byte `c`
```
device = 0x01   (htif-term)     -- match arm Platform.lean:678
cmd    = 0x01   (write)         -- match arm Platform.lean:688 → plat_term_write
payload= 0x0000_0000_00CC       -- low byte = c; plat_term_write uses payload[7:0]
```
64-bit `data` word: **`0x0101_0000_0000_00CC`** where `CC = c` (the byte written to console).
Effect: `sailOutput.push (String.singleton (Char.ofNat c.toNat))`, then `reset_htif`.
(`_get_htif_cmd_cmd = data[55:48] = 0x01`, `_get_htif_cmd_device = data[63:56] = 0x01`,
`plat_term_write (extractLsb payload 7 0) = plat_term_write c`.)

### (b) Exit with code `e`
The C runtime stores `(e <<< 1) ||| 1` to `tohost`:
```
data   = (e <<< 1) ||| 1
data[0] = 1                                  -- payload bit 0 set ⇒ exit
device = data[63:56] = 0x00 (syscall-proxy)  -- requires e small enough that bit≥56 clear
                                                (match arm Platform.lean:663)
payload= data[47:0]                          -- = (e<<<1)|1  (low 48 bits)
```
Guard `(_get_htif_cmd_payload cmd)[0] == 1` (Platform.lean:672) ⇒ true. Effects:
```
htif_done      := true                                        (Platform.lean:675)
htif_exit_code := (zero_extend (m:=64) payload) >>> 1         (Platform.lean:676)
               =  ((e<<<1)|1) >>> 1  =  e                     (for e fitting in 47 bits)
```
So `htif_exit_code = e`, `htif_done = true`. `stepOnce` then reads `BitVec.toNat e` as the exit
code. (Device `0x00` is selected because `(e<<1)|1` has bits `[63:56] = 0` for `e < 2^55`.)

---

## Register / state footprint of a `tohost` store

Registers **read** on the store path (deduped), with the branch each feeds:

| Register | Where | Feeds |
|---|---|---|
| `rs1` (GPR) | execute_STORE via `ext_data_get_addr` | effective address = rs1+imm |
| `rs2` (GPR) | execute_STORE:6585 (`rX_bits rs2`) | the 64-bit store `data` |
| `mstatus` | vmem_write_addr:352,383; mem_write_ea:496; mem_write_value_meta:601 (via `effectivePrivilege`) | MPRV=0 ⇒ priv=Machine |
| `cur_privilege` | same sites | =Machine ⇒ Bare, pmpCheck-allow, no split |
| `pma_regions` | pmaCheck:256 (twice: ea + checked) | RAM region → `writable=true` |
| `pmpcfg_n`, `pmpaddr_n` | pmpCheck (×16, twice) | M-mode allow (`pmp_allows`) |
| `htif_tohost_base` | within_htif_writable:236; htif_store:624 | = tohostAddr ⇒ MMIO route, `paddr==base` |
| `htif_tohost` | htif_store:661 (`cmd`) | the command word to dispatch (= `data`) |
| `htif_cmd_write` | htif_store:656 | dispatch guard |
| `htif_payload_writes` | htif_store:632(read),657,658 | dispatch guard |

Registers **written** (in program order, all inside `htif_store`):

**Console putchar** (device 0x01, cmd 0x01):
```
htif_cmd_write      := 1#1                          (631)
htif_payload_writes := htif_payload_writes + 1      (632)
htif_tohost         := data                          (633)   -- = zero_extend data
-- Phase B, term/reset:
sailOutput          := sailOutput.push (char c)     (688 → print_effect)
htif_cmd_write      := 0#1  \
htif_payload_writes := 0#4   } reset_htif ()        (690 → Platform.lean:578–581)
htif_tohost         := 0#64 /
```
(net: `htif_cmd_write=0`, `htif_payload_writes=0`, `htif_tohost=0`, one char appended.)

**Exit** (device 0x00, payload[0]=1):
```
htif_cmd_write      := 1#1                          (631)
htif_payload_writes := htif_payload_writes + 1      (632)
htif_tohost         := data                          (633)
-- Phase B, syscall/exit (no reset_htif):
htif_done           := true                          (675)
htif_exit_code      := (zero_extend payload) >>> 1   (676)  -- = e
```

State mutation mechanics: `writeReg r v = modify {σ with regs := σ.regs.insert r v}`
(ConcurrencyInterfaceV1.lean:169); `print_effect str = modify {σ with sailOutput :=
σ.sailOutput.push str}` (293). Both compose into the StateNF insert-chain / array-push spine
(`Vsa/Sim/StateNF.lean`).

---

## Proof plan implications

### Lemma 1 — console putchar appends exactly one character

```lean
theorem htif_store_putchar
    (σ : MState) (c : BitVec 8)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hpw : ∃ v, σ.regs.get? Register.htif_payload_writes = some v)    -- present; value irrelevant
    (hth : ∃ v, σ.regs.get? Register.htif_tohost = some v)
    -- data encodes a term-write of byte c:
    (hdata : data = (0x0101000000000000#64) ||| (BitVec.zeroExtend 64 c)) :
    (htif_store (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8 data).run σ
      = .ok (.Ok true)
          { σ with
            regs := ((σ.regs.insert Register.htif_cmd_write 1#1)
                       .insert Register.htif_payload_writes (…+1)
                       .insert Register.htif_tohost data
                       -- reset_htif overwrites:
                       .insert Register.htif_cmd_write 0#1
                       .insert Register.htif_payload_writes 0x0#4
                       .insert Register.htif_tohost (zeros 64)),
            sailOutput := σ.sailOutput.push (String.singleton (Char.ofNat c.toNat)) }
```
Conclusion: **`sailOutput` gains exactly `String.singleton (Char.ofNat c.toNat)`**, so
`Machine.output σ' = Machine.output σ ++ String.singleton (Char.ofNat c.toNat)`. The register
insert-chain is the two writeReg (631–633) + `reset_htif`'s three (578–581); by StateNF the
duplicate `htif_cmd_write`/`htif_payload_writes`/`htif_tohost` keys collapse to their last value.
Key sub-facts: `_get_htif_cmd_device data = 0x01`, `_get_htif_cmd_cmd data = 0x01`,
`extractLsb (payload) 7 0 = c` — all `by decide`/`bv_decide` from `hdata`.

### Lemma 2 — exit store sets `htif_done` and `htif_exit_code`

```lean
theorem htif_store_exit
    (σ : MState) (e : BitVec 64) (data : BitVec 64)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hpw : ∃ v, σ.regs.get? Register.htif_payload_writes = some v)
    (hth : ∃ v, σ.regs.get? Register.htif_tohost = some v)
    (hdata : data = (e <<< 1) ||| 1#64)
    (hsmall : e.toNat < 2^55) :                       -- device byte stays 0
    (htif_store (physaddr.Physaddr (BitVec.ofNat 64 tohostAddr)) 8 data).run σ
      = .ok (.Ok true)
          { σ with
            regs := ((σ.regs.insert Register.htif_cmd_write 1#1)
                       .insert Register.htif_payload_writes (…+1)
                       .insert Register.htif_tohost data
                       .insert Register.htif_done true
                       .insert Register.htif_exit_code e) }
    -- and σ'.sailOutput = σ.sailOutput  (no console output on exit)
```
Conclusion: `htif_done := true`, `htif_exit_code := e` (from `((zero_extend payload)>>>1) = e`,
discharged by `hdata`+`hsmall` via `bv_omega`/`bv_decide`), `sailOutput` **unchanged**. Feeds
`stepOnce`'s second `htif_done` read (Elf.lean:86) ⇒ `.inl (some e.toNat, used+1)` ⇒
`Machine.Halted.mk`.

### Reusable existing `Vsa/Sim` lemmas

- **`pmp_allows`** (Pmp.lean:114) — verbatim; already `∀ access`, covers `Store Data`.
  Discharges both `pmpCheck` calls (mem_write_ea:515, checked_mem_write:552) in M-mode.
- **`split_misaligned_aligned`** (Hooks.lean:130) — proved for width 4; needs a **width-8
  clone** (`tmod _ 8 = 0`) — same one-line proof (the `Or.inr (Or.inl …)` alignment disjunct).
- **`effectivePrivilege_fetch`/`translationMode_machine`/`translateAddr_machine_fetch`**
  (Hooks.lean:42/56/70) — proved for `InstructionFetch`; need **`Store Data` clones**
  (`effectivePrivilege` guard now `bne (Store Data) IF && MPRV`, still false via MPRV=0;
  `translationMode`/`translateAddr` are access-agnostic ⇒ reuse directly or trivial re-proof).
- **`pmaCheck_ram_exec`** (Hooks.lean:193) — the template for a new **`pmaCheck_ram_write`**
  (`Store Data`, `writable` arm, width 8, aligned) over the same `initPmaRegions`.
- **`within_mmio_readable_ram_false`** (Hooks.lean:151) — the template for the new
  **`within_mmio_writable_htif_true`** (prove `= true` at `paddr = tohostAddr`, width 8:
  `within_clint=within_sig=false`, `within_htif_writable=true`, `width≤8`).
- **StateNF** `get?_insert`/`get?_insert_self` (StateNF.lean:27–30) — consume the register
  insert-chain; `htif_*` keys are distinct `Register` constructors ⇒ `simp` discharges
  disequalities. Add `sailOutput` push to the state-NF handling (it is an `Array.push`, not an
  insert — a new spine element the StateNF lemmas must thread past register inserts, since
  `writeReg` and `print_effect` `modify` different fields; they commute).
- **`readByte_char`/`readBytes_eight`** (MemRead.lean:23/44) — reused if the *ordinary RAM*
  `sd` path (write_ram → `writeBytes`, 8 bytes) is ever characterized; NOT needed for the
  tohost store (MMIO branch), but needed for the general SD lemma.

### Top-3 hard parts

1. **The two-phase `htif_store` control flow with the dispatch guard and nested device/cmd
   matches** (Platform.lean:614–693). The guard `(cmd_write==1 && pw>0) || pw>2` reads
   `htif_payload_writes` *after* Phase A incremented it, and the outer `if` has an 8-byte
   branch feeding a *second* `if` (the device match) — a `SailME.run` boundary wrapping
   sequenced `modify`s where later reads see earlier writes. Must thread `writeReg`→`readReg`
   through the `EStateM` state (read-after-write on `htif_cmd_write`/`htif_payload_writes`/
   `htif_tohost`), then land the 8-bit `device`/`cmd` match arms by `decide` on the concrete
   `data`. The `reset_htif` tail (console path) adds three more inserts that overwrite Phase-A
   keys — StateNF must collapse the duplicated keys to final values.

2. **Two independent state fields mutated in one term** (`regs` via `writeReg`, `sailOutput`
   via `print_effect`). StateNF so far only handles `regs`/`mem` insert-chains; the `sailOutput`
   `Array.push` is a new spine element. The putchar lemma's conclusion is an interleaving of
   register-inserts and one array-push that must commute cleanly so `Machine.output` reads off
   the single appended char — and the exit lemma must prove `sailOutput` is *untouched*
   (no `print_effect` on the syscall-exit arm).

3. **Bit-level command decoding under the model's `extractLsb`/`updateSubrange`/`zero_extend`
   forms.** Proving `_get_htif_cmd_device data = 0x01`, `_get_htif_cmd_cmd data = 0x01`,
   `extractLsb payload 7 0 = c` (putchar) and `payload[0]=1`, `(zero_extend payload)>>>1 = e`
   (exit) from `data = 0x0101…00CC` / `data = (e<<<1)|1`. Per M1 gotchas these route through
   `BitVec.eq_of_toNat_eq; decide` / `bv_decide`, watching `zero_extend a ≠ a` syntactically
   (setWidth) and the `physaddrbits = BitVec (if 64=32 then 34 else 64)` width for `paddr==base`
   comparisons. The `e < 2^55` side-condition (device byte stays 0) is a `bv_omega`, and
   `((e<<<1)|1)>>>1 = e` needs the low-bit-drop identity (bv_decide) — the load-bearing exit
   fact.
