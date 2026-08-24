# M1 — Instruction fetch path (hot path, M-mode / Bare / 4-aligned RV64I)

Model root: `riscv-lean/Lean_RV64D_executable/LeanRV64DExecutable/`
PreSail library: `riscv-lean/lean-sail/Sail/ConcurrencyInterfaceV1.lean`

Fixed conditions assumed throughout ("hot path"):

- `cur_privilege = Machine`
- `satp` mode = Bare (translation off) — but note this is *decided by privilege*, not by satp, on the fetch path (see #4).
- `mstatus.MPRV = 0`, `mstatus.MXR/SUM` irrelevant (Bare).
- `misa.C = 0` at runtime (binary is pure RV64I, compressed not enabled) → `currentlyEnabled Ext_Zca = false`.
- `PC` is 4-aligned (`PC[0]=PC[1]=0`).
- `get_config_rvfi () = false` (compile-time constant), all `get_config_print_* = false`.
- `Ext_Ziccif` supported (`hartSupports Ext_Ziccif = true`).

Under these, **fetch takes the single 4-byte `fetch_bytes … 4` path** (Fetch.lean:237–246); the 2-byte-first RVC probing path (lines 249–262) is **never entered**. See "RVC branch" below.

---

## The chain (numbered, 5 points each)

### 1. `fetch (_ : Unit) : SailM FetchResult` — Fetch.lean:224
1. Top of fetch. `SailME.run do …`.
2. Reads **`PC`** (readReg PC) — read 5× on our path: at 229 (×2, ext_fetch_check_pc args), 232/233 (alignment bit tests), 237 (is_aligned_vaddr), 240 (fetch_bytes args, ×2). No writes.
3. Branches:
   - 229: `ext_fetch_check_pc PC PC` = `none` (const, #7) → skip throw.
   - 232–234: `PC[0]≠0 ∨ (PC[1]≠0 ∧ ¬currentlyEnabled Ext_Zca)`. PC 4-aligned ⇒ both bit tests false ⇒ **not** misaligned; the `Ext_Zca` disjunct is short-circuited away (PC[1]=0). Skip `F_Error (E_Fetch_Addr_Align …)`.
   - 237: `is_aligned_vaddr (Virtaddr PC) 4  ∧  currentlyEnabled Ext_Ziccif`. Both `true` ⇒ take the **then** branch: `fetch_bytes PC PC 4`.
   - 244: `isRVC (bytes[15:0])`. For an RV64I word `bytes[1:0] = 0b11` ⇒ `isRVC = false` ⇒ return `F_Base bytes`.
4. **SailME** (`SailME.run do`). Its two internal `SailME.throw` sites (230, and via fetch_bytes) are the only early exits; on the success path `.run` unwraps a `pure`.
5. n/a (delegates memory read to fetch_bytes).

### 2. `fetch_bytes (fetch_start granule_start : BitVec 64) (width∈{2,4}) : SailM (FetchBytes_Result width)` — Fetch.lean:208
1. Does PC-check → translate → mem_read, packaging exceptions into `FetchBytes_Result`.
2. No direct readReg/writeReg (operates on the passed `fetch_start`/`granule_start`; both = PC here). Register reads happen inside its callees (#4, #6).
3. Branches:
   - 209: `ext_fetch_check_pc = none` → skip.
   - 212–216: `translateAddr (Virtaddr granule_start) (InstructionFetch ())` → `.Ok (paddr, pbmt, _)` on our path (Bare, #4); binds `paddr = Physaddr (zero_extend PC)`, `pbmt = PBMT_PMA`.
   - 217: `mem_read (InstructionFetch ()) pbmt paddr 4 false false false` → `.Ok bytes` ⇒ `FetchBytes_Success bytes`.
4. **SailME** (`SailME.run do`). Throws on ext-error (210) and translate-error (214). On the hot path neither fires; `.run` unwraps `pure (FetchBytes_Success bytes)`.
5. Delegates to mem_read (#6).

### 3. `ext_fetch_check_pc (_start_pc _pc : BitVec 64) : Option Unit` — AddrChecks.lean:196
1. Extension hook for fetch-address checking.
2. No reg access.
3. Body is literally `none`. Always the "no error" branch.
4. **Pure** (not even SailM). Trivial to `simp`/`rfl`.
5. n/a.

### 4. `translateAddr (vAddr : virtaddr) (access) : SailM (Result (physaddr × pbmt × Unit) (ExceptionType × Unit))` — Vmem.lean:499
1. Virtual→physical translation front door.
2. Reads: via `effectivePrivilege` (500) → **`mstatus`**, **`cur_privilege`**; via `translationMode` (501) → nothing extra in Machine mode (returns Bare before reading satp). No writes.
3. Branches:
   - 500 `effectivePrivilege (InstructionFetch()) mstatus cur_privilege`: guard `bne access (InstructionFetch())` is **false** for fetch ⇒ MPRV branch skipped ⇒ returns `cur_privilege` = Machine (SysControl.lean:214). So `mstatus` is *read but not consulted* for the result.
   - 501 `translationMode Machine` = **Bare** (Vmem.lean:366, `priv == Machine ⇒ Bare`; satp not read).
   - 502 `is_shadow_stack_access (InstructionFetch())` = **false** (VmemTypes.lean:274) ⇒ skip shadow-stack block.
   - 510 `mode == Bare` = **true** ⇒ return `Ok (Physaddr (zero_extend PC), PBMT_PMA, init_ext_ptw)`. **The entire page-table walk / TLB path (`translate`, `lookup_TLB`, `get_satp`, `translate_TLB_hit/miss`) is dead code here.**
4. **SailME** (`SailME.run do`). Only throw is the shadow-stack fault (507), not reachable. Hot path `.run`-unwraps `pure (Ok …)`.
5. n/a.

   Sub-helpers on this path:
   - `effectivePrivilege` — SysControl.lean:214 — SailM; reads its args only; here returns `cur_privilege`.
   - `translationMode` — Vmem.lean:365 — SailM; Machine ⇒ `pure Bare`, no reg read.
   - `is_shadow_stack_access` — VmemTypes.lean:269 — SailM; `InstructionFetch () ⇒ pure false`.
   - `bits_of_virtaddr` — MemAddrtype.lean:206 — pure projection.

### 5. `is_aligned_vaddr (typ_0 : virtaddr) (width) : Bool` — SplitAccessUtils.lean:206
1. Alignment predicate `addr % width == 0`.
2. No reg access (pure on the BitVec).
3. `PC % 4 == 0` = **true**.
4. **Pure** Bool.
5. n/a.

### 6. `mem_read (access) (pbmt) (paddr) (width) (aq rel res : Bool) : SailM (Result (BitVec (8*width)) (physaddr × ExceptionType))` — Mem.lean:488
1. Thin wrapper: resolves effective privilege, calls `mem_read_priv`.
2. Reads **`mstatus`**, **`cur_privilege`** again (490, via `effectivePrivilege`). Returns Machine on fetch (same as #4). No writes.
3. Straight-line; `aq=rel=res=false`.
4. **SailM** (plain `do`, no SailME here). 
5. Delegates down.

### 6a. `mem_read_priv` — Mem.lean:482 → `mem_read_priv_meta` — Mem.lean:458
1. `mem_read_priv` drops metadata; `mem_read_priv_meta` dispatches on `(aq,rl,res)` and fires callbacks.
2. No reg access.
3. `mem_read_priv_meta` 460: `(false,false,false)` ⇒ falls to `(_,_,_) ⇒ checked_mem_read … meta'=false`. 466: `.Ok (value,_)` ⇒ `mem_read_callback` (a no-op, Callbacks.lean:207).
4. **SailM** (plain `do`). The inner match is wrapped `( … : SailM …)` but not SailME.
5. Delegates to `checked_mem_read`.

### 7. `checked_mem_read (access pbmt priv paddr width aq rl res meta') : SailM (Result ((BitVec (8*width)) × Unit) (physaddr × ExceptionType))` — Mem.lean:402
1. The PMA/PMP-checked, possibly-split, byte-loop read.
2. No direct readReg; **calls `check_pma_with_pmp_priority` (→ reads `pma_regions`, #8) and `pmpCheck` (→ reads `pmpcfg_n`, `pmpaddr_n`, #9)**. No writes.
3. Branches (width=4, 4-aligned, Machine):
   - 404 `check_pma_with_pmp_priority` ⇒ `.Ok access_info` (PMA region executable; #8).
   - 410 `split_misaligned paddr 4 …` ⇒ **`(N=1, split_width=4)`** (SplitAccessUtils.lean:247; `addr%4==0` ⇒ `do_not_split`). So the "loop" is a single iteration.
   - loop body 424 `pmpCheck paddr 4 (InstructionFetch()) Machine` ⇒ **`none`** (Machine ⇒ allow; #9).
   - 429 `within_mmio_readable paddr 4` ⇒ **`false`** for normal RAM (not CLINT/SIG/HTIF; #10) ⇒ take the **else** (RAM) branch 438 `read_ram rk paddr 4 meta'`.
   - `updateSubrange` writes the 4 bytes into `data`; 444 `offset==last` ⇒ finished.
   - returns `Ok (data, default_meta)`.
4. **SailME** (`SailME.run do`). Throws on PMA err (407), pmpCheck err (426), mmio err (434) — none reachable. Loop is `untilFuelM (fuel:=N)` with N=1: **the fuel-driven loop must be unfolded once** in proofs.
5. The actual bytes are produced by `read_ram` (#11).

   - `read_kind_of_flags aq rl res` — Mem.lean:213 — SailM; `(false,false,false) ⇒ Read_plain` (but fetch uses ifetch? see #11 note: `rk` here comes from `read_kind_of_flags`, giving `Read_plain`, since fetch calls `mem_read` with res=false — the `AK_ifetch` kind is *not* selected on this path; the ifetch distinction is cosmetic for the RAM read, which ignores `rk` except to build a request record).

### 8. `check_pma_with_pmp_priority (access pbmt priv paddr width res_or_con) : SailM (Result Phys_Mem_Access_Info ExceptionType)` — Mem.lean:391
1. PMA check first, PMP only as tiebreak on PMA failure.
2. No direct reg read; calls `pmaCheck` (#8a) then possibly `pmpCheck` (#9).
3. 392 `pmaCheck … ⇒ .Ok access_info` on our path ⇒ return `Ok` immediately; the `pmpCheck` fallback (396) is not reached.
4. **SailM** (plain `do`).
5. n/a.

### 8a. `pmaCheck (paddr width access pbmt res_or_con) : SailM (Result Phys_Mem_Access_Info ExceptionType)` — Mem.lean:254
1. Look up the PMA region for `paddr`, check the access is permitted.
2. Reads **`pma_regions`** (256). No writes.
3. 256 `matching_pma_region pma_regions paddr width ⇒ .some region` (code lives in a PMA region); `override_PMA attributes pbmt` with `pbmt=PBMT_PMA` leaves attributes. 265 `InstructionFetch () ⇒ canAccess = attributes.executable` (must be `true` for the code region). Returns `Ok {splittable, granule_size_exp}`.
4. **SailME** (`SailME.run do`). Throw at 258 (no matching region → access fault) not reachable if code region is mapped executable. `granule_size_exp`/`splittable` come from `mag_pma_check` (Pma.lean:389).
5. n/a.

### 9. `pmpCheck (addr width access priv) : SailM (Option ExceptionType)` — PmpControl.lean:294
1. 16-entry PMP walk; Machine mode with no locked matching entry ⇒ allow.
2. Reads **`pmpcfg_n`** (310) and **`pmpaddr_n`** (via `pmpReadAddrReg`, 306/311) for each of 16 entries. No writes.
3. `sys_pmp_count = 16 ≠ 0` (PmpRegs.lean:202) ⇒ enters loop `[0:15]`. For the reset config all entries `PMP_NoMatch` (312) — but *even a `PMP_Match`* returns `none` in Machine mode when unlocked (325 `priv==Machine && ¬pmpLocked cfg`). After the loop, 338 `priv==Machine ⇒ pure none`. **Result: `none` (allow) regardless of entries, as long as no *locked* partial/enforcing match — the reset PMP config has none.**
4. **SailME** (`SailME.run do`). Its `SailME.throw` sites carry the *allow/deny result* out of the loop (314/324) — throw is used here as early-return, not as exception; `.run` catches it (`.error (.inr e) ⇒ pure e`). The plain `for … in [..]i` mutable loop must be handled: 16 iterations, each reads two PMP regs.
5. n/a. (This is the single biggest unfold in the whole chain — see Proof plan.)

### 10. `within_mmio_readable (addr width) : SailM Bool` — Platform.lean:696
1. Is this address a memory-mapped IO read region (CLINT / SIG / HTIF)?
2. No reg reads on our path (config-constant region bounds); `get_config_rvfi () = false` at 697.
3. 697 rvfi=false ⇒ else; returns `within_clint ∨ within_sig ∨ (within_htif_readable ∧ 1≤width)`. For a code address all three are **false** ⇒ **`false`** ⇒ checked_mem_read takes the RAM branch.
4. **SailM** (plain `do`).
5. n/a.

### 11. `read_ram (rk : read_kind) (physaddr) (width) (read_meta : Bool) : SailM ((BitVec (8*width)) × Unit)` — PhysMemInterface.lean:327
1. Build a `Mem_read_request`, call `sail_mem_read`, return bytes.
2. No reg read. `read_meta=false` ⇒ `meta' = default_meta` (skips `__ReadRAM_Meta`).
3. 334 builds request; `rk` selects `access_kind` (`Read_plain ⇒ AK_explicit{AV_plain}`), immaterial to the map read. 360 `sail_mem_read request ⇒ .Ok (value,_)` ⇒ `pure (value, meta')`. The `.Err () ⇒ throw Error.Exit` (362) is unreachable (the model's `sail_mem_read` always returns `.Ok`).
4. **SailM** (plain `do`).
5. Delegates the ExtMap read to `sail_mem_read` (#12).

### 12. `sail_mem_read [Arch] (req) : PreSailM … (Result ((BitVec (8*n)) × Option Bool) Arch.abort)` — lean-sail ConcurrencyInterfaceV1.lean:260 (project alias `SpecializationV1.lean:50`)
1. The PreSail primitive. `addr := req.pa.toNat`; `value ← readBytes n addr`; `pure (.Ok value)`.
2. Reads `σ.mem` (see #13). No reg access.
3. Straight-line; `n = width = 4`.
4. **PreSailM** (`EStateM`, not SailME). `@[simp_sail]`.
5. Calls `readBytes` (#13).

### 13. The ExtMap read — `readBytes` / `readByte` — ConcurrencyInterfaceV1.lean:225 / 218
1. `readBytes (size addr)` recurses byte-by-byte, little-endian: `readByte addr` for the low byte then `readBytes (n-1) (addr+1)`, appending high bytes (`bytes.append b`, 236). For `size=4` this expands to 4 `readByte` calls at `addr, addr+1, addr+2, addr+3`.
2. `readByte (addr : Nat)`: `pure ((← get).mem.get? addr |>.getD 0)`.
3. n/a (no branches on our path except the `size` structural recursion 0/1/n+1).
4. **PreSailM** (`EStateM`). Both `@[simp_sail]`.
5. **THE ExtMap lookup**: `σ.mem : Std.ExtHashMap Nat (BitVec 8)` (SequentialState, ConcurrencyInterfaceV1.lean:104). Key type = **`Nat`** (the byte address `req.pa.toNat`). Per-**byte** (one `BitVec 8` per key), assembled into `BitVec 32` by `readBytes`. Read function = `Std.ExtHashMap.get?` with **`.getD 0`** — i.e. **unmapped addresses read as 0**, so a fetch does *not* require the key to be present; but for a loaded code word all four keys `pc+0..pc+3` are present with the ELF bytes.

---

## Extension hooks / announce / config (values + provenance)

| Symbol | File:line | Value | Kind |
|---|---|---|---|
| `ext_fetch_check_pc` | AddrChecks.lean:196 | `none` (const) | pure |
| `ext_fetch_hook (f)` | StepExt.lean:200 | `f` (identity) — wraps fetch result in run_hart_active:317 | pure |
| `sail_instr_announce (_)` | Common0.lean:201 | `()` | pure |
| `fetch_callback (_)` | Callbacks.lean:199 | `()` | pure |
| `mem_read_callback (…)` | Callbacks.lean:207 | `()` | pure |
| `get_config_print_instr ()` | Prelude.lean:212 | `false` | pure |
| `get_config_rvfi ()` | Prelude.lean:233 | `false` | pure |
| `get_config_print_pma/pmp/htif ()` | Prelude.lean:227–231 | `false` | pure |

All of these are compile-time constants in this generated model (no register/state provenance) — they collapse under `simp`. `ext_fetch_hook` is applied to the fetch result in `run_hart_active` (Step.lean:317) and is the identity, so `Step_Execute`/`F_Base` flow through unchanged.

`is_landing_pad_expected ()` — ZicfilpRegs.lean:245 — **reads register `elp`**; `pure (elp == landing_pad_bits_backwards LP_EXPECTED)`. On the F_Base path (Step.lean:377) it is `is_landing_pad_expected () && ¬is_lpad_instruction instruction`; for `elp = NO_LP_EXPECTED` (reset) this is `false`, skipping the CFI trap. **`elp` must be pinned in `GoodState`.**

---

## PC threading (straight-line instruction)

Fetch itself does **not** write PC. PC advances in the step postlude:

- `run_hart_active` F_Base branch: **`writeReg nextPC (PC + 4)`** (Step.lean:384) before `execute`.
- `execute` of a straight-line instruction leaves `nextPC` alone (branches/jumps call `set_next_pc`).
- `set_next_pc (pc)` — PcAccess.lean:205 — `sail_branch_announce` (no-op) then **`writeReg nextPC pc`**, then `redirect_callback` (no-op).
- `tick_pc ()` — PcAccess.lean:210 — **`writeReg PC (← readReg nextPC)`**, then `pc_write_callback` (no-op). Called in `try_step` at Step.lean:448, only when `hart_state = HART_ACTIVE`.

So for a straight-line RV64I instr the PC update is exactly: `nextPC := PC+4` (Step.lean:384) then `PC := nextPC` (Step.lean:448) ⇒ `PC := PC+4`. This matches the `setPC σ (pc+4)` in the PLAN's `step_addi` shape.

Note the try_step prelude before fetch (Step.lean:399–404): `ext_pre_step_hook` (no-op), `writeReg minstret_increment (should_inc_minstret cur_privilege)` (reads `cur_privilege`, writes `minstret_increment`), then `run_hart_active` calls `dispatchInterrupt (← readReg cur_privilege)` (SysControl.lean:533) **before** fetch — must be `none` under GoodState (`mstatus.MIE=0`, `mie=0`), otherwise the interrupt branch preempts fetch.

---

## Register footprint of a hot-path fetch

Deduped registers **read** on the fetch path (`fetch` → … → `read_ram`), with the branch each read feeds:

| Register | Where | Feeds branch decision |
|---|---|---|
| `PC` | Fetch.lean:229,232,233,237,240 | fetch-check args; alignment tests (232–234 → misaligned?); is_aligned_vaddr (237 → 4-byte vs RVC path); fetch_bytes args; is the translated vaddr |
| `mstatus` | translateAddr:500, mem_read:490 (both via `effectivePrivilege`) | MPRV test (false for fetch → priv unchanged); read but not decisive |
| `cur_privilege` | translateAddr:500, mem_read:490 (via `effectivePrivilege`) | = Machine → translationMode Bare (Vmem:366); → pmpCheck allow (PmpControl:338); → pmaCheck priv |
| `misa` | via `currentlyEnabled Ext_Zca → Ext_C` (PlatformConfig:2074) | **only if** PC[1]≠0 (short-circuited away when 4-aligned) — the `.C` bit decides RVC-enable; on our path this read is *not* forced because PC[1]=0. Also `currentlyEnabled Ext_Ziccif` does **not** read misa (pure `hartSupports`). |
| `satp` | translationMode (Vmem:376) | **NOT read** on Machine/Bare path (guarded out at Vmem:366) |
| `pma_regions` | pmaCheck:256 | region lookup → `attributes.executable` (must be true) |
| `pmpcfg_n` | pmpCheck:310 (×16) | per-entry match/RWX; irrelevant in M-mode-allow but still read |
| `pmpaddr_n` | pmpCheck via `pmpReadAddrReg`:306,311 (×16) | per-entry address match; ditto |

Registers **written** on the fetch path: **none.** (Writes happen in the step postlude: `nextPC`, `PC`, `minstret_increment` — not in fetch.)

Additional register consulted in `run_hart_active`/`try_step` around fetch (not in fetch proper but same step): `hart_state`, `elp` (is_landing_pad_expected), `cur_privilege` (dispatchInterrupt, should_inc_minstret), plus `mstatus`/`mie`/`mip` inside `dispatchInterrupt`.

---

## Proof plan implications

### Helpers needing dedicated simp/characterization lemmas

1. **`pmpCheck` = `none` in M-mode** (PmpControl.lean:294). The 16-iteration `for … in [0:15]i` mutable loop plus 32 register reads (`pmpcfg_n`, `pmpaddr_n`) is the heaviest single unfold. Prove once: *under GoodState (Machine, reset PMP config), `pmpCheck paddr w access Machine = pure none`* — this is the PLAN's `pmp_allows` lemma (§Layer0.1). Consumers: `checked_mem_read:424`, `check_pma_with_pmp_priority:396` (latter not even reached). Without it every fetch/load re-pays the 16-entry walk.
2. **`translateAddr` on Bare** (Vmem.lean:499). Lemma: *priv=Machine ⇒ `translateAddr (Virtaddr a) (InstructionFetch()) = pure (Ok (Physaddr (zero_extend a), PBMT_PMA, init_ext_ptw))`*, discharging `effectivePrivilege`, `translationMode`, `is_shadow_stack_access` in one step and killing the entire PTW/TLB subtree.
3. **`effectivePrivilege … (InstructionFetch())` = priv** (SysControl.lean:214) — trivial `simp` lemma (guard false); reused by translateAddr and mem_read (twice).
4. **`pmaCheck` executable region** (Mem.lean:254). Lemma keyed on a `CodeRegionExecutable`/PMA predicate in GoodState: *`pmaCheck paddr 4 (InstructionFetch()) PBMT_PMA false = pure (Ok {splittable := CannotSplit?/…, granule_size_exp})`* with `attributes.executable = true`. Needs the concrete `pma_regions` reset value or a predicate over it.
5. **`split_misaligned … 4` with 4-aligned addr = `(1,4)`** (SplitAccessUtils.lean:247) — pure `decide` lemma; collapses the `untilFuelM` in `checked_mem_read` to a single iteration.
6. **`within_mmio_readable` = false for code addresses** (Platform.lean:696) — needs a `¬within_clint/sig/htif` region lemma (config constants; `decide` given the address range).
7. **`readBytes 4 addr` = word assembly over `readByte`** — the PLAN's "memory normal form" (§Layer0.2): `readByte addr = (σ.mem.get? addr).getD 0`; then a read-over-`ProgramRepr` lemma turning `σ.mem[pc+k]? = some bₖ` hypotheses into the concrete `BitVec 32`. The `@[simp_sail] readBytes`/`readByte` already unfold; the work is the ExtHashMap `get?` interface + little-endian `append` reassembly (`bytes.append b`, order matters: byte0 low).
8. **The no-op hooks** (`ext_fetch_check_pc`, `ext_fetch_hook`, `sail_instr_announce`, `fetch_callback`, `mem_read_callback`, all `get_config_*`) — add to the `seval`/`simp_sail` set as `rfl`-unfoldings.
9. **`currentlyEnabled Ext_Ziccif = true`** (pure `hartSupports`) and **`currentlyEnabled Ext_Zca = currentlyEnabled Ext_C = (misa.C == 1)`** — small lemmas; Zca=false requires `misa.C = 0` in GoodState (needed to *justify* the 4-byte path via the 237 conjunction, and to make the 232–234 disjunct irrelevant).
10. **`is_landing_pad_expected () = false`** given `elp = NO_LP_EXPECTED` in GoodState (ZicfilpRegs.lean:245) — kills the CFI trap in run_hart_active.

### SailME.run boundaries (must be discharged in proofs)

`SailME.run` (ConcurrencyInterfaceV1.lean:320) wraps: **`fetch`, `fetch_bytes`, `translateAddr`, `checked_mem_read`, `pmaCheck`, `pmpCheck`** (and `run_hart_active`). Each is `ExceptT (Error ⊕ α)` over PreSailM; `.run` maps `.error (.inr e) ⇒ pure e`, `.error (.inl e) ⇒ throw e`, `.ok e ⇒ pure e`. On the hot path **no `SailME.throw` fires**, so every `.run` reduces to `pure` of the success value — but the simp set must include `PreSailME.run`, `ExceptT.run`, `PreSailME.throw`, the `MonadExceptOf`/`bind` instances (the E1i staged set already carries `throw, throwThe, MonadExceptOf.throw, EStateM.throw`, ConcurrencyInterfaceV1 experiments/E1i_decode_staged.lean:20–22). Special care: `pmpCheck` uses `SailME.throw` as *early-return with a value* (the `none`/`some e` result), so its lemma must reason through the throw, not assume it's the error path.

Non-SailME (plain PreSailM/EStateM `do`) links — simpler, just `bind`/`EStateM.bind` unfolding: `mem_read`, `mem_read_priv`, `mem_read_priv_meta`, `check_pma_with_pmp_priority`, `within_mmio_readable`, `read_kind_of_flags`, `read_ram`, `sail_mem_read`, `readBytes`, `readByte`, `effectivePrivilege`, `translationMode`, `is_shadow_stack_access`, `is_landing_pad_expected`.

### Expected shape of the fetch characterization lemma

```lean
theorem fetch_F_Base
    (hG : GoodState σ)                 -- Machine, Bare (via priv), misa.C=0, elp=NO_LP,
                                        -- reset PMP grants M-mode, mstatus.MIE=0/mie=0, …
    (hpc  : (readReg PC).run σ = pc)   -- pc is the current PC
    (halign : pc.toNat % 4 = 0)        -- 4-aligned
    (hcode : CodeRegionExecutable σ pc)          -- pma_regions maps [pc,pc+4) executable
    (hbytes : ∀ k < 4, σ.mem.get? (pc.toNat + k) = some (b k))  -- ELF code bytes present
    (hword  : w = (b 3) ++ (b 2) ++ (b 1) ++ (b 0))            -- little-endian assembly
    (hnotrvc : w.extractLsb 1 0 = 0b11#2) :                     -- ⇒ not RVC
    (fetch ()).run σ = (pure (F_Base w)).run σ                  -- value; σ.regs/mem unchanged
    ∧ (fetch ()) leaves σ unchanged (no writeReg/writeMem)
```

Hypotheses: `GoodState`, PC value, 4-alignment, code-region-executable predicate over `pma_regions`, the four `σ.mem.get?` byte facts, little-endian word reassembly, and `w[1:0]=0b11` (guarantees `isRVC=false`). Conclusion: `fetch () = pure (F_Base w)` with the state (registers *and* memory) unchanged — fetch is read-only, so it composes cleanly into the `try_step`/`stepOnce` skeleton where the only state writes are `nextPC := PC+4` and `PC := nextPC`.

This lemma is exactly the "fetch succeeds with `w`" clause the PLAN's `try_step` skeleton lemma (§Layer0.3) needs; combined with the decode-table lemma (E1i, done) and a per-instruction execute clause it yields `step_addi`.
