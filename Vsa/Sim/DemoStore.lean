import Vsa.Sim.StepStore
import Vsa.Sim.ExecuteStore
import Vsa.Sim.RegAccess
import Vsa.Sim.DecodeTable
import Vsa.Sim.DecodeTable.Batch04Part02

/-!
# M2 STORE-class demo instantiation — `sd x11, 8(x2)` (census word `0x00b13423`)

The composability gate for the STORE class, mirroring `Vsa/Sim/StepAlu.lean`'s
`try_step_alu_add_x15_x15_x14`.  We instantiate the generic `step_store` stack for
**one** concrete `sd` instruction word taken from the binary
(`experiments/disasm_census.json`, mnemonic `sd`, count 26), proving a
`Vsa.Machine.Step` with `GoodState` preservation.

Chosen word `0x00b13423` decodes (`Vsa/Sim/DecodeTable/Batch04.lean:decode_00b13423`)
to `instruction.STORE (0x008#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x02#5, 8)`,
i.e. `sd x11, 8(x2)` — base `rs1 = x2` (sp), data `rs2 = x11` (a1), distinct
registers, small nonzero offset `imm = 8`, width `8`.

## Composition chain (the exact bridges the LOAD demo will replay)

`decode_00b13423 (afterPrelude σ)` (its `hpriv`/`hmisa`/`hsec` come from
`get?_afterPrelude` read-backs of `GoodState`) supplies the skeleton's `hdec`.

The execute step (`hexec`) is assembled at state `σ₂ := afterNextPC (afterPrelude σ) pc`:
* `execute (STORE …)` reduces to `execute_STORE 0x008#12 x11 x2 8` by `simp only [execute]`
  (iota on the dispatch match — the same bridge the ALU chars use for `execute (RTYPE …)`);
* `execute_STORE_char` takes the two GPR reads (`hrs2` on `x11`, `hrs1` on `x2`)
  and the abstract memory write `hwrite`;
* the GPR reads reduce via `rX_bits_x11`/`rX_bits_x2` (RegAccess) against
  `σ₂.regs.get? x11 / x2`, which read back through the two prelude inserts to `σ`
  by `get?_afterNextPC` (nextPC/minstret_increment ≠ x11/x2 by `decide`);
* the control-plane hyps (`cur_privilege = Machine`, `mstatus = initMstatus`,
  `mseccfg = 0`, `pma_regions`, `pmpcfg_n`, `pmpaddr_n`, `htif_tohost_base`) read
  back the same way from `GoodState`, and `_get_Mstatus_MPRV initMstatus = 0#1`
  / `_get_Seccfg_PMM 0 = 0#2` close by `decide`;
* `hwrite` is `vmem_write_addr_8` at `σ₂`, on the plain base address
  `a := vbase + sign_extend 0x008#12`, its RAM/align/HTIF side conditions taken as
  hypotheses on `a`.

## Composition-boundary facts (bridged here — for the LOAD demo)

1. `vmem_write_addr_8`'s post-state is the whole state `{σ₂ with mem := <chain>}`,
   and `sigma3_store σ pc m' = {σ₂ with mem := m'}`.  They coincide **definitionally**
   with `m' := σ₂.mem.insert …` — no bridge lemma needed.  So the byte map handed to
   `try_step_store` is `σ₂.mem.insert a.toNat …`.
2. The `data` slice: `execute_STORE_char`'s `hwrite` wants
   `Sail.BitVec.extractLsb vdata ((8 *i 8) -i 1) 0` (auto-`setWidth (8*8)`-wrapped);
   `vmem_write_addr_8` is instantiated at exactly that `data`, so the byte-insert
   chain is stated on `(sdData vdata).extractLsb' k 8`.
3. `pmpaddr_n` — `vmem_write_addr_8` quantifies its value abstractly (`vpmpaddr`);
   `GoodState` pins it to `initPmpaddr`, so we pass `vpmpaddr := initPmpaddr` and
   discharge `haddr` from `hG.pmpaddr_n`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- The concrete decoded AST for `0x00b13423` (`sd x11, 8(x2)`). -/
abbrev sdAst : instruction :=
  instruction.STORE (0x008#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x02#5, 8)

/-- The store data slice: `execute_STORE`'s `extractLsb vdata (width*8-1) 0` at
`width = 8`, exactly the `data` argument `execute_STORE_char`'s `hwrite` demands
(the `setWidth (8*8)` coercion to `BitVec (8*8)` is inserted automatically). -/
abbrev sdData (vdata : BitVec 64) : BitVec (8 * 8) :=
  Sail.BitVec.extractLsb vdata ((8 *i 8) -i 1) 0

/-- The effective store address for `sd x11, 8(x2)`: `vbase + sign_extend 0x008`. -/
abbrev sdAddr (vbase : BitVec 64) : BitVec 64 :=
  vbase + sign_extend (m := 64) (0x008#12)

/-- The 8-byte little-endian byte-insert map produced by `vmem_write_addr_8`:
byte `k` of `sdData vdata` at `a + k`, `k ∈ [0,8)`. -/
abbrev sdMem (m : Std.ExtHashMap Nat (BitVec 8)) (a : BitVec 64) (vdata : BitVec 64) :
    Std.ExtHashMap Nat (BitVec 8) :=
  ((((((((m.insert a.toNat ((sdData vdata).extractLsb' 0 8)).insert
      (a.toNat + 1) ((sdData vdata).extractLsb' 8 8)).insert
      (a.toNat + 2) ((sdData vdata).extractLsb' 16 8)).insert
      (a.toNat + 3) ((sdData vdata).extractLsb' 24 8)).insert
      (a.toNat + 4) ((sdData vdata).extractLsb' 32 8)).insert
      (a.toNat + 5) ((sdData vdata).extractLsb' 40 8)).insert
      (a.toNat + 6) ((sdData vdata).extractLsb' 48 8)).insert
      (a.toNat + 7) ((sdData vdata).extractLsb' 56 8))

/-! ## `execute` step for `sd x11, 8(x2)` in `hexec` shape -/

/-- `execute (STORE …)` at `σ₂ = afterNextPC (afterPrelude σ) pc` for `sd x11, 8(x2)`,
in exactly the `sigma3_store` post-state shape `try_step_store`'s `hexec` expects.
Assembled from `execute_STORE_char` + `vmem_write_addr_8` (as `hwrite`), with the two
GPR reads reduced from pinned `σ` values through the prelude frame. -/
theorem exec_sd_x11_x2
    (σ : MState) (pc : BitVec 64) (vbase vdata : BitVec 64)
    (hG : GoodState σ)
    (hx2 : σ.regs.get? Register.x2 = some vbase)
    (hx11 : σ.regs.get? Register.x11 = some vdata)
    (hlo : 0x80000000 ≤ (sdAddr vbase).toNat)
    (hhiram : (sdAddr vbase).toNat + 8 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (sdAddr vbase).toNat)
    (halign : (sdAddr vbase).toNat % 8 = 0) :
    (execute sdAst).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_store σ pc
            (sdMem (afterNextPC (afterPrelude σ) pc).mem (sdAddr vbase) vdata)) := by
  -- control-plane reads of σ₂ from GoodState, through the prelude frame
  have hpriv : (afterNextPC (afterPrelude σ) pc).regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.cur_privilege
  have hmstatus : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mstatus = some initMstatus := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mstatus
  have hseccfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mseccfg = some (0#64) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mseccfg
  have hpma : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pma_regions
  have hcfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpcfg_n
  have haddr : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpaddr_n = some initPmpaddr := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpaddr_n
  have hbase' : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base) := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.htif_tohost_base
  -- GPR reads of σ₂ from pinned σ values, through the prelude frame
  have hx2₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x2 = some vbase := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx2
  have hx11₂ : (afterNextPC (afterPrelude σ) pc).regs.get? Register.x11 = some vdata := by
    rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hx11
  have hrs1 : (rX_bits (regidx.Regidx 0x02#5)).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc) :=
    rX_bits_x2 _ vbase hx2₂
  have hrs2 : (rX_bits (regidx.Regidx 0x0b#5)).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc) :=
    rX_bits_x11 _ vdata hx11₂
  -- the memory write, on the plain base address `a = sdAddr vbase`
  have hwrite := vmem_write_addr_8 (afterNextPC (afterPrelude σ) pc) (sdAddr vbase) (sdData vdata)
    initMstatus initPmpaddr
    hpriv hmstatus (by decide) hpma hcfg haddr hbase' hlo hhiram hhiwin halign
  -- `execute_STORE_char`, with `hwrite` at `a = vbase + sign_extend 0x008`
  have hchar := execute_STORE_char (0x008#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x02#5) 8
    vbase vdata (afterNextPC (afterPrelude σ) pc) initMstatus (0#64)
    (sigma3_store σ pc (sdMem (afterNextPC (afterPrelude σ) pc).mem (sdAddr vbase) vdata))
    (by decide) hpriv hmstatus (by decide) hseccfg (by decide) hrs2 hrs1
    (by
      -- discharge `hwrite` obligation: address `vbase + sign_extend 0x008` = `sdAddr vbase`,
      -- data `sdData vdata`, post-state `{σ₂ with mem := sdMem …}` = `sigma3_store σ pc …`.
      show (vmem_write_addr (virtaddr.Virtaddr (sdAddr vbase)) 8
          (sdData vdata) (MemoryAccessType.Store mem_payload.Data) false false false).run
          (afterNextPC (afterPrelude σ) pc)
        = .ok (.Ok true) (sigma3_store σ pc (sdMem (afterNextPC (afterPrelude σ) pc).mem (sdAddr vbase) vdata))
      exact hwrite)
  -- bridge `execute (STORE …)` to `execute_STORE …` and finish
  show (execute (instruction.STORE (0x008#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x02#5, 8))).run
      (afterNextPC (afterPrelude σ) pc) = _
  simp only [execute]
  exact hchar

/-! ## Byte-word facts for `0x00b13423`

Little-endian: word `0x00b13423` = bytes `b0=0x23 b1=0x34 b2=0xb1 b3=0x00`. -/

/-- The four code bytes of `0x00b13423` assemble to the word. -/
theorem sd_bytes_word :
    (((0x00#8).append (0xb1#8)).append (0x34#8)).append (0x23#8) = (0x00b13423#32 : BitVec 32) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- The word is non-RVC: its low two bits are `0b11`. -/
theorem sd_notrvc :
    Sail.BitVec.extractLsb ((((0x00#8).append (0xb1#8)).append (0x34#8)).append (0x23#8)) 1 0
      = (0b11#2 : BitVec 2) := by
  apply BitVec.eq_of_toNat_eq; decide

/-! ## Demonstration instantiation — `sd x11, 8(x2)` (census word `0x00b13423`)

Validates that the generic STORE interface composes with a real `ExecuteStore`
clause end-to-end: `decode_00b13423` (decode) + `exec_sd_x11_x2` (execute, from
`execute_STORE_char` ∘ `vmem_write_addr_8`) plug straight into `try_step_store` and
`step_store_notick`. -/

/-- **`try_step` on `sd x11, 8(x2)`** (census word `0x00b13423`, count 26),
composing `exec_sd_x11_x2` through the generic `try_step_store`. -/
theorem try_step_store_sd_x11_x2
    (σ : MState) (u : Nat) (pc : BitVec 64) (vminstret vbase vdata : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vbase)
    (hx11 : σ.regs.get? Register.x11 = some vdata)
    (hb0 : σ.mem[pc.toNat]? = some (0x23#8)) (hb1 : σ.mem[pc.toNat + 1]? = some (0x34#8))
    (hb2 : σ.mem[pc.toNat + 2]? = some (0xb1#8)) (hb3 : σ.mem[pc.toNat + 3]? = some (0x00#8))
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (halo : 0x80000000 ≤ (sdAddr vbase).toNat)
    (hahiram : (sdAddr vbase).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (sdAddr vbase).toNat)
    (haalign : (sdAddr vbase).toNat % 8 = 0) :
    (try_step u true).run σ
      = .ok false
          (sigmaPost_store σ pc vminstret
            (sdMem (afterNextPC (afterPrelude σ) pc).mem (sdAddr vbase) vdata)) :=
  try_step_store σ u pc vminstret (0x00b13423#32 : BitVec 32) sdAst
    (sdMem (afterNextPC (afterPrelude σ) pc).mem (sdAddr vbase) vdata)
    (0x23#8) (0x34#8) (0xb1#8) (0x00#8)
    hG hpc hminstret sd_bytes_word sd_notrvc
    (Vsa.Sim.DecodeTable.decode_00b13423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_x11_x2 σ pc vbase vdata hG hx2 hx11 halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 hlo hhi halign

/-- **`step_store` (no clock tick) on `sd x11, 8(x2)`.** The M2 composability gate
for the STORE class: one architectural `Vsa.Machine.Step` on the concrete census
word `0x00b13423`, with `GoodState` preserved.  `i+1 ≠ 2` (no tick). -/
theorem step_store_sd_x11_x2_notick
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vbase vdata : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vbase)
    (hx11 : σ.regs.get? Register.x11 = some vdata)
    (hb0 : σ.mem[pc.toNat]? = some (0x23#8)) (hb1 : σ.mem[pc.toNat + 1]? = some (0x34#8))
    (hb2 : σ.mem[pc.toNat + 2]? = some (0xb1#8)) (hb3 : σ.mem[pc.toNat + 3]? = some (0x00#8))
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (halign : pc.toNat % 4 = 0)
    (halo : 0x80000000 ≤ (sdAddr vbase).toNat)
    (hahiram : (sdAddr vbase).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (sdAddr vbase).toNat)
    (haalign : (sdAddr vbase).toNat % 8 = 0)
    (htick : i + 1 ≠ 2) :
    Vsa.Machine.Step ⟨σ, i, u⟩
      ⟨sigmaPost_store σ pc vminstret
          (sdMem (afterNextPC (afterPrelude σ) pc).mem (sdAddr vbase) vdata), i + 1, u + 1⟩
    ∧ GoodState (sigmaPost_store σ pc vminstret
          (sdMem (afterNextPC (afterPrelude σ) pc).mem (sdAddr vbase) vdata)) :=
  step_store_notick σ i u pc vminstret (0x00b13423#32 : BitVec 32) sdAst
    (sdMem (afterNextPC (afterPrelude σ) pc).mem (sdAddr vbase) vdata)
    (0x23#8) (0x34#8) (0xb1#8) (0x00#8)
    hG hpc hminstret sd_bytes_word sd_notrvc
    (Vsa.Sim.DecodeTable.decode_00b13423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_x11_x2 σ pc vbase vdata hG hx2 hx11 halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 hlo hhi halign htick

end Vsa.Sim
