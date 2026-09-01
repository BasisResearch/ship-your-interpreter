import Vsa.Sim.BlockPilot
import Vsa.Sim.ValueSites
import Vsa.Sim.ObsAvoid

/-!
# `BlockMem` — proof-by-reflection block lemma for straight-line ALU + LOAD + STORE runs

Generalizes `BlockPilot`'s `block_alu_sound` (ADDI/ADD only) to the memory
classes: value loads (`lw`/`ld`/`lbu`) and stores (`sw`/`sd`/`sb`).  One lemma,
`block_mem_sound`, consumes a concrete `List MInstr` and produces the whole
`Steps` chain with a *computed* register outcome (`runGM`) **and** a computed
memory outcome: the final memory is the `writeMap` fold (`writeLog`) of a
computed write log (`wlogM : List (addr × width × value)`, symbolic addresses
as base-pin + concrete offset, symbolic data).

## Measured verdict (acceptance test: the mixed 7-instruction `__ssputs_r`
prologue `0x8001438c–0x800143a4` — `addi/sd/lw/sd/sd/mv/mv`, real byte pins +
DecodeTable lemmas, ONE `block_mem_sound` application (`BlockMemDemo.lean`) vs
the same 7 steps via `site_1438c_sp …` per-site ceremony in the
`SnprintfSpec19.tr_ssputs_head` style (`/tmp/bm_ceremony.lean`); *identical*
hypotheses and conclusions: `Steps (u+7)`, tick, `GoodState`, the three nested
`writeMap8` images, HTIF output, `PC = 0x800143a8`, the four written registers
incl. the `lw` value, minstret, and an `x10` frame)

* `lean --profile` proof work (elaboration + tactic execution + kernel):
  reflection **≈ 250 ms** (49 + 181 + 20) vs ceremony **≈ 990 ms**
  (52 + 852 + 86) — **≈ 4× less** at 7 instructions.  The pilot measured 1.7×
  at 3 ALU instructions; the gap grows with block length and pin count as
  predicted — ceremony is O(instrs × tracked-registers) plus per-store
  mem-image/`…Loaded` bookkeeping, reflection O(instrs).
* wall-clock `lean` on the use site (5 runs): reflection **1.22–1.35 s** vs
  ceremony **2.32–2.59 s** — both import-dominated (0.65 s vs 2.0–2.4 s of
  olean loading; the ceremony additionally pulls the `SnprintfSpec19` closure
  for the `…Loaded`-under-store lemmas that reflection does not need).
* line count (identical theorem statement, ≈ 105 shared hypothesis/conclusion
  lines): reflection proof body **30** lines + **9** block-data lines
  (`ssputsProlog`) vs ceremony proof body **192** lines (≈ 27 per instruction
  at 6–7 tracked registers: `obs_*` transports + per-store `mem_afterNextPC`
  image chains + `…Loaded` re-establishment).  Marginal cost per added
  instruction: reflection = 1 data line + 1–3 `ProgFactsM` entries, and 0 new
  lines per extra *tracked register*; ceremony ≈ 1 line per (instruction ×
  register) + ≈ 6 lines per store.
* one-time cost: this file (≈ 1060 lines, of which ≈ 40 are the scripted
  `obs_gpr_store` battery) compiles in ≈ 1.8 s.

**Verdict: WIN, and it grows with the memory classes.**  The pilot's "modest
win now, structural win at scale" sharpens at 7 mixed instructions to a 4×
proof-work and 6.4× proof-body reduction; stores are where the ceremony hurts
most (mem-image chains, `…Loaded` transport, per-register store transports) and
exactly where the block lemma's computed write log + internal code-pin
survival pay off.

## Design deltas over `BlockPilot`

* `MInstr`/`MKind` — the pilot's `AInstr` grown by six memory kinds.  Structure
  stays fully concrete (kinds enumerate the width/sign variants), so the VC
  `BlockOKM` stays decidable; *nothing symbolic ever enters the instruction
  list* (the `decide`-rejects-fvars gotcha).
* **Load data is supplied positionally**: `lds : List (List (BitVec 8))`, one
  byte-list per load in program order.  The loaded value enters the computed
  register outcome as `sign_extend`/`zero_extend` of the LE byte append
  (`bytesVal`), phrased over `bs.getD j 0#8` so no length side condition is
  needed anywhere: for a literal byte list the `getD`s reduce to the bare
  symbolic bytes.
* **Per-element `ProgFactsM` gains the data-dependent side conditions**
  (`MemFacts`): RAM bounds / HTIF-window / alignment at the *symbolic*
  effective address `eaddrM = srcVal rs1 + sext imm`, plus (for loads) the
  byte-definedness pins — stated on the **threaded memory** at that point in
  the block, so loads can read back earlier stores of the same block.  These
  are `Prop`-side hypotheses (they mention symbolic values), *not* `BlockOKM`.
* **The memory thread**: `ProgFactsM` recurses with `stepMemM`, the same
  `applyW` update that `wlogM`/`writeLog` use in the conclusion, so the load
  pins and the final-memory statement share one definition of the evolving map.
* **Code pins survive stores for free**: `BytePinsM` stay on the *entry*
  memory; the induction carries `∀ j < tohostAddr, m[j]? = m0[j]?`, re-proved
  after each store from its `tohostAddr + 16 ≤ addr` window fact (code lives
  below `tohostAddr`, stores land above the window — `*_low_miss`).
* Per-class step consumption: loads go through `stepObs_alu` (a load is a
  register write; memory unchanged) with `exec_lw`/`exec_ld`/`exec_lbu_bm`
  characterizations; stores through `stepObs_store` + `exec_sw`/`exec_sd_val`/
  `exec_sb_bm`.  `exec_lbu_bm`/`exec_sb_bm` are the generic width-1 characterizations
  (the `MemcpySites` per-site `exec_c48`/`exec_c54` shapes, made generic).
* One new 33-branch dispatch battery (`obs_gpr_store`): every GPR pin survives
  a store step.  Everything else (`gprReg`/`gprGet`/`gprRT`/`rX_src`/`wX_gpr`/
  `obs_gpr_rd`/`obs_gpr_other`/`gholds_eraseG`/`srcVal`/`SrcOK`…) is reused
  from `BlockPilot` unchanged.

**Obstructions hit** (the pilot's four all reappear unchanged; new ones):
(5) load data cannot live in `MInstr` — `decide` rejects fvars, so a symbolic
byte in the list would kill the `show BlockOKM … by decide` close; solved by
the positional `lds` + `getD` phrasing.  (6) at the use site the caller
supplies `ProgFactsM` components whose *expected* types are `srcVal`/`eaddrM`
applications over the computed pin list — the anonymous-constructor bundle
elaborates because `lookupG`/`stepGM`/`stepMemM` all whnf-reduce on concrete
keys (symbolic values are never inspected); hypotheses must be phrased with
the *computed* base value (e.g. `v2 + sext 0xfc0 + sext 0x028` for a store
whose base register was written earlier in the block).  (7) the load-pin
obligations land on `writeMap`-image memories when a store precedes the load —
this matches what the per-site ceremony demands at the same point, so nothing
is lost, but callers reading loads *disjoint* from the block's stores must
discharge the image pins from entry pins via `insert`-miss rewrites
(`getElem?_insert_outside`-style), exactly as ceremony compositions do today.

## What branch-terminator support (the remaining class) would need

A taken branch/jump ends the block, so `block_*_sound` becomes a *basic-block*
lemma: `List MInstr` (straight-line body, this file) + an optional terminator
consumed by `stepObs_branch_taken`/`stepObs_branch_nottaken`/`stepObs_j`/
`stepObs_jr` at the end.  Concretely: (1) a `Term` sum type (branch kind + the
two source indices + the 13/21-bit immediate, or jump target); (2) the branch
*condition* (e.g. `zopz0zKzJ_u v13 v9 = false`) is data-dependent, so it joins
`ProgFactsM` as one more per-terminator hypothesis, exactly like the store
window facts; (3) `endPCM` returns the branch target instead of fall-through
in the taken case; (4) the register/memory outcome is unchanged (branches
write nothing) — so no new batteries are needed, only a last non-inductive
step case after the list induction.  The list-induction skeleton is untouched.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Generic width-1 execute characterizations (`lbu` / `sb`)

The width-4/8 generics (`exec_lw`/`exec_ld`/`exec_sw`/`exec_sd_val`) live in
`ValueSites`; width 1 only existed as the per-site `exec_c48`/`exec_c54`
(`MemcpySites`).  These are those shapes with generic registers/immediate. -/

/-- Generic unsigned 1-byte load `lbu rd,off(rs1)` at `afterNextPC …`: reads the
byte at `vbase + sext off` and writes `zero_extend b0` to `rd`.  No alignment
side condition at width 1. -/
theorem exec_lbu_bm (σ : MState) (pc : BitVec 64) (off : BitVec 12) (rs1 rd : regidx)
    (σ' : MState) (vbase : BitVec 64) (b0 : BitVec 8)
    (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hwr : (wX_bits rd (zero_extend (m := 64) (b0 : BitVec (8 * 1)))).run
        (afterNextPC (afterPrelude σ) pc) = .ok () σ')
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (hhiram : (vbase + sign_extend (m := 64) off).toNat + 1 ≤ 0x100000000)
    (hhtif : (vbase + sign_extend (m := 64) off).toNat + 1 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vbase + sign_extend (m := 64) off).toNat)
    (h0 : σ.mem[(vbase + sign_extend (m := 64) off).toNat]? = some b0) :
    (execute (instruction.LOAD (off, rs1, rd, true, 1))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS σ' := by
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
  have hread := vmem_read_data_one (afterNextPC (afterPrelude σ) pc) rs1
    (sign_extend (m := 64) off) vbase b0 initMstatus initPmpaddr
    hpriv hmstatus (by decide) hseccfg hpma hcfg haddr hbase' hrs1 hlo hhiram hhtif
    (by rw [mem_afterNextPC]; exact h0)
  exact execute_load_unsigned_char off rs1 rd 1 (b0 : BitVec (8 * 1))
    (afterNextPC (afterPrelude σ) pc) σ' (by decide) hread hwr

/-- Generic width-1 `sb rs2,off(rs1)` execute characterization: stores the low
byte of `rs2` at `vbase + sext off`; post memory is the single insert.  No
alignment side condition at width 1. -/
theorem exec_sb_bm (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs2 rs1 : regidx)
    (vbase vdata : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) imm).toNat)
    (hhiram : (vbase + sign_extend (m := 64) imm).toNat + 1 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (vbase + sign_extend (m := 64) imm).toNat) :
    (execute (instruction.STORE (imm, rs2, rs1, 1))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_store σ pc
            ((afterNextPC (afterPrelude σ) pc).mem.insert
              (vbase + sign_extend (m := 64) imm).toNat (sbData vdata))) := by
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
  have hwrite := vmem_write_addr_1 (afterNextPC (afterPrelude σ) pc)
    (vbase + sign_extend (m := 64) imm) (sbData vdata) initMstatus initPmpaddr
    hpriv hmstatus (by decide) hpma hcfg haddr hbase' hlo hhiram hhiwin
  have hchar := execute_STORE_char imm rs2 rs1 1
    vbase vdata (afterNextPC (afterPrelude σ) pc) initMstatus (0#64)
    (sigma3_store σ pc
      ((afterNextPC (afterPrelude σ) pc).mem.insert
        (vbase + sign_extend (m := 64) imm).toNat (sbData vdata)))
    (by decide) hpriv hmstatus (by decide) hseccfg (by decide) hrs2 hrs1
    (by
      show (vmem_write_addr (virtaddr.Virtaddr (vbase + sign_extend (m := 64) imm)) 1
          (sbData vdata) (MemoryAccessType.Store mem_payload.Data) false false false).run
          (afterNextPC (afterPrelude σ) pc)
        = .ok (.Ok true) (sigma3_store σ pc
            ((afterNextPC (afterPrelude σ) pc).mem.insert
              (vbase + sign_extend (m := 64) imm).toNat (sbData vdata)))
      exact hwrite)
  show (execute (instruction.STORE (imm, rs2, rs1, 1))).run (afterNextPC (afterPrelude σ) pc) = _
  simp only [execute]
  exact hchar

/-! ## The write log and its fold -/

/-- One store: effective address (as `Nat`), width (1/4/8), full data value. -/
abbrev WEntry := Nat × Nat × BitVec 64

/-- Apply one write-log entry: the per-width store image (`writeMap4`/`writeMap8`
of `ValueSites`, single `insert` for `sb`). -/
def applyW (m : Std.ExtHashMap Nat (BitVec 8)) : WEntry → Std.ExtHashMap Nat (BitVec 8)
  | (a, 1, d) => m.insert a (sbData d)
  | (a, 4, d) => writeMap4 m a (swData d)
  | (a, 8, d) => writeMap8 m a (sdData_val d)
  | (_, _, _) => m

/-- Fold a write log over a memory (left-to-right = program order). -/
def writeLog (m : Std.ExtHashMap Nat (BitVec 8)) (log : List WEntry) :
    Std.ExtHashMap Nat (BitVec 8) :=
  log.foldl applyW m

/-! ## Low-address misses: stores above the HTIF window never touch code -/

theorem insert_low_miss (m : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (j : Nat) (hj : j < k) : (m.insert k v)[j]? = m[j]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

theorem writeMap4_low_miss (m : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (d : BitVec (8 * 4))
    (j : Nat) (hj : j < k) : (writeMap4 m k d)[j]? = m[j]? := by
  show ((((m.insert k _).insert (k + 1) _).insert (k + 2) _).insert (k + 3) _)[j]? = m[j]?
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

theorem writeMap8_low_miss (m : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (d : BitVec (8 * 8))
    (j : Nat) (hj : j < k) : (writeMap8 m k d)[j]? = m[j]? := by
  show ((((((((m.insert k _).insert (k + 1) _).insert (k + 2) _).insert (k + 3) _).insert
      (k + 4) _).insert (k + 5) _).insert (k + 6) _).insert (k + 7) _)[j]? = m[j]?
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

/-! ## Store-step GPR pin transport (the one new dispatch battery) -/

/-- Transport a `gprGet` pin (any GPR `1..31`) through a STORE step: the STORE
register write-set is `{PC, minstret, nextPC, minstret_increment}` + tick noise,
so every GPR pin survives.  33-branch dispatch (the `obs_gpr_other` of stores). -/
theorem obs_gpr_store {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) :
    ∀ (n : Nat), 1 ≤ n → n ≤ 31 →
    ∀ (w : BitVec 64), gprGet σ n = some w → gprGet σ' n = some w
  | 0, h, _, _, _ => absurd h (by omega)
  | 1, _, _, w, h => obs_store_other' hobs Register.x1 (by decide) h
  | 2, _, _, w, h => obs_store_other' hobs Register.x2 (by decide) h
  | 3, _, _, w, h => obs_store_other' hobs Register.x3 (by decide) h
  | 4, _, _, w, h => obs_store_other' hobs Register.x4 (by decide) h
  | 5, _, _, w, h => obs_store_other' hobs Register.x5 (by decide) h
  | 6, _, _, w, h => obs_store_other' hobs Register.x6 (by decide) h
  | 7, _, _, w, h => obs_store_other' hobs Register.x7 (by decide) h
  | 8, _, _, w, h => obs_store_other' hobs Register.x8 (by decide) h
  | 9, _, _, w, h => obs_store_other' hobs Register.x9 (by decide) h
  | 10, _, _, w, h => obs_store_other' hobs Register.x10 (by decide) h
  | 11, _, _, w, h => obs_store_other' hobs Register.x11 (by decide) h
  | 12, _, _, w, h => obs_store_other' hobs Register.x12 (by decide) h
  | 13, _, _, w, h => obs_store_other' hobs Register.x13 (by decide) h
  | 14, _, _, w, h => obs_store_other' hobs Register.x14 (by decide) h
  | 15, _, _, w, h => obs_store_other' hobs Register.x15 (by decide) h
  | 16, _, _, w, h => obs_store_other' hobs Register.x16 (by decide) h
  | 17, _, _, w, h => obs_store_other' hobs Register.x17 (by decide) h
  | 18, _, _, w, h => obs_store_other' hobs Register.x18 (by decide) h
  | 19, _, _, w, h => obs_store_other' hobs Register.x19 (by decide) h
  | 20, _, _, w, h => obs_store_other' hobs Register.x20 (by decide) h
  | 21, _, _, w, h => obs_store_other' hobs Register.x21 (by decide) h
  | 22, _, _, w, h => obs_store_other' hobs Register.x22 (by decide) h
  | 23, _, _, w, h => obs_store_other' hobs Register.x23 (by decide) h
  | 24, _, _, w, h => obs_store_other' hobs Register.x24 (by decide) h
  | 25, _, _, w, h => obs_store_other' hobs Register.x25 (by decide) h
  | 26, _, _, w, h => obs_store_other' hobs Register.x26 (by decide) h
  | 27, _, _, w, h => obs_store_other' hobs Register.x27 (by decide) h
  | 28, _, _, w, h => obs_store_other' hobs Register.x28 (by decide) h
  | 29, _, _, w, h => obs_store_other' hobs Register.x29 (by decide) h
  | 30, _, _, w, h => obs_store_other' hobs Register.x30 (by decide) h
  | 31, _, _, w, h => obs_store_other' hobs Register.x31 (by decide) h
  | _+32, _, h, _, _ => absurd h (by omega)

/-- All pins survive a STORE step (list form of `obs_gpr_store`). -/
theorem gholds_store {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) :
    ∀ (L : GRegs), KeysOK (keysG L) → GHolds σ L → GHolds σ' L := by
  intro L
  induction L with
  | nil => intro _ _; exact trivial
  | cons p L ih =>
    obtain ⟨n, w⟩ := p
    intro hK hL
    have hn := hK n (List.mem_cons_self ..)
    exact ⟨obs_gpr_store hobs n hn.1 hn.2 w hL.1,
      ih (fun k hk => hK k (List.mem_cons_of_mem _ hk)) hL.2⟩

/-! ## Shared post-step bookkeeping (factored out of the pilot's per-branch copies) -/

/-- Keys of a register-writing step stay in `1..31`. -/
theorem keysOK_cons_erase {n : Nat} (hn1 : 1 ≤ n) (hn31 : n ≤ 31) (L : GRegs)
    (hkeys : KeysOK (keysG L)) : KeysOK (n :: keysG (eraseG n L)) := by
  intro k hk
  cases hk with
  | head => exact ⟨hn1, hn31⟩
  | tail _ h => exact hkeys k (mem_of_mem_keysG_eraseG L h)

/-- The domain extended by the written register stays inside the new keys. -/
theorem dom_cons_erase {n : Nat} {dom : List Nat} {L : GRegs}
    (hdom : ∀ k ∈ dom, k ∈ keysG L) :
    ∀ k ∈ (n :: dom), k ∈ n :: keysG (eraseG n L) := by
  intro k hk
  cases hk with
  | head => exact List.mem_cons_self ..
  | tail _ h =>
    cases Nat.decEq k n with
    | isTrue e => rw [e]; exact List.mem_cons_self ..
    | isFalse ne => exact List.mem_cons_of_mem _ (mem_keysG_eraseG ne L (hdom k h))

/-- One-step register frame through an ALU/load step (noise + the written GPR). -/
theorem frame_step_alu {σ' σ : MState} {pc vm : BitVec 64} {n : Nat} {v : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm (gprReg n) (gprRT n v)))
    (R : Register) (hn : ∀ rr ∈ noiseRegs, (rr == R) = false)
    (hrd : (gprReg n == R) = false) :
    σ'.regs.get? R = σ.regs.get? R :=
  (hobs.1 R (hn Register.mcycle (by decide)) (hn Register.mtime (by decide))
    (hn Register.mip (by decide))).trans
    (get?_sigmaPost_alu σ pc vm (gprReg n) _ R
      (hn Register.minstret (by decide)) (hn Register.PC (by decide))
      hrd (hn Register.nextPC (by decide)) (hn Register.minstret_increment (by decide)))

/-- One-step register frame through a STORE step (noise only). -/
theorem frame_step_store {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m'))
    (R : Register) (hn : ∀ rr ∈ noiseRegs, (rr == R) = false) :
    σ'.regs.get? R = σ.regs.get? R :=
  (hobs.1 R (hn Register.mcycle (by decide)) (hn Register.mtime (by decide))
    (hn Register.mip (by decide))).trans
    (get?_sigmaPost_store σ pc vm m' R
      (hn Register.minstret (by decide)) (hn Register.PC (by decide))
      (hn Register.nextPC (by decide)) (hn Register.minstret_increment (by decide)))

/-! ## The program description -/

/-- Instruction kind: the pilot's ALU classes + signed loads (`lw`/`ld`),
unsigned byte load (`lbu`), and stores (`sw`/`sd`/`sb`).  Width/signedness is
enumerated so all structure stays concrete/decidable.

Extended (the comparison-arm kinds): `addiw`/`slli`/`srli`/`slti`/`slt`/
`subw`/`auipc` — all pure first-order GPR computations backed by the
`ExecuteAlu` characterizations (`execute_addiw_char`, `execute_shiftiop_slli_char`,
`execute_shiftiop_srli_char`, `execute_itype_slti_char`, `execute_rtype_slt_char`,
`execute_rtypew_subw_char`, `execute_utype_auipc_char`). -/
inductive MKind where
  | addi : MKind
  | add  : MKind
  | sub  : MKind
  | lw   : MKind
  | lwu  : MKind
  | ld   : MKind
  | lbu  : MKind
  | sw   : MKind
  | sd   : MKind
  | sb   : MKind
  | addiw : MKind
  | slli  : MKind
  | srli  : MKind
  | slti  : MKind
  | slt   : MKind
  | subw  : MKind
  | auipc : MKind
  | xori  : MKind
  | slliw : MKind
deriving DecidableEq

/-- One straight-line instruction, fully concrete (the pilot's `AInstr` with
memory kinds).  `rd` is the destination for ALU/loads (ignored for stores);
`rs1` is ALU src1 / the load-store *base*; `rs2` is ALU src2 / the store *data*
(ignored otherwise); `imm` is the ITYPE immediate / load-store offset. -/
structure MInstr where
  pc   : BitVec 64
  word : BitVec 32
  b0   : BitVec 8
  b1   : BitVec 8
  b2   : BitVec 8
  b3   : BitVec 8
  kind : MKind
  rd   : Nat
  rs1  : Nat
  rs2  : Nat
  imm  : BitVec 12

/-- Shift amount of `slli`/`srli`: the 6-bit shamt lives in the low 6 bits of
the I-type immediate field (word bits 25..20).  The `extractLsb … 5 0`
wrapping (the shape the `ExecuteAlu` characterizations expect) is applied at
the `wvalM`/use sites. -/
def shamtOf (a : MInstr) : BitVec 6 :=
  a.imm.extractLsb' 0 6

/-- The 20-bit upper immediate of `auipc` (word bits 31..12). -/
def imm20Of (a : MInstr) : BitVec 20 :=
  a.word.extractLsb' 12 20

/-- Shift amount of `slliw` (and the other SHIFTIWOP word-shifts): a **5-bit**
shamt in word bits 24..20 (`BitVec 5` — one bit narrower than `slli`'s 6-bit
`shamtOf`, since a 32-bit shift only ranges over 0..31).  Read off the raw
`word` (not `imm`) so it matches the DecodeTable's `SHIFTIWOP (shamt5, …)`
output exactly. -/
def shamt5Of (a : MInstr) : BitVec 5 :=
  a.word.extractLsb' 20 5

/-- The decoded AST the DecodeTable lemma for `a.word` must produce. -/
def astOfM (a : MInstr) : instruction :=
  match a.kind with
  | .addi => instruction.ITYPE (a.imm, gprIdx a.rs1, gprIdx a.rd, iop.ADDI)
  | .add  => instruction.RTYPE (gprIdx a.rs2, gprIdx a.rs1, gprIdx a.rd, rop.ADD)
  | .sub  => instruction.RTYPE (gprIdx a.rs2, gprIdx a.rs1, gprIdx a.rd, rop.SUB)
  | .lw   => instruction.LOAD (a.imm, gprIdx a.rs1, gprIdx a.rd, false, 4)
  | .lwu  => instruction.LOAD (a.imm, gprIdx a.rs1, gprIdx a.rd, true, 4)
  | .ld   => instruction.LOAD (a.imm, gprIdx a.rs1, gprIdx a.rd, false, 8)
  | .lbu  => instruction.LOAD (a.imm, gprIdx a.rs1, gprIdx a.rd, true, 1)
  | .sw   => instruction.STORE (a.imm, gprIdx a.rs2, gprIdx a.rs1, 4)
  | .sd   => instruction.STORE (a.imm, gprIdx a.rs2, gprIdx a.rs1, 8)
  | .sb   => instruction.STORE (a.imm, gprIdx a.rs2, gprIdx a.rs1, 1)
  | .addiw => instruction.ADDIW (a.imm, gprIdx a.rs1, gprIdx a.rd)
  | .slli  => instruction.SHIFTIOP (shamtOf a, gprIdx a.rs1, gprIdx a.rd, sop.SLLI)
  | .srli  => instruction.SHIFTIOP (shamtOf a, gprIdx a.rs1, gprIdx a.rd, sop.SRLI)
  | .slti  => instruction.ITYPE (a.imm, gprIdx a.rs1, gprIdx a.rd, iop.SLTI)
  | .slt   => instruction.RTYPE (gprIdx a.rs2, gprIdx a.rs1, gprIdx a.rd, rop.SLT)
  | .subw  => instruction.RTYPEW (gprIdx a.rs2, gprIdx a.rs1, gprIdx a.rd, ropw.SUBW)
  | .auipc => instruction.UTYPE (imm20Of a, gprIdx a.rd, uop.AUIPC)
  | .xori  => instruction.ITYPE (a.imm, gprIdx a.rs1, gprIdx a.rd, iop.XORI)
  | .slliw => instruction.SHIFTIWOP (shamt5Of a, gprIdx a.rs1, gprIdx a.rd, sopw.SLLIW)

/-- Effective address of a load/store: base pin + concrete offset. -/
def eaddrM (a : MInstr) (L : GRegs) : BitVec 64 :=
  srcVal a.rs1 L + sign_extend (m := 64) a.imm

/-- Access width of a memory kind (`0` for ALU). -/
def widthOfM : MKind → Nat
  | .lw | .lwu | .sw => 4
  | .ld | .sd => 8
  | .lbu | .sb => 1
  | _ => 0

/-- The value a load writes, from its supplied byte list (LE).  Phrased over
`bs.getD j 0#8` so a literal byte list reduces to the bare symbolic bytes and
no length side condition is needed. -/
def bytesVal (k : MKind) (bs : List (BitVec 8)) : BitVec 64 :=
  match k with
  | .lw => sign_extend (m := 64)
      (((((bs.getD 3 0#8).append (bs.getD 2 0#8)).append (bs.getD 1 0#8)).append
        (bs.getD 0 0#8)) : BitVec (8 * 4))
  | .lwu => zero_extend (m := 64)
      (((((bs.getD 3 0#8).append (bs.getD 2 0#8)).append (bs.getD 1 0#8)).append
        (bs.getD 0 0#8)) : BitVec (8 * 4))
  | .ld => sign_extend (m := 64)
      (((((((((bs.getD 7 0#8).append (bs.getD 6 0#8)).append (bs.getD 5 0#8)).append
        (bs.getD 4 0#8)).append (bs.getD 3 0#8)).append (bs.getD 2 0#8)).append
        (bs.getD 1 0#8)).append (bs.getD 0 0#8)) : BitVec (8 * 8))
  | .lbu => zero_extend (m := 64) ((bs.getD 0 0#8) : BitVec (8 * 1))
  | _ => 0#64

/-- The value written to `rd` (ALU result or loaded value); unused for stores. -/
def wvalM (a : MInstr) (L : GRegs) (bs : List (BitVec 8)) : BitVec 64 :=
  match a.kind with
  | .addi => srcVal a.rs1 L + sign_extend (m := 64) a.imm
  | .add  => srcVal a.rs1 L + srcVal a.rs2 L
  | .sub  => srcVal a.rs1 L - srcVal a.rs2 L
  | .addiw => sign_extend (m := 64)
      (Sail.BitVec.extractLsb (srcVal a.rs1 L + sign_extend (m := 64) a.imm) 31 0)
  | .slli => shift_bits_left (srcVal a.rs1 L) (Sail.BitVec.extractLsb (shamtOf a) 5 0)
  | .srli => shift_bits_right (srcVal a.rs1 L) (Sail.BitVec.extractLsb (shamtOf a) 5 0)
  | .slti => zero_extend (m := 64)
      (bool_to_bit (zopz0zI_s (srcVal a.rs1 L) (sign_extend (m := 64) a.imm)))
  | .slt  => zero_extend (m := 64) (bool_to_bit (zopz0zI_s (srcVal a.rs1 L) (srcVal a.rs2 L)))
  | .subw => sign_extend (m := 64)
      (Sail.BitVec.extractLsb (srcVal a.rs1 L) 31 0
        - Sail.BitVec.extractLsb (srcVal a.rs2 L) 31 0)
  | .auipc => a.pc + sign_extend (m := 64) (imm20Of a +++ (0x000#12))
  | .xori => srcVal a.rs1 L ^^^ sign_extend (m := 64) a.imm
  | .slliw => sign_extend (m := 64)
      (shift_bits_left (Sail.BitVec.extractLsb (srcVal a.rs1 L) 31 0) (shamt5Of a))
  | k => bytesVal k bs

/-- Pin-list effect of one instruction (stores write no register). -/
def stepGM (a : MInstr) (L : GRegs) (bs : List (BitVec 8)) : GRegs :=
  match a.kind with
  | .sw | .sd | .sb => L
  | _ => (a.rd, wvalM a L bs) :: eraseG a.rd L

/-- Load-data consumption: loads pop one byte-list, everything else none. -/
def stepLdsM (k : MKind) (lds : List (List (BitVec 8))) : List (List (BitVec 8)) :=
  match k with
  | .lw | .lwu | .ld | .lbu => lds.tail
  | _ => lds

/-- The write-log entry of a store. -/
def wentryM (a : MInstr) (L : GRegs) : WEntry :=
  ((eaddrM a L).toNat, widthOfM a.kind, srcVal a.rs2 L)

/-- Memory effect of one instruction. -/
def stepMemM (m : Std.ExtHashMap Nat (BitVec 8)) (a : MInstr) (L : GRegs) :
    Std.ExtHashMap Nat (BitVec 8) :=
  match a.kind with
  | .sw | .sd | .sb => applyW m (wentryM a L)
  | _ => m

/-- Pin-list effect of the whole block: the computed register outcome. -/
def runGM : List MInstr → GRegs → List (List (BitVec 8)) → GRegs
  | [], L, _ => L
  | a :: r, L, lds => runGM r (stepGM a L (lds.headD [])) (stepLdsM a.kind lds)

/-- The computed write log of the whole block (program order). -/
def wlogM : List MInstr → GRegs → List (List (BitVec 8)) → List WEntry
  | [], _, _ => []
  | a :: r, L, lds =>
    match a.kind with
    | .sw | .sd | .sb => wentryM a L :: wlogM r L lds
    | _ => wlogM r (stepGM a L (lds.headD [])) (stepLdsM a.kind lds)

/-- Registers written by the block (`rd`s of ALU/load elements). -/
def wrRegsM : List MInstr → List Nat
  | [] => []
  | a :: r =>
    match a.kind with
    | .sw | .sd | .sb => wrRegsM r
    | _ => a.rd :: wrRegsM r

/-- Fall-through end PC of the block. -/
def endPCM (pc0 : BitVec 64) : List MInstr → BitVec 64
  | [] => pc0
  | a :: r => endPCM (BitVec.addInt a.pc 4) r

/-! ## Per-element obligations (`ProgFactsM`) -/

/-- The four little-endian code-byte pins, on the block-entry memory `m0`
(code lives below `tohostAddr`, all stores land above the HTIF window, so entry
pins serve every step — re-established internally via the low-agreement
invariant). -/
def BytePinsM (m : Std.ExtHashMap Nat (BitVec 8)) (a : MInstr) : Prop :=
  m[a.pc.toNat]? = some a.b0 ∧ m[a.pc.toNat + 1]? = some a.b1 ∧
  m[a.pc.toNat + 2]? = some a.b2 ∧ m[a.pc.toNat + 3]? = some a.b3

/-- σ-generic decode fact — the DecodeTable lemma shape, inhabited directly. -/
def DecodeFactM (a : MInstr) : Prop :=
  ∀ s : SequentialState RegisterType trivialChoiceSource,
    s.regs.get? Register.misa = some ((Vsa.Sim.initMisa) : RegisterType Register.misa) →
    s.regs.get? Register.cur_privilege =
      some ((Privilege.Machine) : RegisterType Register.cur_privilege) →
    s.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg) →
    (ext_decode a.word).run s = .ok (astOfM a) s

/-- Load byte pins at widths 4/8 (width 1 is the single pin inline). -/
def LPins4 (m : Std.ExtHashMap Nat (BitVec 8)) (ea : Nat) (bs : List (BitVec 8)) : Prop :=
  m[ea]? = some (bs.getD 0 0#8) ∧ m[ea + 1]? = some (bs.getD 1 0#8) ∧
  m[ea + 2]? = some (bs.getD 2 0#8) ∧ m[ea + 3]? = some (bs.getD 3 0#8)

def LPins8 (m : Std.ExtHashMap Nat (BitVec 8)) (ea : Nat) (bs : List (BitVec 8)) : Prop :=
  m[ea]? = some (bs.getD 0 0#8) ∧ m[ea + 1]? = some (bs.getD 1 0#8) ∧
  m[ea + 2]? = some (bs.getD 2 0#8) ∧ m[ea + 3]? = some (bs.getD 3 0#8) ∧
  m[ea + 4]? = some (bs.getD 4 0#8) ∧ m[ea + 5]? = some (bs.getD 5 0#8) ∧
  m[ea + 6]? = some (bs.getD 6 0#8) ∧ m[ea + 7]? = some (bs.getD 7 0#8)

/-- The data-dependent side conditions of one element: RAM bounds / HTIF window
/ alignment at the *symbolic* effective address, plus (loads) the byte pins on
the threaded memory `m`.  These live here — not in `BlockOKM` — because they
mention symbolic values. -/
def MemFacts (m : Std.ExtHashMap Nat (BitVec 8)) (L : GRegs) (bs : List (BitVec 8))
    (a : MInstr) : Prop :=
  match a.kind with
  | .addi | .add | .sub => True
  | .addiw | .slli | .srli | .slti | .slt | .subw | .auipc | .xori | .slliw => True
  | .lw =>
    (0x80000000 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat + 4 ≤ 0x100000000 ∧
     ((eaddrM a L).toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (eaddrM a L).toNat) ∧
     (eaddrM a L).toNat % 4 = 0) ∧
    LPins4 m (eaddrM a L).toNat bs
  | .lwu =>
    (0x80000000 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat + 4 ≤ 0x100000000 ∧
     ((eaddrM a L).toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (eaddrM a L).toNat) ∧
     (eaddrM a L).toNat % 4 = 0) ∧
    LPins4 m (eaddrM a L).toNat bs
  | .ld =>
    (0x80000000 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat + 8 ≤ 0x100000000 ∧
     ((eaddrM a L).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (eaddrM a L).toNat) ∧
     (eaddrM a L).toNat % 8 = 0) ∧
    LPins8 m (eaddrM a L).toNat bs
  | .lbu =>
    (0x80000000 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat + 1 ≤ 0x100000000 ∧
     ((eaddrM a L).toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (eaddrM a L).toNat)) ∧
    m[(eaddrM a L).toNat]? = some (bs.getD 0 0#8)
  | .sw =>
    0x80000000 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat + 4 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat % 4 = 0
  | .sd =>
    0x80000000 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat + 8 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat % 8 = 0
  | .sb =>
    0x80000000 ≤ (eaddrM a L).toNat ∧ (eaddrM a L).toNat + 1 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ (eaddrM a L).toNat

/-- The non-computable per-element obligations, with the register-pin,
load-data, and memory threads advancing in lockstep with `runGM`/`wlogM`. -/
def ProgFactsM (mc : Std.ExtHashMap Nat (BitVec 8)) :
    Std.ExtHashMap Nat (BitVec 8) → GRegs → List (List (BitVec 8)) → List MInstr → Prop
  | _, _, _, [] => True
  | m, L, lds, a :: r =>
    BytePinsM mc a ∧ DecodeFactM a ∧ MemFacts m L (lds.headD []) a ∧
    ProgFactsM mc (stepMemM m a L) (stepGM a L (lds.headD [])) (stepLdsM a.kind lds) r

/-! ## The computable VC (`BlockOKM`) -/

/-- Per-kind register-index obligations (all decidable, no symbolic values). -/
def KindOK (dom : List Nat) (k : MKind) (rd rs1 rs2 : Nat) : Prop :=
  match k with
  | .addi => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom
  | .add  => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom ∧ SrcOK rs2 dom
  | .sub  => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom ∧ SrcOK rs2 dom
  | .lw | .lwu | .ld | .lbu => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom
  | .sw | .sd | .sb  => SrcOK rs1 dom ∧ SrcOK rs2 dom
  | .addiw | .slti => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom
  | .slli | .srli => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom
  | .slt | .subw  => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom ∧ SrcOK rs2 dom
  | .auipc => (1 ≤ rd ∧ rd ≤ 31)
  | .xori => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom
  | .slliw => (1 ≤ rd ∧ rd ≤ 31) ∧ SrcOK rs1 dom

instance instDecKindOK (dom : List Nat) (k : MKind) (rd rs1 rs2 : Nat) :
    Decidable (KindOK dom k rd rs1 rs2) :=
  match k with
  | .addi => inferInstanceAs (Decidable (_ ∧ _))
  | .add  => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .sub  => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .lw   => inferInstanceAs (Decidable (_ ∧ _))
  | .lwu  => inferInstanceAs (Decidable (_ ∧ _))
  | .ld   => inferInstanceAs (Decidable (_ ∧ _))
  | .lbu  => inferInstanceAs (Decidable (_ ∧ _))
  | .sw   => inferInstanceAs (Decidable (_ ∧ _))
  | .sd   => inferInstanceAs (Decidable (_ ∧ _))
  | .sb   => inferInstanceAs (Decidable (_ ∧ _))
  | .addiw => inferInstanceAs (Decidable (_ ∧ _))
  | .slli  => inferInstanceAs (Decidable (_ ∧ _))
  | .srli  => inferInstanceAs (Decidable (_ ∧ _))
  | .slti  => inferInstanceAs (Decidable (_ ∧ _))
  | .slt   => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .subw  => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .auipc => inferInstanceAs (Decidable (_ ∧ _))
  | .xori  => inferInstanceAs (Decidable (_ ∧ _))
  | .slliw => inferInstanceAs (Decidable (_ ∧ _))

/-- The computable per-instruction VC (structure only — symbolic pin/load/store
*values* are never inspected; the symbolic-address side conditions live in
`MemFacts`). -/
abbrev InstrOKM (pc0 : BitVec 64) (dom : List Nat) (a : MInstr) : Prop :=
  a.pc.toNat = pc0.toNat ∧
  (((a.b3.append a.b2).append a.b1).append a.b0).toNat = a.word.toNat ∧
  (Sail.BitVec.extractLsb (((a.b3.append a.b2).append a.b1).append a.b0) 1 0).toNat
    = (0b11#2 : BitVec 2).toNat ∧
  0x80000000 ≤ a.pc.toNat ∧
  a.pc.toNat + 4 ≤ tohostAddr ∧
  a.pc.toNat % 4 = 0 ∧
  KindOK dom a.kind a.rd a.rs1 a.rs2

/-- Domain threading: stores add nothing, ALU/loads add `rd`. -/
def domStepM (a : MInstr) (dom : List Nat) : List Nat :=
  match a.kind with
  | .sw | .sd | .sb => dom
  | _ => a.rd :: dom

/-- The block VC: per-instruction VCs with PC contiguity and source-domain
threading. -/
def BlockOKM (pc0 : BitVec 64) (dom : List Nat) : List MInstr → Prop
  | [] => True
  | a :: r => InstrOKM pc0 dom a ∧ BlockOKM (BitVec.addInt a.pc 4) (domStepM a dom) r

instance instDecBlockOKM (pc0 : BitVec 64) (dom : List Nat) :
    (is : List MInstr) → Decidable (BlockOKM pc0 dom is)
  | [] => isTrue trivial
  | a :: r =>
    have : Decidable (BlockOKM (BitVec.addInt a.pc 4) (domStepM a dom) r) :=
      instDecBlockOKM _ _ r
    inferInstanceAs (Decidable (_ ∧ _))

/-! ## The block lemma -/

/-- Generalized form: `dom` under-approximates the pinned keys; `mc` is the
code memory (entry memory of the enclosing straight-line run), `m` the current
threaded memory with `∀ j < tohostAddr, m[j]? = mc[j]?`.  Proved by one list
induction; each step goes through `stepObs_alu` (ALU + loads) or
`stepObs_store` (stores). -/
theorem block_mem_run (is : List MInstr) :
    ∀ (σ : MState) (i u : Nat) (pc0 vm : BitVec 64) (L : GRegs)
      (lds : List (List (BitVec 8)))
      (mc m : Std.ExtHashMap Nat (BitVec 8)) (dom : List Nat),
    GoodState σ →
    σ.regs.get? Register.PC = some pc0 →
    σ.regs.get? Register.minstret = some vm →
    σ.mem = m →
    (∀ j, j < tohostAddr → m[j]? = mc[j]?) →
    GHolds σ L →
    KeysOK (keysG L) →
    (∀ n ∈ dom, n ∈ keysG L) →
    ProgFactsM mc m L lds is →
    BlockOKM pc0 dom is →
    i < 2 →
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + is.length⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeLog m (wlogM is L lds) ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (endPCM pc0 is) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' (runGM is L lds) ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ n ∈ wrRegsM is, (gprReg n == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) := by
  induction is with
  | nil =>
    intro σ i u pc0 vm L lds mc m dom hG hpc hmi hmem _ hL _ _ _ _ hi
    exact ⟨σ, i, Steps.refl _, hi, hG, hmem, rfl, hpc, ⟨vm, hmi⟩, hL, fun R _ _ => rfl⟩
  | cons a r ih =>
    intro σ i u pc0 vm L lds mc m dom hG hpc hmi hmem hlow hL hkeys hdom hfacts hwf hi
    subst hmem
    obtain ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ := a
    have hfacts' : BytePinsM mc ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ ∧
        DecodeFactM ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ ∧
        MemFacts σ.mem L (lds.headD [])
          ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ ∧
        ProgFactsM mc
          (stepMemM σ.mem ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ L)
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM akind lds) r := hfacts
    obtain ⟨hbp, hdec, hextra, hfr⟩ := hfacts'
    have hwf' : InstrOKM pc0 dom ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ ∧
        BlockOKM (BitVec.addInt apc 4)
          (domStepM ⟨apc, aword, ab0, ab1, ab2, ab3, akind, ard, ars1, ars2, aimm⟩ dom) r := hwf
    obtain ⟨hwfa, hwfr⟩ := hwf'
    obtain ⟨hpcn, hwn, hrvcn, hlo, hhi, halign, hkok⟩ := hwfa
    have hpceq : apc = pc0 := BitVec.eq_of_toNat_eq hpcn
    subst hpceq
    have hword : (((ab3.append ab2).append ab1).append ab0) = aword :=
      BitVec.eq_of_toNat_eq hwn
    have hnotrvc : Sail.BitVec.extractLsb (((ab3.append ab2).append ab1).append ab0) 1 0
        = (0b11#2 : BitVec 2) := BitVec.eq_of_toNat_eq hrvcn
    have hhi' : apc.toNat + 4 ≤ tohostAddr := hhi
    have hb0 : σ.mem[apc.toNat]? = some ab0 := (hlow _ (by omega)).trans hbp.1
    have hb1 : σ.mem[apc.toNat + 1]? = some ab1 := (hlow _ (by omega)).trans hbp.2.1
    have hb2 : σ.mem[apc.toNat + 2]? = some ab2 := (hlow _ (by omega)).trans hbp.2.2.1
    have hb3 : σ.mem[apc.toNat + 3]? = some ab3 := (hlow _ (by omega)).trans hbp.2.2.2
    have hdec' := hdec (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg)
    cases akind with
    | addi =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .addi ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (srcVal ars1 L + sign_extend (m := 64) aimm) ard hrd1 hrd31
      have hexec := execute_itype_addi_char aimm (gprIdx ars1) (gprIdx ard) (srcVal ars1 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard (srcVal ars1 L + sign_extend (m := 64) aimm)))
        hrx1 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.ITYPE (aimm, gprIdx ars1, gprIdx ard, iop.ADDI))
          (gprReg ard) (gprRT ard (srcVal ars1 L + sign_extend (m := 64) aimm))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .addi, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31 (srcVal ars1 L + sign_extend (m := 64) aimm) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .addi, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .addi, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .addi, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .addi lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | add =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok, hs2ok⟩ :=
        (hkok : KindOK dom .add ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (srcVal ars1 L + srcVal ars2 L) ard hrd1 hrd31
      have hexec := execute_rtype_add_char (gprIdx ars2) (gprIdx ars1) (gprIdx ard)
        (srcVal ars1 L) (srcVal ars2 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard (srcVal ars1 L + srcVal ars2 L)))
        hrx1 hrx2 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.RTYPE (gprIdx ars2, gprIdx ars1, gprIdx ard, rop.ADD))
          (gprReg ard) (gprRT ard (srcVal ars1 L + srcVal ars2 L))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .add, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31 (srcVal ars1 L + srcVal ars2 L) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .add, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .add, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .add, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .add lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | sub =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok, hs2ok⟩ :=
        (hkok : KindOK dom .sub ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (srcVal ars1 L - srcVal ars2 L) ard hrd1 hrd31
      have hexec := execute_rtype_sub_char (gprIdx ars2) (gprIdx ars1) (gprIdx ard)
        (srcVal ars1 L) (srcVal ars2 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard (srcVal ars1 L - srcVal ars2 L)))
        hrx1 hrx2 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.RTYPE (gprIdx ars2, gprIdx ars1, gprIdx ard, rop.SUB))
          (gprReg ard) (gprRT ard (srcVal ars1 L - srcVal ars2 L))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sub, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31 (srcVal ars1 L - srcVal ars2 L) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sub, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sub, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .sub, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .sub lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | lw =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .lw ard ars1 ars2)
      obtain ⟨⟨halo, hahiram, hahtif, haalign⟩, hp0, hp1, hp2, hp3⟩ := hextra
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (bytesVal .lw (lds.headD [])) ard hrd1 hrd31
      have hexec := exec_lw σ apc aimm (gprIdx ars1) (gprIdx ard)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard (bytesVal .lw (lds.headD []))))
        (srcVal ars1 L)
        ((lds.headD []).getD 0 0#8) ((lds.headD []).getD 1 0#8)
        ((lds.headD []).getD 2 0#8) ((lds.headD []).getD 3 0#8)
        hG hrx1 hwx halo hahiram hahtif haalign hp0 hp1 hp2 hp3
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.LOAD (aimm, gprIdx ars1, gprIdx ard, false, 4))
          (gprReg ard) (gprRT ard (bytesVal .lw (lds.headD [])))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31 (bytesVal .lw (lds.headD [])) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lw, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lw, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .lw lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | lwu =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .lwu ard ars1 ars2)
      obtain ⟨⟨halo, hahiram, hahtif, haalign⟩, hp0, hp1, hp2, hp3⟩ := hextra
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (bytesVal .lwu (lds.headD [])) ard hrd1 hrd31
      have hexec := exec_lwu σ apc aimm (gprIdx ars1) (gprIdx ard)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard (bytesVal .lwu (lds.headD []))))
        (srcVal ars1 L)
        ((lds.headD []).getD 0 0#8) ((lds.headD []).getD 1 0#8)
        ((lds.headD []).getD 2 0#8) ((lds.headD []).getD 3 0#8)
        hG hrx1 hwx halo hahiram hahtif haalign hp0 hp1 hp2 hp3
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.LOAD (aimm, gprIdx ars1, gprIdx ard, true, 4))
          (gprReg ard) (gprRT ard (bytesVal .lwu (lds.headD [])))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lwu, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31 (bytesVal .lwu (lds.headD [])) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lwu, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lwu, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lwu, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .lwu lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | ld =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .ld ard ars1 ars2)
      obtain ⟨⟨halo, hahiram, hahtif, haalign⟩, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7⟩ := hextra
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (bytesVal .ld (lds.headD [])) ard hrd1 hrd31
      have hexec := exec_ld σ apc aimm (gprIdx ars1) (gprIdx ard)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard (bytesVal .ld (lds.headD []))))
        (srcVal ars1 L)
        ((lds.headD []).getD 0 0#8) ((lds.headD []).getD 1 0#8)
        ((lds.headD []).getD 2 0#8) ((lds.headD []).getD 3 0#8)
        ((lds.headD []).getD 4 0#8) ((lds.headD []).getD 5 0#8)
        ((lds.headD []).getD 6 0#8) ((lds.headD []).getD 7 0#8)
        hG hrx1 hwx halo hahiram hahtif haalign hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.LOAD (aimm, gprIdx ars1, gprIdx ard, false, 8))
          (gprReg ard) (gprRT ard (bytesVal .ld (lds.headD [])))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .ld, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31 (bytesVal .ld (lds.headD [])) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .ld, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .ld, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .ld, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .ld lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | lbu =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .lbu ard ars1 ars2)
      obtain ⟨⟨halo, hahiram, hahtif⟩, hp0⟩ := hextra
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (bytesVal .lbu (lds.headD [])) ard hrd1 hrd31
      have hexec := exec_lbu_bm σ apc aimm (gprIdx ars1) (gprIdx ard)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard (bytesVal .lbu (lds.headD []))))
        (srcVal ars1 L) ((lds.headD []).getD 0 0#8)
        hG hrx1 hwx halo hahiram hahtif hp0
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.LOAD (aimm, gprIdx ars1, gprIdx ard, true, 1))
          (gprReg ard) (gprRT ard (bytesVal .lbu (lds.headD [])))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lbu, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31 (bytesVal .lbu (lds.headD [])) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lbu, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lbu, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .lbu, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .lbu lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | sw =>
      obtain ⟨hs1ok, hs2ok⟩ := (hkok : KindOK dom .sw ard ars1 ars2)
      obtain ⟨halo, hahiram, hahiwin, haalign⟩ := hextra
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hexec := exec_sw σ apc aimm (gprIdx ars2) (gprIdx ars1)
        (srcVal ars1 L) (srcVal ars2 L) hG hrx1 hrx2 halo hahiram hahiwin haalign
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_store σ i u apc vm aword
          (instruction.STORE (aimm, gprIdx ars2, gprIdx ars1, 4))
          (writeMap4 (afterNextPC (afterPrelude σ) apc).mem
            (srcVal ars1 L + sign_extend (m := 64) aimm).toNat (swData (srcVal ars2 L)))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_store_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_store_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1 L := gholds_store hobs1 L hkeys hL
      have hmem1' : σ1.mem = stepMemM σ.mem
          ⟨apc, aword, ab0, ab1, ab2, ab3, .sw, ard, ars1, ars2, aimm⟩ L := hmem1
      have hlow1 : ∀ j, j < tohostAddr →
          (stepMemM σ.mem ⟨apc, aword, ab0, ab1, ab2, ab3, .sw, ard, ars1, ars2, aimm⟩ L)[j]?
            = mc[j]? := by
        intro j hj
        exact (writeMap4_low_miss σ.mem _ _ j (by omega)).trans (hlow j hj)
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1 L
          (stepLdsM .sw lds) mc
          (stepMemM σ.mem ⟨apc, aword, ab0, ab1, ab2, ab3, .sw, ard, ars1, ars2, aimm⟩ L) dom
          hG1 hpc1 hmi1 hmem1' hlow1 hL1 hkeys hdom hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn hrds).trans (frame_step_store hobs1 R hn)
    | sd =>
      obtain ⟨hs1ok, hs2ok⟩ := (hkok : KindOK dom .sd ard ars1 ars2)
      obtain ⟨halo, hahiram, hahiwin, haalign⟩ := hextra
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hexec := exec_sd_val σ apc aimm (gprIdx ars2) (gprIdx ars1)
        (srcVal ars1 L) (srcVal ars2 L) hG hrx1 hrx2 halo hahiram hahiwin haalign
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_store σ i u apc vm aword
          (instruction.STORE (aimm, gprIdx ars2, gprIdx ars1, 8))
          (writeMap8 (afterNextPC (afterPrelude σ) apc).mem
            (srcVal ars1 L + sign_extend (m := 64) aimm).toNat (sdData_val (srcVal ars2 L)))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_store_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_store_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1 L := gholds_store hobs1 L hkeys hL
      have hmem1' : σ1.mem = stepMemM σ.mem
          ⟨apc, aword, ab0, ab1, ab2, ab3, .sd, ard, ars1, ars2, aimm⟩ L := hmem1
      have hlow1 : ∀ j, j < tohostAddr →
          (stepMemM σ.mem ⟨apc, aword, ab0, ab1, ab2, ab3, .sd, ard, ars1, ars2, aimm⟩ L)[j]?
            = mc[j]? := by
        intro j hj
        exact (writeMap8_low_miss σ.mem _ _ j (by omega)).trans (hlow j hj)
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1 L
          (stepLdsM .sd lds) mc
          (stepMemM σ.mem ⟨apc, aword, ab0, ab1, ab2, ab3, .sd, ard, ars1, ars2, aimm⟩ L) dom
          hG1 hpc1 hmi1 hmem1' hlow1 hL1 hkeys hdom hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn hrds).trans (frame_step_store hobs1 R hn)
    | sb =>
      obtain ⟨hs1ok, hs2ok⟩ := (hkok : KindOK dom .sb ard ars1 ars2)
      obtain ⟨halo, hahiram, hahiwin⟩ := hextra
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hexec := exec_sb_bm σ apc aimm (gprIdx ars2) (gprIdx ars1)
        (srcVal ars1 L) (srcVal ars2 L) hG hrx1 hrx2 halo hahiram hahiwin
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_store σ i u apc vm aword
          (instruction.STORE (aimm, gprIdx ars2, gprIdx ars1, 1))
          ((afterNextPC (afterPrelude σ) apc).mem.insert
            (srcVal ars1 L + sign_extend (m := 64) aimm).toNat (sbData (srcVal ars2 L)))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_store_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_store_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1 L := gholds_store hobs1 L hkeys hL
      have hmem1' : σ1.mem = stepMemM σ.mem
          ⟨apc, aword, ab0, ab1, ab2, ab3, .sb, ard, ars1, ars2, aimm⟩ L := hmem1
      have hlow1 : ∀ j, j < tohostAddr →
          (stepMemM σ.mem ⟨apc, aword, ab0, ab1, ab2, ab3, .sb, ard, ars1, ars2, aimm⟩ L)[j]?
            = mc[j]? := by
        intro j hj
        exact (insert_low_miss σ.mem _ _ j (by omega)).trans (hlow j hj)
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1 L
          (stepLdsM .sb lds) mc
          (stepMemM σ.mem ⟨apc, aword, ab0, ab1, ab2, ab3, .sb, ard, ars1, ars2, aimm⟩ L) dom
          hG1 hpc1 hmi1 hmem1' hlow1 hL1 hkeys hdom hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn hrds).trans (frame_step_store hobs1 R hn)
    | addiw =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .addiw ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (srcVal ars1 L + sign_extend (m := 64) aimm) 31 0)) ard hrd1 hrd31
      have hexec := execute_addiw_char aimm (gprIdx ars1) (gprIdx ard) (srcVal ars1 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb (srcVal ars1 L + sign_extend (m := 64) aimm) 31 0))))
        hrx1 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.ADDIW (aimm, gprIdx ars1, gprIdx ard))
          (gprReg ard) (gprRT ard
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb (srcVal ars1 L + sign_extend (m := 64) aimm) 31 0)))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .addiw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb (srcVal ars1 L + sign_extend (m := 64) aimm) 31 0)) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .addiw, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .addiw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .addiw, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .addiw lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | slli =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .slli ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (shift_bits_left (srcVal ars1 L)
          (Sail.BitVec.extractLsb (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .slli, ard, ars1, ars2, aimm⟩) 5 0))
        ard hrd1 hrd31
      have hexec := execute_shiftiop_slli_char
          (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .slli, ard, ars1, ars2, aimm⟩)
          (gprIdx ars1) (gprIdx ard) (srcVal ars1 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (shift_bits_left (srcVal ars1 L)
            (Sail.BitVec.extractLsb (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .slli, ard, ars1, ars2, aimm⟩) 5 0))))
        hrx1 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.SHIFTIOP (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .slli, ard, ars1, ars2, aimm⟩,
            gprIdx ars1, gprIdx ard, sop.SLLI))
          (gprReg ard) (gprRT ard
            (shift_bits_left (srcVal ars1 L)
              (Sail.BitVec.extractLsb (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .slli, ard, ars1, ars2, aimm⟩) 5 0)))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slli, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (shift_bits_left (srcVal ars1 L)
              (Sail.BitVec.extractLsb (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .slli, ard, ars1, ars2, aimm⟩) 5 0)) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slli, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slli, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slli, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .slli lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | srli =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .srli ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (shift_bits_right (srcVal ars1 L)
          (Sail.BitVec.extractLsb (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .srli, ard, ars1, ars2, aimm⟩) 5 0))
        ard hrd1 hrd31
      have hexec := execute_shiftiop_srli_char
          (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .srli, ard, ars1, ars2, aimm⟩)
          (gprIdx ars1) (gprIdx ard) (srcVal ars1 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (shift_bits_right (srcVal ars1 L)
            (Sail.BitVec.extractLsb (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .srli, ard, ars1, ars2, aimm⟩) 5 0))))
        hrx1 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.SHIFTIOP (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .srli, ard, ars1, ars2, aimm⟩,
            gprIdx ars1, gprIdx ard, sop.SRLI))
          (gprReg ard) (gprRT ard
            (shift_bits_right (srcVal ars1 L)
              (Sail.BitVec.extractLsb (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .srli, ard, ars1, ars2, aimm⟩) 5 0)))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srli, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (shift_bits_right (srcVal ars1 L)
              (Sail.BitVec.extractLsb (shamtOf ⟨apc, aword, ab0, ab1, ab2, ab3, .srli, ard, ars1, ars2, aimm⟩) 5 0)) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srli, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srli, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .srli, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .srli lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | slti =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .slti ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (zero_extend (m := 64)
          (bool_to_bit (zopz0zI_s (srcVal ars1 L) (sign_extend (m := 64) aimm)))) ard hrd1 hrd31
      have hexec := execute_itype_slti_char aimm (gprIdx ars1) (gprIdx ard) (srcVal ars1 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (zero_extend (m := 64)
            (bool_to_bit (zopz0zI_s (srcVal ars1 L) (sign_extend (m := 64) aimm))))))
        hrx1 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.ITYPE (aimm, gprIdx ars1, gprIdx ard, iop.SLTI))
          (gprReg ard) (gprRT ard
            (zero_extend (m := 64)
              (bool_to_bit (zopz0zI_s (srcVal ars1 L) (sign_extend (m := 64) aimm)))))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slti, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (zero_extend (m := 64)
              (bool_to_bit (zopz0zI_s (srcVal ars1 L) (sign_extend (m := 64) aimm)))) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slti, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slti, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slti, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .slti lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | xori =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .xori ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (srcVal ars1 L ^^^ sign_extend (m := 64) aimm) ard hrd1 hrd31
      have hexec := execute_itype_xori_char aimm (gprIdx ars1) (gprIdx ard) (srcVal ars1 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (srcVal ars1 L ^^^ sign_extend (m := 64) aimm)))
        hrx1 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.ITYPE (aimm, gprIdx ars1, gprIdx ard, iop.XORI))
          (gprReg ard) (gprRT ard
            (srcVal ars1 L ^^^ sign_extend (m := 64) aimm))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .xori, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (srcVal ars1 L ^^^ sign_extend (m := 64) aimm) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .xori, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .xori, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .xori, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .xori lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | slliw =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok⟩ :=
        (hkok : KindOK dom .slliw ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (sign_extend (m := 64)
          (shift_bits_left (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0)
            (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .slliw, ard, ars1, ars2, aimm⟩)))
        ard hrd1 hrd31
      have hexec := execute_shiftiwop_slliw_char
          (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .slliw, ard, ars1, ars2, aimm⟩)
          (gprIdx ars1) (gprIdx ard) (srcVal ars1 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (sign_extend (m := 64)
            (shift_bits_left (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0)
              (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .slliw, ard, ars1, ars2, aimm⟩)))))
        hrx1 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.SHIFTIWOP (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .slliw, ard, ars1, ars2, aimm⟩,
            gprIdx ars1, gprIdx ard, sopw.SLLIW))
          (gprReg ard) (gprRT ard
            (sign_extend (m := 64)
              (shift_bits_left (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0)
                (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .slliw, ard, ars1, ars2, aimm⟩))))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slliw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (sign_extend (m := 64)
              (shift_bits_left (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0)
                (shamt5Of ⟨apc, aword, ab0, ab1, ab2, ab3, .slliw, ard, ars1, ars2, aimm⟩))) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slliw, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slliw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slliw, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .slliw lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | slt =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok, hs2ok⟩ :=
        (hkok : KindOK dom .slt ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (srcVal ars1 L) (srcVal ars2 L)))) ard hrd1 hrd31
      have hexec := execute_rtype_slt_char (gprIdx ars2) (gprIdx ars1) (gprIdx ard)
        (srcVal ars1 L) (srcVal ars2 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (srcVal ars1 L) (srcVal ars2 L))))))
        hrx1 hrx2 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.RTYPE (gprIdx ars2, gprIdx ars1, gprIdx ard, rop.SLT))
          (gprReg ard) (gprRT ard
            (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (srcVal ars1 L) (srcVal ars2 L)))))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slt, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (srcVal ars1 L) (srcVal ars2 L)))) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slt, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slt, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .slt, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .slt lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | subw =>
      obtain ⟨⟨hrd1, hrd31⟩, hs1ok, hs2ok⟩ :=
        (hkok : KindOK dom .subw ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hsp1 : srcPin σ ars1 (srcVal ars1 L) :=
        srcPin_srcVal σ L ars1 (hs1ok.2.imp (fun h => h) (hdom ars1)) hL
      have hrx1 := rX_src σ apc ars1 hs1ok.1 (srcVal ars1 L) hsp1
      have hsp2 : srcPin σ ars2 (srcVal ars2 L) :=
        srcPin_srcVal σ L ars2 (hs2ok.2.imp (fun h => h) (hdom ars2)) hL
      have hrx2 := rX_src σ apc ars2 hs2ok.1 (srcVal ars2 L) hsp2
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0
            - Sail.BitVec.extractLsb (srcVal ars2 L) 31 0)) ard hrd1 hrd31
      have hexec := execute_rtypew_subw_char (gprIdx ars2) (gprIdx ars1) (gprIdx ard)
        (srcVal ars1 L) (srcVal ars2 L)
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0
              - Sail.BitVec.extractLsb (srcVal ars2 L) 31 0))))
        hrx1 hrx2 hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.RTYPEW (gprIdx ars2, gprIdx ars1, gprIdx ard, ropw.SUBW))
          (gprReg ard) (gprRT ard
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0
                - Sail.BitVec.extractLsb (srcVal ars2 L) 31 0)))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .subw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb (srcVal ars1 L) 31 0
                - Sail.BitVec.extractLsb (srcVal ars2 L) 31 0)) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .subw, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .subw, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .subw, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .subw lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))
    | auipc =>
      obtain ⟨hrd1, hrd31⟩ :=
        (hkok : KindOK dom .auipc ard ars1 ars2)
      have hrd31' : ard ≤ 31 := hrd31
      have hrdf := gpr_rd_ok ard (Nat.lt_succ_of_le hrd31') hrd1
      have hwx := wX_gpr (afterNextPC (afterPrelude σ) apc)
        (apc + sign_extend (m := 64)
          (imm20Of ⟨apc, aword, ab0, ab1, ab2, ab3, .auipc, ard, ars1, ars2, aimm⟩ +++ (0x000#12)))
        ard hrd1 hrd31
      have hpc₂ : (afterNextPC (afterPrelude σ) apc).regs.get? Register.PC = some apc := by
        rw [get?_afterNextPC σ apc _ (by decide) (by decide)]; exact hpc
      have hexec := execute_utype_auipc_char
          (imm20Of ⟨apc, aword, ab0, ab1, ab2, ab3, .auipc, ard, ars1, ars2, aimm⟩)
          (gprIdx ard) apc
        (afterNextPC (afterPrelude σ) apc)
        (sigma3_alu σ apc (gprReg ard) (gprRT ard
          (apc + sign_extend (m := 64)
            (imm20Of ⟨apc, aword, ab0, ab1, ab2, ab3, .auipc, ard, ars1, ars2, aimm⟩ +++ (0x000#12)))))
        hpc₂ hwx
      obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
        stepObs_alu σ i u apc vm aword
          (instruction.UTYPE (imm20Of ⟨apc, aword, ab0, ab1, ab2, ab3, .auipc, ard, ars1, ars2, aimm⟩,
            gprIdx ard, uop.AUIPC))
          (gprReg ard) (gprRT ard
            (apc + sign_extend (m := 64)
              (imm20Of ⟨apc, aword, ab0, ab1, ab2, ab3, .auipc, ard, ars1, ars2, aimm⟩ +++ (0x000#12))))
          ab0 ab1 ab2 ab3 hG hpc hmi hword hnotrvc hdec' hexec
          hrdf.1 hrdf.2.1 hrdf.2.2.1 hrdf.2.2.2.1 hrdf.2.2.2.2
          hb0 hb1 hb2 hb3 hlo hhi halign hi
      have hpc1 := obs_alu_pc hobs1
      obtain ⟨vm1, hmi1⟩ := obs_alu_minstret hobs1
      have hout1 : σ1.sailOutput = σ.sailOutput := hobs1.2
      have hL1 : GHolds σ1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .auipc, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        ⟨obs_gpr_rd ard hrd1 hrd31
            (apc + sign_extend (m := 64)
              (imm20Of ⟨apc, aword, ab0, ab1, ab2, ab3, .auipc, ard, ars1, ars2, aimm⟩ +++ (0x000#12))) hobs1,
         gholds_eraseG hobs1 hrd1 hrd31 L hkeys hL⟩
      have hkeys1 : KeysOK (keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .auipc, ard, ars1, ars2, aimm⟩ L (lds.headD []))) :=
        keysOK_cons_erase hrd1 hrd31 L hkeys
      have hdom1 : ∀ n ∈ (ard :: dom), n ∈ keysG
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .auipc, ard, ars1, ars2, aimm⟩ L (lds.headD [])) :=
        dom_cons_erase hdom
      obtain ⟨σf, i', hsteps, hi', hGf, hmemf, houtf, hpcf, hmif, hGHf, hframef⟩ :=
        ih σ1 i1 (u + 1) (BitVec.addInt apc 4) vm1
          (stepGM ⟨apc, aword, ab0, ab1, ab2, ab3, .auipc, ard, ars1, ars2, aimm⟩ L (lds.headD []))
          (stepLdsM .auipc lds) mc σ.mem (ard :: dom)
          hG1 hpc1 hmi1 hmem1 hlow hL1 hkeys1 hdom1 hfr hwfr hi1
      refine ⟨σf, i', ?_, hi', hGf, hmemf, houtf.trans hout1, hpcf, hmif, hGHf, ?_⟩
      · have hsteps' : Steps ⟨σ, i, u⟩ ⟨σf, i', u + 1 + r.length⟩ := Steps.head hs1 hsteps
        have e : u + 1 + r.length = u + (r.length + 1) := by omega
        rw [e] at hsteps'
        exact hsteps'
      · intro R hn hrds
        exact (hframef R hn (fun a' ha' => hrds a' (List.mem_cons_of_mem _ ha'))).trans
          (frame_step_alu hobs1 R hn (hrds _ (List.mem_cons_self ..)))

/-- **The block lemma.** A concrete list of straight-line ALU/load/store
instructions, with per-element byte pins + decode facts + data-dependent
address side conditions and load-data pins (`ProgFactsM`) and a decidable
structural VC (`BlockOKM`, one `by decide`), turns an entry state with pinned
PC / minstret / source registers into the full `Steps` chain with: tick
invariant, `GoodState`, HTIF output unchanged, the fall-through PC, the
*computed* register outcome `runGM is L lds`, the *computed* memory outcome
`writeLog σ.mem (wlogM is L lds)`, and the register frame outside
`noiseRegs ∪ wrRegsM is`. -/
theorem block_mem_sound (is : List MInstr) (σ : MState) (i u : Nat)
    (pc0 vm : BitVec 64) (L : GRegs) (lds : List (List (BitVec 8)))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some pc0)
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hL : GHolds σ L)
    (hkeys : KeysOK (keysG L))
    (hfacts : ProgFactsM σ.mem σ.mem L lds is)
    (hwf : BlockOKM pc0 (keysG L) is)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ', i', u + is.length⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeLog σ.mem (wlogM is L lds) ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC = some (endPCM pc0 is) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' (runGM is L lds) ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ n ∈ wrRegsM is, (gprReg n == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) :=
  block_mem_run is σ i u pc0 vm L lds σ.mem σ.mem (keysG L)
    hG hpc hmi rfl (fun _ _ => rfl) hL hkeys (fun _ h => h) hfacts hwf hi

end Vsa.Sim
