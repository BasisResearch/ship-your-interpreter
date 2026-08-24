import Vsa.Sim.EnvGetSites2
import Vsa.Sim.Muldi3Spec
import Vsa.Sim.StrcmpSpecW4
import Vsa.RuntimeRepr
import Vsa.While.Semantics
import Vsa.Triple

/-!
# Layer 3 — total-correctness spec for `env_get` (WORK IN PROGRESS FOUNDATION)

Config-level (`Vsa.Logic.Triple`) target: a total-correctness triple for
`env_get(env, name, out)` (`c/src/env.c`, entry `0x80002c10`), the M4-critical
`eval_expr` variable lookup.  The per-site observational steps are landed and
verified in `Vsa/Sim/EnvGetSites.lean` (foundation, `_eg`) and
`Vsa/Sim/EnvGetSites2.lean` (this cluster, `_eg2`) — every one of the 51
instructions has a `stepObs_*` lemma.

This file holds the **reusable, fully-verified composition scaffold**: the
blanket ghost-frame predicate `NotWrittenEG`, the generic per-instruction-class
frame lemmas, and the register-disequality helpers.  These are the same shape as
`EnvNewSpec`'s `NotWrittenEnv`/`frame_*_env` (cloned here with the `_eg` suffix,
tracking `env_get`'s written GPR set) and are the pieces every transition in the
eventual scan-loop / chain-walk triple consumes.

## The two-loop structure (design settled — for the next increment)

`env_get` is a nested loop:

* **Scan loop** (`0x80002c54 … 0x80002c6c`, head-test at `0x80002c5c`,
  back-edge `0x80002c6c → 0x80002c54`): linear scan of `names[0..count)`.  Each
  iteration composes `strcmp(names[i], name)` (via `strcmp_full_spec` at
  `StrcmpSpecW4`; the callee P needs `StrcmpLoaded`, `MaskPinned` at the rodata
  the strcmp reads, `CString` on both argument buffers, the `StrcmpRegion`/
  `WRegion` disjointness, and a ghost tie).  The env code then tests the result
  `== 0` via the `bnez a0` at `0x80002c6c` (`site_80002c6c_{taken,nottaken}_eg2`):
  taken (≠0) ⇒ next iteration; not-taken (==0) ⇒ HIT.  Measure = `count - i`,
  PC-guarded per `DivLoops`.

* **Chain-walk loop** (`0x80002cc4 … 0x80002cc8`, back-edge `0x80002cc8 →
  0x80002c40`): descends `env = env->parent` until NULL.  Measure = the
  **spec-side gas** of `Store.lookup` (its fuel is `frames.size`, threaded as a
  decrementing `Nat`; `StoreRepr` has NO acyclicity field — do not look for one).

## The chain-walk correspondence `P` (settled form)

The walker's `P` carries an `EnvRepr`/`StoreRepr` correspondence for the walked
chain: each machine env pointer equals `φf` of a spec frame address whose
`Store.lookup` visits in the same order.  Concretely, the loop invariant threads:

* a spec-side `store : StoreRepr` and a `chain : List Vsa.While.Addr` of the
  frame addresses still to visit, with `chain.head?` corresponding to the current
  machine `s4 = env` pointer through `φf` (NULL ⇔ `chain = []`);
* `FrameRepr store.mem N φf φc (φf a) (store.frames a)` for each visited `a`
  (count@0 read32, names@8 stride 8, vals@16 stride 24, parent@24 — see
  `RuntimeRepr`);
* the gas `= chain.length`, strictly decreasing on each descend, matching
  `Store.lookup`'s `frames.size` fuel.

## `Q` (settled form)

* **HIT**: `a0 = 1`, `*out` (the 24-byte `Value` window at `s5`) equals the
  `ValueRepr`-image of the found `Store.lookup … name` value, memory framed
  outside the `out`-window (pure walker: no allocator, nothing else changes),
  related to `Store.get?` in `Vsa/While/Semantics.lean` exactly.
* **MISS** (through the whole chain): `a0 = 0`, memory unchanged.

`env_set` is structurally identical (HIT stores 24B INTO `vals[i]`; `Q` is a
`writeMap`-described update + `FrameRepr` re-established + `Store.set`
correspondence) and reuses this scaffold with `_es` names.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step)
open Vsa.Sim.Code (Env_getLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Blanket ghost-frame predicate (`NotWrittenEG`) + generic per-class helpers

`env_get`'s straight-line paths write GPRs `x1` (ra), `x2` (sp), `x8` (s0/i),
`x9` (s1/names-ptr), `x10`–`x15` (a0–a5 scratch), `x18`–`x21` (s2–s5).
`NotWrittenEG R` is the disequality conjunction over those written GPRs and the
per-step write-set / tick-set registers, so preservation of every *other*
register is recovered through the blanket ghost-frame conjunct.  (Because
`env_get` clobbers essentially all caller/temp registers it spills, in practice
callers tie only the ABI-preserved set through the spill/restore; this predicate
is the exhaustive machine-level write set used by the internal transitions.) -/

/-- `R` is outside the union of `env_get`'s written GPRs and every register any
hot-path step (ALU / branch / store / jump / tick) can write. -/
abbrev NotWrittenEG (R : Register) : Prop :=
  (Register.x1 == R) = false ∧ (Register.x2 == R) = false ∧
  (Register.x8 == R) = false ∧ (Register.x9 == R) = false ∧
  (Register.x10 == R) = false ∧ (Register.x11 == R) = false ∧
  (Register.x12 == R) = false ∧ (Register.x13 == R) = false ∧
  (Register.x14 == R) = false ∧ (Register.x15 == R) = false ∧
  (Register.x18 == R) = false ∧ (Register.x19 == R) = false ∧
  (Register.x20 == R) = false ∧ (Register.x21 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

theorem NotWrittenEG.pc {R : Register} (h : NotWrittenEG R) : (Register.PC == R) = false :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem NotWrittenEG.nextPC {R : Register} (h : NotWrittenEG R) : (Register.nextPC == R) = false :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem NotWrittenEG.minstret {R : Register} (h : NotWrittenEG R) : (Register.minstret == R) = false :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem NotWrittenEG.minstret_increment {R : Register} (h : NotWrittenEG R) :
    (Register.minstret_increment == R) = false := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem NotWrittenEG.mcycle {R : Register} (h : NotWrittenEG R) : (Register.mcycle == R) = false :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem NotWrittenEG.mtime {R : Register} (h : NotWrittenEG R) : (Register.mtime == R) = false :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem NotWrittenEG.mip {R : Register} (h : NotWrittenEG R) : (Register.mip == R) = false :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- Generic ALU frame step (covers `mv`/`li`/`addi`/`slli`/`add` and the ALU-class
`lw`/`ld` loads). -/
theorem frame_alu_eg {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) (R : Register)
    (hrd : (rd == R) = false) (hR : NotWrittenEG R) :
    σ'.regs.get? R = σ.regs.get? R := by
  rw [hobs.1 R hR.mcycle hR.mtime hR.mip]
  exact get?_sigmaPost_alu σ pc vm rd v R hR.minstret hR.pc hrd hR.nextPC hR.minstret_increment

/-- Generic not-taken-branch frame step. -/
theorem frame_bnottaken_eg {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register)
    (hR : NotWrittenEG R) : σ'.regs.get? R = σ.regs.get? R := by
  rw [hobs.1 R hR.mcycle hR.mtime hR.mip]
  exact get?_sigmaPost_branch_nottaken σ pc vm R hR.minstret hR.pc hR.nextPC hR.minstret_increment

/-- Generic taken-branch frame step. -/
theorem frame_btaken_eg {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) (R : Register)
    (hR : NotWrittenEG R) : σ'.regs.get? R = σ.regs.get? R := by
  rw [hobs.1 R hR.mcycle hR.mtime hR.mip]
  exact get?_sigmaPost_branch_taken σ pc vm imm R hR.minstret hR.pc hR.nextPC hR.minstret_increment

/-- Generic STORE frame step (no `rd`). -/
theorem frame_store_eg {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) (R : Register)
    (hR : NotWrittenEG R) : σ'.regs.get? R = σ.regs.get? R := by
  rw [hobs.1 R hR.mcycle hR.mtime hR.mip]
  exact get?_sigmaPost_store σ pc vm m' R hR.minstret hR.pc hR.nextPC hR.minstret_increment

/-- Generic `jal` frame step (write-set `rd = x1, PC, minstret, nextPC, minstret_increment`). -/
theorem frame_jal_eg {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) (R : Register)
    (hrd : (rd_reg == R) = false) (hR : NotWrittenEG R) :
    σ'.regs.get? R = σ.regs.get? R := by
  rw [hobs.1 R hR.mcycle hR.mtime hR.mip]
  exact get?_sigmaPost_jal σ pc vm imm rd_reg link R hR.minstret hR.pc hrd hR.nextPC hR.minstret_increment

/-- Generic `jr`/`ret`/`j` (`jump_x0`) frame step. -/
theorem frame_jump_x0_eg {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register)
    (hR : NotWrittenEG R) : σ'.regs.get? R = σ.regs.get? R := by
  rw [hobs.1 R hR.mcycle hR.mtime hR.mip]
  exact get?_sigmaPost_jump_x0 σ pc vm tgt R hR.minstret hR.pc hR.nextPC hR.minstret_increment

/-! ## Observation read-back consumers (PC / rd / minstret), reusing `readback`

These lift the `sigmaPost_*` field reads to `σ'` through the tick chain, exactly
as the `obs_*` families in `Muldi3Spec`/`ValueSpec` do; provided here specialised
to the read-backs the eventual triple needs. -/

/-- Read the PC of an ALU step off `σ'`: `PC = pc + 4`. -/
theorem obs_alu_pc_eg {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) :
    σ'.regs.get? Register.PC = some (BitVec.addInt pc 4) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_alu_pc σ pc vm rd v)

/-- Read the destination of an ALU step off `σ'`: `rd = v`. -/
theorem obs_alu_rd_eg {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v))
    (hmc : (Register.mcycle == rd) = false) (hmt : (Register.mtime == rd) = false)
    (hmi : (Register.mip == rd) = false)
    (hrd_ms : (Register.minstret == rd) = false) (hrd_pc : (Register.PC == rd) = false) :
    σ'.regs.get? rd = some v :=
  readback σ' _ hobs rd hmc hmt hmi (post_alu_rd σ pc vm rd v hrd_ms hrd_pc)

/-- Read the PC of a taken branch off `σ'`: `PC = pc + sext imm`. -/
theorem obs_btaken_pc_eg {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) :
    σ'.regs.get? Register.PC = some (pc + sign_extend (m := 64) imm) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_branch_taken_pc σ pc vm imm)

/-- Read the PC of a not-taken branch off `σ'`: `PC = pc + 4`. -/
theorem obs_bnottaken_pc_eg {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) :
    σ'.regs.get? Register.PC = some (BitVec.addInt pc 4) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_branch_nottaken_pc σ pc vm)

/-- Read the PC of a `jump_x0` (`j`/`ret`) step off `σ'`: `PC = tgt`. -/
theorem obs_jump_x0_pc_eg {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) :
    σ'.regs.get? Register.PC = some tgt :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_jump_x0_pc σ pc vm tgt)

end Vsa.Sim

