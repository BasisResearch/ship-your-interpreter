import Vsa.Sim.ObsAvoid
import Vsa.Sim.DecodeTable.Batch01Part08
import Vsa.Sim.DecodeTable.Batch02Part21
import Vsa.Sim.DecodeTable.Batch03Part17
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch05Part10
import Vsa.Sim.DecodeTable.Batch06Part16
import Vsa.Sim.DecodeTable.Batch06Part20
import Vsa.Sim.DecodeTable.Batch12Part19
import Vsa.Sim.DecodeTable.Batch16Part17

/-!
# Layer 3 — total-correctness spec for `env_new` (the first malloc-consumer)

Config-level (`Vsa.Logic.Triple`) composition of the per-site observational steps
(`Vsa/Sim/EnvNewSites.lean`) into a total-correctness triple for `env_new`
(`c/src/env.c`, entry `0x800029fc`).  `env_new(parent)` allocates a 32-byte C
`Env`, initialises `count = cap = 0`, `names = vals = NULL`, `parent = parent`,
and returns the pointer.

This is the FIRST function that calls `malloc`, so it pioneers the
**MallocContract-consumer + C-stack-convention pattern** that `env_define`/
`env_get`/`env_set` and everything above reuse.

## What the assembly does on the NULL path

Read off `experiments/disasm.txt`: after `jal malloc`, `beqz a0,0x80002a38`
branches to a NULL-error block `[0x80002a38, 0x80002a5c)` that loads
`_impure_ptr`, calls `fwrite` on an error string, and calls `exit(1)` — it
**never returns**.  So there is no meaningful post-state on the NULL path.  We
therefore constrain the precondition with an **arena-non-exhaustion hypothesis**
`harena` drawn from `MallocContract`'s interface: the returned pointer is the
`some p` (fresh, aligned, in-arena) disjunct, never the NULL disjunct.  With
`x10 = p ≠ 0` the `beqz` is not taken and the machine runs the success path to
`ret`.  (This is exactly the "constrain P with an arena-non-exhaustion
hypothesis instead of proving the exit path" option the design note anticipates.)

## The malloc-composition pattern (the reusable interface)

The call site is (`0x80002a10 jal malloc`; link `0x80002a14`):

* Before the `jal`, the callee-stores have spilled the entry `s0` at `sp_new+0`
  and the entry `ra` at `sp_new+8`, where `sp_new = entry_sp - 16`.
* At the `jal`-successor state `cent` we invoke `M.spec` with the ghost `g`
  instantiated at `fun R => cent.σ.regs.get?` (so the callee-entry ABI-frame
  hypothesis `∀ R, AbiPreserved R → get? R = g R` is `rfl`), `n = 32`,
  `sp = sp_new`, `r = 0x80002a14`, `m0 = cent.σ.mem`.
* `M.spec`'s post returns: `PC = 0x80002a14`, `x2 = sp_new`, `x3 = gpv`, the
  ABI frame (`sp/gp/tp/s0-s11` preserved — this is how `s0 = par` survives the
  call), the result disjunction, and memory preserved outside
  `privFoot ∪ [SL.lo, sp_new)`.  The two spill slots live at `≥ sp_new`, so
  (given they are not allocator-private, `hframe_priv`) they survive the call
  and `ld ra`/`ld s0` recover the entry values.

Callers of `env_new` copy this exact P/Q shape: supply a `MallocContract`, a
`StackOK` frame with ≥ 16 + malloc's `headroom` bytes below the entry sp, an
arena-non-exhaustion hypothesis, and the frame/arena/stack disjointness bundle.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.While (Frame)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Blanket ghost-frame predicate (`NotWrittenEnv`) + generic per-class helpers

`env_new`'s straight-line success path writes GPRs `x1` (ra: `jal`, `ld`),
`x2` (sp: two `addi`), `x8` (s0: `mv`, `ld`), `x10` (a0: `li`, and the malloc
result). `NotWrittenEnv R` is the disequality conjunction over those written
GPRs and the per-step write-set / tick-set registers, so preservation of every
other register is recovered through the blanket ghost-frame conjunct. -/

/-! ## `jal` observation consumers (inlined; analogue of `obs_alu_*`)

Copied from `DivSites2` (which we do not import — it transitively pulls the
concurrently-broken `DivSites`).  From a `jal` observation
`ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)` read the framing
fields off `σ'`. -/

theorem post_jal_pc_env (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg) :
    (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? Register.PC
      = some (pc + sign_extend (m := 64) imm) := by
  show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem post_jal_rd_env (σ : MState) (pc vminstret : BitVec 64) (imm : BitVec 21)
    (rd_reg : Register) (link : RegisterType rd_reg)
    (h1 : (Register.minstret == rd_reg) = false) (h2 : (Register.PC == rd_reg) = false) :
    (sigmaPost_jal σ pc vminstret imm rd_reg link).regs.get? rd_reg = some link := by
  show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? rd_reg = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
  show (((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
    (pc + sign_extend (m := 64) imm)).insert rd_reg link).get? rd_reg = _
  rw [Std.ExtDHashMap.get?_insert_self]

theorem obs_jal_pc_env {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) :
    σ'.regs.get? Register.PC = some (pc + sign_extend (m := 64) imm) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_jal_pc_env σ pc vm imm rd_reg link)

theorem obs_jal_rd_env {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link))
    (hmc : (Register.mcycle == rd_reg) = false) (hmt : (Register.mtime == rd_reg) = false)
    (hmi : (Register.mip == rd_reg) = false)
    (h1 : (Register.minstret == rd_reg) = false) (h2 : (Register.PC == rd_reg) = false) :
    σ'.regs.get? rd_reg = some link :=
  readback σ' _ hobs rd_reg hmc hmt hmi (post_jal_rd_env σ pc vm imm rd_reg link h1 h2)

theorem obs_jal_other_env {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h3 : (rd_reg == R) = false) (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi
    ((get?_sigmaPost_jal σ pc vm imm rd_reg link R h1 h2 h3 h4 h5).trans hσ)

theorem obs_jal_minstret_env {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-! ## Region / disjointness bundle for `env_new`

Bundles the C-stack-convention and heap-frame disjointness facts the memory
threading needs.  `entry_sp` is the entry stack pointer; `sp_new = entry_sp - 16`
is the frame pointer passed to `malloc`.  `p` is the fresh env pointer. -/

/-! ## Pointer-arithmetic helpers (offsets from `sp_new` / `p`, no wrap) -/

/-- `sp_new + sext 0x000 = sp_new` (0-offset store/load). -/
theorem off0_addr (base : BitVec 64) : (base + sign_extend (m := 64) (0x000#12)).toNat = base.toNat := by
  rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide,
    BitVec.add_zero]

/-- `p + sext 0x008 = p + 8` when `p + 8 < 2^64`. -/
theorem off8_addr (base : BitVec 64) (h : base.toNat + 8 < 2^64) :
    (base + sign_extend (m := 64) (0x008#12)).toNat = base.toNat + 8 := by
  have hs : (sign_extend (m := 64) (0x008#12) : BitVec 64).toNat = 8 := by decide
  rw [BitVec.toNat_add, hs]; omega

/-- `entry_sp - 16 = sp_new` as a `BitVec`.
The `addi sp,sp,-16` computes `sp + sext 0xff0 = sp - 16`. -/
theorem sp_sub16 (sp : BitVec 64) :
    (sp + sign_extend (m := 64) (0xff0#12)) = sp - 16#64 := by
  have hs : (sign_extend (m := 64) (0xff0#12) : BitVec 64) = -(16#64) := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_sub]
  have hn : (-(16#64) : BitVec 64).toNat = 2^64 - 16 := by decide
  have h16 : (16#64 : BitVec 64).toNat = 16 := by decide
  rw [hn, h16]; have := sp.isLt; omega

/-- `(sp - 16).toNat = sp.toNat - 16` when `16 ≤ sp.toNat`. -/
theorem sp_sub16_toNat (sp : BitVec 64) (h : 16 ≤ sp.toNat) :
    (sp - 16#64).toNat = sp.toNat - 16 := by
  have h16 : (16#64 : BitVec 64).toNat = 16 := by decide
  rw [BitVec.toNat_sub, h16]
  have := sp.isLt
  omega

/-! ## `Env_newLoaded` survives the frame + stack stores

Each of the six `sd`s inserts an 8-byte `writeMap8` window; `Env_newLoaded`
survives each because its (concrete) code addresses `[0x800029fc, 0x80002a5c)`
are disjoint from the (out-of-range) frame `[p, p+32)` and stack
`[sp_new, sp_new+16)` windows. -/

/-! ## `read32` / `read64` read-backs over the frame stores

`read64_writeMap8_disjoint`: a `read64` at `a` is unaffected by a `writeMap8`
whose window `[a8, a8+8)` is disjoint from `[a, a+8)`.  `read32_writeMap8_lo` /
`_hi`: the low / high 4 bytes of a freshly `writeMap8`-written window read back as
`d.toNat % 2^32` / `d.toNat / 2^32`.  For the zero-store these are both `0`. -/
theorem read64_writeMap8_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (a a8 : Nat)
    (d : BitVec (8 * 8)) (hdis : a + 8 ≤ a8 ∨ a8 + 8 ≤ a) :
    read64 (writeMap8 mem a8 d) a = read64 mem a := by
  have g0 := getElem_writeMap8_disjoint mem a8 a d (by omega)
  have g1 := getElem_writeMap8_disjoint mem a8 (a + 1) d (by omega)
  have g2 := getElem_writeMap8_disjoint mem a8 (a + 2) d (by omega)
  have g3 := getElem_writeMap8_disjoint mem a8 (a + 3) d (by omega)
  have g4 := getElem_writeMap8_disjoint mem a8 (a + 4) d (by omega)
  have g5 := getElem_writeMap8_disjoint mem a8 (a + 5) d (by omega)
  have g6 := getElem_writeMap8_disjoint mem a8 (a + 6) d (by omega)
  have g7 := getElem_writeMap8_disjoint mem a8 (a + 7) d (by omega)
  simp only [read64, readLE, g0, g1, g2, g3, g4, g5, g6, g7]

/-- `mv rd,rs` folds `v + sext 0 = v`. -/
theorem addi0_env (v : BitVec 64) : v + sign_extend (m := 64) (0x000#12) = v := by
  rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide,
    BitVec.add_zero]

/-! ## The spec statement

`env_new_pre` / `env_new_post` are parametrised by:
* `M : MallocContract A SL gpv headroom maxReq` — the allocator hypothesis (a
  structure parameter, never an axiom);
* `g` — the entry ghost register snapshot (blanket frame);
* `par` — the parent env pointer (entry `a0`), and `parentSpec : Option Addr`
  the spec-side parent it corresponds to through `φf`;
* `r` — the return address (entry `ra`, 4-aligned);
* `sp` — the entry stack pointer;
* `m0` — the pinned entry memory;
* the correspondence maps `N`, `φf`, `φc` and the `EnvRegions`/parent-link
  side data supplied existentially in the post.

`env_new_pre` requires: `GoodState`, code loaded, PC at entry, `a0 = par`,
`ra = r` (4-aligned target), `sp = entry sp` with `StackOK` leaving ≥ `16 +
headroom` bytes, `gp = gpv`, the ABI-frame ghost tie, `M.AInv`, `mem = m0`,
`32 ≤ maxReq`, the arena-non-exhaustion outcome selector, and the disjointness
bundle. -/

end Vsa.Sim
