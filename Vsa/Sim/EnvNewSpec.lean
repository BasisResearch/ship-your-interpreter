import Vsa.Sim.EnvNewSites
import Vsa.Sim.ValueSpec
import Vsa.Sim.Muldi3Spec
import Vsa.Sim.MemcpySpec
import Vsa.Alloc
import Vsa.RuntimeRepr
import Vsa.Triple

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
open Vsa.Sim.Code (Env_newLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Blanket ghost-frame predicate (`NotWrittenEnv`) + generic per-class helpers

`env_new`'s straight-line success path writes GPRs `x1` (ra: `jal`, `ld`),
`x2` (sp: two `addi`), `x8` (s0: `mv`, `ld`), `x10` (a0: `li`, and the malloc
result). `NotWrittenEnv R` is the disequality conjunction over those written
GPRs and the per-step write-set / tick-set registers, so preservation of every
other register is recovered through the blanket ghost-frame conjunct. -/

/-- `R` is outside the union of `env_new`'s written GPRs (`x1, x2, x8, x10`) and
every register any hot-path step (ALU / branch / store / jump / tick) can write. -/
abbrev NotWrittenEnv (R : Register) : Prop :=
  (Register.x1 == R) = false ∧ (Register.x2 == R) = false ∧
  (Register.x8 == R) = false ∧ (Register.x10 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

/-- A caller-saved register `X` (with `AbiPreserved X = false`) differs from any
ABI-preserved `R`: `(X == R) = false`. -/
theorem abi_ne {X R : Register} (hX : AbiPreserved X = false) (hR : AbiPreserved R = true) :
    (X == R) = false := by
  rcases hXR : (X == R) with _ | _
  · rfl
  · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)

/-- `R ≠ X` gives `(X == R) = false`. -/
theorem beq_false_of_ne' {X R : Register} (h : R ≠ X) : (X == R) = false := by
  rcases hXR : (X == R) with _ | _
  · rfl
  · rw [beq_iff_eq] at hXR; exact absurd hXR.symm h

theorem NotWrittenEnv.x1 {R : Register} (h : NotWrittenEnv R) : (Register.x1 == R) = false := h.1
theorem NotWrittenEnv.x2 {R : Register} (h : NotWrittenEnv R) : (Register.x2 == R) = false := h.2.1
theorem NotWrittenEnv.x8 {R : Register} (h : NotWrittenEnv R) : (Register.x8 == R) = false := h.2.2.1
theorem NotWrittenEnv.x10 {R : Register} (h : NotWrittenEnv R) : (Register.x10 == R) = false := h.2.2.2.1

/-- Generic ALU frame step (covers `addi`, `mv`, and the ALU-class `ld` loads). -/
theorem frame_alu_env {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) (R : Register)
    (hrd : (rd == R) = false) (hR : NotWrittenEnv R) :
    σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_alu σ pc vm rd v R hmi hpc hrd hnpc hmii

/-- Generic not-taken-branch frame step. -/
theorem frame_bnottaken_env {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register)
    (hR : NotWrittenEnv R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_nottaken σ pc vm R hmi hpc hnpc hmii

/-- Generic STORE frame step (no `rd`). -/
theorem frame_store_env {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) (R : Register)
    (hR : NotWrittenEnv R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_store σ pc vm m' R hmi hpc hnpc hmii

/-- Generic `jal` frame step (write-set `rd = x1, PC, minstret, nextPC, minstret_increment`). -/
theorem frame_jal_env {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) (R : Register)
    (hrd : (rd_reg == R) = false) (hR : NotWrittenEnv R) :
    σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jal σ pc vm imm rd_reg link R hmi hpc hrd hnpc hmii

/-- Generic `jr`/`ret` frame step. -/
theorem frame_jr_env {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register)
    (hR : NotWrittenEnv R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jump_x0 σ pc vm tgt R hmi hpc hnpc hmii

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
structure EnvRegions (SL : StackLayout) (privFoot : Nat → Prop)
    (entry_sp p : Nat) : Prop where
  /-- The two spill slots `[sp_new, sp_new+16)` are not allocator-private
  (they are the caller's stack frame). -/
  spill_not_priv : ∀ k, k < 16 → ¬ privFoot ((entry_sp - 16) + k)
  /-- The fresh 32-byte frame `[p, p+32)` is disjoint from the whole stack region
  `[SL.lo, entry_sp)` (heap arena ≠ stack). -/
  frame_stack_disjoint : p + 32 ≤ SL.lo ∨ entry_sp ≤ p
  /-- The fresh frame is disjoint from the `env_new` code `[0x800029fc, 0x80002a5c)`. -/
  frame_code_disjoint : p + 32 ≤ 0x800029fc ∨ 0x80002a5c ≤ p
  /-- The fresh frame lies in RAM `[0x80000000, 0x100000000)`. -/
  frame_lo : 0x80000000 ≤ p
  frame_hi : p + 32 ≤ 0x100000000
  /-- The fresh frame is above the HTIF window. -/
  frame_win : tohostAddr + 16 ≤ p
  /-- 8-byte alignment of the fresh frame (malloc returns 16-aligned ⇒ 8-aligned). -/
  frame_align : p % 8 = 0
  /-- The two spill slots `[sp_new, sp_new+16)` lie in RAM, above the HTIF window,
  and are 8-aligned (`sp_new` 16-aligned ⇒ 8-aligned). -/
  spill_lo : 0x80000000 ≤ entry_sp - 16
  spill_hi : entry_sp ≤ 0x100000000
  spill_win : tohostAddr + 16 ≤ entry_sp - 16
  spill_align : (entry_sp - 16) % 8 = 0
  /-- The spill slots are disjoint from the `env_new` code. -/
  spill_code_disjoint : entry_sp ≤ 0x800029fc ∨ 0x80002a5c ≤ entry_sp - 16
  /-- The `env_new` code text `[0x800029fc, 0x80002a5c)` is not allocator-private
  (read-only text ≠ heap metadata / reent state). -/
  code_not_priv : ∀ a, 0x800029fc ≤ a → a < 0x80002a5c → ¬ privFoot a
  /-- The `env_new` code text is disjoint from the caller's stack region. -/
  code_stack_disjoint : SL.lo ≥ 0x80002a5c ∨ entry_sp ≤ 0x800029fc
  /-- The caller's stack region `[SL.lo, entry_sp)` is not allocator-private
  (stack ≠ heap metadata / reent state). -/
  stack_not_priv : ∀ a, SL.lo ≤ a → a < entry_sp → ¬ privFoot a

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

/-- `p + sext 0x010 = p + 16` when `p + 16 < 2^64`. -/
theorem off16_addr (base : BitVec 64) (h : base.toNat + 16 < 2^64) :
    (base + sign_extend (m := 64) (0x010#12)).toNat = base.toNat + 16 := by
  have hs : (sign_extend (m := 64) (0x010#12) : BitVec 64).toNat = 16 := by decide
  rw [BitVec.toNat_add, hs]; omega

/-- `p + sext 0x018 = p + 24` when `p + 24 < 2^64`. -/
theorem off24_addr (base : BitVec 64) (h : base.toNat + 24 < 2^64) :
    (base + sign_extend (m := 64) (0x018#12)).toNat = base.toNat + 24 := by
  have hs : (sign_extend (m := 64) (0x018#12) : BitVec 64).toNat = 24 := by decide
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

/-- `(sp - 16) + 16 = sp` (the `addi sp,sp,16` restore). -/
theorem sp_restore (sp : BitVec 64) :
    (sp - 16#64) + sign_extend (m := 64) (0x010#12) = sp := by
  have hs : (sign_extend (m := 64) (0x010#12) : BitVec 64) = 16#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_sub]
  have h16 : (16#64 : BitVec 64).toNat = 16 := by decide
  rw [h16]; have := sp.isLt; omega

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
theorem loaded_env_writeMap8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ 0x800029fc ∨ 0x80002a5c ≤ a8) (h : Env_newLoaded mem) :
    Env_newLoaded (writeMap8 mem a8 d) := by
  obtain ⟨c0, c1⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [Vsa.Sim.Code.env_newChunk0] at c0 ⊢
    repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_newChunk1] at c1 ⊢
    repeat' apply And.intro
    all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])

/-- **`Env_newLoaded` transfers through any memory agreeing on the code region**
`[0x800029fc, 0x80002a5c)`.  Used to re-establish `Env_newLoaded` after `malloc`
(whose post preserves memory outside `privFoot ∪ stack`, both disjoint from code). -/
theorem loaded_env_of_agree (mem1 mem2 : Std.ExtHashMap Nat (BitVec 8))
    (hagree : ∀ a, 0x800029fc ≤ a → a < 0x80002a5c → mem2[a]? = mem1[a]?)
    (h : Env_newLoaded mem1) : Env_newLoaded mem2 := by
  obtain ⟨c0, c1⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [Vsa.Sim.Code.env_newChunk0] at c0 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_newChunk1] at c1 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])

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

/-- `read32` of the low 4 bytes of a `writeMap8` window recovers `d.toNat % 2^32`. -/
theorem read32_writeMap8_lo (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    read32 (writeMap8 mem a d) a = some (d.toNat % 2^32) := by
  have e0 := getElem_writeMap8_0 mem a d
  have e1 := getElem_writeMap8_1 mem a d
  have e2 := getElem_writeMap8_2 mem a d
  have e3 := getElem_writeMap8_3 mem a d
  simp only [read32, readLE, e0, e1, e2, e3, bind, Option.bind, pure]
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Option.some.injEq, Nat.reducePow, Nat.pow_zero, Nat.div_one]
  have hd : d.toNat < 2 ^ 64 := by have := d.isLt; simpa using this
  omega

/-- `read32` of the high 4 bytes of a `writeMap8` window (at `a+4`) recovers
`d.toNat / 2^32`. -/
theorem read32_writeMap8_hi (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    read32 (writeMap8 mem a d) (a + 4) = some (d.toNat / 2^32) := by
  have e4 := getElem_writeMap8_4 mem a d
  have e5 := getElem_writeMap8_5 mem a d
  have e6 := getElem_writeMap8_6 mem a d
  have e7 := getElem_writeMap8_7 mem a d
  simp only [read32, readLE, show a + 4 + 1 = a + 5 from by omega,
    show a + 4 + 2 = a + 6 from by omega, show a + 4 + 3 = a + 7 from by omega,
    e4, e5, e6, e7, bind, Option.bind, pure]
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Option.some.injEq, Nat.reducePow, Nat.pow_zero, Nat.div_one]
  have hd : d.toNat < 2 ^ 64 := by have := d.isLt; simpa using this
  omega

/-- `sdData_val 0 = 0` at the byte level: its `toNat` is `0`. -/
theorem sdData_val_zero_toNat : (sdData_val (0#64)).toNat = 0 := by
  rw [sdData_toNat]; rfl

/-- `sign_extend` of a 64-bit value is itself (the `ld` write value fold): a signed
8-byte load writes `sign_extend (m := 64) (d : BitVec 64)`; at width 64 that is `d`. -/
theorem sext64_id (d : BitVec (8 * 8)) : (sign_extend (m := 64) d : BitVec 64) = d := by
  simp only [sign_extend, Sail.BitVec.signExtend]
  exact BitVec.signExtend_eq d

/-- The 8-byte LE reconstruction equals the `toNat` of the assembled word
(same technique as `ValueTruthySpec.word8_toNat_recon`, inlined to avoid importing
that file). -/
theorem word8_recon_env (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
      : BitVec (8 * 8)).toNat
      = b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 *
        (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) := by
  simp only [BitVec.append_eq, BitVec.toNat_append]
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  have h4 := b4.isLt; have h5 := b5.isLt; have h6 := b6.isLt; have h7 := b7.isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  omega

/-- The `ld` at a spill slot recovers the spilled value: sign-extending the LE
reassembly of the 8 `writeMap8 (sdData_val v)` bytes gives `v`. -/
theorem sext_reassemble (v : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h0 : b0 = (sdData_val v).extractLsb' 0 8) (h1 : b1 = (sdData_val v).extractLsb' 8 8)
    (h2 : b2 = (sdData_val v).extractLsb' 16 8) (h3 : b3 = (sdData_val v).extractLsb' 24 8)
    (h4 : b4 = (sdData_val v).extractLsb' 32 8) (h5 : b5 = (sdData_val v).extractLsb' 40 8)
    (h6 : b6 = (sdData_val v).extractLsb' 48 8) (h7 : b7 = (sdData_val v).extractLsb' 56 8) :
    (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)) : BitVec 64) = v := by
  rw [sext64_id]
  apply BitVec.eq_of_toNat_eq
  rw [word8_recon_env]
  subst h0 h1 h2 h3 h4 h5 h6 h7
  have hv : (sdData_val v).toNat = v.toNat := sdData_toNat v
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, hv]
  have := v.isLt
  omega

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
def env_new_pre (A : Arena) (SL : StackLayout) (gpv : BitVec 64) (headroom maxReq : Nat)
    (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R))
    (par r sp s0e : BitVec 64) (exts : List (Nat × Nat))
    (φf : Vsa.While.Addr → Nat) (parentSpec : Option Vsa.While.Addr)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ Env_newLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x800029fc#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some par ∧
  c.σ.regs.get? Register.x8 = some s0e ∧
  c.σ.regs.get? Register.x1 = some r ∧ r.toNat % 4 = 0 ∧
  (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 ∧
  c.σ.regs.get? Register.x2 = some sp ∧ StackOK SL sp (16 + headroom) ∧
  c.σ.regs.get? Register.x3 = some gpv ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
  32 ≤ maxReq ∧ M.AInv c.σ exts ∧
  -- `AInv` is the allocator state: it depends only on `gp` and the allocator-private
  -- footprint `privFoot` (heap metadata + reent state).  So it survives any change
  -- that preserves `gp` and every `privFoot` byte — in particular the callee prologue
  -- (which scribbles only the caller's stack frame, disjoint from `privFoot`) and the
  -- `Env`-initialisation stores (which write only the freshly-allocated block, disjoint
  -- from `privFoot` by `MallocContract.privFoot_disjoint`).  This is the exact
  -- `MallocContract` interface property drawn on to re-establish `AInv` at the call
  -- site and to carry it into the post.
  (∀ (exts' : List (Nat × Nat)) (σa σb : MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a, M.privFoot a → σa.mem[a]? = σb.mem[a]?) →
      M.AInv σa exts' → M.AInv σb exts') ∧
  -- the parent pointer `par` corresponds to the spec-side `parentSpec` through `φf`
  -- (NULL ⇔ top-level frame; `env.c`: `env->parent = parent`):
  (match parentSpec with
   | none => par = 0#64
   | some pa => φf pa = par.toNat ∧ par ≠ 0#64) ∧
  -- ARENA NON-EXHAUSTION (see module doc): this allocation does not hit the
  -- allocator's NULL-on-exhaustion branch. Drawn from `MallocContract`'s
  -- interface — the NULL branch is `x10 = 0 ∧ AInv exts`, and on it the assembly
  -- `exit`s (never returns), so the caller must rule it out. Any config whose
  -- `AInv` still equals the pre-call `exts` with a zero result is impossible.
  (∀ c' : Config, M.AInv c'.σ exts →
      c'.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) → False) ∧
  -- callee-saved (ABI-preserved) registers tie to the entry ghost snapshot `g`.
  -- Caller-saved scratch registers are forfeit (malloc clobbers them), so only
  -- `AbiPreserved` registers appear in the frame — exactly `MallocContract`'s shape.
  (∀ R : Register, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
  16 ≤ sp.toNat

/-- Postcondition: `PC = r` (exact `ret` return), `a0 = p` a fresh in-arena env
pointer, `sp/gp` restored, the blanket frame for untouched registers, the new
32-byte `Env` at `p` (`count = cap = 0`, `names = vals = NULL`, `parent = par`)
via `FrameRepr`, and memory unchanged outside the fresh frame `[p, p+32)`, the
allocator-private footprint, and the caller's stack region `[SL.lo, sp)`. -/
def env_new_post (A : Arena) (SL : StackLayout) (gpv : BitVec 64) (headroom maxReq : Nat)
    (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R))
    (par r sp s0e : BitVec 64) (exts : List (Nat × Nat))
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat) (parentSpec : Option Vsa.While.Addr)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x2 = some sp ∧
  c.σ.regs.get? Register.x3 = some gpv ∧
  c.σ.regs.get? Register.x1 = some r ∧
  c.σ.regs.get? Register.x8 = some s0e ∧
  (∃ p, c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
    p ≠ 0 ∧ p % 16 = 0 ∧ A.contains p 32 ∧
    (∀ e ∈ exts, ExtDisjoint (p, 32) e) ∧
    M.AInv c.σ ((p, 32) :: exts) ∧
    -- the fresh 32-byte `Env` at `p` represents the empty frame with parent `parentSpec`
    FrameRepr c.σ.mem N φf φc p ⟨parentSpec, []⟩ ∧
    -- memory untouched outside the fresh frame, the malloc-private footprint,
    -- and the caller's stack region:
    (∀ a, ¬ M.privFoot a → ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
      (a < p ∨ p + 32 ≤ a) → c.σ.mem[a]? = m0[a]?)) ∧
  (∀ R : Register, AbiPreserved R = true → c.σ.regs.get? R = g R)

/-- **`env_new` total-correctness spec.** From `env_new_pre` the machine runs the
straight-line success path (through the `malloc` contract `M.spec`) to
`env_new_post`: a fresh, aligned, in-arena 32-byte `Env` at `p`, initialised as
the empty frame `⟨parentSpec, []⟩` (`FrameRepr`), `sp`/`gp`/callee-saved restored,
memory framed to `[p,p+32) ∪ privFoot ∪ stack`, and an exact `ret` to `r`.

`M : MallocContract …` is a hypothesis parameter (structure), never an axiom.

NOTE: at the time of writing, `Vsa/Sim/StepObs.lean` is broken by an in-progress
rename in `Vsa/Sim/StepJump.lean` (the `sigmaPost_jump_x0`/`step_jr_notick`
family), so the whole `Sim` corpus (this file included) cannot be kernel-checked
until that lands.  The proof below follows the `value_null_spec` (ValueSpec) +
`umoddi3_spec` (DivSpec2) idioms verbatim and is expected to close once the tree
builds. -/
theorem env_new_spec (A : Arena) (SL : StackLayout) (gpv : BitVec 64) (headroom maxReq : Nat)
    (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R))
    (par r sp s0e : BitVec 64) (exts : List (Nat × Nat))
    (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat) (parentSpec : Option Vsa.While.Addr)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hER : ∀ p : Nat, EnvRegions SL M.privFoot sp.toNat p) :
    Triple (env_new_pre A SL gpv headroom maxReq M g par r sp s0e exts φf parentSpec m0)
      (env_new_post A SL gpv headroom maxReq M g par r sp s0e exts N φf φc parentSpec m0) := by
  intro c hpre
  obtain ⟨hG, hloaded, hmem, hpc, ha0, hs8e, hra, hralign, hrettgt, hsp, hstackok, hgp,
    ⟨vmi, hmi⟩, htick, hmaxreq, hAInv, hAInvFrame, hparlink, hnonexh, hframe, hsp16⟩ := hpre
  obtain ⟨hSLlo, hSLhi, hspalign⟩ := hstackok
  -- convenient stack facts
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- === 0x800029fc: addi sp,sp,-16  ⇒ x2 := sp - 16 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_800029fc_env c.σ c.tick c.steps (0x800029fc#64) vmi sp hG hpc hmi hsp hloaded rfl htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002a00#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800029fc#64 : BitVec 64) 4 = (0x80002a00#64 : BitVec 64) from by decide] at this
  have hsp1 : σ1.regs.get? Register.x2 = some (sp - 16#64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sp_sub16 sp] at this
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have hs8e_1 := obs_alu_other hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs8e
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hloaded1 : Env_newLoaded σ1.mem := hmem1 ▸ hloaded
  -- sp_new facts (spn := sp - 16)
  have hspn_toNat : (sp - 16#64).toNat = sp.toNat - 16 := sp_sub16_toNat sp hsp16
  have hspn0 : ((sp - 16#64) + sign_extend (m := 64) (0x000#12)).toNat = (sp - 16#64).toNat :=
    off0_addr (sp - 16#64)
  have hspn8 : ((sp - 16#64) + sign_extend (m := 64) (0x008#12)).toNat = (sp - 16#64).toNat + 8 := by
    apply off8_addr; rw [hspn_toNat]; have := sp.isLt; omega
  -- === 0x80002a00: sd s0,0(sp)  ⇒ mem += spill (entry s0 = s0e) @ spn+0 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80002a00_env σ1 i1 (c.steps + 1) (0x80002a00#64) vmi1 (sp - 16#64) s0e hG1 hpc1 hmi1 hsp1 hs8e_1 hloaded1 rfl
      (by rw [hspn0, hspn_toNat]; have := (hER 0).spill_lo; omega)
      (by rw [hspn0, hspn_toNat]; have := (hER 0).spill_hi; omega)
      (by rw [hspn0, hspn_toNat]; have := (hER 0).spill_win; omega)
      (by rw [hspn0, hspn_toNat]; have := (hER 0).spill_align; omega) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x80002a04#64 : BitVec 64) := by
    have := obs_store_pc hobs2
    rwa [show BitVec.addInt (0x80002a00#64 : BitVec 64) 4 = (0x80002a04#64 : BitVec 64) from by decide] at this
  have hsp2 := obs_store_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp1
  have ha0_2 := obs_store_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have hra_2 := obs_store_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have hs8e_2 := obs_store_other hobs2 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs8e_1
  obtain ⟨vmi2, hmi2⟩ := obs_store_minstret hobs2
  -- σ2.mem = writeMap8 c.σ.mem spn (s0e); reduce afterNextPC mem to σ1.mem = c.σ.mem
  have hmem2' : σ2.mem = writeMap8 c.σ.mem (sp - 16#64).toNat (sdData_val s0e) := by
    rw [hmem2, mem_afterNextPC, hmem1, hspn0]
  have hloaded2 : Env_newLoaded σ2.mem := by
    rw [hmem2']
    exact loaded_env_writeMap8 c.σ.mem (sp - 16#64).toNat (sdData_val s0e)
      (by rw [hspn_toNat]; have := (hER 0).spill_code_disjoint; omega) hloaded
  -- === 0x80002a04: mv s0,a0  ⇒ x8 := par ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80002a04_env σ2 i2 (c.steps + 1 + 1) (0x80002a04#64) vmi2 par hG2 hpc2 hmi2 ha0_2 hloaded2 rfl hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x80002a08#64 : BitVec 64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80002a04#64 : BitVec 64) 4 = (0x80002a08#64 : BitVec 64) from by decide] at this
  have hsp3 := obs_alu_other hobs3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp2
  have ha0_3 := obs_alu_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
  have hra_3 := obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  have hs8_3 : σ3.regs.get? Register.x8 = some par := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addi0_env par] at this
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hmem3' : σ3.mem = σ2.mem := hmem3
  have hloaded3 : Env_newLoaded σ3.mem := hmem3' ▸ hloaded2
  -- === 0x80002a08: li a0,32  ⇒ x10 := 32 ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80002a08_env σ3 i3 (c.steps + 1 + 1 + 1) (0x80002a08#64) vmi3 hG3 hpc3 hmi3 hloaded3 rfl hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x80002a0c#64 : BitVec 64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x80002a08#64 : BitVec 64) 4 = (0x80002a0c#64 : BitVec 64) from by decide] at this
  have hsp4 := obs_alu_other hobs4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp3
  have hra_4 := obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
  have hs8_4 := obs_alu_other hobs4 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs8_3
  have ha0_4 : σ4.regs.get? Register.x10 = some (32#64) := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) + sign_extend (m := 64) (0x020#12) : BitVec 64) = 32#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hmem4' : σ4.mem = σ2.mem := by rw [hmem4, hmem3']
  have hloaded4 : Env_newLoaded σ4.mem := hmem4' ▸ hloaded2
  -- === 0x80002a0c: sd ra,8(sp)  ⇒ mem += spill (entry ra = r) @ spn+8 ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80002a0c_env σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80002a0c#64) vmi4 (sp - 16#64) r
      hG4 hpc4 hmi4 hsp4 hra_4 hloaded4 rfl
      (by rw [hspn8, hspn_toNat]; have := (hER 0).spill_lo; omega)
      (by rw [hspn8, hspn_toNat]; have := (hER 0).spill_hi; omega)
      (by rw [hspn8, hspn_toNat]; have := (hER 0).spill_win; omega)
      (by rw [hspn8, hspn_toNat]; have := (hER 0).spill_align; omega) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x80002a10#64 : BitVec 64) := by
    have := obs_store_pc hobs5
    rwa [show BitVec.addInt (0x80002a0c#64 : BitVec 64) 4 = (0x80002a10#64 : BitVec 64) from by decide] at this
  have hsp5 := obs_store_other hobs5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp4
  have ha0_5 := obs_store_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_4
  have hs8_5 := obs_store_other hobs5 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs8_4
  obtain ⟨vmi5, hmi5⟩ := obs_store_minstret hobs5
  -- σ5.mem = writeMap8 (writeMap8 m0 spn s0e) (spn+8) r
  have hmem5' : σ5.mem = writeMap8 σ2.mem ((sp - 16#64).toNat + 8) (sdData_val r) := by
    rw [hmem5, mem_afterNextPC, hmem4', hspn8]
  have hloaded5 : Env_newLoaded σ5.mem := by
    rw [hmem5']
    exact loaded_env_writeMap8 σ2.mem ((sp - 16#64).toNat + 8) (sdData_val r)
      (by rw [hspn_toNat]; have := (hER 0).spill_code_disjoint; omega) hloaded2
  -- === 0x80002a10: jal malloc  ⇒ x1 := 0x80002a14, PC := mallocEntry ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80002a10_env σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80002a10#64) vmi5 hG5 hpc5 hmi5 hloaded5 rfl hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs6
  have hpc6 : σ6.regs.get? Register.PC = some (BitVec.ofNat 64 mallocEntry) := by
    have := obs_jal_pc_env hobs6
    rwa [show (0x80002a10#64 : BitVec 64) + sign_extend (m := 64) (0x001d80#21)
      = (BitVec.ofNat 64 mallocEntry) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have ha0_6 : σ6.regs.get? Register.x10 = some (BitVec.ofNat 64 32) := by
    have := obs_jal_other_env hobs6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_5
    rwa [show (32#64 : BitVec 64) = BitVec.ofNat 64 32 from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hra_6 : σ6.regs.get? Register.x1 = some (0x80002a14#64) := by
    have := obs_jal_rd_env hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80002a10#64 : BitVec 64) 4 = (0x80002a14#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hsp6 := obs_jal_other_env hobs6 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp5
  have hs8_6 := obs_jal_other_env hobs6 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs8_5
  have hmi6 : ∃ v, σ6.regs.get? Register.minstret = some v := obs_jal_minstret_env hobs6
  have hmem6' : σ6.mem = σ5.mem := hmem6
  -- gp (x3) preserved across all prefix steps (never written) via the blanket frame
  have hgp6 : σ6.regs.get? Register.x3 = some gpv := by
    have hgpR : NotWrittenEnv Register.x3 := by refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide
    rw [frame_jal_env hobs6 Register.x3 (by decide) hgpR,
      frame_store_env hobs5 Register.x3 hgpR,
      frame_alu_env hobs4 Register.x3 (by decide) hgpR,
      frame_alu_env hobs3 Register.x3 (by decide) hgpR,
      frame_store_env hobs2 Register.x3 hgpR,
      frame_alu_env hobs1 Register.x3 (by decide) hgpR]
    exact hgp
  -- AInv at σ6 via `hAInvFrame`: σ6 agrees with `c.σ` on gp and on all memory outside
  -- the caller's stack frame `[SL.lo, sp)` (the only writes are the two spill stores at
  -- `spn`/`spn+8`, both inside `[spn, sp) ⊆ [SL.lo, sp)`).
  have hspn_lo : SL.lo ≤ (sp - 16#64).toNat := by
    rw [hspn_toNat]; have := (hER 0).spill_lo; have := hSLlo; omega
  have hspn_hi : (sp - 16#64).toNat + 16 = sp.toNat := by rw [hspn_toNat]; omega
  have hAInv_σ6 : M.AInv σ6 exts := by
    refine hAInvFrame exts c.σ σ6 ?_ ?_ hAInv
    · rw [hgp, hgp6]
    · intro a ha
      -- σ6.mem = writeMap8 (writeMap8 m0 spn s0e) (spn+8) r; a ∈ privFoot ⇒ a ∉ stack
      have hanotstk : ¬ (SL.lo ≤ a ∧ a < sp.toNat) := by
        rintro ⟨h1, h2⟩; exact (hER 0).stack_not_priv a h1 h2 ha
      have hmem6eq : σ6.mem = writeMap8 σ2.mem ((sp - 16#64).toNat + 8) (sdData_val r) := by
        rw [hmem6', hmem5']
      rw [hmem6eq, hmem2']
      rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega), hmem]
  -- === malloc contract call (0x80004790) ===
  -- instantiate malloc's ghost at σ6's own reads so the ABI-frame entry is `rfl`.
  have hStackOK6 : StackOK SL (sp - 16#64) headroom := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hspn_toNat]; omega
    · rw [hspn_toNat]; have := sp.isLt; omega
    · rw [hspn_toNat]
      have h16 : sp.toNat % 16 = 0 := hspalign
      omega
  obtain ⟨c7, hs7, hmpost⟩ :=
    M.spec (fun R => σ6.regs.get? R) exts 32 (sp - 16#64) (0x80002a14#64) σ6.mem hmaxreq
      ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨hG6, hi6, hpc6, ha0_6, hra_6, by decide, hsp6, hStackOK6, hgp6,
        fun R _ => rfl, hAInv_σ6, rfl⟩
  -- malloc post: unpack. `c7` is the return config at PC = 0x80002a14.
  obtain ⟨hG7, hi7, hpc7, hsp7, hgp7, habi7, hresult7, hmemframe7⟩ := hmpost
  -- rule out NULL via the non-exhaustion hypothesis; take the `some p` branch.
  have hsome : ∃ p, c7.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
      p ≠ 0 ∧ p % 16 = 0 ∧ A.contains p 32 ∧
      (∀ e ∈ exts, ExtDisjoint (p, 32) e) ∧ M.AInv c7.σ ((p, 32) :: exts) := by
    rcases hresult7 with ⟨hnull, hAInvexts⟩ | hp
    · exact absurd hAInvexts (fun h => hnonexh c7 h hnull)
    · exact hp
  obtain ⟨p, ha0_7, hp0, hp16, hpcontains, hpdisj, hAInv7⟩ := hsome
  -- Callee-saved registers preserved across malloc via the ABI frame `habi7`:
  have hs8_7 : c7.σ.regs.get? Register.x8 = some par := by
    rw [habi7 Register.x8 (by decide)]; exact hs8_6
  obtain ⟨vmi7, hmi7⟩ := hG7.minstret
  -- p-region facts from `A.contains p 32` + `EnvRegions`; `p + k` no-wrap etc.
  have hpwin := (hER p).frame_win
  have hplo := (hER p).frame_lo
  have hphi := (hER p).frame_hi
  have hpalign := (hER p).frame_align
  have hpstack := (hER p).frame_stack_disjoint
  have hpcode := (hER p).frame_code_disjoint
  have hp_nowrap : p + 32 < 2^64 := by have := hphi; omega
  -- Env_newLoaded at c7: malloc preserved code (disjoint from privFoot and stack)
  have hloaded7 : Env_newLoaded c7.σ.mem := by
    apply loaded_env_of_agree σ6.mem c7.σ.mem
    · intro a hlo hhi
      apply hmemframe7 a
      · exact (hER p).code_not_priv a hlo hhi
      · rintro ⟨hstk1, hstk2⟩
        have := (hER p).code_stack_disjoint; rw [hspn_toNat] at hstk2; omega
    · exact hmem6' ▸ hloaded5
  -- === 0x80002a14: beqz a0 (not taken; p ≠ 0) ⇒ fall to 0x80002a18 ===
  have hbne : ((BitVec.ofNat 64 p) == 0#64) = false := by
    rw [beq_eq_false_iff_ne, ne_eq]
    intro heq
    have : (BitVec.ofNat 64 p).toNat = (0#64 : BitVec 64).toNat := by rw [heq]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    exact hp0 (by simpa using this)
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80002a14_nottaken_env c7.σ c7.tick c7.steps (0x80002a14#64) vmi7 (BitVec.ofNat 64 p)
      hG7 hpc7 hmi7 ha0_7 hloaded7 rfl hbne hi7
  have hstep8 : Step c7 ⟨σ8, i8, c7.steps + 1⟩ := by cases c7; exact hs8
  have hpc8 : σ8.regs.get? Register.PC = some (0x80002a18#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs8
    rwa [show BitVec.addInt (0x80002a14#64 : BitVec 64) 4 = (0x80002a18#64 : BitVec 64) from by decide] at this
  have ha0_8 := obs_bnottaken_other hobs8 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_7
  have hsp8 := obs_bnottaken_other hobs8 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp7
  have hgp8 := obs_bnottaken_other hobs8 Register.x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hgp7
  have hs8_8 := obs_bnottaken_other hobs8 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs8_7
  obtain ⟨vmi8, hmi8⟩ := obs_bnottaken_minstret hobs8
  have hmem8' : σ8.mem = c7.σ.mem := hmem8
  have hloaded8 : Env_newLoaded σ8.mem := hmem8' ▸ hloaded7
  -- General spill-byte readback: for a slot address `sa` with `spn ≤ sa` and
  -- `sa + 8 ≤ entry_sp`, and slot-offset window `[sa, sa+8) ⊆ [spn, entry_sp)`,
  -- the byte `σ8.mem[sa + k]` equals the spilled `writeMap8` byte, because malloc
  -- preserved it (∉ privFoot via `spill_not_priv`, and `≥ spn` so ∉ `[SL.lo, spn)`).
  have spill_lo_le : SL.lo ≤ (sp - 16#64).toNat := by
    rw [hspn_toNat]; have := (hER 0).spill_lo; have := hSLlo; omega
  have spn16 : (sp - 16#64).toNat + 16 = sp.toNat := by rw [hspn_toNat]; omega
  -- the spilled memory `σ6.mem = writeMap8 (writeMap8 m0 spn s0e) (spn+8) r`
  have hmem6full : σ6.mem = writeMap8 (writeMap8 c.σ.mem (sp - 16#64).toNat (sdData_val s0e))
      ((sp - 16#64).toNat + 8) (sdData_val r) := by rw [hmem6', hmem5', hmem2']
  -- byte transfer from σ6 to σ8 (= c7.mem) at a spill-window offset `j < 16`:
  have spill_transfer : ∀ j, j < 16 →
      σ8.mem[(sp - 16#64).toNat + j]? = σ6.mem[(sp - 16#64).toNat + j]? := by
    intro j hj
    rw [hmem8']
    apply hmemframe7 ((sp - 16#64).toNat + j)
    · rw [hspn_toNat]; exact (hER 0).spill_not_priv j hj
    · rintro ⟨_, hlt⟩; rw [hspn_toNat] at hlt; omega
  -- the `ld ra` reads spn+8; its k-th byte (k<8) is `(sdData_val r).extractLsb' (8k) 8`.
  have hld_ra : ∀ k, k < 8 → (σ6.mem[((sp - 16#64).toNat + 8) + k]? = some ((sdData_val r).extractLsb' (8 * k) 8)) →
      σ8.mem[((sp - 16#64) + sign_extend (m := 64) (0x008#12)).toNat + k]?
        = some ((sdData_val r).extractLsb' (8 * k) 8) := fun k hk glem => by
    rw [hspn8]
    have ht := spill_transfer (8 + k) (by omega)
    rw [show (sp - 16#64).toNat + (8 + k) = ((sp - 16#64).toNat + 8) + k from by omega] at ht
    rw [ht]; exact glem
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80002a18_env σ8 i8 (c7.steps + 1) (0x80002a18#64) vmi8 (sp - 16#64)
      ((sdData_val r).extractLsb' 0 8) ((sdData_val r).extractLsb' 8 8)
      ((sdData_val r).extractLsb' 16 8) ((sdData_val r).extractLsb' 24 8)
      ((sdData_val r).extractLsb' 32 8) ((sdData_val r).extractLsb' 40 8)
      ((sdData_val r).extractLsb' 48 8) ((sdData_val r).extractLsb' 56 8)
      hG8 hpc8 hmi8 hsp8 hloaded8 rfl
      (by rw [hspn8, hspn_toNat]; have := (hER 0).spill_lo; omega)
      (by rw [hspn8, hspn_toNat]; have := (hER 0).spill_hi; omega)
      (by rw [hspn8, hspn_toNat]; right; have := (hER 0).spill_win; have : tohostAddr = 0x8001ad00 := rfl; omega)
      (by rw [hspn8, hspn_toNat]; have := (hER 0).spill_align; omega)
      (by have := hld_ra 0 (by omega) (by rw [hmem6full, getElem_writeMap8_0]); simpa using this)
      (by have := hld_ra 1 (by omega) (by rw [hmem6full, getElem_writeMap8_1]); simpa using this)
      (by have := hld_ra 2 (by omega) (by rw [hmem6full, getElem_writeMap8_2]); simpa using this)
      (by have := hld_ra 3 (by omega) (by rw [hmem6full, getElem_writeMap8_3]); simpa using this)
      (by have := hld_ra 4 (by omega) (by rw [hmem6full, getElem_writeMap8_4]); simpa using this)
      (by have := hld_ra 5 (by omega) (by rw [hmem6full, getElem_writeMap8_5]); simpa using this)
      (by have := hld_ra 6 (by omega) (by rw [hmem6full, getElem_writeMap8_6]); simpa using this)
      (by have := hld_ra 7 (by omega) (by rw [hmem6full, getElem_writeMap8_7]); simpa using this) hi8
  have hstep9 : Step ⟨σ8, i8, c7.steps + 1⟩ ⟨σ9, i9, c7.steps + 1 + 1⟩ := hs9
  have hpc9 : σ9.regs.get? Register.PC = some (0x80002a1c#64 : BitVec 64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x80002a18#64 : BitVec 64) 4 = (0x80002a1c#64 : BitVec 64) from by decide] at this
  have hra_9 : σ9.regs.get? Register.x1 = some r := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext_reassemble r _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
  have hsp9 := obs_alu_other hobs9 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp8
  have ha0_9 := obs_alu_other hobs9 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_8
  have hgp9 := obs_alu_other hobs9 Register.x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hgp8
  have hs8_9 := obs_alu_other hobs9 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs8_8
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have hmem9' : σ9.mem = σ8.mem := hmem9
  have hloaded9 : Env_newLoaded σ9.mem := hmem9' ▸ hloaded8
  -- a0 at σ9 is still the fresh pointer `ofNat p`
  have ha0_9p : σ9.regs.get? Register.x10 = some (BitVec.ofNat 64 p) := ha0_9
  -- pointer-offset addresses within the fresh frame (no wrap, from hp_nowrap)
  have hp_toNat : (BitVec.ofNat 64 p).toNat = p := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hp24 : ((BitVec.ofNat 64 p) + sign_extend (m := 64) (0x018#12)).toNat = p + 24 := by
    rw [off24_addr]; rw [hp_toNat]; rw [hp_toNat]; omega
  have hp0a : ((BitVec.ofNat 64 p) + sign_extend (m := 64) (0x000#12)).toNat = p := by
    rw [off0_addr, hp_toNat]
  have hp8 : ((BitVec.ofNat 64 p) + sign_extend (m := 64) (0x008#12)).toNat = p + 8 := by
    rw [off8_addr]; rw [hp_toNat]; rw [hp_toNat]; omega
  have hp16' : ((BitVec.ofNat 64 p) + sign_extend (m := 64) (0x010#12)).toNat = p + 16 := by
    rw [off16_addr]; rw [hp_toNat]; rw [hp_toNat]; omega
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- === 0x80002a1c: sd s0,24(a0)  ⇒ mem += (par @ p+24) [parent field] ===
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_80002a1c_env σ9 i9 (c7.steps + 1 + 1) (0x80002a1c#64) vmi9 (BitVec.ofNat 64 p) par
      hG9 hpc9 hmi9 ha0_9p hs8_9 hloaded9 rfl
      (by rw [hp24]; omega) (by rw [hp24]; omega) (by rw [hp24]; omega) (by rw [hp24]; omega) hi9
  have hstep10 : Step ⟨σ9, i9, c7.steps + 1 + 1⟩ ⟨σ10, i10, c7.steps + 1 + 1 + 1⟩ := hs10
  have hpc10 : σ10.regs.get? Register.PC = some (0x80002a20#64 : BitVec 64) := by
    have := obs_store_pc hobs10
    rwa [show BitVec.addInt (0x80002a1c#64 : BitVec 64) 4 = (0x80002a20#64 : BitVec 64) from by decide] at this
  have hsp10 := obs_store_other hobs10 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp9
  have ha0_10 := obs_store_other hobs10 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_9p
  have hra_10 := obs_store_other hobs10 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_9
  have hgp10 := obs_store_other hobs10 Register.x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hgp9
  obtain ⟨vmi10, hmi10⟩ := obs_store_minstret hobs10
  have hmem10' : σ10.mem = writeMap8 σ9.mem (p + 24) (sdData_val par) := by
    rw [hmem10, mem_afterNextPC, hp24]
  have hloaded10 : Env_newLoaded σ10.mem := by
    rw [hmem10']
    exact loaded_env_writeMap8 σ9.mem (p + 24) (sdData_val par)
      (by have := (hER p).frame_code_disjoint; omega) hloaded9
  -- === 0x80002a20: ld s0,0(sp)  ⇒ x8 := s0e (spilled at spn+0; frame ≠ stack) ===
  have hld_s0 : ∀ k, k < 8 →
      σ10.mem[((sp - 16#64) + sign_extend (m := 64) (0x000#12)).toNat + k]?
        = some ((sdData_val s0e).extractLsb' (8 * k) 8) := by
    intro k hk
    rw [hspn0]
    rw [hmem10', getElem_writeMap8_disjoint _ _ _ _
      (by have := (hER p).frame_stack_disjoint; rw [hspn_toNat] at *; omega)]
    rw [hmem9', hmem8']
    have ht := spill_transfer k (by omega)
    rw [hmem8'] at ht
    rw [ht, hmem6full]
    rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]
    match k, hk with
    | 0, _ => simpa using getElem_writeMap8_0 c.σ.mem (sp - 16#64).toNat (sdData_val s0e)
    | 1, _ => simpa using getElem_writeMap8_1 c.σ.mem (sp - 16#64).toNat (sdData_val s0e)
    | 2, _ => simpa using getElem_writeMap8_2 c.σ.mem (sp - 16#64).toNat (sdData_val s0e)
    | 3, _ => simpa using getElem_writeMap8_3 c.σ.mem (sp - 16#64).toNat (sdData_val s0e)
    | 4, _ => simpa using getElem_writeMap8_4 c.σ.mem (sp - 16#64).toNat (sdData_val s0e)
    | 5, _ => simpa using getElem_writeMap8_5 c.σ.mem (sp - 16#64).toNat (sdData_val s0e)
    | 6, _ => simpa using getElem_writeMap8_6 c.σ.mem (sp - 16#64).toNat (sdData_val s0e)
    | 7, _ => simpa using getElem_writeMap8_7 c.σ.mem (sp - 16#64).toNat (sdData_val s0e)
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_80002a20_env σ10 i10 (c7.steps + 1 + 1 + 1) (0x80002a20#64) vmi10 (sp - 16#64)
      ((sdData_val s0e).extractLsb' 0 8) ((sdData_val s0e).extractLsb' 8 8)
      ((sdData_val s0e).extractLsb' 16 8) ((sdData_val s0e).extractLsb' 24 8)
      ((sdData_val s0e).extractLsb' 32 8) ((sdData_val s0e).extractLsb' 40 8)
      ((sdData_val s0e).extractLsb' 48 8) ((sdData_val s0e).extractLsb' 56 8)
      hG10 hpc10 hmi10 hsp10 hloaded10 rfl
      (by rw [hspn0, hspn_toNat]; have := (hER 0).spill_lo; omega)
      (by rw [hspn0, hspn_toNat]; have := (hER 0).spill_hi; omega)
      (by rw [hspn0, hspn_toNat]; right; have := (hER 0).spill_win; omega)
      (by rw [hspn0, hspn_toNat]; have := (hER 0).spill_align; omega)
      (by have := hld_s0 0 (by omega); simpa using this)
      (by have := hld_s0 1 (by omega); simpa using this)
      (by have := hld_s0 2 (by omega); simpa using this)
      (by have := hld_s0 3 (by omega); simpa using this)
      (by have := hld_s0 4 (by omega); simpa using this)
      (by have := hld_s0 5 (by omega); simpa using this)
      (by have := hld_s0 6 (by omega); simpa using this)
      (by have := hld_s0 7 (by omega); simpa using this) hi10
  have hstep11 : Step ⟨σ10, i10, c7.steps + 1 + 1 + 1⟩ ⟨σ11, i11, c7.steps + 1 + 1 + 1 + 1⟩ := hs11
  have hpc11 : σ11.regs.get? Register.PC = some (0x80002a24#64 : BitVec 64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x80002a20#64 : BitVec 64) 4 = (0x80002a24#64 : BitVec 64) from by decide] at this
  have hsp11 := obs_alu_other hobs11 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp10
  have ha0_11 := obs_alu_other hobs11 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_10
  have hra_11 := obs_alu_other hobs11 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_10
  have hgp11 := obs_alu_other hobs11 Register.x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hgp10
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hmem11' : σ11.mem = σ10.mem := hmem11
  have hloaded11 : Env_newLoaded σ11.mem := hmem11' ▸ hloaded10
  -- === 0x80002a24: sd zero,0(a0)  ⇒ mem += (0 @ p) [count=cap=0] ===
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_80002a24_env σ11 i11 (c7.steps + 1 + 1 + 1 + 1) (0x80002a24#64) vmi11 (BitVec.ofNat 64 p)
      hG11 hpc11 hmi11 ha0_11 hloaded11 rfl
      (by rw [hp0a]; omega) (by rw [hp0a]; omega) (by rw [hp0a]; omega) (by rw [hp0a]; omega) hi11
  have hstep12 : Step ⟨σ11, i11, c7.steps + 1 + 1 + 1 + 1⟩ ⟨σ12, i12, c7.steps + 1 + 1 + 1 + 1 + 1⟩ := hs12
  have hpc12 : σ12.regs.get? Register.PC = some (0x80002a28#64 : BitVec 64) := by
    have := obs_store_pc hobs12
    rwa [show BitVec.addInt (0x80002a24#64 : BitVec 64) 4 = (0x80002a28#64 : BitVec 64) from by decide] at this
  have hsp12 := obs_store_other hobs12 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp11
  have ha0_12 := obs_store_other hobs12 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_11
  have hra_12 := obs_store_other hobs12 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_11
  have hgp12 := obs_store_other hobs12 Register.x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hgp11
  obtain ⟨vmi12, hmi12⟩ := obs_store_minstret hobs12
  have hmem12' : σ12.mem = writeMap8 σ11.mem p (sdData_val (0#64)) := by
    rw [hmem12, mem_afterNextPC, hp0a]
  have hloaded12 : Env_newLoaded σ12.mem := by
    rw [hmem12']
    exact loaded_env_writeMap8 σ11.mem p (sdData_val (0#64))
      (by have := (hER p).frame_code_disjoint; omega) hloaded11
  -- === 0x80002a28: sd zero,8(a0)  ⇒ mem += (0 @ p+8) [names=NULL] ===
  obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
    site_80002a28_env σ12 i12 (c7.steps + 1 + 1 + 1 + 1 + 1) (0x80002a28#64) vmi12 (BitVec.ofNat 64 p)
      hG12 hpc12 hmi12 ha0_12 hloaded12 rfl
      (by rw [hp8]; omega) (by rw [hp8]; omega) (by rw [hp8]; omega) (by rw [hp8]; omega) hi12
  have hstep13 : Step ⟨σ12, i12, c7.steps + 1 + 1 + 1 + 1 + 1⟩ ⟨σ13, i13, c7.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs13
  have hpc13 : σ13.regs.get? Register.PC = some (0x80002a2c#64 : BitVec 64) := by
    have := obs_store_pc hobs13
    rwa [show BitVec.addInt (0x80002a28#64 : BitVec 64) 4 = (0x80002a2c#64 : BitVec 64) from by decide] at this
  have hsp13 := obs_store_other hobs13 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp12
  have ha0_13 := obs_store_other hobs13 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_12
  have hra_13 := obs_store_other hobs13 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_12
  have hgp13 := obs_store_other hobs13 Register.x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hgp12
  obtain ⟨vmi13, hmi13⟩ := obs_store_minstret hobs13
  have hmem13' : σ13.mem = writeMap8 σ12.mem (p + 8) (sdData_val (0#64)) := by
    rw [hmem13, mem_afterNextPC, hp8]
  have hloaded13 : Env_newLoaded σ13.mem := by
    rw [hmem13']
    exact loaded_env_writeMap8 σ12.mem (p + 8) (sdData_val (0#64))
      (by have := (hER p).frame_code_disjoint; omega) hloaded12
  -- === 0x80002a2c: sd zero,16(a0)  ⇒ mem += (0 @ p+16) [vals=NULL] ===
  obtain ⟨σ14, i14, hs14, hi14, hG14, hmem14, hobs14⟩ :=
    site_80002a2c_env σ13 i13 (c7.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80002a2c#64) vmi13 (BitVec.ofNat 64 p)
      hG13 hpc13 hmi13 ha0_13 hloaded13 rfl
      (by rw [hp16']; omega) (by rw [hp16']; omega) (by rw [hp16']; omega) (by rw [hp16']; omega) hi13
  have hstep14 : Step ⟨σ13, i13, c7.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ14, i14, c7.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs14
  have hpc14 : σ14.regs.get? Register.PC = some (0x80002a30#64 : BitVec 64) := by
    have := obs_store_pc hobs14
    rwa [show BitVec.addInt (0x80002a2c#64 : BitVec 64) 4 = (0x80002a30#64 : BitVec 64) from by decide] at this
  have hsp14 := obs_store_other hobs14 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp13
  have ha0_14 := obs_store_other hobs14 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_13
  have hra_14 := obs_store_other hobs14 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_13
  have hgp14 := obs_store_other hobs14 Register.x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hgp13
  obtain ⟨vmi14, hmi14⟩ := obs_store_minstret hobs14
  have hmem14' : σ14.mem = writeMap8 σ13.mem (p + 16) (sdData_val (0#64)) := by
    rw [hmem14, mem_afterNextPC, hp16']
  have hloaded14 : Env_newLoaded σ14.mem := by
    rw [hmem14']
    exact loaded_env_writeMap8 σ13.mem (p + 16) (sdData_val (0#64))
      (by have := (hER p).frame_code_disjoint; omega) hloaded13
  -- === 0x80002a30: addi sp,sp,16  ⇒ x2 := sp (restore) ===
  obtain ⟨σ15, i15, hs15, hi15, hG15, hmem15, hobs15⟩ :=
    site_80002a30_env σ14 i14 (c7.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80002a30#64) vmi14 (sp - 16#64)
      hG14 hpc14 hmi14 hsp14 hloaded14 rfl hi14
  have hstep15 : Step ⟨σ14, i14, c7.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ15, i15, c7.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs15
  have hpc15 : σ15.regs.get? Register.PC = some (0x80002a34#64 : BitVec 64) := by
    have := obs_alu_pc hobs15
    rwa [show BitVec.addInt (0x80002a30#64 : BitVec 64) 4 = (0x80002a34#64 : BitVec 64) from by decide] at this
  have hsp15 : σ15.regs.get? Register.x2 = some sp := by
    have := obs_alu_rd hobs15 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sp_restore sp] at this
  have ha0_15 := obs_alu_other hobs15 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_14
  have hra_15 := obs_alu_other hobs15 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_14
  have hgp15 := obs_alu_other hobs15 Register.x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hgp14
  obtain ⟨vmi15, hmi15⟩ := obs_alu_minstret hobs15
  have hmem15' : σ15.mem = σ14.mem := hmem15
  have hloaded15 : Env_newLoaded σ15.mem := hmem15' ▸ hloaded14
  -- === 0x80002a34: ret  ⇒ PC := r ===
  obtain ⟨σ16, i16, hs16, hi16, hG16, hmem16, hobs16⟩ :=
    site_80002a34_env σ15 i15 (c7.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80002a34#64) vmi15 r
      hG15 hpc15 hmi15 hra_15 hloaded15 rfl hrettgt hi15
  have hstep16 : Step ⟨σ15, i15, c7.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ16, i16, c7.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs16
  have hmem16' : σ16.mem = σ14.mem := by rw [hmem16, hmem15']
  -- PC = r (bit-0-cleared ra = r, since r 4-aligned)
  have hpc16 : σ16.regs.get? Register.PC = some r := by
    rw [obs_jr_pc hobs16, ret_tgt r hralign]
  -- lift the returned registers through the final `ret` (jr preserves GPRs)
  have hsp16 := obs_jr_other hobs16 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp15
  have hgp16 := obs_jr_other hobs16 Register.x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hgp15
  have hra16 := obs_jr_other hobs16 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_15
  have ha0_16 := obs_jr_other hobs16 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_15
  -- assemble the whole run
  have hsteps : Steps c ⟨σ16, i16, c7.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := by
    refine (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
      ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans
      (hs7.trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans
      ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans
      ((Steps.single hstep13).trans ((Steps.single hstep14).trans ((Steps.single hstep15).trans
      (Steps.single hstep16)))))))))))))))
  -- final memory: σ16.mem = σ14.mem = writeMap8×3 over p on top of (par@p+24) over σ9.mem
  have hmemfin : σ16.mem = writeMap8 (writeMap8 (writeMap8
      (writeMap8 σ9.mem (p + 24) (sdData_val par)) p (sdData_val (0#64)))
      (p + 8) (sdData_val (0#64))) (p + 16) (sdData_val (0#64)) := by
    rw [hmem16', hmem14', hmem13', hmem12', hmem11', hmem10']
  -- AInv at σ16 from `hAInv7` (at c7) via `hAInvFrame`: the suffix wrote only the fresh
  -- block `[p, p+32)`, disjoint from `privFoot` (`MallocContract.privFoot_disjoint`),
  -- and gp is preserved (hgp15 lifts to c7 through habi7).
  have hAInv_σ16 : M.AInv σ16 ((p, 32) :: exts) := by
    refine hAInvFrame ((p, 32) :: exts) c7.σ σ16 ?_ ?_ hAInv7
    · -- gp: c7 and σ16 both hold gpv
      rw [hgp7]; exact hgp16.symm
    · intro a ha
      -- a ∈ privFoot ⇒ a ∉ [p, p+32) (privFoot disjoint from the live extent (p,32))
      have hanotp : a < p ∨ p + 32 ≤ a := by
        rcases Nat.lt_or_ge a p with h | h
        · exact Or.inl h
        rcases Nat.lt_or_ge a (p + 32) with h2 | h2
        · exact absurd ha (M.privFoot_disjoint c7.σ ((p, 32) :: exts) hAInv7 (p, 32) (by simp)
            (a - p) (by omega) |> fun hnp => (show p + (a - p) = a from by omega) ▸ hnp)
        · exact Or.inr h2
      -- σ16.mem = writeMap8×4 over σ9.mem within [p, p+32); a outside ⇒ passthrough
      rw [hmemfin,
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega),
        getElem_writeMap8_disjoint _ _ _ _ (by omega)]
      -- σ9.mem = σ8.mem = c7.mem
      rw [hmem9', hmem8']
  refine ⟨⟨σ16, i16, c7.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, hsteps, hG16, hi16, hpc16,
    hsp16, hgp16, hra16, ?_, ⟨p, ha0_16, hp0, hp16, hpcontains, hpdisj, hAInv_σ16, ?_, ?_⟩, ?_⟩
  · -- x8 = s0e (callee-saved s0 restored by `ld s0` at σ11, preserved to σ16)
    have hs8_11 : σ11.regs.get? Register.x8 = some s0e := by
      have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [sext_reassemble s0e _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
    have hs8_12 := obs_store_other hobs12 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs8_11
    have hs8_13 := obs_store_other hobs13 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs8_12
    have hs8_14 := obs_store_other hobs14 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs8_13
    have hs8_15 := obs_alu_other hobs15 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs8_14
    exact obs_jr_other hobs16 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs8_15
  · -- FrameRepr for the fresh empty frame ⟨parentSpec, []⟩ at p
    refine ⟨?_, ⟨0, ?_, Nat.le_refl 0⟩, ⟨0, 0, ?_, ?_, ?_⟩, ?_⟩
    · -- count: read32 p = 0 = ([] : List _).length
      show read32 σ16.mem p = some ([] : List (String × Vsa.While.Value)).length
      rw [hmemfin]
      rw [read32_writeMap8_disjoint _ _ _ _ (by omega),
        read32_writeMap8_disjoint _ _ _ _ (by omega), read32_writeMap8_lo, sdData_val_zero_toNat]
      rfl
    · -- cap: read32 (p+4) = 0
      show read32 σ16.mem (p + 4) = some 0
      rw [hmemfin]
      rw [read32_writeMap8_disjoint _ _ _ _ (by omega),
        read32_writeMap8_disjoint _ _ _ _ (by omega),
        show p + 4 = p + 4 from rfl, read32_writeMap8_hi, sdData_val_zero_toNat]
    · -- names ptr read64 (p+8) = 0
      show read64 σ16.mem (p + 8) = some 0
      rw [hmemfin]
      rw [read64_writeMap8_disjoint _ _ _ _ (by omega), read64_writeMap8, sdData_val_zero_toNat]
    · -- vals ptr read64 (p+16) = 0
      show read64 σ16.mem (p + 16) = some 0
      rw [hmemfin, read64_writeMap8, sdData_val_zero_toNat]
    · -- (vacuous binding clause: [].length = 0, no i < 0)
      intro i hi'; exact absurd hi' (by simp)
    · -- parent field: read64 (p+24) = par (or φf), per parentSpec
      show (match (⟨parentSpec, []⟩ : Frame).parent with
        | none => read64 σ16.mem (p + 24) = some 0
        | some pa => read64 σ16.mem (p + 24) = some (φf pa) ∧ φf pa ≠ 0)
      have hpar24 : read64 σ16.mem (p + 24) = some par.toNat := by
        rw [hmemfin]
        rw [read64_writeMap8_disjoint _ _ _ _ (by omega),
          read64_writeMap8_disjoint _ _ _ _ (by omega),
          read64_writeMap8_disjoint _ _ _ _ (by omega), read64_writeMap8, sdData_toNat]
      cases parentSpec with
      | none =>
        show read64 σ16.mem (p + 24) = some 0
        rw [hpar24, hparlink]; rfl
      | some pa =>
        show read64 σ16.mem (p + 24) = some (φf pa) ∧ φf pa ≠ 0
        obtain ⟨hlink, hne⟩ := hparlink
        refine ⟨by rw [hpar24, hlink], ?_⟩
        rw [hlink]
        intro h
        apply hne
        apply BitVec.eq_of_toNat_eq
        rw [h]; rfl
  · -- memory framed: outside [p,p+32) ∪ privFoot ∪ stack, mem unchanged
    intro a hpriv hstk hframe_a
    -- `a` is outside the stack window `[spn, spn+16)` (from `hstk` + `spn ≥ SL.lo`,
    -- `spn + 16 = sp.toNat`).
    have ha_stack : a < (sp - 16#64).toNat ∨ (sp - 16#64).toNat + 16 ≤ a := by
      rw [hspn_toNat]
      rcases Nat.lt_or_ge a SL.lo with h | h
      · left; have := spill_lo_le; rw [hspn_toNat] at this; omega
      · right
        have hnlt : ¬ (a < sp.toNat) := fun hlt => hstk ⟨h, hlt⟩
        omega
    rw [hmemfin]
    -- the four frame writes are all inside [p, p+32); a is outside
    rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
      getElem_writeMap8_disjoint _ _ _ _ (by omega),
      getElem_writeMap8_disjoint _ _ _ _ (by omega),
      getElem_writeMap8_disjoint _ _ _ _ (by omega)]
    -- now σ9.mem[a] = c7.mem[a] = σ6.mem[a] (malloc frame) = m0[a] (spill outside a)
    rw [hmem9', hmem8']
    have hmf := hmemframe7 a hpriv (by
      rintro ⟨h1, h2⟩; exact hstk ⟨h1, by rw [hspn_toNat] at h2; omega⟩)
    rw [hmf, hmem6full]
    -- σ6.mem = writeMap8 (writeMap8 m0 spn s0e) (spn+8) r; a outside both spill windows
    rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
      getElem_writeMap8_disjoint _ _ _ _ (by omega)]
    rw [hmem]
  · -- callee-saved frame: every ABI-preserved register reads as ghost `g`.
    intro R hAbi
    -- `g R = c.σ.regs.get? R` for ABI-preserved R (from P's frame), so it suffices
    -- to show env_new preserves R: `σ16.regs.get? R = c.σ.regs.get? R`.
    rw [← hframe R hAbi]
    -- x2 (sp) and x8 (s0) are written-then-restored; handle explicitly.
    by_cases hx2 : R = Register.x2
    · subst hx2; rw [hsp16]; exact hsp.symm
    by_cases hx8 : R = Register.x8
    · subst hx8
      -- x8 restored to s0e at σ11 and preserved through σ12..σ16
      have hs8_11 : σ11.regs.get? Register.x8 = some s0e := by
        have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
        rwa [sext_reassemble s0e _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl] at this
      have hs8_12 := obs_store_other hobs12 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs8_11
      have hs8_13 := obs_store_other hobs13 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs8_12
      have hs8_14 := obs_store_other hobs14 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs8_13
      have hs8_15 := obs_alu_other hobs15 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs8_14
      have hs8_16 := obs_jr_other hobs16 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs8_15
      rw [hs8_16]; exact hs8e.symm
    -- other ABI-preserved R: NotWrittenEnv R holds; thread prefix→σ6 (frame),
    -- malloc σ6→c7 (habi7), suffix c7→σ16 (frame).
    have hR : NotWrittenEnv R :=
      ⟨abi_ne (by decide) hAbi, beq_false_of_ne' hx2,
       beq_false_of_ne' hx8, abi_ne (by decide) hAbi,
       abi_ne (by decide) hAbi, abi_ne (by decide) hAbi, abi_ne (by decide) hAbi,
       abi_ne (by decide) hAbi, abi_ne (by decide) hAbi, abi_ne (by decide) hAbi,
       abi_ne (by decide) hAbi⟩
    -- prefix threading c.σ → σ6
    have ep : σ6.regs.get? R = c.σ.regs.get? R := by
      rw [frame_jal_env hobs6 R (abi_ne (by decide) hAbi) hR,
        frame_store_env hobs5 R hR,
        frame_alu_env hobs4 R hR.x10 hR,
        frame_alu_env hobs3 R hR.x8 hR,
        frame_store_env hobs2 R hR,
        frame_alu_env hobs1 R hR.x2 hR]
    -- malloc region σ6 → c7 via ABI frame
    have em : c7.σ.regs.get? R = σ6.regs.get? R := habi7 R hAbi
    -- suffix threading c7 (= σ8's pred) → σ16
    have es : σ16.regs.get? R = c7.σ.regs.get? R := by
      rw [frame_jr_env hobs16 R hR,
        frame_alu_env hobs15 R hR.x2 hR,
        frame_store_env hobs14 R hR,
        frame_store_env hobs13 R hR,
        frame_store_env hobs12 R hR,
        frame_alu_env hobs11 R hR.x8 hR,
        frame_store_env hobs10 R hR,
        frame_alu_env hobs9 R hR.x1 hR,
        frame_bnottaken_env hobs8 R hR]
    rw [es, em, ep]

end Vsa.Sim
