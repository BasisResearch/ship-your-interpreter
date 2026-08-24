import Vsa.Sim.JmpSites
import Vsa.Sim.Code.Runtime_error
import Vsa.Sim.ValueSpec
import Vsa.Sim.ValueTruthySpec
import Vsa.Sim.Muldi3Spec
import Vsa.Triple

/-!
# Layer 3 — total-correctness specs for the error-transfer core: `setjmp`, `longjmp`,
`runtime_error`

Config-level (`Vsa.Logic.Triple`) composition of the per-site observational steps
(`Vsa/Sim/JmpSites.lean`) into total-correctness triples for the newlib RV64
soft-float `setjmp`/`longjmp` and the interpreter's `runtime_error`, per the
analysis brief `experiments/M3-setjmp-longjmp.md` (§5 spec shapes, §2 jmp_buf
layout, §3 continuation contract).

The **jmp_buf** is 112 bytes at address `jb` (= `&interp->on_error` = `in + 16`),
15 GPR slots: `ra`@0, `s0`@8, `s1`@16, `s2..s11`@24..96, `sp`@104 (see §2).

* `setjmp_spec` (initial zero-return passage): from entry with `a0 = jb`, the 14
  `sd`s copy the live callee-saved registers into the buffer, `li a0,0` returns 0,
  and `ret` lands at the caller's `ra`.  `Q` states the **exact buffer write chain**
  (the load-bearing part: these become the contents `longjmp` reads back), `a0 = 0`,
  `PC = ra0`, and every register other than `a0`/`PC` framed to entry.
* `longjmp_spec`: from entry with `a0 = jb`, `a1 = v`, and `P` carrying the 15
  buffer contents as `read64` facts (per the brief: "state P with the 15 read64
  facts, not a history"), the 14 `ld`s restore `ra,s0..s11,sp`, `seqz`/`add`
  materialize `a0 = (v==0 ? 1 : v)`, and `ret` lands at the restored `ra`.
* `runtime_error_spec`: two `snprintf` calls (into a stack `body` scratch and into
  `err_msg` at `in+224`) then `longjmp(&in->on_error, 1)`.  Since `snprintf` is not
  forward-simulated here, this spec is **segmented + parameterized by a
  `SnprintfContract` structure hypothesis** (TYPE-valued, NOT an axiom): given a
  contract that `snprintf` terminates leaving `err_msg` in-bounds and the jmp_buf
  untouched, `runtime_error` transfers control (via `longjmp_spec`) to interp_run's
  return-again point `0x80004428` with `a0 = 1` and callee-saveds restored.

Idiom follows `EnvNewSpec`/`Muldi3Spec`: `StepObs` steps, `obs_*` consumers, the
blanket ghost-frame (`NotWrittenJmp` + `frame_*_jmp` one-liners), `tick < 2`,
`minstret` ∃-bound, all noise absorbed.  Region lemmas cloned privately with a
`_jmp` suffix (a shared `Vsa/Sim/Regions.lean` is being authored concurrently — not
imported).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr
open Vsa.Sim.Code (SetjmpLoaded LongjmpLoaded Runtime_errorLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Blanket ghost-frame predicate + generic per-class helpers

`setjmp` writes GPRs only `x10` (`li a0,0`) and memory; `longjmp` writes
`x1,x2,x8,x9,x18..x27,x10`.  We use a single `NotWrittenJmp` covering the union so
both functions share the frame helpers. -/

/-- `R` is outside the union of the jmp functions' written GPRs
(`x1,x2,x8,x9,x10,x18..x27`) and every hot-path step's write/tick set. -/
abbrev NotWrittenJmp (R : Register) : Prop :=
  (Register.x1 == R) = false ∧ (Register.x2 == R) = false ∧
  (Register.x8 == R) = false ∧ (Register.x9 == R) = false ∧
  (Register.x10 == R) = false ∧
  (Register.x18 == R) = false ∧ (Register.x19 == R) = false ∧
  (Register.x20 == R) = false ∧ (Register.x21 == R) = false ∧
  (Register.x22 == R) = false ∧ (Register.x23 == R) = false ∧
  (Register.x24 == R) = false ∧ (Register.x25 == R) = false ∧
  (Register.x26 == R) = false ∧ (Register.x27 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

theorem NotWrittenJmp.pc {R : Register} (h : NotWrittenJmp R) : (Register.PC == R) = false :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem NotWrittenJmp.npc {R : Register} (h : NotWrittenJmp R) : (Register.nextPC == R) = false :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem NotWrittenJmp.mi {R : Register} (h : NotWrittenJmp R) : (Register.minstret == R) = false :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem NotWrittenJmp.mii {R : Register} (h : NotWrittenJmp R) :
    (Register.minstret_increment == R) = false :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem NotWrittenJmp.mc {R : Register} (h : NotWrittenJmp R) : (Register.mcycle == R) = false :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem NotWrittenJmp.mt {R : Register} (h : NotWrittenJmp R) : (Register.mtime == R) = false :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem NotWrittenJmp.mip {R : Register} (h : NotWrittenJmp R) : (Register.mip == R) = false :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- Generic ALU frame step (covers `mv`/`li`/`seqz`/`add`, and the ALU-class `ld`). -/
theorem frame_alu_jmp {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) (R : Register)
    (hrd : (rd == R) = false) (hR : NotWrittenJmp R) :
    σ'.regs.get? R = σ.regs.get? R := by
  rw [hobs.1 R hR.mc hR.mt hR.mip]
  exact get?_sigmaPost_alu σ pc vm rd v R hR.mi hR.pc hrd hR.npc hR.mii

theorem NotWrittenJmp.x10 {R : Register} (h : NotWrittenJmp R) : (Register.x10 == R) = false :=
  h.2.2.2.2.1
theorem NotWrittenJmp.x1 {R : Register} (h : NotWrittenJmp R) : (Register.x1 == R) = false :=
  h.1
theorem NotWrittenJmp.x2 {R : Register} (h : NotWrittenJmp R) : (Register.x2 == R) = false :=
  h.2.1
theorem NotWrittenJmp.x8 {R : Register} (h : NotWrittenJmp R) : (Register.x8 == R) = false :=
  h.2.2.1
theorem NotWrittenJmp.x9 {R : Register} (h : NotWrittenJmp R) : (Register.x9 == R) = false :=
  h.2.2.2.1
theorem NotWrittenJmp.x18 {R : Register} (h : NotWrittenJmp R) : (Register.x18 == R) = false :=
  h.2.2.2.2.2.1
theorem NotWrittenJmp.x19 {R : Register} (h : NotWrittenJmp R) : (Register.x19 == R) = false :=
  h.2.2.2.2.2.2.1
theorem NotWrittenJmp.x20 {R : Register} (h : NotWrittenJmp R) : (Register.x20 == R) = false :=
  h.2.2.2.2.2.2.2.1
theorem NotWrittenJmp.x21 {R : Register} (h : NotWrittenJmp R) : (Register.x21 == R) = false :=
  h.2.2.2.2.2.2.2.2.1
theorem NotWrittenJmp.x22 {R : Register} (h : NotWrittenJmp R) : (Register.x22 == R) = false :=
  h.2.2.2.2.2.2.2.2.2.1
theorem NotWrittenJmp.x23 {R : Register} (h : NotWrittenJmp R) : (Register.x23 == R) = false :=
  h.2.2.2.2.2.2.2.2.2.2.1
theorem NotWrittenJmp.x24 {R : Register} (h : NotWrittenJmp R) : (Register.x24 == R) = false :=
  h.2.2.2.2.2.2.2.2.2.2.2.1
theorem NotWrittenJmp.x25 {R : Register} (h : NotWrittenJmp R) : (Register.x25 == R) = false :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem NotWrittenJmp.x26 {R : Register} (h : NotWrittenJmp R) : (Register.x26 == R) = false :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem NotWrittenJmp.x27 {R : Register} (h : NotWrittenJmp R) : (Register.x27 == R) = false :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Generic STORE frame step (no `rd`). -/
theorem frame_store_jmp {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) (R : Register)
    (hR : NotWrittenJmp R) : σ'.regs.get? R = σ.regs.get? R := by
  rw [hobs.1 R hR.mc hR.mt hR.mip]
  exact get?_sigmaPost_store σ pc vm m' R hR.mi hR.pc hR.npc hR.mii

/-- Generic `jr`/`ret` frame step. -/
theorem frame_jr_jmp {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register)
    (hR : NotWrittenJmp R) : σ'.regs.get? R = σ.regs.get? R := by
  rw [hobs.1 R hR.mc hR.mt hR.mip]
  exact get?_sigmaPost_jump_x0 σ pc vm tgt R hR.mi hR.pc hR.npc hR.mii

/-! ## `SetjmpLoaded` / `LongjmpLoaded` survive the buffer stores / a code-agreeing mem -/

/-- `SetjmpLoaded` survives an 8-byte `writeMap8` whose window `[a8, a8+8)` is
disjoint from the setjmp code `[0x80006ffc, 0x8000703c)`. -/
theorem loaded_setjmp_writeMap8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ 0x80006ffc ∨ 0x8000703c ≤ a8) (h : SetjmpLoaded mem) :
    SetjmpLoaded (writeMap8 mem a8 d) := by
  simp only [SetjmpLoaded, Vsa.Sim.Code.setjmpChunk0] at h ⊢
  repeat' apply And.intro
  all_goals (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])

/-! ## Pointer-offset helpers: `(jb + sext offX).toNat = jb.toNat + X` (no wrap) -/

theorem joff (base : BitVec 64) (off : BitVec 12) (X : Nat)
    (hoff : (sign_extend (m := 64) off : BitVec 64).toNat = X)
    (h : base.toNat + X < 2^64) :
    (base + sign_extend (m := 64) off).toNat = base.toNat + X := by
  rw [BitVec.toNat_add, hoff]; omega

/-! ## setjmp: the buffer write chain

`setjmpBuf m0 jb ra0 s0v s1v s2v .. s11v spv` is the exact 14-fold `writeMap8`
memory that setjmp produces from entry memory `m0`: the 14 callee-saved GPR values
placed at `jb+0, jb+8, .., jb+104`.  This is the load-bearing part of `Q`: it is
the buffer contents `longjmp` will later read back. -/
abbrev setjmpBuf (m0 : Std.ExtHashMap Nat (BitVec 8)) (jb : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64) :
    Std.ExtHashMap Nat (BitVec 8) :=
  writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8
  (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 m0
    (jb.toNat + 0)   (sdData_val ra0))
    (jb.toNat + 8)   (sdData_val s0v))
    (jb.toNat + 16)  (sdData_val s1v))
    (jb.toNat + 24)  (sdData_val s2v))
    (jb.toNat + 32)  (sdData_val s3v))
    (jb.toNat + 40)  (sdData_val s4v))
    (jb.toNat + 48)  (sdData_val s5v))
    (jb.toNat + 56)  (sdData_val s6v))
    (jb.toNat + 64)  (sdData_val s7v))
    (jb.toNat + 72)  (sdData_val s8v))
    (jb.toNat + 80)  (sdData_val s9v))
    (jb.toNat + 88)  (sdData_val s10v))
    (jb.toNat + 96)  (sdData_val s11v))
    (jb.toNat + 104) (sdData_val spv)

/-! ## `WinRAM jb`: the 112-byte buffer window is in usable RAM, above HTIF, aligned,
and disjoint from the setjmp/longjmp code text. -/
structure WinRAM (jb : BitVec 64) : Prop where
  lo : 0x80000000 ≤ jb.toNat
  hi : jb.toNat + 112 ≤ 0x100000000
  win : tohostAddr + 16 ≤ jb.toNat
  align : jb.toNat % 8 = 0
  /-- disjoint from setjmp code `[0x80006ffc, 0x8000703c)`. -/
  code_sj : jb.toNat + 112 ≤ 0x80006ffc ∨ 0x8000703c ≤ jb.toNat
  /-- disjoint from longjmp code `[0x8000703c, 0x80007080)`. -/
  code_lj : jb.toNat + 112 ≤ 0x8000703c ∨ 0x80007080 ≤ jb.toNat

/-! ## `setjmp_spec` -/

/-- `setjmp_pre`: entry at `0x80006ffc` with `a0 = jb` (the buffer address), the 14
live callee-saved GPRs held in `x1,x8,x9,x18..x27,x2`, code loaded, `mem = m0`,
`WinRAM jb`, ghost frame `g`, tick/minstret noise, and the caller's `ra`-target
`ra0` 4-aligned (so `ret` lands cleanly). -/
def setjmp_pre (g : (R : Register) → Option (RegisterType R)) (jb : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ SetjmpLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x80006ffc#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some jb ∧
  c.σ.regs.get? Register.x1 = some ra0 ∧ ra0.toNat % 4 = 0 ∧
  c.σ.regs.get? Register.x8 = some s0v ∧ c.σ.regs.get? Register.x9 = some s1v ∧
  c.σ.regs.get? Register.x18 = some s2v ∧ c.σ.regs.get? Register.x19 = some s3v ∧
  c.σ.regs.get? Register.x20 = some s4v ∧ c.σ.regs.get? Register.x21 = some s5v ∧
  c.σ.regs.get? Register.x22 = some s6v ∧ c.σ.regs.get? Register.x23 = some s7v ∧
  c.σ.regs.get? Register.x24 = some s8v ∧ c.σ.regs.get? Register.x25 = some s9v ∧
  c.σ.regs.get? Register.x26 = some s10v ∧ c.σ.regs.get? Register.x27 = some s11v ∧
  c.σ.regs.get? Register.x2 = some spv ∧
  WinRAM jb ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
  (∀ R : Register, NotWrittenJmp R → c.σ.regs.get? R = g R)

/-- `setjmp_post`: `PC = ra0` (exact `ret`), `a0 = 0` (initial passage), `mem` is the
buffer write chain `setjmpBuf …` (the 14 saved values at `jb+0..jb+104` — the
load-bearing part), and every register other than `x10`/`PC`/noise framed to `g`. -/
def setjmp_post (g : (R : Register) → Option (RegisterType R)) (jb : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some ra0 ∧
  c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧
  c.σ.mem = setjmpBuf m0 jb ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧
  (∀ R : Register, NotWrittenJmp R → c.σ.regs.get? R = g R)

/-- **`setjmp` total-correctness spec** (initial zero-return passage). -/
theorem setjmp_spec (g : (R : Register) → Option (RegisterType R)) (jb : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (setjmp_pre g jb ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
      (setjmp_post g jb ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0) := by
  intro c hpre
  obtain ⟨hG, hloaded, hmem, hpc, ha0, hra, hraA, hs0, hs1, hs2, hs3, hs4, hs5, hs6,
    hs7, hs8, hs9, hs10, hs11, hsp, hWin, ⟨vmi, hmi⟩, htick, hframe⟩ := hpre
  obtain ⟨hlo, hhi, hwin, halgn, hcsj, hclj⟩ := hWin
  have hj0 : (jb + sign_extend (m := 64) (0x000#12)).toNat = jb.toNat + 0 := by
    apply joff jb (0x000#12) 0
    · decide
    · omega
  have hj8 : (jb + sign_extend (m := 64) (0x008#12)).toNat = jb.toNat + 8 := by
    apply joff jb (0x008#12) 8
    · decide
    · omega
  have hj16 : (jb + sign_extend (m := 64) (0x010#12)).toNat = jb.toNat + 16 := by
    apply joff jb (0x010#12) 16
    · decide
    · omega
  have hj24 : (jb + sign_extend (m := 64) (0x018#12)).toNat = jb.toNat + 24 := by
    apply joff jb (0x018#12) 24
    · decide
    · omega
  have hj32 : (jb + sign_extend (m := 64) (0x020#12)).toNat = jb.toNat + 32 := by
    apply joff jb (0x020#12) 32
    · decide
    · omega
  have hj40 : (jb + sign_extend (m := 64) (0x028#12)).toNat = jb.toNat + 40 := by
    apply joff jb (0x028#12) 40
    · decide
    · omega
  have hj48 : (jb + sign_extend (m := 64) (0x030#12)).toNat = jb.toNat + 48 := by
    apply joff jb (0x030#12) 48
    · decide
    · omega
  have hj56 : (jb + sign_extend (m := 64) (0x038#12)).toNat = jb.toNat + 56 := by
    apply joff jb (0x038#12) 56
    · decide
    · omega
  have hj64 : (jb + sign_extend (m := 64) (0x040#12)).toNat = jb.toNat + 64 := by
    apply joff jb (0x040#12) 64
    · decide
    · omega
  have hj72 : (jb + sign_extend (m := 64) (0x048#12)).toNat = jb.toNat + 72 := by
    apply joff jb (0x048#12) 72
    · decide
    · omega
  have hj80 : (jb + sign_extend (m := 64) (0x050#12)).toNat = jb.toNat + 80 := by
    apply joff jb (0x050#12) 80
    · decide
    · omega
  have hj88 : (jb + sign_extend (m := 64) (0x058#12)).toNat = jb.toNat + 88 := by
    apply joff jb (0x058#12) 88
    · decide
    · omega
  have hj96 : (jb + sign_extend (m := 64) (0x060#12)).toNat = jb.toNat + 96 := by
    apply joff jb (0x060#12) 96
    · decide
    · omega
  have hj104 : (jb + sign_extend (m := 64) (0x068#12)).toNat = jb.toNat + 104 := by
    apply joff jb (0x068#12) 104
    · decide
    · omega
  obtain ⟨σ1, i1, hs_1, hi1, hG1, hmc1, hobs1⟩ :=
    site_80006ffc_jmp c.σ c.tick (c.steps) (0x80006ffc#64) vmi jb ra0
      hG hpc hmi ha0 hra hloaded rfl
      (by rw [hj0]; omega) (by rw [hj0]; omega) (by rw [hj0]; omega) (by rw [hj0]; omega) htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80007000#64 : BitVec 64) := by
    have := obs_store_pc_val hobs1
    rwa [show BitVec.addInt (0x80006ffc#64 : BitVec 64) 4 = (0x80007000#64 : BitVec 64) from by decide] at this
  have h_x10_1 := obs_store_other_val hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have h_x1_1 := obs_store_other_val hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have h_x8_1 := obs_store_other_val hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs0
  have h_x9_1 := obs_store_other_val hobs1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1
  have h_x18_1 := obs_store_other_val hobs1 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs2
  have h_x19_1 := obs_store_other_val hobs1 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs3
  have h_x20_1 := obs_store_other_val hobs1 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs4
  have h_x21_1 := obs_store_other_val hobs1 Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs5
  have h_x22_1 := obs_store_other_val hobs1 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs6
  have h_x23_1 := obs_store_other_val hobs1 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs7
  have h_x24_1 := obs_store_other_val hobs1 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs8
  have h_x25_1 := obs_store_other_val hobs1 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs9
  have h_x26_1 := obs_store_other_val hobs1 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs10
  have h_x27_1 := obs_store_other_val hobs1 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs11
  have h_x2_1 := obs_store_other_val hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp
  obtain ⟨vmi1, hmi1⟩ := obs_store_minstret_val hobs1
  have hmc1' : σ1.mem = writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0) := by
    rw [hmc1, mem_afterNextPC, hmem, hj0]
  have hload1 : SetjmpLoaded σ1.mem := by
    rw [hmc1']
    exact loaded_setjmp_writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)
      (by omega) (hmem ▸ hloaded)
  obtain ⟨σ2, i2, hs_2, hi2, hG2, hmc2, hobs2⟩ :=
    site_80007000_jmp σ1 i1 (c.steps + 1) (0x80007000#64) vmi1 jb s0v
      hG1 hpc1 hmi1 h_x10_1 h_x8_1 hload1 rfl
      (by rw [hj8]; omega) (by rw [hj8]; omega) (by rw [hj8]; omega) (by rw [hj8]; omega) hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80007004#64 : BitVec 64) := by
    have := obs_store_pc_val hobs2
    rwa [show BitVec.addInt (0x80007000#64 : BitVec 64) 4 = (0x80007004#64 : BitVec 64) from by decide] at this
  have h_x10_2 := obs_store_other_val hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_1
  have h_x1_2 := obs_store_other_val hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_1
  have h_x9_2 := obs_store_other_val hobs2 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x9_1
  have h_x18_2 := obs_store_other_val hobs2 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x18_1
  have h_x19_2 := obs_store_other_val hobs2 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x19_1
  have h_x20_2 := obs_store_other_val hobs2 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x20_1
  have h_x21_2 := obs_store_other_val hobs2 Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x21_1
  have h_x22_2 := obs_store_other_val hobs2 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x22_1
  have h_x23_2 := obs_store_other_val hobs2 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x23_1
  have h_x24_2 := obs_store_other_val hobs2 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x24_1
  have h_x25_2 := obs_store_other_val hobs2 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x25_1
  have h_x26_2 := obs_store_other_val hobs2 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x26_1
  have h_x27_2 := obs_store_other_val hobs2 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x27_1
  have h_x2_2 := obs_store_other_val hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x2_1
  obtain ⟨vmi2, hmi2⟩ := obs_store_minstret_val hobs2
  have hmc2' : σ2.mem = writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v) := by
    rw [hmc2, mem_afterNextPC, hmc1', hj8]
  have hload2 : SetjmpLoaded σ2.mem := by
    rw [hmc2']
    exact loaded_setjmp_writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)
      (by omega) (hmc1' ▸ hload1)
  obtain ⟨σ3, i3, hs_3, hi3, hG3, hmc3, hobs3⟩ :=
    site_80007004_jmp σ2 i2 (c.steps + 1 + 1) (0x80007004#64) vmi2 jb s1v
      hG2 hpc2 hmi2 h_x10_2 h_x9_2 hload2 rfl
      (by rw [hj16]; omega) (by rw [hj16]; omega) (by rw [hj16]; omega) (by rw [hj16]; omega) hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80007008#64 : BitVec 64) := by
    have := obs_store_pc_val hobs3
    rwa [show BitVec.addInt (0x80007004#64 : BitVec 64) 4 = (0x80007008#64 : BitVec 64) from by decide] at this
  have h_x10_3 := obs_store_other_val hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_2
  have h_x1_3 := obs_store_other_val hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_2
  have h_x18_3 := obs_store_other_val hobs3 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x18_2
  have h_x19_3 := obs_store_other_val hobs3 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x19_2
  have h_x20_3 := obs_store_other_val hobs3 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x20_2
  have h_x21_3 := obs_store_other_val hobs3 Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x21_2
  have h_x22_3 := obs_store_other_val hobs3 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x22_2
  have h_x23_3 := obs_store_other_val hobs3 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x23_2
  have h_x24_3 := obs_store_other_val hobs3 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x24_2
  have h_x25_3 := obs_store_other_val hobs3 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x25_2
  have h_x26_3 := obs_store_other_val hobs3 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x26_2
  have h_x27_3 := obs_store_other_val hobs3 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x27_2
  have h_x2_3 := obs_store_other_val hobs3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x2_2
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret_val hobs3
  have hmc3' : σ3.mem = writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v) := by
    rw [hmc3, mem_afterNextPC, hmc2', hj16]
  have hload3 : SetjmpLoaded σ3.mem := by
    rw [hmc3']
    exact loaded_setjmp_writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)
      (by omega) (hmc2' ▸ hload2)
  obtain ⟨σ4, i4, hs_4, hi4, hG4, hmc4, hobs4⟩ :=
    site_80007008_jmp σ3 i3 (c.steps + 1 + 1 + 1) (0x80007008#64) vmi3 jb s2v
      hG3 hpc3 hmi3 h_x10_3 h_x18_3 hload3 rfl
      (by rw [hj24]; omega) (by rw [hj24]; omega) (by rw [hj24]; omega) (by rw [hj24]; omega) hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x8000700c#64 : BitVec 64) := by
    have := obs_store_pc_val hobs4
    rwa [show BitVec.addInt (0x80007008#64 : BitVec 64) 4 = (0x8000700c#64 : BitVec 64) from by decide] at this
  have h_x10_4 := obs_store_other_val hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_3
  have h_x1_4 := obs_store_other_val hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_3
  have h_x19_4 := obs_store_other_val hobs4 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x19_3
  have h_x20_4 := obs_store_other_val hobs4 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x20_3
  have h_x21_4 := obs_store_other_val hobs4 Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x21_3
  have h_x22_4 := obs_store_other_val hobs4 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x22_3
  have h_x23_4 := obs_store_other_val hobs4 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x23_3
  have h_x24_4 := obs_store_other_val hobs4 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x24_3
  have h_x25_4 := obs_store_other_val hobs4 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x25_3
  have h_x26_4 := obs_store_other_val hobs4 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x26_3
  have h_x27_4 := obs_store_other_val hobs4 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x27_3
  have h_x2_4 := obs_store_other_val hobs4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x2_3
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret_val hobs4
  have hmc4' : σ4.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v) := by
    rw [hmc4, mem_afterNextPC, hmc3', hj24]
  have hload4 : SetjmpLoaded σ4.mem := by
    rw [hmc4']
    exact loaded_setjmp_writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)
      (by omega) (hmc3' ▸ hload3)
  obtain ⟨σ5, i5, hs_5, hi5, hG5, hmc5, hobs5⟩ :=
    site_8000700c_jmp σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x8000700c#64) vmi4 jb s3v
      hG4 hpc4 hmi4 h_x10_4 h_x19_4 hload4 rfl
      (by rw [hj32]; omega) (by rw [hj32]; omega) (by rw [hj32]; omega) (by rw [hj32]; omega) hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80007010#64 : BitVec 64) := by
    have := obs_store_pc_val hobs5
    rwa [show BitVec.addInt (0x8000700c#64 : BitVec 64) 4 = (0x80007010#64 : BitVec 64) from by decide] at this
  have h_x10_5 := obs_store_other_val hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_4
  have h_x1_5 := obs_store_other_val hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_4
  have h_x20_5 := obs_store_other_val hobs5 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x20_4
  have h_x21_5 := obs_store_other_val hobs5 Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x21_4
  have h_x22_5 := obs_store_other_val hobs5 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x22_4
  have h_x23_5 := obs_store_other_val hobs5 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x23_4
  have h_x24_5 := obs_store_other_val hobs5 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x24_4
  have h_x25_5 := obs_store_other_val hobs5 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x25_4
  have h_x26_5 := obs_store_other_val hobs5 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x26_4
  have h_x27_5 := obs_store_other_val hobs5 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x27_4
  have h_x2_5 := obs_store_other_val hobs5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x2_4
  obtain ⟨vmi5, hmi5⟩ := obs_store_minstret_val hobs5
  have hmc5' : σ5.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)) (jb.toNat + 32) (sdData_val s3v) := by
    rw [hmc5, mem_afterNextPC, hmc4', hj32]
  have hload5 : SetjmpLoaded σ5.mem := by
    rw [hmc5']
    exact loaded_setjmp_writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)) (jb.toNat + 32) (sdData_val s3v)
      (by omega) (hmc4' ▸ hload4)
  obtain ⟨σ6, i6, hs_6, hi6, hG6, hmc6, hobs6⟩ :=
    site_80007010_jmp σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80007010#64) vmi5 jb s4v
      hG5 hpc5 hmi5 h_x10_5 h_x20_5 hload5 rfl
      (by rw [hj40]; omega) (by rw [hj40]; omega) (by rw [hj40]; omega) (by rw [hj40]; omega) hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x80007014#64 : BitVec 64) := by
    have := obs_store_pc_val hobs6
    rwa [show BitVec.addInt (0x80007010#64 : BitVec 64) 4 = (0x80007014#64 : BitVec 64) from by decide] at this
  have h_x10_6 := obs_store_other_val hobs6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_5
  have h_x1_6 := obs_store_other_val hobs6 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_5
  have h_x21_6 := obs_store_other_val hobs6 Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x21_5
  have h_x22_6 := obs_store_other_val hobs6 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x22_5
  have h_x23_6 := obs_store_other_val hobs6 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x23_5
  have h_x24_6 := obs_store_other_val hobs6 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x24_5
  have h_x25_6 := obs_store_other_val hobs6 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x25_5
  have h_x26_6 := obs_store_other_val hobs6 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x26_5
  have h_x27_6 := obs_store_other_val hobs6 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x27_5
  have h_x2_6 := obs_store_other_val hobs6 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x2_5
  obtain ⟨vmi6, hmi6⟩ := obs_store_minstret_val hobs6
  have hmc6' : σ6.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)) (jb.toNat + 32) (sdData_val s3v)) (jb.toNat + 40) (sdData_val s4v) := by
    rw [hmc6, mem_afterNextPC, hmc5', hj40]
  have hload6 : SetjmpLoaded σ6.mem := by
    rw [hmc6']
    exact loaded_setjmp_writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)) (jb.toNat + 32) (sdData_val s3v)) (jb.toNat + 40) (sdData_val s4v)
      (by omega) (hmc5' ▸ hload5)
  obtain ⟨σ7, i7, hs_7, hi7, hG7, hmc7, hobs7⟩ :=
    site_80007014_jmp σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80007014#64) vmi6 jb s5v
      hG6 hpc6 hmi6 h_x10_6 h_x21_6 hload6 rfl
      (by rw [hj48]; omega) (by rw [hj48]; omega) (by rw [hj48]; omega) (by rw [hj48]; omega) hi6
  have hpc7 : σ7.regs.get? Register.PC = some (0x80007018#64 : BitVec 64) := by
    have := obs_store_pc_val hobs7
    rwa [show BitVec.addInt (0x80007014#64 : BitVec 64) 4 = (0x80007018#64 : BitVec 64) from by decide] at this
  have h_x10_7 := obs_store_other_val hobs7 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_6
  have h_x1_7 := obs_store_other_val hobs7 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_6
  have h_x22_7 := obs_store_other_val hobs7 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x22_6
  have h_x23_7 := obs_store_other_val hobs7 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x23_6
  have h_x24_7 := obs_store_other_val hobs7 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x24_6
  have h_x25_7 := obs_store_other_val hobs7 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x25_6
  have h_x26_7 := obs_store_other_val hobs7 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x26_6
  have h_x27_7 := obs_store_other_val hobs7 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x27_6
  have h_x2_7 := obs_store_other_val hobs7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x2_6
  obtain ⟨vmi7, hmi7⟩ := obs_store_minstret_val hobs7
  have hmc7' : σ7.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)) (jb.toNat + 32) (sdData_val s3v)) (jb.toNat + 40) (sdData_val s4v)) (jb.toNat + 48) (sdData_val s5v) := by
    rw [hmc7, mem_afterNextPC, hmc6', hj48]
  have hload7 : SetjmpLoaded σ7.mem := by
    rw [hmc7']
    exact loaded_setjmp_writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)) (jb.toNat + 32) (sdData_val s3v)) (jb.toNat + 40) (sdData_val s4v)) (jb.toNat + 48) (sdData_val s5v)
      (by omega) (hmc6' ▸ hload6)
  obtain ⟨σ8, i8, hs_8, hi8, hG8, hmc8, hobs8⟩ :=
    site_80007018_jmp σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007018#64) vmi7 jb s6v
      hG7 hpc7 hmi7 h_x10_7 h_x22_7 hload7 rfl
      (by rw [hj56]; omega) (by rw [hj56]; omega) (by rw [hj56]; omega) (by rw [hj56]; omega) hi7
  have hpc8 : σ8.regs.get? Register.PC = some (0x8000701c#64 : BitVec 64) := by
    have := obs_store_pc_val hobs8
    rwa [show BitVec.addInt (0x80007018#64 : BitVec 64) 4 = (0x8000701c#64 : BitVec 64) from by decide] at this
  have h_x10_8 := obs_store_other_val hobs8 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_7
  have h_x1_8 := obs_store_other_val hobs8 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_7
  have h_x23_8 := obs_store_other_val hobs8 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x23_7
  have h_x24_8 := obs_store_other_val hobs8 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x24_7
  have h_x25_8 := obs_store_other_val hobs8 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x25_7
  have h_x26_8 := obs_store_other_val hobs8 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x26_7
  have h_x27_8 := obs_store_other_val hobs8 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x27_7
  have h_x2_8 := obs_store_other_val hobs8 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x2_7
  obtain ⟨vmi8, hmi8⟩ := obs_store_minstret_val hobs8
  have hmc8' : σ8.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)) (jb.toNat + 32) (sdData_val s3v)) (jb.toNat + 40) (sdData_val s4v)) (jb.toNat + 48) (sdData_val s5v)) (jb.toNat + 56) (sdData_val s6v) := by
    rw [hmc8, mem_afterNextPC, hmc7', hj56]
  have hload8 : SetjmpLoaded σ8.mem := by
    rw [hmc8']
    exact loaded_setjmp_writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)) (jb.toNat + 32) (sdData_val s3v)) (jb.toNat + 40) (sdData_val s4v)) (jb.toNat + 48) (sdData_val s5v)) (jb.toNat + 56) (sdData_val s6v)
      (by omega) (hmc7' ▸ hload7)
  obtain ⟨σ9, i9, hs_9, hi9, hG9, hmc9, hobs9⟩ :=
    site_8000701c_jmp σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000701c#64) vmi8 jb s7v
      hG8 hpc8 hmi8 h_x10_8 h_x23_8 hload8 rfl
      (by rw [hj64]; omega) (by rw [hj64]; omega) (by rw [hj64]; omega) (by rw [hj64]; omega) hi8
  have hpc9 : σ9.regs.get? Register.PC = some (0x80007020#64 : BitVec 64) := by
    have := obs_store_pc_val hobs9
    rwa [show BitVec.addInt (0x8000701c#64 : BitVec 64) 4 = (0x80007020#64 : BitVec 64) from by decide] at this
  have h_x10_9 := obs_store_other_val hobs9 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_8
  have h_x1_9 := obs_store_other_val hobs9 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_8
  have h_x24_9 := obs_store_other_val hobs9 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x24_8
  have h_x25_9 := obs_store_other_val hobs9 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x25_8
  have h_x26_9 := obs_store_other_val hobs9 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x26_8
  have h_x27_9 := obs_store_other_val hobs9 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x27_8
  have h_x2_9 := obs_store_other_val hobs9 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x2_8
  obtain ⟨vmi9, hmi9⟩ := obs_store_minstret_val hobs9
  have hmc9' : σ9.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)) (jb.toNat + 32) (sdData_val s3v)) (jb.toNat + 40) (sdData_val s4v)) (jb.toNat + 48) (sdData_val s5v)) (jb.toNat + 56) (sdData_val s6v)) (jb.toNat + 64) (sdData_val s7v) := by
    rw [hmc9, mem_afterNextPC, hmc8', hj64]
  have hload9 : SetjmpLoaded σ9.mem := by
    rw [hmc9']
    exact loaded_setjmp_writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)) (jb.toNat + 32) (sdData_val s3v)) (jb.toNat + 40) (sdData_val s4v)) (jb.toNat + 48) (sdData_val s5v)) (jb.toNat + 56) (sdData_val s6v)) (jb.toNat + 64) (sdData_val s7v)
      (by omega) (hmc8' ▸ hload8)
  obtain ⟨σ10, i10, hs_10, hi10, hG10, hmc10, hobs10⟩ :=
    site_80007020_jmp σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007020#64) vmi9 jb s8v
      hG9 hpc9 hmi9 h_x10_9 h_x24_9 hload9 rfl
      (by rw [hj72]; omega) (by rw [hj72]; omega) (by rw [hj72]; omega) (by rw [hj72]; omega) hi9
  have hpc10 : σ10.regs.get? Register.PC = some (0x80007024#64 : BitVec 64) := by
    have := obs_store_pc_val hobs10
    rwa [show BitVec.addInt (0x80007020#64 : BitVec 64) 4 = (0x80007024#64 : BitVec 64) from by decide] at this
  have h_x10_10 := obs_store_other_val hobs10 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_9
  have h_x1_10 := obs_store_other_val hobs10 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_9
  have h_x25_10 := obs_store_other_val hobs10 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x25_9
  have h_x26_10 := obs_store_other_val hobs10 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x26_9
  have h_x27_10 := obs_store_other_val hobs10 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x27_9
  have h_x2_10 := obs_store_other_val hobs10 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x2_9
  obtain ⟨vmi10, hmi10⟩ := obs_store_minstret_val hobs10
  have hmc10' : σ10.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)) (jb.toNat + 32) (sdData_val s3v)) (jb.toNat + 40) (sdData_val s4v)) (jb.toNat + 48) (sdData_val s5v)) (jb.toNat + 56) (sdData_val s6v)) (jb.toNat + 64) (sdData_val s7v)) (jb.toNat + 72) (sdData_val s8v) := by
    rw [hmc10, mem_afterNextPC, hmc9', hj72]
  have hload10 : SetjmpLoaded σ10.mem := by
    rw [hmc10']
    exact loaded_setjmp_writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)) (jb.toNat + 32) (sdData_val s3v)) (jb.toNat + 40) (sdData_val s4v)) (jb.toNat + 48) (sdData_val s5v)) (jb.toNat + 56) (sdData_val s6v)) (jb.toNat + 64) (sdData_val s7v)) (jb.toNat + 72) (sdData_val s8v)
      (by omega) (hmc9' ▸ hload9)
  obtain ⟨σ11, i11, hs_11, hi11, hG11, hmc11, hobs11⟩ :=
    site_80007024_jmp σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007024#64) vmi10 jb s9v
      hG10 hpc10 hmi10 h_x10_10 h_x25_10 hload10 rfl
      (by rw [hj80]; omega) (by rw [hj80]; omega) (by rw [hj80]; omega) (by rw [hj80]; omega) hi10
  have hpc11 : σ11.regs.get? Register.PC = some (0x80007028#64 : BitVec 64) := by
    have := obs_store_pc_val hobs11
    rwa [show BitVec.addInt (0x80007024#64 : BitVec 64) 4 = (0x80007028#64 : BitVec 64) from by decide] at this
  have h_x10_11 := obs_store_other_val hobs11 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_10
  have h_x1_11 := obs_store_other_val hobs11 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_10
  have h_x26_11 := obs_store_other_val hobs11 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x26_10
  have h_x27_11 := obs_store_other_val hobs11 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x27_10
  have h_x2_11 := obs_store_other_val hobs11 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x2_10
  obtain ⟨vmi11, hmi11⟩ := obs_store_minstret_val hobs11
  have hmc11' : σ11.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)) (jb.toNat + 32) (sdData_val s3v)) (jb.toNat + 40) (sdData_val s4v)) (jb.toNat + 48) (sdData_val s5v)) (jb.toNat + 56) (sdData_val s6v)) (jb.toNat + 64) (sdData_val s7v)) (jb.toNat + 72) (sdData_val s8v)) (jb.toNat + 80) (sdData_val s9v) := by
    rw [hmc11, mem_afterNextPC, hmc10', hj80]
  have hload11 : SetjmpLoaded σ11.mem := by
    rw [hmc11']
    exact loaded_setjmp_writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)) (jb.toNat + 32) (sdData_val s3v)) (jb.toNat + 40) (sdData_val s4v)) (jb.toNat + 48) (sdData_val s5v)) (jb.toNat + 56) (sdData_val s6v)) (jb.toNat + 64) (sdData_val s7v)) (jb.toNat + 72) (sdData_val s8v)) (jb.toNat + 80) (sdData_val s9v)
      (by omega) (hmc10' ▸ hload10)
  obtain ⟨σ12, i12, hs_12, hi12, hG12, hmc12, hobs12⟩ :=
    site_80007028_jmp σ11 i11 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007028#64) vmi11 jb s10v
      hG11 hpc11 hmi11 h_x10_11 h_x26_11 hload11 rfl
      (by rw [hj88]; omega) (by rw [hj88]; omega) (by rw [hj88]; omega) (by rw [hj88]; omega) hi11
  have hpc12 : σ12.regs.get? Register.PC = some (0x8000702c#64 : BitVec 64) := by
    have := obs_store_pc_val hobs12
    rwa [show BitVec.addInt (0x80007028#64 : BitVec 64) 4 = (0x8000702c#64 : BitVec 64) from by decide] at this
  have h_x10_12 := obs_store_other_val hobs12 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_11
  have h_x1_12 := obs_store_other_val hobs12 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_11
  have h_x27_12 := obs_store_other_val hobs12 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x27_11
  have h_x2_12 := obs_store_other_val hobs12 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x2_11
  obtain ⟨vmi12, hmi12⟩ := obs_store_minstret_val hobs12
  have hmc12' : σ12.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)) (jb.toNat + 32) (sdData_val s3v)) (jb.toNat + 40) (sdData_val s4v)) (jb.toNat + 48) (sdData_val s5v)) (jb.toNat + 56) (sdData_val s6v)) (jb.toNat + 64) (sdData_val s7v)) (jb.toNat + 72) (sdData_val s8v)) (jb.toNat + 80) (sdData_val s9v)) (jb.toNat + 88) (sdData_val s10v) := by
    rw [hmc12, mem_afterNextPC, hmc11', hj88]
  have hload12 : SetjmpLoaded σ12.mem := by
    rw [hmc12']
    exact loaded_setjmp_writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)) (jb.toNat + 32) (sdData_val s3v)) (jb.toNat + 40) (sdData_val s4v)) (jb.toNat + 48) (sdData_val s5v)) (jb.toNat + 56) (sdData_val s6v)) (jb.toNat + 64) (sdData_val s7v)) (jb.toNat + 72) (sdData_val s8v)) (jb.toNat + 80) (sdData_val s9v)) (jb.toNat + 88) (sdData_val s10v)
      (by omega) (hmc11' ▸ hload11)
  obtain ⟨σ13, i13, hs_13, hi13, hG13, hmc13, hobs13⟩ :=
    site_8000702c_jmp σ12 i12 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000702c#64) vmi12 jb s11v
      hG12 hpc12 hmi12 h_x10_12 h_x27_12 hload12 rfl
      (by rw [hj96]; omega) (by rw [hj96]; omega) (by rw [hj96]; omega) (by rw [hj96]; omega) hi12
  have hpc13 : σ13.regs.get? Register.PC = some (0x80007030#64 : BitVec 64) := by
    have := obs_store_pc_val hobs13
    rwa [show BitVec.addInt (0x8000702c#64 : BitVec 64) 4 = (0x80007030#64 : BitVec 64) from by decide] at this
  have h_x10_13 := obs_store_other_val hobs13 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_12
  have h_x1_13 := obs_store_other_val hobs13 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_12
  have h_x2_13 := obs_store_other_val hobs13 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x2_12
  obtain ⟨vmi13, hmi13⟩ := obs_store_minstret_val hobs13
  have hmc13' : σ13.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)) (jb.toNat + 32) (sdData_val s3v)) (jb.toNat + 40) (sdData_val s4v)) (jb.toNat + 48) (sdData_val s5v)) (jb.toNat + 56) (sdData_val s6v)) (jb.toNat + 64) (sdData_val s7v)) (jb.toNat + 72) (sdData_val s8v)) (jb.toNat + 80) (sdData_val s9v)) (jb.toNat + 88) (sdData_val s10v)) (jb.toNat + 96) (sdData_val s11v) := by
    rw [hmc13, mem_afterNextPC, hmc12', hj96]
  have hload13 : SetjmpLoaded σ13.mem := by
    rw [hmc13']
    exact loaded_setjmp_writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)) (jb.toNat + 32) (sdData_val s3v)) (jb.toNat + 40) (sdData_val s4v)) (jb.toNat + 48) (sdData_val s5v)) (jb.toNat + 56) (sdData_val s6v)) (jb.toNat + 64) (sdData_val s7v)) (jb.toNat + 72) (sdData_val s8v)) (jb.toNat + 80) (sdData_val s9v)) (jb.toNat + 88) (sdData_val s10v)) (jb.toNat + 96) (sdData_val s11v)
      (by omega) (hmc12' ▸ hload12)
  obtain ⟨σ14, i14, hs_14, hi14, hG14, hmc14, hobs14⟩ :=
    site_80007030_jmp σ13 i13 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007030#64) vmi13 jb spv
      hG13 hpc13 hmi13 h_x10_13 h_x2_13 hload13 rfl
      (by rw [hj104]; omega) (by rw [hj104]; omega) (by rw [hj104]; omega) (by rw [hj104]; omega) hi13
  have hpc14 : σ14.regs.get? Register.PC = some (0x80007034#64 : BitVec 64) := by
    have := obs_store_pc_val hobs14
    rwa [show BitVec.addInt (0x80007030#64 : BitVec 64) 4 = (0x80007034#64 : BitVec 64) from by decide] at this
  have h_x10_14 := obs_store_other_val hobs14 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_13
  have h_x1_14 := obs_store_other_val hobs14 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_13
  obtain ⟨vmi14, hmi14⟩ := obs_store_minstret_val hobs14
  have hmc14' : σ14.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)) (jb.toNat + 32) (sdData_val s3v)) (jb.toNat + 40) (sdData_val s4v)) (jb.toNat + 48) (sdData_val s5v)) (jb.toNat + 56) (sdData_val s6v)) (jb.toNat + 64) (sdData_val s7v)) (jb.toNat + 72) (sdData_val s8v)) (jb.toNat + 80) (sdData_val s9v)) (jb.toNat + 88) (sdData_val s10v)) (jb.toNat + 96) (sdData_val s11v)) (jb.toNat + 104) (sdData_val spv) := by
    rw [hmc14, mem_afterNextPC, hmc13', hj104]
  have hload14 : SetjmpLoaded σ14.mem := by
    rw [hmc14']
    exact loaded_setjmp_writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m0) (jb.toNat + 0) (sdData_val ra0)) (jb.toNat + 8) (sdData_val s0v)) (jb.toNat + 16) (sdData_val s1v)) (jb.toNat + 24) (sdData_val s2v)) (jb.toNat + 32) (sdData_val s3v)) (jb.toNat + 40) (sdData_val s4v)) (jb.toNat + 48) (sdData_val s5v)) (jb.toNat + 56) (sdData_val s6v)) (jb.toNat + 64) (sdData_val s7v)) (jb.toNat + 72) (sdData_val s8v)) (jb.toNat + 80) (sdData_val s9v)) (jb.toNat + 88) (sdData_val s10v)) (jb.toNat + 96) (sdData_val s11v)) (jb.toNat + 104) (sdData_val spv)
      (by omega) (hmc13' ▸ hload13)
  obtain ⟨σ15, i15, hs_15, hi15, hG15, hmc15, hobs15⟩ :=
    site_80007034_jmp σ14 i14 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007034#64) vmi14 hG14 hpc14 hmi14 hload14 rfl hi14
  have hpc15 : σ15.regs.get? Register.PC = some (0x80007038#64 : BitVec 64) := by
    have := obs_alu_pc hobs15
    rwa [show BitVec.addInt (0x80007034#64 : BitVec 64) 4 = (0x80007038#64 : BitVec 64) from by decide] at this
  have ha0_15 : σ15.regs.get? Register.x10 = some (0#64 : BitVec 64) := by
    have := obs_alu_rd hobs15 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) + sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hra_15 := obs_alu_other hobs15 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_14
  obtain ⟨vmi15, hmi15⟩ := obs_alu_minstret hobs15
  have hmc15' : σ15.mem = σ14.mem := hmc15
  have hload15 : SetjmpLoaded σ15.mem := hmc15' ▸ hload14
  have hret_tgt : (BitVec.update (ra0 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt ra0 hraA]; exact hraA
  obtain ⟨σ16, i16, hs_16, hi16, hG16, hmc16, hobs16⟩ :=
    site_80007038_jmp σ15 i15 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007038#64) vmi15 ra0 hG15 hpc15 hmi15 hra_15 hload15 rfl hret_tgt hi15
  have hpc16 : σ16.regs.get? Register.PC = some ra0 := by
    have := obs_jr_pc hobs16
    rwa [ret_tgt ra0 hraA] at this
  have ha0_16 := obs_jr_other hobs16 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_15
  obtain ⟨vmi16, hmi16⟩ := obs_jr_minstret hobs16
  have hmc16' : σ16.mem = σ14.mem := by rw [hmc16, hmc15']
  refine ⟨⟨σ16, i16, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, ?_, ?_⟩
  · have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs_1
    exact Steps.trans (Steps.single hstep1) (Steps.trans (Steps.single hs_2) (Steps.trans (Steps.single hs_3)
      (Steps.trans (Steps.single hs_4) (Steps.trans (Steps.single hs_5) (Steps.trans (Steps.single hs_6)
      (Steps.trans (Steps.single hs_7) (Steps.trans (Steps.single hs_8) (Steps.trans (Steps.single hs_9)
      (Steps.trans (Steps.single hs_10) (Steps.trans (Steps.single hs_11) (Steps.trans (Steps.single hs_12)
      (Steps.trans (Steps.single hs_13) (Steps.trans (Steps.single hs_14) (Steps.trans (Steps.single hs_15)
      (Steps.single hs_16)))))))))))))))
  · refine ⟨hG16, hi16, hpc16, ha0_16, ?_, ⟨vmi16, hmi16⟩, ?_⟩
    · rw [hmc16', hmc14']
    · intro R hR
      rw [frame_jr_jmp hobs16 R hR]
      rw [frame_alu_jmp hobs15 R hR.x10 hR]
      rw [frame_store_jmp hobs14 R hR]
      rw [frame_store_jmp hobs13 R hR]
      rw [frame_store_jmp hobs12 R hR]
      rw [frame_store_jmp hobs11 R hR]
      rw [frame_store_jmp hobs10 R hR]
      rw [frame_store_jmp hobs9 R hR]
      rw [frame_store_jmp hobs8 R hR]
      rw [frame_store_jmp hobs7 R hR]
      rw [frame_store_jmp hobs6 R hR]
      rw [frame_store_jmp hobs5 R hR]
      rw [frame_store_jmp hobs4 R hR]
      rw [frame_store_jmp hobs3 R hR]
      rw [frame_store_jmp hobs2 R hR]
      rw [frame_store_jmp hobs1 R hR]
      exact hframe R hR

/-! ## longjmp: `read64` → 8 bytes + loaded-value identity

`longjmp` performs no stores, so every `ld` reads from the pinned entry memory `m0`.
`ld_readback_jmp` turns a `read64 m0 addr = some v.toNat` buffer fact into the 8
byte hypotheses the `ld` site consumes together with the fact that the site's loaded
value `sign_extend (assembled bytes)` equals `v`. -/
theorem sext64_id_jmp (d : BitVec (8 * 8)) : (sign_extend (m := 64) d : BitVec 64) = d := by
  simp only [sign_extend, Sail.BitVec.signExtend]
  exact BitVec.signExtend_eq d

theorem ld_readback_jmp (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec 64)
    (h : read64 m a = some v.toNat) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8,
      m[a]? = some b0 ∧ m[a + 1]? = some b1 ∧ m[a + 2]? = some b2 ∧ m[a + 3]? = some b3 ∧
      m[a + 4]? = some b4 ∧ m[a + 5]? = some b5 ∧ m[a + 6]? = some b6 ∧ m[a + 7]? = some b7 ∧
      (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8)) : BitVec 64) = v := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, e0, e1, e2, e3, e4, e5, e6, e7, hsum⟩ :=
    read64_bytes m a v.toNat h
  refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, e0, e1, e2, e3, e4, e5, e6, e7, ?_⟩
  rw [sext64_id_jmp]
  apply BitVec.eq_of_toNat_eq
  rw [word8_toNat_recon, hsum]

/-! ## `longjmp_spec` -/

/-- `longjmp_pre`: entry at `0x8000703c` with `a0 = jb`, `a1 = v`, code loaded,
`mem = m0`, `WinRAM jb`, and the **15 buffer contents as `read64` facts** (per the
brief: state P with the read64 facts, not a history) — `ra0` at `jb+0`, `s0v..s11v`
at `jb+8..96`, `spv` at `jb+104`.  `ra0` is the restored return target (4-aligned).
The ghost frame `g` ties untouched registers. -/
def longjmp_pre (g : (R : Register) → Option (RegisterType R)) (jb v : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ LongjmpLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x8000703c#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some jb ∧
  c.σ.regs.get? Register.x11 = some v ∧
  ra0.toNat % 4 = 0 ∧
  WinRAM jb ∧
  read64 m0 (jb.toNat + 0)   = some ra0.toNat ∧
  read64 m0 (jb.toNat + 8)   = some s0v.toNat ∧
  read64 m0 (jb.toNat + 16)  = some s1v.toNat ∧
  read64 m0 (jb.toNat + 24)  = some s2v.toNat ∧
  read64 m0 (jb.toNat + 32)  = some s3v.toNat ∧
  read64 m0 (jb.toNat + 40)  = some s4v.toNat ∧
  read64 m0 (jb.toNat + 48)  = some s5v.toNat ∧
  read64 m0 (jb.toNat + 56)  = some s6v.toNat ∧
  read64 m0 (jb.toNat + 64)  = some s7v.toNat ∧
  read64 m0 (jb.toNat + 72)  = some s8v.toNat ∧
  read64 m0 (jb.toNat + 80)  = some s9v.toNat ∧
  read64 m0 (jb.toNat + 88)  = some s10v.toNat ∧
  read64 m0 (jb.toNat + 96)  = some s11v.toNat ∧
  read64 m0 (jb.toNat + 104) = some spv.toNat ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧ c.tick < 2 ∧
  (∀ R : Register, NotWrittenJmp R → c.σ.regs.get? R = g R)

/-- `longjmp_post`: `PC = ra0` (ret to restored ra), callee-saved registers restored
to the buffer contents (`x1 = ra0, x8 = s0v, .., x27 = s11v, x2 = spv`), `a0`
materialized to `(v==0 ? 1 : v)`, memory unchanged (`= m0`), and every other
register framed to `g`. -/
def longjmp_post (g : (R : Register) → Option (RegisterType R)) (jb v : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some ra0 ∧
  c.σ.regs.get? Register.x1 = some ra0 ∧
  c.σ.regs.get? Register.x8 = some s0v ∧ c.σ.regs.get? Register.x9 = some s1v ∧
  c.σ.regs.get? Register.x18 = some s2v ∧ c.σ.regs.get? Register.x19 = some s3v ∧
  c.σ.regs.get? Register.x20 = some s4v ∧ c.σ.regs.get? Register.x21 = some s5v ∧
  c.σ.regs.get? Register.x22 = some s6v ∧ c.σ.regs.get? Register.x23 = some s7v ∧
  c.σ.regs.get? Register.x24 = some s8v ∧ c.σ.regs.get? Register.x25 = some s9v ∧
  c.σ.regs.get? Register.x26 = some s10v ∧ c.σ.regs.get? Register.x27 = some s11v ∧
  c.σ.regs.get? Register.x2 = some spv ∧
  c.σ.regs.get? Register.x10 = some (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v (sign_extend (m := 64) (0x001#12)))) + v) ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
  (∀ R : Register, NotWrittenJmp R → c.σ.regs.get? R = g R)

/-- **`longjmp` total-correctness spec.** -/
theorem longjmp_spec (g : (R : Register) → Option (RegisterType R)) (jb v : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (longjmp_pre g jb v ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0)
      (longjmp_post g jb v ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0) := by
  intro c hpre
  obtain ⟨hG, hloaded, hmem, hpc, ha0, ha1, hraA, hWin,
    hr0, hr8, hr16, hr24, hr32, hr40, hr48, hr56, hr64, hr72, hr80, hr88, hr96, hr104,
    ⟨vmi, hmi⟩, htick, hframe⟩ := hpre
  obtain ⟨hlo, hhi, hwin, halgn, hcsj, hclj⟩ := hWin
  have hj0 : (jb + sign_extend (m := 64) (0x000#12)).toNat = jb.toNat + 0 := by
    apply joff jb (0x000#12) 0
    · decide
    · omega
  have hj8 : (jb + sign_extend (m := 64) (0x008#12)).toNat = jb.toNat + 8 := by
    apply joff jb (0x008#12) 8
    · decide
    · omega
  have hj16 : (jb + sign_extend (m := 64) (0x010#12)).toNat = jb.toNat + 16 := by
    apply joff jb (0x010#12) 16
    · decide
    · omega
  have hj24 : (jb + sign_extend (m := 64) (0x018#12)).toNat = jb.toNat + 24 := by
    apply joff jb (0x018#12) 24
    · decide
    · omega
  have hj32 : (jb + sign_extend (m := 64) (0x020#12)).toNat = jb.toNat + 32 := by
    apply joff jb (0x020#12) 32
    · decide
    · omega
  have hj40 : (jb + sign_extend (m := 64) (0x028#12)).toNat = jb.toNat + 40 := by
    apply joff jb (0x028#12) 40
    · decide
    · omega
  have hj48 : (jb + sign_extend (m := 64) (0x030#12)).toNat = jb.toNat + 48 := by
    apply joff jb (0x030#12) 48
    · decide
    · omega
  have hj56 : (jb + sign_extend (m := 64) (0x038#12)).toNat = jb.toNat + 56 := by
    apply joff jb (0x038#12) 56
    · decide
    · omega
  have hj64 : (jb + sign_extend (m := 64) (0x040#12)).toNat = jb.toNat + 64 := by
    apply joff jb (0x040#12) 64
    · decide
    · omega
  have hj72 : (jb + sign_extend (m := 64) (0x048#12)).toNat = jb.toNat + 72 := by
    apply joff jb (0x048#12) 72
    · decide
    · omega
  have hj80 : (jb + sign_extend (m := 64) (0x050#12)).toNat = jb.toNat + 80 := by
    apply joff jb (0x050#12) 80
    · decide
    · omega
  have hj88 : (jb + sign_extend (m := 64) (0x058#12)).toNat = jb.toNat + 88 := by
    apply joff jb (0x058#12) 88
    · decide
    · omega
  have hj96 : (jb + sign_extend (m := 64) (0x060#12)).toNat = jb.toNat + 96 := by
    apply joff jb (0x060#12) 96
    · decide
    · omega
  have hj104 : (jb + sign_extend (m := 64) (0x068#12)).toNat = jb.toNat + 104 := by
    apply joff jb (0x068#12) 104
    · decide
    · omega
  -- === 0x8000703c: ld x1,0(a0) ===
  obtain ⟨lb0_1, lb1_1, lb2_1, lb3_1, lb4_1, lb5_1, lb6_1, lb7_1,
    le0_1, le1_1, le2_1, le3_1, le4_1, le5_1, le6_1, le7_1, hval_1⟩ :=
    ld_readback_jmp m0 (jb.toNat + 0) ra0 hr0
  obtain ⟨σ1, i1, hs_1, hi1, hG1, hmc1, hobs1⟩ :=
    site_8000703c_jmp c.σ c.tick (c.steps) (0x8000703c#64) vmi jb
      lb0_1 lb1_1 lb2_1 lb3_1 lb4_1 lb5_1 lb6_1 lb7_1
      hG hpc hmi ha0 hloaded rfl
      (by rw [hj0]; omega) (by rw [hj0]; omega)
      (by rw [hj0]; omega) (by rw [hj0]; omega)
      (by rw [hj0, hmem]; exact le0_1)
      (by rw [hj0, hmem]; exact le1_1)
      (by rw [hj0, hmem]; exact le2_1)
      (by rw [hj0, hmem]; exact le3_1)
      (by rw [hj0, hmem]; exact le4_1)
      (by rw [hj0, hmem]; exact le5_1)
      (by rw [hj0, hmem]; exact le6_1)
      (by rw [hj0, hmem]; exact le7_1) htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80007040#64 : BitVec 64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000703c#64 : BitVec 64) 4 = (0x80007040#64 : BitVec 64) from by decide] at this
  have hset_1 : σ1.regs.get? Register.x1 = some ra0 := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hval_1] at this
  have h_x10_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have h_x11_1 := obs_alu_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hmc1' : σ1.mem = m0 := by rw [hmc1, hmem]
  have hload1 : LongjmpLoaded σ1.mem := hmc1' ▸ (hmem ▸ hloaded)
  -- === 0x80007040: ld x8,8(a0) ===
  obtain ⟨lb0_2, lb1_2, lb2_2, lb3_2, lb4_2, lb5_2, lb6_2, lb7_2,
    le0_2, le1_2, le2_2, le3_2, le4_2, le5_2, le6_2, le7_2, hval_2⟩ :=
    ld_readback_jmp m0 (jb.toNat + 8) s0v hr8
  obtain ⟨σ2, i2, hs_2, hi2, hG2, hmc2, hobs2⟩ :=
    site_80007040_jmp σ1 i1 (c.steps + 1) (0x80007040#64) vmi1 jb
      lb0_2 lb1_2 lb2_2 lb3_2 lb4_2 lb5_2 lb6_2 lb7_2
      hG1 hpc1 hmi1 h_x10_1 hload1 rfl
      (by rw [hj8]; omega) (by rw [hj8]; omega)
      (by rw [hj8]; omega) (by rw [hj8]; omega)
      (by rw [hj8, hmc1']; exact le0_2)
      (by rw [hj8, hmc1']; exact le1_2)
      (by rw [hj8, hmc1']; exact le2_2)
      (by rw [hj8, hmc1']; exact le3_2)
      (by rw [hj8, hmc1']; exact le4_2)
      (by rw [hj8, hmc1']; exact le5_2)
      (by rw [hj8, hmc1']; exact le6_2)
      (by rw [hj8, hmc1']; exact le7_2) hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80007044#64 : BitVec 64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80007040#64 : BitVec 64) 4 = (0x80007044#64 : BitVec 64) from by decide] at this
  have hset_2 : σ2.regs.get? Register.x8 = some s0v := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hval_2] at this
  have h_x1_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hset_1
  have h_x10_2 := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_1
  have h_x11_2 := obs_alu_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x11_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hmc2' : σ2.mem = m0 := by rw [hmc2, hmc1']
  have hload2 : LongjmpLoaded σ2.mem := hmc2' ▸ (hmem ▸ hloaded)
  -- === 0x80007044: ld x9,16(a0) ===
  obtain ⟨lb0_3, lb1_3, lb2_3, lb3_3, lb4_3, lb5_3, lb6_3, lb7_3,
    le0_3, le1_3, le2_3, le3_3, le4_3, le5_3, le6_3, le7_3, hval_3⟩ :=
    ld_readback_jmp m0 (jb.toNat + 16) s1v hr16
  obtain ⟨σ3, i3, hs_3, hi3, hG3, hmc3, hobs3⟩ :=
    site_80007044_jmp σ2 i2 (c.steps + 1 + 1) (0x80007044#64) vmi2 jb
      lb0_3 lb1_3 lb2_3 lb3_3 lb4_3 lb5_3 lb6_3 lb7_3
      hG2 hpc2 hmi2 h_x10_2 hload2 rfl
      (by rw [hj16]; omega) (by rw [hj16]; omega)
      (by rw [hj16]; omega) (by rw [hj16]; omega)
      (by rw [hj16, hmc2']; exact le0_3)
      (by rw [hj16, hmc2']; exact le1_3)
      (by rw [hj16, hmc2']; exact le2_3)
      (by rw [hj16, hmc2']; exact le3_3)
      (by rw [hj16, hmc2']; exact le4_3)
      (by rw [hj16, hmc2']; exact le5_3)
      (by rw [hj16, hmc2']; exact le6_3)
      (by rw [hj16, hmc2']; exact le7_3) hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80007048#64 : BitVec 64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80007044#64 : BitVec 64) 4 = (0x80007048#64 : BitVec 64) from by decide] at this
  have hset_3 : σ3.regs.get? Register.x9 = some s1v := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hval_3] at this
  have h_x1_3 := obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_2
  have h_x10_3 := obs_alu_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_2
  have h_x11_3 := obs_alu_other hobs3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x11_2
  have h_x8_3 := obs_alu_other hobs3 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hset_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hmc3' : σ3.mem = m0 := by rw [hmc3, hmc2']
  have hload3 : LongjmpLoaded σ3.mem := hmc3' ▸ (hmem ▸ hloaded)
  -- === 0x80007048: ld x18,24(a0) ===
  obtain ⟨lb0_4, lb1_4, lb2_4, lb3_4, lb4_4, lb5_4, lb6_4, lb7_4,
    le0_4, le1_4, le2_4, le3_4, le4_4, le5_4, le6_4, le7_4, hval_4⟩ :=
    ld_readback_jmp m0 (jb.toNat + 24) s2v hr24
  obtain ⟨σ4, i4, hs_4, hi4, hG4, hmc4, hobs4⟩ :=
    site_80007048_jmp σ3 i3 (c.steps + 1 + 1 + 1) (0x80007048#64) vmi3 jb
      lb0_4 lb1_4 lb2_4 lb3_4 lb4_4 lb5_4 lb6_4 lb7_4
      hG3 hpc3 hmi3 h_x10_3 hload3 rfl
      (by rw [hj24]; omega) (by rw [hj24]; omega)
      (by rw [hj24]; omega) (by rw [hj24]; omega)
      (by rw [hj24, hmc3']; exact le0_4)
      (by rw [hj24, hmc3']; exact le1_4)
      (by rw [hj24, hmc3']; exact le2_4)
      (by rw [hj24, hmc3']; exact le3_4)
      (by rw [hj24, hmc3']; exact le4_4)
      (by rw [hj24, hmc3']; exact le5_4)
      (by rw [hj24, hmc3']; exact le6_4)
      (by rw [hj24, hmc3']; exact le7_4) hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x8000704c#64 : BitVec 64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x80007048#64 : BitVec 64) 4 = (0x8000704c#64 : BitVec 64) from by decide] at this
  have hset_4 : σ4.regs.get? Register.x18 = some s2v := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hval_4] at this
  have h_x1_4 := obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_3
  have h_x10_4 := obs_alu_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_3
  have h_x11_4 := obs_alu_other hobs4 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x11_3
  have h_x8_4 := obs_alu_other hobs4 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x8_3
  have h_x9_4 := obs_alu_other hobs4 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hset_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hmc4' : σ4.mem = m0 := by rw [hmc4, hmc3']
  have hload4 : LongjmpLoaded σ4.mem := hmc4' ▸ (hmem ▸ hloaded)
  -- === 0x8000704c: ld x19,32(a0) ===
  obtain ⟨lb0_5, lb1_5, lb2_5, lb3_5, lb4_5, lb5_5, lb6_5, lb7_5,
    le0_5, le1_5, le2_5, le3_5, le4_5, le5_5, le6_5, le7_5, hval_5⟩ :=
    ld_readback_jmp m0 (jb.toNat + 32) s3v hr32
  obtain ⟨σ5, i5, hs_5, hi5, hG5, hmc5, hobs5⟩ :=
    site_8000704c_jmp σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x8000704c#64) vmi4 jb
      lb0_5 lb1_5 lb2_5 lb3_5 lb4_5 lb5_5 lb6_5 lb7_5
      hG4 hpc4 hmi4 h_x10_4 hload4 rfl
      (by rw [hj32]; omega) (by rw [hj32]; omega)
      (by rw [hj32]; omega) (by rw [hj32]; omega)
      (by rw [hj32, hmc4']; exact le0_5)
      (by rw [hj32, hmc4']; exact le1_5)
      (by rw [hj32, hmc4']; exact le2_5)
      (by rw [hj32, hmc4']; exact le3_5)
      (by rw [hj32, hmc4']; exact le4_5)
      (by rw [hj32, hmc4']; exact le5_5)
      (by rw [hj32, hmc4']; exact le6_5)
      (by rw [hj32, hmc4']; exact le7_5) hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80007050#64 : BitVec 64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x8000704c#64 : BitVec 64) 4 = (0x80007050#64 : BitVec 64) from by decide] at this
  have hset_5 : σ5.regs.get? Register.x19 = some s3v := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hval_5] at this
  have h_x1_5 := obs_alu_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_4
  have h_x10_5 := obs_alu_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_4
  have h_x11_5 := obs_alu_other hobs5 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x11_4
  have h_x18_5 := obs_alu_other hobs5 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hset_4
  have h_x8_5 := obs_alu_other hobs5 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x8_4
  have h_x9_5 := obs_alu_other hobs5 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x9_4
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hmc5' : σ5.mem = m0 := by rw [hmc5, hmc4']
  have hload5 : LongjmpLoaded σ5.mem := hmc5' ▸ (hmem ▸ hloaded)
  -- === 0x80007050: ld x20,40(a0) ===
  obtain ⟨lb0_6, lb1_6, lb2_6, lb3_6, lb4_6, lb5_6, lb6_6, lb7_6,
    le0_6, le1_6, le2_6, le3_6, le4_6, le5_6, le6_6, le7_6, hval_6⟩ :=
    ld_readback_jmp m0 (jb.toNat + 40) s4v hr40
  obtain ⟨σ6, i6, hs_6, hi6, hG6, hmc6, hobs6⟩ :=
    site_80007050_jmp σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80007050#64) vmi5 jb
      lb0_6 lb1_6 lb2_6 lb3_6 lb4_6 lb5_6 lb6_6 lb7_6
      hG5 hpc5 hmi5 h_x10_5 hload5 rfl
      (by rw [hj40]; omega) (by rw [hj40]; omega)
      (by rw [hj40]; omega) (by rw [hj40]; omega)
      (by rw [hj40, hmc5']; exact le0_6)
      (by rw [hj40, hmc5']; exact le1_6)
      (by rw [hj40, hmc5']; exact le2_6)
      (by rw [hj40, hmc5']; exact le3_6)
      (by rw [hj40, hmc5']; exact le4_6)
      (by rw [hj40, hmc5']; exact le5_6)
      (by rw [hj40, hmc5']; exact le6_6)
      (by rw [hj40, hmc5']; exact le7_6) hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x80007054#64 : BitVec 64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x80007050#64 : BitVec 64) 4 = (0x80007054#64 : BitVec 64) from by decide] at this
  have hset_6 : σ6.regs.get? Register.x20 = some s4v := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hval_6] at this
  have h_x1_6 := obs_alu_other hobs6 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_5
  have h_x10_6 := obs_alu_other hobs6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_5
  have h_x11_6 := obs_alu_other hobs6 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x11_5
  have h_x18_6 := obs_alu_other hobs6 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x18_5
  have h_x19_6 := obs_alu_other hobs6 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hset_5
  have h_x8_6 := obs_alu_other hobs6 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x8_5
  have h_x9_6 := obs_alu_other hobs6 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x9_5
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hmc6' : σ6.mem = m0 := by rw [hmc6, hmc5']
  have hload6 : LongjmpLoaded σ6.mem := hmc6' ▸ (hmem ▸ hloaded)
  -- === 0x80007054: ld x21,48(a0) ===
  obtain ⟨lb0_7, lb1_7, lb2_7, lb3_7, lb4_7, lb5_7, lb6_7, lb7_7,
    le0_7, le1_7, le2_7, le3_7, le4_7, le5_7, le6_7, le7_7, hval_7⟩ :=
    ld_readback_jmp m0 (jb.toNat + 48) s5v hr48
  obtain ⟨σ7, i7, hs_7, hi7, hG7, hmc7, hobs7⟩ :=
    site_80007054_jmp σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80007054#64) vmi6 jb
      lb0_7 lb1_7 lb2_7 lb3_7 lb4_7 lb5_7 lb6_7 lb7_7
      hG6 hpc6 hmi6 h_x10_6 hload6 rfl
      (by rw [hj48]; omega) (by rw [hj48]; omega)
      (by rw [hj48]; omega) (by rw [hj48]; omega)
      (by rw [hj48, hmc6']; exact le0_7)
      (by rw [hj48, hmc6']; exact le1_7)
      (by rw [hj48, hmc6']; exact le2_7)
      (by rw [hj48, hmc6']; exact le3_7)
      (by rw [hj48, hmc6']; exact le4_7)
      (by rw [hj48, hmc6']; exact le5_7)
      (by rw [hj48, hmc6']; exact le6_7)
      (by rw [hj48, hmc6']; exact le7_7) hi6
  have hpc7 : σ7.regs.get? Register.PC = some (0x80007058#64 : BitVec 64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x80007054#64 : BitVec 64) 4 = (0x80007058#64 : BitVec 64) from by decide] at this
  have hset_7 : σ7.regs.get? Register.x21 = some s5v := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hval_7] at this
  have h_x1_7 := obs_alu_other hobs7 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_6
  have h_x10_7 := obs_alu_other hobs7 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_6
  have h_x11_7 := obs_alu_other hobs7 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x11_6
  have h_x18_7 := obs_alu_other hobs7 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x18_6
  have h_x19_7 := obs_alu_other hobs7 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x19_6
  have h_x20_7 := obs_alu_other hobs7 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hset_6
  have h_x8_7 := obs_alu_other hobs7 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x8_6
  have h_x9_7 := obs_alu_other hobs7 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x9_6
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hmc7' : σ7.mem = m0 := by rw [hmc7, hmc6']
  have hload7 : LongjmpLoaded σ7.mem := hmc7' ▸ (hmem ▸ hloaded)
  -- === 0x80007058: ld x22,56(a0) ===
  obtain ⟨lb0_8, lb1_8, lb2_8, lb3_8, lb4_8, lb5_8, lb6_8, lb7_8,
    le0_8, le1_8, le2_8, le3_8, le4_8, le5_8, le6_8, le7_8, hval_8⟩ :=
    ld_readback_jmp m0 (jb.toNat + 56) s6v hr56
  obtain ⟨σ8, i8, hs_8, hi8, hG8, hmc8, hobs8⟩ :=
    site_80007058_jmp σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007058#64) vmi7 jb
      lb0_8 lb1_8 lb2_8 lb3_8 lb4_8 lb5_8 lb6_8 lb7_8
      hG7 hpc7 hmi7 h_x10_7 hload7 rfl
      (by rw [hj56]; omega) (by rw [hj56]; omega)
      (by rw [hj56]; omega) (by rw [hj56]; omega)
      (by rw [hj56, hmc7']; exact le0_8)
      (by rw [hj56, hmc7']; exact le1_8)
      (by rw [hj56, hmc7']; exact le2_8)
      (by rw [hj56, hmc7']; exact le3_8)
      (by rw [hj56, hmc7']; exact le4_8)
      (by rw [hj56, hmc7']; exact le5_8)
      (by rw [hj56, hmc7']; exact le6_8)
      (by rw [hj56, hmc7']; exact le7_8) hi7
  have hpc8 : σ8.regs.get? Register.PC = some (0x8000705c#64 : BitVec 64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x80007058#64 : BitVec 64) 4 = (0x8000705c#64 : BitVec 64) from by decide] at this
  have hset_8 : σ8.regs.get? Register.x22 = some s6v := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hval_8] at this
  have h_x1_8 := obs_alu_other hobs8 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_7
  have h_x10_8 := obs_alu_other hobs8 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_7
  have h_x11_8 := obs_alu_other hobs8 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x11_7
  have h_x18_8 := obs_alu_other hobs8 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x18_7
  have h_x19_8 := obs_alu_other hobs8 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x19_7
  have h_x20_8 := obs_alu_other hobs8 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x20_7
  have h_x21_8 := obs_alu_other hobs8 Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hset_7
  have h_x8_8 := obs_alu_other hobs8 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x8_7
  have h_x9_8 := obs_alu_other hobs8 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x9_7
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hmc8' : σ8.mem = m0 := by rw [hmc8, hmc7']
  have hload8 : LongjmpLoaded σ8.mem := hmc8' ▸ (hmem ▸ hloaded)
  -- === 0x8000705c: ld x23,64(a0) ===
  obtain ⟨lb0_9, lb1_9, lb2_9, lb3_9, lb4_9, lb5_9, lb6_9, lb7_9,
    le0_9, le1_9, le2_9, le3_9, le4_9, le5_9, le6_9, le7_9, hval_9⟩ :=
    ld_readback_jmp m0 (jb.toNat + 64) s7v hr64
  obtain ⟨σ9, i9, hs_9, hi9, hG9, hmc9, hobs9⟩ :=
    site_8000705c_jmp σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000705c#64) vmi8 jb
      lb0_9 lb1_9 lb2_9 lb3_9 lb4_9 lb5_9 lb6_9 lb7_9
      hG8 hpc8 hmi8 h_x10_8 hload8 rfl
      (by rw [hj64]; omega) (by rw [hj64]; omega)
      (by rw [hj64]; omega) (by rw [hj64]; omega)
      (by rw [hj64, hmc8']; exact le0_9)
      (by rw [hj64, hmc8']; exact le1_9)
      (by rw [hj64, hmc8']; exact le2_9)
      (by rw [hj64, hmc8']; exact le3_9)
      (by rw [hj64, hmc8']; exact le4_9)
      (by rw [hj64, hmc8']; exact le5_9)
      (by rw [hj64, hmc8']; exact le6_9)
      (by rw [hj64, hmc8']; exact le7_9) hi8
  have hpc9 : σ9.regs.get? Register.PC = some (0x80007060#64 : BitVec 64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x8000705c#64 : BitVec 64) 4 = (0x80007060#64 : BitVec 64) from by decide] at this
  have hset_9 : σ9.regs.get? Register.x23 = some s7v := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hval_9] at this
  have h_x1_9 := obs_alu_other hobs9 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_8
  have h_x10_9 := obs_alu_other hobs9 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_8
  have h_x11_9 := obs_alu_other hobs9 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x11_8
  have h_x18_9 := obs_alu_other hobs9 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x18_8
  have h_x19_9 := obs_alu_other hobs9 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x19_8
  have h_x20_9 := obs_alu_other hobs9 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x20_8
  have h_x21_9 := obs_alu_other hobs9 Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x21_8
  have h_x22_9 := obs_alu_other hobs9 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hset_8
  have h_x8_9 := obs_alu_other hobs9 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x8_8
  have h_x9_9 := obs_alu_other hobs9 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x9_8
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have hmc9' : σ9.mem = m0 := by rw [hmc9, hmc8']
  have hload9 : LongjmpLoaded σ9.mem := hmc9' ▸ (hmem ▸ hloaded)
  -- === 0x80007060: ld x24,72(a0) ===
  obtain ⟨lb0_10, lb1_10, lb2_10, lb3_10, lb4_10, lb5_10, lb6_10, lb7_10,
    le0_10, le1_10, le2_10, le3_10, le4_10, le5_10, le6_10, le7_10, hval_10⟩ :=
    ld_readback_jmp m0 (jb.toNat + 72) s8v hr72
  obtain ⟨σ10, i10, hs_10, hi10, hG10, hmc10, hobs10⟩ :=
    site_80007060_jmp σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007060#64) vmi9 jb
      lb0_10 lb1_10 lb2_10 lb3_10 lb4_10 lb5_10 lb6_10 lb7_10
      hG9 hpc9 hmi9 h_x10_9 hload9 rfl
      (by rw [hj72]; omega) (by rw [hj72]; omega)
      (by rw [hj72]; omega) (by rw [hj72]; omega)
      (by rw [hj72, hmc9']; exact le0_10)
      (by rw [hj72, hmc9']; exact le1_10)
      (by rw [hj72, hmc9']; exact le2_10)
      (by rw [hj72, hmc9']; exact le3_10)
      (by rw [hj72, hmc9']; exact le4_10)
      (by rw [hj72, hmc9']; exact le5_10)
      (by rw [hj72, hmc9']; exact le6_10)
      (by rw [hj72, hmc9']; exact le7_10) hi9
  have hpc10 : σ10.regs.get? Register.PC = some (0x80007064#64 : BitVec 64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x80007060#64 : BitVec 64) 4 = (0x80007064#64 : BitVec 64) from by decide] at this
  have hset_10 : σ10.regs.get? Register.x24 = some s8v := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hval_10] at this
  have h_x1_10 := obs_alu_other hobs10 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_9
  have h_x10_10 := obs_alu_other hobs10 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_9
  have h_x11_10 := obs_alu_other hobs10 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x11_9
  have h_x18_10 := obs_alu_other hobs10 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x18_9
  have h_x19_10 := obs_alu_other hobs10 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x19_9
  have h_x20_10 := obs_alu_other hobs10 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x20_9
  have h_x21_10 := obs_alu_other hobs10 Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x21_9
  have h_x22_10 := obs_alu_other hobs10 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x22_9
  have h_x23_10 := obs_alu_other hobs10 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hset_9
  have h_x8_10 := obs_alu_other hobs10 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x8_9
  have h_x9_10 := obs_alu_other hobs10 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x9_9
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hmc10' : σ10.mem = m0 := by rw [hmc10, hmc9']
  have hload10 : LongjmpLoaded σ10.mem := hmc10' ▸ (hmem ▸ hloaded)
  -- === 0x80007064: ld x25,80(a0) ===
  obtain ⟨lb0_11, lb1_11, lb2_11, lb3_11, lb4_11, lb5_11, lb6_11, lb7_11,
    le0_11, le1_11, le2_11, le3_11, le4_11, le5_11, le6_11, le7_11, hval_11⟩ :=
    ld_readback_jmp m0 (jb.toNat + 80) s9v hr80
  obtain ⟨σ11, i11, hs_11, hi11, hG11, hmc11, hobs11⟩ :=
    site_80007064_jmp σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007064#64) vmi10 jb
      lb0_11 lb1_11 lb2_11 lb3_11 lb4_11 lb5_11 lb6_11 lb7_11
      hG10 hpc10 hmi10 h_x10_10 hload10 rfl
      (by rw [hj80]; omega) (by rw [hj80]; omega)
      (by rw [hj80]; omega) (by rw [hj80]; omega)
      (by rw [hj80, hmc10']; exact le0_11)
      (by rw [hj80, hmc10']; exact le1_11)
      (by rw [hj80, hmc10']; exact le2_11)
      (by rw [hj80, hmc10']; exact le3_11)
      (by rw [hj80, hmc10']; exact le4_11)
      (by rw [hj80, hmc10']; exact le5_11)
      (by rw [hj80, hmc10']; exact le6_11)
      (by rw [hj80, hmc10']; exact le7_11) hi10
  have hpc11 : σ11.regs.get? Register.PC = some (0x80007068#64 : BitVec 64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x80007064#64 : BitVec 64) 4 = (0x80007068#64 : BitVec 64) from by decide] at this
  have hset_11 : σ11.regs.get? Register.x25 = some s9v := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hval_11] at this
  have h_x1_11 := obs_alu_other hobs11 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_10
  have h_x10_11 := obs_alu_other hobs11 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_10
  have h_x11_11 := obs_alu_other hobs11 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x11_10
  have h_x18_11 := obs_alu_other hobs11 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x18_10
  have h_x19_11 := obs_alu_other hobs11 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x19_10
  have h_x20_11 := obs_alu_other hobs11 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x20_10
  have h_x21_11 := obs_alu_other hobs11 Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x21_10
  have h_x22_11 := obs_alu_other hobs11 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x22_10
  have h_x23_11 := obs_alu_other hobs11 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x23_10
  have h_x24_11 := obs_alu_other hobs11 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hset_10
  have h_x8_11 := obs_alu_other hobs11 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x8_10
  have h_x9_11 := obs_alu_other hobs11 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x9_10
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hmc11' : σ11.mem = m0 := by rw [hmc11, hmc10']
  have hload11 : LongjmpLoaded σ11.mem := hmc11' ▸ (hmem ▸ hloaded)
  -- === 0x80007068: ld x26,88(a0) ===
  obtain ⟨lb0_12, lb1_12, lb2_12, lb3_12, lb4_12, lb5_12, lb6_12, lb7_12,
    le0_12, le1_12, le2_12, le3_12, le4_12, le5_12, le6_12, le7_12, hval_12⟩ :=
    ld_readback_jmp m0 (jb.toNat + 88) s10v hr88
  obtain ⟨σ12, i12, hs_12, hi12, hG12, hmc12, hobs12⟩ :=
    site_80007068_jmp σ11 i11 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007068#64) vmi11 jb
      lb0_12 lb1_12 lb2_12 lb3_12 lb4_12 lb5_12 lb6_12 lb7_12
      hG11 hpc11 hmi11 h_x10_11 hload11 rfl
      (by rw [hj88]; omega) (by rw [hj88]; omega)
      (by rw [hj88]; omega) (by rw [hj88]; omega)
      (by rw [hj88, hmc11']; exact le0_12)
      (by rw [hj88, hmc11']; exact le1_12)
      (by rw [hj88, hmc11']; exact le2_12)
      (by rw [hj88, hmc11']; exact le3_12)
      (by rw [hj88, hmc11']; exact le4_12)
      (by rw [hj88, hmc11']; exact le5_12)
      (by rw [hj88, hmc11']; exact le6_12)
      (by rw [hj88, hmc11']; exact le7_12) hi11
  have hpc12 : σ12.regs.get? Register.PC = some (0x8000706c#64 : BitVec 64) := by
    have := obs_alu_pc hobs12
    rwa [show BitVec.addInt (0x80007068#64 : BitVec 64) 4 = (0x8000706c#64 : BitVec 64) from by decide] at this
  have hset_12 : σ12.regs.get? Register.x26 = some s10v := by
    have := obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hval_12] at this
  have h_x1_12 := obs_alu_other hobs12 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_11
  have h_x10_12 := obs_alu_other hobs12 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_11
  have h_x11_12 := obs_alu_other hobs12 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x11_11
  have h_x18_12 := obs_alu_other hobs12 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x18_11
  have h_x19_12 := obs_alu_other hobs12 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x19_11
  have h_x20_12 := obs_alu_other hobs12 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x20_11
  have h_x21_12 := obs_alu_other hobs12 Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x21_11
  have h_x22_12 := obs_alu_other hobs12 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x22_11
  have h_x23_12 := obs_alu_other hobs12 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x23_11
  have h_x24_12 := obs_alu_other hobs12 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x24_11
  have h_x25_12 := obs_alu_other hobs12 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hset_11
  have h_x8_12 := obs_alu_other hobs12 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x8_11
  have h_x9_12 := obs_alu_other hobs12 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x9_11
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  have hmc12' : σ12.mem = m0 := by rw [hmc12, hmc11']
  have hload12 : LongjmpLoaded σ12.mem := hmc12' ▸ (hmem ▸ hloaded)
  -- === 0x8000706c: ld x27,96(a0) ===
  obtain ⟨lb0_13, lb1_13, lb2_13, lb3_13, lb4_13, lb5_13, lb6_13, lb7_13,
    le0_13, le1_13, le2_13, le3_13, le4_13, le5_13, le6_13, le7_13, hval_13⟩ :=
    ld_readback_jmp m0 (jb.toNat + 96) s11v hr96
  obtain ⟨σ13, i13, hs_13, hi13, hG13, hmc13, hobs13⟩ :=
    site_8000706c_jmp σ12 i12 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000706c#64) vmi12 jb
      lb0_13 lb1_13 lb2_13 lb3_13 lb4_13 lb5_13 lb6_13 lb7_13
      hG12 hpc12 hmi12 h_x10_12 hload12 rfl
      (by rw [hj96]; omega) (by rw [hj96]; omega)
      (by rw [hj96]; omega) (by rw [hj96]; omega)
      (by rw [hj96, hmc12']; exact le0_13)
      (by rw [hj96, hmc12']; exact le1_13)
      (by rw [hj96, hmc12']; exact le2_13)
      (by rw [hj96, hmc12']; exact le3_13)
      (by rw [hj96, hmc12']; exact le4_13)
      (by rw [hj96, hmc12']; exact le5_13)
      (by rw [hj96, hmc12']; exact le6_13)
      (by rw [hj96, hmc12']; exact le7_13) hi12
  have hpc13 : σ13.regs.get? Register.PC = some (0x80007070#64 : BitVec 64) := by
    have := obs_alu_pc hobs13
    rwa [show BitVec.addInt (0x8000706c#64 : BitVec 64) 4 = (0x80007070#64 : BitVec 64) from by decide] at this
  have hset_13 : σ13.regs.get? Register.x27 = some s11v := by
    have := obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hval_13] at this
  have h_x1_13 := obs_alu_other hobs13 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_12
  have h_x10_13 := obs_alu_other hobs13 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x10_12
  have h_x11_13 := obs_alu_other hobs13 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x11_12
  have h_x18_13 := obs_alu_other hobs13 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x18_12
  have h_x19_13 := obs_alu_other hobs13 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x19_12
  have h_x20_13 := obs_alu_other hobs13 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x20_12
  have h_x21_13 := obs_alu_other hobs13 Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x21_12
  have h_x22_13 := obs_alu_other hobs13 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x22_12
  have h_x23_13 := obs_alu_other hobs13 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x23_12
  have h_x24_13 := obs_alu_other hobs13 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x24_12
  have h_x25_13 := obs_alu_other hobs13 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x25_12
  have h_x26_13 := obs_alu_other hobs13 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hset_12
  have h_x8_13 := obs_alu_other hobs13 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x8_12
  have h_x9_13 := obs_alu_other hobs13 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x9_12
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  have hmc13' : σ13.mem = m0 := by rw [hmc13, hmc12']
  have hload13 : LongjmpLoaded σ13.mem := hmc13' ▸ (hmem ▸ hloaded)
  -- === 0x80007070: ld x2,104(a0) ===
  obtain ⟨lb0_14, lb1_14, lb2_14, lb3_14, lb4_14, lb5_14, lb6_14, lb7_14,
    le0_14, le1_14, le2_14, le3_14, le4_14, le5_14, le6_14, le7_14, hval_14⟩ :=
    ld_readback_jmp m0 (jb.toNat + 104) spv hr104
  obtain ⟨σ14, i14, hs_14, hi14, hG14, hmc14, hobs14⟩ :=
    site_80007070_jmp σ13 i13 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007070#64) vmi13 jb
      lb0_14 lb1_14 lb2_14 lb3_14 lb4_14 lb5_14 lb6_14 lb7_14
      hG13 hpc13 hmi13 h_x10_13 hload13 rfl
      (by rw [hj104]; omega) (by rw [hj104]; omega)
      (by rw [hj104]; omega) (by rw [hj104]; omega)
      (by rw [hj104, hmc13']; exact le0_14)
      (by rw [hj104, hmc13']; exact le1_14)
      (by rw [hj104, hmc13']; exact le2_14)
      (by rw [hj104, hmc13']; exact le3_14)
      (by rw [hj104, hmc13']; exact le4_14)
      (by rw [hj104, hmc13']; exact le5_14)
      (by rw [hj104, hmc13']; exact le6_14)
      (by rw [hj104, hmc13']; exact le7_14) hi13
  have hpc14 : σ14.regs.get? Register.PC = some (0x80007074#64 : BitVec 64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x80007070#64 : BitVec 64) 4 = (0x80007074#64 : BitVec 64) from by decide] at this
  have hset_14 : σ14.regs.get? Register.x2 = some spv := by
    have := obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hval_14] at this
  have h_x1_14 := obs_alu_other hobs14 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_13
  have h_x11_14 := obs_alu_other hobs14 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x11_13
  have h_x18_14 := obs_alu_other hobs14 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x18_13
  have h_x19_14 := obs_alu_other hobs14 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x19_13
  have h_x20_14 := obs_alu_other hobs14 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x20_13
  have h_x21_14 := obs_alu_other hobs14 Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x21_13
  have h_x22_14 := obs_alu_other hobs14 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x22_13
  have h_x23_14 := obs_alu_other hobs14 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x23_13
  have h_x24_14 := obs_alu_other hobs14 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x24_13
  have h_x25_14 := obs_alu_other hobs14 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x25_13
  have h_x26_14 := obs_alu_other hobs14 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x26_13
  have h_x27_14 := obs_alu_other hobs14 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hset_13
  have h_x8_14 := obs_alu_other hobs14 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x8_13
  have h_x9_14 := obs_alu_other hobs14 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x9_13
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  have hmc14' : σ14.mem = m0 := by rw [hmc14, hmc13']
  have hload14 : LongjmpLoaded σ14.mem := hmc14' ▸ (hmem ▸ hloaded)
  -- === 0x80007074: seqz a0,a1 ===
  obtain ⟨σ15, i15, hs_15, hi15, hG15, hmc15, hobs15⟩ :=
    site_80007074_jmp σ14 i14 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007074#64) vmi14 v hG14 hpc14 hmi14 h_x11_14 hload14 rfl hi14
  have hpc15 : σ15.regs.get? Register.PC = some (0x80007078#64 : BitVec 64) := by
    have := obs_alu_pc hobs15
    rwa [show BitVec.addInt (0x80007074#64 : BitVec 64) 4 = (0x80007078#64 : BitVec 64) from by decide] at this
  have ha0_15 : σ15.regs.get? Register.x10 = some (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v (sign_extend (m := 64) (0x001#12))))) :=
    obs_alu_rd hobs15 (by decide) (by decide) (by decide) (by decide) (by decide)
  have ha1_15 := obs_alu_other hobs15 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x11_14
  have h_x1_15 := obs_alu_other hobs15 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_14
  have h_x8_15 := obs_alu_other hobs15 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x8_14
  have h_x9_15 := obs_alu_other hobs15 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x9_14
  have h_x18_15 := obs_alu_other hobs15 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x18_14
  have h_x19_15 := obs_alu_other hobs15 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x19_14
  have h_x20_15 := obs_alu_other hobs15 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x20_14
  have h_x21_15 := obs_alu_other hobs15 Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x21_14
  have h_x22_15 := obs_alu_other hobs15 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x22_14
  have h_x23_15 := obs_alu_other hobs15 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x23_14
  have h_x24_15 := obs_alu_other hobs15 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x24_14
  have h_x25_15 := obs_alu_other hobs15 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x25_14
  have h_x26_15 := obs_alu_other hobs15 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x26_14
  have h_x27_15 := obs_alu_other hobs15 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x27_14
  have h_x2_15 := obs_alu_other hobs15 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hset_14
  obtain ⟨vmi15, hmi15⟩ := obs_alu_minstret hobs15
  have hmc15' : σ15.mem = m0 := by rw [hmc15, hmc14']
  have hload15 : LongjmpLoaded σ15.mem := hmc15' ▸ (hmem ▸ hloaded)
  -- === 0x80007078: add a0,a0,a1 ===
  obtain ⟨σ16, i16, hs_16, hi16, hG16, hmc16, hobs16⟩ :=
    site_80007078_jmp σ15 i15 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80007078#64) vmi15 (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v (sign_extend (m := 64) (0x001#12))))) v hG15 hpc15 hmi15 ha0_15 ha1_15 hload15 rfl hi15
  have hpc16 : σ16.regs.get? Register.PC = some (0x8000707c#64 : BitVec 64) := by
    have := obs_alu_pc hobs16
    rwa [show BitVec.addInt (0x80007078#64 : BitVec 64) 4 = (0x8000707c#64 : BitVec 64) from by decide] at this
  have ha0_16 : σ16.regs.get? Register.x10 = some (zero_extend (m := 64) (bool_to_bit (zopz0zI_u v (sign_extend (m := 64) (0x001#12)))) + v) :=
    obs_alu_rd hobs16 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h_x1_16 := obs_alu_other hobs16 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_15
  have h_x8_16 := obs_alu_other hobs16 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x8_15
  have h_x9_16 := obs_alu_other hobs16 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x9_15
  have h_x18_16 := obs_alu_other hobs16 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x18_15
  have h_x19_16 := obs_alu_other hobs16 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x19_15
  have h_x20_16 := obs_alu_other hobs16 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x20_15
  have h_x21_16 := obs_alu_other hobs16 Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x21_15
  have h_x22_16 := obs_alu_other hobs16 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x22_15
  have h_x23_16 := obs_alu_other hobs16 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x23_15
  have h_x24_16 := obs_alu_other hobs16 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x24_15
  have h_x25_16 := obs_alu_other hobs16 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x25_15
  have h_x26_16 := obs_alu_other hobs16 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x26_15
  have h_x27_16 := obs_alu_other hobs16 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x27_15
  have h_x2_16 := obs_alu_other hobs16 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x2_15
  obtain ⟨vmi16, hmi16⟩ := obs_alu_minstret hobs16
  have hmc16' : σ16.mem = m0 := by rw [hmc16, hmc15']
  have hload16 : LongjmpLoaded σ16.mem := hmc16' ▸ (hmem ▸ hloaded)
  -- === 0x8000707c: ret ===
  have hret_tgt : (BitVec.update (ra0 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt ra0 hraA]; exact hraA
  obtain ⟨σ17, i17, hs_17, hi17, hG17, hmc17, hobs17⟩ :=
    site_8000707c_jmp σ16 i16 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000707c#64) vmi16 ra0 hG16 hpc16 hmi16 h_x1_16 hload16 rfl hret_tgt hi16
  have hpc17 : σ17.regs.get? Register.PC = some ra0 := by
    have := obs_jr_pc hobs17
    rwa [ret_tgt ra0 hraA] at this
  have ha0_17 := obs_jr_other hobs17 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_16
  have h_x1_17 := obs_jr_other hobs17 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x1_16
  have h_x8_17 := obs_jr_other hobs17 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x8_16
  have h_x9_17 := obs_jr_other hobs17 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x9_16
  have h_x18_17 := obs_jr_other hobs17 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x18_16
  have h_x19_17 := obs_jr_other hobs17 Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x19_16
  have h_x20_17 := obs_jr_other hobs17 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x20_16
  have h_x21_17 := obs_jr_other hobs17 Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x21_16
  have h_x22_17 := obs_jr_other hobs17 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x22_16
  have h_x23_17 := obs_jr_other hobs17 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x23_16
  have h_x24_17 := obs_jr_other hobs17 Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x24_16
  have h_x25_17 := obs_jr_other hobs17 Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x25_16
  have h_x26_17 := obs_jr_other hobs17 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x26_16
  have h_x27_17 := obs_jr_other hobs17 Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x27_16
  have h_x2_17 := obs_jr_other hobs17 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h_x2_16
  obtain ⟨vmi17, hmi17⟩ := obs_jr_minstret hobs17
  have hmc17' : σ17.mem = m0 := by rw [hmc17, hmc16']
  refine ⟨⟨σ17, i17, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, ?_, ?_⟩
  · have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs_1
    exact Steps.trans (Steps.single hstep1) (Steps.trans (Steps.single hs_2) (Steps.trans (Steps.single hs_3)
      (Steps.trans (Steps.single hs_4) (Steps.trans (Steps.single hs_5) (Steps.trans (Steps.single hs_6)
      (Steps.trans (Steps.single hs_7) (Steps.trans (Steps.single hs_8) (Steps.trans (Steps.single hs_9)
      (Steps.trans (Steps.single hs_10) (Steps.trans (Steps.single hs_11) (Steps.trans (Steps.single hs_12)
      (Steps.trans (Steps.single hs_13) (Steps.trans (Steps.single hs_14) (Steps.trans (Steps.single hs_15)
      (Steps.trans (Steps.single hs_16) (Steps.single hs_17))))))))))))))))
  · refine ⟨hG17, hi17, hmc17', hpc17, h_x1_17, h_x8_17, h_x9_17, h_x18_17, h_x19_17,
      h_x20_17, h_x21_17, h_x22_17, h_x23_17, h_x24_17, h_x25_17, h_x26_17, h_x27_17,
      h_x2_17, ha0_17, ⟨vmi17, hmi17⟩, ?_⟩
    intro R hR
    rw [frame_jr_jmp hobs17 R hR]
    rw [frame_alu_jmp hobs16 R hR.x10 hR]
    rw [frame_alu_jmp hobs15 R hR.x10 hR]
    rw [frame_alu_jmp hobs14 R (by exact hR.x2) hR]
    rw [frame_alu_jmp hobs13 R (by exact hR.x27) hR]
    rw [frame_alu_jmp hobs12 R (by exact hR.x26) hR]
    rw [frame_alu_jmp hobs11 R (by exact hR.x25) hR]
    rw [frame_alu_jmp hobs10 R (by exact hR.x24) hR]
    rw [frame_alu_jmp hobs9 R (by exact hR.x23) hR]
    rw [frame_alu_jmp hobs8 R (by exact hR.x22) hR]
    rw [frame_alu_jmp hobs7 R (by exact hR.x21) hR]
    rw [frame_alu_jmp hobs6 R (by exact hR.x20) hR]
    rw [frame_alu_jmp hobs5 R (by exact hR.x19) hR]
    rw [frame_alu_jmp hobs4 R (by exact hR.x18) hR]
    rw [frame_alu_jmp hobs3 R (by exact hR.x9) hR]
    rw [frame_alu_jmp hobs2 R (by exact hR.x8) hR]
    rw [frame_alu_jmp hobs1 R (by exact hR.x1) hR]
    exact hframe R hR

/-! ## `runtime_error_spec` (segmented + `SnprintfContract`-parameterized)

`runtime_error` (`0x80002da8`, 19 insts) formats a message via two `snprintf`
calls (into a stack `body` scratch and into `err_msg` at `in+224`) then tail-calls
`longjmp(&in->on_error, 1)` (`0x80002df0`) and never returns.  The two `snprintf`
calls are **not forward-simulated here** (they route into newlib's formatter, far
beyond this proof's scope).  Following the brief's fallback, `runtime_error`'s
pre-`longjmp` segment is abstracted by a **`SnprintfContract`** — a `Prop`-parameter
structure (NOT an axiom) that a caller must discharge with a real `snprintf` spec.

The contract states the one property the error transfer needs: from `runtime_error`
entry, the machine runs (in finitely many steps) to the `jal longjmp` call site
`0x80002df0` in a state where the arguments are set (`a0 = &in->on_error = in+16`,
`a1 = 1`), the jmp_buf `[in+16, in+128)` is **preserved** (its 15 `read64` slots
still hold the setjmp-time continuation the longjmp will restore), the return
address `ra` is 4-aligned, code is loaded, `GoodState`/tick/minstret hold, and the
blanket ghost frame is maintained.  Composing this segment with `longjmp_spec` (via
`Triple.seq`) yields the full transfer to interp_run's continuation. -/

/-- The pre-`longjmp` segment contract for `runtime_error`, parameterized by the
`Interp*` `inp`, the buffer contents `ra0 s0v..s11v spv` (as populated by
interp_run's setjmp — `ra0 = 0x80004428`), the entry ghost `g`, entry memory `m0`,
and the memory `m1` present at the `longjmp` call site (`snprintf` may have written
`err_msg`/`body`, but not the jmp_buf).  `SnprintfContract` is a `Prop`, discharged
by a caller's `snprintf` verification. -/
structure SnprintfContract (g : (R : Register) → Option (RegisterType R)) (inp : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  /-- From `runtime_error` entry, the machine reaches the `jal longjmp` site with the
  longjmp arguments set, the jmp_buf preserved (15 `read64` slots), `ra` 4-aligned,
  and the standing config invariants — packaged as a `Triple`. -/
  segment :
    Triple
      (fun c => GoodState c.σ ∧ Runtime_errorLoaded c.σ.mem ∧ LongjmpLoaded c.σ.mem ∧
        c.σ.mem = m0 ∧
        c.σ.regs.get? Register.PC = some (0x80002da8#64 : BitVec 64) ∧
        c.σ.regs.get? Register.x10 = some inp ∧
        WinRAM (inp + 16#64) ∧
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧ c.tick < 2 ∧
        (∀ R : Register, NotWrittenJmp R → c.σ.regs.get? R = g R))
      (fun c => GoodState c.σ ∧ LongjmpLoaded c.σ.mem ∧
        c.σ.regs.get? Register.PC = some (0x8000703c#64 : BitVec 64) ∧
        c.σ.regs.get? Register.x10 = some (inp + 16#64) ∧
        c.σ.regs.get? Register.x11 = some (1#64) ∧
        ra0.toNat % 4 = 0 ∧
        WinRAM (inp + 16#64) ∧
        read64 c.σ.mem ((inp + 16#64).toNat + 0)   = some ra0.toNat ∧
        read64 c.σ.mem ((inp + 16#64).toNat + 8)   = some s0v.toNat ∧
        read64 c.σ.mem ((inp + 16#64).toNat + 16)  = some s1v.toNat ∧
        read64 c.σ.mem ((inp + 16#64).toNat + 24)  = some s2v.toNat ∧
        read64 c.σ.mem ((inp + 16#64).toNat + 32)  = some s3v.toNat ∧
        read64 c.σ.mem ((inp + 16#64).toNat + 40)  = some s4v.toNat ∧
        read64 c.σ.mem ((inp + 16#64).toNat + 48)  = some s5v.toNat ∧
        read64 c.σ.mem ((inp + 16#64).toNat + 56)  = some s6v.toNat ∧
        read64 c.σ.mem ((inp + 16#64).toNat + 64)  = some s7v.toNat ∧
        read64 c.σ.mem ((inp + 16#64).toNat + 72)  = some s8v.toNat ∧
        read64 c.σ.mem ((inp + 16#64).toNat + 80)  = some s9v.toNat ∧
        read64 c.σ.mem ((inp + 16#64).toNat + 88)  = some s10v.toNat ∧
        read64 c.σ.mem ((inp + 16#64).toNat + 96)  = some s11v.toNat ∧
        read64 c.σ.mem ((inp + 16#64).toNat + 104) = some spv.toNat ∧
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧ c.tick < 2 ∧
        (∀ R : Register, NotWrittenJmp R → c.σ.regs.get? R = g R))

/-- **`runtime_error` error-transfer spec.**  Given the pre-`longjmp`
`SnprintfContract` and the setjmp-populated buffer at `in+16` (with `ra0`), from
`runtime_error` entry the machine transfers control (via `longjmp`) to the restored
`ra` (`= ra0 = 0x80004428`, interp_run's setjmp-continuation) with the callee-saved
registers restored to their setjmp-time values, `a0 = 1` (materialized longjmp
return), and `sp = spv`.  `snprintf`'s message text is left entirely unconstrained —
the transfer holds for any `err_msg` content the contract's segment produces. -/
theorem runtime_error_spec (g : (R : Register) → Option (RegisterType R)) (inp : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0) :
    Triple
      (fun c => GoodState c.σ ∧ Runtime_errorLoaded c.σ.mem ∧ LongjmpLoaded c.σ.mem ∧
        c.σ.mem = m0 ∧
        c.σ.regs.get? Register.PC = some (0x80002da8#64 : BitVec 64) ∧
        c.σ.regs.get? Register.x10 = some inp ∧
        WinRAM (inp + 16#64) ∧
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧ c.tick < 2 ∧
        (∀ R : Register, NotWrittenJmp R → c.σ.regs.get? R = g R))
      (fun c => GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some ra0 ∧
        c.σ.regs.get? Register.x1 = some ra0 ∧
        c.σ.regs.get? Register.x8 = some s0v ∧ c.σ.regs.get? Register.x9 = some s1v ∧
        c.σ.regs.get? Register.x18 = some s2v ∧ c.σ.regs.get? Register.x19 = some s3v ∧
        c.σ.regs.get? Register.x20 = some s4v ∧ c.σ.regs.get? Register.x21 = some s5v ∧
        c.σ.regs.get? Register.x22 = some s6v ∧ c.σ.regs.get? Register.x23 = some s7v ∧
        c.σ.regs.get? Register.x24 = some s8v ∧ c.σ.regs.get? Register.x25 = some s9v ∧
        c.σ.regs.get? Register.x26 = some s10v ∧ c.σ.regs.get? Register.x27 = some s11v ∧
        c.σ.regs.get? Register.x2 = some spv ∧
        c.σ.regs.get? Register.x10 = some (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (1#64) (sign_extend (m := 64) (0x001#12)))) + 1#64) ∧
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
        (∀ R : Register, NotWrittenJmp R → c.σ.regs.get? R = g R)) := by
  intro c hpre
  -- run the pre-longjmp segment to the `jal longjmp` site
  obtain ⟨c1, hseg, hq1⟩ := SC.segment c hpre
  obtain ⟨hG1, hload1, hpc1, ha0_1, ha1_1, hraA1, hWin1,
    hb0, hb8, hb16, hb24, hb32, hb40, hb48, hb56, hb64, hb72, hb80, hb88, hb96, hb104,
    hmi1, htick1, hframe1⟩ := hq1
  -- apply `longjmp_spec` at the call site, with entry memory `c1.σ.mem`
  obtain ⟨c2, hlj, hq2⟩ :=
    longjmp_spec g (inp + 16#64) (1#64) ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv
      c1.σ.mem c1
      ⟨hG1, hload1, rfl, hpc1, ha0_1, ha1_1, hraA1, hWin1,
        hb0, hb8, hb16, hb24, hb32, hb40, hb48, hb56, hb64, hb72, hb80, hb88, hb96, hb104,
        hmi1, htick1, hframe1⟩
  obtain ⟨hG2, htick2, hmem2, hpc2, hx1, hx8, hx9, hx18, hx19, hx20, hx21, hx22, hx23,
    hx24, hx25, hx26, hx27, hx2, hx10, hmi2, hframe2⟩ := hq2
  exact ⟨c2, hseg.trans hlj, hG2, htick2, hpc2, hx1, hx8, hx9, hx18, hx19, hx20, hx21, hx22,
    hx23, hx24, hx25, hx26, hx27, hx2, hx10, hmi2, hframe2⟩
