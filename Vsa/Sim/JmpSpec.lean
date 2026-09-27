import Vsa.Sim.JmpSites
import Vsa.Sim.Code.Runtime_error
import Vsa.Sim.Code.Interp_run
import Vsa.Sim.ValueSpec
import Vsa.Sim.ValueTruthySpec
import Vsa.Sim.Muldi3Spec
import Vsa.Triple
import Vsa.Sim.ObsAvoid

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
open Vsa.Sim.Code (LongjmpLoaded)

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

/-! ## `SetjmpLoaded` / `LongjmpLoaded` survive the buffer stores / a code-agreeing mem -/

/-! ## Pointer-offset helpers: `(jb + sext offX).toNat = jb.toNat + X` (no wrap) -/

/-! ## setjmp: the buffer write chain

`setjmpBuf m0 jb ra0 s0v s1v s2v .. s11v spv` is the exact 14-fold `writeMap8`
memory that setjmp produces from entry memory `m0`: the 14 callee-saved GPR values
placed at `jb+0, jb+8, .., jb+104`.  This is the load-bearing part of `Q`: it is
the buffer contents `longjmp` will later read back. -/

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

/-! ## longjmp: `read64` → 8 bytes + loaded-value identity

`longjmp` performs no stores, so every `ld` reads from the pinned entry memory `m0`.
`ld_readback_jmp` turns a `read64 m0 addr = some v.toNat` buffer fact into the 8
byte hypotheses the `ld` site consumes together with the fact that the site's loaded
value `sign_extend (assembled bytes)` equals `v`. -/
theorem sext64_id_jmp (d : BitVec (8 * 8)) : (sign_extend (m := 64) d : BitVec 64) = d := by
  simp only [sign_extend, Sail.BitVec.signExtend]
  exact BitVec.signExtend_eq d

/-! ## `longjmp_spec` -/

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

