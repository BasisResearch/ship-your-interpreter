import Vsa.Sim.rows.FnWriteFold
import Vsa.Sim.rows.FnWriteR
import Vsa.Sim.PtrArith
import Vsa.Sim.EnvNewSpec
import Vsa.Sim.DecodeTable.Batch17

/-!
# `_write_r` — the whole-function summary FOLD (gen_fn P2 pilot)

Folds the generated `_write_r` block arms (`rows/FnWriteR.lean`) around the P1
`_write` summary (`rows/FnWriteFold.lean`) into ONE `FnSummary`: from the ABI
entry `0x800104fc` with `(a0,a1,a2,a3) = (reent, fd, buf, len)` and the buffer
bytes pinned, `_write_r` spills `s0`/`ra`, clears `errno`, shuffles the
arguments, calls `_write` (the `jal` SEAM, `stepObs_jal`), takes the
`a0 ≠ -1` fall-through, reloads `ra`/`s0` off its own spill slots, and returns
to `ra0` with `a0 = len` and the console extended by EXACTLY the byte string.

Architecture (the gen_fn call-wrapper template, hand-developed here):

* ghosts bundled in `WRG`; static side conditions in `WRGOk` (named fields);
* the entry write-log is REIFIED (`wrEntryLog`, three stores) and its image
  `wrM1` is the summary's declared memory footprint;
* code/buffer pins are TRANSPORTED onto `wrM1` through the log's disjointness
  (`wrM1_getElem_lo` + the generated per-byte rebuilds);
* every block runs via `segRowFramed` over the GENERATED segs (zero
  `#derive_case` here — R9's point);
* the `jal _write` is the SEAM (`stepObs_jal` + the `obs_jal_*` accessors);
  the callee is spliced by instantiating P1's `write_summary` at the ghost
  bundle `wrWG1` whose `m0` is `wrM1`;
* the epilogue `ld`s read the spilled values back off `wrM1` via the
  store-image readback (`getElem_writeMap8_*` + `sext_reassemble`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/
-- discipline: allow(R7-conj-tower-def) every post/entry here IS a named-field
-- structure; the ∃ count is single-witness fields (`minstret : ∃ vm, …`,
-- `th : ∃ v, …`) inside those structures — no anonymous ∃/∧ towers.

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Vsa.Sim

/-! ## Ghosts and static side conditions -/

/-- The linked binary's global pointer (`__global_pointer$`, set once in
`_start`: `auipc gp,0x1b ; addi gp,gp,1296` at `0x80000000`). -/
def wrGpVal : BitVec 64 := 0x8001b510#64

/-- `errno`'s address: `gp + 1272 = 0x8001ba08` (the `sw zero,1272(gp)` target). -/
def wrErrnoAddr : Nat := 0x8001ba08

/-- The `_write_r` summary ghosts: entry ABI values (`a0 = reent`, `a1 = fd`,
`a2 = buf`, `a3 = len`), the callee-saved entry values, the buffer bytes, the
entry memory and console output. -/
structure WRG where
  reent : BitVec 64
  fd : BitVec 64
  buf : BitVec 64
  len : BitVec 64
  ra0 : BitVec 64
  sp0 : BitVec 64
  s00 : BitVec 64
  /-- the callee-saved `s1..s11` entry values (preserved by the summary). -/
  sv : SRegs
  bytes : List (BitVec 8)
  m0 : Std.ExtHashMap Nat (BitVec 8)
  out0 : Array String

/-- The stack pointer inside `_write_r`'s frame (`sp0 - 16`, as the computed
`addi sp,sp,-16` expression so every seg readback is `rfl`-shaped). -/
def wrSpE (g : WRG) : BitVec 64 := g.sp0 + sign_extend (m := 64) (0xff0#12)

/-- Static (config-independent) side conditions of the `_write_r` summary.
The buffer fields mirror P1's `WGOk`; the stack/errno fields are what the
frame's `sd`/`sw`/`ld` `MemFacts` and the store-image transports need. -/
structure WRGOk (g : WRG) : Prop where
  len_bytes : g.len.toNat = g.bytes.length
  nowrap : g.buf.toNat + g.bytes.length < 2 ^ 64
  lo : 0x80000000 ≤ g.buf.toNat
  hiram : g.buf.toNat + g.bytes.length ≤ 0x100000000
  htif : g.buf.toNat + g.bytes.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ g.buf.toNat
  pins : ∀ i, (h : i < g.bytes.length) → g.m0[g.buf.toNat + i]? = some (g.bytes[i]'h)
  code : Vsa.Sim.Code._writeLoaded g.m0
  codeR : Vsa.Sim.Code._write_rLoaded g.m0
  ra_align : g.ra0.toNat % 4 = 0
  ra_fix : BitVec.update (g.ra0 + sign_extend (m := 64) (0x000#12)) 0 0#1 = g.ra0
  /-- The spill window `[sp0-16, sp0)` sits above the HTIF window. -/
  sp_htif : tohostAddr + 16 ≤ g.sp0.toNat - 16
  /-- The spill window sits above the `errno` word. -/
  sp_errno : wrErrnoAddr + 4 ≤ g.sp0.toNat - 16
  sp_hi : g.sp0.toNat ≤ 0x100000000
  sp_align : g.sp0.toNat % 8 = 0
  /-- The buffer window avoids the spill window. -/
  buf_stack_disj : g.buf.toNat + g.bytes.length ≤ g.sp0.toNat - 16 ∨ g.sp0.toNat ≤ g.buf.toNat
  /-- The buffer window avoids the `errno` word. -/
  buf_errno_disj : g.buf.toNat + g.bytes.length ≤ wrErrnoAddr ∨ wrErrnoAddr + 4 ≤ g.buf.toNat

/-! ## The entry block's reified write-log and its memory image -/

/-- The entry pin list (`write_rX04fcL` at the ghosts; `gp` pinned concretely). -/
def wrEntryL (g : WRG) : GRegs :=
  write_rX04fcL g.fd g.sp0 g.s00 g.buf g.reent g.len g.ra0 wrGpVal

/-- The entry block's three stores (computed off `write_rX04fcSeg`, verified by
`wrEntryLog_eq`): `sd s0,0(sp')` (the ENTRY `s00` — the `sd` precedes
`mv s0,a0`), `sd ra,8(sp')`, `sw zero,1272(gp)`. -/
def wrEntryLog (g : WRG) : List WEntry :=
  [((wrSpE g + sign_extend (m := 64) (0x000#12)).toNat, 8, g.s00),
   ((wrSpE g + sign_extend (m := 64) (0x008#12)).toNat, 8, g.ra0),
   ((wrGpVal + sign_extend (m := 64) (0x4f8#12)).toNat, 4, 0#64)]

theorem wrEntryLog_eq (g : WRG) :
    (evalBlocks write_rX04fcSeg (SegEvalState.init (wrEntryL g) [])).log
      = wrEntryLog g := rfl

/-- The memory after `_write_r`'s entry block — the summary's whole footprint
(`_write` itself touches no memory; the epilogue only reads). -/
def wrM1 (g : WRG) : Std.ExtHashMap Nat (BitVec 8) :=
  writeLog g.m0 (wrEntryLog g)

/-! ## Frame-address arithmetic -/

theorem wr_spE_toNat (g : WRG) (hg : WRGOk g) :
    (wrSpE g).toNat = g.sp0.toNat - 16 := by
  show (g.sp0 + sign_extend (m := 64) (0xff0#12)).toNat = g.sp0.toNat - 16
  exact ptr_sub_toNat g.sp0 (0xff0#12) 16 sext_ff0_toNat (by have := hg.sp_htif; omega)

theorem wr_slot_s0_addr (g : WRG) (hg : WRGOk g) :
    (wrSpE g + sign_extend (m := 64) (0x000#12)).toNat = g.sp0.toNat - 16 := by
  rw [addi0_env]
  exact wr_spE_toNat g hg

theorem wr_slot_ra_addr (g : WRG) (hg : WRGOk g) :
    (wrSpE g + sign_extend (m := 64) (0x008#12)).toNat = g.sp0.toNat - 8 := by
  have hE := wr_spE_toNat g hg
  have h32 : 32 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
  rw [ptr_addoff (wrSpE g) (0x008#12) 8 (by decide)
    (by rw [hE]; have := g.sp0.isLt; omega), hE]
  omega

theorem wr_errno_addr :
    (wrGpVal + sign_extend (m := 64) (0x4f8#12)).toNat = wrErrnoAddr := by decide

/-- `addi sp,sp,16` undoes the prologue's `addi sp,sp,-16`. -/
theorem wr_sp_restore (g : WRG) :
    wrSpE g + sign_extend (m := 64) (0x010#12) = g.sp0 :=
  sp_dec16_restore g.sp0

/-- `len ≠ -1`: the buffer fits in RAM, so `len.toNat` is far below `2^64-1`. -/
theorem wr_len_ne_neg1 (g : WRG) (hg : WRGOk g) :
    g.len ≠ 0xFFFFFFFFFFFFFFFF#64 := by
  intro h
  have h1 := congrArg BitVec.toNat h
  rw [hg.len_bytes,
    show (0xFFFFFFFFFFFFFFFF#64 : BitVec 64).toNat = 0xFFFFFFFFFFFFFFFF from by decide] at h1
  have := hg.hiram
  have := hg.lo
  omega

/-! ## Transporting the entry pins onto `wrM1` -/

/-- Any byte outside the spill window and the `errno` word survives the entry
block's write-log. -/
theorem wrM1_getElem_lo (g : WRG) (hg : WRGOk g) (k : Nat)
    (hstack : k < g.sp0.toNat - 16 ∨ g.sp0.toNat ≤ k)
    (herrno : k < wrErrnoAddr ∨ wrErrnoAddr + 4 ≤ k) :
    (wrM1 g)[k]? = g.m0[k]? := by
  have h32 : 32 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
  show (writeMap4
      (writeMap8
        (writeMap8 g.m0 ((wrSpE g + sign_extend (m := 64) (0x000#12)).toNat)
          (sdData_val g.s00))
        ((wrSpE g + sign_extend (m := 64) (0x008#12)).toNat) (sdData_val g.ra0))
      ((wrGpVal + sign_extend (m := 64) (0x4f8#12)).toNat) (swData 0#64))[k]?
    = g.m0[k]?
  rw [getElem_writeMap4_disjoint _ _ _ _ (by rw [wr_errno_addr]; omega),
    getElem_writeMap8_disjoint _ _ _ _ (by rw [wr_slot_ra_addr g hg]; omega),
    getElem_writeMap8_disjoint _ _ _ _ (by rw [wr_slot_s0_addr g hg]; omega)]

/-- Everything below the HTIF window (all code) survives the entry write-log. -/
theorem wrM1_agree_lo (g : WRG) (hg : WRGOk g) :
    ∀ j : Nat, j < tohostAddr → (wrM1 g)[j]? = g.m0[j]? := by
  intro j hj
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hw : wrErrnoAddr = 0x8001ba08 := rfl
  refine wrM1_getElem_lo g hg j ?_ ?_
  · left; have := hg.sp_htif; omega
  · left; omega


/-- Transport `_writeLoaded` across a memory that agrees below `tohostAddr`
(all `_write` code bytes sit below the HTIF window). -/
theorem writeLoaded_of_agree_lo {m1 m0 : Std.ExtHashMap Nat (BitVec 8)}
    (hlo : ∀ j : Nat, j < tohostAddr → m1[j]? = m0[j]?)
    (h : Vsa.Sim.Code._writeLoaded m0) : Vsa.Sim.Code._writeLoaded m1 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47⟩ := h
  exact ⟨(hlo 0x8000003c (by decide)).trans h0,
    (hlo 0x8000003d (by decide)).trans h1,
    (hlo 0x8000003e (by decide)).trans h2,
    (hlo 0x8000003f (by decide)).trans h3,
    (hlo 0x80000040 (by decide)).trans h4,
    (hlo 0x80000041 (by decide)).trans h5,
    (hlo 0x80000042 (by decide)).trans h6,
    (hlo 0x80000043 (by decide)).trans h7,
    (hlo 0x80000044 (by decide)).trans h8,
    (hlo 0x80000045 (by decide)).trans h9,
    (hlo 0x80000046 (by decide)).trans h10,
    (hlo 0x80000047 (by decide)).trans h11,
    (hlo 0x80000048 (by decide)).trans h12,
    (hlo 0x80000049 (by decide)).trans h13,
    (hlo 0x8000004a (by decide)).trans h14,
    (hlo 0x8000004b (by decide)).trans h15,
    (hlo 0x8000004c (by decide)).trans h16,
    (hlo 0x8000004d (by decide)).trans h17,
    (hlo 0x8000004e (by decide)).trans h18,
    (hlo 0x8000004f (by decide)).trans h19,
    (hlo 0x80000050 (by decide)).trans h20,
    (hlo 0x80000051 (by decide)).trans h21,
    (hlo 0x80000052 (by decide)).trans h22,
    (hlo 0x80000053 (by decide)).trans h23,
    (hlo 0x80000054 (by decide)).trans h24,
    (hlo 0x80000055 (by decide)).trans h25,
    (hlo 0x80000056 (by decide)).trans h26,
    (hlo 0x80000057 (by decide)).trans h27,
    (hlo 0x80000058 (by decide)).trans h28,
    (hlo 0x80000059 (by decide)).trans h29,
    (hlo 0x8000005a (by decide)).trans h30,
    (hlo 0x8000005b (by decide)).trans h31,
    (hlo 0x8000005c (by decide)).trans h32,
    (hlo 0x8000005d (by decide)).trans h33,
    (hlo 0x8000005e (by decide)).trans h34,
    (hlo 0x8000005f (by decide)).trans h35,
    (hlo 0x80000060 (by decide)).trans h36,
    (hlo 0x80000061 (by decide)).trans h37,
    (hlo 0x80000062 (by decide)).trans h38,
    (hlo 0x80000063 (by decide)).trans h39,
    (hlo 0x80000064 (by decide)).trans h40,
    (hlo 0x80000065 (by decide)).trans h41,
    (hlo 0x80000066 (by decide)).trans h42,
    (hlo 0x80000067 (by decide)).trans h43,
    (hlo 0x80000068 (by decide)).trans h44,
    (hlo 0x80000069 (by decide)).trans h45,
    (hlo 0x8000006a (by decide)).trans h46,
    (hlo 0x8000006b (by decide)).trans h47⟩

/-- Transport `_write_rLoaded` across a memory that agrees below `tohostAddr`
(all `_write_r` code bytes sit below the HTIF window). -/
theorem write_rLoaded_of_agree_lo {m1 m0 : Std.ExtHashMap Nat (BitVec 8)}
    (hlo : ∀ j : Nat, j < tohostAddr → m1[j]? = m0[j]?)
    (h : Vsa.Sim.Code._write_rLoaded m0) : Vsa.Sim.Code._write_rLoaded m1 := by
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63⟩, ⟨h64, h65, h66, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82, h83, h84, h85, h86, h87, h88, h89, h90, h91⟩⟩ := h
  exact ⟨⟨(hlo 0x800104fc (by decide)).trans h0,
    (hlo 0x800104fd (by decide)).trans h1,
    (hlo 0x800104fe (by decide)).trans h2,
    (hlo 0x800104ff (by decide)).trans h3,
    (hlo 0x80010500 (by decide)).trans h4,
    (hlo 0x80010501 (by decide)).trans h5,
    (hlo 0x80010502 (by decide)).trans h6,
    (hlo 0x80010503 (by decide)).trans h7,
    (hlo 0x80010504 (by decide)).trans h8,
    (hlo 0x80010505 (by decide)).trans h9,
    (hlo 0x80010506 (by decide)).trans h10,
    (hlo 0x80010507 (by decide)).trans h11,
    (hlo 0x80010508 (by decide)).trans h12,
    (hlo 0x80010509 (by decide)).trans h13,
    (hlo 0x8001050a (by decide)).trans h14,
    (hlo 0x8001050b (by decide)).trans h15,
    (hlo 0x8001050c (by decide)).trans h16,
    (hlo 0x8001050d (by decide)).trans h17,
    (hlo 0x8001050e (by decide)).trans h18,
    (hlo 0x8001050f (by decide)).trans h19,
    (hlo 0x80010510 (by decide)).trans h20,
    (hlo 0x80010511 (by decide)).trans h21,
    (hlo 0x80010512 (by decide)).trans h22,
    (hlo 0x80010513 (by decide)).trans h23,
    (hlo 0x80010514 (by decide)).trans h24,
    (hlo 0x80010515 (by decide)).trans h25,
    (hlo 0x80010516 (by decide)).trans h26,
    (hlo 0x80010517 (by decide)).trans h27,
    (hlo 0x80010518 (by decide)).trans h28,
    (hlo 0x80010519 (by decide)).trans h29,
    (hlo 0x8001051a (by decide)).trans h30,
    (hlo 0x8001051b (by decide)).trans h31,
    (hlo 0x8001051c (by decide)).trans h32,
    (hlo 0x8001051d (by decide)).trans h33,
    (hlo 0x8001051e (by decide)).trans h34,
    (hlo 0x8001051f (by decide)).trans h35,
    (hlo 0x80010520 (by decide)).trans h36,
    (hlo 0x80010521 (by decide)).trans h37,
    (hlo 0x80010522 (by decide)).trans h38,
    (hlo 0x80010523 (by decide)).trans h39,
    (hlo 0x80010524 (by decide)).trans h40,
    (hlo 0x80010525 (by decide)).trans h41,
    (hlo 0x80010526 (by decide)).trans h42,
    (hlo 0x80010527 (by decide)).trans h43,
    (hlo 0x80010528 (by decide)).trans h44,
    (hlo 0x80010529 (by decide)).trans h45,
    (hlo 0x8001052a (by decide)).trans h46,
    (hlo 0x8001052b (by decide)).trans h47,
    (hlo 0x8001052c (by decide)).trans h48,
    (hlo 0x8001052d (by decide)).trans h49,
    (hlo 0x8001052e (by decide)).trans h50,
    (hlo 0x8001052f (by decide)).trans h51,
    (hlo 0x80010530 (by decide)).trans h52,
    (hlo 0x80010531 (by decide)).trans h53,
    (hlo 0x80010532 (by decide)).trans h54,
    (hlo 0x80010533 (by decide)).trans h55,
    (hlo 0x80010534 (by decide)).trans h56,
    (hlo 0x80010535 (by decide)).trans h57,
    (hlo 0x80010536 (by decide)).trans h58,
    (hlo 0x80010537 (by decide)).trans h59,
    (hlo 0x80010538 (by decide)).trans h60,
    (hlo 0x80010539 (by decide)).trans h61,
    (hlo 0x8001053a (by decide)).trans h62,
    (hlo 0x8001053b (by decide)).trans h63⟩,
   ⟨(hlo 0x8001053c (by decide)).trans h64,
    (hlo 0x8001053d (by decide)).trans h65,
    (hlo 0x8001053e (by decide)).trans h66,
    (hlo 0x8001053f (by decide)).trans h67,
    (hlo 0x80010540 (by decide)).trans h68,
    (hlo 0x80010541 (by decide)).trans h69,
    (hlo 0x80010542 (by decide)).trans h70,
    (hlo 0x80010543 (by decide)).trans h71,
    (hlo 0x80010544 (by decide)).trans h72,
    (hlo 0x80010545 (by decide)).trans h73,
    (hlo 0x80010546 (by decide)).trans h74,
    (hlo 0x80010547 (by decide)).trans h75,
    (hlo 0x80010548 (by decide)).trans h76,
    (hlo 0x80010549 (by decide)).trans h77,
    (hlo 0x8001054a (by decide)).trans h78,
    (hlo 0x8001054b (by decide)).trans h79,
    (hlo 0x8001054c (by decide)).trans h80,
    (hlo 0x8001054d (by decide)).trans h81,
    (hlo 0x8001054e (by decide)).trans h82,
    (hlo 0x8001054f (by decide)).trans h83,
    (hlo 0x80010550 (by decide)).trans h84,
    (hlo 0x80010551 (by decide)).trans h85,
    (hlo 0x80010552 (by decide)).trans h86,
    (hlo 0x80010553 (by decide)).trans h87,
    (hlo 0x80010554 (by decide)).trans h88,
    (hlo 0x80010555 (by decide)).trans h89,
    (hlo 0x80010556 (by decide)).trans h90,
    (hlo 0x80010557 (by decide)).trans h91⟩⟩


theorem wrM1_code (g : WRG) (hg : WRGOk g) : Vsa.Sim.Code._writeLoaded (wrM1 g) :=
  writeLoaded_of_agree_lo (wrM1_agree_lo g hg) hg.code

theorem wrM1_codeR (g : WRG) (hg : WRGOk g) : Vsa.Sim.Code._write_rLoaded (wrM1 g) :=
  write_rLoaded_of_agree_lo (wrM1_agree_lo g hg) hg.codeR

/-- The buffer byte pins survive onto `wrM1` (buffer disjoint from both store
windows). -/
theorem wrM1_pins (g : WRG) (hg : WRGOk g) :
    ∀ i, (h : i < g.bytes.length) → (wrM1 g)[g.buf.toNat + i]? = some (g.bytes[i]'h) := by
  intro i h
  refine (wrM1_getElem_lo g hg (g.buf.toNat + i) ?_ ?_).trans (hg.pins i h)
  · rcases hg.buf_stack_disj with hd | hd
    · left; omega
    · right; omega
  · rcases hg.buf_errno_disj with hd | hd
    · left; omega
    · right; omega

/-! ## The P1 ghost bundle at the call site -/

/-- P1's ghost bundle as seen at the `jal _write`: `ra0` is the link
`0x80010524`, `sp0` the framed stack pointer, `s00` the CURRENT `s0`
(= `reent`, set by `mv s0,a0`), memory the entry-block image `wrM1`. -/
def wrWG1 (g : WRG) : WG :=
  { buf := g.buf, len := g.len, ra0 := 0x80010524#64,
    sp0 := wrSpE g, gp0 := wrGpVal, s00 := g.reent, sv := g.sv,
    bytes := g.bytes, m0 := wrM1 g, out0 := g.out0 }

theorem wrWG1_ok (g : WRG) (hg : WRGOk g) : WGOk (wrWG1 g) :=
  { len_bytes := hg.len_bytes
    nowrap := hg.nowrap
    lo := hg.lo
    hiram := hg.hiram
    htif := hg.htif
    pins := wrM1_pins g hg
    code := wrM1_code g hg
    ra_align := by
      show (0x80010524#64 : BitVec 64).toNat % 4 = 0
      decide
    ra_fix := by
      show BitVec.update (0x80010524#64 + sign_extend (m := 64) (0x000#12)) 0 0#1
        = 0x80010524#64
      apply BitVec.eq_of_toNat_eq; decide }

/-! ## The epilogue's reload byte lists (the spilled store images) -/

/-- The 8 LE bytes the `ld ra,8(sp)` reads back — the `sd ra` store image. -/
def wrRaBytes (g : WRG) : List (BitVec 8) :=
  [(sdData_val g.ra0).extractLsb' 0 8, (sdData_val g.ra0).extractLsb' 8 8,
   (sdData_val g.ra0).extractLsb' 16 8, (sdData_val g.ra0).extractLsb' 24 8,
   (sdData_val g.ra0).extractLsb' 32 8, (sdData_val g.ra0).extractLsb' 40 8,
   (sdData_val g.ra0).extractLsb' 48 8, (sdData_val g.ra0).extractLsb' 56 8]

/-- The 8 LE bytes the `ld s0,0(sp)` reads back — the `sd s0` store image. -/
def wrS0Bytes (g : WRG) : List (BitVec 8) :=
  [(sdData_val g.s00).extractLsb' 0 8, (sdData_val g.s00).extractLsb' 8 8,
   (sdData_val g.s00).extractLsb' 16 8, (sdData_val g.s00).extractLsb' 24 8,
   (sdData_val g.s00).extractLsb' 32 8, (sdData_val g.s00).extractLsb' 40 8,
   (sdData_val g.s00).extractLsb' 48 8, (sdData_val g.s00).extractLsb' 56 8]

/-- The reloaded `ra` is the spilled `ra0` (`sext_reassemble`). -/
theorem wr_raBytes_val (g : WRG) : bytesVal MKind.ld (wrRaBytes g) = g.ra0 :=
  sext_reassemble g.ra0
    ((sdData_val g.ra0).extractLsb' 0 8) ((sdData_val g.ra0).extractLsb' 8 8)
    ((sdData_val g.ra0).extractLsb' 16 8) ((sdData_val g.ra0).extractLsb' 24 8)
    ((sdData_val g.ra0).extractLsb' 32 8) ((sdData_val g.ra0).extractLsb' 40 8)
    ((sdData_val g.ra0).extractLsb' 48 8) ((sdData_val g.ra0).extractLsb' 56 8)
    rfl rfl rfl rfl rfl rfl rfl rfl

/-- The reloaded `s0` is the spilled entry `s00`. -/
theorem wr_s0Bytes_val (g : WRG) : bytesVal MKind.ld (wrS0Bytes g) = g.s00 :=
  sext_reassemble g.s00
    ((sdData_val g.s00).extractLsb' 0 8) ((sdData_val g.s00).extractLsb' 8 8)
    ((sdData_val g.s00).extractLsb' 16 8) ((sdData_val g.s00).extractLsb' 24 8)
    ((sdData_val g.s00).extractLsb' 32 8) ((sdData_val g.s00).extractLsb' 40 8)
    ((sdData_val g.s00).extractLsb' 48 8) ((sdData_val g.s00).extractLsb' 56 8)
    rfl rfl rfl rfl rfl rfl rfl rfl

/-- The `ld ra,8(sp)` byte pins on `wrM1`: a hit on the `sd ra` store image
(peel the `errno` `sw`, then read the `writeMap8` back). -/
theorem wrM1_ra_pins (g : WRG) (hg : WRGOk g) :
    LPins8 (wrM1 g) ((wrSpE g + sign_extend (m := 64) (0x008#12)).toNat)
      (wrRaBytes g) := by
  have h32 : 32 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
  have hpeel : ∀ k : Nat, k < 8 →
      (wrM1 g)[(wrSpE g + sign_extend (m := 64) (0x008#12)).toNat + k]?
        = (writeMap8
            (writeMap8 g.m0 ((wrSpE g + sign_extend (m := 64) (0x000#12)).toNat)
              (sdData_val g.s00))
            ((wrSpE g + sign_extend (m := 64) (0x008#12)).toNat)
            (sdData_val g.ra0))[(wrSpE g + sign_extend (m := 64) (0x008#12)).toNat + k]? := by
    intro k hk
    show (writeMap4 _ ((wrGpVal + sign_extend (m := 64) (0x4f8#12)).toNat) (swData 0#64))[_]? = _
    exact getElem_writeMap4_disjoint _ _ _ _
      (by rw [wr_errno_addr, wr_slot_ra_addr g hg]; have := hg.sp_errno; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hpeel 0 (by omega)
    rw [Nat.add_zero] at h
    exact lpin_of_present (h.trans (getElem_writeMap8_0 _ _ _))
  · exact lpin_of_present ((hpeel 1 (by omega)).trans (getElem_writeMap8_1 _ _ _))
  · exact lpin_of_present ((hpeel 2 (by omega)).trans (getElem_writeMap8_2 _ _ _))
  · exact lpin_of_present ((hpeel 3 (by omega)).trans (getElem_writeMap8_3 _ _ _))
  · exact lpin_of_present ((hpeel 4 (by omega)).trans (getElem_writeMap8_4 _ _ _))
  · exact lpin_of_present ((hpeel 5 (by omega)).trans (getElem_writeMap8_5 _ _ _))
  · exact lpin_of_present ((hpeel 6 (by omega)).trans (getElem_writeMap8_6 _ _ _))
  · exact lpin_of_present ((hpeel 7 (by omega)).trans (getElem_writeMap8_7 _ _ _))

/-- The `ld s0,0(sp)` byte pins on `wrM1`: peel the `sw` and the `sd ra`
window, then read the `sd s0` `writeMap8` back. -/
theorem wrM1_s0_pins (g : WRG) (hg : WRGOk g) :
    LPins8 (wrM1 g) ((wrSpE g + sign_extend (m := 64) (0x000#12)).toNat)
      (wrS0Bytes g) := by
  have h32 : 32 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
  have hpeel : ∀ k : Nat, k < 8 →
      (wrM1 g)[(wrSpE g + sign_extend (m := 64) (0x000#12)).toNat + k]?
        = (writeMap8 g.m0 ((wrSpE g + sign_extend (m := 64) (0x000#12)).toNat)
            (sdData_val g.s00))[(wrSpE g + sign_extend (m := 64) (0x000#12)).toNat + k]? := by
    intro k hk
    show (writeMap4 _ ((wrGpVal + sign_extend (m := 64) (0x4f8#12)).toNat) (swData 0#64))[_]? = _
    rw [getElem_writeMap4_disjoint _ _ _ _
      (by rw [wr_errno_addr, wr_slot_s0_addr g hg]; have := hg.sp_errno; omega)]
    exact getElem_writeMap8_disjoint _ _ _ _
      (by rw [wr_slot_ra_addr g hg, wr_slot_s0_addr g hg]; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hpeel 0 (by omega)
    rw [Nat.add_zero] at h
    exact lpin_of_present (h.trans (getElem_writeMap8_0 _ _ _))
  · exact lpin_of_present ((hpeel 1 (by omega)).trans (getElem_writeMap8_1 _ _ _))
  · exact lpin_of_present ((hpeel 2 (by omega)).trans (getElem_writeMap8_2 _ _ _))
  · exact lpin_of_present ((hpeel 3 (by omega)).trans (getElem_writeMap8_3 _ _ _))
  · exact lpin_of_present ((hpeel 4 (by omega)).trans (getElem_writeMap8_4 _ _ _))
  · exact lpin_of_present ((hpeel 5 (by omega)).trans (getElem_writeMap8_5 _ _ _))
  · exact lpin_of_present ((hpeel 6 (by omega)).trans (getElem_writeMap8_6 _ _ _))
  · exact lpin_of_present ((hpeel 7 (by omega)).trans (getElem_writeMap8_7 _ _ _))

/-! ## Per-seg `ChainFacts` lemmas (ONE `chain_facts` each) -/

/-- Entry block (`mv`-shuffle + two `sd` spills + the `errno` clear): the three
store `MemFacts` windows. -/
theorem wrEntry_facts (g : WRG) (hg : WRGOk g)
    (hcode : Vsa.Sim.Code._write_rLoaded g.m0) (lds : List (List (BitVec 8))) :
    ChainFacts g.m0 g.m0 (wrEntryL g) lds write_rX04fcSeg := by
  chain_facts hcode with "Vsa.Sim.Code._write_r_at_"
  · -- sd s0,0(sp')
    show 0x80000000 ≤ (wrSpE g + sign_extend (m := 64) (0x000#12)).toNat ∧
      (wrSpE g + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (wrSpE g + sign_extend (m := 64) (0x000#12)).toNat ∧
      (wrSpE g + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0
    rw [wr_slot_s0_addr g hg]
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hg.sp_htif
    have := hg.sp_hi
    have := hg.sp_align
    refine ⟨by omega, by omega, by omega, by omega⟩
  · -- sd ra,8(sp')
    show 0x80000000 ≤ (wrSpE g + sign_extend (m := 64) (0x008#12)).toNat ∧
      (wrSpE g + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (wrSpE g + sign_extend (m := 64) (0x008#12)).toNat ∧
      (wrSpE g + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0
    rw [wr_slot_ra_addr g hg]
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hg.sp_htif
    have := hg.sp_hi
    have := hg.sp_align
    refine ⟨by omega, by omega, by omega, by omega⟩
  · -- sw zero,1272(gp)
    show 0x80000000 ≤ (wrGpVal + sign_extend (m := 64) (0x4f8#12)).toNat ∧
      (wrGpVal + sign_extend (m := 64) (0x4f8#12)).toNat + 4 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (wrGpVal + sign_extend (m := 64) (0x4f8#12)).toNat ∧
      (wrGpVal + sign_extend (m := 64) (0x4f8#12)).toNat % 4 = 0
    exact ⟨by decide, by decide, by decide, by decide⟩

/-- The `beq a0,a5` FALL arm (`a0 = len ≠ -1`). -/
theorem wrBeqF_facts (g : WRG) (hg : WRGOk g)
    (m : Std.ExtHashMap Nat (BitVec 8))
    (hcode : Vsa.Sim.Code._write_rLoaded m) (lds : List (List (BitVec 8))) :
    ChainFacts m m (write_rX0524FL g.len) lds write_rX0524FSeg := by
  chain_facts hcode with "Vsa.Sim.Code._write_r_at_"
  · -- the branch guard (`li a5,-1`'s computed value): symbolic-reduce, then the
    -- `len ≠ -1` fact (deep `rfl`/`show` through `mkLine` overflows — the
    -- `seg_guard_close` recipe, finished by hand since `len` is symbolic)
    simp only [runGM, stepGM, wvalM, srcVal, lookupG, eraseG, guardB,
      write_rX0524FL,
      show (mkLine 0x80010524#64 0xfff00793#32).kind = MKind.addi from rfl,
      show (mkLine 0x80010524#64 0xfff00793#32).rd = 15 from rfl,
      show (mkLine 0x80010524#64 0xfff00793#32).rs1 = 0 from rfl,
      show (mkLine 0x80010524#64 0xfff00793#32).imm = 0xfff#12 from rfl,
      Nat.reduceEqDiff, if_true, if_false, Option.getD_some]
    rw [show (0#64 + sign_extend (m := 64) (0xfff#12) : BitVec 64)
      = 0xFFFFFFFFFFFFFFFF#64 from by apply BitVec.eq_of_toNat_eq; decide]
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact wr_len_ne_neg1 g hg

/-- The epilogue (`ld ra,8(sp) ; ld s0,0(sp) ; addi sp,sp,16 ▷ ret`): the two
reload windows/pins off the `wrM1` store images + the `jr` return-target
alignment. -/
theorem wrEpi_facts (g : WRG) (hg : WRGOk g)
    (hcode : Vsa.Sim.Code._write_rLoaded (wrM1 g)) :
    ChainFacts (wrM1 g) (wrM1 g) (write_rX052cL (wrSpE g))
      [wrRaBytes g, wrS0Bytes g] write_rX052cSeg := by
  chain_facts hcode with "Vsa.Sim.Code._write_r_at_"
  · -- ld ra,8(sp)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0x80000000 ≤ (wrSpE g + sign_extend (m := 64) (0x008#12)).toNat
      rw [wr_slot_ra_addr g hg]
      have ht : tohostAddr = 0x8001ad00 := rfl
      have := hg.sp_htif
      omega
    · show (wrSpE g + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000
      rw [wr_slot_ra_addr g hg]
      have := hg.sp_hi
      have := hg.sp_htif
      omega
    · show (wrSpE g + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (wrSpE g + sign_extend (m := 64) (0x008#12)).toNat
      rw [wr_slot_ra_addr g hg]
      right
      have := hg.sp_htif
      omega
    · show (wrSpE g + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0
      rw [wr_slot_ra_addr g hg]
      have := hg.sp_htif
      have := hg.sp_align
      omega
    · exact wrM1_ra_pins g hg
  · -- ld s0,0(sp)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0x80000000 ≤ (wrSpE g + sign_extend (m := 64) (0x000#12)).toNat
      rw [wr_slot_s0_addr g hg]
      have ht : tohostAddr = 0x8001ad00 := rfl
      have := hg.sp_htif
      omega
    · show (wrSpE g + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000
      rw [wr_slot_s0_addr g hg]
      have := hg.sp_hi
      have := hg.sp_htif
      omega
    · show (wrSpE g + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (wrSpE g + sign_extend (m := 64) (0x000#12)).toNat
      rw [wr_slot_s0_addr g hg]
      right
      have := hg.sp_htif
      omega
    · show (wrSpE g + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0
      rw [wr_slot_s0_addr g hg]
      have := hg.sp_htif
      have := hg.sp_align
      omega
    · exact wrM1_s0_pins g hg
  · -- jr: return-target alignment (the reloaded ra0)
    show (BitVec.update (bytesVal MKind.ld (wrRaBytes g)
        + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
    rw [wr_raBytes_val g, hg.ra_fix]
    exact hg.ra_align

/-! ## Write-log collapse for the store-free segs

(`rfl` directly on `writeLog (wrM1 g) log = wrM1 g` sends the unifier into the
`ExtHashMap` internals — collapse the computed log to `[]` FIRST.) -/

theorem writeLog_nil (m : Std.ExtHashMap Nat (BitVec 8)) : writeLog m [] = m := rfl

theorem wrBeqF_log_nil (len : BitVec 64) :
    (evalBlocks write_rX0524FSeg (SegEvalState.init (write_rX0524FL len) [])).log
      = [] := rfl

theorem wrEpi_log_nil (g : WRG) :
    (evalBlocks write_rX052cSeg
      (SegEvalState.init (write_rX052cL (wrSpE g)) [wrRaBytes g, wrS0Bytes g])).log
      = [] := rfl

/-! ## Join-point predicates (one named-field structure per join) -/

/-- Parked at the `jal _write` (`0x80010520`), entry block done: arguments
shuffled (`a1 = buf`, `a2 = len`), frame stores landed (`mem = wrM1`), `s0`
now `reent`. -/
structure WRAtJal (g : WRG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = wrM1 g
  pc : c.σ.regs.get? Register.PC = some 0x80010520#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a1 : gprGet c.σ 11 = some g.buf
  a2 : gprGet c.σ 12 = some g.len
  sp : gprGet c.σ 2 = some (wrSpE g)
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.reent
  sregs : GHolds c.σ (sKeepL g.sv)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-- Parked at the epilogue (`0x8001052c`), `_write` returned and the branch
fell: `a0 = len`, frame intact on `wrM1`, console extended. -/
structure WRAtEpi (g : WRG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = wrM1 g
  pc : c.σ.regs.get? Register.PC = some 0x8001052c#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some g.len
  sp : gprGet c.σ 2 = some (wrSpE g)
  gp : gprGet c.σ 3 = some wrGpVal
  sregs : GHolds c.σ (sKeepL g.sv)
  out : c.σ.sailOutput = pushBytes g.out0 g.bytes
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-! ## The summary pre/post -/

/-- `_write_r`'s summary precondition (at the ABI entry `0x800104fc`):
`(a0,a1,a2,a3) = (reent, fd, buf, len)`, `gp` the linked binary's global
pointer, buffer/stack/errno side conditions in `ok`. -/
structure WriteRFnPre (g : WRG) (c : Config) : Prop where
  ok : WRGOk g
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = g.m0
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some g.reent
  a1 : gprGet c.σ 11 = some g.fd
  a2 : gprGet c.σ 12 = some g.buf
  a3 : gprGet c.σ 13 = some g.len
  ra : gprGet c.σ 1 = some g.ra0
  sp : gprGet c.σ 2 = some g.sp0
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.s00
  sregs : GHolds c.σ (sKeepL g.sv)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-- `_write_r`'s summary post: returned to `ra0` with `a0 = len`, callee-saved
`ra`/`sp`/`gp`/`s0` restored, memory = the entry-block image `wrM1` (the
`errno` clear and the stale spill slots ARE the footprint), console = entry
output ++ the buffer's byte string. -/
structure WriteRFnPost (g : WRG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = wrM1 g
  pc : c.σ.regs.get? Register.PC = some g.ra0
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some g.len
  ra : gprGet c.σ 1 = some g.ra0
  sp : gprGet c.σ 2 = some g.sp0
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.s00
  sregs : GHolds c.σ (sKeepL g.sv)
  out : c.σ.sailOutput = pushBytes g.out0 g.bytes
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-! ## Arm Triples -/

/-- Entry block: `0x800104fc → 0x80010520` (parked at the `jal`). -/
theorem wrEntryArm (g : WRG) (hg : WRGOk g) :
    Triple (fun c => PCAt 0x800104fc#64 c ∧ WriteRFnPre g c) (WRAtJal g) := by
  have T := segRowFramed write_rX04fcSeg (wrEntryL g) []
    0x800104fc#64 g.m0 (sKeepL g.sv) g.out0 (0#4)
    (by show ChainOK 0x800104fc#64 [11, 2, 8, 12, 10, 13, 1, 3] write_rX04fcSeg; decide)
    (by show FrameOK [9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] write_rX04fcSeg
        decide)
  intro c hc
  obtain ⟨hpc, hp⟩ := hc
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hp.good, hp.mem, hpc, hp.minstret,
        ⟨hp.a1, hp.sp, hp.s0, hp.a2, hp.a0, hp.a3, hp.ra, hp.gp, trivial⟩,
        by show KeysOK [11, 2, 8, 12, 10, 13, 1, 3]; decide,
        by rw [hp.mem]; exact wrEntry_facts g hg hg.codeR [], hp.tick⟩
      keep := hp.sregs
      out := hp.out
      pw := hp.pw
      th := hp.th }
  refine ⟨c1, hs1, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by rw [h1.mem]; rfl
      pc := by rw [h1.pc]; rfl
      minstret := h1.minstret
      a1 := by
        have h := gholds_lookup (n := 11)
          (v := g.buf + sign_extend (m := 64) (0x000#12)) _ h1.regs (by rfl)
        rwa [addi0_env] at h
      a2 := by
        have h := gholds_lookup (n := 12)
          (v := g.len + sign_extend (m := 64) (0x000#12)) _ h1.regs (by rfl)
        rwa [addi0_env] at h
      sp := gholds_lookup (v := wrSpE g) _ h1.regs (by rfl)
      gp := gholds_lookup (v := wrGpVal) _ h1.regs (by rfl)
      s0 := by
        have h := gholds_lookup (n := 8)
          (v := g.reent + sign_extend (m := 64) (0x000#12)) _ h1.regs (by rfl)
        rwa [addi0_env] at h
      sregs := h1.keep
      out := h1.out
      pw := h1.pw
      th := h1.th }

/-- The `jal _write` SEAM: one `stepObs_jal` step from the parked config lands
at `_write`'s entry with P1's precondition established (`ra := 0x80010524`,
memory/args/frame transported by the `obs_jal_*` accessors). -/
theorem wrJalArm (g : WRG) (hg : WRGOk g) :
    Triple (WRAtJal g)
      (fun c => PCAt 0x8000003c#64 c ∧ WriteFnPre (wrWG1 g) c) := by
  intro c hA
  obtain ⟨vm1, hmi1⟩ := hA.minstret
  have hcR : Vsa.Sim.Code._write_rLoaded c.σ.mem := by
    rw [hA.mem]; exact wrM1_codeR g hg
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code._write_r_at_80010520 hcR
  obtain ⟨σ2, i2, hstep, hi2, hG2, hmem2, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x80010520#64) vm1 (0xb1def0ef#32) (0x1efb1c#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80010520#64) 4)
      (0xef#8) (0xf0#8) (0xde#8) (0xb1#8)
      hA.good hA.pc hmi1 hb0 hb1 hb2 hb3
      (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide)
      (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_b1def0ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hA.good.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hA.good.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hA.good.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x80010520#64) 4))
      hA.tick
  refine ⟨⟨σ2, i2, c.steps + 1⟩, Steps.head hstep (Steps.refl _), ?_, ?_⟩
  · show σ2.regs.get? Register.PC = some 0x8000003c#64
    rw [obs_jal_pc_env hobs]
    rw [show (0x80010520#64 + sign_extend (m := 64) (0x1efb1c#21) : BitVec 64)
      = 0x8000003c#64 from by decide]
  · exact
      { ok := wrWG1_ok g hg
        good := hG2
        tick := hi2
        mem := hmem2.trans hA.mem
        minstret := obs_jal_minstret_env hobs
        a1 := obs_jal_other_env hobs Register.x11 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.a1
        a2 := obs_jal_other_env hobs Register.x12 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.a2
        ra := by
          have h := obs_jal_rd_env hobs (by decide) (by decide) (by decide)
            (by decide) (by decide)
          rwa [show BitVec.addInt (0x80010520#64) 4 = 0x80010524#64 from by decide] at h
        sp := obs_jal_other_env hobs Register.x2 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.sp
        gp := obs_jal_other_env hobs Register.x3 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.gp
        s0 := obs_jal_other_env hobs Register.x8 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.s0
        sregs := by
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -⟩ := hA.sregs
          exact ⟨obs_jal_other_env hobs Register.x9 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) h1,
            obs_jal_other_env hobs Register.x18 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) h2,
            obs_jal_other_env hobs Register.x19 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) h3,
            obs_jal_other_env hobs Register.x20 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) h4,
            obs_jal_other_env hobs Register.x21 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) h5,
            obs_jal_other_env hobs Register.x22 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) h6,
            obs_jal_other_env hobs Register.x23 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) h7,
            obs_jal_other_env hobs Register.x24 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) h8,
            obs_jal_other_env hobs Register.x25 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) h9,
            obs_jal_other_env hobs Register.x26 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) h10,
            obs_jal_other_env hobs Register.x27 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) h11,
            trivial⟩
        out := hobs.2.trans ((sailOutput_sigmaPost_jal c.σ (0x80010520#64) vm1
          (0x1efb1c#21) Register.x1 (BitVec.addInt (0x80010520#64) 4)).trans hA.out)
        pw := obs_jal_other_env hobs Register.htif_payload_writes (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hA.pw
        th := by
          obtain ⟨v, hv⟩ := hA.th
          exact ⟨v, obs_jal_other_env hobs Register.htif_tohost (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩ }

/-- The `beq a0,a5` twin at `0x80010524`, FALL route (`len ≠ -1`): from P1's
exit to the epilogue entry. -/
theorem wrBeqArm (g : WRG) (hg : WRGOk g) :
    Triple (WriteFnPost (wrWG1 g)) (WRAtEpi g) := by
  have T := segRowFramed write_rX0524FSeg (write_rX0524FL g.len) []
    0x80010524#64 (wrM1 g)
    ([(2, wrSpE g), (3, wrGpVal)] ++ sKeepL g.sv)
    (pushBytes g.out0 g.bytes) (0#4)
    (by show ChainOK 0x80010524#64 [10] write_rX0524FSeg; decide)
    (by show FrameOK [2, 3, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
          write_rX0524FSeg
        decide)
  intro c hP
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hP.good, hP.mem, hP.pc, hP.minstret, ⟨hP.a0, trivial⟩,
        by show KeysOK [10]; decide,
        by rw [show c.σ.mem = wrM1 g from hP.mem];
           exact wrBeqF_facts g hg (wrM1 g) (wrM1_codeR g hg) [], hP.tick⟩
      keep := ⟨hP.sp, hP.gp, hP.sregs⟩
      out := hP.out
      pw := hP.pw
      th := hP.th }
  obtain ⟨hksp, hkgp, hsk⟩ := h1.keep
  refine ⟨c1, hs1, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by rw [h1.mem, wrBeqF_log_nil g.len, writeLog_nil]
      pc := by rw [h1.pc]; rfl
      minstret := h1.minstret
      a0 := gholds_lookup (v := g.len) _ h1.regs (by rfl)
      sp := hksp
      gp := hkgp
      sregs := hsk
      out := h1.out
      pw := h1.pw
      th := h1.th }

/-- The epilogue through the `ret`: `ra`/`s0` reloaded off the `wrM1` spill
images, `sp` restored, PC := `ra0`. -/
theorem wrEpiArm (g : WRG) (hg : WRGOk g) :
    Triple (WRAtEpi g) (WriteRFnPost g) := by
  have T := segRowFramed write_rX052cSeg (write_rX052cL (wrSpE g))
    [wrRaBytes g, wrS0Bytes g]
    0x8001052c#64 (wrM1 g)
    ([(10, g.len), (3, wrGpVal)] ++ sKeepL g.sv)
    (pushBytes g.out0 g.bytes) (0#4)
    (by show ChainOK 0x8001052c#64 [2] write_rX052cSeg; decide)
    (by show FrameOK [10, 3, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
          write_rX052cSeg
        decide)
  intro c hE
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hE.good, hE.mem, hE.pc, hE.minstret, ⟨hE.sp, trivial⟩,
        by show KeysOK [2]; decide,
        by rw [show c.σ.mem = wrM1 g from hE.mem]; exact wrEpi_facts g hg (wrM1_codeR g hg),
        hE.tick⟩
      keep := ⟨hE.a0, hE.gp, hE.sregs⟩
      out := hE.out
      pw := hE.pw
      th := hE.th }
  obtain ⟨hka0, hkgp, hsk⟩ := h1.keep
  refine ⟨c1, hs1, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by rw [h1.mem, wrEpi_log_nil g, writeLog_nil]
      pc := by
        rw [h1.pc]
        show some (BitVec.update (bytesVal MKind.ld (wrRaBytes g)
          + sign_extend (m := 64) (0x000#12)) 0 0#1) = some g.ra0
        rw [wr_raBytes_val g, hg.ra_fix]
      minstret := h1.minstret
      a0 := hka0
      ra := by
        have h := gholds_lookup (n := 1)
          (v := bytesVal MKind.ld (wrRaBytes g)) _ h1.regs (by rfl)
        rwa [wr_raBytes_val g] at h
      sp := by
        have h := gholds_lookup (n := 2)
          (v := wrSpE g + sign_extend (m := 64) (0x010#12)) _ h1.regs (by rfl)
        rwa [wr_sp_restore g] at h
      gp := hkgp
      s0 := by
        have h := gholds_lookup (n := 8)
          (v := bytesVal MKind.ld (wrS0Bytes g)) _ h1.regs (by rfl)
        rwa [wr_s0Bytes_val g] at h
      sregs := hsk
      out := h1.out
      pw := h1.pw
      th := h1.th }

/-! ## The summary -/

/-- **The `_write_r` whole-function summary** (gen_fn pilot P2): from the ABI
entry with the buffer pinned, `_write_r` returns to `ra0` with `a0 = len`,
callee-saved registers restored, memory = the entry-block store image `wrM1`
(the `errno` clear + the stale spill slots), and the console output extended by
EXACTLY the buffer's byte string — the P1 `_write` summary spliced through the
`jal` seam. -/
theorem write_r_summary (g : WRG) :
    FnSummary 0x800104fc#64 (WriteRFnPre g) (WriteRFnPost g) := by
  refine ⟨?_⟩
  intro c hc
  have hg := hc.2.ok
  obtain ⟨c1, hs1, h1⟩ := wrEntryArm g hg c hc
  obtain ⟨c2, hs2, h2⟩ := wrJalArm g hg c1 h1
  obtain ⟨c3, hs3, h3⟩ := (write_summary (wrWG1 g)).run c2 h2
  obtain ⟨c4, hs4, h4⟩ := wrBeqArm g hg c3 h3
  obtain ⟨c5, hs5, h5⟩ := wrEpiArm g hg c4 h4
  exact ⟨c5, (((hs1.trans hs2).trans hs3).trans hs4).trans hs5, h5⟩

#print axioms write_r_summary

end Vsa.Sim
