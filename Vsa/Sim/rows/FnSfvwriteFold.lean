import Vsa.Sim.rows.FnSfvwrite_r
import Vsa.Sim.rows.FnSwriteFold
import Vsa.Sim.rows.TransportSfvwrite_r
import Vsa.Sim.SnprintfSitesRet5
import Vsa.Sim.WriteLogNF
import Vsa.Sim.DecodeTable.Batch01Part29

/-!
# `__sfvwrite_r` — the UNBUFFERED (`__SNBF`) arm whole-function summary fold

The io-DAG crux (run1 io lane): from the ABI entry `0x8000de8c` with
`(a0,a1,a2) = (reent, fp, uio)`, the real-stdout pin set (`__SWR ∧ __SNBF`
flags, non-null `_bf._base`, `fp->_write = __swrite`, `fp->_cookie = fp`) and
a SINGLE-iov uio (`uio_resid = iov_len = len ≠ 0`, `iov_base = buf`),
`__sfvwrite_r` takes the unbuffered route: spills `s0/s4/s5/ra` + `s1/s2/s3/s6`,
loads the iov, clamps (no-op for `len ≤ 0x7FFFFC00`), and calls
`fp->_write(reent, fp->_cookie, buf, len)` through the **`jalr a5` indirect
seam** (`stepObs_jalr`, the target pinned to `__swrite`'s entry off the loaded
image) — the landed `swrite_summary` (P3) carries the whole
`__swrite → _write_r → _write → HTIF putchar` chain, appending EXACTLY the
buffer's byte string to the console.  The single full write zeroes
`uio_resid`, the loop exits, the spills reload, and control returns to `ra0`
with `a0 = 0` (success).

Architecture = the P2/P3 fold recipe over the `--route`-pruned generated arms
(`rows/FnSfvwrite_r.lean`): ghosts `SFVG`, static side conditions `SFVGOk`
(named fields), reified write logs (`WriteLogNF` for all pin transport),
`segRowFramed` per block, `stepObs_jalr` at the seam, `FnSummary`-shaped
`sfvwrite_unbuf_summary`.

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

/-! ## Byte-list helpers (the `bytes8`/`Pin8` bridge) -/

/-- The 8 LE bytes of a 64-bit value as stored/pinned in memory (the `sd`
store-image shape — `Pin8`'s exact byte spellings). -/
def bytes8 (v : BitVec 64) : List (BitVec 8) :=
  [(sdData_val v).extractLsb' 0 8, (sdData_val v).extractLsb' 8 8,
   (sdData_val v).extractLsb' 16 8, (sdData_val v).extractLsb' 24 8,
   (sdData_val v).extractLsb' 32 8, (sdData_val v).extractLsb' 40 8,
   (sdData_val v).extractLsb' 48 8, (sdData_val v).extractLsb' 56 8]

/-- An `ld` over `bytes8 v` reassembles `v`. -/
theorem bytes8_val (v : BitVec 64) : bytesVal MKind.ld (bytes8 v) = v :=
  sext_reassemble v _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl

/-- `Pin8` (presence) gives `LPins8` at the `bytes8` list.  Since wave 48k
`LPins8` is the TOTAL read, so each conjunct lifts through `lpin_of_present`. -/
theorem lpins8_of_pin8 {m : Std.ExtHashMap Nat (BitVec 8)} {a : Nat} {v : BitVec 64}
    (h : Pin8 m a v) : LPins8 m a (bytes8 v) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := h
  exact ⟨lpin_of_present p0, lpin_of_present p1, lpin_of_present p2, lpin_of_present p3,
    lpin_of_present p4, lpin_of_present p5, lpin_of_present p6, lpin_of_present p7⟩

/-- Peel ONE disjoint 8-byte store image off a `Pin8` — the in-block
store-then-load transport.  A load AFTER stores in the same block gets its
`MemFacts` pins goal over the `stepMemM`-threaded `writeMap8` TOWER;
`show`-converting that memory back to the named base image forces an
`isDefEq` whnf of two abstract `ExtHashMap.insert` towers (elaborator stack
overflow).  Instead: leave the memory a metavar (`show LPins8 _ (addr) _`),
peel outermost store first, close on the base image. -/
theorem pin8_peel_sd {m : Std.ExtHashMap Nat (BitVec 8)}
    (a' : Nat) (d : BitVec 64) {a : Nat} {v : BitVec 64}
    (hd : a + 8 ≤ a' ∨ a' + 8 ≤ a) (h : Pin8 m a v) :
    Pin8 (writeMap8 m a' (sdData_val d)) a v := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := h
  exact ⟨(getElem_writeMap8_disjoint _ _ _ _ (by omega)).trans p0,
    (getElem_writeMap8_disjoint _ _ _ _ (by omega)).trans p1,
    (getElem_writeMap8_disjoint _ _ _ _ (by omega)).trans p2,
    (getElem_writeMap8_disjoint _ _ _ _ (by omega)).trans p3,
    (getElem_writeMap8_disjoint _ _ _ _ (by omega)).trans p4,
    (getElem_writeMap8_disjoint _ _ _ _ (by omega)).trans p5,
    (getElem_writeMap8_disjoint _ _ _ _ (by omega)).trans p6,
    (getElem_writeMap8_disjoint _ _ _ _ (by omega)).trans p7⟩

/-! ## Ghosts -/

/-- The `__sfvwrite_r` (unbuffered arm) summary ghosts. -/
structure SFVG where
  /-- `a0`: the reent pointer (passed through to `fp->_write`). -/
  reent : BitVec 64
  /-- `a1`: the `FILE*`. -/
  fp : BitVec 64
  /-- `a2`: the `__suio*`. -/
  uio : BitVec 64
  /-- `uio->uio_iov` (the single iov's address). -/
  iovp : BitVec 64
  /-- `iov_base`. -/
  buf : BitVec 64
  /-- `iov_len = uio_resid` (single-iov pin). -/
  len : BitVec 64
  /-- the FILE `_flags` halfword bytes at `fp+16/17` (LE). -/
  fl0 : BitVec 8
  fl1 : BitVec 8
  /-- the FILE `_file` (fd) halfword bytes at `fp+18/19` (consumed by
  `__swrite`'s summary; value unconstrained). -/
  fd0 : BitVec 8
  fd1 : BitVec 8
  /-- `fp->_bf._base` (≠ 0 on the pinned route). -/
  base : BitVec 64
  ra0 : BitVec 64
  sp0 : BitVec 64
  /-- entry `s0` (spilled at `sp0-16`, restored at exit). -/
  s00 : BitVec 64
  /-- entry `s1..s11` (s1..s6 spilled/restored; s7..s11 kept). -/
  sv : SRegs
  bytes : List (BitVec 8)
  m0 : Std.ExtHashMap Nat (BitVec 8)
  out0 : Array String

/-- The stack pointer inside `__sfvwrite_r`'s frame (`sp0 - 96`). -/
def sfvSpE (g : SFVG) : BitVec 64 := g.sp0 + sign_extend (m := 64) (0xfa0#12)

/-- The loaded FILE flags halfword (`lh a3,16(a1)`), sign-extended. -/
def sfvFlags (g : SFVG) : BitVec 64 := bytesVal MKind.lh [g.fl0, g.fl1]

/-- The write-clamp constant (`lui s6,0x80000 ; xori s6,s6,-1024`), carried as
the computed expression so seg readback is `rfl`-shaped. -/
def sfvClamp : BitVec 64 :=
  sign_extend (m := 64) ((0x80000#20 : BitVec 20) +++ (0x000#12))
    ^^^ sign_extend (m := 64) (0xc00#12)

theorem sfvClamp_eq : sfvClamp = 0x7ffffc00#64 := by
  apply BitVec.eq_of_toNat_eq; decide

/-- The `sext.w a3,a3` image of `len` (the `a3` handed to `fp->_write`),
carried as the computed expression. -/
def sfvLenW (g : SFVG) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb (g.len + sign_extend (m := 64) (0x000#12)) 31 0)

/-- `sext.w` is the identity below `2^31`. -/
theorem sfvLenW_id (g : SFVG) (h : g.len.toNat < 2 ^ 31) : sfvLenW g = g.len := by
  show sign_extend (m := 64)
    (Sail.BitVec.extractLsb (g.len + sign_extend (m := 64) (0x000#12)) 31 0) = g.len
  rw [addi0_env]
  apply BitVec.eq_of_toNat_eq
  rw [sext32_toNat_small]
  · show (g.len.extractLsb 31 0).toNat = _
    rw [BitVec.extractLsb, BitVec.extractLsb'_toNat]
    simp only [Nat.shiftRight_zero]
    omega
  · show (g.len.extractLsb 31 0).toNat < 2 ^ 31
    rw [BitVec.extractLsb, BitVec.extractLsb'_toNat]
    simp only [Nat.shiftRight_zero]
    omega

/-! ## Static side conditions -/

/-- Static (config-independent) side conditions of the unbuffered-arm summary.
The `uio`/`iovp` windows sit at/above `sp0` (the caller's frame — true for
`_fputs_r`/`_fwrite_r`, which build the uio on their own stack); the FILE sits
below the whole grown frame (newlib's `__sf` in `.data`). -/
structure SFVGOk (g : SFVG) : Prop where
  -- the buffer (mirrors P1..P3)
  len_bytes : g.len.toNat = g.bytes.length
  len_ne : g.len ≠ 0#64
  base_ne : g.base ≠ 0#64
  len_le : g.len.toNat ≤ 0x7ffffc00
  nowrap : g.buf.toNat + g.bytes.length < 2 ^ 64
  lo : 0x80000000 ≤ g.buf.toNat
  hiram : g.buf.toNat + g.bytes.length ≤ 0x100000000
  htif : g.buf.toNat + g.bytes.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ g.buf.toNat
  pins : ∀ i, (h : i < g.bytes.length) → g.m0[g.buf.toNat + i]? = some (g.bytes[i]'h)
  -- the four code images (this fn + the __swrite→_write_r→_write chain)
  codeSf : Vsa.Sim.Code.__sfvwrite_rLoaded g.m0
  code : Vsa.Sim.Code._writeLoaded g.m0
  codeR : Vsa.Sim.Code._write_rLoaded g.m0
  codeS : Vsa.Sim.Code.__swriteLoaded g.m0
  -- return target
  ra_align : g.ra0.toNat % 4 = 0
  ra_fix : BitVec.update (g.ra0 + sign_extend (m := 64) (0x000#12)) 0 0#1 = g.ra0
  -- the grown frame [sp0-144, sp0): ours [sp0-96, sp0) + __swrite's
  -- [sp0-144, sp0-96) + _write_r's [sp0-112, sp0-96)
  sp_htif : tohostAddr + 16 ≤ g.sp0.toNat - 144
  sp_errno : wrErrnoAddr + 4 ≤ g.sp0.toNat - 144
  sp_hi : g.sp0.toNat ≤ 0x100000000
  sp_align : g.sp0.toNat % 8 = 0
  -- buffer vs frame/errno/FILE
  buf_stack_disj : g.buf.toNat + g.bytes.length ≤ g.sp0.toNat - 144
    ∨ g.sp0.toNat ≤ g.buf.toNat
  buf_errno_disj : g.buf.toNat + g.bytes.length ≤ wrErrnoAddr
    ∨ wrErrnoAddr + 4 ≤ g.buf.toNat
  buf_fp_disj : g.buf.toNat + g.bytes.length ≤ g.fp.toNat + 16
    ∨ g.fp.toNat + 20 ≤ g.buf.toNat
  -- buffer vs the uio windows (the resid write-back at uio+16)
  buf_uio_disj : g.buf.toNat + g.bytes.length ≤ g.uio.toNat
    ∨ g.uio.toNat + 24 ≤ g.buf.toNat
  -- the FILE window [fp+16, fp+72): flags/fd halfwords, _bf._base, _cookie,
  -- _write vector
  fl_pin0 : g.m0[g.fp.toNat + 16]? = some g.fl0
  fl_pin1 : g.m0[g.fp.toNat + 17]? = some g.fl1
  fd_pin0 : g.m0[g.fp.toNat + 18]? = some g.fd0
  fd_pin1 : g.m0[g.fp.toNat + 19]? = some g.fd1
  base_pins : Pin8 g.m0 (g.fp.toNat + 24) g.base
  cookie_pins : Pin8 g.m0 (g.fp.toNat + 48) g.fp
  wvec_pins : Pin8 g.m0 (g.fp.toNat + 64) 0x8000efd4#64
  fp_htif : tohostAddr + 16 ≤ g.fp.toNat + 16
  fp_hi : g.fp.toNat + 72 ≤ 0x100000000
  fp_align : g.fp.toNat % 8 = 0
  fp_below : g.fp.toNat + 72 ≤ g.sp0.toNat - 144
  -- the uio (single-iov: uio_iov at +0, uio_resid at +16 — iovcnt unread)
  iovp_pins : Pin8 g.m0 g.uio.toNat g.iovp
  resid_pins : Pin8 g.m0 (g.uio.toNat + 16) g.len
  uio_above : g.sp0.toNat ≤ g.uio.toNat
  uio_hi : g.uio.toNat + 24 ≤ 0x100000000
  uio_align : g.uio.toNat % 8 = 0
  -- the iov record (base at +0, len at +8)
  iov_base_pins : Pin8 g.m0 g.iovp.toNat g.buf
  iov_len_pins : Pin8 g.m0 (g.iovp.toNat + 8) g.len
  iov_above : g.sp0.toNat ≤ g.iovp.toNat
  iov_hi : g.iovp.toNat + 16 ≤ 0x100000000
  iov_align : g.iovp.toNat % 8 = 0
  -- FILE flags bits: __SWR (8) on, __SNBF (2) on, __SAPP (0x100) off
  swr_on : sfvFlags g &&& sign_extend (m := 64) (0x008#12) ≠ 0#64
  nbf_on : sfvFlags g &&& sign_extend (m := 64) (0x002#12) ≠ 0#64
  append_off : sfvFlags g &&& sign_extend (m := 64) (0x100#12) = 0#64

/-! ## Frame-address arithmetic -/

theorem sfv_spE_toNat (g : SFVG) (hg : SFVGOk g) :
    (sfvSpE g).toNat = g.sp0.toNat - 96 := by
  show (g.sp0 + sign_extend (m := 64) (0xfa0#12)).toNat = g.sp0.toNat - 96
  refine ptr_sub_toNat g.sp0 (0xfa0#12) 96 sext_fa0_toNat ?_
  have ht : tohostAddr = 0x8001ad00 := rfl
  have := hg.sp_htif
  omega

/-- Generic spill-slot address on the frame. -/
theorem sfv_slotAddr (g : SFVG) (hg : SFVGOk g) (imm : BitVec 12) (k : Nat)
    (himm : (sign_extend (m := 64) imm : BitVec 64).toNat = k) (hk : k ≤ 96) :
    (sfvSpE g + sign_extend (m := 64) imm).toNat = g.sp0.toNat - 96 + k := by
  have hE := sfv_spE_toNat g hg
  have ht : tohostAddr = 0x8001ad00 := rfl
  have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
  rw [ptr_addoff (sfvSpE g) imm k himm
    (by rw [hE]; have := hg.sp_hi; omega), hE]

theorem sfv_uioAddr (g : SFVG) (hg : SFVGOk g) :
    (g.uio + sign_extend (m := 64) (0x000#12)).toNat = g.uio.toNat :=
  by rw [addi0_env]

theorem sfv_residAddr (g : SFVG) (hg : SFVGOk g) :
    (g.uio + sign_extend (m := 64) (0x010#12)).toNat = g.uio.toNat + 16 :=
  ptr_addoff g.uio (0x010#12) 16 (by decide) (by have := hg.uio_hi; omega)

theorem sfv_flAddr (g : SFVG) (hg : SFVGOk g) :
    (g.fp + sign_extend (m := 64) (0x010#12)).toNat = g.fp.toNat + 16 :=
  ptr_addoff g.fp (0x010#12) 16 (by decide) (by have := hg.fp_hi; omega)

theorem sfv_baseAddr (g : SFVG) (hg : SFVGOk g) :
    (g.fp + sign_extend (m := 64) (0x018#12)).toNat = g.fp.toNat + 24 :=
  ptr_addoff g.fp (0x018#12) 24 (by decide) (by have := hg.fp_hi; omega)

theorem sfv_cookieAddr (g : SFVG) (hg : SFVGOk g) :
    (g.fp + sign_extend (m := 64) (0x030#12)).toNat = g.fp.toNat + 48 :=
  ptr_addoff g.fp (0x030#12) 48 (by decide) (by have := hg.fp_hi; omega)

theorem sfv_wvecAddr (g : SFVG) (hg : SFVGOk g) :
    (g.fp + sign_extend (m := 64) (0x040#12)).toNat = g.fp.toNat + 64 :=
  ptr_addoff g.fp (0x040#12) 64 (by decide) (by have := hg.fp_hi; omega)

theorem sfv_iovBaseAddr (g : SFVG) (hg : SFVGOk g) :
    (g.iovp + sign_extend (m := 64) (0x000#12)).toNat = g.iovp.toNat := by
  rw [addi0_env]

theorem sfv_iovLenAddr (g : SFVG) (hg : SFVGOk g) :
    (g.iovp + sign_extend (m := 64) (0x008#12)).toNat = g.iovp.toNat + 8 :=
  ptr_addoff g.iovp (0x008#12) 8 (by decide) (by have := hg.iov_hi; omega)

/-- `addi sp,sp,96` undoes the prologue. -/
theorem sfv_sp_restore (g : SFVG) :
    sfvSpE g + sign_extend (m := 64) (0x060#12) = g.sp0 :=
  sp_dec96_restore g.sp0

/-! ## The reified write logs and memory images -/

/-- Entry pin list of the `de94F` block (`a1 sp s0 s4 s5 ra a0 a2`). -/
def sfvL1 (g : SFVG) : GRegs :=
  sfvwrite_rXde94FL g.fp g.sp0 g.s00 g.sv.s4 g.sv.s5 g.ra0 g.reent g.uio

/-- `de94F`'s four spills: `s0@80, s4@48, s5@40, ra@88` (chain order). -/
def sfvLog1 (g : SFVG) : List WEntry :=
  [((sfvSpE g + sign_extend (m := 64) (0x050#12)).toNat, 8, g.s00),
   ((sfvSpE g + sign_extend (m := 64) (0x030#12)).toNat, 8, g.sv.s4),
   ((sfvSpE g + sign_extend (m := 64) (0x028#12)).toNat, 8, g.sv.s5),
   ((sfvSpE g + sign_extend (m := 64) (0x058#12)).toNat, 8, g.ra0)]
-- (the named `sfvE_*` views of these entries live below, after the images)

theorem sfvLog1_eq (g : SFVG) :
    (evalBlocks sfvwrite_rXde94FSeg
      (SegEvalState.init (sfvL1 g) [[g.fl0, g.fl1]])).log = sfvLog1 g := rfl

def sfvM1a (g : SFVG) : Std.ExtHashMap Nat (BitVec 8) :=
  writeLog g.m0 (sfvLog1 g)

/-- Entry pin list of the `dec8F` block (`s1 sp s2 s3 s6 a3 s4`). -/
def sfvL2 (g : SFVG) : GRegs :=
  sfvwrite_rXdec8FL g.sv.s1 (sfvSpE g) g.sv.s2 g.sv.s3 g.sv.s6 (sfvFlags g) g.uio

/-- `dec8F`'s four spills: `s1@72, s2@64, s3@56, s6@32`. -/
def sfvLog2 (g : SFVG) : List WEntry :=
  [((sfvSpE g + sign_extend (m := 64) (0x048#12)).toNat, 8, g.sv.s1),
   ((sfvSpE g + sign_extend (m := 64) (0x040#12)).toNat, 8, g.sv.s2),
   ((sfvSpE g + sign_extend (m := 64) (0x038#12)).toNat, 8, g.sv.s3),
   ((sfvSpE g + sign_extend (m := 64) (0x020#12)).toNat, 8, g.sv.s6)]

theorem sfvLog2_eq (g : SFVG) :
    (evalBlocks sfvwrite_rXdec8FSeg
      (SegEvalState.init (sfvL2 g) [bytes8 g.iovp])).log = sfvLog2 g := rfl

def sfvM1 (g : SFVG) : Std.ExtHashMap Nat (BitVec 8) :=
  writeLog (sfvM1a g) (sfvLog2 g)

/-- The whole 8-spill log (for `WriteLogNF` reasoning on `sfvM1`). -/
theorem sfvM1_as_log (g : SFVG) :
    sfvM1 g = writeLog g.m0 (sfvLog1 g ++ sfvLog2 g) := by
  rw [writeLog_append]; rfl

/-! ## Transport across the eight spills -/

/-- Any byte below `sp0-96` or at/above `sp0` survives the eight spills. -/
theorem sfvM1_out (g : SFVG) (hg : SFVGOk g) (k : Nat)
    (hk : k < g.sp0.toNat - 64 ∨ g.sp0.toNat ≤ k) :
    (sfvM1 g)[k]? = g.m0[k]? := by
  rw [sfvM1_as_log]
  refine writeLog_out _ _ _ ?_
  have h1 := sfv_slotAddr g hg (0x050#12) 80 (by decide) (by omega)
  have h2 := sfv_slotAddr g hg (0x030#12) 48 (by decide) (by omega)
  have h3 := sfv_slotAddr g hg (0x028#12) 40 (by decide) (by omega)
  have h4 := sfv_slotAddr g hg (0x058#12) 88 (by decide) (by omega)
  have h5 := sfv_slotAddr g hg (0x048#12) 72 (by decide) (by omega)
  have h6 := sfv_slotAddr g hg (0x040#12) 64 (by decide) (by omega)
  have h7 := sfv_slotAddr g hg (0x038#12) 56 (by decide) (by omega)
  have h8 := sfv_slotAddr g hg (0x020#12) 32 (by decide) (by omega)
  have h96 : 96 ≤ g.sp0.toNat := by
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hg.sp_htif; omega
  simp only [sfvLog1, sfvLog2, List.cons_append, List.nil_append, OutL,
    h1, h2, h3, h4, h5, h6, h7, h8, and_true]
  omega

/-- Same, `sfvM1a` (after the first four spills only). -/
theorem sfvM1a_out (g : SFVG) (hg : SFVGOk g) (k : Nat)
    (hk : k < g.sp0.toNat - 64 ∨ g.sp0.toNat ≤ k) :
    (sfvM1a g)[k]? = g.m0[k]? := by
  refine writeLog_out _ _ _ ?_
  have h1 := sfv_slotAddr g hg (0x050#12) 80 (by decide) (by omega)
  have h2 := sfv_slotAddr g hg (0x030#12) 48 (by decide) (by omega)
  have h3 := sfv_slotAddr g hg (0x028#12) 40 (by decide) (by omega)
  have h4 := sfv_slotAddr g hg (0x058#12) 88 (by decide) (by omega)
  have h96 : 96 ≤ g.sp0.toNat := by
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hg.sp_htif; omega
  simp only [sfvLog1, OutL, h1, h2, h3, h4, and_true]
  omega

theorem sfvM1_agree_lo (g : SFVG) (hg : SFVGOk g) :
    ∀ j : Nat, j < tohostAddr → (sfvM1 g)[j]? = g.m0[j]? := by
  intro j hj
  have ht : tohostAddr = 0x8001ad00 := rfl
  refine sfvM1_out g hg j ?_
  left; have := hg.sp_htif; omega

theorem sfvM1a_agree_lo (g : SFVG) (hg : SFVGOk g) :
    ∀ j : Nat, j < tohostAddr → (sfvM1a g)[j]? = g.m0[j]? := by
  intro j hj
  have ht : tohostAddr = 0x8001ad00 := rfl
  refine sfvM1a_out g hg j ?_
  left; have := hg.sp_htif; omega

/-- Below-frame ∨ above-frame windows keep their `Pin8`s across the spills. -/
theorem sfvM1_pin8 (g : SFVG) (hg : SFVGOk g) (a : Nat) (v : BitVec 64)
    (ha : a + 8 ≤ g.sp0.toNat - 64 ∨ g.sp0.toNat ≤ a)
    (h : Pin8 g.m0 a v) : Pin8 (sfvM1 g) a v := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := h
  exact ⟨(sfvM1_out g hg a (by omega)).trans p0,
    (sfvM1_out g hg (a + 1) (by omega)).trans p1,
    (sfvM1_out g hg (a + 2) (by omega)).trans p2,
    (sfvM1_out g hg (a + 3) (by omega)).trans p3,
    (sfvM1_out g hg (a + 4) (by omega)).trans p4,
    (sfvM1_out g hg (a + 5) (by omega)).trans p5,
    (sfvM1_out g hg (a + 6) (by omega)).trans p6,
    (sfvM1_out g hg (a + 7) (by omega)).trans p7⟩

theorem sfvM1a_pin8 (g : SFVG) (hg : SFVGOk g) (a : Nat) (v : BitVec 64)
    (ha : a + 8 ≤ g.sp0.toNat - 64 ∨ g.sp0.toNat ≤ a)
    (h : Pin8 g.m0 a v) : Pin8 (sfvM1a g) a v := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := h
  exact ⟨(sfvM1a_out g hg a (by omega)).trans p0,
    (sfvM1a_out g hg (a + 1) (by omega)).trans p1,
    (sfvM1a_out g hg (a + 2) (by omega)).trans p2,
    (sfvM1a_out g hg (a + 3) (by omega)).trans p3,
    (sfvM1a_out g hg (a + 4) (by omega)).trans p4,
    (sfvM1a_out g hg (a + 5) (by omega)).trans p5,
    (sfvM1a_out g hg (a + 6) (by omega)).trans p6,
    (sfvM1a_out g hg (a + 7) (by omega)).trans p7⟩

/-- `fp` window bytes sit below `sp0-144` (hence below the spill window). -/
theorem sfv_fp_below_frame (g : SFVG) (hg : SFVGOk g) :
    g.fp.toNat + 72 ≤ g.sp0.toNat - 64 := by
  have := hg.fp_below
  have ht : tohostAddr = 0x8001ad00 := rfl
  have := hg.sp_htif
  omega

/-! ## The `__swrite` ghost bundle at the seam -/

/-- The live callee-saved bundle at the `jalr` (`s1..s6` hold the iov cursor
state; `s7..s11` the outer entries). -/
def sfvLiveSV (g : SFVG) : SRegs :=
  { s1 := bytesVal MKind.ld (bytes8 g.iovp) + sign_extend (m := 64) (0x010#12)
    s2 := g.len
    s3 := g.buf
    s4 := g.uio
    s5 := g.reent
    s6 := sfvClamp
    s7 := g.sv.s7, s8 := g.sv.s8, s9 := g.sv.s9, s10 := g.sv.s10, s11 := g.sv.s11 }

/-- P3's `__swrite` ghost bundle as seen at the `jalr fp->_write` seam. -/
def sfvSWG (g : SFVG) : SWG :=
  { cookie := g.reent, fp := g.fp, buf := g.buf, len := sfvLenW g,
    ra0 := 0x8000df20#64, sp0 := sfvSpE g, s00 := g.fp, sv := sfvLiveSV g,
    fl0 := g.fl0, fl1 := g.fl1, fd0 := g.fd0, fd1 := g.fd1,
    bytes := g.bytes, m0 := sfvM1 g, out0 := g.out0 }

theorem sfv_lenW_toNat (g : SFVG) (hg : SFVGOk g) : (sfvLenW g).toNat = g.len.toNat := by
  rw [sfvLenW_id g (by have := hg.len_le; omega)]

theorem sfvSWG_ok (g : SFVG) (hg : SFVGOk g) : SWGOk (sfvSWG g) := by
  have hlenW : sfvLenW g = g.len := sfvLenW_id g (by have := hg.len_le; omega)
  have hspE := sfv_spE_toNat g hg
  have ht : tohostAddr = 0x8001ad00 := rfl
  have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
  have hfpb := sfv_fp_below_frame g hg
  exact
    { len_bytes := by
        show (sfvLenW g).toNat = g.bytes.length
        rw [hlenW]; exact hg.len_bytes
      nowrap := hg.nowrap
      lo := hg.lo
      hiram := hg.hiram
      htif := hg.htif
      pins := by
        intro i h
        have h' : i < g.bytes.length := h
        show (sfvM1 g)[g.buf.toNat + i]? = _
        refine (sfvM1_out g hg (g.buf.toNat + i) ?_).trans (hg.pins i h')
        rcases hg.buf_stack_disj with hd | hd
        · left; omega
        · right; omega
      code := by
        show Vsa.Sim.Code._writeLoaded (sfvM1 g)
        exact writeLoaded_of_agree_lo (sfvM1_agree_lo g hg) hg.code
      codeR := by
        show Vsa.Sim.Code._write_rLoaded (sfvM1 g)
        exact write_rLoaded_of_agree_lo (sfvM1_agree_lo g hg) hg.codeR
      codeS := by
        show Vsa.Sim.Code.__swriteLoaded (sfvM1 g)
        exact swriteLoaded_of_agree_lo (sfvM1_agree_lo g hg) hg.codeS
      ra_align := by
        show (0x8000df20#64 : BitVec 64).toNat % 4 = 0
        decide
      ra_fix := by
        show BitVec.update (0x8000df20#64 + sign_extend (m := 64) (0x000#12)) 0 0#1
          = 0x8000df20#64
        apply BitVec.eq_of_toNat_eq; decide
      sp_htif := by
        show tohostAddr + 16 ≤ (sfvSpE g).toNat - 48
        rw [hspE]; have := hg.sp_htif; omega
      sp_errno := by
        show wrErrnoAddr + 4 ≤ (sfvSpE g).toNat - 48
        rw [hspE]; have := hg.sp_errno; omega
      sp_hi := by
        show (sfvSpE g).toNat ≤ 0x100000000
        rw [hspE]; have := hg.sp_hi; omega
      sp_align := by
        show (sfvSpE g).toNat % 8 = 0
        rw [hspE]; have := hg.sp_align
        omega
      buf_stack_disj := by
        show g.buf.toNat + g.bytes.length ≤ (sfvSpE g).toNat - 48
          ∨ (sfvSpE g).toNat ≤ g.buf.toNat
        rw [hspE]
        rcases hg.buf_stack_disj with hd | hd
        · left; omega
        · right; omega
      buf_errno_disj := hg.buf_errno_disj
      fl_pin0 := by
        show (sfvM1 g)[g.fp.toNat + 16]? = some g.fl0
        exact (sfvM1_out g hg _ (by left; omega)).trans hg.fl_pin0
      fl_pin1 := by
        show (sfvM1 g)[g.fp.toNat + 17]? = some g.fl1
        exact (sfvM1_out g hg _ (by left; omega)).trans hg.fl_pin1
      fd_pin0 := by
        show (sfvM1 g)[g.fp.toNat + 18]? = some g.fd0
        exact (sfvM1_out g hg _ (by left; omega)).trans hg.fd_pin0
      fd_pin1 := by
        show (sfvM1 g)[g.fp.toNat + 19]? = some g.fd1
        exact (sfvM1_out g hg _ (by left; omega)).trans hg.fd_pin1
      fp_htif := hg.fp_htif
      fp_hi := by
        show g.fp.toNat + 20 ≤ 0x100000000
        have := hg.fp_hi; omega
      fp_align := by
        show g.fp.toNat % 2 = 0
        have := hg.fp_align; omega
      fp_stack_disj := by
        show g.fp.toNat + 20 ≤ (sfvSpE g).toNat - 48 ∨ (sfvSpE g).toNat ≤ g.fp.toNat
        rw [hspE]; left; have := hg.fp_below; omega
      buf_fp_disj := hg.buf_fp_disj
      append_off := by
        show bytesVal MKind.lh [g.fl0, g.fl1] &&& sign_extend (m := 64) (0x100#12) = 0#64
        exact hg.append_off }

/-! ## Post-callee memory image -/

/-- The memory at the `jalr` return: `_write_r`'s spill/errno image over
`__swrite`'s spill/flags image over our own eight spills. -/
def sfvMC (g : SFVG) : Std.ExtHashMap Nat (BitVec 8) :=
  wrM1 (swWRG (sfvSWG g))

/-- The resid write-back (`sd a5,16(s4)` at `0x8000df34`): the loaded resid
minus the callee's return, as computed. -/
def sfvLog3 (g : SFVG) : List WEntry :=
  [((g.uio + sign_extend (m := 64) (0x010#12)).toNat, 8,
    bytesVal MKind.ld (bytes8 g.len) - g.len)]

/-- The final memory (the whole-function footprint). -/
def sfvM3 (g : SFVG) : Std.ExtHashMap Nat (BitVec 8) :=
  writeLog (sfvMC g) (sfvLog3 g)

/-- The callee's four writes on top of `sfvM1`: `__swrite`'s `ra` spill at
`spE-8`, the flags halfword at `fp+16`, `_write_r`'s `s0/ra` spills at
`spE-16/spE-8`, and the `errno` word.  Everything outside survives. -/
theorem sfvMC_out (g : SFVG) (hg : SFVGOk g) (k : Nat)
    (hstack : k < g.sp0.toNat - 112 ∨ g.sp0.toNat - 96 ≤ k)
    (hfp : k < g.fp.toNat + 16 ∨ g.fp.toNat + 18 ≤ k)
    (herr : k < wrErrnoAddr ∨ wrErrnoAddr + 4 ≤ k) :
    (sfvMC g)[k]? = (sfvM1 g)[k]? := by
  have hspE := sfv_spE_toNat g hg
  have ht : tohostAddr = 0x8001ad00 := rfl
  have h144 : 144 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
  -- _write_r's frame addresses at its sp0 = sfvSpE g
  have hwrE : (wrSpE (swWRG (sfvSWG g))).toNat = g.sp0.toNat - 112 := by
    show ((sfvSpE g) + sign_extend (m := 64) (0xff0#12)).toNat = _
    rw [ptr_sub_toNat _ (0xff0#12) 16 sext_ff0_toNat (by rw [hspE]; omega), hspE]
    omega
  have hs0slot : (wrSpE (swWRG (sfvSWG g)) + sign_extend (m := 64) (0x000#12)).toNat
      = g.sp0.toNat - 112 := by rw [addi0_env]; exact hwrE
  have hraslot : (wrSpE (swWRG (sfvSWG g)) + sign_extend (m := 64) (0x008#12)).toNat
      = g.sp0.toNat - 104 := by
    rw [ptr_addoff _ (0x008#12) 8 (by decide) (by rw [hwrE]; have := hg.sp_hi; omega), hwrE]
    omega
  have herrA : (wrGpVal + sign_extend (m := 64) (0x4f8#12)).toNat = wrErrnoAddr := by
    show (0x8001b510#64 + sign_extend (m := 64) (0x4f8#12)).toNat = 0x8001ba08
    apply ptr_addoff _ _ 1272 (by decide) (by decide)
  -- __swrite's frame addresses at its sp0 = sfvSpE g
  have hswE : (swSpE (sfvSWG g)).toNat = g.sp0.toNat - 144 := by
    show ((sfvSpE g) + sign_extend (m := 64) (0xfd0#12)).toNat = _
    rw [ptr_sub_toNat _ (0xfd0#12) 48 sext_fd0_toNat (by rw [hspE]; omega), hspE]
    omega
  have hswra : (swSpE (sfvSWG g) + sign_extend (m := 64) (0x028#12)).toNat
      = g.sp0.toNat - 104 := by
    rw [ptr_addoff _ (0x028#12) 40 (by decide) (by rw [hswE]; have := hg.sp_hi; omega), hswE]
    omega
  have hswfl : ((sfvSWG g).fp + sign_extend (m := 64) (0x010#12)).toNat
      = g.fp.toNat + 16 := sfv_flAddr g hg
  show (writeLog (swM2 (sfvSWG g)) (wrEntryLog (swWRG (sfvSWG g))))[k]? = _
  rw [writeLog_out _ _ _ (by
    simp only [wrEntryLog, OutL, hs0slot, hraslot, herrA, and_true]
    omega)]
  show (writeLog (swM1 (sfvSWG g)) (swTailLog (sfvSWG g)))[k]? = _
  rw [writeLog_out _ _ _ (by
    simp only [swTailLog, OutL, hswfl, and_true]
    omega)]
  show (writeLog (sfvM1 g) (swEntryLog (sfvSWG g)))[k]? = _
  rw [writeLog_out _ _ _ (by
    simp only [swEntryLog, OutL, hswra, and_true]
    omega)]

/-- Everything outside the resid slot survives the final write-back too. -/
theorem sfvM3_out (g : SFVG) (hg : SFVGOk g) (k : Nat)
    (hstack : k < g.sp0.toNat - 112 ∨ g.sp0.toNat - 96 ≤ k)
    (hfp : k < g.fp.toNat + 16 ∨ g.fp.toNat + 18 ≤ k)
    (herr : k < wrErrnoAddr ∨ wrErrnoAddr + 4 ≤ k)
    (hresid : k < g.uio.toNat + 16 ∨ g.uio.toNat + 24 ≤ k) :
    (sfvM3 g)[k]? = (sfvM1 g)[k]? := by
  have hres := sfv_residAddr g hg
  show (writeLog (sfvMC g) (sfvLog3 g))[k]? = _
  rw [writeLog_out _ _ _ (by
    simp only [sfvLog3, OutL, hres, and_true]
    omega)]
  exact sfvMC_out g hg k hstack hfp herr



/-! ## The eight spill entries (named — the `pin8_of_writeLog` split points) -/

def sfvE_s0 (g : SFVG) : WEntry :=
  ((sfvSpE g + sign_extend (m := 64) (0x050#12)).toNat, 8, g.s00)
def sfvE_s4 (g : SFVG) : WEntry :=
  ((sfvSpE g + sign_extend (m := 64) (0x030#12)).toNat, 8, g.sv.s4)
def sfvE_s5 (g : SFVG) : WEntry :=
  ((sfvSpE g + sign_extend (m := 64) (0x028#12)).toNat, 8, g.sv.s5)
def sfvE_ra (g : SFVG) : WEntry :=
  ((sfvSpE g + sign_extend (m := 64) (0x058#12)).toNat, 8, g.ra0)
def sfvE_s1 (g : SFVG) : WEntry :=
  ((sfvSpE g + sign_extend (m := 64) (0x048#12)).toNat, 8, g.sv.s1)
def sfvE_s2 (g : SFVG) : WEntry :=
  ((sfvSpE g + sign_extend (m := 64) (0x040#12)).toNat, 8, g.sv.s2)
def sfvE_s3 (g : SFVG) : WEntry :=
  ((sfvSpE g + sign_extend (m := 64) (0x038#12)).toNat, 8, g.sv.s3)
def sfvE_s6 (g : SFVG) : WEntry :=
  ((sfvSpE g + sign_extend (m := 64) (0x020#12)).toNat, 8, g.sv.s6)

/-! ## `agree_lo` + resid/spill `Pin8` providers on the later images -/

theorem sfvMC_agree_lo (g : SFVG) (hg : SFVGOk g) :
    ∀ j : Nat, j < tohostAddr → (sfvMC g)[j]? = g.m0[j]? := by
  intro j hj
  have ht : tohostAddr = 0x8001ad00 := rfl
  have he : wrErrnoAddr = 0x8001ba08 := rfl
  refine ((sfvMC_out g hg j ?_ ?_ ?_).trans (sfvM1_out g hg j ?_))
  · left; have := hg.sp_htif; omega
  · left; have := hg.fp_htif; omega
  · left; omega
  · left; have := hg.sp_htif; omega

theorem sfvM3_agree_lo (g : SFVG) (hg : SFVGOk g) :
    ∀ j : Nat, j < tohostAddr → (sfvM3 g)[j]? = g.m0[j]? := by
  intro j hj
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hres := sfv_residAddr g hg
  show (writeLog (sfvMC g) (sfvLog3 g))[j]? = _
  rw [writeLog_out _ _ _ (by
    simp only [sfvLog3, OutL, hres, and_true]
    have := hg.sp_htif
    have := hg.uio_above
    omega)]
  exact sfvMC_agree_lo g hg j hj

/-- The resid `Pin8` survives onto the post-callee image `sfvMC`. -/
theorem sfvMC_resid_pin8 (g : SFVG) (hg : SFVGOk g) :
    Pin8 (sfvMC g) (g.uio.toNat + 16) g.len := by
  have ht : tohostAddr = 0x8001ad00 := rfl
  have he : wrErrnoAddr = 0x8001ad00 + 3336 := rfl
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := hg.resid_pins
  have step : ∀ k : Nat, g.uio.toNat + 16 ≤ k → k < g.uio.toNat + 24 →
      (sfvMC g)[k]? = g.m0[k]? := by
    intro k hk1 hk2
    have := hg.uio_above
    have := hg.sp_htif
    have := hg.sp_errno
    have := hg.fp_below
    refine (sfvMC_out g hg k ?_ ?_ ?_).trans (sfvM1_out g hg k ?_) <;> omega
  exact ⟨(step _ (by omega) (by omega)).trans p0,
    (step _ (by omega) (by omega)).trans p1,
    (step _ (by omega) (by omega)).trans p2,
    (step _ (by omega) (by omega)).trans p3,
    (step _ (by omega) (by omega)).trans p4,
    (step _ (by omega) (by omega)).trans p5,
    (step _ (by omega) (by omega)).trans p6,
    (step _ (by omega) (by omega)).trans p7⟩

/-- Spill-window bytes: `sfvM3` reads back what `sfvM1` holds there (the
callee footprint and the resid slot avoid `[sp0-64, sp0)`). -/
theorem sfvM3_spillWindow (g : SFVG) (hg : SFVGOk g) (k : Nat)
    (hk1 : g.sp0.toNat - 64 ≤ k) (hk2 : k < g.sp0.toNat) :
    (sfvM3 g)[k]? = (sfvM1 g)[k]? := by
  have ht : tohostAddr = 0x8001ad00 := rfl
  have he : wrErrnoAddr = 0x8001ad00 + 3336 := rfl
  have := hg.uio_above
  have := hg.sp_htif
  have := hg.sp_errno
  have := hg.fp_below
  refine sfvM3_out g hg k ?_ ?_ ?_ ?_ <;> omega

/-- One spill slot read back off the final image (generic over the
`pin8_of_writeLog` split of the eight-entry log). -/
theorem sfvM3_spill_pin8 (g : SFVG) (hg : SFVGOk g) (l1 l2 : List WEntry)
    (A : Nat) (v : BitVec 64)
    (hsplit : sfvLog1 g ++ sfvLog2 g = l1 ++ (A, 8, v) :: l2)
    (hdis : OutLRange l2 A 8)
    (hA1 : g.sp0.toNat - 64 ≤ A) (hA2 : A + 8 ≤ g.sp0.toNat) :
    Pin8 (sfvM3 g) A v := by
  have base : Pin8 (sfvM1 g) A v := by
    rw [sfvM1_as_log, hsplit]
    exact pin8_of_writeLog g.m0 l1 l2 A v hdis
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7⟩ := base
  exact ⟨(sfvM3_spillWindow g hg _ (by omega) (by omega)).trans p0,
    (sfvM3_spillWindow g hg _ (by omega) (by omega)).trans p1,
    (sfvM3_spillWindow g hg _ (by omega) (by omega)).trans p2,
    (sfvM3_spillWindow g hg _ (by omega) (by omega)).trans p3,
    (sfvM3_spillWindow g hg _ (by omega) (by omega)).trans p4,
    (sfvM3_spillWindow g hg _ (by omega) (by omega)).trans p5,
    (sfvM3_spillWindow g hg _ (by omega) (by omega)).trans p6,
    (sfvM3_spillWindow g hg _ (by omega) (by omega)).trans p7⟩

/-! ## Signed/unsigned guard producers -/

theorem sfv_bgeu_of_le (a b : BitVec 64) (h : b.toNat ≤ a.toNat) :
    zopz0zKzJ_u a b = true := by
  unfold zopz0zKzJ_u
  simp only [Sail.BitVec.toNatInt]
  exact decide_eq_true (Int.ofNat_le.mpr h)

theorem sfv_blez_false (a : BitVec 64) (hne : a.toNat ≠ 0) (hlt : a.toNat < 2 ^ 63) :
    zopz0zKzJ_s (0#64) a = false := by
  unfold zopz0zKzJ_s
  refine decide_eq_false ?_
  simp only [BitVec.toInt_zero, ge_iff_le]
  intro hle
  rw [BitVec.toInt_eq_toNat_cond] at hle
  rw [if_pos (by omega)] at hle
  omega

/-! ## Per-seg `ChainFacts` lemmas (ONE `chain_facts` each) -/

/-- `de8cF`: the resid `ld` + the `beqz` FALL (`resid = len ≠ 0`). -/
theorem sfvDe8cF_facts (g : SFVG) (hg : SFVGOk g)
    (hcode : Vsa.Sim.Code.__sfvwrite_rLoaded g.m0) :
    ChainFacts g.m0 g.m0 (sfvwrite_rXde8cFL g.uio) [bytes8 g.len]
      sfvwrite_rXde8cFSeg := by
  chain_facts hcode with "Vsa.Sim.Code.__sfvwrite_r_at_"
  · -- ld a5,16(a2)
    have ht : tohostAddr = 0x8001ad00 := rfl
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0x80000000 ≤ (g.uio + sign_extend (m := 64) (0x010#12)).toNat
      rw [sfv_residAddr g hg]
      have ht : tohostAddr = 0x8001ad00 := rfl
      have := hg.sp_htif; have := hg.uio_above
      omega
    · show (g.uio + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000
      rw [sfv_residAddr g hg]
      have := hg.uio_hi
      omega
    · show (g.uio + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (g.uio + sign_extend (m := 64) (0x010#12)).toNat
      rw [sfv_residAddr g hg]
      right
      have ht : tohostAddr = 0x8001ad00 := rfl
      have := hg.sp_htif; have := hg.uio_above
      omega
    · show (g.uio + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0
      rw [sfv_residAddr g hg]
      have := hg.uio_align
      omega
    · show LPins8 g.m0 (g.uio + sign_extend (m := 64) (0x010#12)).toNat (bytes8 g.len)
      rw [sfv_residAddr g hg]
      exact lpins8_of_pin8 hg.resid_pins
  · -- beqz FALL: resid ≠ 0
    have ht : tohostAddr = 0x8001ad00 := rfl
    show (bytesVal MKind.ld (bytes8 g.len) == 0#64) = false
    rw [bytes8_val]
    exact beq_eq_false_iff_ne.mpr hg.len_ne

/-- `de94F`: the flags `lh` + four spills + the `beqz` FALL (`__SWR` on). -/
theorem sfvDe94F_facts (g : SFVG) (hg : SFVGOk g)
    (hcode : Vsa.Sim.Code.__sfvwrite_rLoaded g.m0) :
    ChainFacts g.m0 g.m0 (sfvL1 g) [[g.fl0, g.fl1]] sfvwrite_rXde94FSeg := by
  chain_facts hcode with "Vsa.Sim.Code.__sfvwrite_r_at_"
  · -- lh a3,16(a1)
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs80 := sfv_slotAddr g hg (0x050#12) 80 (by decide) (by omega)
    have hs48 := sfv_slotAddr g hg (0x030#12) 48 (by decide) (by omega)
    have hs40 := sfv_slotAddr g hg (0x028#12) 40 (by decide) (by omega)
    have hs88 := sfv_slotAddr g hg (0x058#12) 88 (by decide) (by omega)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · show 0x80000000 ≤ (g.fp + sign_extend (m := 64) (0x010#12)).toNat
      rw [sfv_flAddr g hg]
      have := hg.fp_htif
      omega
    · show (g.fp + sign_extend (m := 64) (0x010#12)).toNat + 2 ≤ 0x100000000
      rw [sfv_flAddr g hg]
      have := hg.fp_hi
      omega
    · show (g.fp + sign_extend (m := 64) (0x010#12)).toNat + 2 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (g.fp + sign_extend (m := 64) (0x010#12)).toNat
      rw [sfv_flAddr g hg]
      right
      have := hg.fp_htif
      omega
    · show (g.fp + sign_extend (m := 64) (0x010#12)).toNat % 2 = 0
      rw [sfv_flAddr g hg]
      have := hg.fp_align
      omega
    · show (g.m0[(g.fp + sign_extend (m := 64) (0x010#12)).toNat]?).getD 0 = g.fl0
      rw [sfv_flAddr g hg]
      exact lpin_of_present hg.fl_pin0
    · show (g.m0[(g.fp + sign_extend (m := 64) (0x010#12)).toNat + 1]?).getD 0 = g.fl1
      rw [sfv_flAddr g hg,
        show g.fp.toNat + 16 + 1 = g.fp.toNat + 17 from by omega]
      exact lpin_of_present hg.fl_pin1
  · -- sd s0,80(sp)
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs80 := sfv_slotAddr g hg (0x050#12) 80 (by decide) (by omega)
    have hs48 := sfv_slotAddr g hg (0x030#12) 48 (by decide) (by omega)
    have hs40 := sfv_slotAddr g hg (0x028#12) 40 (by decide) (by omega)
    have hs88 := sfv_slotAddr g hg (0x058#12) 88 (by decide) (by omega)
    show 0x80000000 ≤ (sfvSpE g + sign_extend (m := 64) (0x050#12)).toNat ∧
      (sfvSpE g + sign_extend (m := 64) (0x050#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (sfvSpE g + sign_extend (m := 64) (0x050#12)).toNat ∧
      (sfvSpE g + sign_extend (m := 64) (0x050#12)).toNat % 8 = 0
    rw [hs80]
    have := hg.sp_htif; have := hg.sp_hi; have := hg.sp_align
    refine ⟨by omega, by omega, by omega, by omega⟩
  · -- sd s4,48(sp)
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs80 := sfv_slotAddr g hg (0x050#12) 80 (by decide) (by omega)
    have hs48 := sfv_slotAddr g hg (0x030#12) 48 (by decide) (by omega)
    have hs40 := sfv_slotAddr g hg (0x028#12) 40 (by decide) (by omega)
    have hs88 := sfv_slotAddr g hg (0x058#12) 88 (by decide) (by omega)
    show 0x80000000 ≤ (sfvSpE g + sign_extend (m := 64) (0x030#12)).toNat ∧
      (sfvSpE g + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (sfvSpE g + sign_extend (m := 64) (0x030#12)).toNat ∧
      (sfvSpE g + sign_extend (m := 64) (0x030#12)).toNat % 8 = 0
    rw [hs48]
    have := hg.sp_htif; have := hg.sp_hi; have := hg.sp_align
    refine ⟨by omega, by omega, by omega, by omega⟩
  · -- sd s5,40(sp)
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs80 := sfv_slotAddr g hg (0x050#12) 80 (by decide) (by omega)
    have hs48 := sfv_slotAddr g hg (0x030#12) 48 (by decide) (by omega)
    have hs40 := sfv_slotAddr g hg (0x028#12) 40 (by decide) (by omega)
    have hs88 := sfv_slotAddr g hg (0x058#12) 88 (by decide) (by omega)
    show 0x80000000 ≤ (sfvSpE g + sign_extend (m := 64) (0x028#12)).toNat ∧
      (sfvSpE g + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (sfvSpE g + sign_extend (m := 64) (0x028#12)).toNat ∧
      (sfvSpE g + sign_extend (m := 64) (0x028#12)).toNat % 8 = 0
    rw [hs40]
    have := hg.sp_htif; have := hg.sp_hi; have := hg.sp_align
    refine ⟨by omega, by omega, by omega, by omega⟩
  · -- sd ra,88(sp)
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs80 := sfv_slotAddr g hg (0x050#12) 80 (by decide) (by omega)
    have hs48 := sfv_slotAddr g hg (0x030#12) 48 (by decide) (by omega)
    have hs40 := sfv_slotAddr g hg (0x028#12) 40 (by decide) (by omega)
    have hs88 := sfv_slotAddr g hg (0x058#12) 88 (by decide) (by omega)
    show 0x80000000 ≤ (sfvSpE g + sign_extend (m := 64) (0x058#12)).toNat ∧
      (sfvSpE g + sign_extend (m := 64) (0x058#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (sfvSpE g + sign_extend (m := 64) (0x058#12)).toNat ∧
      (sfvSpE g + sign_extend (m := 64) (0x058#12)).toNat % 8 = 0
    rw [hs88]
    have := hg.sp_htif; have := hg.sp_hi; have := hg.sp_align
    refine ⟨by omega, by omega, by omega, by omega⟩
  · -- beqz FALL: flags & __SWR ≠ 0
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs80 := sfv_slotAddr g hg (0x050#12) 80 (by decide) (by omega)
    have hs48 := sfv_slotAddr g hg (0x030#12) 48 (by decide) (by omega)
    have hs40 := sfv_slotAddr g hg (0x028#12) 40 (by decide) (by omega)
    have hs88 := sfv_slotAddr g hg (0x058#12) 88 (by decide) (by omega)
    show (bytesVal MKind.lh [g.fl0, g.fl1] &&& sign_extend (m := 64) (0x008#12)
      == 0#64) = false
    exact beq_eq_false_iff_ne.mpr hg.swr_on

/-- `dec0F`: the `_bf._base` `ld` + the `beqz` FALL (`base ≠ 0`). -/
theorem sfvDec0F_facts (g : SFVG) (hg : SFVGOk g)
    (hcode : Vsa.Sim.Code.__sfvwrite_rLoaded (sfvM1a g)) :
    ChainFacts (sfvM1a g) (sfvM1a g) (sfvwrite_rXdec0FL g.fp) [bytes8 g.base]
      sfvwrite_rXdec0FSeg := by
  chain_facts hcode with "Vsa.Sim.Code.__sfvwrite_r_at_"
  · -- ld a5,24(a1)
    have ht : tohostAddr = 0x8001ad00 := rfl
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0x80000000 ≤ (g.fp + sign_extend (m := 64) (0x018#12)).toNat
      rw [sfv_baseAddr g hg]
      have := hg.fp_htif
      omega
    · show (g.fp + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ 0x100000000
      rw [sfv_baseAddr g hg]
      have := hg.fp_hi
      omega
    · show (g.fp + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (g.fp + sign_extend (m := 64) (0x018#12)).toNat
      rw [sfv_baseAddr g hg]
      right
      have := hg.fp_htif
      omega
    · show (g.fp + sign_extend (m := 64) (0x018#12)).toNat % 8 = 0
      rw [sfv_baseAddr g hg]
      have := hg.fp_align
      omega
    · show LPins8 (sfvM1a g) (g.fp + sign_extend (m := 64) (0x018#12)).toNat
        (bytes8 g.base)
      rw [sfv_baseAddr g hg]
      refine lpins8_of_pin8 (sfvM1a_pin8 g hg _ _ ?_ hg.base_pins)
      left
      have := sfv_fp_below_frame g hg
      omega
  · -- beqz FALL: base ≠ 0
    have ht : tohostAddr = 0x8001ad00 := rfl
    show (bytesVal MKind.ld (bytes8 g.base) == 0#64) = false
    rw [bytes8_val]
    exact beq_eq_false_iff_ne.mpr hg.base_ne

/-- `dec8F`: four spills + the `uio_iov` `ld` + the `beqz` FALL (`__SNBF` on). -/
theorem sfvDec8F_facts (g : SFVG) (hg : SFVGOk g)
    (hcode : Vsa.Sim.Code.__sfvwrite_rLoaded (sfvM1a g)) :
    ChainFacts (sfvM1a g) (sfvM1a g) (sfvL2 g) [bytes8 g.iovp]
      sfvwrite_rXdec8FSeg := by
  chain_facts hcode with "Vsa.Sim.Code.__sfvwrite_r_at_"
  · -- sd s1,72(sp)
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs72 := sfv_slotAddr g hg (0x048#12) 72 (by decide) (by omega)
    have hs64 := sfv_slotAddr g hg (0x040#12) 64 (by decide) (by omega)
    have hs56 := sfv_slotAddr g hg (0x038#12) 56 (by decide) (by omega)
    have hs32 := sfv_slotAddr g hg (0x020#12) 32 (by decide) (by omega)
    show 0x80000000 ≤ (sfvSpE g + sign_extend (m := 64) (0x048#12)).toNat ∧
      (sfvSpE g + sign_extend (m := 64) (0x048#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (sfvSpE g + sign_extend (m := 64) (0x048#12)).toNat ∧
      (sfvSpE g + sign_extend (m := 64) (0x048#12)).toNat % 8 = 0
    rw [hs72]
    have := hg.sp_htif; have := hg.sp_hi; have := hg.sp_align
    refine ⟨by omega, by omega, by omega, by omega⟩
  · -- sd s2,64(sp)
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs72 := sfv_slotAddr g hg (0x048#12) 72 (by decide) (by omega)
    have hs64 := sfv_slotAddr g hg (0x040#12) 64 (by decide) (by omega)
    have hs56 := sfv_slotAddr g hg (0x038#12) 56 (by decide) (by omega)
    have hs32 := sfv_slotAddr g hg (0x020#12) 32 (by decide) (by omega)
    show 0x80000000 ≤ (sfvSpE g + sign_extend (m := 64) (0x040#12)).toNat ∧
      (sfvSpE g + sign_extend (m := 64) (0x040#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (sfvSpE g + sign_extend (m := 64) (0x040#12)).toNat ∧
      (sfvSpE g + sign_extend (m := 64) (0x040#12)).toNat % 8 = 0
    rw [hs64]
    have := hg.sp_htif; have := hg.sp_hi; have := hg.sp_align
    refine ⟨by omega, by omega, by omega, by omega⟩
  · -- sd s3,56(sp)
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs72 := sfv_slotAddr g hg (0x048#12) 72 (by decide) (by omega)
    have hs64 := sfv_slotAddr g hg (0x040#12) 64 (by decide) (by omega)
    have hs56 := sfv_slotAddr g hg (0x038#12) 56 (by decide) (by omega)
    have hs32 := sfv_slotAddr g hg (0x020#12) 32 (by decide) (by omega)
    show 0x80000000 ≤ (sfvSpE g + sign_extend (m := 64) (0x038#12)).toNat ∧
      (sfvSpE g + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (sfvSpE g + sign_extend (m := 64) (0x038#12)).toNat ∧
      (sfvSpE g + sign_extend (m := 64) (0x038#12)).toNat % 8 = 0
    rw [hs56]
    have := hg.sp_htif; have := hg.sp_hi; have := hg.sp_align
    refine ⟨by omega, by omega, by omega, by omega⟩
  · -- sd s6,32(sp)
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs72 := sfv_slotAddr g hg (0x048#12) 72 (by decide) (by omega)
    have hs64 := sfv_slotAddr g hg (0x040#12) 64 (by decide) (by omega)
    have hs56 := sfv_slotAddr g hg (0x038#12) 56 (by decide) (by omega)
    have hs32 := sfv_slotAddr g hg (0x020#12) 32 (by decide) (by omega)
    show 0x80000000 ≤ (sfvSpE g + sign_extend (m := 64) (0x020#12)).toNat ∧
      (sfvSpE g + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (sfvSpE g + sign_extend (m := 64) (0x020#12)).toNat ∧
      (sfvSpE g + sign_extend (m := 64) (0x020#12)).toNat % 8 = 0
    rw [hs32]
    have := hg.sp_htif; have := hg.sp_hi; have := hg.sp_align
    refine ⟨by omega, by omega, by omega, by omega⟩
  · -- ld s1,0(s4)
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs72 := sfv_slotAddr g hg (0x048#12) 72 (by decide) (by omega)
    have hs64 := sfv_slotAddr g hg (0x040#12) 64 (by decide) (by omega)
    have hs56 := sfv_slotAddr g hg (0x038#12) 56 (by decide) (by omega)
    have hs32 := sfv_slotAddr g hg (0x020#12) 32 (by decide) (by omega)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0x80000000 ≤ (g.uio + sign_extend (m := 64) (0x000#12)).toNat
      rw [sfv_uioAddr g hg]
      have := hg.sp_htif; have := hg.uio_above
      omega
    · show (g.uio + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000
      rw [sfv_uioAddr g hg]
      have := hg.uio_hi
      omega
    · show (g.uio + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (g.uio + sign_extend (m := 64) (0x000#12)).toNat
      rw [sfv_uioAddr g hg]
      right
      have := hg.sp_htif; have := hg.uio_above
      omega
    · show (g.uio + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0
      rw [sfv_uioAddr g hg]
      have := hg.uio_align
      omega
    · -- pins over the 4-spill store TOWER: memory stays a metavar (`_`),
      -- peel outermost store first (`pin8_peel_sd`) — NEVER `show` it back
      -- to `sfvM1a` (insert-tower isDefEq = stack overflow)
      show LPins8 _ (g.uio + sign_extend (m := 64) (0x000#12)).toNat
        (bytes8 g.iovp)
      rw [sfv_uioAddr g hg]
      refine lpins8_of_pin8
        (pin8_peel_sd (sfvSpE g + sign_extend (m := 64) (0x020#12)).toNat _
          (by rw [hs32]; have := hg.uio_above; omega)
        (pin8_peel_sd (sfvSpE g + sign_extend (m := 64) (0x038#12)).toNat _
          (by rw [hs56]; have := hg.uio_above; omega)
        (pin8_peel_sd (sfvSpE g + sign_extend (m := 64) (0x040#12)).toNat _
          (by rw [hs64]; have := hg.uio_above; omega)
        (pin8_peel_sd (sfvSpE g + sign_extend (m := 64) (0x048#12)).toNat _
          (by rw [hs72]; have := hg.uio_above; omega)
        (sfvM1a_pin8 g hg _ _ ?_ hg.iovp_pins)))))
      right
      have := hg.uio_above
      omega
  · -- beqz FALL: flags & __SNBF ≠ 0
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs72 := sfv_slotAddr g hg (0x048#12) 72 (by decide) (by omega)
    have hs64 := sfv_slotAddr g hg (0x040#12) 64 (by decide) (by omega)
    have hs56 := sfv_slotAddr g hg (0x038#12) 56 (by decide) (by omega)
    have hs32 := sfv_slotAddr g hg (0x020#12) 32 (by decide) (by omega)
    show (sfvFlags g &&& sign_extend (m := 64) (0x002#12) == 0#64) = false
    exact beq_eq_false_iff_ne.mpr hg.nbf_on

/-- `dee4`: pure ALU (clamp constant + zero inits). -/
theorem sfvDee4_facts (g : SFVG) (hg : SFVGOk g)
    (hcode : Vsa.Sim.Code.__sfvwrite_rLoaded (sfvM1 g)) :
    ChainFacts (sfvM1 g) (sfvM1 g) sfvwrite_rXdee4L [] sfvwrite_rXdee4Seg := by
  chain_facts hcode with "Vsa.Sim.Code.__sfvwrite_r_at_"

/-- `def4T` (first loop-head visit, `s2 = 0`): the `beqz` TAKEN. -/
theorem sfvDef4T_facts (g : SFVG) (hg : SFVGOk g)
    (hcode : Vsa.Sim.Code.__sfvwrite_rLoaded (sfvM1 g)) :
    ChainFacts (sfvM1 g) (sfvM1 g) (sfvwrite_rXdef4TL 0#64 g.reent 0#64) []
      sfvwrite_rXdef4TSeg := by
  chain_facts hcode with "Vsa.Sim.Code.__sfvwrite_r_at_"
  · -- beqz TAKEN: s2 = 0
    show ((0#64 : BitVec 64) == 0#64) = true
    decide

/-- `e0bc`: the iov `ld`s. -/
theorem sfvE0bc_facts (g : SFVG) (hg : SFVGOk g)
    (hcode : Vsa.Sim.Code.__sfvwrite_rLoaded (sfvM1 g)) :
    ChainFacts (sfvM1 g) (sfvM1 g) (sfvwrite_rXe0bcL g.iovp)
      [bytes8 g.buf, bytes8 g.len] sfvwrite_rXe0bcSeg := by
  chain_facts hcode with "Vsa.Sim.Code.__sfvwrite_r_at_"
  · -- ld s3,0(s1)
    have ht : tohostAddr = 0x8001ad00 := rfl
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0x80000000 ≤ (g.iovp + sign_extend (m := 64) (0x000#12)).toNat
      rw [sfv_iovBaseAddr g hg]
      have := hg.sp_htif; have := hg.iov_above
      omega
    · show (g.iovp + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000
      rw [sfv_iovBaseAddr g hg]
      have := hg.iov_hi
      omega
    · show (g.iovp + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (g.iovp + sign_extend (m := 64) (0x000#12)).toNat
      rw [sfv_iovBaseAddr g hg]
      right
      have := hg.sp_htif; have := hg.iov_above
      omega
    · show (g.iovp + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0
      rw [sfv_iovBaseAddr g hg]
      have := hg.iov_align
      omega
    · show LPins8 (sfvM1 g) (g.iovp + sign_extend (m := 64) (0x000#12)).toNat
        (bytes8 g.buf)
      rw [sfv_iovBaseAddr g hg]
      refine lpins8_of_pin8 (sfvM1_pin8 g hg _ _ ?_ hg.iov_base_pins)
      right
      have := hg.iov_above
      omega
  · -- ld s2,8(s1)
    have ht : tohostAddr = 0x8001ad00 := rfl
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0x80000000 ≤ (g.iovp + sign_extend (m := 64) (0x008#12)).toNat
      rw [sfv_iovLenAddr g hg]
      have := hg.sp_htif; have := hg.iov_above
      omega
    · show (g.iovp + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000
      rw [sfv_iovLenAddr g hg]
      have := hg.iov_hi
      omega
    · show (g.iovp + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (g.iovp + sign_extend (m := 64) (0x008#12)).toNat
      rw [sfv_iovLenAddr g hg]
      right
      have := hg.sp_htif; have := hg.iov_above
      omega
    · show (g.iovp + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0
      rw [sfv_iovLenAddr g hg]
      have := hg.iov_align
      omega
    · show LPins8 (sfvM1 g) (g.iovp + sign_extend (m := 64) (0x008#12)).toNat
        (bytes8 g.len)
      rw [sfv_iovLenAddr g hg]
      refine lpins8_of_pin8 (sfvM1_pin8 g hg _ _ ?_ hg.iov_len_pins)
      right
      have := hg.iov_above
      omega

/-- `def4F` (second visit, `s2 = len ≠ 0`): the `beqz` FALL. -/
theorem sfvDef4F_facts (g : SFVG) (hg : SFVGOk g)
    (hcode : Vsa.Sim.Code.__sfvwrite_rLoaded (sfvM1 g)) :
    ChainFacts (sfvM1 g) (sfvM1 g) (sfvwrite_rXdef4FL g.buf g.reent g.len) []
      sfvwrite_rXdef4FSeg := by
  chain_facts hcode with "Vsa.Sim.Code.__sfvwrite_r_at_"
  · -- beqz FALL: s2 = len ≠ 0
    show (g.len == 0#64) = false
    exact beq_eq_false_iff_ne.mpr hg.len_ne

/-- `df00T`: the clamp `bgeu` TAKEN (`len ≤ 0x7ffffc00`). -/
theorem sfvDf00T_facts (g : SFVG) (hg : SFVGOk g)
    (hcode : Vsa.Sim.Code.__sfvwrite_rLoaded (sfvM1 g)) :
    ChainFacts (sfvM1 g) (sfvM1 g) (sfvwrite_rXdf00TL g.len sfvClamp) []
      sfvwrite_rXdf00TSeg := by
  chain_facts hcode with "Vsa.Sim.Code.__sfvwrite_r_at_"
  · -- bgeu TAKEN: clamp ≥ len
    show zopz0zKzJ_u sfvClamp g.len = true
    rw [sfvClamp_eq]
    refine sfv_bgeu_of_le _ _ ?_
    have hc : (0x7ffffc00#64 : BitVec 64).toNat = 0x7ffffc00 := rfl
    have := hg.len_le
    omega

/-- `df10`: the `_write` vector + `_cookie` `ld`s (both on `sfvM1`). -/
theorem sfvDf10_facts (g : SFVG) (hg : SFVGOk g)
    (hcode : Vsa.Sim.Code.__sfvwrite_rLoaded (sfvM1 g)) :
    ChainFacts (sfvM1 g) (sfvM1 g) (sfvwrite_rXdf10L g.fp g.len)
      [bytes8 0x8000efd4#64, bytes8 g.fp] sfvwrite_rXdf10Seg := by
  chain_facts hcode with "Vsa.Sim.Code.__sfvwrite_r_at_"
  · -- ld a5,64(s0)
    have ht : tohostAddr = 0x8001ad00 := rfl
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0x80000000 ≤ (g.fp + sign_extend (m := 64) (0x040#12)).toNat
      rw [sfv_wvecAddr g hg]
      have := hg.fp_htif
      omega
    · show (g.fp + sign_extend (m := 64) (0x040#12)).toNat + 8 ≤ 0x100000000
      rw [sfv_wvecAddr g hg]
      have := hg.fp_hi
      omega
    · show (g.fp + sign_extend (m := 64) (0x040#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (g.fp + sign_extend (m := 64) (0x040#12)).toNat
      rw [sfv_wvecAddr g hg]
      right
      have := hg.fp_htif
      omega
    · show (g.fp + sign_extend (m := 64) (0x040#12)).toNat % 8 = 0
      rw [sfv_wvecAddr g hg]
      have := hg.fp_align
      omega
    · show LPins8 (sfvM1 g) (g.fp + sign_extend (m := 64) (0x040#12)).toNat
        (bytes8 0x8000efd4#64)
      rw [sfv_wvecAddr g hg]
      refine lpins8_of_pin8 (sfvM1_pin8 g hg _ _ ?_ hg.wvec_pins)
      left
      have := sfv_fp_below_frame g hg
      omega
  · -- ld a1,48(s0)
    have ht : tohostAddr = 0x8001ad00 := rfl
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0x80000000 ≤ (g.fp + sign_extend (m := 64) (0x030#12)).toNat
      rw [sfv_cookieAddr g hg]
      have := hg.fp_htif
      omega
    · show (g.fp + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ 0x100000000
      rw [sfv_cookieAddr g hg]
      have := hg.fp_hi
      omega
    · show (g.fp + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (g.fp + sign_extend (m := 64) (0x030#12)).toNat
      rw [sfv_cookieAddr g hg]
      right
      have := hg.fp_htif
      omega
    · show (g.fp + sign_extend (m := 64) (0x030#12)).toNat % 8 = 0
      rw [sfv_cookieAddr g hg]
      have := hg.fp_align
      omega
    · show LPins8 (sfvM1 g) (g.fp + sign_extend (m := 64) (0x030#12)).toNat
        (bytes8 g.fp)
      rw [sfv_cookieAddr g hg]
      refine lpins8_of_pin8 (sfvM1_pin8 g hg _ _ ?_ hg.cookie_pins)
      left
      have := sfv_fp_below_frame g hg
      omega

/-- `df20F`: the `blez` FALL (the callee returned `len > 0`). -/
theorem sfvDf20F_facts (g : SFVG) (hg : SFVGOk g)
    (hcode : Vsa.Sim.Code.__sfvwrite_rLoaded (sfvMC g)) :
    ChainFacts (sfvMC g) (sfvMC g) (sfvwrite_rXdf20FL g.len) []
      sfvwrite_rXdf20FSeg := by
  chain_facts hcode with "Vsa.Sim.Code.__sfvwrite_r_at_"
  · -- blez FALL: len > 0 (signed)
    show zopz0zKzJ_s (0#64) g.len = false
    refine sfv_blez_false g.len ?_ ?_
    · intro hz
      exact hg.len_ne (BitVec.eq_of_toNat_eq (by rw [hz]; rfl))
    · have := hg.len_le
      omega

/-- `df24F`: the resid `ld` (on the callee image) + the resid write-back +
the `bnez` FALL (`resid − written = 0`). -/
theorem sfvDf24F_facts (g : SFVG) (hg : SFVGOk g)
    (hcode : Vsa.Sim.Code.__sfvwrite_rLoaded (sfvMC g)) :
    ChainFacts (sfvMC g) (sfvMC g) (sfvwrite_rXdf24FL g.uio g.buf g.len g.len)
      [bytes8 g.len] sfvwrite_rXdf24FSeg := by
  chain_facts hcode with "Vsa.Sim.Code.__sfvwrite_r_at_"
  · -- ld a5,16(s4) — the resid, read back off the callee image
    have ht : tohostAddr = 0x8001ad00 := rfl
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0x80000000 ≤ (g.uio + sign_extend (m := 64) (0x010#12)).toNat
      rw [sfv_residAddr g hg]
      have := hg.sp_htif; have := hg.uio_above
      omega
    · show (g.uio + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000
      rw [sfv_residAddr g hg]
      have := hg.uio_hi
      omega
    · show (g.uio + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (g.uio + sign_extend (m := 64) (0x010#12)).toNat
      rw [sfv_residAddr g hg]
      right
      have := hg.sp_htif; have := hg.uio_above
      omega
    · show (g.uio + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0
      rw [sfv_residAddr g hg]
      have := hg.uio_align
      omega
    · show LPins8 (sfvMC g) (g.uio + sign_extend (m := 64) (0x010#12)).toNat
        (bytes8 g.len)
      rw [sfv_residAddr g hg]
      exact lpins8_of_pin8 (sfvMC_resid_pin8 g hg)
  · -- sd a5,16(s4) — the resid write-back
    have ht : tohostAddr = 0x8001ad00 := rfl
    show 0x80000000 ≤ (g.uio + sign_extend (m := 64) (0x010#12)).toNat ∧
      (g.uio + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (g.uio + sign_extend (m := 64) (0x010#12)).toNat ∧
      (g.uio + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0
    rw [sfv_residAddr g hg]
    have := hg.sp_htif; have := hg.uio_above; have := hg.uio_hi
    have := hg.uio_align
    refine ⟨by omega, by omega, by omega, by omega⟩
  · -- bnez FALL: resid − written = 0
    have ht : tohostAddr = 0x8001ad00 := rfl
    show ((bytesVal MKind.ld (bytes8 g.len) - g.len != 0#64)) = false
    rw [bytes8_val, BitVec.sub_self]
    decide

/-- `df3c`: four spill readbacks (on the final image). -/
theorem sfvDf3c_facts (g : SFVG) (hg : SFVGOk g)
    (hcode : Vsa.Sim.Code.__sfvwrite_rLoaded (sfvM3 g)) :
    ChainFacts (sfvM3 g) (sfvM3 g) (sfvwrite_rXdf3cL (sfvSpE g))
      [bytes8 g.sv.s1, bytes8 g.sv.s2, bytes8 g.sv.s3, bytes8 g.sv.s6]
      sfvwrite_rXdf3cSeg := by
  chain_facts hcode with "Vsa.Sim.Code.__sfvwrite_r_at_"
  · -- ld s1,72(sp)
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs80 := sfv_slotAddr g hg (0x050#12) 80 (by decide) (by omega)
    have hs48 := sfv_slotAddr g hg (0x030#12) 48 (by decide) (by omega)
    have hs40 := sfv_slotAddr g hg (0x028#12) 40 (by decide) (by omega)
    have hs88 := sfv_slotAddr g hg (0x058#12) 88 (by decide) (by omega)
    have hs72 := sfv_slotAddr g hg (0x048#12) 72 (by decide) (by omega)
    have hs64 := sfv_slotAddr g hg (0x040#12) 64 (by decide) (by omega)
    have hs56 := sfv_slotAddr g hg (0x038#12) 56 (by decide) (by omega)
    have hs32 := sfv_slotAddr g hg (0x020#12) 32 (by decide) (by omega)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0x80000000 ≤ (sfvSpE g + sign_extend (m := 64) (0x048#12)).toNat
      rw [hs72]; have := hg.sp_htif; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x048#12)).toNat + 8 ≤ 0x100000000
      rw [hs72]; have := hg.sp_hi; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x048#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (sfvSpE g + sign_extend (m := 64) (0x048#12)).toNat
      rw [hs72]; right; have := hg.sp_htif; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x048#12)).toNat % 8 = 0
      rw [hs72]; have := hg.sp_align; omega
    · show LPins8 (sfvM3 g) (sfvSpE g + sign_extend (m := 64) (0x048#12)).toNat
        (bytes8 g.sv.s1)
      refine lpins8_of_pin8 (sfvM3_spill_pin8 g hg
        [sfvE_s0 g, sfvE_s4 g, sfvE_s5 g, sfvE_ra g]
        [sfvE_s2 g, sfvE_s3 g, sfvE_s6 g] _ _ (by simp only [sfvLog1, sfvLog2, sfvE_s0, sfvE_s4, sfvE_s5, sfvE_ra,
          sfvE_s1, sfvE_s2, sfvE_s3, sfvE_s6, List.cons_append, List.nil_append]) ?_ (by rw [hs72]; omega)
        (by rw [hs72]; omega))
      simp only [OutLRange, sfvE_s2, sfvE_s3, sfvE_s6, hs72, hs64, hs56, hs32,
        and_true]
      omega
  · -- ld s2,64(sp)
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs80 := sfv_slotAddr g hg (0x050#12) 80 (by decide) (by omega)
    have hs48 := sfv_slotAddr g hg (0x030#12) 48 (by decide) (by omega)
    have hs40 := sfv_slotAddr g hg (0x028#12) 40 (by decide) (by omega)
    have hs88 := sfv_slotAddr g hg (0x058#12) 88 (by decide) (by omega)
    have hs72 := sfv_slotAddr g hg (0x048#12) 72 (by decide) (by omega)
    have hs64 := sfv_slotAddr g hg (0x040#12) 64 (by decide) (by omega)
    have hs56 := sfv_slotAddr g hg (0x038#12) 56 (by decide) (by omega)
    have hs32 := sfv_slotAddr g hg (0x020#12) 32 (by decide) (by omega)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0x80000000 ≤ (sfvSpE g + sign_extend (m := 64) (0x040#12)).toNat
      rw [hs64]; have := hg.sp_htif; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x040#12)).toNat + 8 ≤ 0x100000000
      rw [hs64]; have := hg.sp_hi; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x040#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (sfvSpE g + sign_extend (m := 64) (0x040#12)).toNat
      rw [hs64]; right; have := hg.sp_htif; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x040#12)).toNat % 8 = 0
      rw [hs64]; have := hg.sp_align; omega
    · show LPins8 (sfvM3 g) (sfvSpE g + sign_extend (m := 64) (0x040#12)).toNat
        (bytes8 g.sv.s2)
      refine lpins8_of_pin8 (sfvM3_spill_pin8 g hg
        [sfvE_s0 g, sfvE_s4 g, sfvE_s5 g, sfvE_ra g, sfvE_s1 g]
        [sfvE_s3 g, sfvE_s6 g] _ _ (by simp only [sfvLog1, sfvLog2, sfvE_s0, sfvE_s4, sfvE_s5, sfvE_ra,
          sfvE_s1, sfvE_s2, sfvE_s3, sfvE_s6, List.cons_append, List.nil_append]) ?_ (by rw [hs64]; omega)
        (by rw [hs64]; omega))
      simp only [OutLRange, sfvE_s3, sfvE_s6, hs64, hs56, hs32, and_true]
      omega
  · -- ld s3,56(sp)
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs80 := sfv_slotAddr g hg (0x050#12) 80 (by decide) (by omega)
    have hs48 := sfv_slotAddr g hg (0x030#12) 48 (by decide) (by omega)
    have hs40 := sfv_slotAddr g hg (0x028#12) 40 (by decide) (by omega)
    have hs88 := sfv_slotAddr g hg (0x058#12) 88 (by decide) (by omega)
    have hs72 := sfv_slotAddr g hg (0x048#12) 72 (by decide) (by omega)
    have hs64 := sfv_slotAddr g hg (0x040#12) 64 (by decide) (by omega)
    have hs56 := sfv_slotAddr g hg (0x038#12) 56 (by decide) (by omega)
    have hs32 := sfv_slotAddr g hg (0x020#12) 32 (by decide) (by omega)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0x80000000 ≤ (sfvSpE g + sign_extend (m := 64) (0x038#12)).toNat
      rw [hs56]; have := hg.sp_htif; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ 0x100000000
      rw [hs56]; have := hg.sp_hi; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (sfvSpE g + sign_extend (m := 64) (0x038#12)).toNat
      rw [hs56]; right; have := hg.sp_htif; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x038#12)).toNat % 8 = 0
      rw [hs56]; have := hg.sp_align; omega
    · show LPins8 (sfvM3 g) (sfvSpE g + sign_extend (m := 64) (0x038#12)).toNat
        (bytes8 g.sv.s3)
      refine lpins8_of_pin8 (sfvM3_spill_pin8 g hg
        [sfvE_s0 g, sfvE_s4 g, sfvE_s5 g, sfvE_ra g, sfvE_s1 g, sfvE_s2 g]
        [sfvE_s6 g] _ _ (by simp only [sfvLog1, sfvLog2, sfvE_s0, sfvE_s4, sfvE_s5, sfvE_ra,
          sfvE_s1, sfvE_s2, sfvE_s3, sfvE_s6, List.cons_append, List.nil_append]) ?_ (by rw [hs56]; omega)
        (by rw [hs56]; omega))
      simp only [OutLRange, sfvE_s6, hs56, hs32, and_true]
      omega
  · -- ld s6,32(sp)
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs80 := sfv_slotAddr g hg (0x050#12) 80 (by decide) (by omega)
    have hs48 := sfv_slotAddr g hg (0x030#12) 48 (by decide) (by omega)
    have hs40 := sfv_slotAddr g hg (0x028#12) 40 (by decide) (by omega)
    have hs88 := sfv_slotAddr g hg (0x058#12) 88 (by decide) (by omega)
    have hs72 := sfv_slotAddr g hg (0x048#12) 72 (by decide) (by omega)
    have hs64 := sfv_slotAddr g hg (0x040#12) 64 (by decide) (by omega)
    have hs56 := sfv_slotAddr g hg (0x038#12) 56 (by decide) (by omega)
    have hs32 := sfv_slotAddr g hg (0x020#12) 32 (by decide) (by omega)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0x80000000 ≤ (sfvSpE g + sign_extend (m := 64) (0x020#12)).toNat
      rw [hs32]; have := hg.sp_htif; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ 0x100000000
      rw [hs32]; have := hg.sp_hi; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (sfvSpE g + sign_extend (m := 64) (0x020#12)).toNat
      rw [hs32]; right; have := hg.sp_htif; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x020#12)).toNat % 8 = 0
      rw [hs32]; have := hg.sp_align; omega
    · show LPins8 (sfvM3 g) (sfvSpE g + sign_extend (m := 64) (0x020#12)).toNat
        (bytes8 g.sv.s6)
      refine lpins8_of_pin8 (sfvM3_spill_pin8 g hg
        [sfvE_s0 g, sfvE_s4 g, sfvE_s5 g, sfvE_ra g, sfvE_s1 g, sfvE_s2 g,
         sfvE_s3 g] [] _ _ (by simp only [sfvLog1, sfvLog2, sfvE_s0, sfvE_s4, sfvE_s5, sfvE_ra,
          sfvE_s1, sfvE_s2, sfvE_s3, sfvE_s6, List.cons_append, List.nil_append]) trivial (by rw [hs32]; omega)
        (by rw [hs32]; omega))

/-- `df50`: four more spill readbacks + the `ret`. -/
theorem sfvDf50_facts (g : SFVG) (hg : SFVGOk g)
    (hcode : Vsa.Sim.Code.__sfvwrite_rLoaded (sfvM3 g)) :
    ChainFacts (sfvM3 g) (sfvM3 g) (sfvwrite_rXdf50L (sfvSpE g))
      [bytes8 g.ra0, bytes8 g.s00, bytes8 g.sv.s4, bytes8 g.sv.s5]
      sfvwrite_rXdf50Seg := by
  chain_facts hcode with "Vsa.Sim.Code.__sfvwrite_r_at_"
  · -- ld ra,88(sp)
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs80 := sfv_slotAddr g hg (0x050#12) 80 (by decide) (by omega)
    have hs48 := sfv_slotAddr g hg (0x030#12) 48 (by decide) (by omega)
    have hs40 := sfv_slotAddr g hg (0x028#12) 40 (by decide) (by omega)
    have hs88 := sfv_slotAddr g hg (0x058#12) 88 (by decide) (by omega)
    have hs72 := sfv_slotAddr g hg (0x048#12) 72 (by decide) (by omega)
    have hs64 := sfv_slotAddr g hg (0x040#12) 64 (by decide) (by omega)
    have hs56 := sfv_slotAddr g hg (0x038#12) 56 (by decide) (by omega)
    have hs32 := sfv_slotAddr g hg (0x020#12) 32 (by decide) (by omega)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0x80000000 ≤ (sfvSpE g + sign_extend (m := 64) (0x058#12)).toNat
      rw [hs88]; have := hg.sp_htif; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x058#12)).toNat + 8 ≤ 0x100000000
      rw [hs88]; have := hg.sp_hi; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x058#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (sfvSpE g + sign_extend (m := 64) (0x058#12)).toNat
      rw [hs88]; right; have := hg.sp_htif; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x058#12)).toNat % 8 = 0
      rw [hs88]; have := hg.sp_align; omega
    · show LPins8 (sfvM3 g) (sfvSpE g + sign_extend (m := 64) (0x058#12)).toNat
        (bytes8 g.ra0)
      refine lpins8_of_pin8 (sfvM3_spill_pin8 g hg
        [sfvE_s0 g, sfvE_s4 g, sfvE_s5 g]
        [sfvE_s1 g, sfvE_s2 g, sfvE_s3 g, sfvE_s6 g] _ _ (by simp only [sfvLog1, sfvLog2, sfvE_s0, sfvE_s4, sfvE_s5, sfvE_ra,
          sfvE_s1, sfvE_s2, sfvE_s3, sfvE_s6, List.cons_append, List.nil_append]) ?_
        (by rw [hs88]; omega) (by rw [hs88]; omega))
      simp only [OutLRange, sfvE_s1, sfvE_s2, sfvE_s3, sfvE_s6, hs88, hs72,
        hs64, hs56, hs32, and_true]
      omega
  · -- ld s0,80(sp)
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs80 := sfv_slotAddr g hg (0x050#12) 80 (by decide) (by omega)
    have hs48 := sfv_slotAddr g hg (0x030#12) 48 (by decide) (by omega)
    have hs40 := sfv_slotAddr g hg (0x028#12) 40 (by decide) (by omega)
    have hs88 := sfv_slotAddr g hg (0x058#12) 88 (by decide) (by omega)
    have hs72 := sfv_slotAddr g hg (0x048#12) 72 (by decide) (by omega)
    have hs64 := sfv_slotAddr g hg (0x040#12) 64 (by decide) (by omega)
    have hs56 := sfv_slotAddr g hg (0x038#12) 56 (by decide) (by omega)
    have hs32 := sfv_slotAddr g hg (0x020#12) 32 (by decide) (by omega)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0x80000000 ≤ (sfvSpE g + sign_extend (m := 64) (0x050#12)).toNat
      rw [hs80]; have := hg.sp_htif; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x050#12)).toNat + 8 ≤ 0x100000000
      rw [hs80]; have := hg.sp_hi; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x050#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (sfvSpE g + sign_extend (m := 64) (0x050#12)).toNat
      rw [hs80]; right; have := hg.sp_htif; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x050#12)).toNat % 8 = 0
      rw [hs80]; have := hg.sp_align; omega
    · show LPins8 (sfvM3 g) (sfvSpE g + sign_extend (m := 64) (0x050#12)).toNat
        (bytes8 g.s00)
      refine lpins8_of_pin8 (sfvM3_spill_pin8 g hg []
        [sfvE_s4 g, sfvE_s5 g, sfvE_ra g, sfvE_s1 g, sfvE_s2 g, sfvE_s3 g,
         sfvE_s6 g] _ _ (by simp only [sfvLog1, sfvLog2, sfvE_s0, sfvE_s4, sfvE_s5, sfvE_ra,
          sfvE_s1, sfvE_s2, sfvE_s3, sfvE_s6, List.cons_append, List.nil_append]) ?_ (by rw [hs80]; omega) (by rw [hs80]; omega))
      simp only [OutLRange, sfvE_s4, sfvE_s5, sfvE_ra, sfvE_s1, sfvE_s2,
        sfvE_s3, sfvE_s6, hs80, hs48, hs40, hs88, hs72, hs64, hs56, hs32,
        and_true]
      omega
  · -- ld s4,48(sp)
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs80 := sfv_slotAddr g hg (0x050#12) 80 (by decide) (by omega)
    have hs48 := sfv_slotAddr g hg (0x030#12) 48 (by decide) (by omega)
    have hs40 := sfv_slotAddr g hg (0x028#12) 40 (by decide) (by omega)
    have hs88 := sfv_slotAddr g hg (0x058#12) 88 (by decide) (by omega)
    have hs72 := sfv_slotAddr g hg (0x048#12) 72 (by decide) (by omega)
    have hs64 := sfv_slotAddr g hg (0x040#12) 64 (by decide) (by omega)
    have hs56 := sfv_slotAddr g hg (0x038#12) 56 (by decide) (by omega)
    have hs32 := sfv_slotAddr g hg (0x020#12) 32 (by decide) (by omega)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0x80000000 ≤ (sfvSpE g + sign_extend (m := 64) (0x030#12)).toNat
      rw [hs48]; have := hg.sp_htif; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ 0x100000000
      rw [hs48]; have := hg.sp_hi; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (sfvSpE g + sign_extend (m := 64) (0x030#12)).toNat
      rw [hs48]; right; have := hg.sp_htif; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x030#12)).toNat % 8 = 0
      rw [hs48]; have := hg.sp_align; omega
    · show LPins8 (sfvM3 g) (sfvSpE g + sign_extend (m := 64) (0x030#12)).toNat
        (bytes8 g.sv.s4)
      refine lpins8_of_pin8 (sfvM3_spill_pin8 g hg [sfvE_s0 g]
        [sfvE_s5 g, sfvE_ra g, sfvE_s1 g, sfvE_s2 g, sfvE_s3 g, sfvE_s6 g]
        _ _ (by simp only [sfvLog1, sfvLog2, sfvE_s0, sfvE_s4, sfvE_s5, sfvE_ra,
          sfvE_s1, sfvE_s2, sfvE_s3, sfvE_s6, List.cons_append, List.nil_append]) ?_ (by rw [hs48]; omega) (by rw [hs48]; omega))
      simp only [OutLRange, sfvE_s5, sfvE_ra, sfvE_s1, sfvE_s2, sfvE_s3,
        sfvE_s6, hs48, hs40, hs88, hs72, hs64, hs56, hs32, and_true]
      omega
  · -- ld s5,40(sp)
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs80 := sfv_slotAddr g hg (0x050#12) 80 (by decide) (by omega)
    have hs48 := sfv_slotAddr g hg (0x030#12) 48 (by decide) (by omega)
    have hs40 := sfv_slotAddr g hg (0x028#12) 40 (by decide) (by omega)
    have hs88 := sfv_slotAddr g hg (0x058#12) 88 (by decide) (by omega)
    have hs72 := sfv_slotAddr g hg (0x048#12) 72 (by decide) (by omega)
    have hs64 := sfv_slotAddr g hg (0x040#12) 64 (by decide) (by omega)
    have hs56 := sfv_slotAddr g hg (0x038#12) 56 (by decide) (by omega)
    have hs32 := sfv_slotAddr g hg (0x020#12) 32 (by decide) (by omega)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0x80000000 ≤ (sfvSpE g + sign_extend (m := 64) (0x028#12)).toNat
      rw [hs40]; have := hg.sp_htif; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ 0x100000000
      rw [hs40]; have := hg.sp_hi; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (sfvSpE g + sign_extend (m := 64) (0x028#12)).toNat
      rw [hs40]; right; have := hg.sp_htif; omega
    · show (sfvSpE g + sign_extend (m := 64) (0x028#12)).toNat % 8 = 0
      rw [hs40]; have := hg.sp_align; omega
    · show LPins8 (sfvM3 g) (sfvSpE g + sign_extend (m := 64) (0x028#12)).toNat
        (bytes8 g.sv.s5)
      refine lpins8_of_pin8 (sfvM3_spill_pin8 g hg [sfvE_s0 g, sfvE_s4 g]
        [sfvE_ra g, sfvE_s1 g, sfvE_s2 g, sfvE_s3 g, sfvE_s6 g]
        _ _ (by simp only [sfvLog1, sfvLog2, sfvE_s0, sfvE_s4, sfvE_s5, sfvE_ra,
          sfvE_s1, sfvE_s2, sfvE_s3, sfvE_s6, List.cons_append, List.nil_append]) ?_ (by rw [hs40]; omega) (by rw [hs40]; omega))
      simp only [OutLRange, sfvE_ra, sfvE_s1, sfvE_s2, sfvE_s3, sfvE_s6,
        hs40, hs88, hs72, hs64, hs56, hs32, and_true]
      omega
  · -- jr: return-target alignment (the reloaded ra0)
    have ht : tohostAddr = 0x8001ad00 := rfl
    have h96 : 96 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
    have hs80 := sfv_slotAddr g hg (0x050#12) 80 (by decide) (by omega)
    have hs48 := sfv_slotAddr g hg (0x030#12) 48 (by decide) (by omega)
    have hs40 := sfv_slotAddr g hg (0x028#12) 40 (by decide) (by omega)
    have hs88 := sfv_slotAddr g hg (0x058#12) 88 (by decide) (by omega)
    have hs72 := sfv_slotAddr g hg (0x048#12) 72 (by decide) (by omega)
    have hs64 := sfv_slotAddr g hg (0x040#12) 64 (by decide) (by omega)
    have hs56 := sfv_slotAddr g hg (0x038#12) 56 (by decide) (by omega)
    have hs32 := sfv_slotAddr g hg (0x020#12) 32 (by decide) (by omega)
    show (BitVec.update (bytesVal MKind.ld (bytes8 g.ra0)
        + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
    rw [bytes8_val, hg.ra_fix]
    exact hg.ra_align

/-! ## Code-image transports onto the intermediate images -/

theorem sfvM1a_codeSf (g : SFVG) (hg : SFVGOk g) :
    Vsa.Sim.Code.__sfvwrite_rLoaded (sfvM1a g) :=
  Vsa.Sim.Code.sfvwrite_rLoaded_of_agree_lo (sfvM1a_agree_lo g hg) hg.codeSf

theorem sfvM1_codeSf (g : SFVG) (hg : SFVGOk g) :
    Vsa.Sim.Code.__sfvwrite_rLoaded (sfvM1 g) :=
  Vsa.Sim.Code.sfvwrite_rLoaded_of_agree_lo (sfvM1_agree_lo g hg) hg.codeSf

theorem sfvMC_codeSf (g : SFVG) (hg : SFVGOk g) :
    Vsa.Sim.Code.__sfvwrite_rLoaded (sfvMC g) :=
  Vsa.Sim.Code.sfvwrite_rLoaded_of_agree_lo (sfvMC_agree_lo g hg) hg.codeSf

theorem sfvM3_codeSf (g : SFVG) (hg : SFVGOk g) :
    Vsa.Sim.Code.__sfvwrite_rLoaded (sfvM3 g) :=
  Vsa.Sim.Code.sfvwrite_rLoaded_of_agree_lo (sfvM3_agree_lo g hg) hg.codeSf

/-- `sigmaPost_jalr` never touches `sailOutput` (the jalr twin of
`sailOutput_sigmaPost_jal`). -/
theorem sailOutput_sigmaPost_jalr (σ : MState) (pc vminstret tgt : BitVec 64)
    (rd_reg : Register) (link : RegisterType rd_reg) :
    (sigmaPost_jalr σ pc vminstret tgt rd_reg link).sailOutput = σ.sailOutput := rfl

/-- The outer (never-spilled) `s7..s11` keep list — the spilled `s1..s6` leave
`sKeepL` piecewise once `de94F`/`dec8F` overwrite them. -/
def sHiKeepL (v : SRegs) : GRegs :=
  [(23, v.s7), (24, v.s8), (25, v.s9), (26, v.s10), (27, v.s11)]

/-! ## Join-point predicates (one named-field structure per join) -/

/-- Parked at `0x8000de94` (resid ≠ 0, nothing changed yet). -/
structure SfvAtDe94 (g : SFVG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = g.m0
  pc : c.σ.regs.get? Register.PC = some 0x8000de94#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some g.reent
  a1 : gprGet c.σ 11 = some g.fp
  a2 : gprGet c.σ 12 = some g.uio
  ra : gprGet c.σ 1 = some g.ra0
  sp : gprGet c.σ 2 = some g.sp0
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.s00
  sregs : GHolds c.σ (sKeepL g.sv)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-- Parked at `0x8000dec0` (prologue done, `__SWR` on): flags in `a3`,
`s0/s5/s4 = fp/reent/uio`, frame at `sfvSpE`, first four spills landed. -/
structure SfvAtDec0 (g : SFVG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = sfvM1a g
  pc : c.σ.regs.get? Register.PC = some 0x8000dec0#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a1 : gprGet c.σ 11 = some g.fp
  a3 : gprGet c.σ 13 = some (sfvFlags g)
  sp : gprGet c.σ 2 = some (sfvSpE g)
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.fp
  s4 : gprGet c.σ 20 = some g.uio
  s5 : gprGet c.σ 21 = some g.reent
  s1o : gprGet c.σ 9 = some g.sv.s1
  s2o : gprGet c.σ 18 = some g.sv.s2
  s3o : gprGet c.σ 19 = some g.sv.s3
  s6o : gprGet c.σ 22 = some g.sv.s6
  shi : GHolds c.σ (sHiKeepL g.sv)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-- Parked at `0x8000dec8` (`_bf._base ≠ 0`). -/
structure SfvAtDec8 (g : SFVG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = sfvM1a g
  pc : c.σ.regs.get? Register.PC = some 0x8000dec8#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a3 : gprGet c.σ 13 = some (sfvFlags g)
  sp : gprGet c.σ 2 = some (sfvSpE g)
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.fp
  s4 : gprGet c.σ 20 = some g.uio
  s5 : gprGet c.σ 21 = some g.reent
  s1o : gprGet c.σ 9 = some g.sv.s1
  s2o : gprGet c.σ 18 = some g.sv.s2
  s3o : gprGet c.σ 19 = some g.sv.s3
  s6o : gprGet c.σ 22 = some g.sv.s6
  shi : GHolds c.σ (sHiKeepL g.sv)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-- Parked at `0x8000dee4` (`__SNBF` on — the unbuffered route committed):
all eight spills landed, `s1` = the iov pointer. -/
structure SfvAtDee4 (g : SFVG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = sfvM1 g
  pc : c.σ.regs.get? Register.PC = some 0x8000dee4#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  sp : gprGet c.σ 2 = some (sfvSpE g)
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.fp
  s4 : gprGet c.σ 20 = some g.uio
  s5 : gprGet c.σ 21 = some g.reent
  s1 : gprGet c.σ 9 = some g.iovp
  shi : GHolds c.σ (sHiKeepL g.sv)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-- Parked at the loop head `0x8000def4`, FIRST visit (`s2 = s3 = 0`,
clamp constant loaded). -/
structure SfvAtLoop1 (g : SFVG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = sfvM1 g
  pc : c.σ.regs.get? Register.PC = some 0x8000def4#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  sp : gprGet c.σ 2 = some (sfvSpE g)
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.fp
  s4 : gprGet c.σ 20 = some g.uio
  s5 : gprGet c.σ 21 = some g.reent
  s1 : gprGet c.σ 9 = some g.iovp
  s2 : gprGet c.σ 18 = some (0#64)
  s3 : gprGet c.σ 19 = some (0#64)
  s6 : gprGet c.σ 22 = some sfvClamp
  shi : GHolds c.σ (sHiKeepL g.sv)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-- Parked at `0x8000e0bc` (first `beqz s2` TAKEN — fetch the iov). -/
structure SfvAtE0bc (g : SFVG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = sfvM1 g
  pc : c.σ.regs.get? Register.PC = some 0x8000e0bc#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  sp : gprGet c.σ 2 = some (sfvSpE g)
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.fp
  s4 : gprGet c.σ 20 = some g.uio
  s5 : gprGet c.σ 21 = some g.reent
  s1 : gprGet c.σ 9 = some g.iovp
  s6 : gprGet c.σ 22 = some sfvClamp
  shi : GHolds c.σ (sHiKeepL g.sv)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-- Parked at the loop head `0x8000def4`, SECOND visit (`s3/s2` = the iov's
base/len, `s1` advanced past the consumed iov record). -/
structure SfvAtLoop2 (g : SFVG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = sfvM1 g
  pc : c.σ.regs.get? Register.PC = some 0x8000def4#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  sp : gprGet c.σ 2 = some (sfvSpE g)
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.fp
  s4 : gprGet c.σ 20 = some g.uio
  s5 : gprGet c.σ 21 = some g.reent
  s1 : gprGet c.σ 9 = some (g.iovp + sign_extend (m := 64) (0x010#12))
  s2 : gprGet c.σ 18 = some g.len
  s3 : gprGet c.σ 19 = some g.buf
  s6 : gprGet c.σ 22 = some sfvClamp
  shi : GHolds c.σ (sHiKeepL g.sv)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-- Parked at `0x8000df00` (second `beqz s2` FALL — a write to do):
`a2 = buf`, `a0 = reent` marshalled. -/
structure SfvAtDf00 (g : SFVG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = sfvM1 g
  pc : c.σ.regs.get? Register.PC = some 0x8000df00#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some g.reent
  a2 : gprGet c.σ 12 = some g.buf
  sp : gprGet c.σ 2 = some (sfvSpE g)
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.fp
  s4 : gprGet c.σ 20 = some g.uio
  s5 : gprGet c.σ 21 = some g.reent
  s1 : gprGet c.σ 9 = some (g.iovp + sign_extend (m := 64) (0x010#12))
  s2 : gprGet c.σ 18 = some g.len
  s3 : gprGet c.σ 19 = some g.buf
  s6 : gprGet c.σ 22 = some sfvClamp
  shi : GHolds c.σ (sHiKeepL g.sv)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-- Parked at `0x8000df10` (`bgeu` TAKEN — no clamp): `a3 = len`. -/
structure SfvAtDf10 (g : SFVG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = sfvM1 g
  pc : c.σ.regs.get? Register.PC = some 0x8000df10#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some g.reent
  a2 : gprGet c.σ 12 = some g.buf
  a3 : gprGet c.σ 13 = some g.len
  sp : gprGet c.σ 2 = some (sfvSpE g)
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.fp
  s4 : gprGet c.σ 20 = some g.uio
  s5 : gprGet c.σ 21 = some g.reent
  s1 : gprGet c.σ 9 = some (g.iovp + sign_extend (m := 64) (0x010#12))
  s2 : gprGet c.σ 18 = some g.len
  s3 : gprGet c.σ 19 = some g.buf
  s6 : gprGet c.σ 22 = some sfvClamp
  shi : GHolds c.σ (sHiKeepL g.sv)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-- Parked AT the `jalr a5` (`0x8000df1c`): `a5` = `__swrite`'s entry (read
off the `_write` vector), `a1` = the cookie (= `fp`), `a3` = the `sext.w`
image of `len` — the whole `SwFnPre` argument frame staged. -/
structure SfvAtJalr (g : SFVG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = sfvM1 g
  pc : c.σ.regs.get? Register.PC = some 0x8000df1c#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some g.reent
  a1 : gprGet c.σ 11 = some g.fp
  a2 : gprGet c.σ 12 = some g.buf
  a3 : gprGet c.σ 13 = some (sfvLenW g)
  a5 : gprGet c.σ 15 = some 0x8000efd4#64
  sp : gprGet c.σ 2 = some (sfvSpE g)
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.fp
  s4 : gprGet c.σ 20 = some g.uio
  s5 : gprGet c.σ 21 = some g.reent
  s1 : gprGet c.σ 9 = some (g.iovp + sign_extend (m := 64) (0x010#12))
  s2 : gprGet c.σ 18 = some g.len
  s3 : gprGet c.σ 19 = some g.buf
  s6 : gprGet c.σ 22 = some sfvClamp
  shi : GHolds c.σ (sHiKeepL g.sv)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-- Parked at `0x8000df24` (callee returned `a0 = len > 0`, `blez` FELL). -/
structure SfvAtDf24 (g : SFVG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = sfvMC g
  pc : c.σ.regs.get? Register.PC = some 0x8000df24#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some g.len
  sp : gprGet c.σ 2 = some (sfvSpE g)
  gp : gprGet c.σ 3 = some wrGpVal
  s2 : gprGet c.σ 18 = some g.len
  s3 : gprGet c.σ 19 = some g.buf
  s4 : gprGet c.σ 20 = some g.uio
  shi : GHolds c.σ (sHiKeepL g.sv)
  out : c.σ.sailOutput = pushBytes g.out0 g.bytes
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-- Parked at `0x8000df3c` (resid written back to 0, `bnez` FELL — the
epilogue begins). -/
structure SfvAtDf3c (g : SFVG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = sfvM3 g
  pc : c.σ.regs.get? Register.PC = some 0x8000df3c#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  sp : gprGet c.σ 2 = some (sfvSpE g)
  gp : gprGet c.σ 3 = some wrGpVal
  shi : GHolds c.σ (sHiKeepL g.sv)
  out : c.σ.sailOutput = pushBytes g.out0 g.bytes
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-- Parked at `0x8000df50` (`s1/s2/s3/s6` reloaded, `a0 = 0`). -/
structure SfvAtDf50 (g : SFVG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = sfvM3 g
  pc : c.σ.regs.get? Register.PC = some 0x8000df50#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some (0#64)
  sp : gprGet c.σ 2 = some (sfvSpE g)
  gp : gprGet c.σ 3 = some wrGpVal
  s1 : gprGet c.σ 9 = some g.sv.s1
  s2 : gprGet c.σ 18 = some g.sv.s2
  s3 : gprGet c.σ 19 = some g.sv.s3
  s6 : gprGet c.σ 22 = some g.sv.s6
  shi : GHolds c.σ (sHiKeepL g.sv)
  out : c.σ.sailOutput = pushBytes g.out0 g.bytes
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-! ## The summary pre/post -/

/-- `__sfvwrite_r`'s unbuffered-arm summary precondition (ABI entry
`0x8000de8c`): `(a0,a1,a2) = (reent, fp, uio)` with the real-stdout pin set
and the single-iov uio in `ok`. -/
structure SfvFnPre (g : SFVG) (c : Config) : Prop where
  ok : SFVGOk g
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = g.m0
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some g.reent
  a1 : gprGet c.σ 11 = some g.fp
  a2 : gprGet c.σ 12 = some g.uio
  ra : gprGet c.σ 1 = some g.ra0
  sp : gprGet c.σ 2 = some g.sp0
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.s00
  sregs : GHolds c.σ (sKeepL g.sv)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-- `__sfvwrite_r`'s unbuffered-arm summary post: returned to `ra0` with
`a0 = 0` (success), callee-saved registers RESTORED (the full `sKeepL g.sv`),
memory = the final image `sfvM3` (own spills + callee footprint + resid slot
zeroed), console extended by EXACTLY the buffer's byte string. -/
structure SfvFnPost (g : SFVG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = sfvM3 g
  pc : c.σ.regs.get? Register.PC = some g.ra0
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some (0#64)
  ra : gprGet c.σ 1 = some g.ra0
  sp : gprGet c.σ 2 = some g.sp0
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.s00
  sregs : GHolds c.σ (sKeepL g.sv)
  out : c.σ.sailOutput = pushBytes g.out0 g.bytes
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-! ## Empty write-log lemmas (no-store segs: `rw` the log away — NEVER `rfl`
the whole memory equation, whose head-congruence delta-unfolds the image
towers) -/

theorem sfvDec0F_log_nil (g : SFVG) :
    (evalBlocks sfvwrite_rXdec0FSeg
      (SegEvalState.init (sfvwrite_rXdec0FL g.fp) [bytes8 g.base])).log = [] := rfl

theorem sfvDee4_log_nil :
    (evalBlocks sfvwrite_rXdee4Seg (SegEvalState.init sfvwrite_rXdee4L [])).log
      = [] := rfl

/-! ## Arm Triples -/

/-- `de8c` entry: the resid load + `beqz` FALL (`resid = len ≠ 0`). -/
theorem sfvArmDe8c (g : SFVG) (hg : SFVGOk g) :
    Triple (fun c => PCAt 0x8000de8c#64 c ∧ SfvFnPre g c) (SfvAtDe94 g) := by
  have T := segRowFramed sfvwrite_rXde8cFSeg (sfvwrite_rXde8cFL g.uio)
    [bytes8 g.len] 0x8000de8c#64 g.m0
    ([(10, g.reent), (11, g.fp), (1, g.ra0), (2, g.sp0), (3, wrGpVal),
      (8, g.s00)] ++ sKeepL g.sv) g.out0 (0#4)
    (by show ChainOK 0x8000de8c#64 [12] sfvwrite_rXde8cFSeg; decide)
    (by show FrameOK [10, 11, 1, 2, 3, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
          sfvwrite_rXde8cFSeg
        decide)
  intro c hc
  obtain ⟨hpc, hp⟩ := hc
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hp.good, hp.mem, hpc, hp.minstret, ⟨hp.a2, trivial⟩,
        by show KeysOK [12]; decide,
        by rw [hp.mem]; exact sfvDe8cF_facts g hg hg.codeSf, hp.tick⟩
      keep := by
        obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, -⟩ := hp.sregs
        exact ⟨hp.a0, hp.a1, hp.ra, hp.sp, hp.gp, hp.s0,
          k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, trivial⟩
      out := hp.out
      pw := hp.pw
      th := hp.th }
  obtain ⟨ka0, ka1, kra, ksp, kgp, ks0, k1, k2, k3, k4, k5, k6, k7, k8, k9,
    k10, k11, -⟩ := h1.keep
  refine ⟨c1, hs1, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by rw [h1.mem]; rfl
      pc := by rw [h1.pc]; rfl
      minstret := h1.minstret
      a0 := ka0
      a1 := ka1
      a2 := gholds_lookup (v := g.uio) _ h1.regs (by rfl)
      ra := kra
      sp := ksp
      gp := kgp
      s0 := ks0
      sregs := ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, trivial⟩
      out := h1.out
      pw := h1.pw
      th := h1.th }

/-- `de94` prologue: flags load, frame, first four spills, `__SWR` guard FALL. -/
theorem sfvArmDe94 (g : SFVG) (hg : SFVGOk g) :
    Triple (SfvAtDe94 g) (SfvAtDec0 g) := by
  have T := segRowFramed sfvwrite_rXde94FSeg (sfvL1 g) [[g.fl0, g.fl1]]
    0x8000de94#64 g.m0
    ([(3, wrGpVal), (9, g.sv.s1), (18, g.sv.s2), (19, g.sv.s3), (22, g.sv.s6)]
      ++ sHiKeepL g.sv) g.out0 (0#4)
    (by show ChainOK 0x8000de94#64 [11, 2, 8, 20, 21, 1, 10, 12] sfvwrite_rXde94FSeg
        decide)
    (by show FrameOK [3, 9, 18, 19, 22, 23, 24, 25, 26, 27] sfvwrite_rXde94FSeg
        decide)
  intro c hA
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, -⟩ := hA.sregs
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hA.good, hA.mem, hA.pc, hA.minstret,
        ⟨hA.a1, hA.sp, hA.s0, v4, v5, hA.ra, hA.a0, hA.a2, trivial⟩,
        by show KeysOK [11, 2, 8, 20, 21, 1, 10, 12]; decide,
        by rw [hA.mem]; exact sfvDe94F_facts g hg hg.codeSf, hA.tick⟩
      keep := ⟨hA.gp, v1, v2, v3, v6, v7, v8, v9, v10, v11, trivial⟩
      out := hA.out
      pw := hA.pw
      th := hA.th }
  obtain ⟨kgp, k1, k2, k3, k6, k7, k8, k9, k10, k11, -⟩ := h1.keep
  refine ⟨c1, hs1, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by rw [h1.mem]; rfl
      pc := by rw [h1.pc]; rfl
      minstret := h1.minstret
      a1 := by
        have h := gholds_lookup (n := 11) (v := g.fp) _ h1.regs (by rfl)
        exact h
      a3 := gholds_lookup (v := sfvFlags g) _ h1.regs (by rfl)
      sp := gholds_lookup (v := sfvSpE g) _ h1.regs (by rfl)
      gp := kgp
      s0 := by
        have h := gholds_lookup (n := 8)
          (v := g.fp + sign_extend (m := 64) (0x000#12)) _ h1.regs (by rfl)
        rwa [addi0_env] at h
      s4 := by
        have h := gholds_lookup (n := 20)
          (v := g.uio + sign_extend (m := 64) (0x000#12)) _ h1.regs (by rfl)
        rwa [addi0_env] at h
      s5 := by
        have h := gholds_lookup (n := 21)
          (v := g.reent + sign_extend (m := 64) (0x000#12)) _ h1.regs (by rfl)
        rwa [addi0_env] at h
      s1o := k1
      s2o := k2
      s3o := k3
      s6o := k6
      shi := ⟨k7, k8, k9, k10, k11, trivial⟩
      out := h1.out
      pw := h1.pw
      th := h1.th }

/-- `dec0`: the `_bf._base` load + `beqz` FALL (`base ≠ 0`). -/
theorem sfvArmDec0 (g : SFVG) (hg : SFVGOk g) :
    Triple (SfvAtDec0 g) (SfvAtDec8 g) := by
  have T := segRowFramed sfvwrite_rXdec0FSeg (sfvwrite_rXdec0FL g.fp)
    [bytes8 g.base] 0x8000dec0#64 (sfvM1a g)
    ([(2, sfvSpE g), (3, wrGpVal), (8, g.fp), (13, sfvFlags g), (20, g.uio),
      (21, g.reent), (9, g.sv.s1), (18, g.sv.s2), (19, g.sv.s3), (22, g.sv.s6)]
      ++ sHiKeepL g.sv) g.out0 (0#4)
    (by show ChainOK 0x8000dec0#64 [11] sfvwrite_rXdec0FSeg; decide)
    (by show FrameOK [2, 3, 8, 13, 20, 21, 9, 18, 19, 22, 23, 24, 25, 26, 27]
          sfvwrite_rXdec0FSeg
        decide)
  intro c hA
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hA.good, hA.mem, hA.pc, hA.minstret, ⟨hA.a1, trivial⟩,
        by show KeysOK [11]; decide,
        by rw [hA.mem]; exact sfvDec0F_facts g hg (sfvM1a_codeSf g hg), hA.tick⟩
      keep := by
        obtain ⟨k7, k8, k9, k10, k11, -⟩ := hA.shi
        exact ⟨hA.sp, hA.gp, hA.s0, hA.a3, hA.s4, hA.s5, hA.s1o, hA.s2o,
          hA.s3o, hA.s6o, k7, k8, k9, k10, k11, trivial⟩
      out := hA.out
      pw := hA.pw
      th := hA.th }
  obtain ⟨ksp, kgp, ks0, ka3, ks4, ks5, k1, k2, k3, k6, k7, k8, k9, k10, k11, -⟩
    := h1.keep
  refine ⟨c1, hs1, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by rw [h1.mem, sfvDec0F_log_nil g, writeLog_nil]
      pc := by rw [h1.pc]; rfl
      minstret := h1.minstret
      a3 := ka3
      sp := ksp
      gp := kgp
      s0 := ks0
      s4 := ks4
      s5 := ks5
      s1o := k1
      s2o := k2
      s3o := k3
      s6o := k6
      shi := ⟨k7, k8, k9, k10, k11, trivial⟩
      out := h1.out
      pw := h1.pw
      th := h1.th }

/-- `dec8`: the second four spills, `__SNBF` guard FALL, `s1 := uio_iov`. -/
theorem sfvArmDec8 (g : SFVG) (hg : SFVGOk g) :
    Triple (SfvAtDec8 g) (SfvAtDee4 g) := by
  have T := segRowFramed sfvwrite_rXdec8FSeg (sfvL2 g) [bytes8 g.iovp]
    0x8000dec8#64 (sfvM1a g)
    ([(3, wrGpVal), (8, g.fp), (21, g.reent)] ++ sHiKeepL g.sv) g.out0 (0#4)
    (by show ChainOK 0x8000dec8#64 [9, 2, 18, 19, 22, 13, 20] sfvwrite_rXdec8FSeg
        decide)
    (by show FrameOK [3, 8, 21, 23, 24, 25, 26, 27] sfvwrite_rXdec8FSeg; decide)
  intro c hA
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hA.good, hA.mem, hA.pc, hA.minstret,
        ⟨hA.s1o, hA.sp, hA.s2o, hA.s3o, hA.s6o, hA.a3, hA.s4, trivial⟩,
        by show KeysOK [9, 2, 18, 19, 22, 13, 20]; decide,
        by rw [hA.mem]; exact sfvDec8F_facts g hg (sfvM1a_codeSf g hg), hA.tick⟩
      keep := by
        obtain ⟨k7, k8, k9, k10, k11, -⟩ := hA.shi
        exact ⟨hA.gp, hA.s0, hA.s5, k7, k8, k9, k10, k11, trivial⟩
      out := hA.out
      pw := hA.pw
      th := hA.th }
  obtain ⟨kgp, ks0, ks5, k7, k8, k9, k10, k11, -⟩ := h1.keep
  refine ⟨c1, hs1, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by rw [h1.mem]; rfl
      pc := by rw [h1.pc]; rfl
      minstret := h1.minstret
      sp := gholds_lookup (v := sfvSpE g) _ h1.regs (by rfl)
      gp := kgp
      s0 := ks0
      s4 := gholds_lookup (v := g.uio) _ h1.regs (by rfl)
      s5 := ks5
      s1 := by
        have h := gholds_lookup (n := 9)
          (v := bytesVal MKind.ld (bytes8 g.iovp)) _ h1.regs (by rfl)
        rwa [bytes8_val] at h
      shi := ⟨k7, k8, k9, k10, k11, trivial⟩
      out := h1.out
      pw := h1.pw
      th := h1.th }

/-- `dee4`: pure ALU — clamp constant + `s3 := 0`, `s2 := 0`. -/
theorem sfvArmDee4 (g : SFVG) (hg : SFVGOk g) :
    Triple (SfvAtDee4 g) (SfvAtLoop1 g) := by
  have T := segRowFramed sfvwrite_rXdee4Seg sfvwrite_rXdee4L []
    0x8000dee4#64 (sfvM1 g)
    ([(2, sfvSpE g), (3, wrGpVal), (8, g.fp), (20, g.uio), (21, g.reent),
      (9, g.iovp)] ++ sHiKeepL g.sv) g.out0 (0#4)
    (by show ChainOK 0x8000dee4#64 [] sfvwrite_rXdee4Seg; decide)
    (by show FrameOK [2, 3, 8, 20, 21, 9, 23, 24, 25, 26, 27] sfvwrite_rXdee4Seg
        decide)
  intro c hA
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hA.good, hA.mem, hA.pc, hA.minstret, trivial,
        by show KeysOK []; decide,
        by rw [hA.mem]; exact sfvDee4_facts g hg (sfvM1_codeSf g hg), hA.tick⟩
      keep := by
        obtain ⟨k7, k8, k9, k10, k11, -⟩ := hA.shi
        exact ⟨hA.sp, hA.gp, hA.s0, hA.s4, hA.s5, hA.s1, k7, k8, k9, k10, k11,
          trivial⟩
      out := hA.out
      pw := hA.pw
      th := hA.th }
  obtain ⟨ksp, kgp, ks0, ks4, ks5, ks1, k7, k8, k9, k10, k11, -⟩ := h1.keep
  refine ⟨c1, hs1, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by rw [h1.mem, sfvDee4_log_nil, writeLog_nil]
      pc := by rw [h1.pc]; rfl
      minstret := h1.minstret
      sp := ksp
      gp := kgp
      s0 := ks0
      s4 := ks4
      s5 := ks5
      s1 := ks1
      s2 := by
        have h := gholds_lookup (n := 18)
          (v := (0#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) _ h1.regs (by rfl)
        rwa [addi0_env] at h
      s3 := by
        have h := gholds_lookup (n := 19)
          (v := (0#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) _ h1.regs (by rfl)
        rwa [addi0_env] at h
      s6 := gholds_lookup (v := sfvClamp) _ h1.regs (by rfl)
      shi := ⟨k7, k8, k9, k10, k11, trivial⟩
      out := h1.out
      pw := h1.pw
      th := h1.th }

theorem sfvDef4T_log_nil (g : SFVG) :
    (evalBlocks sfvwrite_rXdef4TSeg
      (SegEvalState.init (sfvwrite_rXdef4TL 0#64 g.reent 0#64) [])).log = [] := rfl

theorem sfvE0bc_log_nil (g : SFVG) :
    (evalBlocks sfvwrite_rXe0bcSeg
      (SegEvalState.init (sfvwrite_rXe0bcL g.iovp)
        [bytes8 g.buf, bytes8 g.len])).log = [] := rfl

theorem sfvDef4F_log_nil (g : SFVG) :
    (evalBlocks sfvwrite_rXdef4FSeg
      (SegEvalState.init (sfvwrite_rXdef4FL g.buf g.reent g.len) [])).log = [] := rfl

theorem sfvDf00T_log_nil (g : SFVG) :
    (evalBlocks sfvwrite_rXdf00TSeg
      (SegEvalState.init (sfvwrite_rXdf00TL g.len sfvClamp) [])).log = [] := rfl

theorem sfvDf10_log_nil (g : SFVG) :
    (evalBlocks sfvwrite_rXdf10Seg
      (SegEvalState.init (sfvwrite_rXdf10L g.fp g.len)
        [bytes8 0x8000efd4#64, bytes8 g.fp])).log = [] := rfl

/-- Loop head, FIRST visit: `beqz s2` TAKEN (`s2 = 0`) → the iov fetch. -/
theorem sfvArmLoop1 (g : SFVG) (hg : SFVGOk g) :
    Triple (SfvAtLoop1 g) (SfvAtE0bc g) := by
  have T := segRowFramed sfvwrite_rXdef4TSeg (sfvwrite_rXdef4TL 0#64 g.reent 0#64) []
    0x8000def4#64 (sfvM1 g)
    ([(2, sfvSpE g), (3, wrGpVal), (8, g.fp), (20, g.uio), (9, g.iovp),
      (22, sfvClamp)] ++ sHiKeepL g.sv) g.out0 (0#4)
    (by show ChainOK 0x8000def4#64 [19, 21, 18] sfvwrite_rXdef4TSeg; decide)
    (by show FrameOK [2, 3, 8, 20, 9, 22, 23, 24, 25, 26, 27] sfvwrite_rXdef4TSeg
        decide)
  intro c hA
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hA.good, hA.mem, hA.pc, hA.minstret,
        ⟨hA.s3, hA.s5, hA.s2, trivial⟩,
        by show KeysOK [19, 21, 18]; decide,
        by rw [hA.mem]; exact sfvDef4T_facts g hg (sfvM1_codeSf g hg), hA.tick⟩
      keep := by
        obtain ⟨k7, k8, k9, k10, k11, -⟩ := hA.shi
        exact ⟨hA.sp, hA.gp, hA.s0, hA.s4, hA.s1, hA.s6, k7, k8, k9, k10, k11,
          trivial⟩
      out := hA.out
      pw := hA.pw
      th := hA.th }
  obtain ⟨ksp, kgp, ks0, ks4, ks1, ks6, k7, k8, k9, k10, k11, -⟩ := h1.keep
  refine ⟨c1, hs1, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by rw [h1.mem, sfvDef4T_log_nil g, writeLog_nil]
      pc := by rw [h1.pc]; rfl
      minstret := h1.minstret
      sp := ksp
      gp := kgp
      s0 := ks0
      s4 := ks4
      s5 := gholds_lookup (v := g.reent) _ h1.regs (by rfl)
      s1 := ks1
      s6 := ks6
      shi := ⟨k7, k8, k9, k10, k11, trivial⟩
      out := h1.out
      pw := h1.pw
      th := h1.th }

/-- `e0bc`: the iov record loads (`s3 := base`, `s2 := len`), cursor advance,
`j` back to the loop head. -/
theorem sfvArmE0bc (g : SFVG) (hg : SFVGOk g) :
    Triple (SfvAtE0bc g) (SfvAtLoop2 g) := by
  have T := segRowFramed sfvwrite_rXe0bcSeg (sfvwrite_rXe0bcL g.iovp)
    [bytes8 g.buf, bytes8 g.len]
    0x8000e0bc#64 (sfvM1 g)
    ([(2, sfvSpE g), (3, wrGpVal), (8, g.fp), (20, g.uio), (21, g.reent),
      (22, sfvClamp)] ++ sHiKeepL g.sv) g.out0 (0#4)
    (by show ChainOK 0x8000e0bc#64 [9] sfvwrite_rXe0bcSeg; decide)
    (by show FrameOK [2, 3, 8, 20, 21, 22, 23, 24, 25, 26, 27] sfvwrite_rXe0bcSeg
        decide)
  intro c hA
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hA.good, hA.mem, hA.pc, hA.minstret, ⟨hA.s1, trivial⟩,
        by show KeysOK [9]; decide,
        by rw [hA.mem]; exact sfvE0bc_facts g hg (sfvM1_codeSf g hg), hA.tick⟩
      keep := by
        obtain ⟨k7, k8, k9, k10, k11, -⟩ := hA.shi
        exact ⟨hA.sp, hA.gp, hA.s0, hA.s4, hA.s5, hA.s6, k7, k8, k9, k10, k11,
          trivial⟩
      out := hA.out
      pw := hA.pw
      th := hA.th }
  obtain ⟨ksp, kgp, ks0, ks4, ks5, ks6, k7, k8, k9, k10, k11, -⟩ := h1.keep
  refine ⟨c1, hs1, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by rw [h1.mem, sfvE0bc_log_nil g, writeLog_nil]
      pc := by rw [h1.pc]; rfl
      minstret := h1.minstret
      sp := ksp
      gp := kgp
      s0 := ks0
      s4 := ks4
      s5 := ks5
      s1 := gholds_lookup (v := g.iovp + sign_extend (m := 64) (0x010#12)) _
        h1.regs (by rfl)
      s2 := by
        have h := gholds_lookup (n := 18)
          (v := bytesVal MKind.ld (bytes8 g.len)) _ h1.regs (by rfl)
        rwa [bytes8_val] at h
      s3 := by
        have h := gholds_lookup (n := 19)
          (v := bytesVal MKind.ld (bytes8 g.buf)) _ h1.regs (by rfl)
        rwa [bytes8_val] at h
      s6 := ks6
      shi := ⟨k7, k8, k9, k10, k11, trivial⟩
      out := h1.out
      pw := h1.pw
      th := h1.th }

/-- Loop head, SECOND visit: `beqz s2` FALL (`s2 = len ≠ 0`) — marshal
`a2 := buf`, `a0 := reent`. -/
theorem sfvArmLoop2 (g : SFVG) (hg : SFVGOk g) :
    Triple (SfvAtLoop2 g) (SfvAtDf00 g) := by
  have T := segRowFramed sfvwrite_rXdef4FSeg (sfvwrite_rXdef4FL g.buf g.reent g.len) []
    0x8000def4#64 (sfvM1 g)
    ([(2, sfvSpE g), (3, wrGpVal), (8, g.fp), (20, g.uio),
      (9, g.iovp + sign_extend (m := 64) (0x010#12)), (22, sfvClamp)]
      ++ sHiKeepL g.sv) g.out0 (0#4)
    (by show ChainOK 0x8000def4#64 [19, 21, 18] sfvwrite_rXdef4FSeg; decide)
    (by show FrameOK [2, 3, 8, 20, 9, 22, 23, 24, 25, 26, 27] sfvwrite_rXdef4FSeg
        decide)
  intro c hA
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hA.good, hA.mem, hA.pc, hA.minstret,
        ⟨hA.s3, hA.s5, hA.s2, trivial⟩,
        by show KeysOK [19, 21, 18]; decide,
        by rw [hA.mem]; exact sfvDef4F_facts g hg (sfvM1_codeSf g hg), hA.tick⟩
      keep := by
        obtain ⟨k7, k8, k9, k10, k11, -⟩ := hA.shi
        exact ⟨hA.sp, hA.gp, hA.s0, hA.s4, hA.s1, hA.s6, k7, k8, k9, k10, k11,
          trivial⟩
      out := hA.out
      pw := hA.pw
      th := hA.th }
  obtain ⟨ksp, kgp, ks0, ks4, ks1, ks6, k7, k8, k9, k10, k11, -⟩ := h1.keep
  refine ⟨c1, hs1, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by rw [h1.mem, sfvDef4F_log_nil g, writeLog_nil]
      pc := by rw [h1.pc]; rfl
      minstret := h1.minstret
      a0 := by
        have h := gholds_lookup (n := 10)
          (v := g.reent + sign_extend (m := 64) (0x000#12)) _ h1.regs (by rfl)
        rwa [addi0_env] at h
      a2 := by
        have h := gholds_lookup (n := 12)
          (v := g.buf + sign_extend (m := 64) (0x000#12)) _ h1.regs (by rfl)
        rwa [addi0_env] at h
      sp := ksp
      gp := kgp
      s0 := ks0
      s4 := ks4
      s5 := gholds_lookup (v := g.reent) _ h1.regs (by rfl)
      s1 := ks1
      s2 := gholds_lookup (v := g.len) _ h1.regs (by rfl)
      s3 := gholds_lookup (v := g.buf) _ h1.regs (by rfl)
      s6 := ks6
      shi := ⟨k7, k8, k9, k10, k11, trivial⟩
      out := h1.out
      pw := h1.pw
      th := h1.th }

/-- `df00`: `a3 := s2`, `bgeu s6,s2` TAKEN (`len ≤ clamp` — no clamping). -/
theorem sfvArmDf00 (g : SFVG) (hg : SFVGOk g) :
    Triple (SfvAtDf00 g) (SfvAtDf10 g) := by
  have T := segRowFramed sfvwrite_rXdf00TSeg (sfvwrite_rXdf00TL g.len sfvClamp) []
    0x8000df00#64 (sfvM1 g)
    ([(2, sfvSpE g), (3, wrGpVal), (8, g.fp), (20, g.uio), (21, g.reent),
      (9, g.iovp + sign_extend (m := 64) (0x010#12)), (19, g.buf),
      (10, g.reent), (12, g.buf)] ++ sHiKeepL g.sv) g.out0 (0#4)
    (by show ChainOK 0x8000df00#64 [18, 22] sfvwrite_rXdf00TSeg; decide)
    (by show FrameOK [2, 3, 8, 20, 21, 9, 19, 10, 12, 23, 24, 25, 26, 27]
          sfvwrite_rXdf00TSeg
        decide)
  intro c hA
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hA.good, hA.mem, hA.pc, hA.minstret,
        ⟨hA.s2, hA.s6, trivial⟩,
        by show KeysOK [18, 22]; decide,
        by rw [hA.mem]; exact sfvDf00T_facts g hg (sfvM1_codeSf g hg), hA.tick⟩
      keep := by
        obtain ⟨k7, k8, k9, k10, k11, -⟩ := hA.shi
        exact ⟨hA.sp, hA.gp, hA.s0, hA.s4, hA.s5, hA.s1, hA.s3, hA.a0, hA.a2,
          k7, k8, k9, k10, k11, trivial⟩
      out := hA.out
      pw := hA.pw
      th := hA.th }
  obtain ⟨ksp, kgp, ks0, ks4, ks5, ks1, ks3, ka0, ka2, k7, k8, k9, k10, k11, -⟩
    := h1.keep
  refine ⟨c1, hs1, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by rw [h1.mem, sfvDf00T_log_nil g, writeLog_nil]
      pc := by rw [h1.pc]; rfl
      minstret := h1.minstret
      a0 := ka0
      a2 := ka2
      a3 := by
        have h := gholds_lookup (n := 13)
          (v := g.len + sign_extend (m := 64) (0x000#12)) _ h1.regs (by rfl)
        rwa [addi0_env] at h
      sp := ksp
      gp := kgp
      s0 := ks0
      s4 := ks4
      s5 := ks5
      s1 := ks1
      s2 := gholds_lookup (v := g.len) _ h1.regs (by rfl)
      s3 := ks3
      s6 := gholds_lookup (v := sfvClamp) _ h1.regs (by rfl)
      shi := ⟨k7, k8, k9, k10, k11, trivial⟩
      out := h1.out
      pw := h1.pw
      th := h1.th }

/-- `df10`: the `_write` vector + cookie loads, `sext.w a3` — parked AT the
`jalr a5`. -/
theorem sfvArmDf10 (g : SFVG) (hg : SFVGOk g) :
    Triple (SfvAtDf10 g) (SfvAtJalr g) := by
  have T := segRowFramed sfvwrite_rXdf10Seg (sfvwrite_rXdf10L g.fp g.len)
    [bytes8 0x8000efd4#64, bytes8 g.fp]
    0x8000df10#64 (sfvM1 g)
    ([(2, sfvSpE g), (3, wrGpVal), (20, g.uio), (21, g.reent),
      (9, g.iovp + sign_extend (m := 64) (0x010#12)), (18, g.len), (19, g.buf),
      (22, sfvClamp), (10, g.reent), (12, g.buf)] ++ sHiKeepL g.sv) g.out0 (0#4)
    (by show ChainOK 0x8000df10#64 [8, 13] sfvwrite_rXdf10Seg; decide)
    (by show FrameOK [2, 3, 20, 21, 9, 18, 19, 22, 10, 12, 23, 24, 25, 26, 27]
          sfvwrite_rXdf10Seg
        decide)
  intro c hA
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hA.good, hA.mem, hA.pc, hA.minstret,
        ⟨hA.s0, hA.a3, trivial⟩,
        by show KeysOK [8, 13]; decide,
        by rw [hA.mem]; exact sfvDf10_facts g hg (sfvM1_codeSf g hg), hA.tick⟩
      keep := by
        obtain ⟨k7, k8, k9, k10, k11, -⟩ := hA.shi
        exact ⟨hA.sp, hA.gp, hA.s4, hA.s5, hA.s1, hA.s2, hA.s3, hA.s6, hA.a0,
          hA.a2, k7, k8, k9, k10, k11, trivial⟩
      out := hA.out
      pw := hA.pw
      th := hA.th }
  obtain ⟨ksp, kgp, ks4, ks5, ks1, ks2, ks3, ks6, ka0, ka2, k7, k8, k9, k10,
    k11, -⟩ := h1.keep
  refine ⟨c1, hs1, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by rw [h1.mem, sfvDf10_log_nil g, writeLog_nil]
      pc := by rw [h1.pc]; rfl
      minstret := h1.minstret
      a0 := ka0
      a1 := by
        have h := gholds_lookup (n := 11)
          (v := bytesVal MKind.ld (bytes8 g.fp)) _ h1.regs (by rfl)
        rwa [bytes8_val] at h
      a2 := ka2
      a3 := gholds_lookup (v := sfvLenW g) _ h1.regs (by rfl)
      a5 := by
        have h := gholds_lookup (n := 15)
          (v := bytesVal MKind.ld (bytes8 0x8000efd4#64)) _ h1.regs (by rfl)
        rwa [bytes8_val] at h
      sp := ksp
      gp := kgp
      s0 := gholds_lookup (v := g.fp) _ h1.regs (by rfl)
      s4 := ks4
      s5 := ks5
      s1 := ks1
      s2 := ks2
      s3 := ks3
      s6 := ks6
      shi := ⟨k7, k8, k9, k10, k11, trivial⟩
      out := h1.out
      pw := h1.pw
      th := h1.th }

/-- The `jalr` target is the entry itself (bit-0 clear is a no-op on the
4-aligned `__swrite` entry). -/
theorem sfv_jalr_tgt :
    BitVec.update (0x8000efd4#64 + sign_extend (m := 64) (0x000#12)) 0 0#1
      = 0x8000efd4#64 := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **The `jalr fp->_write` SEAM** (`0x8000df1c`): one `stepObs_jalr` step
from the parked config lands at `__swrite`'s ABI entry with P3's whole
precondition marshalled (`ra := 0x8000df20`, args/frame transported by the
`obs_jalr_*` accessors, memory untouched). -/
theorem sfvArmJalr (g : SFVG) (hg : SFVGOk g) :
    Triple (SfvAtJalr g)
      (fun c => PCAt 0x8000efd4#64 c ∧ SwFnPre (sfvSWG g) c) := by
  intro c hA
  obtain ⟨vm1, hmi1⟩ := hA.minstret
  have hcSf : Vsa.Sim.Code.__sfvwrite_rLoaded c.σ.mem := by
    rw [hA.mem]; exact sfvM1_codeSf g hg
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.__sfvwrite_r_at_8000df1c hcSf
  obtain ⟨σ2, i2, hstep, hi2, hG2, hmem2, hobs⟩ :=
    stepObs_jalr c.σ c.tick c.steps (0x8000df1c#64) vm1 (0x8000efd4#64)
      (0x000780e7#32) (0x000#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x01#5)
      Register.x1 (BitVec.addInt (0x8000df1c#64) 4)
      (0xe7#8) (0x80#8) (0x07#8) (0x00#8)
      hA.good hA.pc hmi1 hb0 hb1 hb2 hb3
      (by decide) (by decide) (by decide)
      (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_000780e7 (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hA.good.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hA.good.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hA.good.mseccfg))
      (rX_bits_x15 _ (0x8000efd4#64)
        (by rw [get?_afterNextPC c.σ (0x8000df1c#64) _ (by decide) (by decide)]
            exact hA.a5))
      (by rw [sfv_jalr_tgt]; decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000df1c#64) 4))
      hA.tick
  rw [sfv_jalr_tgt] at hobs
  refine ⟨⟨σ2, i2, c.steps + 1⟩, Steps.head hstep (Steps.refl _), ?_, ?_⟩
  · show σ2.regs.get? Register.PC = some 0x8000efd4#64
    exact obs_jalr_pc hobs
  · exact
      { ok := sfvSWG_ok g hg
        good := hG2
        tick := hi2
        mem := hmem2.trans hA.mem
        minstret := obs_jalr_minstret hobs
        a0 := obs_jalr_other hobs Register.x10 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.a0
        a1 := obs_jalr_other hobs Register.x11 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.a1
        a2 := obs_jalr_other hobs Register.x12 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.a2
        a3 := obs_jalr_other hobs Register.x13 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.a3
        ra := by
          have h := obs_jalr_rd hobs (by decide) (by decide) (by decide)
            (by decide) (by decide)
          show gprGet σ2 1 = some 0x8000df20#64
          rwa [show BitVec.addInt (0x8000df1c#64) 4 = (0x8000df20#64 : BitVec 64)
            from by apply BitVec.eq_of_toNat_eq; decide] at h
        sp := obs_jalr_other hobs Register.x2 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.sp
        gp := obs_jalr_other hobs Register.x3 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.gp
        s0 := obs_jalr_other hobs Register.x8 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) hA.s0
        sregs := by
          obtain ⟨k7, k8, k9, k10, k11, -⟩ := hA.shi
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
          · show gprGet σ2 9
              = some (bytesVal MKind.ld (bytes8 g.iovp) + sign_extend (m := 64) (0x010#12))
            rw [bytes8_val]
            exact obs_jalr_other hobs Register.x9 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) hA.s1
          · exact obs_jalr_other hobs Register.x18 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) hA.s2
          · exact obs_jalr_other hobs Register.x19 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) hA.s3
          · exact obs_jalr_other hobs Register.x20 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) hA.s4
          · exact obs_jalr_other hobs Register.x21 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) hA.s5
          · exact obs_jalr_other hobs Register.x22 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) hA.s6
          · exact obs_jalr_other hobs Register.x23 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k7
          · exact obs_jalr_other hobs Register.x24 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k8
          · exact obs_jalr_other hobs Register.x25 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k9
          · exact obs_jalr_other hobs Register.x26 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k10
          · exact obs_jalr_other hobs Register.x27 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) k11
        out := hobs.2.trans ((sailOutput_sigmaPost_jalr c.σ (0x8000df1c#64) vm1
          (0x8000efd4#64) Register.x1 (BitVec.addInt (0x8000df1c#64) 4)).trans hA.out)
        pw := obs_jalr_other hobs Register.htif_payload_writes (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hA.pw
        th := by
          obtain ⟨v, hv⟩ := hA.th
          exact ⟨v, obs_jalr_other hobs Register.htif_tohost (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hv⟩ }

theorem sfvDf20F_log_nil (g : SFVG) :
    (evalBlocks sfvwrite_rXdf20FSeg
      (SegEvalState.init (sfvwrite_rXdf20FL g.len) [])).log = [] := rfl

theorem sfvDf3c_log_nil (g : SFVG) :
    (evalBlocks sfvwrite_rXdf3cSeg
      (SegEvalState.init (sfvwrite_rXdf3cL (sfvSpE g))
        [bytes8 g.sv.s1, bytes8 g.sv.s2, bytes8 g.sv.s3, bytes8 g.sv.s6])).log
      = [] := rfl

theorem sfvDf50_log_nil (g : SFVG) :
    (evalBlocks sfvwrite_rXdf50Seg
      (SegEvalState.init (sfvwrite_rXdf50L (sfvSpE g))
        [bytes8 g.ra0, bytes8 g.s00, bytes8 g.sv.s4, bytes8 g.sv.s5])).log
      = [] := rfl

/-- `df20`: the callee returned (`a0 = len > 0`), `blez` FALL — from P3's
summary post to the write-back block. -/
theorem sfvArmDf20 (g : SFVG) (hg : SFVGOk g) :
    Triple (WriteRFnPost (swWRG (sfvSWG g))) (SfvAtDf24 g) := by
  have hlen31 : g.len.toNat < 2 ^ 31 := by have := hg.len_le; omega
  have T := segRowFramed sfvwrite_rXdf20FSeg (sfvwrite_rXdf20FL g.len) []
    0x8000df20#64 (sfvMC g)
    ([(2, sfvSpE g), (3, wrGpVal), (18, g.len), (19, g.buf), (20, g.uio)]
      ++ sHiKeepL g.sv) (pushBytes g.out0 g.bytes) (0#4)
    (by show ChainOK 0x8000df20#64 [10] sfvwrite_rXdf20FSeg; decide)
    (by show FrameOK [2, 3, 18, 19, 20, 23, 24, 25, 26, 27] sfvwrite_rXdf20FSeg
        decide)
  intro c hP
  have ha0 : gprGet c.σ 10 = some g.len := by
    have h : gprGet c.σ 10 = some (sfvLenW g) := hP.a0
    rwa [sfvLenW_id g hlen31] at h
  obtain ⟨hs1', hs2', hs3', hs4', hs5', hs6', k7, k8, k9, k10, k11, -⟩ := hP.sregs
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hP.good, hP.mem, hP.pc, hP.minstret, ⟨ha0, trivial⟩,
        by show KeysOK [10]; decide,
        by rw [show c.σ.mem = sfvMC g from hP.mem]
           exact sfvDf20F_facts g hg (sfvMC_codeSf g hg), hP.tick⟩
      keep := ⟨hP.sp, hP.gp, hs2', hs3', hs4', k7, k8, k9, k10, k11, trivial⟩
      out := hP.out
      pw := hP.pw
      th := hP.th }
  obtain ⟨ksp, kgp, ks2, ks3, ks4, k7', k8', k9', k10', k11', -⟩ := h1.keep
  refine ⟨c1, hs1, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by rw [h1.mem, sfvDf20F_log_nil g, writeLog_nil]
      pc := by rw [h1.pc]; rfl
      minstret := h1.minstret
      a0 := gholds_lookup (v := g.len) _ h1.regs (by rfl)
      sp := ksp
      gp := kgp
      s2 := ks2
      s3 := ks3
      s4 := ks4
      shi := ⟨k7', k8', k9', k10', k11', trivial⟩
      out := h1.out
      pw := h1.pw
      th := h1.th }

/-- `df24`: resid readback, cursor arithmetic, the resid write-back
(`sd a5,16(s4)` — the value computes to 0), `bnez` FALL. -/
theorem sfvArmDf24 (g : SFVG) (hg : SFVGOk g) :
    Triple (SfvAtDf24 g) (SfvAtDf3c g) := by
  have T := segRowFramed sfvwrite_rXdf24FSeg
    (sfvwrite_rXdf24FL g.uio g.buf g.len g.len) [bytes8 g.len]
    0x8000df24#64 (sfvMC g)
    ([(2, sfvSpE g), (3, wrGpVal)] ++ sHiKeepL g.sv)
    (pushBytes g.out0 g.bytes) (0#4)
    (by show ChainOK 0x8000df24#64 [20, 19, 10, 18] sfvwrite_rXdf24FSeg; decide)
    (by show FrameOK [2, 3, 23, 24, 25, 26, 27] sfvwrite_rXdf24FSeg; decide)
  intro c hA
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hA.good, hA.mem, hA.pc, hA.minstret,
        ⟨hA.s4, hA.s3, hA.a0, hA.s2, trivial⟩,
        by show KeysOK [20, 19, 10, 18]; decide,
        by rw [hA.mem]; exact sfvDf24F_facts g hg (sfvMC_codeSf g hg), hA.tick⟩
      keep := by
        obtain ⟨k7, k8, k9, k10, k11, -⟩ := hA.shi
        exact ⟨hA.sp, hA.gp, k7, k8, k9, k10, k11, trivial⟩
      out := hA.out
      pw := hA.pw
      th := hA.th }
  obtain ⟨ksp, kgp, k7, k8, k9, k10, k11, -⟩ := h1.keep
  refine ⟨c1, hs1, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by rw [h1.mem]; rfl
      pc := by rw [h1.pc]; rfl
      minstret := h1.minstret
      sp := ksp
      gp := kgp
      shi := ⟨k7, k8, k9, k10, k11, trivial⟩
      out := h1.out
      pw := h1.pw
      th := h1.th }

/-- `df3c`: the first four spill readbacks (`s1/s2/s3/s6`), `a0 := 0`. -/
theorem sfvArmDf3c (g : SFVG) (hg : SFVGOk g) :
    Triple (SfvAtDf3c g) (SfvAtDf50 g) := by
  have T := segRowFramed sfvwrite_rXdf3cSeg (sfvwrite_rXdf3cL (sfvSpE g))
    [bytes8 g.sv.s1, bytes8 g.sv.s2, bytes8 g.sv.s3, bytes8 g.sv.s6]
    0x8000df3c#64 (sfvM3 g)
    ([(3, wrGpVal)] ++ sHiKeepL g.sv) (pushBytes g.out0 g.bytes) (0#4)
    (by show ChainOK 0x8000df3c#64 [2] sfvwrite_rXdf3cSeg; decide)
    (by show FrameOK [3, 23, 24, 25, 26, 27] sfvwrite_rXdf3cSeg; decide)
  intro c hA
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hA.good, hA.mem, hA.pc, hA.minstret, ⟨hA.sp, trivial⟩,
        by show KeysOK [2]; decide,
        by rw [hA.mem]; exact sfvDf3c_facts g hg (sfvM3_codeSf g hg), hA.tick⟩
      keep := by
        obtain ⟨k7, k8, k9, k10, k11, -⟩ := hA.shi
        exact ⟨hA.gp, k7, k8, k9, k10, k11, trivial⟩
      out := hA.out
      pw := hA.pw
      th := hA.th }
  obtain ⟨kgp, k7, k8, k9, k10, k11, -⟩ := h1.keep
  refine ⟨c1, hs1, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by rw [h1.mem, sfvDf3c_log_nil g, writeLog_nil]
      pc := by rw [h1.pc]; rfl
      minstret := h1.minstret
      a0 := by
        have h := gholds_lookup (n := 10)
          (v := (0#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) _ h1.regs (by rfl)
        rwa [addi0_env] at h
      sp := gholds_lookup (v := sfvSpE g) _ h1.regs (by rfl)
      gp := kgp
      s1 := by
        have h := gholds_lookup (n := 9)
          (v := bytesVal MKind.ld (bytes8 g.sv.s1)) _ h1.regs (by rfl)
        rwa [bytes8_val] at h
      s2 := by
        have h := gholds_lookup (n := 18)
          (v := bytesVal MKind.ld (bytes8 g.sv.s2)) _ h1.regs (by rfl)
        rwa [bytes8_val] at h
      s3 := by
        have h := gholds_lookup (n := 19)
          (v := bytesVal MKind.ld (bytes8 g.sv.s3)) _ h1.regs (by rfl)
        rwa [bytes8_val] at h
      s6 := by
        have h := gholds_lookup (n := 22)
          (v := bytesVal MKind.ld (bytes8 g.sv.s6)) _ h1.regs (by rfl)
        rwa [bytes8_val] at h
      shi := ⟨k7, k8, k9, k10, k11, trivial⟩
      out := h1.out
      pw := h1.pw
      th := h1.th }

/-- `df50`: the last four spill readbacks (`ra/s0/s4/s5`), frame pop, `ret` —
lands parked at `g.ra0` with the whole summary post. -/
theorem sfvArmDf50 (g : SFVG) (hg : SFVGOk g) :
    Triple (SfvAtDf50 g) (SfvFnPost g) := by
  have T := segRowFramed sfvwrite_rXdf50Seg (sfvwrite_rXdf50L (sfvSpE g))
    [bytes8 g.ra0, bytes8 g.s00, bytes8 g.sv.s4, bytes8 g.sv.s5]
    0x8000df50#64 (sfvM3 g)
    ([(3, wrGpVal), (10, (0#64 : BitVec 64)), (9, g.sv.s1), (18, g.sv.s2),
      (19, g.sv.s3), (22, g.sv.s6)] ++ sHiKeepL g.sv)
    (pushBytes g.out0 g.bytes) (0#4)
    (by show ChainOK 0x8000df50#64 [2] sfvwrite_rXdf50Seg; decide)
    (by show FrameOK [3, 10, 9, 18, 19, 22, 23, 24, 25, 26, 27] sfvwrite_rXdf50Seg
        decide)
  intro c hA
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hA.good, hA.mem, hA.pc, hA.minstret, ⟨hA.sp, trivial⟩,
        by show KeysOK [2]; decide,
        by rw [hA.mem]; exact sfvDf50_facts g hg (sfvM3_codeSf g hg), hA.tick⟩
      keep := by
        obtain ⟨k7, k8, k9, k10, k11, -⟩ := hA.shi
        exact ⟨hA.gp, hA.a0, hA.s1, hA.s2, hA.s3, hA.s6, k7, k8, k9, k10, k11,
          trivial⟩
      out := hA.out
      pw := hA.pw
      th := hA.th }
  obtain ⟨kgp, ka0, ks1, ks2, ks3, ks6, k7, k8, k9, k10, k11, -⟩ := h1.keep
  refine ⟨c1, hs1, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by rw [h1.mem, sfvDf50_log_nil g, writeLog_nil]
      pc := by
        rw [h1.pc]
        show some (BitVec.update (bytesVal MKind.ld (bytes8 g.ra0)
          + sign_extend (m := 64) (0x000#12)) 0 0#1) = some g.ra0
        rw [bytes8_val, hg.ra_fix]
      minstret := h1.minstret
      a0 := ka0
      ra := by
        have h := gholds_lookup (n := 1)
          (v := bytesVal MKind.ld (bytes8 g.ra0)) _ h1.regs (by rfl)
        rwa [bytes8_val] at h
      sp := by
        have h := gholds_lookup (n := 2)
          (v := sfvSpE g + sign_extend (m := 64) (0x060#12)) _ h1.regs (by rfl)
        rwa [sfv_sp_restore] at h
      gp := kgp
      s0 := by
        have h := gholds_lookup (n := 8)
          (v := bytesVal MKind.ld (bytes8 g.s00)) _ h1.regs (by rfl)
        rwa [bytes8_val] at h
      sregs := by
        refine ⟨ks1, ks2, ks3, ?_, ?_, ks6, k7, k8, k9, k10, k11, trivial⟩
        · have h := gholds_lookup (n := 20)
            (v := bytesVal MKind.ld (bytes8 g.sv.s4)) _ h1.regs (by rfl)
          rwa [bytes8_val] at h
        · have h := gholds_lookup (n := 21)
            (v := bytesVal MKind.ld (bytes8 g.sv.s5)) _ h1.regs (by rfl)
          rwa [bytes8_val] at h
      out := h1.out
      pw := h1.pw
      th := h1.th }

/-! ## The summary -/

/-- **The `__sfvwrite_r` UNBUFFERED-arm whole-function summary** (the io-DAG
crux): from the ABI entry with the real-stdout pin set (`__SWR ∧ __SNBF`,
non-null `_bf._base`, `fp->_write = __swrite`, `fp->_cookie = fp`) and a
single-iov uio (`uio_resid = iov_len = len ≠ 0`), `__sfvwrite_r` runs the
unbuffered route, calls `fp->_write` through the `jalr` seam — the landed
`swrite_summary` carries the whole `__swrite → _write_r → _write → HTIF`
chain — zeroes `uio_resid`, and returns to `ra0` with `a0 = 0`, callee-saved
registers restored, memory = `sfvM3`, console extended by EXACTLY the
buffer's byte string. -/
theorem sfvwrite_unbuf_summary (g : SFVG) :
    FnSummary 0x8000de8c#64 (SfvFnPre g) (SfvFnPost g) := by
  refine ⟨?_⟩
  intro c hc
  have hg := hc.2.ok
  exact Triple.seq (sfvArmDe8c g hg)
    (Triple.seq (sfvArmDe94 g hg)
    (Triple.seq (sfvArmDec0 g hg)
    (Triple.seq (sfvArmDec8 g hg)
    (Triple.seq (sfvArmDee4 g hg)
    (Triple.seq (sfvArmLoop1 g hg)
    (Triple.seq (sfvArmE0bc g hg)
    (Triple.seq (sfvArmLoop2 g hg)
    (Triple.seq (sfvArmDf00 g hg)
    (Triple.seq (sfvArmDf10 g hg)
    (Triple.seq (sfvArmJalr g hg)
    (Triple.seq (swrite_summary (sfvSWG g)).run
    (Triple.seq (sfvArmDf20 g hg)
    (Triple.seq (sfvArmDf24 g hg)
    (Triple.seq (sfvArmDf3c g hg)
      (sfvArmDf50 g hg))))))))))))))) c hc

#print axioms sfvwrite_unbuf_summary

end Vsa.Sim
