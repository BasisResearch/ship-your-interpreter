import Vsa.Sim.rows.FnSwrite
import Vsa.Sim.rows.FnWriteRFold
import Vsa.Sim.DecodeTable

/-!
# `__swrite` — the whole-function summary FOLD (gen_fn P3 pilot: the tail-`j` seam)

Folds the generated `__swrite` block arms (`rows/FnSwrite.lean`) into ONE
`FnSummary`: from the ABI entry `0x8000efd4` with `(a0,a1,a2,a3) =
(cookie, FILE*, buf, len)`, the append-mode-OFF (`bnez` FALL) route spills `ra`,
clears the flags bit `0x1000` (writing the halfword back at `fp+16`), loads the
`fd` halfword at `fp+18`, restores the argument registers and `sp`, and ends in
`j _write_r` — the **tail-jump seam**: `_write_r` returns FOR `__swrite`
(`ra` reloaded to the ORIGINAL `ra0` before the `j`), so its summary exit *is*
this function's exit and there is NO suffix (`tailJump_of_summary`,
`Vsa/Sim/FnSummary.lean`).

Architecture (the gen_fn tail-call template, hand-developed here; P2 =
`rows/FnWriteRFold.lean` is the model):

* ghosts bundled in `SWG`; static side conditions in `SWGOk` (named fields);
* both block write-logs are REIFIED (`swEntryLog` = the `sd ra` spill,
  `swTailLog` = the `sh` flags write-back) and the composed image `swM2` is the
  ghost memory handed to `_write_r`'s bundle;
* code/buffer pins are TRANSPORTED across the two stores (`swM2_getElem_lo` +
  the python-emitted per-byte `swriteLoaded_of_agree_lo`, plus P2's
  `writeLoaded_of_agree_lo`/`write_rLoaded_of_agree_lo` REUSED verbatim);
* every block runs via `segRowFramed` over the GENERATED segs;
* the epilogue-in-the-tail `ld ra,40(sp)` reads the spill back off `swM1`
  (`getElem_writeMap8_*` + `sext_reassemble` — P2's readback idiom);
* the tail `j` is spliced by `tailJump_of_summary` consuming
  `write_r_summary (swWRG g)` — the target's `WriteRFnPre` is marshalled as the
  tail arm's post, and `SwFnPost g` is BY DEFINITION `WriteRFnPost (swWRG g)`.

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

/-- The `__swrite` summary ghosts: entry ABI values (`a0 = cookie` — passed
through to `_write_r` untouched, `a1 = fp` the `FILE*`, `a2 = buf`,
`a3 = len`), the callee-saved entry values, the FILE flags/fd halfword bytes
(LE), the buffer bytes, the entry memory and console output. -/
structure SWG where
  cookie : BitVec 64
  fp : BitVec 64
  buf : BitVec 64
  len : BitVec 64
  ra0 : BitVec 64
  sp0 : BitVec 64
  s00 : BitVec 64
  /-- the callee-saved `s1..s11` entry values (preserved by the summary). -/
  sv : SRegs
  fl0 : BitVec 8
  fl1 : BitVec 8
  fd0 : BitVec 8
  fd1 : BitVec 8
  bytes : List (BitVec 8)
  m0 : Std.ExtHashMap Nat (BitVec 8)
  out0 : Array String

/-- The stack pointer inside `__swrite`'s frame (`sp0 - 48`, as the computed
`addi sp,sp,-48` expression so every seg readback is `rfl`-shaped). -/
def swSpE (g : SWG) : BitVec 64 := g.sp0 + sign_extend (m := 64) (0xfd0#12)

/-- The loaded FILE flags halfword (`lh a5,16(a1)`), sign-extended. -/
def swFlags (g : SWG) : BitVec 64 := bytesVal MKind.lh [g.fl0, g.fl1]

/-- The loaded fd halfword (`lh a1,18(a4)`) — `_write_r`'s `fd` argument. -/
def swFd (g : SWG) : BitVec 64 := bytesVal MKind.lh [g.fd0, g.fd1]

/-- The tail block's flags mask (`lui a3,0xfffff ; addi a3,a3,-1`
= `0xffffffffffffefff`, clearing bit 12), carried as the computed expression so
the seg's write-log readback is `rfl`-shaped (probe-verified). -/
def swMask : BitVec 64 :=
  sign_extend (m := 64) ((0xfffff#20 : BitVec 20) +++ (0x000#12))
    + sign_extend (m := 64) (0xfff#12)

/-- The flags halfword value written back by the tail `sh` (`and a5,a5,a3`). -/
def swClr (g : SWG) : BitVec 64 := swFlags g &&& swMask

/-- Static (config-independent) side conditions of the `__swrite` summary.  The
buffer/stack/errno fields mirror P2's `WRGOk` (they are marshalled INTO it at
the tail jump); the `fp` fields are what the FILE-struct halfword loads and the
flags write-back need. -/
structure SWGOk (g : SWG) : Prop where
  len_bytes : g.len.toNat = g.bytes.length
  nowrap : g.buf.toNat + g.bytes.length < 2 ^ 64
  lo : 0x80000000 ≤ g.buf.toNat
  hiram : g.buf.toNat + g.bytes.length ≤ 0x100000000
  htif : g.buf.toNat + g.bytes.length ≤ tohostAddr ∨ tohostAddr + 8 ≤ g.buf.toNat
  pins : ∀ i, (h : i < g.bytes.length) → g.m0[g.buf.toNat + i]? = some (g.bytes[i]'h)
  code : Vsa.Sim.Code._writeLoaded g.m0
  codeR : Vsa.Sim.Code._write_rLoaded g.m0
  codeS : Vsa.Sim.Code.__swriteLoaded g.m0
  ra_align : g.ra0.toNat % 4 = 0
  ra_fix : BitVec.update (g.ra0 + sign_extend (m := 64) (0x000#12)) 0 0#1 = g.ra0
  /-- `__swrite`'s frame `[sp0-48, sp0)` (ra spill at `sp0-8`) sits above the
  HTIF window — also gives `_write_r`'s `[sp0-16, sp0)` frame condition. -/
  sp_htif : tohostAddr + 16 ≤ g.sp0.toNat - 48
  /-- The frame sits above the `errno` word. -/
  sp_errno : wrErrnoAddr + 4 ≤ g.sp0.toNat - 48
  sp_hi : g.sp0.toNat ≤ 0x100000000
  sp_align : g.sp0.toNat % 8 = 0
  /-- The buffer window avoids the whole frame. -/
  buf_stack_disj : g.buf.toNat + g.bytes.length ≤ g.sp0.toNat - 48 ∨ g.sp0.toNat ≤ g.buf.toNat
  /-- The buffer window avoids the `errno` word. -/
  buf_errno_disj : g.buf.toNat + g.bytes.length ≤ wrErrnoAddr ∨ wrErrnoAddr + 4 ≤ g.buf.toNat
  /-- The FILE flags halfword bytes at `fp+16`/`fp+17` (LE). -/
  fl_pin0 : g.m0[g.fp.toNat + 16]? = some g.fl0
  fl_pin1 : g.m0[g.fp.toNat + 17]? = some g.fl1
  /-- The FILE fd halfword bytes at `fp+18`/`fp+19` (LE). -/
  fd_pin0 : g.m0[g.fp.toNat + 18]? = some g.fd0
  fd_pin1 : g.m0[g.fp.toNat + 19]? = some g.fd1
  /-- The flags/fd window `[fp+16, fp+20)` sits above the HTIF window (the
  `sh` write-back demands it; newlib's `__sf` FILE array lives in `.data`). -/
  fp_htif : tohostAddr + 16 ≤ g.fp.toNat + 16
  fp_hi : g.fp.toNat + 20 ≤ 0x100000000
  fp_align : g.fp.toNat % 2 = 0
  /-- The flags/fd window avoids the frame (the spill readback needs it). -/
  fp_stack_disj : g.fp.toNat + 20 ≤ g.sp0.toNat - 48 ∨ g.sp0.toNat ≤ g.fp.toNat
  /-- The buffer window avoids the flags/fd window (the `sh` write-back). -/
  buf_fp_disj : g.buf.toNat + g.bytes.length ≤ g.fp.toNat + 16 ∨ g.fp.toNat + 20 ≤ g.buf.toNat
  /-- Append mode OFF: bit 8 (`__SAPP`) of the flags halfword is clear — the
  entry `andi a3,a5,256 ; bnez a3` guard computes 0 and the branch FALLS
  (probe-verified guard shape; `decide`-dischargeable for concrete flags). -/
  append_off : swFlags g &&& sign_extend (m := 64) (0x100#12) = 0#64

/-! ## The two reified write-logs and their memory images -/

/-- The entry pin list (`swriteXefd4FL` at the ghosts). -/
def swEntryL (g : SWG) : GRegs :=
  swriteXefd4FL g.fp g.sp0 g.len g.ra0 g.buf g.cookie

/-- The entry block's ONE store (computed off `swriteXefd4FSeg`, verified by
`swEntryLog_eq`): `sd ra,40(sp')` — the spill at `sp0-8`. -/
def swEntryLog (g : SWG) : List WEntry :=
  [((swSpE g + sign_extend (m := 64) (0x028#12)).toNat, 8, g.ra0)]

theorem swEntryLog_eq (g : SWG) :
    (evalBlocks swriteXefd4FSeg (SegEvalState.init (swEntryL g) [[g.fl0, g.fl1]])).log
      = swEntryLog g := rfl

/-- The memory after `__swrite`'s entry block (the ra spill landed). -/
def swM1 (g : SWG) : Std.ExtHashMap Nat (BitVec 8) :=
  writeLog g.m0 (swEntryLog g)

/-- The 8 LE bytes the tail `ld ra,40(sp)` reads back — the `sd ra` store
image on `swM1`. -/
def swRaBytes (g : SWG) : List (BitVec 8) :=
  [(sdData_val g.ra0).extractLsb' 0 8, (sdData_val g.ra0).extractLsb' 8 8,
   (sdData_val g.ra0).extractLsb' 16 8, (sdData_val g.ra0).extractLsb' 24 8,
   (sdData_val g.ra0).extractLsb' 32 8, (sdData_val g.ra0).extractLsb' 40 8,
   (sdData_val g.ra0).extractLsb' 48 8, (sdData_val g.ra0).extractLsb' 56 8]

/-- The tail pin list (`swriteXeff8L` at the entry block's computed values). -/
def swTailL (g : SWG) : GRegs :=
  swriteXeff8L (swSpE g) (swFlags g) g.fp g.len g.buf g.cookie

/-- The tail block's two loads, in chain order: `ld ra,40(sp)` (the spill
readback) then `lh a1,18(a4)` (the fd halfword). -/
def swTailLds (g : SWG) : List (List (BitVec 8)) :=
  [swRaBytes g, [g.fd0, g.fd1]]

/-- The tail block's ONE store (verified by `swTailLog_eq`): `sh a5,16(a4)` —
the cleared flags halfword written back at `fp+16`. -/
def swTailLog (g : SWG) : List WEntry :=
  [((g.fp + sign_extend (m := 64) (0x010#12)).toNat, 2, swClr g)]

theorem swTailLog_eq (g : SWG) :
    (evalBlocks swriteXeff8Seg (SegEvalState.init (swTailL g) (swTailLds g))).log
      = swTailLog g := rfl

/-- The memory at the tail `j` — the summary's OWN footprint contribution
(`_write_r`'s summary adds its `wrM1` image on top of this). -/
def swM2 (g : SWG) : Std.ExtHashMap Nat (BitVec 8) :=
  writeLog (swM1 g) (swTailLog g)

/-! ## Frame-address arithmetic -/

theorem sw_spE_toNat (g : SWG) (hg : SWGOk g) :
    (swSpE g).toNat = g.sp0.toNat - 48 := by
  show (g.sp0 + sign_extend (m := 64) (0xfd0#12)).toNat = g.sp0.toNat - 48
  refine ptr_sub_toNat g.sp0 (0xfd0#12) 48 sext_fd0_toNat ?_
  have ht : tohostAddr = 0x8001ad00 := rfl
  have := hg.sp_htif
  omega

theorem sw_slot_ra_addr (g : SWG) (hg : SWGOk g) :
    (swSpE g + sign_extend (m := 64) (0x028#12)).toNat = g.sp0.toNat - 8 := by
  have hE := sw_spE_toNat g hg
  have ht : tohostAddr = 0x8001ad00 := rfl
  have h48 : 48 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
  rw [ptr_addoff (swSpE g) (0x028#12) 40 (by decide)
    (by rw [hE]; have := g.sp0.isLt; omega), hE]
  omega

theorem sw_flAddr (g : SWG) (hg : SWGOk g) :
    (g.fp + sign_extend (m := 64) (0x010#12)).toNat = g.fp.toNat + 16 :=
  ptr_addoff g.fp (0x010#12) 16 (by decide) (by have := hg.fp_hi; omega)

theorem sw_fdAddr (g : SWG) (hg : SWGOk g) :
    (g.fp + sign_extend (m := 64) (0x012#12)).toNat = g.fp.toNat + 18 :=
  ptr_addoff g.fp (0x012#12) 18 (by decide) (by have := hg.fp_hi; omega)

/-- `addi sp,sp,48` undoes the prologue's `addi sp,sp,-48`. -/
theorem sw_sp_restore (g : SWG) :
    swSpE g + sign_extend (m := 64) (0x030#12) = g.sp0 :=
  sp_dec48_restore g.sp0

/-- The reloaded `ra` is the spilled `ra0` (`sext_reassemble`). -/
theorem sw_raBytes_val (g : SWG) : bytesVal MKind.ld (swRaBytes g) = g.ra0 :=
  sext_reassemble g.ra0
    ((sdData_val g.ra0).extractLsb' 0 8) ((sdData_val g.ra0).extractLsb' 8 8)
    ((sdData_val g.ra0).extractLsb' 16 8) ((sdData_val g.ra0).extractLsb' 24 8)
    ((sdData_val g.ra0).extractLsb' 32 8) ((sdData_val g.ra0).extractLsb' 40 8)
    ((sdData_val g.ra0).extractLsb' 48 8) ((sdData_val g.ra0).extractLsb' 56 8)
    rfl rfl rfl rfl rfl rfl rfl rfl

/-! ## Transporting pins across the two stores -/

/-- Any byte outside the ra-spill slot survives the entry block's write-log. -/
theorem swM1_getElem_lo (g : SWG) (hg : SWGOk g) (k : Nat)
    (hstack : k < g.sp0.toNat - 8 ∨ g.sp0.toNat ≤ k) :
    (swM1 g)[k]? = g.m0[k]? := by
  have ht : tohostAddr = 0x8001ad00 := rfl
  have h48 : 48 ≤ g.sp0.toNat := by have := hg.sp_htif; omega
  show (writeMap8 g.m0 ((swSpE g + sign_extend (m := 64) (0x028#12)).toNat)
      (sdData_val g.ra0))[k]? = g.m0[k]?
  exact getElem_writeMap8_disjoint _ _ _ _ (by rw [sw_slot_ra_addr g hg]; omega)

/-- Any byte outside the ra-spill slot AND the flags halfword survives both
stores (the whole `__swrite` footprint). -/
theorem swM2_getElem_lo (g : SWG) (hg : SWGOk g) (k : Nat)
    (hstack : k < g.sp0.toNat - 8 ∨ g.sp0.toNat ≤ k)
    (hfp : k < g.fp.toNat + 16 ∨ g.fp.toNat + 18 ≤ k) :
    (swM2 g)[k]? = g.m0[k]? := by
  have hin : (swM2 g)[k]? = (swM1 g)[k]? := by
    show (((swM1 g).insert ((g.fp + sign_extend (m := 64) (0x010#12)).toNat)
        ((shData (swClr g)).extractLsb' 0 8)).insert
        ((g.fp + sign_extend (m := 64) (0x010#12)).toNat + 1)
        ((shData (swClr g)).extractLsb' 8 8))[k]? = (swM1 g)[k]?
    exact getElem_writeMap2_disjoint _ _ _ _ (by rw [sw_flAddr g hg]; omega)
  exact hin.trans (swM1_getElem_lo g hg k hstack)

/-- Everything below the HTIF window (all code) survives the entry store. -/
theorem swM1_agree_lo (g : SWG) (hg : SWGOk g) :
    ∀ j : Nat, j < tohostAddr → (swM1 g)[j]? = g.m0[j]? := by
  intro j hj
  have ht : tohostAddr = 0x8001ad00 := rfl
  refine swM1_getElem_lo g hg j ?_
  left; have := hg.sp_htif; omega

/-- Everything below the HTIF window (all code) survives both stores. -/
theorem swM2_agree_lo (g : SWG) (hg : SWGOk g) :
    ∀ j : Nat, j < tohostAddr → (swM2 g)[j]? = g.m0[j]? := by
  intro j hj
  have ht : tohostAddr = 0x8001ad00 := rfl
  refine swM2_getElem_lo g hg j ?_ ?_
  · left; have := hg.sp_htif; omega
  · left; have := hg.fp_htif; omega

/-- Transport `__swriteLoaded` across a memory that agrees below `tohostAddr`
(all `__swrite` code bytes sit below the HTIF window) — the P2
`write_rLoaded_of_agree_lo` idiom, emitted for the third module. -/
theorem swriteLoaded_of_agree_lo {m1 m0 : Std.ExtHashMap Nat (BitVec 8)}
    (hlo : ∀ j : Nat, j < tohostAddr → m1[j]? = m0[j]?)
    (h : Vsa.Sim.Code.__swriteLoaded m0) : Vsa.Sim.Code.__swriteLoaded m1 := by
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63⟩, ⟨h64, h65, h66, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82, h83, h84, h85, h86, h87, h88, h89, h90, h91, h92, h93, h94, h95, h96, h97, h98, h99, h100, h101, h102, h103, h104, h105, h106, h107, h108, h109, h110, h111, h112, h113, h114, h115, h116, h117, h118, h119, h120, h121, h122, h123, h124, h125, h126, h127⟩, ⟨h128, h129, h130, h131, h132, h133, h134, h135⟩⟩ := h
  exact ⟨⟨
    (hlo 0x8000efd4 (by decide)).trans h0,
    (hlo 0x8000efd5 (by decide)).trans h1,
    (hlo 0x8000efd6 (by decide)).trans h2,
    (hlo 0x8000efd7 (by decide)).trans h3,
    (hlo 0x8000efd8 (by decide)).trans h4,
    (hlo 0x8000efd9 (by decide)).trans h5,
    (hlo 0x8000efda (by decide)).trans h6,
    (hlo 0x8000efdb (by decide)).trans h7,
    (hlo 0x8000efdc (by decide)).trans h8,
    (hlo 0x8000efdd (by decide)).trans h9,
    (hlo 0x8000efde (by decide)).trans h10,
    (hlo 0x8000efdf (by decide)).trans h11,
    (hlo 0x8000efe0 (by decide)).trans h12,
    (hlo 0x8000efe1 (by decide)).trans h13,
    (hlo 0x8000efe2 (by decide)).trans h14,
    (hlo 0x8000efe3 (by decide)).trans h15,
    (hlo 0x8000efe4 (by decide)).trans h16,
    (hlo 0x8000efe5 (by decide)).trans h17,
    (hlo 0x8000efe6 (by decide)).trans h18,
    (hlo 0x8000efe7 (by decide)).trans h19,
    (hlo 0x8000efe8 (by decide)).trans h20,
    (hlo 0x8000efe9 (by decide)).trans h21,
    (hlo 0x8000efea (by decide)).trans h22,
    (hlo 0x8000efeb (by decide)).trans h23,
    (hlo 0x8000efec (by decide)).trans h24,
    (hlo 0x8000efed (by decide)).trans h25,
    (hlo 0x8000efee (by decide)).trans h26,
    (hlo 0x8000efef (by decide)).trans h27,
    (hlo 0x8000eff0 (by decide)).trans h28,
    (hlo 0x8000eff1 (by decide)).trans h29,
    (hlo 0x8000eff2 (by decide)).trans h30,
    (hlo 0x8000eff3 (by decide)).trans h31,
    (hlo 0x8000eff4 (by decide)).trans h32,
    (hlo 0x8000eff5 (by decide)).trans h33,
    (hlo 0x8000eff6 (by decide)).trans h34,
    (hlo 0x8000eff7 (by decide)).trans h35,
    (hlo 0x8000eff8 (by decide)).trans h36,
    (hlo 0x8000eff9 (by decide)).trans h37,
    (hlo 0x8000effa (by decide)).trans h38,
    (hlo 0x8000effb (by decide)).trans h39,
    (hlo 0x8000effc (by decide)).trans h40,
    (hlo 0x8000effd (by decide)).trans h41,
    (hlo 0x8000effe (by decide)).trans h42,
    (hlo 0x8000efff (by decide)).trans h43,
    (hlo 0x8000f000 (by decide)).trans h44,
    (hlo 0x8000f001 (by decide)).trans h45,
    (hlo 0x8000f002 (by decide)).trans h46,
    (hlo 0x8000f003 (by decide)).trans h47,
    (hlo 0x8000f004 (by decide)).trans h48,
    (hlo 0x8000f005 (by decide)).trans h49,
    (hlo 0x8000f006 (by decide)).trans h50,
    (hlo 0x8000f007 (by decide)).trans h51,
    (hlo 0x8000f008 (by decide)).trans h52,
    (hlo 0x8000f009 (by decide)).trans h53,
    (hlo 0x8000f00a (by decide)).trans h54,
    (hlo 0x8000f00b (by decide)).trans h55,
    (hlo 0x8000f00c (by decide)).trans h56,
    (hlo 0x8000f00d (by decide)).trans h57,
    (hlo 0x8000f00e (by decide)).trans h58,
    (hlo 0x8000f00f (by decide)).trans h59,
    (hlo 0x8000f010 (by decide)).trans h60,
    (hlo 0x8000f011 (by decide)).trans h61,
    (hlo 0x8000f012 (by decide)).trans h62,
    (hlo 0x8000f013 (by decide)).trans h63⟩,
   ⟨
    (hlo 0x8000f014 (by decide)).trans h64,
    (hlo 0x8000f015 (by decide)).trans h65,
    (hlo 0x8000f016 (by decide)).trans h66,
    (hlo 0x8000f017 (by decide)).trans h67,
    (hlo 0x8000f018 (by decide)).trans h68,
    (hlo 0x8000f019 (by decide)).trans h69,
    (hlo 0x8000f01a (by decide)).trans h70,
    (hlo 0x8000f01b (by decide)).trans h71,
    (hlo 0x8000f01c (by decide)).trans h72,
    (hlo 0x8000f01d (by decide)).trans h73,
    (hlo 0x8000f01e (by decide)).trans h74,
    (hlo 0x8000f01f (by decide)).trans h75,
    (hlo 0x8000f020 (by decide)).trans h76,
    (hlo 0x8000f021 (by decide)).trans h77,
    (hlo 0x8000f022 (by decide)).trans h78,
    (hlo 0x8000f023 (by decide)).trans h79,
    (hlo 0x8000f024 (by decide)).trans h80,
    (hlo 0x8000f025 (by decide)).trans h81,
    (hlo 0x8000f026 (by decide)).trans h82,
    (hlo 0x8000f027 (by decide)).trans h83,
    (hlo 0x8000f028 (by decide)).trans h84,
    (hlo 0x8000f029 (by decide)).trans h85,
    (hlo 0x8000f02a (by decide)).trans h86,
    (hlo 0x8000f02b (by decide)).trans h87,
    (hlo 0x8000f02c (by decide)).trans h88,
    (hlo 0x8000f02d (by decide)).trans h89,
    (hlo 0x8000f02e (by decide)).trans h90,
    (hlo 0x8000f02f (by decide)).trans h91,
    (hlo 0x8000f030 (by decide)).trans h92,
    (hlo 0x8000f031 (by decide)).trans h93,
    (hlo 0x8000f032 (by decide)).trans h94,
    (hlo 0x8000f033 (by decide)).trans h95,
    (hlo 0x8000f034 (by decide)).trans h96,
    (hlo 0x8000f035 (by decide)).trans h97,
    (hlo 0x8000f036 (by decide)).trans h98,
    (hlo 0x8000f037 (by decide)).trans h99,
    (hlo 0x8000f038 (by decide)).trans h100,
    (hlo 0x8000f039 (by decide)).trans h101,
    (hlo 0x8000f03a (by decide)).trans h102,
    (hlo 0x8000f03b (by decide)).trans h103,
    (hlo 0x8000f03c (by decide)).trans h104,
    (hlo 0x8000f03d (by decide)).trans h105,
    (hlo 0x8000f03e (by decide)).trans h106,
    (hlo 0x8000f03f (by decide)).trans h107,
    (hlo 0x8000f040 (by decide)).trans h108,
    (hlo 0x8000f041 (by decide)).trans h109,
    (hlo 0x8000f042 (by decide)).trans h110,
    (hlo 0x8000f043 (by decide)).trans h111,
    (hlo 0x8000f044 (by decide)).trans h112,
    (hlo 0x8000f045 (by decide)).trans h113,
    (hlo 0x8000f046 (by decide)).trans h114,
    (hlo 0x8000f047 (by decide)).trans h115,
    (hlo 0x8000f048 (by decide)).trans h116,
    (hlo 0x8000f049 (by decide)).trans h117,
    (hlo 0x8000f04a (by decide)).trans h118,
    (hlo 0x8000f04b (by decide)).trans h119,
    (hlo 0x8000f04c (by decide)).trans h120,
    (hlo 0x8000f04d (by decide)).trans h121,
    (hlo 0x8000f04e (by decide)).trans h122,
    (hlo 0x8000f04f (by decide)).trans h123,
    (hlo 0x8000f050 (by decide)).trans h124,
    (hlo 0x8000f051 (by decide)).trans h125,
    (hlo 0x8000f052 (by decide)).trans h126,
    (hlo 0x8000f053 (by decide)).trans h127⟩,
   ⟨
    (hlo 0x8000f054 (by decide)).trans h128,
    (hlo 0x8000f055 (by decide)).trans h129,
    (hlo 0x8000f056 (by decide)).trans h130,
    (hlo 0x8000f057 (by decide)).trans h131,
    (hlo 0x8000f058 (by decide)).trans h132,
    (hlo 0x8000f059 (by decide)).trans h133,
    (hlo 0x8000f05a (by decide)).trans h134,
    (hlo 0x8000f05b (by decide)).trans h135⟩⟩

theorem swM1_codeS (g : SWG) (hg : SWGOk g) : Vsa.Sim.Code.__swriteLoaded (swM1 g) :=
  swriteLoaded_of_agree_lo (swM1_agree_lo g hg) hg.codeS

theorem swM2_code (g : SWG) (hg : SWGOk g) : Vsa.Sim.Code._writeLoaded (swM2 g) :=
  writeLoaded_of_agree_lo (swM2_agree_lo g hg) hg.code

theorem swM2_codeR (g : SWG) (hg : SWGOk g) : Vsa.Sim.Code._write_rLoaded (swM2 g) :=
  write_rLoaded_of_agree_lo (swM2_agree_lo g hg) hg.codeR

/-- The buffer byte pins survive onto `swM2` (buffer disjoint from the spill
slot and the flags halfword). -/
theorem swM2_pins (g : SWG) (hg : SWGOk g) :
    ∀ i, (h : i < g.bytes.length) → (swM2 g)[g.buf.toNat + i]? = some (g.bytes[i]'h) := by
  intro i h
  refine (swM2_getElem_lo g hg (g.buf.toNat + i) ?_ ?_).trans (hg.pins i h)
  · rcases hg.buf_stack_disj with hd | hd
    · left; omega
    · right; omega
  · rcases hg.buf_fp_disj with hd | hd
    · left; omega
    · right; omega

/-- The tail `ld ra,40(sp)` byte pins on `swM1`: a direct hit on the `sd ra`
store image (`getElem_writeMap8_*`). -/
theorem swM1_ra_pins (g : SWG) :
    LPins8 (swM1 g) ((swSpE g + sign_extend (m := 64) (0x028#12)).toNat)
      (swRaBytes g) :=
  ⟨getElem_writeMap8_0 _ _ _, getElem_writeMap8_1 _ _ _,
   getElem_writeMap8_2 _ _ _, getElem_writeMap8_3 _ _ _,
   getElem_writeMap8_4 _ _ _, getElem_writeMap8_5 _ _ _,
   getElem_writeMap8_6 _ _ _, getElem_writeMap8_7 _ _ _⟩

/-- The fd halfword pins survive onto `swM1` (the FILE window avoids the
frame). -/
theorem swM1_fd_pin0 (g : SWG) (hg : SWGOk g) :
    (swM1 g)[(g.fp + sign_extend (m := 64) (0x012#12)).toNat]? = some g.fd0 := by
  have h := swM1_getElem_lo g hg ((g.fp + sign_extend (m := 64) (0x012#12)).toNat)
    (by rw [sw_fdAddr g hg]
        rcases hg.fp_stack_disj with hd | hd
        · left; omega
        · right; omega)
  rw [h, sw_fdAddr g hg]
  exact hg.fd_pin0

theorem swM1_fd_pin1 (g : SWG) (hg : SWGOk g) :
    (swM1 g)[(g.fp + sign_extend (m := 64) (0x012#12)).toNat + 1]? = some g.fd1 := by
  have h := swM1_getElem_lo g hg ((g.fp + sign_extend (m := 64) (0x012#12)).toNat + 1)
    (by rw [sw_fdAddr g hg]
        rcases hg.fp_stack_disj with hd | hd
        · left; omega
        · right; omega)
  rw [h, sw_fdAddr g hg,
    show g.fp.toNat + 18 + 1 = g.fp.toNat + 19 from by omega]
  exact hg.fd_pin1

/-! ## The P2 ghost bundle at the tail jump -/

/-- P2's `_write_r` ghost bundle as seen at the `j _write_r`: same `cookie`
(`a0` passed through), `fd` the loaded halfword, same `ra0` (reloaded off the
spill — `_write_r` returns FOR `__swrite`), same `sp0` (frame popped), memory
the two-store image `swM2`. -/
def swWRG (g : SWG) : WRG :=
  { reent := g.cookie, fd := swFd g, buf := g.buf, len := g.len,
    ra0 := g.ra0, sp0 := g.sp0, s00 := g.s00, sv := g.sv,
    bytes := g.bytes, m0 := swM2 g, out0 := g.out0 }

theorem swWRG_ok (g : SWG) (hg : SWGOk g) : WRGOk (swWRG g) :=
  { len_bytes := hg.len_bytes
    nowrap := hg.nowrap
    lo := hg.lo
    hiram := hg.hiram
    htif := hg.htif
    pins := swM2_pins g hg
    code := swM2_code g hg
    codeR := swM2_codeR g hg
    ra_align := hg.ra_align
    ra_fix := hg.ra_fix
    sp_htif := by
      show tohostAddr + 16 ≤ g.sp0.toNat - 16
      have := hg.sp_htif; omega
    sp_errno := by
      show wrErrnoAddr + 4 ≤ g.sp0.toNat - 16
      have := hg.sp_errno; omega
    sp_hi := hg.sp_hi
    sp_align := hg.sp_align
    buf_stack_disj := by
      show g.buf.toNat + g.bytes.length ≤ g.sp0.toNat - 16 ∨ g.sp0.toNat ≤ g.buf.toNat
      rcases hg.buf_stack_disj with hd | hd
      · left; omega
      · right; exact hd
    buf_errno_disj := hg.buf_errno_disj }

/-! ## Per-seg `ChainFacts` lemmas (ONE `chain_facts` each) -/

/-- Entry block (`lh` flags + `addi sp` + `sd ra` spill + `andi` + `mv`-shuffle
▷ `bnez` FALL): the flags-load window/pins, the spill window, and the
append-off guard. -/
theorem swEntry_facts (g : SWG) (hg : SWGOk g)
    (hcode : Vsa.Sim.Code.__swriteLoaded g.m0) :
    ChainFacts g.m0 g.m0 (swEntryL g) [[g.fl0, g.fl1]] swriteXefd4FSeg := by
  chain_facts hcode with "Vsa.Sim.Code.__swrite_at_"
  · -- lh a5,16(a1)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · show 0x80000000 ≤ (g.fp + sign_extend (m := 64) (0x010#12)).toNat
      rw [sw_flAddr g hg]
      have ht : tohostAddr = 0x8001ad00 := rfl
      have := hg.fp_htif
      omega
    · show (g.fp + sign_extend (m := 64) (0x010#12)).toNat + 2 ≤ 0x100000000
      rw [sw_flAddr g hg]
      have := hg.fp_hi
      omega
    · show (g.fp + sign_extend (m := 64) (0x010#12)).toNat + 2 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (g.fp + sign_extend (m := 64) (0x010#12)).toNat
      rw [sw_flAddr g hg]
      right
      have := hg.fp_htif
      omega
    · show (g.fp + sign_extend (m := 64) (0x010#12)).toNat % 2 = 0
      rw [sw_flAddr g hg]
      have := hg.fp_align
      omega
    · show g.m0[(g.fp + sign_extend (m := 64) (0x010#12)).toNat]? = some g.fl0
      rw [sw_flAddr g hg]
      exact hg.fl_pin0
    · show g.m0[(g.fp + sign_extend (m := 64) (0x010#12)).toNat + 1]? = some g.fl1
      rw [sw_flAddr g hg,
        show g.fp.toNat + 16 + 1 = g.fp.toNat + 17 from by omega]
      exact hg.fl_pin1
  · -- sd ra,40(sp)
    show 0x80000000 ≤ (swSpE g + sign_extend (m := 64) (0x028#12)).toNat ∧
      (swSpE g + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (swSpE g + sign_extend (m := 64) (0x028#12)).toNat ∧
      (swSpE g + sign_extend (m := 64) (0x028#12)).toNat % 8 = 0
    rw [sw_slot_ra_addr g hg]
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hg.sp_htif
    have := hg.sp_hi
    have := hg.sp_align
    refine ⟨by omega, by omega, by omega, by omega⟩
  · -- the bnez guard: append mode OFF (probe-verified reduced shape)
    show (bytesVal MKind.lh [g.fl0, g.fl1] &&& sign_extend (m := 64) (0x100#12)
      != 0#64) = false
    rw [show bytesVal MKind.lh [g.fl0, g.fl1] &&& sign_extend (m := 64) (0x100#12)
      = 0#64 from hg.append_off]
    decide

/-- Tail block (`lui/addi` mask + `ld ra` spill readback + `and` + `lh` fd +
`sh` flags write-back + `mv`-shuffle + `addi sp,sp,48` ▷ `j _write_r`): the
reload window/pins off the `swM1` store image, the fd-load window/pins, and
the write-back window. -/
theorem swTail_facts (g : SWG) (hg : SWGOk g)
    (hcodeS : Vsa.Sim.Code.__swriteLoaded (swM1 g)) :
    ChainFacts (swM1 g) (swM1 g) (swTailL g) (swTailLds g) swriteXeff8Seg := by
  chain_facts hcodeS with "Vsa.Sim.Code.__swrite_at_"
  · -- ld ra,40(sp)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show 0x80000000 ≤ (swSpE g + sign_extend (m := 64) (0x028#12)).toNat
      rw [sw_slot_ra_addr g hg]
      have ht : tohostAddr = 0x8001ad00 := rfl
      have := hg.sp_htif
      omega
    · show (swSpE g + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ 0x100000000
      rw [sw_slot_ra_addr g hg]
      have h48 : 48 ≤ g.sp0.toNat := by
        have ht : tohostAddr = 0x8001ad00 := rfl
        have := hg.sp_htif
        omega
      have := hg.sp_hi
      omega
    · show (swSpE g + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (swSpE g + sign_extend (m := 64) (0x028#12)).toNat
      rw [sw_slot_ra_addr g hg]
      right
      have := hg.sp_htif
      omega
    · show (swSpE g + sign_extend (m := 64) (0x028#12)).toNat % 8 = 0
      rw [sw_slot_ra_addr g hg]
      have ht : tohostAddr = 0x8001ad00 := rfl
      have := hg.sp_htif
      have := hg.sp_align
      omega
    · exact swM1_ra_pins g
  · -- lh a1,18(a4)
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · show 0x80000000 ≤ (g.fp + sign_extend (m := 64) (0x012#12)).toNat
      rw [sw_fdAddr g hg]
      have ht : tohostAddr = 0x8001ad00 := rfl
      have := hg.fp_htif
      omega
    · show (g.fp + sign_extend (m := 64) (0x012#12)).toNat + 2 ≤ 0x100000000
      rw [sw_fdAddr g hg]
      have := hg.fp_hi
      omega
    · show (g.fp + sign_extend (m := 64) (0x012#12)).toNat + 2 ≤ tohostAddr
        ∨ tohostAddr + 8 ≤ (g.fp + sign_extend (m := 64) (0x012#12)).toNat
      rw [sw_fdAddr g hg]
      right
      have := hg.fp_htif
      omega
    · show (g.fp + sign_extend (m := 64) (0x012#12)).toNat % 2 = 0
      rw [sw_fdAddr g hg]
      have := hg.fp_align
      omega
    · exact swM1_fd_pin0 g hg
    · exact swM1_fd_pin1 g hg
  · -- sh a5,16(a4)
    show 0x80000000 ≤ (g.fp + sign_extend (m := 64) (0x010#12)).toNat ∧
      (g.fp + sign_extend (m := 64) (0x010#12)).toNat + 2 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (g.fp + sign_extend (m := 64) (0x010#12)).toNat ∧
      (g.fp + sign_extend (m := 64) (0x010#12)).toNat % 2 = 0
    rw [sw_flAddr g hg]
    have ht : tohostAddr = 0x8001ad00 := rfl
    have := hg.fp_htif
    have := hg.fp_hi
    have := hg.fp_align
    refine ⟨by omega, by omega, by omega, by omega⟩

/-! ## Join-point predicate -/

/-- Parked at the tail block (`0x8000eff8`), entry block done: the flags
halfword loaded into `a5`, the arguments parked in `a4/t1/a7/a6`, the ra spill
landed (`mem = swM1`). -/
structure SwAtTail (g : SWG) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = swM1 g
  pc : c.σ.regs.get? Register.PC = some 0x8000eff8#64
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a5 : gprGet c.σ 15 = some (swFlags g)
  a4 : gprGet c.σ 14 = some g.fp
  t1 : gprGet c.σ 6 = some g.len
  a7 : gprGet c.σ 17 = some g.buf
  a6 : gprGet c.σ 16 = some g.cookie
  sp : gprGet c.σ 2 = some (swSpE g)
  gp : gprGet c.σ 3 = some wrGpVal
  s0 : gprGet c.σ 8 = some g.s00
  sregs : GHolds c.σ (sKeepL g.sv)
  out : c.σ.sailOutput = g.out0
  pw : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v

/-! ## The summary pre/post -/

/-- `__swrite`'s summary precondition (at the ABI entry `0x8000efd4`):
`(a0,a1,a2,a3) = (cookie, fp, buf, len)`, `gp` the linked binary's global
pointer, buffer/stack/FILE-window side conditions in `ok`. -/
structure SwFnPre (g : SWG) (c : Config) : Prop where
  ok : SWGOk g
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = g.m0
  minstret : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  a0 : gprGet c.σ 10 = some g.cookie
  a1 : gprGet c.σ 11 = some g.fp
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

/-- `__swrite`'s summary post IS `_write_r`'s summary post at the tail-jump
ghost bundle — the tail target returns FOR the caller, so its exit condition
(returned to `g.ra0` with `a0 = len`, callee-saved registers restored, memory
= `wrM1 (swWRG g)` — `_write_r`'s spill/errno image over `__swrite`'s own
two-store image `swM2` — console extended by EXACTLY the byte string) is the
whole function's exit.  No re-expression: the tail-`j` seam has NO suffix. -/
def SwFnPost (g : SWG) : Config → Prop := WriteRFnPost (swWRG g)

/-! ## Arm Triples -/

/-- Entry block: `0x8000efd4 → 0x8000eff8` (the `bnez` FALL — append off). -/
theorem swEntryArm (g : SWG) (hg : SWGOk g) :
    Triple (fun c => PCAt 0x8000efd4#64 c ∧ SwFnPre g c) (SwAtTail g) := by
  have T := segRowFramed swriteXefd4FSeg (swEntryL g) [[g.fl0, g.fl1]]
    0x8000efd4#64 g.m0 ([(3, wrGpVal), (8, g.s00)] ++ sKeepL g.sv) g.out0 (0#4)
    (by show ChainOK 0x8000efd4#64 [11, 2, 13, 1, 12, 10] swriteXefd4FSeg; decide)
    (by show FrameOK [3, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
          swriteXefd4FSeg
        decide)
  intro c hc
  obtain ⟨hpc, hp⟩ := hc
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hp.good, hp.mem, hpc, hp.minstret,
        ⟨hp.a1, hp.sp, hp.a3, hp.ra, hp.a2, hp.a0, trivial⟩,
        by show KeysOK [11, 2, 13, 1, 12, 10]; decide,
        by rw [hp.mem]; exact swEntry_facts g hg hg.codeS, hp.tick⟩
      keep := ⟨hp.gp, hp.s0, hp.sregs⟩
      out := hp.out
      pw := hp.pw
      th := hp.th }
  obtain ⟨hkgp, hks0, hsk⟩ := h1.keep
  refine ⟨c1, hs1, ?_⟩
  exact
    { good := h1.good
      tick := h1.tick
      mem := by rw [h1.mem]; rfl
      pc := by rw [h1.pc]; rfl
      minstret := h1.minstret
      a5 := gholds_lookup (v := swFlags g) _ h1.regs (by rfl)
      a4 := by
        have h := gholds_lookup (n := 14)
          (v := g.fp + sign_extend (m := 64) (0x000#12)) _ h1.regs (by rfl)
        rwa [addi0_env] at h
      t1 := by
        have h := gholds_lookup (n := 6)
          (v := g.len + sign_extend (m := 64) (0x000#12)) _ h1.regs (by rfl)
        rwa [addi0_env] at h
      a7 := by
        have h := gholds_lookup (n := 17)
          (v := g.buf + sign_extend (m := 64) (0x000#12)) _ h1.regs (by rfl)
        rwa [addi0_env] at h
      a6 := by
        have h := gholds_lookup (n := 16)
          (v := g.cookie + sign_extend (m := 64) (0x000#12)) _ h1.regs (by rfl)
        rwa [addi0_env] at h
      sp := gholds_lookup (v := swSpE g) _ h1.regs (by rfl)
      gp := hkgp
      s0 := hks0
      sregs := hsk
      out := h1.out
      pw := h1.pw
      th := h1.th }

/-- Tail block through the `j _write_r`: lands parked at `_write_r`'s ABI
entry with its whole summary precondition marshalled (`ra` reloaded to `ra0`
off the spill image, `sp` restored, `fd` loaded, flags written back —
`mem = swM2`). -/
theorem swTailArm (g : SWG) (hg : SWGOk g) :
    Triple (SwAtTail g)
      (fun c => PCAt 0x800104fc#64 c ∧ WriteRFnPre (swWRG g) c) := by
  have T := segRowFramed swriteXeff8Seg (swTailL g) (swTailLds g)
    0x8000eff8#64 (swM1 g) ([(3, wrGpVal), (8, g.s00)] ++ sKeepL g.sv) g.out0 (0#4)
    (by show ChainOK 0x8000eff8#64 [2, 15, 14, 6, 17, 16] swriteXeff8Seg; decide)
    (by show FrameOK [3, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
          swriteXeff8Seg
        decide)
  intro c hA
  obtain ⟨c1, hs1, h1⟩ := T c
    { seg := ⟨hA.good, hA.mem, hA.pc, hA.minstret,
        ⟨hA.sp, hA.a5, hA.a4, hA.t1, hA.a7, hA.a6, trivial⟩,
        by show KeysOK [2, 15, 14, 6, 17, 16]; decide,
        by rw [hA.mem]; exact swTail_facts g hg (swM1_codeS g hg), hA.tick⟩
      keep := ⟨hA.gp, hA.s0, hA.sregs⟩
      out := hA.out
      pw := hA.pw
      th := hA.th }
  obtain ⟨hkgp, hks0, hsk⟩ := h1.keep
  refine ⟨c1, hs1, ?_, ?_⟩
  · show c1.σ.regs.get? Register.PC = some 0x800104fc#64
    rw [h1.pc]
    rfl
  · exact
      { ok := swWRG_ok g hg
        good := h1.good
        tick := h1.tick
        mem := by rw [h1.mem]; rfl
        minstret := h1.minstret
        a0 := by
          have h := gholds_lookup (n := 10)
            (v := g.cookie + sign_extend (m := 64) (0x000#12)) _ h1.regs (by rfl)
          rwa [addi0_env] at h
        a1 := gholds_lookup (v := swFd g) _ h1.regs (by rfl)
        a2 := by
          have h := gholds_lookup (n := 12)
            (v := g.buf + sign_extend (m := 64) (0x000#12)) _ h1.regs (by rfl)
          rwa [addi0_env] at h
        a3 := by
          have h := gholds_lookup (n := 13)
            (v := g.len + sign_extend (m := 64) (0x000#12)) _ h1.regs (by rfl)
          rwa [addi0_env] at h
        ra := by
          have h := gholds_lookup (n := 1)
            (v := bytesVal MKind.ld (swRaBytes g)) _ h1.regs (by rfl)
          rwa [sw_raBytes_val g] at h
        sp := by
          have h := gholds_lookup (n := 2)
            (v := swSpE g + sign_extend (m := 64) (0x030#12)) _ h1.regs (by rfl)
          rwa [sw_sp_restore g] at h
        gp := hkgp
        s0 := hks0
        sregs := hsk
        out := h1.out
        pw := h1.pw
        th := h1.th }

/-! ## The summary -/

/-- **The `__swrite` whole-function summary** (gen_fn pilot P3 — the FINAL
pilot: the tail-`j` seam).  From the ABI entry with append mode off and the
buffer pinned, `__swrite` clears the flags bit, writes the halfword back, and
tail-jumps into `_write_r`, which returns FOR it: to `g.ra0` with `a0 = len`,
callee-saved registers restored, and the console output extended by EXACTLY
the buffer's byte string — `tailJump_of_summary` around `write_r_summary`,
NO suffix. -/
theorem swrite_summary (g : SWG) :
    FnSummary 0x8000efd4#64 (SwFnPre g) (SwFnPost g) := by
  refine ⟨?_⟩
  intro c hc
  have hg := hc.2.ok
  exact tailJump_of_summary
    (Triple.seq (swEntryArm g hg) (swTailArm g hg))
    (write_r_summary (swWRG g)) (fun _ h => h) c hc

#print axioms swrite_summary

end Vsa.Sim
