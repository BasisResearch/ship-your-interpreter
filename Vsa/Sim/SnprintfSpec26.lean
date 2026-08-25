import Vsa.Sim.SnprintfSpec17
import Vsa.Sim.SnprintfSpec25

/-!
# M3 Layer-3 — `SnprintfSpec26` : PRINT/iov call setup ≫ flush ≫ svfprintf return
## `0x800078ac` (second-iovec entry) → svfprintf's `ret`, `a0 = total`

The glue that chains the verified PRINT/iov call setup into the verified
flush + return path:

    iov2ToSsprintCall_spec   (SnprintfSpec17: 0x800078ac → the jal completed,
                              PC = 0x8000e908, ra = 0x80008688)
      ≫ svfprintf_flushReturn_spec
                             (SnprintfSpec25: the __ssprint_r 2-iovec flush,
                              post-call cleanup, parse-loop NUL exit, epilogue,
                              PC = vra0 with a0 = the total)

`PreSr` (SnprintfSpec20) at the call is discharged from Spec17's postcondition
`writeMap` chain (the five writes: resid `sp+240 := n1+n2`, `iov[1].base
:= vbase` at `sp+368`, `iov[1].len := n2` at `sp+376`, count `sp+232 := 2`,
total `sp+16`) plus caller hypotheses transported across the writes through the
single pointwise agreement `hagree` (everything outside the five windows is
unchanged).

## Residual-hypothesis provenance

Every hypothesis below is established upstream on the real `%lld` run:

* register values at `0x800078ac` (`hx2 … hx28`) and the branch guards
  (`hvt0`, `hsubwle`, `hb256`, `hb4`) — the exit state of
  `printEntryToSignIov_spec` (SnprintfSpec11) / the parse-loop segments
  (Spec7–16); Spec11's post must still be strengthened to *export* them
  (its own composition note), so they are stated here;
* `hcnt0 … hcnt3` (count word = 1 at `sp+232`) — Spec11's `sw` (count 0 → 1
  over the prologue's `sw zero,232(sp)`);
* `hvcurF` (`a2 = cursor = n1`) — the prologue's `sd zero,240(sp)` plus
  Spec11's cursor bump (`0 → 1 = n1`); `hvnd6` (`s6` = digit count `n2`) —
  the digit-loop exit (Spec7's restore, `s6 = len`);
* `htotS`/`hstrS`/`hfmtS`/`hs020S` (total / sink-struct ptr / fmt cursor /
  parse slot at `sp+16/8/0/32`) — svfprintf prologue (`sd a1,8(sp)`) and
  parse loop; `hnulB` — the fmt NUL that ended the parse loop;
* `hviovS` + `hviovBN` (`mem[sp+224] = viovB = sp+352`) — the prologue's
  `addi s5,sp,352` / `sd s5,224(sp)` (uio.uio_iov := iov array);
  `hviov2N` (`s7 = sp+368`) — Spec11's `addi s7,s7,16`;
* `hiov0b`/`hiov0l`/`hsignB` (sign iovec `(sp+167, 1)` + the `'-'` byte) —
  Spec11's two `sd`s and the sign block (Spec4/6: the byte at `sp+167`
  survives to the PRINT segment);
* `hdigB` + `hvb1`/`hvb2` (digit bytes at `vbase`, inside the `BufInv` window
  `[vsp+328, vsp+348)` — the buffer top is `entryTop vsp = vsp+348` and at most
  20 digits are emitted, so `vbase = vsp+348−n2 ≥ vsp+328`) — the digit loop
  (Spec3/5) leaves the digits in svfprintf's stack buffer, `s10 = vbase`
  (Spec7's restore; see Spec37's `PreSr` instantiation for the exact base);
* `hsinkcur`/`hsinkcap`/`hfl0B`/`hfl1B`/`hflag`/`hcaplt`/`hcap31` — the FILE
  sink struct built by the `snprintf`/`_svsnprintf_r` wrapper (cursor `d`,
  capacity `cap32`, `_flags` bit 6 clear) — NOT yet verified (NEXT);
* the 15 spill slots `hsv1e8 … hsv248` — svfprintf's prologue `sd`s at
  `sp+488 … sp+584` (visible at `0x80007658 … 0x800076dc`), untouched since;
* `hfnslot`/`hmbB` — static locale data (`__global_locale.mbtowc =
  __ascii_mbtowc` at `0x8001b880`, `__mb_cur_max = 1` at `0x8001b8f8`),
  written once at startup — NOT yet verified (NEXT);
* `hmidregs` — the five register facts `iov2ToSsprintCall_spec`'s post omits
  (`gp = 0x8001b510`, `s1 = &__global_locale = 0x8001b798`, and x18/x19/x21
  defined): none of the 28 instructions `0x800078ac → 0x8000e908` writes
  x3/x9/x18/x19/x21, but Spec17 states no register frame, so (as with
  `env_get_found_spec`'s `hreach` residual) the preserved values are taken as
  a mid-state hypothesis, dischargeable mechanically once Spec17's post is
  strengthened with the obs-extraction additions its composition note already
  plans.  `gp` is set by crt0 and never rewritten; `s1` holds the current
  locale pointer loaded in svfprintf's prologue — NEXT;
* the layout block (`hsplo … hra0align`) — address facts of the concrete
  image (stack above `0x8001c000`, sink/dest above the static data, fmt
  cursor outside the touched windows).

The postcondition is `svfprintf_flushReturn_spec`'s, re-based to the memory at
`0x800078ac`: digits+sign flushed to `[d, d+n1+n2)`, sink cursor/capacity
updated, uio resid/count cleared, the wide-char out-slot zeroed, the running
total at `sp+16` (also returned in `a0`), and a pointwise frame outside nine
windows (Spec25's seven, plus the total slot `[sp+16, sp+24)` and the second
iovec entry `[sp+368, sp+384)`). -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded FlushPinsLoaded MemmoveLoaded __ssprint_rLoaded
  __locale_mb_cur_maxLoaded __ascii_mbtowcLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- A `SlotHolds` *is* the `Pin8` at the slot's effective address (converse of
`slotHolds_of_pin8_rt`). -/
theorem pin8_of_slotHolds_i26 (base : BitVec 64) (off : Nat) (v : BitVec 64) (A : Nat)
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (hA : (base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat = A)
    (h : SlotHolds base off v mem) : Pin8 mem A v := by
  unfold SlotHolds at h
  rw [hA] at h
  exact h

/-- **PRINT/iov call setup ≫ 2-iovec flush ≫ svfprintf return, end to end.**

From `0x800078ac` (the state `printEntryToSignIov_spec` reaches: first iovec
built, count = 1, cursor = `n1`) through the second-iovec/call-setup segment
(`iov2ToSsprintCall_spec`), the whole `__ssprint_r` 2-iovec flush, the
post-call cleanup, the parse-loop NUL exit and svfprintf's epilogue
(`svfprintf_flushReturn_spec`), to `PC = vra0` with **`a0 = vtotF`** — the
total svfprintf returns.  See the module docstring for the provenance of every
hypothesis. -/
theorem iov2ToSvfprintfRet_spec
    (vsp vt0 vt1 v8 vcurF vlen vs4 vnd6 viov2 viovB vbase vt3 p d : BitVec 64)
    (vtot vtotF vfmt vra0 : BitVec 64)
    (vS0o vS1o vS2 vS3 vS4 vS5 vS6o vS7 vS8 vS9 vS10 vS11 : BitVec 64)
    (fl0 fl1 : BitVec 8) (n1 n2 : Nat) (cap32 : BitVec 32)
    (bs1 bs2 : Nat → BitVec 8) (c : Config)
    -- machine state at 0x800078ac
    (hGood : GoodState c.σ)
    (hpc : c.σ.regs.get? Register.PC = some (0x800078ac#64))
    (htick : c.tick < 2)
    -- code / static-code pins at 0x800078ac
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hfp : FlushPinsLoaded c.σ.mem)
    (hsspL : __ssprint_rLoaded c.σ.mem)
    (hsspuL : Vsa.Sim.Code.__ssputs_rLoaded c.σ.mem)
    (hmvL : MemmoveLoaded c.σ.mem)
    (hlocC : __locale_mb_cur_maxLoaded c.σ.mem)
    (hambC : __ascii_mbtowcLoaded c.σ.mem)
    -- registers at 0x800078ac  [Spec11 exit state]
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx5 : c.σ.regs.get? Register.x5 = some vt0)
    (hx6 : c.σ.regs.get? Register.x6 = some vt1)
    (hx8 : c.σ.regs.get? Register.x8 = some v8)
    (hx12 : c.σ.regs.get? Register.x12 = some vcurF)
    (hx16 : c.σ.regs.get? Register.x16 = some vlen)
    (hx20 : c.σ.regs.get? Register.x20 = some vs4)
    (hx22 : c.σ.regs.get? Register.x22 = some vnd6)
    (hx23 : c.σ.regs.get? Register.x23 = some viov2)
    (hx26 : c.σ.regs.get? Register.x26 = some vbase)
    (hx28 : c.σ.regs.get? Register.x28 = some vt3)
    -- ghost links (iov geometry, lengths, the selected total)
    (hvt0 : vt0 = 0#64)
    (hvcurF : vcurF = BitVec.ofNat 64 n1)
    (hvnd6 : vnd6 = BitVec.ofNat 64 n2)
    (hn1a : 1 ≤ n1) (hn1b : n1 ≤ 31) (hn2a : 1 ≤ n2) (hn2b : n2 ≤ 31)
    (hviovBN : viovB.toNat = vsp.toNat + 352)
    (hviov2N : viov2.toNat = vsp.toNat + 368)
    (hvtotF : vtotF = sign_extend (m := 64)
      (Sail.BitVec.extractLsb (if zopz0zKzJ_s vt3 vlen = true then vt3 else vlen) 31 0
        + Sail.BitVec.extractLsb vtot 31 0))
    -- parse-state branch guards (verbatim Spec17 residuals)
    (hsubwle : zopz0zI_s (0#64)
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) = false)
    (hb256 : ((vt1 &&& sign_extend (m := 64) (0x100#12)) != (0#64)) = false)
    (hb4 : ((vt1 &&& sign_extend (m := 64) (0x004#12)) == (0#64)) = true)
    -- the iov count word at sp+232 (= 1, after the sign iovec)
    (hcnt0 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat]?
      = some ((1#32 : BitVec 32).extractLsb' 0 8))
    (hcnt1 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 1]?
      = some ((1#32 : BitVec 32).extractLsb' 8 8))
    (hcnt2b : c.σ.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 2]?
      = some ((1#32 : BitVec 32).extractLsb' 16 8))
    (hcnt3 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0e8#12)).toNat + 3]?
      = some ((1#32 : BitVec 32).extractLsb' 24 8))
    -- caller stack slots at 0x800078ac (parse state + uio + prologue spills)
    (htotS : SlotHolds vsp 0x010 vtot c.σ.mem)
    (hstrS : SlotHolds vsp 0x008 p c.σ.mem)
    (hfmtS : SlotHolds vsp 0x000 vfmt c.σ.mem)
    (hs020S : SlotHolds vsp 0x020 (0#64) c.σ.mem)
    (hviovS : SlotHolds vsp 0x0e0 viovB c.σ.mem)
    (hsv1e8 : SlotHolds vsp 0x1e8 vS11 c.σ.mem)
    (hsv1f0 : SlotHolds vsp 0x1f0 vS10 c.σ.mem)
    (hsv1f8 : SlotHolds vsp 0x1f8 vS9 c.σ.mem)
    (hsv200 : SlotHolds vsp 0x200 vS8 c.σ.mem)
    (hsv208 : SlotHolds vsp 0x208 vS7 c.σ.mem)
    (hsv210 : SlotHolds vsp 0x210 vS6o c.σ.mem)
    (hsv218 : SlotHolds vsp 0x218 vS5 c.σ.mem)
    (hsv220 : SlotHolds vsp 0x220 vS4 c.σ.mem)
    (hsv228 : SlotHolds vsp 0x228 vS3 c.σ.mem)
    (hsv230 : SlotHolds vsp 0x230 vS2 c.σ.mem)
    (hsv238 : SlotHolds vsp 0x238 vS1o c.σ.mem)
    (hsv240 : SlotHolds vsp 0x240 vS0o c.σ.mem)
    (hsv248 : SlotHolds vsp 0x248 vra0 c.σ.mem)
    -- the first (sign) iovec and its bytes, the digit bytes
    (hiov0b : Pin8 c.σ.mem viovB.toNat (vsp + sign_extend (m := 64) (0x0a7#12)))
    (hiov0l : Pin8 c.σ.mem (viovB.toNat + 8) (BitVec.ofNat 64 n1))
    (hsignB : MvBytes c.σ.mem (vsp + sign_extend (m := 64) (0x0a7#12)) n1 bs1)
    (hdigB : MvBytes c.σ.mem vbase n2 bs2)
    -- the FILE sink struct (cursor, capacity, flags) and the fmt NUL
    (hsinkcur : Pin8 c.σ.mem p.toNat d)
    (hsinkcap : Pin4 c.σ.mem (p.toNat + 12) cap32)
    (hcaplt : n1 + n2 < cap32.toNat)
    (hcap31 : cap32.toNat < 2 ^ 31)
    (hnulB : c.σ.mem[vfmt.toNat]? = some (0x00#8))
    (hfl0B : c.σ.mem[p.toNat + 16]? = some fl0)
    (hfl1B : c.σ.mem[p.toNat + 17]? = some fl1)
    (hflag : ((zero_extend (m := 64) ((fl1.append fl0) : BitVec (8 * 2)) : BitVec 64)
      &&& sign_extend (m := 64) (0x040#12)) = 0#64)
    -- static locale data
    (hfnslot : SlotHolds (0x8001b798#64) 0x0e8 (0x80012268#64) c.σ.mem)
    (hmbB : c.σ.mem[(0x8001b8f8 : Nat)]? = some (0x01#8))
    -- the five register facts Spec17's post omits (preserved by the segment,
    -- to be discharged when its post is strengthened; see the docstring)
    (hmidregs : ∀ cm : Config, Steps c cm →
      cm.σ.regs.get? Register.PC = some (0x8000e908#64) →
      cm.σ.regs.get? Register.x3 = some (0x8001b510#64) ∧
      cm.σ.regs.get? Register.x9 = some (0x8001b798#64) ∧
      (∃ w, cm.σ.regs.get? Register.x18 = some w) ∧
      (∃ w, cm.σ.regs.get? Register.x19 = some w) ∧
      (∃ w, cm.σ.regs.get? Register.x21 = some w))
    -- layout
    (hsplo : 0x8001c000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (hdge : 0x8001b900 ≤ d.toNat)
    (hdhi : d.toNat + n1 + n2 ≤ 0x100000000)
    (hdstk : vsp.toNat + 592 ≤ d.toNat ∨ d.toNat + n1 + n2 ≤ vsp.toNat - 128)
    (hpge : 0x8001b900 ≤ p.toNat)
    (hp18hi : p.toNat + 18 ≤ 0x100000000)
    (hpal : p.toNat % 8 = 0)
    (hpstk : vsp.toNat + 592 ≤ p.toNat ∨ p.toNat + 18 ≤ vsp.toNat - 128)
    (hpd18 : p.toNat + 18 ≤ d.toNat ∨ d.toNat + n1 + n2 ≤ p.toNat)
    (hvb1 : vsp.toNat + 328 ≤ vbase.toNat)
    (hvb2 : vbase.toNat + n2 ≤ vsp.toNat + 348)
    (hfd : vfmt.toNat + 1 ≤ d.toNat ∨ d.toNat + n1 + n2 ≤ vfmt.toNat)
    (hfpp : vfmt.toNat + 1 ≤ p.toNat ∨ p.toNat + 16 ≤ vfmt.toNat)
    (hfstk : vfmt.toNat + 1 ≤ vsp.toNat - 128 ∨ vsp.toNat + 592 ≤ vfmt.toNat)
    (hflo : 0x80000000 ≤ vfmt.toNat)
    (hfhi : vfmt.toNat + 1 ≤ 0x100000000)
    (hfhtif : vfmt.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vfmt.toNat)
    (hra0align : vra0.toNat % 4 = 0) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some vra0 ∧
      c'.σ.regs.get? Register.x1 = some vra0 ∧
      c'.σ.regs.get? Register.x2 = some (vsp + (592#64)) ∧
      c'.σ.regs.get? Register.x10 = some vtotF ∧
      c'.σ.regs.get? Register.x8 = some vS0o ∧
      c'.σ.regs.get? Register.x9 = some vS1o ∧
      c'.σ.regs.get? Register.x18 = some vS2 ∧
      c'.σ.regs.get? Register.x19 = some vS3 ∧
      c'.σ.regs.get? Register.x20 = some vS4 ∧
      c'.σ.regs.get? Register.x21 = some vS5 ∧
      c'.σ.regs.get? Register.x22 = some vS6o ∧
      c'.σ.regs.get? Register.x23 = some vS7 ∧
      c'.σ.regs.get? Register.x24 = some vS8 ∧
      c'.σ.regs.get? Register.x25 = some vS9 ∧
      c'.σ.regs.get? Register.x26 = some vS10 ∧
      c'.σ.regs.get? Register.x27 = some vS11 ∧
      (∀ k, k < n1 → c'.σ.mem[(d.toNat + k)]? = some (bs1 k)) ∧
      (∀ k, k < n2 → c'.σ.mem[(d.toNat + n1 + k)]? = some (bs2 k)) ∧
      Pin8 c'.σ.mem p.toNat (d + BitVec.ofNat 64 (n1 + n2)) ∧
      Pin4 c'.σ.mem (p.toNat + 12) (cap32 - BitVec.ofNat 32 n1 - BitVec.ofNat 32 n2) ∧
      Pin8 c'.σ.mem (vsp.toNat + 240) (0#64 : BitVec 64) ∧
      Pin4 c'.σ.mem (vsp.toNat + 232) (0#32 : BitVec 32) ∧
      Pin4 c'.σ.mem (vsp.toNat + 180) (0#32 : BitVec 32) ∧
      Pin8 c'.σ.mem (vsp.toNat + 16) vtotF ∧
      (∀ a, ¬(d.toNat ≤ a ∧ a < d.toNat + n1 + n2) →
        ¬(p.toNat ≤ a ∧ a < p.toNat + 8) → ¬(p.toNat + 12 ≤ a ∧ a < p.toNat + 16) →
        ¬(vsp.toNat + 232 ≤ a ∧ a < vsp.toNat + 236) →
        ¬(vsp.toNat + 240 ≤ a ∧ a < vsp.toNat + 248) →
        ¬(vsp.toNat - 88 ≤ a ∧ a < vsp.toNat) →
        ¬(vsp.toNat + 180 ≤ a ∧ a < vsp.toNat + 184) →
        ¬(vsp.toNat + 16 ≤ a ∧ a < vsp.toNat + 24) →
        ¬(vsp.toNat + 368 ≤ a ∧ a < vsp.toNat + 384) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- resid = cursor + digit count = n1 + n2, and it is nonzero
  have hresv : vcurF + vnd6 = BitVec.ofNat 64 (n1 + n2) := by
    rw [hvcurF, hvnd6]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hcurne' : ((vcurF + vnd6 != (0#64 : BitVec 64)) = true) := by
    rw [hresv]
    simp only [bne_iff_ne, ne_eq]
    intro hz
    have hz2 : (BitVec.ofNat 64 (n1 + n2)).toNat = 0 := by rw [hz]; rfl
    rw [BitVec.toNat_ofNat] at hz2
    omega
  -- ============ the call-setup segment (Spec17) ============
  obtain ⟨c1, hsteps17, hG1, hpc1, hra1, ha0c1, ha1c1, ha2c1, hsp1, ht0c1, ht1c1, hs0c1,
      ha6c1, hs4c1, hs6c1, hs7c1, hs10c1, ht3c1, hmemc1, htkc1, hmic1, _hkeep17⟩ :=
    iov2ToSsprintCall_spec vsp vt0 vt1 v8 vcurF vlen vs4 vnd6 viov2 vbase vt3 p vtot (1#32) c
      hGood hload hfp hpc hx2 hx5 hx6 hx8 hx12 hx16 hx20 hx22 hx23 hx26 hx28
      hcnt0 hcnt1 hcnt2b hcnt3 htotS hstrS
      (by rw [hvt0]; decide) hsubwle hb256 (by decide) hb4 hcurne'
      (by omega) (by omega) hspal
      (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega)) htick
  -- the five register facts Spec17 does not export
  obtain ⟨hx3c1, hx9c1, ⟨v18, hx18c1⟩, ⟨v19, hx19c1⟩, ⟨v21, hx21c1⟩⟩ :=
    hmidregs c1 hsteps17 hpc1
  -- ============ address normalization ============
  have hA240 : (vsp + sign_extend (m := 64) (0x0f0#12)).toNat = vsp.toNat + 240 :=
    ptr_addoff vsp _ 240 (by decide) (by omega)
  have hA232 : (vsp + sign_extend (m := 64) (0x0e8#12)).toNat = vsp.toNat + 232 :=
    ptr_addoff vsp _ 232 (by decide) (by omega)
  have hA16 : (vsp + sign_extend (m := 64) (0x010#12)).toNat = vsp.toNat + 16 :=
    ptr_addoff vsp _ 16 (by decide) (by omega)
  have hAv8 : (viov2 + sign_extend (m := 64) (0x008#12)).toNat = vsp.toNat + 376 := by
    rw [ptr_addoff viov2 _ 8 (by decide) (by omega)]
    omega
  have hq224 : (vsp + sign_extend (m := 64) (0x0e0#12)).toNat = vsp.toNat + 224 :=
    ptr_addoff vsp _ 224 (by decide) (by omega)
  have hs1N : (vsp + sign_extend (m := 64) (0x0a7#12)).toNat = vsp.toNat + 167 :=
    ptr_addoff vsp _ 167 (by decide) (by omega)
  rw [hA240, hviov2N, hAv8, hA232, hA16] at hmemc1
  -- pointwise agreement outside the five written windows
  have hagree : ∀ a : Nat, ¬(vsp.toNat + 16 ≤ a ∧ a < vsp.toNat + 24) →
      ¬(vsp.toNat + 232 ≤ a ∧ a < vsp.toNat + 236) →
      ¬(vsp.toNat + 240 ≤ a ∧ a < vsp.toNat + 248) →
      ¬(vsp.toNat + 368 ≤ a ∧ a < vsp.toNat + 384) →
      c1.σ.mem[a]? = c.σ.mem[a]? := by
    intro a h1 h2 h3 h4
    rw [hmemc1, getElem?_writeMap8_out _ _ _ _ (by omega),
      getElem?_writeMap4_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega),
      getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega)]
  -- ============ PreSr's fresh pins (from Spec17's writes) ============
  have hsw2 : swData (sign_extend (m := 64)
      (Sail.BitVec.extractLsb ((sign_extend (m := 64) (1#32 : BitVec 32) : BitVec 64)
        + sign_extend (m := 64) (0x001#12)) 31 0)) = (2#32 : BitVec 32) := by decide
  have hresid1 : Pin8 c1.σ.mem (vsp.toNat + 240) (BitVec.ofNat 64 (n1 + n2)) := by
    rw [hmemc1, ← hresv]
    exact Pin8_frame (fun k hk1 hk2 => by
      rw [getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap4_out _ _ _ _ (by omega),
        getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega)])
      (Pin8_writeMap8 _ _ _)
  have hcount1 : Pin4 c1.σ.mem (vsp.toNat + 232) (2#32 : BitVec 32) := by
    rw [hmemc1, ← hsw2]
    exact Pin4_frame (fun k hk1 hk2 => by
      rw [getElem?_writeMap8_out _ _ _ _ (by omega)]) (Pin4_writeMap4 _ _ _)
  have hiov1b1 : Pin8 c1.σ.mem (viovB.toNat + 16) vbase := by
    rw [show viovB.toNat + 16 = vsp.toNat + 368 from by omega, hmemc1]
    exact Pin8_frame (fun k hk1 hk2 => by
      rw [getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap4_out _ _ _ _ (by omega),
        getElem?_writeMap8_out _ _ _ _ (by omega)]) (Pin8_writeMap8 _ _ _)
  have hiov1l1 : Pin8 c1.σ.mem (viovB.toNat + 24) (BitVec.ofNat 64 n2) := by
    rw [show viovB.toNat + 24 = vsp.toNat + 376 from by omega, hmemc1, ← hvnd6]
    exact Pin8_frame (fun k hk1 hk2 => by
      rw [getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap4_out _ _ _ _ (by omega)])
      (Pin8_writeMap8 _ _ _)
  have htot1 : SlotHolds vsp 0x010 vtotF c1.σ.mem := by
    rw [hvtotF, hmemc1]
    exact slotHolds_self vsp 0x010 (vsp.toNat + 16) _ _ hA16
  -- ============ transported caller slots / pins / bytes ============
  have hslotUp : ∀ (off : Nat) (v : BitVec 64) (A : Nat),
      (vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat = A →
      (A + 8 ≤ vsp.toNat + 16 ∨ (vsp.toNat + 24 ≤ A ∧ A + 8 ≤ vsp.toNat + 232) ∨
        vsp.toNat + 384 ≤ A) →
      SlotHolds vsp off v c.σ.mem → SlotHolds vsp off v c1.σ.mem := by
    intro off v A hA hcond h
    exact slotHolds_of_agree_rt vsp off v A _ _ hA
      (fun a ha1 ha2 => hagree a (by omega) (by omega) (by omega) (by omega)) h
  have hfmt1 := hslotUp 0x000 vfmt (vsp.toNat + 0)
    (ptr_addoff vsp _ 0 (by decide) (by omega)) (by omega) hfmtS
  have h008c1 := hslotUp 0x008 p (vsp.toNat + 8)
    (ptr_addoff vsp _ 8 (by decide) (by omega)) (by omega) hstrS
  have h020c1 := hslotUp 0x020 (0#64) (vsp.toNat + 32)
    (ptr_addoff vsp _ 32 (by decide) (by omega)) (by omega) hs020S
  have hviovc1 := hslotUp 0x0e0 viovB (vsp.toNat + 224)
    (ptr_addoff vsp _ 224 (by decide) (by omega)) (by omega) hviovS
  have h1e8c1 := hslotUp 0x1e8 vS11 (vsp.toNat + 488)
    (ptr_addoff vsp _ 488 (by decide) (by omega)) (by omega) hsv1e8
  have h1f0c1 := hslotUp 0x1f0 vS10 (vsp.toNat + 496)
    (ptr_addoff vsp _ 496 (by decide) (by omega)) (by omega) hsv1f0
  have h1f8c1 := hslotUp 0x1f8 vS9 (vsp.toNat + 504)
    (ptr_addoff vsp _ 504 (by decide) (by omega)) (by omega) hsv1f8
  have h200c1 := hslotUp 0x200 vS8 (vsp.toNat + 512)
    (ptr_addoff vsp _ 512 (by decide) (by omega)) (by omega) hsv200
  have h208c1 := hslotUp 0x208 vS7 (vsp.toNat + 520)
    (ptr_addoff vsp _ 520 (by decide) (by omega)) (by omega) hsv208
  have h210c1 := hslotUp 0x210 vS6o (vsp.toNat + 528)
    (ptr_addoff vsp _ 528 (by decide) (by omega)) (by omega) hsv210
  have h218c1 := hslotUp 0x218 vS5 (vsp.toNat + 536)
    (ptr_addoff vsp _ 536 (by decide) (by omega)) (by omega) hsv218
  have h220c1 := hslotUp 0x220 vS4 (vsp.toNat + 544)
    (ptr_addoff vsp _ 544 (by decide) (by omega)) (by omega) hsv220
  have h228c1 := hslotUp 0x228 vS3 (vsp.toNat + 552)
    (ptr_addoff vsp _ 552 (by decide) (by omega)) (by omega) hsv228
  have h230c1 := hslotUp 0x230 vS2 (vsp.toNat + 560)
    (ptr_addoff vsp _ 560 (by decide) (by omega)) (by omega) hsv230
  have h238c1 := hslotUp 0x238 vS1o (vsp.toNat + 568)
    (ptr_addoff vsp _ 568 (by decide) (by omega)) (by omega) hsv238
  have h240c1 := hslotUp 0x240 vS0o (vsp.toNat + 576)
    (ptr_addoff vsp _ 576 (by decide) (by omega)) (by omega) hsv240
  have h248c1 := hslotUp 0x248 vra0 (vsp.toNat + 584)
    (ptr_addoff vsp _ 584 (by decide) (by omega)) (by omega) hsv248
  have hfnslot1 : SlotHolds (0x8001b798#64) 0x0e8 (0x80012268#64) c1.σ.mem :=
    slotHolds_of_agree_rt _ _ _ 0x8001b880 _ _ (by decide)
      (fun a ha1 ha2 => hagree a (by omega) (by omega) (by omega) (by omega)) hfnslot
  have hmb1 : c1.σ.mem[(0x8001b8f8 : Nat)]? = some (0x01#8) :=
    (hagree _ (by omega) (by omega) (by omega) (by omega)).trans hmbB
  have hnul1 : c1.σ.mem[vfmt.toNat]? = some (0x00#8) :=
    (hagree _ (by omega) (by omega) (by omega) (by omega)).trans hnulB
  have hfl0c1 : c1.σ.mem[p.toNat + 16]? = some fl0 :=
    (hagree _ (by omega) (by omega) (by omega) (by omega)).trans hfl0B
  have hfl1c1 : c1.σ.mem[p.toNat + 17]? = some fl1 :=
    (hagree _ (by omega) (by omega) (by omega) (by omega)).trans hfl1B
  have hiov0b1 : Pin8 c1.σ.mem viovB.toNat (vsp + sign_extend (m := 64) (0x0a7#12)) :=
    Pin8_frame (fun k hk1 hk2 => hagree k (by omega) (by omega) (by omega) (by omega)) hiov0b
  have hiov0l1 : Pin8 c1.σ.mem (viovB.toNat + 8) (BitVec.ofNat 64 n1) :=
    Pin8_frame (fun k hk1 hk2 => hagree k (by omega) (by omega) (by omega) (by omega)) hiov0l
  have hsinkcur1 : Pin8 c1.σ.mem p.toNat d :=
    Pin8_frame (fun k hk1 hk2 => hagree k (by omega) (by omega) (by omega) (by omega)) hsinkcur
  have hsinkcap1 : Pin4 c1.σ.mem (p.toNat + 12) cap32 :=
    Pin4_frame (fun k hk1 hk2 => hagree k (by omega) (by omega) (by omega) (by omega)) hsinkcap
  have hbs1c1 : MvBytes c1.σ.mem (vsp + sign_extend (m := 64) (0x0a7#12)) n1 bs1 :=
    fun k hk => (hagree _ (by omega) (by omega) (by omega) (by omega)).trans (hsignB k hk)
  have hbs2c1 : MvBytes c1.σ.mem vbase n2 bs2 :=
    fun k hk => (hagree _ (by omega) (by omega) (by omega) (by omega)).trans (hdigB k hk)
  -- code pins at the call
  have hsspL1 : __ssprint_rLoaded c1.σ.mem :=
    ssprint_frame_sr _ _
      (fun a ha => hagree a (by omega) (by omega) (by omega) (by omega)) hsspL
  have hsspuL1 : Vsa.Sim.Code.__ssputs_rLoaded c1.σ.mem :=
    ssputs_frame_ss _ _
      (fun a ha => hagree a (by omega) (by omega) (by omega) (by omega)) hsspuL
  have hmvL1 : MemmoveLoaded c1.σ.mem :=
    memmove_frame_sr _ _
      (fun a ha => hagree a (by omega) (by omega) (by omega) (by omega)) hmvL
  have hsliceL1 : SvfprintfSliceLoaded c1.σ.mem :=
    svfSlice_of_agree_rt
      (fun a h1 h2 => hagree a (by omega) (by omega) (by omega) (by omega)) hload
  have hfpL1 : FlushPinsLoaded c1.σ.mem :=
    flushPins_of_agree_rt
      (fun a h1 h2 => hagree a (by omega) (by omega) (by omega) (by omega)) hfp
  have hlocL1 : __locale_mb_cur_maxLoaded c1.σ.mem :=
    locale_of_agree_rt
      (fun a h1 h2 => hagree a (by omega) (by omega) (by omega) (by omega)) hlocC
  have hambL1 : __ascii_mbtowcLoaded c1.σ.mem :=
    amb_of_agree_rt
      (fun a h1 h2 => hagree a (by omega) (by omega) (by omega) (by omega)) hambC
  -- ============ PreSr at the call ============
  have hRegions : SrRegions (vsp + sign_extend (m := 64) (0x0e0#12)) viovB p d
      (vsp + sign_extend (m := 64) (0x0a7#12)) vbase vsp n1 n2 := by
    constructor <;> omega
  have hPre : PreSr (fun R => c1.σ.regs.get? R) (0x80008688#64)
      (vsp + sign_extend (m := 64) (0x0e0#12)) viovB p d
      (vsp + sign_extend (m := 64) (0x0a7#12)) vbase vsp v8 (0x8001b798#64)
      v18 v19 (sign_extend (m := 64)
        (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) v21 v8
      n1 n2 cap32 c1.σ.mem bs1 bs2 c1 :=
    { good := hG1, loaded := hsspL1, sloaded := hsspuL1, mvloaded := hmvL1,
      pc := hpc1, ra := hra1, sp := hsp1, a0 := ha0c1, a1 := ha1c1, a2 := ha2c1,
      cs0 := hs0c1, cs1 := hx9c1, cs2 := hx18c1, cs3 := hx19c1, cs4 := hs4c1,
      cs5 := hx21c1, minstret := hmic1, tick := htkc1, regions := hRegions,
      hviov := by
        rw [hq224]
        exact pin8_of_slotHolds_i26 vsp 0x0e0 viovB (vsp.toNat + 224) c1.σ.mem
          (ptr_addoff vsp _ 224 (by decide) (by omega)) hviovc1,
      hcount := by
        rw [show (vsp + sign_extend (m := 64) (0x0e0#12)).toNat + 8 = vsp.toNat + 232
          from by omega]
        exact hcount1,
      hresid := by
        rw [show (vsp + sign_extend (m := 64) (0x0e0#12)).toNat + 16 = vsp.toNat + 240
          from by omega]
        exact hresid1,
      hiov0b := hiov0b1, hiov0l := hiov0l1, hiov1b := hiov1b1, hiov1l := hiov1l1,
      hcursor := hsinkcur1, hcap := hsinkcap1, hbs1 := hbs1c1, hbs2 := hbs2c1,
      hcaplt := hcaplt, hcap31 := hcap31, memeq := rfl, hframe := fun R _ => rfl }
  -- ============ the flush + return path (Spec25) ============
  obtain ⟨c2, hstepsF, hGf, hpcf, hx1f, hx2f, hx10f, hx8f, hx9f, hx18f, hx19f, hx20f,
      hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hw1f, hw2f, hcurPf, hcapPf, hresPf,
      hcntPf, h180Pf, hframeF, htkF, hmiF⟩ :=
    svfprintf_flushReturn_spec (fun R => c1.σ.regs.get? R)
      (vsp + sign_extend (m := 64) (0x0e0#12)) viovB p d
      (vsp + sign_extend (m := 64) (0x0a7#12)) vbase vsp v8 v18 v19
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb vs4 31 0 - Sail.BitVec.extractLsb vnd6 31 0)) v21 v8
      vfmt vra0 vtotF vS0o vS1o vS2 vS3 vS4 vS5 vS6o vS7 vS8 vS9 vS10 vS11
      fl0 fl1 n1 n2 cap32 c1.σ.mem bs1 bs2 c1
      hPre hsliceL1 hfpL1 hlocL1 hambL1 hx3c1 hfnslot1 hmb1
      hfmt1 h008c1 htot1 h020c1
      h1e8c1 h1f0c1 h1f8c1 h200c1 h208c1 h210c1 h218c1 h220c1 h228c1 h230c1 h238c1
      h240c1 h248c1
      hnul1 hfl0c1 hfl1c1 hflag
      hq224 hsplo hsphi hspal (Or.inl hdge) (Or.inl hpge) hdstk hpstk hpd18
      hfd hfpp hfstk hflo hfhi hfhtif hp18hi hra0align
  -- ============ final assembly ============
  have htotPin1 : Pin8 c1.σ.mem (vsp.toNat + 16) vtotF := by
    rw [hvtotF, hmemc1]
    exact Pin8_writeMap8 _ _ _
  refine ⟨c2, hsteps17.trans hstepsF, hGf, hpcf, hx1f, hx2f, hx10f, hx8f, hx9f, hx18f,
    hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hw1f, hw2f, hcurPf,
    hcapPf, ?_, ?_, h180Pf, ?_, ?_, htkF, hmiF⟩
  · -- uio resid cleared (sp+240)
    rw [show vsp.toNat + 240 = (vsp + sign_extend (m := 64) (0x0e0#12)).toNat + 16
      from by omega]
    exact hresPf
  · -- uio count cleared (sp+232)
    rw [show vsp.toNat + 232 = (vsp + sign_extend (m := 64) (0x0e0#12)).toNat + 8
      from by omega]
    exact hcntPf
  · -- the running total at sp+16 (also returned in a0)
    exact Pin8_frame (fun k hk1 hk2 => hframeF k (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)) htotPin1
  · -- the pointwise frame back to the memory at 0x800078ac
    intro a hW1 hW2 hW3 hW4 hW5 hW6 hW7 hW8 hW9
    exact (hframeF a hW1 hW2 hW3 (by omega) (by omega) hW6 hW7).trans
      (hagree a hW8 hW4 hW5 hW9)

end Vsa.Sim
