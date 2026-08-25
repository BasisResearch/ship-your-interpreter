import Vsa.Sim.SnprintfPost
import Vsa.Sim.SnprintfSpec42
import Vsa.Sim.SnprintfSpec38

/-!
# `SnprintfRecords` — record-form wrappers for the M6 boundary capstones

The Spec37–55 capstones each carry 90+ flat hypotheses (`SnprintfPost`
documents the four repeated groups).  `SnprintfPost` already republishes the
**total** M3 capstone (`snprintf_lld_total_spec'`, over every `v : BitVec 64`)
through its records.  This module does the same for the two *boundary*
capstones that M6 / downstream compositions consume directly:

* `snprintf_lld_spec'` — the `snprintf("%lld")` wrapper capstone (Spec42,
  `Vsa.Sim.snprintf_lld_spec`) through the `SnprintfPost` records plus a
  `FrameOn` frame.  Same `SnprintfCall`/`CalleeSaved12`/`SnprintfStatics`/
  `SnprintfLayout` inputs as the total spec, plus the negative-multi-digit
  value ghost `hneg`, and the same `SnprintfResult` conclusion (`FrameOn`
  memory frame).

* `svfprintf_lld_spec'` — the full `_svfprintf_r("%lld")` capstone (Spec38,
  `Vsa.Sim.svfprintf_lld_spec`), the svfprintf-entry ABI boundary Spec37/38
  present to M6.  `SnprintfPost` does *not* name this entry's ABI shape (it is
  the *inner* svfprintf frame, not the snprintf wrapper), so this module
  defines the missing records here:

  * `SvfprintfCall` — the `_svfprintf_r(va0, vfile, vfmt, vva)` entry registers
    at `0x80007654`;
  * `SvfprintfSink` — the wrapper-owned sink: the `"%lld"` format bytes, the
    FILE `_flags` halfword (both guard bits clear), the sink cursor/capacity
    pins, and the eight va-area argument bytes;
  * `SvfprintfLayout` — the fmt/FILE/va/dest/stack geometry block;
  * `SvfprintfResult` — the shared conclusion: `a0 = 1 + n2`, the `'-' ++
    digits` destination, the updated FILE fields, and the memory frame as
    **`FrameOn` data** over svfprintf's four windows.

Each wrapper is proved by unpacking the records, applying the original
capstone verbatim, and repacking (the static byte pins via the `SnprintfPost`
`SnprintfStatics.image` + `ImageDischarge` discharge lemmas; the pointwise
frame re-packaged by `frameOn_of_pointwise{2,4}`).  `svfprintfResult_frame_pointwise`
recovers the legacy four-window pointwise frame for flat-style consumers.
-/

open Vsa Vsa.Sim Vsa.While
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Sim.Code (SvfprintfSliceLoaded SvfprintfSlice2Loaded FlushPinsLoaded MemmoveLoaded
  __ssprint_rLoaded __locale_mb_cur_maxLoaded __ascii_mbtowcLoaded __hidden___udivdi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## 1. `snprintf("%lld")` wrapper capstone, record form (Spec42) -/

/-- **The `snprintf("%lld")` wrapper capstone, record form** — the statement of
`Vsa.Sim.snprintf_lld_spec` (Spec42) through the `SnprintfPost` records: the
same `SnprintfCall`/`CalleeSaved12`/`SnprintfStatics`/`SnprintfLayout` inputs
as `snprintf_lld_total_spec'`, plus the negative-multi-digit value ghost
`hneg`, with the `SnprintfResult` (`FrameOn`) conclusion instead of the ~30
flat conjuncts.  Proof = unpack, apply Spec42 verbatim, repack. -/
theorem snprintf_lld_spec'
    (vsp wra0 d sz v va4 va5 va6 va7 : BitVec 64)
    (v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hstat : SnprintfStatics c.σ.mem)
    (hcall : SnprintfCall c wra0 vsp d sz v va4 va5 va6 va7)
    (hsave : CalleeSaved12 c v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27)
    (hlay : SnprintfLayout vsp d sz wra0)
    (hneg : zopz0zKzJ_s v (0#64) = false)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧
    ∃ ubytes : List UInt8,
      ubytes = (intToString v.toInt).toUTF8.data.toList ∧
      SnprintfResult c c' wra0 vsp d v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 ubytes := by
  obtain ⟨himg, hsnp, hsl, hsl2, hlc, hstr, hms, hlm, hamb, hum, hud, hfp, hap, hssp,
    hssu, hmv⟩ := hstat
  obtain ⟨hpc, hx1, hx2, hx3, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17⟩ := hcall
  obtain ⟨hx8, hx9, hx18, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27⟩ := hsave
  obtain ⟨hsz23, hszhi, hsplo, hsphi, hspal, hdge, hdhi, hdstk, hraal⟩ := hlay
  obtain ⟨c', hsteps, hG', ub, hub, hpc', hra', hsp', ha0', h8, h9, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, hbytes, hnul, hfr, htk', hmi'⟩ :=
    snprintf_lld_spec vsp wra0 d sz v va4 va5 va6 va7
      v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 c
      hG hsnp (imageStatics_lldFmt himg) hsl hsl2 hlc hstr hms hlm hamb hum hud hfp hap
      (imageStatics_parseSlotD himg) hssp hssu hmv
      hpc hx1 hx2 hx3 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx17
      hx8 hx9 hx18 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27
      (imageStatics_hdp0 himg) (imageStatics_hdp1 himg) (imageStatics_hdp2 himg)
      (imageStatics_hdp3 himg) (imageStatics_hdp4 himg) (imageStatics_hdp5 himg)
      (imageStatics_hdp6 himg) (imageStatics_hdp7 himg)
      (imageStatics_hdb0 himg) (imageStatics_hdb1 himg) (imageStatics_hdb2 himg)
      (imageStatics_hdb3 himg) (imageStatics_hdb4 himg) (imageStatics_hdb5 himg)
      (imageStatics_hdb6 himg) (imageStatics_hdb7 himg)
      (imageStatics_hfn0 himg) (imageStatics_hfn1 himg) (imageStatics_hfn2 himg)
      (imageStatics_hfn3 himg) (imageStatics_hfn4 himg) (imageStatics_hfn5 himg)
      (imageStatics_hfn6 himg) (imageStatics_hfn7 himg)
      (imageStatics_hmbB himg)
      (imageStatics_htb0 himg) (imageStatics_htb1 himg) (imageStatics_htb2 himg)
      (imageStatics_htb3 himg)
      (imageStatics_himp0 himg) (imageStatics_himp1 himg) (imageStatics_himp2 himg)
      (imageStatics_himp3 himg) (imageStatics_himp4 himg) (imageStatics_himp5 himg)
      (imageStatics_himp6 himg) (imageStatics_himp7 himg)
      hsz23 hszhi hneg hsplo hsphi hspal hdge hdhi hdstk hraal htick
  exact ⟨c', hsteps, ub, hub,
    { good := hG', pc := hpc', ra := hra', sp := hsp', a0 := ha0',
      saved := ⟨h8, h9, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩,
      bytes := hbytes, nul := hnul,
      frame := frameOn_of_pointwise2 hfr, tick := htk', minstret := hmi' }⟩

/-! ## 2. `_svfprintf_r("%lld")` capstone, record form (Spec38) -/

/-- The `_svfprintf_r(va0, vfile, vfmt, vva)` ABI entry-register block at
`0x80007654`: PC, return address, stack pointer, the crt0 `gp`, and the four
argument registers (reent, sink FILE, format, va_list). -/
structure SvfprintfCall (c : Config) (vsp vra0 va0 vfile vfmt vva : BitVec 64) : Prop where
  pc : c.σ.regs.get? Register.PC = some (0x80007654#64)
  sp : c.σ.regs.get? Register.x2 = some (vsp + (592#64))
  ra : c.σ.regs.get? Register.x1 = some vra0
  gp : c.σ.regs.get? Register.x3 = some (0x8001b510#64)
  a0 : c.σ.regs.get? Register.x10 = some va0
  a1 : c.σ.regs.get? Register.x11 = some vfile
  a2 : c.σ.regs.get? Register.x12 = some vfmt
  a3 : c.σ.regs.get? Register.x13 = some vva

/-- The wrapper-owned sink of `_svfprintf_r`: the `"%lld"` format bytes at
`vfmt`, the FILE `_flags` halfword (`fl0`/`fl1`, with the `__SCLE` (`0x080`)
and `__SSTRICT` (`0x040`) bits clear), the sink cursor (`d`) and capacity
(`cap32`) pins, the capacity bounds, and the eight va-area argument bytes at
`vva`. -/
structure SvfprintfSink (m : Std.ExtHashMap Nat (BitVec 8))
    (vfmt vfile vva d : BitVec 64) (fl0 fl1 : BitVec 8) (cap32 : BitVec 32)
    (a0 a1 a2 a3 a4b a5b a6 a7 : BitVec 8) : Prop where
  fmt0 : m[vfmt.toNat]? = some (0x25#8)
  fmt1 : m[vfmt.toNat + 1]? = some (0x6c#8)
  fmt2 : m[vfmt.toNat + 2]? = some (0x6c#8)
  fmt3 : m[vfmt.toNat + 3]? = some (0x64#8)
  fmt4 : m[vfmt.toNat + 4]? = some (0x00#8)
  fl0B : m[vfile.toNat + 16]? = some fl0
  fl1B : m[vfile.toNat + 17]? = some fl1
  flagB : (zero_extend (m := 64) ((fl1.append fl0) : BitVec (8 * 2)) : BitVec 64)
    &&& sign_extend (m := 64) (0x080#12) = 0#64
  flag40 : (zero_extend (m := 64) ((fl1.append fl0) : BitVec (8 * 2)) : BitVec 64)
    &&& sign_extend (m := 64) (0x040#12) = 0#64
  sinkcur : Pin8 m vfile.toNat d
  sinkcap : Pin4 m (vfile.toNat + 12) cap32
  cap21 : 21 < cap32.toNat
  cap31 : cap32.toNat < 2 ^ 31
  a0B : m[vva.toNat]? = some a0
  a1B : m[vva.toNat + 1]? = some a1
  a2B : m[vva.toNat + 2]? = some a2
  a3B : m[vva.toNat + 3]? = some a3
  a4B : m[vva.toNat + 4]? = some a4b
  a5B : m[vva.toNat + 5]? = some a5b
  a6B : m[vva.toNat + 6]? = some a6
  a7B : m[vva.toNat + 7]? = some a7

/-- The `_svfprintf_r` fmt/FILE/va/dest/stack geometry block: RAM bounds,
alignment, HTIF disjointness, and the pairwise-disjointness facts the body and
return path need. -/
structure SvfprintfLayout (vsp vfmt vfile vva d vra0 : BitVec 64) : Prop where
  vlo : 0x80000000 ≤ vva.toNat
  vhiram : vva.toNat + 8 ≤ 0x100000000
  vhtif : vva.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vva.toNat
  valign : vva.toNat % 8 = 0
  vdisj : vva.toNat + 8 ≤ vsp.toNat ∨ vsp.toNat + 592 ≤ vva.toNat
  filelo : vsp.toNat + 592 ≤ vfile.toNat
  filehi : vfile.toNat + 24 ≤ 0x100000000
  fileal : vfile.toNat % 8 = 0
  flo : 0x80000000 ≤ vfmt.toNat
  fhi : vfmt.toNat + 8 ≤ 0x100000000
  fhtif : vfmt.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vfmt.toNat
  fstk : vfmt.toNat + 8 ≤ vsp.toNat - 128 ∨ vsp.toNat + 592 ≤ vfmt.toNat
  fd : vfmt.toNat + 8 ≤ d.toNat ∨ d.toNat + 21 ≤ vfmt.toNat
  fpp : vfmt.toNat + 8 ≤ vfile.toNat ∨ vfile.toNat + 24 ≤ vfmt.toNat
  splo : 0x8001c000 ≤ vsp.toNat
  sphi : vsp.toNat + 592 ≤ 0x100000000
  spal : vsp.toNat % 8 = 0
  dge : 0x8001b900 ≤ d.toNat
  dhi : d.toNat + 21 ≤ 0x100000000
  dstk : vsp.toNat + 592 ≤ d.toNat ∨ d.toNat + 21 ≤ vsp.toNat - 128
  filed : vfile.toNat + 24 ≤ d.toNat ∨ d.toNat + 21 ≤ vfile.toNat
  ra0align : vra0.toNat % 4 = 0

/-- The `_svfprintf_r("%lld")` conclusion shape: return to `vra0` with `sp`
restored, `a0 = 1 + n2` (the total = sign byte + `n2` digits), callee-saves
restored, the destination = `'-'` (`signByte`) followed by the `n2` decimal
digits `bs2 k`, the updated FILE cursor/capacity fields, and the memory frame
as **`FrameOn` data** over svfprintf's four windows (its stack frame, the
destination, and the two written FILE fields). -/
structure SvfprintfResult (c c' : Config) (vsp vra0 vfile d : BitVec 64)
    (vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o : BitVec 64)
    (cap32 : BitVec 32) (mag : Nat) (n2 : Nat) (bs2 : Nat → BitVec 8) : Prop where
  good : GoodState c'.σ
  n2lo : 1 ≤ n2
  n2hi : n2 ≤ 20
  lead : mag / 10 ^ (n2 - 1) ≤ 9
  minD : n2 = 1 ∨ 9 < mag / 10 ^ (n2 - 2)
  digits : ∀ k, k < n2 → bs2 k = BitVec.ofNat 8 (48 + (mag / 10 ^ (n2 - 1 - k)) % 10)
  pc : c'.σ.regs.get? Register.PC = some vra0
  ra : c'.σ.regs.get? Register.x1 = some vra0
  sp : c'.σ.regs.get? Register.x2 = some (vsp + (592#64))
  a0 : c'.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 (1 + n2))
  s0 : c'.σ.regs.get? Register.x8 = some vS0o
  s1 : c'.σ.regs.get? Register.x9 = some vS1o
  s2 : c'.σ.regs.get? Register.x18 = some vS2o
  s3 : c'.σ.regs.get? Register.x19 = some vS3o
  s4 : c'.σ.regs.get? Register.x20 = some vS4o
  s5 : c'.σ.regs.get? Register.x21 = some vS5o
  s6 : c'.σ.regs.get? Register.x22 = some vS6o
  s7 : c'.σ.regs.get? Register.x23 = some vS7o
  s8 : c'.σ.regs.get? Register.x24 = some vS8o
  s9 : c'.σ.regs.get? Register.x25 = some vS9o
  s10 : c'.σ.regs.get? Register.x26 = some vS10o
  s11 : c'.σ.regs.get? Register.x27 = some vS11o
  sign : c'.σ.mem[d.toNat]? = some signByte
  digitsMem : ∀ k, k < n2 → c'.σ.mem[d.toNat + 1 + k]? = some (bs2 k)
  cur : Pin8 c'.σ.mem vfile.toNat (d + BitVec.ofNat 64 (1 + n2))
  cap : Pin4 c'.σ.mem (vfile.toNat + 12)
    (cap32 - BitVec.ofNat 32 1 - BitVec.ofNat 32 n2)
  frame : FrameOn [⟨vsp.toNat - 88, vsp.toNat + 592⟩,
    ⟨d.toNat, d.toNat + 1 + n2⟩,
    ⟨vfile.toNat, vfile.toNat + 8⟩,
    ⟨vfile.toNat + 12, vfile.toNat + 16⟩] c.σ.mem c'.σ.mem
  tick : c'.tick < 2
  minstret : ∃ u, c'.σ.regs.get? Register.minstret = some u

/-- Legacy-shape adapter: the `SvfprintfResult` `FrameOn` as the flat
four-window pointwise frame (for flat-style consumers). -/
theorem svfprintfResult_frame_pointwise {c c' : Config} {vsp vra0 vfile d : BitVec 64}
    {vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o : BitVec 64}
    {cap32 : BitVec 32} {mag n2 : Nat} {bs2 : Nat → BitVec 8}
    (h : SvfprintfResult c c' vsp vra0 vfile d
      vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o cap32 mag n2 bs2) :
    ∀ a : Nat, ¬(vsp.toNat - 88 ≤ a ∧ a < vsp.toNat + 592) →
      ¬(d.toNat ≤ a ∧ a < d.toNat + 1 + n2) →
      ¬(vfile.toNat ≤ a ∧ a < vfile.toNat + 8) →
      ¬(vfile.toNat + 12 ≤ a ∧ a < vfile.toNat + 16) →
      c'.σ.mem[a]? = c.σ.mem[a]? :=
  pointwise_of_frameOn4 h.frame

/-- **The full `_svfprintf_r("%lld")` capstone, record form** — the statement of
`Vsa.Sim.svfprintf_lld_spec` (Spec38) through the records: `SvfprintfCall`
(ABI entry) + `SnprintfStatics` (image statics) + `SvfprintfSink`
(wrapper-owned sink) + `CalleeSaved12` + `SvfprintfLayout` + the value ghost
`hneg`, with the `SvfprintfResult` (`FrameOn`) conclusion.  Proof = unpack,
apply Spec38 verbatim (static byte pins from `ImageDischarge`), repack. -/
theorem svfprintf_lld_spec'
    (vsp vra0 va0 vfile vfmt vva d : BitVec 64)
    (vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o : BitVec 64)
    (fl0 fl1 : BitVec 8) (cap32 : BitVec 32)
    (a0 a1 a2 a3 a4b a5b a6 a7 : BitVec 8)
    (c : Config)
    (hG : GoodState c.σ)
    (hstat : SnprintfStatics c.σ.mem)
    (hcall : SvfprintfCall c vsp vra0 va0 vfile vfmt vva)
    (hsave : CalleeSaved12 c vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o)
    (hsink : SvfprintfSink c.σ.mem vfmt vfile vva d fl0 fl1 cap32 a0 a1 a2 a3 a4b a5b a6 a7)
    (hlay : SvfprintfLayout vsp vfmt vfile vva d vra0)
    (hneg : zopz0zKzJ_s (llArg a0 a1 a2 a3 a4b a5b a6 a7) (0#64) = false)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧
    ∃ (n2 : Nat) (bs2 : Nat → BitVec 8),
      SvfprintfResult c c' vsp vra0 vfile d
        vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o cap32
        ((0#64) - llArg a0 a1 a2 a3 a4b a5b a6 a7).toNat n2 bs2 := by
  obtain ⟨himg, hsnp, hsl, hsl2, hlc, hstr, hms, hlm, hamb, hum, hud, hfp, hap, hssp,
    hssu, hmv⟩ := hstat
  obtain ⟨hpc, hx2, hx1, hx3, hx10, hx11, hx12, hx13⟩ := hcall
  obtain ⟨hx8, hx9, hx18, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27⟩ := hsave
  obtain ⟨hfmt0, hfmt1, hfmt2, hfmt3, hfmt4, hfl0B, hfl1B, hflagB, hflag40,
    hsinkcur, hsinkcap, hcap21, hcap31,
    ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ := hsink
  obtain ⟨hvlo, hvhiram, hvhtif, hvalign, hvdisj, hfilelo, hfilehi, hfileal, hflo, hfhi,
    hfhtif, hfstk, hfd, hfpp, hsplo, hsphi, hspal, hdge, hdhi, hdstk, hfiled, hra0align⟩ := hlay
  obtain ⟨c', hsteps, hG', n2, bs2, hn2a, hn2b, hlead, hminD, hbs2f,
    hpc', hra', hsp', ha0', h8, h9, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27,
    hsign, hdig, hcur, hcap, hframe, htk', hmi'⟩ :=
    svfprintf_lld_spec vsp vra0 va0 vfile vfmt vva d
      vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o
      fl0 fl1 cap32 a0 a1 a2 a3 a4b a5b a6 a7 c hG
      hsl hsl2 hlc hstr hms hlm hamb hum hud hfp hap
      (imageStatics_parseSlotD himg) hssp hssu hmv
      hpc hx2 hx1 hx3 hx10 hx11 hx12 hx13 hx8 hx9 hx22 hx18 hx19 hx20 hx21 hx23 hx24
      hx25 hx26 hx27
      (imageStatics_hdp0 himg) (imageStatics_hdp1 himg) (imageStatics_hdp2 himg)
      (imageStatics_hdp3 himg) (imageStatics_hdp4 himg) (imageStatics_hdp5 himg)
      (imageStatics_hdp6 himg) (imageStatics_hdp7 himg)
      (imageStatics_hdb0 himg) (imageStatics_hdb1 himg) (imageStatics_hdb2 himg)
      (imageStatics_hdb3 himg) (imageStatics_hdb4 himg) (imageStatics_hdb5 himg)
      (imageStatics_hdb6 himg) (imageStatics_hdb7 himg)
      (imageStatics_hfn0 himg) (imageStatics_hfn1 himg) (imageStatics_hfn2 himg)
      (imageStatics_hfn3 himg) (imageStatics_hfn4 himg) (imageStatics_hfn5 himg)
      (imageStatics_hfn6 himg) (imageStatics_hfn7 himg)
      (imageStatics_hmbB himg)
      (imageStatics_htb0 himg) (imageStatics_htb1 himg) (imageStatics_htb2 himg)
      (imageStatics_htb3 himg)
      hfmt0 hfmt1 hfmt2 hfmt3 hfmt4 hfl0B hfl1B hflagB hflag40
      hsinkcur hsinkcap hcap21 hcap31
      ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 hvlo hvhiram hvhtif hvalign hvdisj
      hneg
      hfilelo hfilehi hfileal hflo hfhi hfhtif hfstk hfd hfpp hsplo hsphi hspal
      hdge hdhi hdstk hfiled hra0align htick
  exact ⟨c', hsteps, n2, bs2,
    { good := hG', n2lo := hn2a, n2hi := hn2b, lead := hlead, minD := hminD,
      digits := hbs2f, pc := hpc', ra := hra', sp := hsp', a0 := ha0',
      s0 := h8, s1 := h9, s2 := h18, s3 := h19, s4 := h20, s5 := h21, s6 := h22,
      s7 := h23, s8 := h24, s9 := h25, s10 := h26, s11 := h27,
      sign := hsign, digitsMem := hdig, cur := hcur, cap := hcap,
      frame := frameOn_of_pointwise4 hframe, tick := htk', minstret := hmi' }⟩

end Vsa.Sim
