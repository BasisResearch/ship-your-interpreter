import Vsa.Sim.SnprintfSpec55
import Vsa.Sim.ImageDischarge
import Vsa.Sim.FrameOn

/-!
# `SnprintfPost` — published Pre/Post records for the snprintf capstone chain

The Spec37–55 capstones each carry 90+ flat hypotheses; consumers must spell
every one, and every statement repeats the same four groups verbatim:

* the ABI entry-register block (PC/ra/sp/gp + the argument registers),
* the 12 callee-saved register conjuncts,
* the static-image pins (45 byte pins + 17 `*Loaded` predicates),
* the `vsp`/`d`/`sz` layout geometry block,

and each conclusion repeats the same 24-conjunct result shape.  Following the
`PreSr` precedent (SnprintfSpec20), this module names those groups as records:

* `SnprintfCall c wra0 vsp d sz v va4 va5 va6 va7` — the ABI entry registers
  of `snprintf(d, sz, "%lld", v)`;
* `CalleeSaved12 c v8 … v27` — the 12 callee-saved values (hypothesis at
  entry, restored in the result);
* `SnprintfStatics m` — `Code.ImageStaticsLoaded` (ONE ELF-load fact, all 45
  data byte pins discharge from it via `ImageDischarge`) + the 16 code-range
  `*Loaded` predicates;
* `SnprintfLayout vsp d sz wra0` — the size guards and layout geometry;
* `SnprintfResult c c' wra0 vsp d v8 … v27 ubytes` — the shared conclusion
  shape: PC/`x1`/`x2`/`x10`, the buffer bytes + NUL, the memory frame **as
  `FrameOn` data** (`Vsa/Sim/FrameOn.lean`), tick/minstret.

and republishes the M3 total capstone through them:

    snprintf_lld_total_spec'  —  6 record hypotheses + `GoodState` + tick
                                 instead of 96 flat ones,

proved by unpacking the records and applying
`Vsa.Sim.snprintf_lld_total_spec` (SnprintfSpec55) verbatim (the 45 byte pins
via the generated `imageStatics_*` discharge lemmas; the pointwise frame
re-packaged by `frameOn_of_pointwise2`).  `snprintfResult_frame_pointwise`
recovers the legacy pointwise frame for flat-style consumers.
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

/-- The ABI entry-register block of `snprintf(d, sz, "%lld", v)` at
`0x80005c44`: PC, return address, stack pointer, the crt0 `gp`, and the four
argument registers (+ the defined-but-arbitrary `a4..a7`). -/
structure SnprintfCall (c : Config) (wra0 vsp d sz v va4 va5 va6 va7 : BitVec 64) : Prop where
  pc : c.σ.regs.get? Register.PC = some (0x80005c44#64)
  ra : c.σ.regs.get? Register.x1 = some wra0
  sp : c.σ.regs.get? Register.x2 = some (vsp + (864#64))
  gp : c.σ.regs.get? Register.x3 = some (0x8001b510#64)
  a0 : c.σ.regs.get? Register.x10 = some d
  a1 : c.σ.regs.get? Register.x11 = some sz
  a2 : c.σ.regs.get? Register.x12 = some (0x800192c0#64)
  a3 : c.σ.regs.get? Register.x13 = some v
  a4 : c.σ.regs.get? Register.x14 = some va4
  a5 : c.σ.regs.get? Register.x15 = some va5
  a6 : c.σ.regs.get? Register.x16 = some va6
  a7 : c.σ.regs.get? Register.x17 = some va7

/-- The 12 callee-saved registers (`s0..s11` = `x8/x9/x18..x27`) holding the
named values — the hypothesis group at entry AND the restored-register group
of every capstone conclusion. -/
structure CalleeSaved12 (c : Config)
    (v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : BitVec 64) : Prop where
  s0 : c.σ.regs.get? Register.x8 = some v8
  s1 : c.σ.regs.get? Register.x9 = some v9
  s2 : c.σ.regs.get? Register.x18 = some v18
  s3 : c.σ.regs.get? Register.x19 = some v19
  s4 : c.σ.regs.get? Register.x20 = some v20
  s5 : c.σ.regs.get? Register.x21 = some v21
  s6 : c.σ.regs.get? Register.x22 = some v22
  s7 : c.σ.regs.get? Register.x23 = some v23
  s8 : c.σ.regs.get? Register.x24 = some v24
  s9 : c.σ.regs.get? Register.x25 = some v25
  s10 : c.σ.regs.get? Register.x26 = some v26
  s11 : c.σ.regs.get? Register.x27 = some v27

/-- The static image at the entry memory: `Code.ImageStaticsLoaded` (one
ELF-load fact — every data byte pin the capstones hypothesize discharges from
it via `ImageDischarge`) plus the 16 code-range `*Loaded` predicates of the
`%lld` path. -/
structure SnprintfStatics (m : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  image : Code.ImageStaticsLoaded m
  snp : Code.SnprintfLoaded m
  slice : SvfprintfSliceLoaded m
  slice2 : SvfprintfSlice2Loaded m
  lconv : Code._localeconv_rLoaded m
  strlen : Code.StrlenLoaded m
  memset : Code.MemsetLoaded m
  lmcm : __locale_mb_cur_maxLoaded m
  amb : __ascii_mbtowcLoaded m
  umod : Code.__umoddi3Loaded m
  udiv : __hidden___udivdi3Loaded m
  flush : FlushPinsLoaded m
  arm : Code.ArmPinsLoaded m
  ssp : __ssprint_rLoaded m
  ssu : Code.__ssputs_rLoaded m
  mv : MemmoveLoaded m

/-- The `vsp`/`d`/`sz` geometry block: size guards (no truncation on this
path), stack placement/alignment, buffer placement/disjointness, return
alignment. -/
structure SnprintfLayout (vsp d sz wra0 : BitVec 64) : Prop where
  sz23 : 23 ≤ sz.toNat
  szhi : sz.toNat < 2 ^ 31
  splo : 0x8001c100 ≤ vsp.toNat
  sphi : vsp.toNat + 864 ≤ 0x100000000
  spal : vsp.toNat % 8 = 0
  dge : 0x8001c000 ≤ d.toNat
  dhi : d.toNat + 22 ≤ 0x100000000
  dstk : vsp.toNat + 864 ≤ d.toNat ∨ d.toNat + 22 ≤ vsp.toNat - 128
  raal : wra0.toNat % 4 = 0

/-- The shared capstone conclusion shape: return to `wra0` with `sp` restored,
`a0` = the byte length, callee-saves restored, the caller buffer =
`ubytes ++ [0]` byte-for-byte, and the memory frame as `FrameOn` data over
the two windows (stack frames, written buffer). -/
structure SnprintfResult (c c' : Config) (wra0 vsp d : BitVec 64)
    (v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : BitVec 64)
    (ubytes : List UInt8) : Prop where
  good : GoodState c'.σ
  pc : c'.σ.regs.get? Register.PC = some wra0
  ra : c'.σ.regs.get? Register.x1 = some wra0
  sp : c'.σ.regs.get? Register.x2 = some (vsp + (864#64))
  a0 : c'.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 ubytes.length)
  saved : CalleeSaved12 c' v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27
  bytes : ∀ (k : Nat) (hk : k < ubytes.length),
    c'.σ.mem[d.toNat + k]? = some (ubytes[k].toBitVec)
  nul : c'.σ.mem[d.toNat + ubytes.length]? = some (0x00#8)
  frame : FrameOn [⟨vsp.toNat - 88, vsp.toNat + 864⟩,
    ⟨d.toNat, d.toNat + ubytes.length + 1⟩] c.σ.mem c'.σ.mem
  tick : c'.tick < 2
  minstret : ∃ u, c'.σ.regs.get? Register.minstret = some u

/-- Legacy-shape adapter: the record's `FrameOn` as the flat two-window
pointwise frame (for flat-style consumers of the record capstone). -/
theorem snprintfResult_frame_pointwise {c c' : Config} {wra0 vsp d : BitVec 64}
    {v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : BitVec 64} {ubytes : List UInt8}
    (h : SnprintfResult c c' wra0 vsp d v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 ubytes) :
    ∀ a : Nat, ¬(vsp.toNat - 88 ≤ a ∧ a < vsp.toNat + 864) →
      ¬(d.toNat ≤ a ∧ a < d.toNat + ubytes.length + 1) →
      c'.σ.mem[a]? = c.σ.mem[a]? :=
  pointwise_of_frameOn2 h.frame

/-- **The `snprintf("%lld")` TOTAL capstone, record form** — every
`v : BitVec 64`; the statement of `Vsa.Sim.snprintf_lld_total_spec`
(SnprintfSpec55) through the published records: 6 record hypotheses +
`GoodState` + the tick bound instead of the 96 flat ones.  Proof = unpack and
apply the original verbatim (static byte pins from `ImageDischarge`). -/
theorem snprintf_lld_total_spec'
    (vsp wra0 d sz v va4 va5 va6 va7 : BitVec 64)
    (v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hstat : SnprintfStatics c.σ.mem)
    (hcall : SnprintfCall c wra0 vsp d sz v va4 va5 va6 va7)
    (hsave : CalleeSaved12 c v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27)
    (hlay : SnprintfLayout vsp d sz wra0)
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
    snprintf_lld_total_spec vsp wra0 d sz v va4 va5 va6 va7
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
      hsz23 hszhi hsplo hsphi hspal hdge hdhi hdstk hraal htick
  exact ⟨c', hsteps, ub, hub,
    { good := hG', pc := hpc', ra := hra', sp := hsp', a0 := ha0',
      saved := ⟨h8, h9, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩,
      bytes := hbytes, nul := hnul,
      frame := frameOn_of_pointwise2 hfr, tick := htk', minstret := hmi' }⟩

end Vsa.Sim
