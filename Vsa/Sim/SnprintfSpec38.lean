import Vsa.Sim.SnprintfSpec37

/-!
# M3 Layer-3 — `SnprintfSpec38` : the FULL svfprintf `%lld` spec
## `0x80007654` (`_svfprintf_r` ABI entry) → svfprintf's `ret`, `a0 = 1 + n2`

THE svfprintf capstone: one `Steps` chain

    svfEntryToSsprintCall_spec  (Spec37 : 0x80007654 → 0x8000e908, `PreSr`
                                 assembled + every non-wrapper Spec25 input)
  ≫ svfprintf_flushReturn_spec  (Spec25 : the `__ssprint_r` 2-iovec flush,
                                 post-call cleanup, parse-loop NUL exit,
                                 epilogue, `ret` with `a0 = the total`)

from the `_svfprintf_r` ABI entry (reent/FILE/fmt/va registers, the `"%lld"`
bytes, the sink FILE struct pins, the image statics, the value ghosts
`hneg`, layout) to svfprintf's `ret` with

* **`a0 = BitVec.ofNat 64 (1 + n2)`** — the total character count (`1` sign
  byte + `n2` digits), also pinned at the (dead) total slot;
* the destination buffer `[d, d + 1 + n2)` = the `'-'` byte (`signByte`)
  followed by the `n2` decimal digits — the exact Spec37 formula
  `bs2 k = ofNat 8 (48 + (mag / 10^(n2−1−k)) % 10)` for the magnitude
  `mag = ((0#64) − llArg …).toNat`, with `1 ≤ n2 ≤ 20`, the leading-digit
  bound `mag / 10^(n2−1) ≤ 9` and the minimality bound
  `n2 = 1 ∨ 9 < mag / 10^(n2−2)` (the leading digit is nonzero — `n2` is
  exactly the decimal digit count, from the widened `DLI`);
* the FILE cursor slot := `d + ofNat (1+n2)` and the capacity slot :=
  `cap32 − 1 − n2` (32-bit);
* callee-saves x8/x9/x18–x27 and `sp` restored, `PC = x1 = vra0`;
* a pointwise memory frame outside `[vsp − 88, vsp + 592)` (svfprintf's frame
  plus the `__ssprint_r`/`__ssputs_r` sub-frames), the destination window and
  the two written FILE fields.

## Residual hypotheses (wrapper-owned only)

Exactly Spec37's wrapper-owned inputs — the sink FILE struct (`hsinkcur`/
`hsinkcap`/capacity bounds/the `_flags` bytes with the `0x080` **and** `0x040`
bits clear), the destination-buffer layout, the va-area bytes + layout, the
value ghosts (negative, magnitude > 9), the `"%lld"` bytes, the static-image
pins, and the fmt/stack layout — plus `vra0` 4-aligned and two fmt-vs-sink/
dest disjointness facts (`hfd`/`hfpp`) the return path's re-read of the fmt
NUL needs.  `hfstk` is stated with the `vsp − 128` margin (the fmt bytes must
survive the flush sub-frames; on the real run the format is a `.rodata`
string far below the stack).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded SvfprintfSlice2Loaded FlushPinsLoaded MemmoveLoaded
  __ssprint_rLoaded __locale_mb_cur_maxLoaded __ascii_mbtowcLoaded __hidden___udivdi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- **The full svfprintf `%lld` spec** — `_svfprintf_r` ABI entry to `ret`,
negative multi-digit argument: `a0 = 1 + n2`, destination = `'-' ++ digits`.
See the module docstring. -/
theorem svfprintf_lld_spec
    (vsp vra0 va0 vfile vfmt vva d : BitVec 64)
    (vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o : BitVec 64)
    (fl0 fl1 : BitVec 8) (cap32 : BitVec 32)
    (a0 a1 a2 a3 a4b a5b a6 a7 : BitVec 8)
    (c : Config)
    (hG : GoodState c.σ)
    -- code / static-code pins at entry (link-time constants of the image)
    (hsl0 : SvfprintfSliceLoaded c.σ.mem)
    (hsl20 : SvfprintfSlice2Loaded c.σ.mem)
    (hlc0 : Vsa.Sim.Code._localeconv_rLoaded c.σ.mem)
    (hstr0 : Vsa.Sim.Code.StrlenLoaded c.σ.mem)
    (hms0 : Vsa.Sim.Code.MemsetLoaded c.σ.mem)
    (hlm0 : __locale_mb_cur_maxLoaded c.σ.mem)
    (hamb0 : __ascii_mbtowcLoaded c.σ.mem)
    (hum0 : Vsa.Sim.Code.__umoddi3Loaded c.σ.mem)
    (hud0 : __hidden___udivdi3Loaded c.σ.mem)
    (hfp0 : FlushPinsLoaded c.σ.mem)
    (hap0 : Vsa.Sim.Code.ArmPinsLoaded c.σ.mem)
    (hslot0 : ParseSlotPinned 0x64 (0x80008008#64) c.σ.mem)
    (hsspL0 : __ssprint_rLoaded c.σ.mem)
    (hsspuL0 : Vsa.Sim.Code.__ssputs_rLoaded c.σ.mem)
    (hmvL0 : MemmoveLoaded c.σ.mem)
    -- ABI entry registers
    (hpc : c.σ.regs.get? Register.PC = some (0x80007654#64))
    (hx2 : c.σ.regs.get? Register.x2 = some (vsp + (592#64)))
    (hx1 : c.σ.regs.get? Register.x1 = some vra0)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx10 : c.σ.regs.get? Register.x10 = some va0)
    (hx11 : c.σ.regs.get? Register.x11 = some vfile)
    (hx12 : c.σ.regs.get? Register.x12 = some vfmt)
    (hx13 : c.σ.regs.get? Register.x13 = some vva)
    (hx8 : c.σ.regs.get? Register.x8 = some vS0o)
    (hx9 : c.σ.regs.get? Register.x9 = some vS1o)
    (hx22 : c.σ.regs.get? Register.x22 = some vS6o)
    (hx18 : c.σ.regs.get? Register.x18 = some vS2o)
    (hx19 : c.σ.regs.get? Register.x19 = some vS3o)
    (hx20 : c.σ.regs.get? Register.x20 = some vS4o)
    (hx21 : c.σ.regs.get? Register.x21 = some vS5o)
    (hx23 : c.σ.regs.get? Register.x23 = some vS7o)
    (hx24 : c.σ.regs.get? Register.x24 = some vS8o)
    (hx25 : c.σ.regs.get? Register.x25 = some vS9o)
    (hx26 : c.σ.regs.get? Register.x26 = some vS10o)
    (hx27 : c.σ.regs.get? Register.x27 = some vS11o)
    -- static data (link-time constants, as Spec36/37)
    (hdp0 : c.σ.mem[(0x8001b898 : Nat)]? = some (0x70#8))
    (hdp1 : c.σ.mem[(0x8001b898 : Nat) + 1]? = some (0x97#8))
    (hdp2 : c.σ.mem[(0x8001b898 : Nat) + 2]? = some (0x01#8))
    (hdp3 : c.σ.mem[(0x8001b898 : Nat) + 3]? = some (0x80#8))
    (hdp4 : c.σ.mem[(0x8001b898 : Nat) + 4]? = some (0x00#8))
    (hdp5 : c.σ.mem[(0x8001b898 : Nat) + 5]? = some (0x00#8))
    (hdp6 : c.σ.mem[(0x8001b898 : Nat) + 6]? = some (0x00#8))
    (hdp7 : c.σ.mem[(0x8001b898 : Nat) + 7]? = some (0x00#8))
    (hdb0 : c.σ.mem[(0x80019770 : Nat)]? = some (0x2e#8))
    (hdb1 : c.σ.mem[(0x80019770 : Nat) + 1]? = some (0x00#8))
    (hdb2 : c.σ.mem[(0x80019770 : Nat) + 2]? = some (0x00#8))
    (hdb3 : c.σ.mem[(0x80019770 : Nat) + 3]? = some (0x00#8))
    (hdb4 : c.σ.mem[(0x80019770 : Nat) + 4]? = some (0x00#8))
    (hdb5 : c.σ.mem[(0x80019770 : Nat) + 5]? = some (0x00#8))
    (hdb6 : c.σ.mem[(0x80019770 : Nat) + 6]? = some (0x00#8))
    (hdb7 : c.σ.mem[(0x80019770 : Nat) + 7]? = some (0x00#8))
    (hfn0 : c.σ.mem[(0x8001b880 : Nat)]? = some (0x68#8))
    (hfn1 : c.σ.mem[(0x8001b880 : Nat) + 1]? = some (0x22#8))
    (hfn2 : c.σ.mem[(0x8001b880 : Nat) + 2]? = some (0x01#8))
    (hfn3 : c.σ.mem[(0x8001b880 : Nat) + 3]? = some (0x80#8))
    (hfn4 : c.σ.mem[(0x8001b880 : Nat) + 4]? = some (0x00#8))
    (hfn5 : c.σ.mem[(0x8001b880 : Nat) + 5]? = some (0x00#8))
    (hfn6 : c.σ.mem[(0x8001b880 : Nat) + 6]? = some (0x00#8))
    (hfn7 : c.σ.mem[(0x8001b880 : Nat) + 7]? = some (0x00#8))
    (hmbB : c.σ.mem[(0x8001b8f8 : Nat)]? = some (0x01#8))
    (htb0 : c.σ.mem[(0x8001a22c : Nat)]? = some (0x38#8))
    (htb1 : c.σ.mem[(0x8001a22c : Nat) + 1]? = some (0xe4#8))
    (htb2 : c.σ.mem[(0x8001a22c : Nat) + 2]? = some (0xfe#8))
    (htb3 : c.σ.mem[(0x8001a22c : Nat) + 3]? = some (0xff#8))
    -- the "%lld" format bytes
    (hfmt0 : c.σ.mem[vfmt.toNat]? = some (0x25#8))
    (hfmt1 : c.σ.mem[vfmt.toNat + 1]? = some (0x6c#8))
    (hfmt2 : c.σ.mem[vfmt.toNat + 2]? = some (0x6c#8))
    (hfmt3 : c.σ.mem[vfmt.toNat + 3]? = some (0x64#8))
    (hfmt4 : c.σ.mem[vfmt.toNat + 4]? = some (0x00#8))
    -- the FILE `_flags` halfword (wrapper-owned; __SCLE and __SSTRICT clear)
    (hfl0B : c.σ.mem[vfile.toNat + 16]? = some fl0)
    (hfl1B : c.σ.mem[vfile.toNat + 17]? = some fl1)
    (hflagB : (zero_extend (m := 64) ((fl1.append fl0) : BitVec (8 * 2)) : BitVec 64)
        &&& sign_extend (m := 64) (0x080#12) = 0#64)
    (hflag40 : (zero_extend (m := 64) ((fl1.append fl0) : BitVec (8 * 2)) : BitVec 64)
        &&& sign_extend (m := 64) (0x040#12) = 0#64)
    -- the sink FILE struct (wrapper-owned)
    (hsinkcur : Pin8 c.σ.mem vfile.toNat d)
    (hsinkcap : Pin4 c.σ.mem (vfile.toNat + 12) cap32)
    (hcap21 : 21 < cap32.toNat)
    (hcap31 : cap32.toNat < 2 ^ 31)
    -- the va_list area (wrapper-owned): the eight argument bytes at `vva`
    (ha0 : c.σ.mem[vva.toNat]? = some a0)
    (ha1 : c.σ.mem[vva.toNat + 1]? = some a1)
    (ha2 : c.σ.mem[vva.toNat + 2]? = some a2)
    (ha3 : c.σ.mem[vva.toNat + 3]? = some a3)
    (ha4 : c.σ.mem[vva.toNat + 4]? = some a4b)
    (ha5 : c.σ.mem[vva.toNat + 5]? = some a5b)
    (ha6 : c.σ.mem[vva.toNat + 6]? = some a6)
    (ha7 : c.σ.mem[vva.toNat + 7]? = some a7)
    (hvlo : 0x80000000 ≤ vva.toNat)
    (hvhiram : vva.toNat + 8 ≤ 0x100000000)
    (hvhtif : vva.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vva.toNat)
    (hvalign : vva.toNat % 8 = 0)
    (hvdisj : vva.toNat + 8 ≤ vsp.toNat ∨ vsp.toNat + 592 ≤ vva.toNat)
    -- the argument-value ghosts: negative, magnitude > 9
    (hneg : zopz0zKzJ_s (llArg a0 a1 a2 a3 a4b a5b a6 a7) (0#64) = false)
    -- layout
    (hfilelo : vsp.toNat + 592 ≤ vfile.toNat)
    (hfilehi : vfile.toNat + 24 ≤ 0x100000000)
    (hfileal : vfile.toNat % 8 = 0)
    (hflo : 0x80000000 ≤ vfmt.toNat)
    (hfhi : vfmt.toNat + 8 ≤ 0x100000000)
    (hfhtif : vfmt.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vfmt.toNat)
    (hfstk : vfmt.toNat + 8 ≤ vsp.toNat - 128 ∨ vsp.toNat + 592 ≤ vfmt.toNat)
    (hfd : vfmt.toNat + 8 ≤ d.toNat ∨ d.toNat + 21 ≤ vfmt.toNat)
    (hfpp : vfmt.toNat + 8 ≤ vfile.toNat ∨ vfile.toNat + 24 ≤ vfmt.toNat)
    (hsplo : 0x8001c000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (hdge : 0x8001b900 ≤ d.toNat)
    (hdhi : d.toNat + 21 ≤ 0x100000000)
    (hdstk : vsp.toNat + 592 ≤ d.toNat ∨ d.toNat + 21 ≤ vsp.toNat - 128)
    (hfiled : vfile.toNat + 24 ≤ d.toNat ∨ d.toNat + 21 ≤ vfile.toNat)
    (hra0align : vra0.toNat % 4 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
    ∃ (n2 : Nat) (bs2 : Nat → BitVec 8),
      1 ≤ n2 ∧ n2 ≤ 20 ∧
      ((0#64) - llArg a0 a1 a2 a3 a4b a5b a6 a7).toNat / 10 ^ (n2 - 1) ≤ 9 ∧
      (n2 = 1 ∨ 9 < ((0#64) - llArg a0 a1 a2 a3 a4b a5b a6 a7).toNat / 10 ^ (n2 - 2)) ∧
      (∀ k, k < n2 → bs2 k = BitVec.ofNat 8
        (48 + (((0#64) - llArg a0 a1 a2 a3 a4b a5b a6 a7).toNat / 10 ^ (n2 - 1 - k)) % 10)) ∧
      -- return: PC = ra = the caller's return address, sp restored
      c'.σ.regs.get? Register.PC = some vra0 ∧
      c'.σ.regs.get? Register.x1 = some vra0 ∧
      c'.σ.regs.get? Register.x2 = some (vsp + (592#64)) ∧
      -- **a0 = the total: 1 sign byte + n2 digits**
      c'.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 (1 + n2)) ∧
      -- callee-saves restored to the entry values
      c'.σ.regs.get? Register.x8 = some vS0o ∧
      c'.σ.regs.get? Register.x9 = some vS1o ∧
      c'.σ.regs.get? Register.x18 = some vS2o ∧
      c'.σ.regs.get? Register.x19 = some vS3o ∧
      c'.σ.regs.get? Register.x20 = some vS4o ∧
      c'.σ.regs.get? Register.x21 = some vS5o ∧
      c'.σ.regs.get? Register.x22 = some vS6o ∧
      c'.σ.regs.get? Register.x23 = some vS7o ∧
      c'.σ.regs.get? Register.x24 = some vS8o ∧
      c'.σ.regs.get? Register.x25 = some vS9o ∧
      c'.σ.regs.get? Register.x26 = some vS10o ∧
      c'.σ.regs.get? Register.x27 = some vS11o ∧
      -- **the destination buffer: the '-' byte, then the n2 decimal digits**
      c'.σ.mem[d.toNat]? = some signByte ∧
      (∀ k, k < n2 → c'.σ.mem[d.toNat + 1 + k]? = some (bs2 k)) ∧
      -- FILE cursor/capacity updated
      Pin8 c'.σ.mem vfile.toNat (d + BitVec.ofNat 64 (1 + n2)) ∧
      Pin4 c'.σ.mem (vfile.toNat + 12)
        (cap32 - BitVec.ofNat 32 1 - BitVec.ofNat 32 n2) ∧
      -- pointwise frame back to the ABI-entry memory
      (∀ a : Nat, ¬(vsp.toNat - 88 ≤ a ∧ a < vsp.toNat + 592) →
        ¬(d.toNat ≤ a ∧ a < d.toNat + 1 + n2) →
        ¬(vfile.toNat ≤ a ∧ a < vfile.toNat + 8) →
        ¬(vfile.toNat + 12 ≤ a ∧ a < vfile.toNat + 16) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- ============ stage 1: entry → the __ssprint_r call (Spec37) ============
  obtain ⟨c1, hs1, n2, bs2, vsubw, hn2a, hn2b, hlead, hminD, hbs2f, hPre,
      h1x3, hfnslot1, hmb1, hfmtS1, hfmtN4, hnul1, hstr1, htot1, hs0201,
      h1e8c1, h1f0c1, h1f8c1, h200c1, h208c1, h210c1, h218c1, h220c1, h228c1, h230c1,
      h238c1, h240c1, h248c1, hfl0c1, hfl1c1, hagAll⟩ :=
    svfEntryToSsprintCall_spec vsp vra0 va0 vfile vfmt vva d
      vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o
      fl0 fl1 cap32 a0 a1 a2 a3 a4b a5b a6 a7 c hG
      hsl0 hsl20 hlc0 hstr0 hms0 hlm0 hamb0 hum0 hud0 hfp0 hap0 hslot0 hsspL0 hsspuL0 hmvL0
      hpc hx2 hx1 hx3 hx10 hx11 hx12 hx13 hx8 hx9 hx22 hx18 hx19 hx20 hx21 hx23 hx24
      hx25 hx26 hx27
      hdp0 hdp1 hdp2 hdp3 hdp4 hdp5 hdp6 hdp7
      hdb0 hdb1 hdb2 hdb3 hdb4 hdb5 hdb6 hdb7
      hfn0 hfn1 hfn2 hfn3 hfn4 hfn5 hfn6 hfn7 hmbB htb0 htb1 htb2 htb3
      hfmt0 hfmt1 hfmt2 hfmt3 hfmt4 hfl0B hfl1B hflagB
      hsinkcur hsinkcap hcap21 hcap31
      ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 hvlo hvhiram hvhtif hvalign hvdisj
      hneg
      hfilelo hfilehi hfileal hflo hfhi hfhtif (by omega) hsplo hsphi hspal
      hdge hdhi hdstk hfiled htick
  -- code pins at the call (all below 0x8001c000 ≤ vsp, outside the frame)
  have hagLow : ∀ a : Nat, a < 0x8001c000 → c1.σ.mem[a]? = c.σ.mem[a]? :=
    fun a ha => hagAll a (by omega)
  have hslice1 : SvfprintfSliceLoaded c1.σ.mem :=
    svfSlice_of_agree_rt (fun a h1 h2 => hagLow a (by omega)) hsl0
  have hfp1 : FlushPinsLoaded c1.σ.mem :=
    flushPins_of_agree_rt (fun a h1 h2 => hagLow a (by omega)) hfp0
  have hloc1 : __locale_mb_cur_maxLoaded c1.σ.mem :=
    locale_of_agree_rt (fun a h1 h2 => hagLow a (by omega)) hlm0
  have hamb1 : __ascii_mbtowcLoaded c1.σ.mem :=
    amb_of_agree_rt (fun a h1 h2 => hagLow a (by omega)) hamb0
  -- address bridges
  have hA224 : (vsp + sign_extend (m := 64) (0x0e0#12)).toNat = vsp.toNat + 224 :=
    ptr_addoff vsp _ 224 (by decide) (by omega)
  -- ============ stage 2: the flush + return path (Spec25) ============
  obtain ⟨c2, hs2, hG2, hpc2, hx1f, hx2f, hx10f, hx8f, hx9f, hx18f, hx19f, hx20f,
      hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hw1f, hw2f, hcurPf, hcapPf,
      hresPf, hcntPf, h180Pf, hframeF, htkF, hmiF⟩ :=
    svfprintf_flushReturn_spec (fun R => c1.σ.regs.get? R)
      (vsp + sign_extend (m := 64) (0x0e0#12))
      (vsp + sign_extend (m := 64) (0x160#12)) vfile d
      (vsp + sign_extend (m := 64) (0x0a7#12))
      (BitVec.ofNat 64 (vsp.toNat + 348 - n2)) vsp
      va0 (16#64) (37#64) vsubw (vsp + sign_extend (m := 64) (0x160#12)) va0
      (vfmt + sign_extend (m := 64) (0x004#12)) vra0 (BitVec.ofNat 64 (1 + n2))
      vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o
      fl0 fl1 1 n2 cap32 c1.σ.mem (fun _ => signByte) bs2 c1
      hPre hslice1 hfp1 hloc1 hamb1 h1x3 hfnslot1 hmb1
      hfmtS1 hstr1 htot1 hs0201
      h1e8c1 h1f0c1 h1f8c1 h200c1 h208c1 h210c1 h218c1 h220c1 h228c1 h230c1 h238c1
      h240c1 h248c1
      (by rw [hfmtN4]; exact hnul1) hfl0c1 hfl1c1 hflag40
      hA224 hsplo hsphi hspal (Or.inl hdge) (Or.inl (by omega))
      (by omega) (Or.inl hfilelo) (by omega)
      (by rw [hfmtN4]; omega) (by rw [hfmtN4]; omega) (by rw [hfmtN4]; omega)
      (by rw [hfmtN4]; omega) (by rw [hfmtN4]; omega)
      (by rw [hfmtN4]; simp only [tohostAddr] at hfhtif ⊢; omega)
      (by omega) hra0align
  -- ============ final assembly ============
  refine ⟨c2, hs1.trans hs2, hG2, n2, bs2, hn2a, hn2b, hlead, hminD, hbs2f,
    hpc2, hx1f, hx2f, hx10f, hx8f, hx9f, hx18f, hx19f, hx20f, hx21f, hx22f, hx23f,
    hx24f, hx25f, hx26f, hx27f, ?_, ?_, hcurPf, hcapPf, ?_, htkF, hmiF⟩
  · -- the sign byte at d
    have := hw1f 0 (by omega)
    simpa using this
  · -- the digits at d+1+k
    intro k hk
    have := hw2f k hk
    rwa [show d.toNat + 1 + k = d.toNat + 1 + k from rfl] at this
  · -- the pointwise frame back to the ABI-entry memory
    intro a hW1 hW2 hW3 hW4
    exact (hframeF a hW2 hW3 hW4 (by omega) (by omega) (by omega) (by omega)).trans
      (hagAll a (by omega))

end Vsa.Sim
