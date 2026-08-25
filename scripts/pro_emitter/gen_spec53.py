#!/usr/bin/env python3
"""Emit Vsa/Sim/SnprintfSpec53.lean — `svfprintf_lld_nn_spec`: the NONNEG
twin of SnprintfSpec38's `svfprintf_lld_spec`:

    svfEntryToSsprintCallNN_spec (Spec52) ≫ svfprintf_flushReturn1_spec (Spec51)

`a0 = n1` (the digit count), destination `[d, d+n1)` = the decimal digits of
the (nonneg) argument, NO sign byte.  Generated from Spec38's source.
"""
import pathlib

SRC = pathlib.Path("Vsa/Sim/SnprintfSpec38.lean").read_text()


def sub_must(text, old, new, name=""):
    if old not in text:
        raise SystemExit(f"MISSING [{name}]: {old[:100]!r}")
    return text.replace(old, new)


i = SRC.index("theorem svfprintf_lld_spec")
j = SRC.index("\nend Vsa.Sim")
thm = SRC[i:j]

thm = sub_must(thm, "theorem svfprintf_lld_spec", "theorem svfprintf_lld_nn_spec", name="nm")
# value ghost: negative → nonneg
thm = sub_must(thm,
    "    -- the argument-value ghosts: negative, magnitude > 9\n"
    "    (hneg : zopz0zKzJ_s (llArg a0 a1 a2 a3 a4b a5b a6 a7) (0#64) = false)",
    "    -- the argument-value ghost: NON-negative (any magnitude, incl. 0)\n"
    "    (hnn : zopz0zKzJ_s (llArg a0 a1 a2 a3 a4b a5b a6 a7) (0#64) = true)", name="ghost")
# post: existentials + magnitudes
thm = sub_must(thm,
    "    ∃ (n2 : Nat) (bs2 : Nat → BitVec 8),\n"
    "      1 ≤ n2 ∧ n2 ≤ 20 ∧\n"
    "      ((0#64) - llArg a0 a1 a2 a3 a4b a5b a6 a7).toNat / 10 ^ (n2 - 1) ≤ 9 ∧\n"
    "      (n2 = 1 ∨ 9 < ((0#64) - llArg a0 a1 a2 a3 a4b a5b a6 a7).toNat / 10 ^ (n2 - 2)) ∧\n"
    "      (∀ k, k < n2 → bs2 k = BitVec.ofNat 8\n"
    "        (48 + (((0#64) - llArg a0 a1 a2 a3 a4b a5b a6 a7).toNat / 10 ^ (n2 - 1 - k)) % 10)) ∧",
    "    ∃ (n1 : Nat) (bs1 : Nat → BitVec 8),\n"
    "      1 ≤ n1 ∧ n1 ≤ 20 ∧\n"
    "      (llArg a0 a1 a2 a3 a4b a5b a6 a7).toNat / 10 ^ (n1 - 1) ≤ 9 ∧\n"
    "      (n1 = 1 ∨ 9 < (llArg a0 a1 a2 a3 a4b a5b a6 a7).toNat / 10 ^ (n1 - 2)) ∧\n"
    "      (∀ k, k < n1 → bs1 k = BitVec.ofNat 8\n"
    "        (48 + ((llArg a0 a1 a2 a3 a4b a5b a6 a7).toNat / 10 ^ (n1 - 1 - k)) % 10)) ∧",
    name="post-ex")
thm = sub_must(thm,
    "      -- **a0 = the total: 1 sign byte + n2 digits**\n"
    "      c'.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 (1 + n2)) ∧",
    "      -- **a0 = the total: the n1 digits (no sign byte)**\n"
    "      c'.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 n1) ∧", name="post-a0")
thm = sub_must(thm,
    "      -- **the destination buffer: the '-' byte, then the n2 decimal digits**\n"
    "      c'.σ.mem[d.toNat]? = some signByte ∧\n"
    "      (∀ k, k < n2 → c'.σ.mem[d.toNat + 1 + k]? = some (bs2 k)) ∧",
    "      -- **the destination buffer: the n1 decimal digits**\n"
    "      (∀ k, k < n1 → c'.σ.mem[d.toNat + k]? = some (bs1 k)) ∧",
    name="post-buf")
thm = sub_must(thm,
    "      Pin8 c'.σ.mem vfile.toNat (d + BitVec.ofNat 64 (1 + n2)) ∧\n"
    "      Pin4 c'.σ.mem (vfile.toNat + 12)\n"
    "        (cap32 - BitVec.ofNat 32 1 - BitVec.ofNat 32 n2) ∧",
    "      Pin8 c'.σ.mem vfile.toNat (d + BitVec.ofNat 64 n1) ∧\n"
    "      Pin4 c'.σ.mem (vfile.toNat + 12) (cap32 - BitVec.ofNat 32 n1) ∧",
    name="post-file")
thm = sub_must(thm, "¬(d.toNat ≤ a ∧ a < d.toNat + 1 + n2) →",
               "¬(d.toNat ≤ a ∧ a < d.toNat + n1) →", name="post-frame")
# stage 1: Spec52
thm = sub_must(thm,
    "  obtain ⟨c1, hs1, n2, bs2, vsubw, hn2a, hn2b, hlead, hminD, hbs2f, hPre,",
    "  obtain ⟨c1, hs1, n1, bs1, vsubw, hn1a, hn1b, hlead, hminD, hbs1f, hPre,",
    name="st1-obtain")
thm = sub_must(thm, "    svfEntryToSsprintCall_spec vsp vra0",
               "    svfEntryToSsprintCallNN_spec vsp vra0", name="st1-call")
thm = sub_must(thm, "      hneg\n", "      hnn\n", name="st1-ghost")
# stage 2: Spec51
thm = sub_must(thm,
    "  obtain ⟨c2, hs2, hG2, hpc2, hx1f, hx2f, hx10f, hx8f, hx9f, hx18f, hx19f, hx20f,\n"
    "      hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hw1f, hw2f, hcurPf, hcapPf,\n"
    "      hresPf, hcntPf, h180Pf, hframeF, htkF, hmiF⟩ :=\n"
    "    svfprintf_flushReturn_spec (fun R => c1.σ.regs.get? R)",
    "  obtain ⟨c2, hs2, hG2, hpc2, hx1f, hx2f, hx10f, hx8f, hx9f, hx18f, hx19f, hx20f,\n"
    "      hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hw1f, hcurPf, hcapPf,\n"
    "      hresPf, hcntPf, h180Pf, hframeF, htkF, hmiF⟩ :=\n"
    "    svfprintf_flushReturn1_spec (fun R => c1.σ.regs.get? R)",
    name="st2-call")
thm = sub_must(thm,
    "      (vsp + sign_extend (m := 64) (0x160#12)) vfile d\n"
    "      (vsp + sign_extend (m := 64) (0x0a7#12))\n"
    "      (BitVec.ofNat 64 (vsp.toNat + 348 - n2)) vsp\n"
    "      va0 (16#64) (37#64) vsubw (vsp + sign_extend (m := 64) (0x160#12)) va0\n"
    "      (vfmt + sign_extend (m := 64) (0x004#12)) vra0 (BitVec.ofNat 64 (1 + n2))\n"
    "      vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o\n"
    "      fl0 fl1 1 n2 cap32 c1.σ.mem (fun _ => signByte) bs2 c1",
    "      (vsp + sign_extend (m := 64) (0x160#12)) vfile d\n"
    "      (BitVec.ofNat 64 (vsp.toNat + 348 - n1)) vsp\n"
    "      va0 (16#64) (37#64) vsubw (vsp + sign_extend (m := 64) (0x160#12)) va0\n"
    "      (vfmt + sign_extend (m := 64) (0x004#12)) vra0 (BitVec.ofNat 64 n1)\n"
    "      vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o\n"
    "      fl0 fl1 n1 cap32 c1.σ.mem bs1 c1",
    name="st2-args")
# final assembly
thm = sub_must(thm,
    "  refine ⟨c2, hs1.trans hs2, hG2, n2, bs2, hn2a, hn2b, hlead, hminD, hbs2f,\n"
    "    hpc2, hx1f, hx2f, hx10f, hx8f, hx9f, hx18f, hx19f, hx20f, hx21f, hx22f, hx23f,\n"
    "    hx24f, hx25f, hx26f, hx27f, ?_, ?_, hcurPf, hcapPf, ?_, htkF, hmiF⟩\n"
    "  · -- the sign byte at d\n"
    "    have := hw1f 0 (by omega)\n"
    "    simpa using this\n"
    "  · -- the digits at d+1+k\n"
    "    intro k hk\n"
    "    have := hw2f k hk\n"
    "    rwa [show d.toNat + 1 + k = d.toNat + 1 + k from rfl] at this\n"
    "  · -- the pointwise frame back to the ABI-entry memory",
    "  refine ⟨c2, hs1.trans hs2, hG2, n1, bs1, hn1a, hn1b, hlead, hminD, hbs1f,\n"
    "    hpc2, hx1f, hx2f, hx10f, hx8f, hx9f, hx18f, hx19f, hx20f, hx21f, hx22f, hx23f,\n"
    "    hx24f, hx25f, hx26f, hx27f, hw1f, hcurPf, hcapPf, ?_, htkF, hmiF⟩\n"
    "  · -- the pointwise frame back to the ABI-entry memory",
    name="assembly")

HDR = """import Vsa.Sim.SnprintfSpec52
import Vsa.Sim.SnprintfSpec51

/-!
# M3 Layer-3 — `SnprintfSpec53` : the FULL svfprintf `%lld` spec, NONNEG arm
## `0x80007654` (`_svfprintf_r` ABI entry) → svfprintf's `ret`, `a0 = n1`

The NONNEG twin of `svfprintf_lld_spec` (SnprintfSpec38): one `Steps` chain

    svfEntryToSsprintCallNN_spec (Spec52 : `PreSr1` assembled)
  ≫ svfprintf_flushReturn1_spec  (Spec51 : the 1-iovec flush + return path)

with `a0 = ofNat n1` (the digit count), the destination `[d, d+n1)` = the
decimal digits of the (nonneg) argument, cursor `+ n1`, capacity `− n1`, and
a pointwise frame outside `[vsp−88, vsp+592) ∪ [d, d+n1)` ∪ the two written
FILE fields.  Residuals wrapper-owned only, exactly as Spec38's.

Generated from SnprintfSpec38's source by
`scripts/pro_emitter/gen_spec53.py` (do not hand-edit; regenerate).
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

/-- **The full svfprintf `%lld` spec, NONNEG arm** — `_svfprintf_r` ABI entry
to `ret`: `a0 = n1`, destination = the decimal digits (no sign byte). -/
"""

out = HDR + thm + "\nend Vsa.Sim\n"
p = pathlib.Path("Vsa/Sim/SnprintfSpec53.lean")
p.write_text(out)
print(f"wrote {p} ({out.count(chr(10))} lines)")
