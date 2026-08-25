#!/usr/bin/env python3
"""Emit Vsa/Sim/SnprintfSpec51.lean — `svfprintf_flushReturn1_spec`: the
1-iovec twin of SnprintfSpec25's `svfprintf_flushReturn_spec`.

`ssprint_iov1_spec` (SnprintfSpec50) ≫ retA/B/C/D (SnprintfSpec21-24,
reused VERBATIM via the Spec25 import).  Transform: drop the s2/n2/bs2
ghosts, the second-iovec window and the second capacity decrement;
`PreSr → PreSr1`, `ssprint_iov2_spec → ssprint_iov1_spec`.
"""
import pathlib

SRC = pathlib.Path("Vsa/Sim/SnprintfSpec25.lean").read_text()


def sub_must(text, old, new, name=""):
    if old not in text:
        raise SystemExit(f"MISSING [{name}]: {old[:100]!r}")
    return text.replace(old, new)


i = SRC.index("/-- **The svfprintf flush return path, end to end.**")
j = SRC.index("\nend Vsa.Sim")
thm = SRC[i:j]

thm = sub_must(thm, "theorem svfprintf_flushReturn_spec",
               "theorem svfprintf_flushReturn1_spec", name="name")
thm = sub_must(thm, "(q viov p d s1 s2 vsp v8 v18 v19 v20 v21 va0 : BitVec 64)",
               "(q viov p d s1 vsp v8 v18 v19 v20 v21 va0 : BitVec 64)", name="params")
thm = sub_must(thm, "(n1 n2 : Nat)", "(n1 : Nat)", name="n-params")
thm = sub_must(thm, "(bs1 bs2 : Nat → BitVec 8)", "(bs1 : Nat → BitVec 8)", name="bs-params")
thm = sub_must(thm,
    "hPre : PreSr g (0x80008688#64) q viov p d s1 s2 vsp v8 (0x8001b798#64) v18 v19 v20 v21\n"
    "      va0 n1 n2 cap32 m0 bs1 bs2 c",
    "hPre : PreSr1 g (0x80008688#64) q viov p d s1 vsp v8 (0x8001b798#64) v18 v19 v20 v21\n"
    "      va0 n1 cap32 m0 bs1 c", name="pre")
thm = thm.replace("n1 + n2", "n1")
thm = sub_must(thm,
    "    ssprint_iov2_spec g (0x80008688#64) q viov p d s1 s2 vsp v8 (0x8001b798#64) v18 v19 v20\n"
    "      v21 va0 n1 n2 cap32 m0 bs1 bs2 (by decide) c hPre",
    "    ssprint_iov1_spec g (0x80008688#64) q viov p d s1 vsp v8 (0x8001b798#64) v18 v19 v20\n"
    "      v21 va0 n1 cap32 m0 bs1 (by decide) c hPre", name="iov1")
thm = sub_must(thm, "hcp1, hcp2, hcurspin", "hcp1, hcurspin", name="destructure")
# post: drop the digits-window conjunct (after sum transform the two windows collapsed)
thm = sub_must(thm,
    "      (∀ k, k < n2 → c'.σ.mem[(d.toNat + n1 + k)]? = some (bs2 k)) ∧\n", "",
    name="post-cp2")
thm = sub_must(thm, "cap32 - BitVec.ofNat 32 n1 - BitVec.ofNat 32 n2",
               "cap32 - BitVec.ofNat 32 n1", name="post-cap")
thm = sub_must(thm, "have hn131 := hreg.n1_31; have hn231 := hreg.n2_31",
               "have hn131 := hreg.n1_31", name="n2bind")
thm = sub_must(thm, "hx25_5, hx26_5, hx27_5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htick5, hmi5⟩",
               "hx25_5, hx26_5, hx27_5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htick5, hmi5⟩",
               name="refine")
BULLET2 = """  · -- the second iovec (digits) window
    intro k hk
    rw [hmemF, getElem?_writeMap4_out _ _ _ _ (by omega),
      getElem?_writeMap4_out _ _ _ _ (by omega)]
    exact hcp2 k hk
"""
thm = sub_must(thm, BULLET2, "", name="bullet2")

HDR = """import Vsa.Sim.SnprintfSpec50
import Vsa.Sim.SnprintfSpec25

/-!
# M3 Layer-3 — `SnprintfSpec51` : the 1-iovec svfprintf **flush return path**

`svfprintf_flushReturn1_spec` — the 1-iovec (nonneg `%lld`) twin of
`svfprintf_flushReturn_spec` (SnprintfSpec25): `ssprint_iov1_spec`
(SnprintfSpec50) ≫ `retA/B/C/D` (SnprintfSpec21-24, reused verbatim).
From the completed `jal __ssprint_r` (`PreSr1` with `r := 0x80008688`,
single digit iovec `(s1, n1, bs1)`, count 1, resid `n1`) to svfprintf's
`ret` with `a0 = vtot`.

Generated from SnprintfSpec25's source by
`scripts/pro_emitter/gen_spec51.py` (do not hand-edit; regenerate).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded FlushPinsLoaded __locale_mb_cur_maxLoaded
  __ascii_mbtowcLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

"""

out = HDR + thm + "\nend Vsa.Sim\n"
p = pathlib.Path("Vsa/Sim/SnprintfSpec51.lean")
p.write_text(out)
print(f"wrote {p} ({out.count(chr(10))} lines)")
