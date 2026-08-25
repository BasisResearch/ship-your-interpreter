#!/usr/bin/env python3
"""Emit Vsa/Sim/SnprintfSpec54.lean — `snprintf_lld_nn_spec`: the NONNEG twin
of SnprintfSpec42's `snprintf_lld_spec` (same conclusion, `hnn` instead of
`hneg`):

    snprintfPreCall_spec (Spec40) ≫ svfprintf_lld_nn_spec (Spec53)
      ≫ snprintfPostCall_spec (Spec41)

restated byte-for-byte through the new `svfprintf_buffer_eq_intToString_nn`
(`intToString_nonneg` + `natToString_toUTF8_toList_39`).  Generated from
Spec42's source.
"""
import pathlib

SRC = pathlib.Path("Vsa/Sim/SnprintfSpec42.lean").read_text()


def sub_must(text, old, new, name=""):
    if old not in text:
        raise SystemExit(f"MISSING [{name}]: {old[:100]!r}")
    return text.replace(old, new)


i = SRC.index("theorem snprintf_lld_spec")
j = SRC.index("\nend Vsa.Sim")
thm = SRC[i:j]

thm = sub_must(thm, "theorem snprintf_lld_spec", "theorem snprintf_lld_nn_spec", name="nm")
thm = sub_must(thm,
    "    -- the argument-value ghosts: negative, magnitude > 9\n"
    "    (hneg : zopz0zKzJ_s v (0#64) = false)",
    "    -- the argument-value ghost: NON-negative (any magnitude, incl. 0)\n"
    "    (hnn : zopz0zKzJ_s v (0#64) = true)", name="ghost")
# stage 2: Spec53
thm = sub_must(thm,
    "  obtain ⟨c2, hs2, hG2, n2, bs2, hn2a, hn2b, hub, hlb, hbs2f,\n"
    "      hpc2, h2x1, h2x2, h2x10, h2x8, h2x9, h2x18, h2x19, h2x20, h2x21, h2x22, h2x23,\n"
    "      h2x24, h2x25, h2x26, h2x27, hsignB, hdigB, hcurP, hcapP, hframe2, htk2, hmi2⟩ :=\n"
    "    svfprintf_lld_spec vsp",
    "  obtain ⟨c2, hs2, hG2, n1, bs1, hn1a, hn1b, hub, hlb, hbs1f,\n"
    "      hpc2, h2x1, h2x2, h2x10, h2x8, h2x9, h2x18, h2x19, h2x20, h2x21, h2x22, h2x23,\n"
    "      h2x24, h2x25, h2x26, h2x27, hdigB, hcurP, hcapP, hframe2, htk2, hmi2⟩ :=\n"
    "    svfprintf_lld_nn_spec vsp",
    name="st2")
thm = sub_must(thm, "      (by rw [hllv]; exact hneg)", "      (by rw [hllv]; exact hnn)",
               name="st2-ghost")
thm = sub_must(thm, "  rw [hllv] at hub hlb hbs2f", "  rw [hllv] at hub hlb hbs1f",
               name="rwllv")
# stage 3: cursor d + ofNat n1, a0 = ofNat n1
thm = sub_must(thm,
    "  have hvcN : (d + BitVec.ofNat 64 (1 + n2)).toNat = d.toNat + 1 + n2 := by",
    "  have hvcN : (d + BitVec.ofNat 64 n1).toNat = d.toNat + n1 := by", name="hvcN")
thm = sub_must(thm,
    "    snprintfPostCall_spec vsp wra0 (d + BitVec.ofNat 64 (1 + n2)) sz\n"
    "      (BitVec.ofNat 64 (1 + n2))",
    "    snprintfPostCall_spec vsp wra0 (d + BitVec.ofNat 64 n1) sz\n"
    "      (BitVec.ofNat 64 n1)", name="st3")
# final assembly: nonneg byte bridge
OLD_ASM = """  -- ============ final assembly: byte-for-byte intToString ============
  have hbytes : signByte :: (List.range n2).map bs2
      = (intToString v.toInt).toUTF8.data.toList.map (fun u => u.toBitVec) :=
    svfprintf_buffer_eq_intToString v n2 bs2 hneg hn2a hbs2f hub hlb
  have hlen : (intToString v.toInt).toUTF8.data.toList.length = 1 + n2 := by
    have h := congrArg List.length hbytes
    rw [List.length_cons, List.length_map, List.length_range, List.length_map] at h
    omega
  -- reads at c3 away from the NUL byte fall through to c2
  have hins : ∀ a : Nat, a ≠ d.toNat + 1 + n2 → c3.σ.mem[a]? = c2.σ.mem[a]? := by
    intro a hne
    rw [hmem3, Std.ExtHashMap.getElem?_insert,
      if_neg (by simp only [beq_iff_eq]; rw [hvcN]; exact fun h => hne h.symm)]
  -- the NUL byte itself
  have hnulB : c3.σ.mem[d.toNat + (1 + n2)]? = some (0x00#8) := by
    rw [show d.toNat + (1 + n2) = d.toNat + 1 + n2 from by omega]
    rw [hmem3, Std.ExtHashMap.getElem?_insert,
      if_pos (by simp only [beq_iff_eq]; rw [hvcN]),
      show stData 1 (0#64) = (0x00#8) from by decide]
  refine ⟨c3, (hs1.trans hs2).trans hs3, hG3,
    (intToString v.toInt).toUTF8.data.toList, rfl,
    hpc3, h3x1, h3x2, (by rw [hlen]; exact h3x10),
    h3x8, h3x9, h3x18, h3x19, h3x20, h3x21, h3x22, h3x23, h3x24, h3x25, h3x26, h3x27,
    ?_, (by rw [hlen]; exact hnulB), ?_, htk3, hmi3⟩
  · -- byte-for-byte in the caller buffer
    intro k hk
    have hk' : k < 1 + n2 := by rwa [hlen] at hk
    have hget : (intToString v.toInt).toUTF8.data.toList[k].toBitVec
        = (signByte :: (List.range n2).map bs2)[k]'(by
            rw [List.length_cons, List.length_map, List.length_range]; omega) := by
      have hmapg : ((intToString v.toInt).toUTF8.data.toList.map
          (fun u => u.toBitVec))[k]'(by rw [List.length_map, hlen]; omega)
          = (intToString v.toInt).toUTF8.data.toList[k].toBitVec :=
        List.getElem_map _
      rw [← hmapg]
      exact List.getElem_of_eq hbytes.symm _
    rw [hget]
    cases k with
    | zero =>
      rw [hins _ (by omega)]
      simpa using hsignB
    | succ j =>
      have hj : j < n2 := by omega
      have hcons : (signByte :: (List.range n2).map bs2)[j + 1]'(by simp; omega)
          = bs2 j := by
        simp [List.getElem_map, List.getElem_range]
      rw [hcons, show d.toNat + (j + 1) = d.toNat + 1 + j from by omega,
        hins _ (by omega)]
      exact hdigB j hj
  · -- the pointwise frame back to the ABI-entry memory
    intro a hW1 hW2
    rw [hlen] at hW2
    rw [hins a (by omega)]
    exact ((hframe2 a (by omega) (by omega) (by rw [hoff600]; omega)
        (by rw [hoff600]; omega)).trans (hag1 a (by omega)))"""
NEW_ASM = """  -- ============ final assembly: byte-for-byte intToString (nonneg) ============
  have hbytes : (List.range n1).map bs1
      = (intToString v.toInt).toUTF8.data.toList.map (fun u => u.toBitVec) :=
    svfprintf_buffer_eq_intToString_nn v n1 bs1 hnn hn1a hbs1f hub hlb
  have hlen : (intToString v.toInt).toUTF8.data.toList.length = n1 := by
    have h := congrArg List.length hbytes
    rw [List.length_map, List.length_range, List.length_map] at h
    omega
  -- reads at c3 away from the NUL byte fall through to c2
  have hins : ∀ a : Nat, a ≠ d.toNat + n1 → c3.σ.mem[a]? = c2.σ.mem[a]? := by
    intro a hne
    rw [hmem3, Std.ExtHashMap.getElem?_insert,
      if_neg (by simp only [beq_iff_eq]; rw [hvcN]; exact fun h => hne h.symm)]
  -- the NUL byte itself
  have hnulB : c3.σ.mem[d.toNat + n1]? = some (0x00#8) := by
    rw [hmem3, Std.ExtHashMap.getElem?_insert,
      if_pos (by simp only [beq_iff_eq]; rw [hvcN]),
      show stData 1 (0#64) = (0x00#8) from by decide]
  refine ⟨c3, (hs1.trans hs2).trans hs3, hG3,
    (intToString v.toInt).toUTF8.data.toList, rfl,
    hpc3, h3x1, h3x2, (by rw [hlen]; exact h3x10),
    h3x8, h3x9, h3x18, h3x19, h3x20, h3x21, h3x22, h3x23, h3x24, h3x25, h3x26, h3x27,
    ?_, (by rw [hlen]; exact hnulB), ?_, htk3, hmi3⟩
  · -- byte-for-byte in the caller buffer
    intro k hk
    have hk' : k < n1 := by rwa [hlen] at hk
    have hget : (intToString v.toInt).toUTF8.data.toList[k].toBitVec
        = ((List.range n1).map bs1)[k]'(by
            rw [List.length_map, List.length_range]; omega) := by
      have hmapg : ((intToString v.toInt).toUTF8.data.toList.map
          (fun u => u.toBitVec))[k]'(by rw [List.length_map, hlen]; omega)
          = (intToString v.toInt).toUTF8.data.toList[k].toBitVec :=
        List.getElem_map _
      rw [← hmapg]
      exact List.getElem_of_eq hbytes.symm _
    rw [hget]
    have hidx : ((List.range n1).map bs1)[k]'(by
        rw [List.length_map, List.length_range]; omega) = bs1 k := by
      simp [List.getElem_map, List.getElem_range]
    rw [hidx, hins _ (by omega)]
    exact hdigB k hk'
  · -- the pointwise frame back to the ABI-entry memory
    intro a hW1 hW2
    rw [hlen] at hW2
    rw [hins a (by omega)]
    exact ((hframe2 a (by omega) (by omega) (by rw [hoff600]; omega)
        (by rw [hoff600]; omega)).trans (hag1 a (by omega)))"""
thm = sub_must(thm, OLD_ASM, NEW_ASM, name="assembly")

HDR = """import Vsa.Sim.SnprintfSpec39
import Vsa.Sim.SnprintfSpec41
import Vsa.Sim.SnprintfSpec53

/-!
# M3 Layer-3 — `SnprintfSpec54` : the `snprintf("%lld")` wrapper, NONNEG arm

`snprintf_lld_nn_spec` — the NONNEG twin of `snprintf_lld_spec` (Spec42),
with the IDENTICAL conclusion (`∃ ubytes = (intToString v.toInt).toUTF8`
bytes, `a0 = length`, buffer + NUL, frame): `snprintfPreCall_spec` (Spec40)
≫ `svfprintf_lld_nn_spec` (Spec53) ≫ `snprintfPostCall_spec` (Spec41),
bridged by the new `svfprintf_buffer_eq_intToString_nn`
(`intToString_nonneg` + `natToString_toUTF8_toList_39` — `v = 0` included:
its machine arm renders the single digit `'0'`).

Generated from SnprintfSpec42's source by
`scripts/pro_emitter/gen_spec54.py` (do not hand-edit; regenerate).
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

/-- **The machine-facing byte-for-byte verdict, NONNEG arm**: the flushed
digit list `[bs1 0, …, bs1 (n1−1)]` *is* `(intToString v.toInt).toUTF8`
(as `BitVec 8` bytes) — no sign byte. -/
theorem svfprintf_buffer_eq_intToString_nn (v : BitVec 64) (n1 : Nat) (bs1 : Nat → BitVec 8)
    (hnn : zopz0zKzJ_s v (0#64) = true)
    (h1 : 1 ≤ n1)
    (hbs : ∀ k, k < n1 → bs1 k = BitVec.ofNat 8
      (48 + (v.toNat / 10 ^ (n1 - 1 - k)) % 10))
    (hub : v.toNat / 10 ^ (n1 - 1) ≤ 9)
    (hlb : n1 = 1 ∨ 9 < v.toNat / 10 ^ (n1 - 2)) :
    (List.range n1).map bs1
      = (intToString v.toInt).toUTF8.data.toList.map (fun u => u.toBitVec) := by
  rw [intToString_nonneg v (bgez_true' v hnn),
    natToString_toUTF8_toList_39 v.toNat n1 h1 hub hlb, List.map_map]
  exact List.map_congr_left (fun k hk => by
    rw [hbs k (List.mem_range.mp hk)]; rfl)

/-- **The `snprintf("%lld")` wrapper capstone, NONNEG arm** — snprintf ABI
entry to `ret`, any nonneg argument: the caller buffer holds
`(intToString v.toInt).toUTF8 ++ [0]`, `a0` = the byte length. -/
"""

out = HDR + thm + "\nend Vsa.Sim\n"
p = pathlib.Path("Vsa/Sim/SnprintfSpec54.lean")
p.write_text(out)
print(f"wrote {p} ({out.count(chr(10))} lines)")
