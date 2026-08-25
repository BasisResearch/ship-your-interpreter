#!/usr/bin/env python3
"""Generate the static-data image interface for the snprintf capstones (M6).

Emits TWO files (do not hand-edit either):

- `Vsa/Sim/Code/ImageStatics.lean` — one byte-pin predicate per static-data
  range (`imgLldFmt`, `imgDecPointStr`, …), the umbrella `ImageStaticsLoaded`
  conjunction, and per-range projection theorems.
- `Vsa/Sim/ImageDischarge.lean` — one lemma per static-image hypothesis
  appearing in the SnprintfSpec36–48 capstone statements, each deriving the
  hypothesis from `ImageStaticsLoaded mem` (raw byte pins `hdp*`/`hdb*`/
  `hfn*`/`hmbB`/`htb*`/`himp*`, plus the packaged forms `LldFmtLoaded`,
  `ParseSlotPinned 'd'`/`'l'`, and the locale-slot `SlotHolds`).

Every pinned byte is read out of `riscv64-elf-objdump -s c/while-riscv-htif.elf`
and cross-checked against the EXPECTED values recorded below (the bytes the
capstone hypotheses assume).  Any mismatch — image drift, bad range — aborts
without writing.

Usage: python3 scripts/gen_image_pins.py
       [--elf c/while-riscv-htif.elf] [--objdump riscv64-elf-objdump]
       [--dump FILE]   # pre-saved `objdump -s` output instead of running it
"""
import argparse
import pathlib
import re
import subprocess
import sys

# ---------------------------------------------------------------------------
# The inventoried static-data ranges (SnprintfSpec36-48 capstone hypotheses).
#
# fields: key, base, expected bytes, addr spelling ("abs" = one absolute
# literal per byte, matching Code/LldFmt.lean's lldFmtChunk0; "off" = the
# `(base : Nat) + k` spelling the capstone hypotheses use), hyp prefix (the
# capstone hypothesis family discharged from this range), description.
# ---------------------------------------------------------------------------
RANGES = [
    dict(key="lldFmt", base=0x800192C0,
         bytes=[0x25, 0x6C, 0x6C, 0x64, 0x00, 0x00, 0x00, 0x00],
         spell="abs", hyp="hfmtL0 (via LldFmtLoaded)",
         desc='the `"%lld\\0"` .rodata format string (= `Code/LldFmt.lean`\'s '
              "`lldFmtChunk0`; `stringify`'s int arm passes `a2 = 0x800192c0`)"),
    dict(key="decPointStr", base=0x80019770,
         bytes=[0x2E, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
         spell="off", hyp="hdb0..hdb7",
         desc='the locale decimal-point string `"."` the `_localeconv_r` '
              "result points at"),
    dict(key="parseSlotD", base=0x8001A20C,
         bytes=[0x0C, 0xDF, 0xFE, 0xFF],
         spell="off", hyp="hslot0 (via ParseSlotPinned 0x64)",
         desc="`svfprintf`'s conversion-table `'d'` slot "
              "(`parseTableBase 0x8001a0fc + 4*(0x64-32)`): offset "
              "`-0x120f4` -> handler `0x80008008`"),
    dict(key="parseSlotL", base=0x8001A22C,
         bytes=[0x38, 0xE4, 0xFE, 0xFF],
         spell="off", hyp="htb0..htb3",
         desc="`svfprintf`'s conversion-table `'l'` slot "
              "(`parseTableBase + 4*(0x6c-32)`): offset `-0x11bc8` -> handler "
              "`0x80008534`"),
    dict(key="fnSlot", base=0x8001B880,
         bytes=[0x68, 0x22, 0x01, 0x80, 0x00, 0x00, 0x00, 0x00],
         spell="off", hyp="hfn0..hfn7 (also SlotHolds 0x8001b798+0xe8)",
         desc="`__global_locale.mbtowc` fn-pointer slot = `0x80012268` "
              "(`__ascii_mbtowc`)"),
    dict(key="decPointPtr", base=0x8001B898,
         bytes=[0x70, 0x97, 0x01, 0x80, 0x00, 0x00, 0x00, 0x00],
         spell="off", hyp="hdp0..hdp7",
         desc="the `lconv.decimal_point` pointer slot = `0x80019770`"),
    dict(key="mbCurMax", base=0x8001B8F8,
         bytes=[0x01],
         spell="off", hyp="hmbB",
         desc="the `__global_locale` `__mb_cur_max` byte (`= 1`, C locale)"),
    dict(key="impurePtr", base=0x8001B970,
         bytes=[0x38, 0xB5, 0x01, 0x80, 0x00, 0x00, 0x00, 0x00],
         spell="off", hyp="himp0..himp7",
         desc="`_impure_ptr` = `0x8001b538` (`snprintf`'s reent load)"),
]

# per-byte discharge lemmas for ImageDischarge.lean:
#   (lemma suffix per byte index, range key)
BYTE_FAMILIES = [
    ("hdb", "decPointStr"),
    ("htb", "parseSlotL"),
    ("hfn", "fnSlot"),
    ("hdp", "decPointPtr"),
    ("hmbB", "mbCurMax"),
    ("himp", "impurePtr"),
]


def parse_objdump_s(text):
    """`objdump -s` hex dump -> {addr: byte}."""
    mem = {}
    line_re = re.compile(r"^ ([0-9a-f]{4,16}) ")
    for line in text.splitlines():
        m = line_re.match(line)
        if not m:
            continue
        addr = int(m.group(1), 16)
        data = line[m.end():m.end() + 36]  # 4 groups of 8 hex chars + spaces
        for g in range(4):
            chunk = data[g * 9:g * 9 + 8]
            for k in range(4):
                pair = chunk[2 * k:2 * k + 2] if len(chunk) >= 2 * k + 2 else ""
                if re.fullmatch(r"[0-9a-f]{2}", pair):
                    mem[addr + g * 4 + k] = int(pair, 16)
    return mem


def verify(mem):
    ok = True
    for r in RANGES:
        for i, expected in enumerate(r["bytes"]):
            a = r["base"] + i
            got = mem.get(a)
            if got != expected:
                print(f"MISMATCH {r['key']} @0x{a:x}: image has "
                      f"{'absent' if got is None else f'0x{got:02x}'}, "
                      f"expected 0x{expected:02x}", file=sys.stderr)
                ok = False
    if not ok:
        sys.exit("image bytes do not match the capstone hypotheses; aborting")


def addr_expr(r, i):
    if r["spell"] == "abs":
        return f"(0x{r['base'] + i:x} : Nat)"
    return f"(0x{r['base']:x} : Nat)" + (f" + {i}" if i else "")


def byte_expr(r, i):
    if r["spell"] == "abs":  # match Code/LldFmt.lean's spelling exactly
        return f"(0x{r['bytes'][i]:02x} : BitVec 8)"
    return f"(0x{r['bytes'][i]:02x}#8)"


def chunk_name(key):
    return "img" + key[0].upper() + key[1:]


def emit_image_statics():
    L = []
    L.append("import Vsa.Elf\n")
    L.append("/-!\n# Static-data image pins for the snprintf capstones "
             "(`ImageStaticsLoaded`)\n\n"
             "Generated by `scripts/gen_image_pins.py` from "
             "`riscv64-elf-objdump -s c/while-riscv-htif.elf` — do not "
             "hand-edit.\n\nOne byte-pin predicate per static-data range the "
             "SnprintfSpec36–48 capstone\nstatements assume, and the umbrella "
             "conjunction `ImageStaticsLoaded`.\nDischarge lemmas mapping "
             "these pins onto the exact capstone hypothesis shapes\nlive in "
             "`Vsa/Sim/ImageDischarge.lean`.\n\nRanges:\n")
    for r in RANGES:
        L.append(f"- `{chunk_name(r['key'])}` — "
                 f"[`0x{r['base']:x}`, `0x{r['base'] + len(r['bytes']):x}`) — "
                 f"{r['desc']}")
    L.append("-/\n")
    L.append("open Std (ExtHashMap)\n")
    L.append("namespace Vsa.Sim.Code\n")

    for r in RANGES:
        conj = " ∧\n  ".join(
            f"mem[{addr_expr(r, i)}]? = some {byte_expr(r, i)}"
            for i in range(len(r["bytes"])))
        L.append(f"/-- {len(r['bytes'])} byte(s) at `0x{r['base']:x}`: "
                 f"{r['desc']}. -/\ndef {chunk_name(r['key'])} "
                 f"(mem : ExtHashMap Nat (BitVec 8)) : Prop :=\n  {conj}\n")

    top = " ∧\n  ".join(f"{chunk_name(r['key'])} mem" for r in RANGES)
    L.append("/-- Every static-data range the SnprintfSpec36–48 capstones "
             "assume is loaded. -/\ndef ImageStaticsLoaded "
             f"(mem : ExtHashMap Nat (BitVec 8)) : Prop :=\n  {top}\n"
             .replace("{top}", top))

    n = len(RANGES)
    for ci, r in enumerate(RANGES):
        proj = "h" + ".2" * ci + (".1" if ci < n - 1 else "")
        L.append(f"theorem imageStatics_{r['key']}_range "
                 "{mem : ExtHashMap Nat (BitVec 8)}\n"
                 f"    (h : ImageStaticsLoaded mem) : "
                 f"{chunk_name(r['key'])} mem := {proj}\n")

    L.append("end Vsa.Sim.Code\n")
    return "\n".join(L)


def range_by_key(key):
    return next(r for r in RANGES if r["key"] == key)


def conj_proj(i, n):
    """i-th conjunct of a right-nested n-conjunction, applied to `h`."""
    if n == 1:
        return "h"
    return "h" + ".2" * i + (".1" if i < n - 1 else "")


def emit_image_discharge():
    inventory = [
        "| capstone hypothesis | static range | discharge lemma |",
        "| --- | --- | --- |",
        "| `hfmtL0 : LldFmtLoaded` (Spec42) | `0x800192c0`+8 | `imageStatics_lldFmt` |",
        "| `hdb0..hdb7` (Spec36-39,42) | `0x80019770`+8 | `imageStatics_hdb0..7` |",
        "| `hslot0 : ParseSlotPinned 0x64 …` (Spec37-39,42) | `0x8001a20c`+4 | `imageStatics_parseSlotD` |",
        "| `htb0..htb3` (Spec36-39,42) | `0x8001a22c`+4 | `imageStatics_htb0..3` (+ `imageStatics_parseSlotL`) |",
        "| `hfn0..hfn7` (Spec36-39,42) | `0x8001b880`+8 | `imageStatics_hfn0..7` (+ `imageStatics_fnslot`) |",
        "| `hdp0..hdp7` (Spec36-39,42) | `0x8001b898`+8 | `imageStatics_hdp0..7` |",
        "| `hmbB` (Spec36-39,42) | `0x8001b8f8`+1 | `imageStatics_hmbB` |",
        "| `himp0..himp7` (Spec40,42) | `0x8001b970`+8 | `imageStatics_himp0..7` |",
    ]
    L = []
    L.append("import Vsa.Sim.Code.ImageStatics\n"
             "import Vsa.Sim.Code.LldFmt\n"
             "import Vsa.Sim.SnprintfSpec5\n"
             "import Vsa.Sim.SnprintfSpec13\n")
    L.append("/-!\n# M6 — discharging the capstone static-image hypotheses "
             "from `ImageStaticsLoaded`\n\n"
             "Generated by `scripts/gen_image_pins.py` — do not hand-edit.\n\n"
             "One lemma per static-image hypothesis appearing in the "
             "SnprintfSpec36–48\ncapstone statements: a caller holding "
             "`Code.ImageStaticsLoaded c.σ.mem` (one\nELF-load fact) can "
             "instantiate every static hypothesis below instead of\ncarrying "
             "37 byte pins + 3 packaged predicates separately.\n\n"
             + "\n".join(inventory) + "\n\n"
             "(The code-region `*Loaded` hypotheses — `SnprintfLoaded`, "
             "`SvfprintfSliceLoaded`,\n`StrlenLoaded`, … — are *text*-segment "
             "pins with their own generated modules\nunder `Vsa/Sim/Code/`; "
             "this module covers the *data* statics only.)\n-/\n")
    L.append("open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail "
             "ConcurrencyInterfaceV1 Vsa\nopen Std (ExtHashMap)\n")
    L.append("namespace Vsa.Sim\n")

    # ---- per-byte discharge lemmas ----
    for fam, key in BYTE_FAMILIES:
        r = range_by_key(key)
        n = len(r["bytes"])
        for i in range(n):
            name = fam if n == 1 else f"{fam}{i}"
            L.append(f"/-- Capstone hypothesis `{name}` "
                     f"(byte `0x{r['base'] + i:x}` of {r['desc']}). -/\n"
                     f"theorem imageStatics_{name} "
                     "{m : ExtHashMap Nat (BitVec 8)}\n"
                     f"    (h : Code.ImageStaticsLoaded m) :\n"
                     f"    m[{addr_expr(r, i)}]? = some {byte_expr(r, i)} :=\n"
                     f"  (Code.imageStatics_{key}_range h)"
                     f"{conj_proj(i, n)[1:]}\n")

    # ---- packaged forms ----
    r = range_by_key("lldFmt")
    L.append("/-- Capstone hypothesis `hfmtL0` (Spec42): the `\"%lld\"` "
             "format-string pins. -/\n"
             "theorem imageStatics_lldFmt {m : ExtHashMap Nat (BitVec 8)}\n"
             "    (h : Code.ImageStaticsLoaded m) : Code.LldFmtLoaded m :=\n"
             "  Code.imageStatics_lldFmt_range h\n")

    r = range_by_key("parseSlotD")
    L.append("/-- Capstone hypothesis `hslot0` (Spec37/38/39/42): the "
             "conversion-table `'d'`\nslot dispatches to `0x80008008`. -/\n"
             "theorem imageStatics_parseSlotD {m : ExtHashMap Nat (BitVec 8)}\n"
             "    (h : Code.ImageStaticsLoaded m) :\n"
             "    ParseSlotPinned 0x64 (0x80008008#64) m := by\n"
             "  have hb := Code.imageStatics_parseSlotD_range h\n"
             "  exact parseSlot_d hb.1 hb.2.1 hb.2.2.1 hb.2.2.2\n")
    L.append("/-- The `'l'` slot packaged as `ParseSlotPinned` (the raw "
             "`htb0..3` shape is\ndischarged by `imageStatics_htb0..3`): "
             "dispatches to `0x80008534`. -/\n"
             "theorem imageStatics_parseSlotL {m : ExtHashMap Nat (BitVec 8)}\n"
             "    (h : Code.ImageStaticsLoaded m) :\n"
             "    ParseSlotPinned 0x6c (0x80008534#64) m := by\n"
             "  have hb := Code.imageStatics_parseSlotL_range h\n"
             "  exact parseSlot_l hb.1 hb.2.1 hb.2.2.1 hb.2.2.2\n")

    # SlotHolds packaging of the fnSlot range (Spec37's recipe verbatim).
    fn = range_by_key("fnSlot")
    slot_lines = []
    for i in range(8):
        slot_lines.append(
            f"  · rw [show (sdData_val (0x80012268#64)).extractLsb' {8 * i} 8"
            f" = ({byte_expr(fn, i).strip('()')} : BitVec 8) from by decide]\n"
            f"    exact hb{conj_proj(i, 8)[1:]}")
    L.append("/-- Capstone hypothesis `hfnslot` (Spec22/25/26 shape; Spec37's "
             "conclusion): the\nlocale `mbtowc` slot as a `SlotHolds` at "
             "`0x8001b798 + 0xe8`. -/\n"
             "theorem imageStatics_fnslot {m : ExtHashMap Nat (BitVec 8)}\n"
             "    (h : Code.ImageStaticsLoaded m) :\n"
             "    SlotHolds (0x8001b798#64) 0x0e8 (0x80012268#64) m := by\n"
             "  have hb := Code.imageStatics_fnSlot_range h\n"
             "  unfold SlotHolds\n"
             "  rw [show ((0x8001b798#64 : BitVec 64)\n"
             "      + sign_extend (m := 64) (BitVec.ofNat 12 0x0e8)).toNat "
             "= 0x8001b880 from by decide]\n"
             "  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩\n"
             + "\n".join(slot_lines) + "\n")

    L.append("end Vsa.Sim\n")
    return "\n".join(L)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--elf", default="c/while-riscv-htif.elf")
    ap.add_argument("--objdump", default="riscv64-elf-objdump")
    ap.add_argument("--dump", help="pre-saved `objdump -s` output")
    args = ap.parse_args()

    if args.dump:
        text = pathlib.Path(args.dump).read_text()
    else:
        text = subprocess.run([args.objdump, "-s", args.elf],
                              check=True, capture_output=True,
                              text=True).stdout
    mem = parse_objdump_s(text)
    verify(mem)

    p1 = pathlib.Path("Vsa/Sim/Code/ImageStatics.lean")
    p1.write_text(emit_image_statics())
    print(f"wrote {p1}")
    p2 = pathlib.Path("Vsa/Sim/ImageDischarge.lean")
    p2.write_text(emit_image_discharge())
    print(f"wrote {p2}")


if __name__ == "__main__":
    main()
