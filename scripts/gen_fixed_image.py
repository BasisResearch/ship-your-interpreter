#!/usr/bin/env python3
"""Generate fixed ELF section data and kernel-checkable Code projections.

The default destination is Vsa/Sim/Code. Use --output to stage an integration;
--check verifies reproducibility without writing. This tool never invokes Lean.
The fixed-image manifest records generation; kernel verification is recorded
separately in the Lean build manifest.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import struct

ELF_SHA256 = "b146c6edb76ea9a0f0f30be381f8176ed2de9717e1ae9b37feff4b2b9ca1d0f0"
SECTIONS = {".text": (0x80000000, 101344, 6), ".rodata": (0x80018BE0, 8464, 2)}
PAGE_SIZE = 256
ROOT = Path(__file__).resolve().parents[1]
BYTE_PIN = re.compile(
    r"mem\[\(0x([0-9a-f]+) : Nat\)\]\? = some \(0x([0-9a-f]+) : BitVec 8\)"
)


def sections_from_elf(raw: bytes) -> dict[str, tuple[int, bytes]]:
    if hashlib.sha256(raw).hexdigest() != ELF_SHA256:
        raise ValueError("ELF differs from the approved fixed image")
    if raw[:7] != b"\x7fELF\x02\x01\x01":
        raise ValueError("expected ELF64 little-endian version 1")
    if struct.unpack_from("<H", raw, 18)[0] != 243:
        raise ValueError("expected RISC-V ELF")
    offset = struct.unpack_from("<Q", raw, 40)[0]
    width, count, strings_index = struct.unpack_from("<HHH", raw, 58)
    if (
        width != 64
        or not 0 < strings_index < count
        or offset + count * width > len(raw)
    ):
        raise ValueError("invalid section table")
    headers = [
        struct.unpack_from("<IIQQQQIIQQ", raw, offset + i * width) for i in range(count)
    ]
    strings_header = headers[strings_index]
    start, length = strings_header[4:6]
    names = raw[start : start + length]
    result = {}
    for header in headers:
        name_index, kind, flags, address, start, length = header[:6]
        end = names.find(b"\x00", name_index)
        if end < 0:
            raise ValueError("unterminated section name")
        name = names[name_index:end].decode("ascii")
        if name not in SECTIONS:
            continue
        if name in result or kind != 1 or (address, length, flags) != SECTIONS[name]:
            raise ValueError(f"unexpected section descriptor: {name}")
        if start + length > len(raw):
            raise ValueError(f"truncated section: {name}")
        result[name] = address, raw[start : start + length]
    if set(result) != set(SECTIONS):
        raise ValueError("fixed image sections missing")
    return result


def balanced_page_lookup(names: list[str], lo: int = 0) -> str:
    if len(names) == 1:
        return names[0]
    middle = len(names) // 2
    return (
        f"(if page < {lo + middle} then "
        f"{balanced_page_lookup(names[:middle], lo)} else "
        f"{balanced_page_lookup(names[middle:], lo + middle)})"
    )


def generate_data(sections: dict[str, tuple[int, bytes]]) -> str:
    lines = [
        "import Vsa.Elf",
        "",
        "namespace Vsa.Sim.Code",
        "",
        f"-- Generated from fixed ELF SHA256 {ELF_SHA256}.",
        "-- Packed data only; no memory assumptions or execution claims.",
        "",
    ]
    for section, (base, data) in sections.items():
        stem = "fixed" + section[1:].capitalize()
        names = []
        for number, start in enumerate(range(0, len(data), PAGE_SIZE)):
            name = f"{stem}Page{number}"
            names.append(name)
            packed = int.from_bytes(data[start : start + PAGE_SIZE], "little")
            lines.append(f"private def {name} : Nat := 0x{packed:x}")
        lines += [
            "",
            f"private def {stem}Page (page : Nat) : Nat :=",
            f"  if page < {len(names)} then {balanced_page_lookup(names)} else 0",
            "",
            f"def {stem}Byte (offset : Nat) : BitVec 8 :=",
            f"  BitVec.ofNat 8 (Nat.shiftRight ({stem}Page (offset / {PAGE_SIZE}))",
            f"    (8 * (offset % {PAGE_SIZE})))",
            "",
            f"def {stem}Base : Nat := 0x{base:x}",
            f"def {stem}Size : Nat := {len(data)}",
            "",
        ]
    return "\n".join(lines + ["end Vsa.Sim.Code", ""])


def generate_interface() -> str:
    return """import Vsa.Sim.Code.FixedImageData

open Std (ExtHashMap)

namespace Vsa.Sim.Code

/-- Byte equality on a bounded interval. Nothing is asserted outside it. -/
def FixedBytesLoaded (base size : Nat) (byte : Nat → BitVec 8)
    (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ offset, offset < size → mem[base + offset]? = some (byte offset)

/-- Exact .text bytes of the approved interpreter ELF. -/
def FixedTextLoaded (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  FixedBytesLoaded fixedTextBase fixedTextSize fixedTextByte mem

/-- Exact .rodata bytes; mutable .data/BSS are deliberately separate. -/
def FixedRodataLoaded (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  FixedBytesLoaded fixedRodataBase fixedRodataSize fixedRodataByte mem

theorem FixedBytesLoaded.transport
    {base size : Nat} {byte : Nat → BitVec 8}
    {mem mem' : ExtHashMap Nat (BitVec 8)}
    (h : FixedBytesLoaded base size byte mem)
    (hag : ∀ a, base ≤ a → a < base + size → mem'[a]? = mem[a]?) :
    FixedBytesLoaded base size byte mem' := by
  intro offset hoff
  exact (hag (base + offset) (Nat.le_add_right _ _)
    (Nat.add_lt_add_left hoff base)).trans (h offset hoff)

theorem FixedTextLoaded.transport
    {mem mem' : ExtHashMap Nat (BitVec 8)} (h : FixedTextLoaded mem)
    (hag : ∀ a, 0x80000000 ≤ a → a < 0x80018be0 → mem'[a]? = mem[a]?) :
    FixedTextLoaded mem' :=
  FixedBytesLoaded.transport h hag

theorem FixedRodataLoaded.transport
    {mem mem' : ExtHashMap Nat (BitVec 8)} (h : FixedRodataLoaded mem)
    (hag : ∀ a, 0x80018be0 ≤ a → a < 0x8001acf0 → mem'[a]? = mem[a]?) :
    FixedRodataLoaded mem' :=
  FixedBytesLoaded.transport h hag

#print axioms FixedBytesLoaded.transport
#print axioms FixedTextLoaded.transport
#print axioms FixedRodataLoaded.transport

end Vsa.Sim.Code
"""


def projection_module(
    repo: Path, module: str, image: dict[int, int]
) -> tuple[str, int]:
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", module) is None:
        raise ValueError(f"invalid Code module name: {module}")
    source = (repo / "Vsa/Sim/Code" / f"{module}.lean").read_text()
    chunks = re.findall(
        r"^def (\w+Chunk\d+) \(mem[^\n]*\) : Prop :=\n(.*?)(?=\n\n)",
        source,
        re.MULTILINE | re.DOTALL,
    )
    if not chunks:
        raise ValueError(f"no supported byte chunks: {module}")
    loaded = re.search(
        r"^def (\w+Loaded) \(mem[^\n]*\) : Prop :=\n([^\n]+)", source, re.MULTILINE
    )
    if loaded is None:
        raise ValueError(f"no loaded predicate: {module}")
    expected_body = " ∧ ".join(f"{name} mem" for name, _ in chunks)
    if loaded[2].strip() != expected_body:
        raise ValueError(f"nonstandard loaded predicate: {module}")
    lines = [
        f"import Vsa.Sim.Code.{module}",
        "import Vsa.Sim.Code.FixedImage",
        "",
        "namespace Vsa.Sim.Code",
        "",
    ]
    theorem_names = []
    total = 0
    for name, body in chunks:
        pins = [(int(a, 16), int(b, 16)) for a, b in BYTE_PIN.findall(body)]
        if len(pins) != body.count("mem[") or not 0 < len(pins) <= 64:
            raise ValueError(f"unsupported/malformed byte conjunction: {name}")
        if any(image.get(a) != b for a, b in pins):
            raise ValueError(f"existing Code bytes differ from ELF: {name}")
        if any(not 0x80000000 <= a < 0x80018BE0 for a, _ in pins):
            raise ValueError(f"projection is not entirely text: {name}")
        theorem = f"fixedText_{name}"
        theorem_names.append(theorem)
        terms = ",\n    ".join(f"h {a - 0x80000000} (by decide)" for a, _ in pins)
        value = terms if len(pins) == 1 else f"⟨{terms}⟩"
        lines += [
            f"theorem {theorem} {{mem : Std.ExtHashMap Nat (BitVec 8)}}",
            f"    (h : FixedTextLoaded mem) : {name} mem := by",
            f"  exact {value}",
            "",
        ]
        total += len(pins)
    theorem = f"FixedTextLoaded.{loaded[1]}"
    terms = ", ".join(f"{name} h" for name in theorem_names)
    value = terms if len(theorem_names) == 1 else f"⟨{terms}⟩"
    lines += [
        f"theorem {theorem} {{mem : Std.ExtHashMap Nat (BitVec 8)}}",
        f"    (h : FixedTextLoaded mem) : {loaded[1]} mem :=",
        f"  {value}",
        "",
        f"#print axioms {theorem}",
        "",
        "end Vsa.Sim.Code",
        "",
    ]
    return "\n".join(lines), total


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=ROOT)
    parser.add_argument(
        "--output", type=Path, help="destination (default: REPO/Vsa/Sim/Code)"
    )
    parser.add_argument("--projection", action="append", default=[])
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    repo = args.repo.resolve()
    output = (args.output or repo / "Vsa/Sim/Code").resolve()
    raw = (repo / "c/while-riscv-htif.elf").read_bytes()
    sections = sections_from_elf(raw)
    embedded = re.search(
        r'def elfHex : String :=\s*"([0-9a-f]+)"',
        (repo / "Vsa/ElfBytes.lean").read_text(),
    )
    if embedded is None or bytes.fromhex(embedded[1]) != raw:
        raise ValueError("embedded elfHex does not equal the fixed ELF")
    image = {
        base + i: byte
        for base, data in sections.values()
        for i, byte in enumerate(data)
    }
    # Independent reconstruction check on every packed page and every byte.
    for _, data in sections.values():
        for start in range(0, len(data), PAGE_SIZE):
            page = data[start : start + PAGE_SIZE]
            packed = int.from_bytes(page, "little")
            if bytes((packed >> (8 * i)) & 255 for i in range(len(page))) != page:
                raise ValueError("packed image byte reconstruction failed")
    generated = {
        "FixedImageData.lean": generate_data(sections),
        "FixedImage.lean": generate_interface(),
    }
    counts = {}
    for module in dict.fromkeys(["Interp_run", "Setjmp"] + args.projection):
        generated[f"FixedImage_{module}.lean"], counts[module] = projection_module(
            repo, module, image
        )
    report = {
        "schema": "vsa.fixed-image-manifest.v1",
        "elf_sha256": ELF_SHA256,
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "embedded_elf_identical": True,
        "sections": {
            name: {
                "base": hex(base),
                "size": len(data),
                "sha256": hashlib.sha256(data).hexdigest(),
            }
            for name, (base, data) in sections.items()
        },
        "page_size": PAGE_SIZE,
        "projection_bytes_checked": counts,
        "generated_sha256": {
            name: hashlib.sha256(text.encode()).hexdigest()
            for name, text in generated.items()
        },
    }
    generated["fixed-image-manifest.json"] = json.dumps(report, indent=2) + "\n"
    if args.check:
        for name, text in generated.items():
            if (output / name).read_text() != text:
                raise ValueError(f"generated output is stale: {name}")
    else:
        output.mkdir(parents=True, exist_ok=True)
        for name, text in generated.items():
            (output / name).write_text(text)
    print(
        json.dumps(
            {
                "files": len(generated),
                "bytes": sum(len(text.encode()) for text in generated.values()),
                "projection_bytes": counts,
            }
        )
    )


if __name__ == "__main__":
    main()
