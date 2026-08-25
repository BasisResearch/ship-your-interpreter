#!/usr/bin/env python3
"""disasm_to_sites.py — objdump disassembly -> gen_sites.py site TSV.

The final mechanical layer in front of scripts/gen_sites.py: disassemble an
address range of the WHILE-interpreter ELF and classify every instruction
into gen_sites.py's supported site classes, emitting the TSV rows in its
exact input format.

    python3 scripts/disasm_to_sites.py 0x8001438c 0x800143f4 \
        [--elf c/while-riscv-htif.elf] [-o out.tsv] [--path branches.txt]

Classification is done from the INSTRUCTION WORD (opcode/funct3/funct7), not
from objdump's operand text — pseudo-ops (`mv`, `li`, `sext.w`, `beqz`,
`ret`, `j`, ...) therefore land in the right class automatically and the
emitted operand fields are guaranteed to agree with the encoding that
gen_sites.py re-derives byte pins from.  objdump's text is kept as a
trailing comment on every row.

Supported classes (see gen_sites.py's docstring):
    alu_addi (addi/mv/li)      addiw (addiw/sext.w)
    alu_add  sub  subw
    branch_taken / branch_nottaken (BEQ/BNE/BLT/BGE/BLTU/BGEU + pseudo forms)
    ld lw lbu    sd sw sb
    jal (rd != x0)    j (jal x0)    jr (jalr x0,0(rs1), incl. `ret`)

Branches: by default BOTH arms are emitted (taken first), each on its own
row with a `# branch:` comment above — delete the dead arm by hand.  Or pass
`--path FILE` with lines `<addr-hex> taken|nottaken` to pick one arm per
branch address (missing addresses still get both arms).

Anything else (64-bit `sub` was one until gen_sites.py grew the class;
`lh`/`sh`/`sll`/... still are) is emitted as a clearly-marked
`#UNSUPPORTED <addr> <word> <raw disasm>` comment line, which gen_sites.py
skips, so the gap is visible in the TSV instead of silently dropped.
gen_sites.py-side per-class operand restrictions that this tool can see
statically (rd=x0 ALU ops such as `nop`, x0-operand loads, rs1=x0 stores,
non-`ret` jalr shapes) are also emitted as `#UNSUPPORTED`.
"""

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_ELF = ROOT / "c" / "while-riscv-htif.elf"
DEFAULT_OBJDUMP = "riscv64-elf-objdump"

BRANCH_F3 = {0b000: "BEQ", 0b001: "BNE", 0b100: "BLT", 0b101: "BGE",
             0b110: "BLTU", 0b111: "BGEU"}
LOAD_F3 = {0b011: "ld", 0b010: "lw", 0b100: "lbu"}   # width/signedness key
STORE_F3 = {0b011: "sd", 0b010: "sw", 0b000: "sb"}

DISASM_RE = re.compile(r"^\s*([0-9a-f]+):\s+([0-9a-f]{8})\s+(.*?)\s*$")


def sext(value: int, bits: int) -> int:
    if value & (1 << (bits - 1)):
        value -= 1 << bits
    return value


def fields(word: int):
    return {
        "opcode": word & 0x7f,
        "rd": (word >> 7) & 0x1f,
        "funct3": (word >> 12) & 0x7,
        "rs1": (word >> 15) & 0x1f,
        "rs2": (word >> 20) & 0x1f,
        "funct7": (word >> 25) & 0x7f,
        "imm_i": (word >> 20) & 0xfff,
    }


def imm_b(word: int) -> int:
    """13-bit branch immediate (bit 0 = 0), unsigned 13-bit field value."""
    imm = (((word >> 31) & 1) << 12) | (((word >> 7) & 1) << 11) | \
          (((word >> 25) & 0x3f) << 5) | (((word >> 8) & 0xf) << 1)
    return imm & 0x1fff


def imm_s(word: int) -> int:
    return ((((word >> 25) & 0x7f) << 5) | ((word >> 7) & 0x1f)) & 0xfff


def imm_j(word: int) -> int:
    """21-bit JAL immediate (bit 0 = 0), unsigned 21-bit field value."""
    imm = (((word >> 31) & 1) << 20) | (((word >> 12) & 0xff) << 12) | \
          (((word >> 20) & 1) << 11) | (((word >> 21) & 0x3ff) << 1)
    return imm & 0x1fffff


class Row:
    """One output line: either a site row (cls + fields) or a comment."""

    def __init__(self, addr, word, cls=None, ops=None, comment=None, raw=""):
        self.addr, self.word = addr, word
        self.cls, self.ops = cls, ops or []
        self.comment, self.raw = comment, raw

    def tsv(self) -> str:
        if self.cls is None:
            return self.comment
        line = "\t".join([f"{self.addr:08x}", f"{self.word:08x}", self.cls]
                         + [str(o) for o in self.ops])
        if self.raw:
            line += f"\t# {self.raw}"
        return line


def unsupported(addr, word, raw, why) -> Row:
    return Row(addr, word,
               comment=f"#UNSUPPORTED {addr:08x} {word:08x} {raw}  [{why}]")


def classify(addr: int, word: int, raw: str, path: dict) -> list[Row]:
    """One disasm line -> one or more TSV rows (branches emit both arms)."""
    f = fields(word)
    op = f["opcode"]

    if op == 0b0010011:                                   # OP-IMM
        if f["funct3"] != 0b000:                          # only ADDI
            return [unsupported(addr, word, raw, "OP-IMM funct3 != ADDI")]
        if f["rd"] == 0:
            return [unsupported(addr, word, raw, "alu_addi with rd=x0")]
        return [Row(addr, word, "alu_addi",
                    [f["rd"], f["rs1"], f"{f['imm_i']:03x}"], raw=raw)]

    if op == 0b0011011:                                   # OP-IMM-32
        if f["funct3"] != 0b000:                          # only ADDIW/sext.w
            return [unsupported(addr, word, raw, "OP-IMM-32 funct3 != ADDIW")]
        if f["rd"] == 0:
            return [unsupported(addr, word, raw, "addiw with rd=x0")]
        return [Row(addr, word, "addiw",
                    [f["rd"], f["rs1"], f"{f['imm_i']:03x}"], raw=raw)]

    if op == 0b0110011:                                   # OP (RTYPE)
        key = (f["funct3"], f["funct7"])
        cls = {(0b000, 0b0000000): "alu_add",
               (0b000, 0b0100000): "sub"}.get(key)
        if cls is None:
            return [unsupported(addr, word, raw, "RTYPE op not ADD/SUB")]
        if f["rd"] == 0:
            return [unsupported(addr, word, raw, f"{cls} with rd=x0")]
        return [Row(addr, word, cls, [f["rd"], f["rs1"], f["rs2"]], raw=raw)]

    if op == 0b0111011:                                   # OP-32 (RTYPEW)
        if (f["funct3"], f["funct7"]) != (0b000, 0b0100000):   # only SUBW
            return [unsupported(addr, word, raw, "RTYPEW op not SUBW")]
        if f["rd"] == 0:
            return [unsupported(addr, word, raw, "subw with rd=x0")]
        return [Row(addr, word, "subw", [f["rd"], f["rs1"], f["rs2"]],
                    raw=raw)]

    if op == 0b1100011:                                   # BRANCH
        bop = BRANCH_F3.get(f["funct3"])
        if bop is None:
            return [unsupported(addr, word, raw, "branch funct3 unknown")]
        imm = imm_b(word)
        ops = [bop, f["rs1"], f["rs2"], f"{imm:04x}"]
        tgt = (addr + sext(imm, 13)) % (1 << 64)
        choice = path.get(addr)
        arms = [choice] if choice else ["taken", "nottaken"]
        rows = []
        if choice is None:
            rows.append(Row(addr, word, comment=(
                f"# branch: both arms emitted for 0x{addr:08x} "
                f"(target 0x{tgt:x}) — delete the untaken arm "
                f"(or use --path)")))
        for arm in arms:
            rows.append(Row(addr, word, f"branch_{arm}", ops, raw=raw))
        return rows

    if op == 0b0000011:                                   # LOAD
        cls = LOAD_F3.get(f["funct3"])
        if cls is None:
            return [unsupported(addr, word, raw,
                                "load width/signedness (lb/lh/lhu/lwu?)")]
        if f["rd"] == 0 or f["rs1"] == 0:
            return [unsupported(addr, word, raw, f"{cls} with x0 operand")]
        return [Row(addr, word, cls,
                    [f["rd"], f["rs1"], f"{f['imm_i']:03x}"], raw=raw)]

    if op == 0b0100011:                                   # STORE
        cls = STORE_F3.get(f["funct3"])
        if cls is None:
            return [unsupported(addr, word, raw, "store width (sh?)")]
        if f["rs1"] == 0:
            return [unsupported(addr, word, raw, f"{cls} with rs1=x0")]
        return [Row(addr, word, cls,
                    [f["rs2"], f["rs1"], f"{imm_s(word):03x}"], raw=raw)]

    if op == 0b1101111:                                   # JAL
        imm = imm_j(word)
        if f["rd"] == 0:
            return [Row(addr, word, "j", [f"{imm:06x}"], raw=raw)]
        return [Row(addr, word, "jal", [f["rd"], f"{imm:06x}"], raw=raw)]

    if op == 0b1100111:                                   # JALR
        if f["funct3"] != 0 or f["rd"] != 0 or f["imm_i"] != 0:
            return [unsupported(addr, word, raw,
                                "jalr shape != jr rs1 (rd=x0, imm=0)")]
        if f["rs1"] == 0:
            return [unsupported(addr, word, raw, "jr with rs1=x0")]
        return [Row(addr, word, "jr", [f["rs1"]], raw=raw)]

    return [unsupported(addr, word, raw, f"opcode 0x{op:02x}")]


def read_path(path: Path) -> dict:
    """`<addr-hex> taken|nottaken` per line -> {addr: arm}."""
    out = {}
    for lineno, rawline in enumerate(path.read_text().splitlines(), 1):
        line = rawline.split("#", 1)[0].strip()
        if not line:
            continue
        parts = line.split()
        if len(parts) != 2 or parts[1] not in ("taken", "nottaken"):
            raise ValueError(
                f"{path}:{lineno}: expected `<addr-hex> taken|nottaken`")
        out[int(parts[0], 16)] = parts[1]
    return out


def disassemble(objdump: str, elf: Path, lo: int, hi: int) -> list[tuple]:
    cmd = [objdump, "-d", str(elf),
           f"--start-address=0x{lo:x}", f"--stop-address=0x{hi:x}"]
    res = subprocess.run(cmd, capture_output=True, text=True)
    if res.returncode != 0:
        raise RuntimeError(f"{' '.join(cmd)} failed:\n{res.stderr}")
    out = []
    for line in res.stdout.splitlines():
        m = DISASM_RE.match(line)
        if not m:
            continue
        addr = int(m.group(1), 16)
        if not (lo <= addr < hi):
            continue
        word = int(m.group(2), 16)
        raw = " ".join(m.group(3).split())
        out.append((addr, word, raw))
    return out


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("start", help="range start address (hex)")
    ap.add_argument("stop", help="range stop address (hex, exclusive)")
    ap.add_argument("--elf", type=Path, default=DEFAULT_ELF)
    ap.add_argument("--objdump", default=DEFAULT_OBJDUMP)
    ap.add_argument("--path", type=Path, default=None,
                    help="file of `<addr-hex> taken|nottaken` branch choices")
    ap.add_argument("-o", "--output", type=Path, default=None,
                    help="output TSV (default stdout)")
    args = ap.parse_args()

    lo, hi = int(args.start, 16), int(args.stop, 16)
    path = read_path(args.path) if args.path else {}
    instrs = disassemble(args.objdump, args.elf, lo, hi)
    if not instrs:
        print("error: no instructions disassembled in range", file=sys.stderr)
        return 1

    lines = [f"# Generated by scripts/disasm_to_sites.py "
             f"0x{lo:x} 0x{hi:x} ({args.elf.name});",
             f"# feed to scripts/gen_sites.py.  Branch rows: keep exactly "
             f"one arm per branch."]
    n_sites = n_unsup = 0
    for addr, word, raw in instrs:
        for row in classify(addr, word, raw, path):
            lines.append(row.tsv())
            if row.cls is None and row.comment.startswith("#UNSUPPORTED"):
                n_unsup += 1
            elif row.cls is not None:
                n_sites += 1

    text = "\n".join(lines) + "\n"
    if args.output:
        args.output.write_text(text)
        print(f"wrote {args.output} ({n_sites} site rows, "
              f"{n_unsup} unsupported)", file=sys.stderr)
    else:
        sys.stdout.write(text)
        print(f"({n_sites} site rows, {n_unsup} unsupported)",
              file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
