#!/usr/bin/env python3
"""genseg/lib.py — shared plumbing for the arm-compiler generators.

Extracted from the five hand-written generators (`gen_m4_term_row.py`,
`gen_exec_row.py`, `gen_bin_dispatch_row.py`, `gen_m5_error_routing.py`,
`gen_decode_table.py`) per the residual-unification survey (~70% shared per the
survey).  Groups the genuinely-common machinery:

* `Emitter` — the line accumulator every generator hand-rolls (`L=[]; A=L.append`)
  + the header/write/`#print axioms` idioms.
* `load_tsv` / `load_toml_or_tsv` — the TSV row-dict parser they all share
  (`# comment` + header-line skip + tab split into a dict).
* disasm parsing (`parse_disasm`, `words_for_range`) — read
  `experiments/disasm.txt` into an `addr -> Instr` map with decoded fields; the
  arm compiler reads its `(pc, word)` body-lists straight from here instead of
  hand-transcribing the hex.
* branch/j/jr terminator decoding (`decode_terminator`) — turns a disasm
  branch/jump line into the concrete `TInstr`-record data (`.br op taken?`/`.j`/
  `.jr`, the 4 LE bytes, rs1/rs2, imm13/imm21/imm12, target) that `#derive_case`'s
  `terminator ⟨…⟩` needs — the fiddly part every seg author decodes by hand.
* decode-index lookup (`DecodeIndex`) — the `scripts/decode_index.tsv`
  word→`DecodeTable.Batch..` map; used to VERIFY every word in a span is tabled
  (the seg layer's precondition) before emitting.
* Lean helpers (`bv64`, `bv32`, `le_bytes`, `hex`, `cap`) — the little
  formatters duplicated across the five.

NO Lean output from this module itself; it is import-only plumbing.
"""

import os
import re


# --------------------------------------------------------------------------
# paths
# --------------------------------------------------------------------------

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DISASM = os.path.join(ROOT, "experiments", "disasm.txt")
DECODE_INDEX = os.path.join(ROOT, "scripts", "decode_index.tsv")


# --------------------------------------------------------------------------
# small Lean formatters (the duplicated one-liners)
# --------------------------------------------------------------------------

def hexint(s):
    if isinstance(s, int):
        return s
    return int(str(s), 16)


def bv64(addr):
    """`0x........#64` for a 64-bit address literal."""
    return f"0x{hexint(addr):08x}#64"


def bv32(word):
    """`0x........#32` for a 32-bit instruction word."""
    return f"0x{hexint(word):08x}#32"


def le_bytes(word, n=4):
    """The `n` little-endian bytes of `word`, as `0xNN#8` Lean literals."""
    w = hexint(word)
    return [f"0x{(w >> (8 * i)) & 0xFF:02x}#8" for i in range(n)]


def cap(s):
    """Capitalize first letter only (leave the rest), the `key.capitalize()`
    idiom the generators use for `<Key>Resid` struct names."""
    return s[:1].upper() + s[1:] if s else s


def sext(value, bits):
    """Sign-extend a `bits`-wide value to a Python int."""
    if value & (1 << (bits - 1)):
        value -= 1 << bits
    return value


# --------------------------------------------------------------------------
# the line accumulator + file emission (the `L=[]; A=L.append; write` idiom)
# --------------------------------------------------------------------------

class Emitter:
    """The `L = []; A = L.append` accumulator every generator hand-rolls, plus
    the file-header / write / `#print axioms` conveniences."""

    def __init__(self):
        self.lines = []

    def __call__(self, *ls):
        """`emit("line")` or `emit("a", "b")` — append raw line(s)."""
        for l in ls:
            self.lines.append(l)

    def blank(self):
        self.lines.append("")

    def block(self, text):
        """Append a multi-line string, splitting on newlines (so a template
        constant lands as individual lines)."""
        for l in text.split("\n"):
            self.lines.append(l)

    def print_axioms(self, name):
        self.lines.append(f"#print axioms {name}")
        self.lines.append("")

    def text(self):
        return "\n".join(self.lines)

    def write(self, path):
        with open(path, "w") as f:
            f.write(self.text())
        if not self.text().endswith("\n"):
            with open(path, "a") as f:
                f.write("\n")

    # -- the standard house header for a rows/ file -----------------------
    def house_header(self, imports, doc, namespace="Vsa.Sim",
                     opens=None, options=None, notation_specst=True):
        for m in imports:
            self.lines.append(f"import {m}")
        self.blank()
        self.lines.append("/-!")
        self.block(doc.rstrip("\n"))
        self.lines.append("-/")
        self.blank()
        default_opens = [
            "open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa",
            "open Register",
            "open Vsa.Machine (MState Config Step Steps)",
            "open Vsa.Logic (Triple)",
        ]
        for o in (opens if opens is not None else default_opens):
            self.lines.append(o)
        self.blank()
        for o in (options or []):
            self.lines.append(o)
        if options:
            self.blank()
        self.lines.append(f"namespace {namespace}")
        self.blank()
        if notation_specst:
            self.lines.append('local notation "SpecSt" => Vsa.While.St')
            self.blank()


# --------------------------------------------------------------------------
# TSV / TOML row parsing (the shared `load_tsv`)
# --------------------------------------------------------------------------

def load_tsv(path, columns):
    """Parse a `#`-commented, tab-separated TSV whose first data line may be a
    header (== `columns[0]`).  Returns a list of dicts keyed by `columns`.
    Extra columns beyond `columns` are dropped; missing trailing columns get
    the empty string.  This is the exact loop the five generators duplicate."""
    rows = []
    for line in open(path):
        line = line.rstrip("\n")
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t")
        if parts[0] == columns[0]:
            continue
        d = {}
        for i, c in enumerate(columns):
            d[c] = parts[i] if i < len(parts) else ""
        rows.append(d)
    return rows


def load_toml(path):
    """Minimal TOML loader for arm descriptions.  Uses stdlib `tomllib`
    (py3.11+) when available; else a tiny fallback covering the subset the arm
    descriptions use (top-level key=value + `[[array-of-tables]]`)."""
    try:
        import tomllib
        with open(path, "rb") as f:
            return tomllib.load(f)
    except ModuleNotFoundError:
        return _toml_fallback(path)


def _toml_fallback(path):
    """Handles: `key = value`, string/int/bool/list scalars, `[section]`,
    `[[array-of-tables]]`.  Sufficient for the arm-description format below."""
    root = {}
    cur = root
    for raw in open(path):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        m = re.match(r"\[\[(.+)\]\]$", line)
        if m:
            key = m.group(1).strip()
            root.setdefault(key, [])
            cur = {}
            root[key].append(cur)
            continue
        m = re.match(r"\[(.+)\]$", line)
        if m:
            key = m.group(1).strip()
            root[key] = cur = {}
            continue
        m = re.match(r"([A-Za-z0-9_\-]+)\s*=\s*(.+)$", line)
        if m:
            k, v = m.group(1), m.group(2).strip()
            cur[k] = _toml_value(v)
    return root


def _toml_value(v):
    if v.startswith("[") and v.endswith("]"):
        inner = v[1:-1].strip()
        if not inner:
            return []
        return [_toml_value(x.strip()) for x in _split_toplevel(inner)]
    if (v.startswith('"') and v.endswith('"')) or \
       (v.startswith("'") and v.endswith("'")):
        return v[1:-1]
    if v in ("true", "false"):
        return v == "true"
    try:
        return int(v, 0)
    except ValueError:
        return v


def _split_toplevel(s):
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return out


def load_arm(path):
    """Load an arm description from `.toml` or `.tsv`.  A `.tsv` arm is a flat
    2-column `key<TAB>value` sheet with instr/pin rows encoded as repeated
    `instr` / `pin` keys (see arm-description spec in genseg.py)."""
    if path.endswith(".toml"):
        return load_toml(path)
    return _load_arm_tsv(path)


def _load_arm_tsv(path):
    d = {"instr": [], "pin": []}
    for raw in open(path):
        line = raw.rstrip("\n")
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t")
        k = parts[0].strip()
        if k in ("instr", "pin"):
            d[k].append([p.strip() for p in parts[1:]])
        elif len(parts) >= 2:
            d[k] = parts[1].strip()
    return d


# --------------------------------------------------------------------------
# disasm parsing
# --------------------------------------------------------------------------

# `    80002b24:\t00150413          \taddi\ts0,a0,1`
_DISASM_RE = re.compile(
    r"^\s*([0-9a-fA-F]+):\s+([0-9a-fA-F]{8})\s+(\S+)(?:\s+(.*))?$")

# the branch mnemonics we know how to turn into a terminator, mapped to the
# model's `bop` constructor + the natural-polarity operand order.
_BR_OPS = {
    "beq": "bop.BEQ", "bne": "bop.BNE", "blt": "bop.BLT",
    "bge": "bop.BGE", "bltu": "bop.BLTU", "bgeu": "bop.BGEU",
    # pseudo-ops (rs2 = x0):
    "beqz": "bop.BEQ", "bnez": "bop.BNE",
    "blez": "bop.BGE", "bgez": "bop.BGE", "bltz": "bop.BLT", "bgtz": "bop.BLT",
}


class Instr:
    """One decoded disasm line."""

    def __init__(self, addr, word, mnem, ops, raw):
        self.addr = addr
        self.word = word
        self.mnem = mnem
        self.ops = ops          # raw operand string
        self.raw = raw          # full source line (asm comment)

    @property
    def is_branch(self):
        return self.mnem in _BR_OPS

    @property
    def is_jump(self):
        return self.mnem in ("j", "jal", "jr", "jalr", "ret")

    @property
    def is_terminator(self):
        return self.is_branch or self.is_jump

    def __repr__(self):
        return f"Instr(0x{self.addr:08x}, {self.word:08x}, {self.mnem} {self.ops})"


def parse_disasm(path=DISASM):
    """Read the objdump disasm into an `addr(int) -> Instr` dict."""
    out = {}
    for line in open(path):
        m = _DISASM_RE.match(line)
        if not m:
            continue
        addr = int(m.group(1), 16)
        word = int(m.group(2), 16)
        mnem = m.group(3)
        ops = (m.group(4) or "").split("#")[0].strip()
        out[addr] = Instr(addr, word, mnem, ops, line.rstrip("\n"))
    return out


def words_for_range(lo, hi, disasm=None):
    """The ordered list of `Instr` at `[lo, hi)` (hi exclusive), 4-byte step."""
    disasm = disasm or parse_disasm()
    out = []
    a = hexint(lo)
    hi = hexint(hi)
    while a < hi:
        if a not in disasm:
            raise KeyError(f"0x{a:08x} not in disasm")
        out.append(disasm[a])
        a += 4
    return out


# --------------------------------------------------------------------------
# terminator decoding — the fiddly `#derive_case terminator ⟨…⟩` record data
# --------------------------------------------------------------------------

def _btype_fields(word):
    """Decode a BTYPE word → (rs1, rs2, imm13_int)."""
    rs1 = (word >> 15) & 0x1F
    rs2 = (word >> 20) & 0x1F
    imm = ((((word >> 31) & 1) << 12) | (((word >> 7) & 1) << 11) |
           (((word >> 25) & 0x3F) << 5) | (((word >> 8) & 0xF) << 1))
    return rs1, rs2, imm


def _jal_imm(word):
    """Decode a JAL word → imm21_int (unsigned 21-bit field)."""
    return ((((word >> 31) & 1) << 20) | (((word >> 12) & 0xFF) << 12) |
            (((word >> 20) & 1) << 11) | (((word >> 21) & 0x3FF) << 1))


def _jalr_fields(word):
    """Decode a JALR word → (rs1, imm12_int signed field kept unsigned)."""
    rs1 = (word >> 15) & 0x1F
    imm = (word >> 20) & 0xFFF
    return rs1, imm


def decode_terminator(instr, taken=None):
    """Turn a branch/jump `Instr` into the data `#derive_case`'s `terminator`
    record needs, as a dict:

        kind        one of "br" / "j" / "jr"
        op          the `bop.XXX` string (br only)
        taken       the resolved polarity Bool (br only; caller must supply)
        b0..b3      the 4 LE byte strings ("0xNN#8")
        rs1, rs2    source indices (Nat)
        imm13/21/12 the Lean immediate literals ("0xNNNN#13" etc.)
        target      the concrete branch/jump target (int) for chain contiguity
        record      the fully-formatted `⟨…⟩` terminator record string

    `taken` is a per-CASE choice for branches (which arm this case resolves);
    it is REQUIRED for `br` and ignored otherwise.
    """
    w = instr.word
    b = le_bytes(w)
    d = {"b0": b[0], "b1": b[1], "b2": b[2], "b3": b[3]}
    if instr.is_branch:
        rs1, rs2, imm = _btype_fields(w)
        if taken is None:
            raise ValueError(
                f"0x{instr.addr:08x} {instr.mnem}: branch terminator needs an "
                f"explicit `taken` polarity (which arm this case resolves)")
        d.update(kind="br", op=_BR_OPS[instr.mnem], taken=bool(taken),
                 rs1=rs1, rs2=rs2, imm13=imm, imm21=0, imm12=0,
                 target=(instr.addr + sext(imm, 13)) % 2**64 if taken
                 else instr.addr + 4)
        takenS = "true" if taken else "false"
        d["record"] = (
            f"⟨{bv64(instr.addr)}, {bv32(w)}, {b[0]}, {b[1]}, {b[2]}, {b[3]}, "
            f".br {d['op']} {takenS}, {rs1}, {rs2}, "
            f"0x{imm:04x}#13, 0#21, 0#12⟩")
    elif instr.mnem in ("j", "jal") and instr.mnem == "j":
        imm = _jal_imm(w)
        d.update(kind="j", op=None, rs1=0, rs2=0, imm13=0, imm21=imm, imm12=0,
                 target=(instr.addr + sext(imm, 21)) % 2**64)
        d["record"] = (
            f"⟨{bv64(instr.addr)}, {bv32(w)}, {b[0]}, {b[1]}, {b[2]}, {b[3]}, "
            f".j, 0, 0, 0#13, 0x{imm:06x}#21, 0#12⟩")
    elif instr.mnem in ("jr", "ret"):
        rs1, imm = _jalr_fields(w)
        d.update(kind="jr", op=None, rs1=rs1, rs2=0, imm13=0, imm21=0, imm12=imm,
                 target=None)
        d["record"] = (
            f"⟨{bv64(instr.addr)}, {bv32(w)}, {b[0]}, {b[1]}, {b[2]}, {b[3]}, "
            f".jr, {rs1}, 0, 0#13, 0#21, 0x{imm:03x}#12⟩")
    else:
        raise ValueError(
            f"0x{instr.addr:08x} {instr.mnem}: not a br/j/jr terminator "
            f"(a `jal <sym>` call stays a Shape-D seam — use terminator='jal')")
    return d


# --------------------------------------------------------------------------
# decode-index lookup (the tabledness precondition)
# --------------------------------------------------------------------------

class DecodeIndex:
    """The `scripts/decode_index.tsv` word→Batch map, for verifying that every
    instruction word in a span is on the block-reflection decode table (the seg
    layer's precondition — EnvDefSeg documents this check)."""

    def __init__(self, path=DECODE_INDEX):
        self.tbl = {}
        for line in open(path):
            line = line.rstrip("\n")
            if not line or line.startswith("#"):
                continue
            parts = line.split("\t")
            if len(parts) >= 2:
                self.tbl[parts[0].lower()] = parts[1]

    def has(self, word):
        return f"{hexint(word):08x}" in self.tbl

    def batch(self, word):
        return self.tbl.get(f"{hexint(word):08x}")

    def check_range(self, instrs):
        """Return the list of `Instr` whose word is NOT tabled (empty = all OK).
        Terminators are checked too (their word must decode)."""
        return [i for i in instrs if not self.has(i.word)]
