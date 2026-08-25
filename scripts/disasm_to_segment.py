#!/usr/bin/env python3
"""disasm_to_segment.py — sites TSV (from disasm_to_sites.py) -> DRAFT
segment JSON for gen_segment.py --mode straight.

    python3 scripts/disasm_to_segment.py 0x800069f0 0x80006a0c \
        --sites SITES.tsv [--theorem tr_foo] [--loaded-pred Vsa.Sim.Code.XLoaded]
        [--site-suffix _gen] [-o out.json]

Takes the classified instruction rows of a range (the disasm_to_sites.py
output, with exactly ONE arm kept per branch) and emits a gen_segment.py
core segment spec with everything mechanical filled in:

  * the step list in address order, each with the right gen_segment class,
    the gen_sites.py site name, and the site-call argument tail laid out in
    the generated batteries' uniform signature order;
  * def-use analysis over the operands:
      - registers READ before written in the segment become the initial
        `pins` list, with auto-named ghost values `v<reg>` (and matching
        `(v<reg> : BitVec 64)` theorem parameters);
      - WRITTEN registers get per-step `rd`/`rd_val` entries — gen_segment's
        pin drop/re-add choreography then handles the bundle automatically;
  * per-class placeholders, every one spelled `TODO(...)` so gen_segment.py
    REFUSES to run until they are filled (its TODO gate):
      - loads: the byte value params + `hlo/hhiram/hhtif/halign/h<j>`
        byte-hypothesis slots,
      - stores: `key`/`key_rw`/`loaded_via` (+ the 4 in-call side conditions),
      - branches: a `pre_lines` guard-fact skeleton feeding `hguard$k`
        (concrete-operand guards can instead use `"guard": "decide"` —
        replace the two TODOs with that option and `$guard` in the call),
      - jal: the link step is emitted complete, followed by a
        `class: call` placeholder step for the callee glue,
      - jr: `pc_val`/`pc_rw`/`htgt`;
  * `pre`/`post`/`pre_bind.obtain`/`post_proof` stay segment-specific:
    `pre`/`post` are TODO, `pre_bind` is emitted with the standard names
    and a TODO obtain pattern.  (Alternatively switch the draft to
    `"boundary": "segst"` by hand — then pre/post/pre_bind/post_proof are
    synthesized and only the value/guard/store TODOs remain.)

The value-annotation slots (`rd_val` rewrites like `li31_val`/`dec1_fwd`,
guard derivations, store-key lemmas) are exactly the residue that
scripts/README-segments.md documents as hand-written; the draft carries the
raw machine-level value expression for each write in an informational
`"raw_val"` key (ignored by gen_segment.py) so filling `rd_val`/`rw` is a
lookup, not a re-derivation.
"""

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# gen_sites TSV class -> gen_segment step class
SEG_CLASS = {"alu_addi": "alu", "addiw": "alu", "alu_add": "alu", "sub": "alu",
             "subw": "alu", "ld": "alu", "lw": "alu", "lbu": "alu",
             "sd": "sd", "sw": "sw", "sb": "sb",
             "branch_taken": "btaken", "branch_nottaken": "bnottaken",
             "jal": "jal", "j": "j", "jr": "jr"}
LOAD_BYTES = {"ld": 8, "lw": 4, "lbu": 1}
STORE_BYTES = {"sd": 8, "sw": 4, "sb": 1}


def sext(value: int, bits: int) -> int:
    if value & (1 << (bits - 1)):
        value -= 1 << bits
    return value


class Instr:
    def __init__(self, addr, word, cls, ops, asm):
        self.addr, self.word, self.cls, self.ops, self.asm = \
            addr, word, cls, ops, asm

    def reads(self) -> list[int]:
        c, o = self.cls, self.ops
        if c in ("alu_addi", "addiw", "ld", "lw", "lbu"):
            rs = [int(o[1])]
        elif c in ("alu_add", "sub", "subw"):
            rs = [int(o[1]), int(o[2])]
        elif c in ("branch_taken", "branch_nottaken"):
            rs = [int(o[1]), int(o[2])]
        elif c in ("sd", "sw", "sb"):
            rs = [int(o[1]), int(o[0])]     # address base, stored value
        elif c == "jr":
            rs = [int(o[0])]
        else:                               # jal / j
            rs = []
        return [r for r in dict.fromkeys(rs) if r != 0]

    def writes(self) -> int | None:
        c, o = self.cls, self.ops
        if c in ("alu_addi", "addiw", "alu_add", "sub", "subw",
                 "ld", "lw", "lbu"):
            return int(o[0])
        if c == "jal":
            return int(o[0])
        return None

    def raw_val(self) -> str | None:
        """The machine-level written-value expression (informational)."""
        c, o = self.cls, self.ops
        v = lambda r: f"v{r}" if int(r) else "(0#64)"
        if c == "alu_addi":
            return f"({v(o[1])} + sign_extend (m := 64) (0x{o[2]}#12))"
        if c == "addiw":
            return (f"(sign_extend (m := 64) (Sail.BitVec.extractLsb "
                    f"({v(o[1])} + sign_extend (m := 64) (0x{o[2]}#12)) 31 0))")
        if c == "alu_add":
            return f"({v(o[1])} + {v(o[2])})"
        if c == "sub":
            return f"({v(o[1])} - {v(o[2])})"
        if c == "subw":
            return (f"(sign_extend (m := 64) ((Sail.BitVec.extractLsb "
                    f"{v(o[1])} 31 0) - (Sail.BitVec.extractLsb {v(o[2])} 31 0)))")
        if c in ("ld", "lw"):
            return "(sign_extend (m := 64) <loaded bytes>)"
        if c == "lbu":
            return "(zero_extend (m := 64) <loaded byte>)"
        return None


def parse_sites(path: Path, lo: int, hi: int) -> list[Instr]:
    rows: dict[int, list[Instr]] = {}
    order: list[int] = []
    for lineno, rawline in enumerate(path.read_text().splitlines(), 1):
        line = rawline.strip()
        if not line or line.startswith("#"):
            continue
        body, _, comment = line.partition("#")
        parts = body.split()
        if len(parts) < 3:
            raise ValueError(f"{path}:{lineno}: expected addr word class ...")
        addr, word, cls = int(parts[0], 16), int(parts[1], 16), parts[2]
        if not (lo <= addr < hi):
            continue
        if cls not in SEG_CLASS:
            raise ValueError(f"{path}:{lineno}: unknown class {cls}")
        ins = Instr(addr, word, cls, parts[3:], comment.strip())
        rows.setdefault(addr, []).append(ins)
        if addr not in order:
            order.append(addr)
    out = []
    for addr in sorted(order):
        arms = rows[addr]
        if len(arms) > 1:
            raise ValueError(
                f"0x{addr:08x}: {len(arms)} rows (both branch arms?) — keep "
                f"exactly one arm per branch (delete one row or rerun "
                f"disasm_to_sites.py with --path)")
        out.append(arms[0])
    return out


class DraftBuilder:
    def __init__(self, instrs, suffix, loaded_pred):
        self.instrs = instrs
        self.suffix = suffix
        self.loaded_pred = loaded_pred
        self.written: set[int] = set()
        self.pinned: list[int] = []      # read-before-written, first-use order

    # -- def-use ------------------------------------------------------------

    def compute_pins(self):
        for ins in self.instrs:
            for r in ins.reads():
                if r not in self.written and r not in self.pinned:
                    self.pinned.append(r)
            w = ins.writes()
            if w:
                self.written.add(w)

    def tracked(self, r: int) -> bool:
        """Registers resolvable via `$v:`/`$pin:` at emission time: the
        initial pins, plus registers already written by an earlier step —
        gen_segment re-adds those to the bundle under their (to-be-filled)
        `rd_val`, so the placeholders resolve once the TODO values are in."""
        return r in self.pinned or r in self.walk_written

    def V(self, r: int) -> str:
        if r == 0:
            return "(0#64)"
        return f"$v:x{r}" if self.tracked(r) else f"TODO(v-x{r})"

    def H(self, r: int) -> str:
        return f"$pin:x{r}" if self.tracked(r) else f"TODO(hyp-x{r})"

    # -- steps --------------------------------------------------------------

    def build_steps(self):
        self.walk_written: set[int] = set()
        steps = []
        for ins in self.instrs:
            steps.extend(self.build_step(ins))
            w = ins.writes()
            if w:
                self.walk_written.add(w)
        return steps

    def build_step(self, ins: Instr):
        c, o = ins.cls, ins.ops
        st = {"addr": f"0x{ins.addr:08x}",
              "site": f"site_{ins.addr:08x}{self.suffix}",
              "class": SEG_CLASS[c]}
        if ins.asm:
            st["asm"] = ins.asm
        vregs = [r for r in dict.fromkeys(
            [int(x) for x in (o[1:3] if c in ("alu_add", "sub", "subw",
                                              "branch_taken",
                                              "branch_nottaken")
             else o[1:2] if c in ("alu_addi", "addiw", "ld", "lw", "lbu")
             else [o[1], o[0]] if c in ("sd", "sw", "sb")
             else o[0:1] if c == "jr" else [])]) if r != 0]
        vals = " ".join(self.V(r) for r in vregs)
        hyps = " ".join(self.H(r) for r in vregs)
        vals = (vals + " ") if vals else ""
        hyps = (hyps + " ") if hyps else ""

        if c in ("alu_addi", "addiw", "alu_add", "sub", "subw"):
            st["rd"] = f"x{ins.writes()}"
            st["rd_val"] = "TODO"
            st["rw"] = "TODO"
            st["raw_val"] = ins.raw_val()
            st["call"] = f"$vmi {vals}$hG $hpc $hmi {hyps}$hmem rfl $hi"
        elif c in ("ld", "lw", "lbu"):
            n = LOAD_BYTES[c]
            bs = ("TODO(b)" if c == "lbu"
                  else " ".join(f"TODO(b{j})" for j in range(n)))
            side = "TODO(hlo) TODO(hhiram) TODO(hhtif)" + \
                ("" if c == "lbu" else " TODO(halign)")
            hbs = ("TODO(hb)" if c == "lbu"
                   else " ".join(f"TODO(h{j})" for j in range(n)))
            st["rd"] = f"x{ins.writes()}"
            st["rd_val"] = "TODO"
            st["raw_val"] = ins.raw_val()
            st["call"] = (f"$vmi {vals}{bs} $hG $hpc $hmi {hyps}$hmem rfl "
                          f"{side} {hbs} $hi")
        elif c in ("sd", "sw", "sb"):
            side = "TODO(halo) TODO(hahiram) TODO(hahiwin) TODO(haalign)" \
                if c != "sb" else "TODO(hlo) TODO(hhiram) TODO(hhiwin)"
            st["key"] = "TODO"
            st["key_rw"] = "TODO"
            st["src_val"] = self.V(int(o[0]))
            if c == "sb":
                st["data_rw"] = "stData_zext"
            st["loaded_via"] = "TODO"
            st["call"] = (f"$vmi {vals}$hG $hpc $hmi {hyps}$hmem rfl "
                          f"{side} $hi")
        elif c in ("branch_taken", "branch_nottaken"):
            imm = int(o[3], 16)
            if c == "branch_taken":
                st["imm"] = f"0x{imm:04x}#13"
                st["target"] = f"0x{(ins.addr + sext(imm, 13)) % 2**64:08x}"
            st["pre_lines"] = ["have hguard$k : TODO := TODO"]
            st["call"] = (f"$vmi {vals}$hG $hpc $hmi {hyps}$hmem rfl "
                          f"hguard$k $hi")
        elif c == "jal":
            imm = int(o[1], 16)
            st["imm"] = f"0x{imm:06x}#21"
            st["target"] = f"0x{(ins.addr + sext(imm, 21)) % 2**64:08x}"
            st["rd"] = f"x{int(o[0])}"
            st["call"] = "$vmi $hG $hpc $hmi $hmem rfl $hi"
            call_st = {
                "class": "call", "callee": "TODO",
                "args": "TODO", "pre_fields": ["TODO"],
                "post_obtain": "TODO", "post_good": "TODO",
                "post_pc": "TODO", "post_tick": "TODO",
                "pc_val": "TODO", "pins_drop": ["TODO"], "pins_add": [],
                "write_set": ["TODO"], "frame_hyp": "TODO",
                "loaded_lines": ["have hload$k : TODO := TODO"],
            }
            return [st, call_st]
        elif c == "j":
            imm = int(o[0], 16)
            st["imm"] = f"0x{imm:06x}#21"
            st["target"] = f"0x{(ins.addr + sext(imm, 21)) % 2**64:08x}"
            # htgt is over the literal pc: decidable
            st["call"] = "$vmi $hG $hpc $hmi $hmem rfl (by decide) $hi"
        elif c == "jr":
            st["pc_val"] = "TODO"
            st["pc_rw"] = "TODO"
            st["call"] = (f"$vmi {vals}$hG $hpc $hmi {hyps}$hmem rfl "
                          f"TODO(htgt) $hi")
        return [st]

    # -- whole spec ----------------------------------------------------------

    def build(self, theorem: str, imports: list[str]):
        self.compute_pins()
        steps = self.build_steps()
        has_mem = any(i.cls in LOAD_BYTES or i.cls in STORE_BYTES
                      for i in self.instrs)
        params = ["TODO: extra ghost binders (region facts, callee params, ...)"]
        if self.pinned:
            params.append("(" + " ".join(f"v{r}" for r in self.pinned)
                          + " : BitVec 64)")
        params.append("(m0 : Std.ExtHashMap Nat (BitVec 8))")
        pins = [{"reg": f"x{r}", "val": f"v{r}", "hyp": f"hv{r}"}
                for r in self.pinned]
        n_pin = len(pins)
        obtain = ("⟨hgood, hloaded, hpc, "
                  + ", ".join(f"hv{r}" for r in self.pinned)
                  + (", " if self.pinned else "")
                  + "⟨vmi, hmi⟩, htick, hmemeq, TODO(rest)⟩")
        return {
            "theorem": theorem,
            "doc": f"DRAFT (disasm_to_segment.py) — segment "
                   f"0x{self.instrs[0].addr:08x} → "
                   f"0x{self.instrs[-1].addr + 4:08x}, {len(steps)} steps, "
                   f"{n_pin} read-before-written pins. Fill every TODO.",
            "namespace": "Vsa.Sim",
            "imports": imports,
            "params": params,
            "pre": "TODO",
            "post": "TODO",
            "loaded_pred": self.loaded_pred,
            "pre_bind": {
                "obtain": obtain,
                "good": "hgood", "pc": "hpc", "minstret_var": "vmi",
                "minstret": "hmi", "tick": "htick", "loaded": "hloaded",
                "mem0": "m0", "memeq": "hmemeq",
            },
            "pins": pins,
            "prelude": ["-- TODO: hand facts (region bounds, hkey lemmas, ...)"]
            if has_mem else [],
            "steps": steps,
            "post_proof": ["TODO"],
        }


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("start", help="range start address (hex)")
    ap.add_argument("stop", help="range stop address (hex, exclusive)")
    ap.add_argument("--sites", type=Path, required=True,
                    help="site TSV from disasm_to_sites.py (one branch arm "
                         "per branch)")
    ap.add_argument("--theorem", default="tr_draft")
    ap.add_argument("--loaded-pred", default="TODO",
                    help="fully-qualified code byte-pin predicate")
    ap.add_argument("--site-suffix", default="",
                    help="suffix of the gen_sites.py battery theorem names")
    ap.add_argument("--imports", default=None,
                    help="comma-separated import list (default: TODO + RegPins)")
    ap.add_argument("-o", "--output", type=Path, default=None)
    args = ap.parse_args()

    lo, hi = int(args.start, 16), int(args.stop, 16)
    try:
        instrs = parse_sites(args.sites, lo, hi)
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    if not instrs:
        print("error: no site rows in range", file=sys.stderr)
        return 1
    imports = (args.imports.split(",") if args.imports
               else ["TODO(site battery module)", "Vsa.Sim.RegPins"])
    spec = DraftBuilder(instrs, args.site_suffix,
                        args.loaded_pred).build(args.theorem, imports)
    text = json.dumps(spec, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        args.output.write_text(text)
        n_todo = text.count("TODO")
        print(f"wrote {args.output} ({len(spec['steps'])} steps, "
              f"{len(spec['pins'])} pins, {n_todo} TODO slots)",
              file=sys.stderr)
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
