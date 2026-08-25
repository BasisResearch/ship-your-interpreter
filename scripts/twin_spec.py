#!/usr/bin/env python3
"""twin_spec — checked source-to-source variant emitter for verified segments.

A recurring Layer-3 cost: a verified segment needs a *twin* — same statement
and step battery with a small delta (a seam branch flipped taken<->nottaken, a
hypothesis dropped, a constant/name swapped).  Exemplars: SnprintfSpec46 =
SnprintfSpec7 with the `beqz t5` seam flipped (steps 1-16 verbatim, new tail);
SnprintfSpec44 = SnprintfSpec8's statement with `hmag` removed.

This tool makes that a *checked* transformation: every edit in the JSON delta
must match the source EXACTLY (old strings, hypothesis binders, seam sites) or
the tool aborts without writing — no silent drift when the source spec is
later edited.

Usage:
    python3 scripts/twin_spec.py SRC.lean DELTA.json -o OUT.lean

Delta JSON (all keys optional):

    {
      "rename":    {"exitToPrint_spec": "exitToPrintNN_spec", ...},
      "drop_hyps": ["hmag",                              # unique in source
                    {"name": "hmag", "in_theorem": "entryToPrint_neg_spec"}],
      "flip_sites": [{"addr": "0x8000812c",
                      "from_site": "site_8000812c_nottaken_fl",
                      "to_site":   "site_8000812c_taken_fs",
                      "tail_lines": ["  -- === 812c: ... ===", ...]}],
      "replace":   [{"old_str": "...", "new_str": "...", "count": 1}, ...]
    }

Semantics (applied in this order; all matching is done AFTER rename, so write
`drop_hyps`/`flip_sites`/`replace` entries in the *renamed* vocabulary):

1. rename — whole-word regex rename (theorem/def/hypothesis names).  Each old
   name must occur at least once.
2. drop_hyps — remove the paren-balanced binder `(name : ...)` (plus its line
   if that leaves it blank).  Each name must occur as a binder exactly once.
3. flip_sites — seam flip: locate the FIRST line invoking `from_site`, walk up
   to the nearest step-block comment (`-- ===`), check `addr` appears in that
   comment or the invocation, truncate from the comment line to EOF, append
   `tail_lines` verbatim.  `to_site` must appear in `tail_lines` (which must
   also close any namespaces the truncation cut off).
4. replace — exact string replacement; the number of occurrences must equal
   `count` (default 1).

The output gets a provenance header (source + delta sha256) and is written
only if every check passes.
"""
import argparse
import hashlib
import json
import pathlib
import re
import sys


class TwinError(SystemExit):
    def __init__(self, msg):
        super().__init__(f"twin_spec: FAIL: {msg}")


def apply_rename(text, rename):
    for old, new in rename.items():
        pat = re.compile(r"(?<![A-Za-z0-9_'!?])" + re.escape(old)
                         + r"(?![A-Za-z0-9_'!?])")
        text, n = pat.subn(new, text)
        if n == 0:
            raise TwinError(f"rename: name {old!r} not found in source")
        print(f"  rename {old} -> {new}: {n} occurrence(s)")
    return text


def decl_region(text, thm):
    """[start, end) of the declaration `theorem thm` (to the next top-level
    `theorem`/`def`/`end`, or EOF)."""
    m = re.search(r"^theorem\s+" + re.escape(thm) + r"(?![A-Za-z0-9_'!?])",
                  text, re.M)
    if m is None:
        raise TwinError(f"drop_hyps: theorem {thm!r} not found")
    e = re.compile(r"^(theorem|def|end)\b", re.M).search(text, m.end())
    return m.start(), (len(text) if e is None else e.start())


def apply_drop_hyps(text, entries):
    for ent in entries:
        if isinstance(ent, str):
            name, lo, hi = ent, 0, len(text)
            scope = "source"
        else:
            name = ent["name"]
            lo, hi = decl_region(text, ent["in_theorem"])
            scope = f"theorem {ent['in_theorem']}"
        pat = re.compile(r"\(\s*" + re.escape(name) + r"\s*:")
        starts = [m.start() for m in pat.finditer(text, lo, hi)]
        if len(starts) != 1:
            raise TwinError(f"drop_hyps: binder ({name} : ...) found "
                            f"{len(starts)} times in {scope} "
                            f"(need exactly 1)")
        i = starts[0]
        depth, j = 0, i
        while j < len(text):
            if text[j] == "(":
                depth += 1
            elif text[j] == ")":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        if depth != 0:
            raise TwinError(f"drop_hyps: unbalanced parens for {name}")
        # widen to whole line(s) if the binder is alone on them
        ls = text.rfind("\n", 0, i) + 1
        le = text.find("\n", j)
        le = len(text) if le == -1 else le
        if text[ls:i].strip() == "" and text[j + 1:le].strip() == "":
            text = text[:ls] + text[le + 1:]
        else:
            text = text[:i] + text[j + 1:]
        print(f"  drop_hyps: removed ({name} : ...) in {scope}")
    return text


def apply_flip_sites(text, flips):
    for f in flips:
        addr, from_site, to_site = f["addr"], f["from_site"], f["to_site"]
        tail = f["tail_lines"]
        lines = text.splitlines()
        inv = next((k for k, l in enumerate(lines) if from_site in l), None)
        if inv is None:
            raise TwinError(f"flip_sites: from_site {from_site!r} not found")
        cut = next((k for k in range(inv, -1, -1)
                    if lines[k].lstrip().startswith("-- ===")), None)
        if cut is None:
            raise TwinError(f"flip_sites: no step-block comment `-- ===` "
                            f"above the {from_site!r} invocation")
        anorm = addr.lower().removeprefix("0x").lstrip("0")
        window = "\n".join(lines[cut:inv + 3]).lower()
        if anorm not in window:
            raise TwinError(f"flip_sites: addr {addr!r} not found in the "
                            f"step block at line {cut + 1}")
        if not any(to_site in l for l in tail):
            raise TwinError(f"flip_sites: to_site {to_site!r} does not appear "
                            f"in tail_lines")
        text = "\n".join(lines[:cut] + tail)
        if not text.endswith("\n"):
            text += "\n"
        print(f"  flip_sites: cut at line {cut + 1} ({from_site} @ {addr}), "
              f"appended {len(tail)}-line tail ({to_site})")
    return text


def apply_replace(text, repls):
    for i, r in enumerate(repls):
        old, new = r["old_str"], r["new_str"]
        want = r.get("count", 1)
        got = text.count(old)
        if got != want:
            raise TwinError(f"replace[{i}]: old_str found {got} times "
                            f"(need exactly {want}); starts with "
                            f"{old[:60]!r}")
        text = text.replace(old, new)
        print(f"  replace[{i}]: {want} occurrence(s), "
              f"{old[:40]!r}... -> {new[:40]!r}...")
    return text


def sha12(b):
    return hashlib.sha256(b).hexdigest()[:12]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("src")
    ap.add_argument("delta")
    ap.add_argument("-o", "--out", required=True)
    args = ap.parse_args()

    src_path = pathlib.Path(args.src)
    delta_path = pathlib.Path(args.delta)
    src = src_path.read_text()
    delta = json.loads(delta_path.read_text())

    unknown = set(delta) - {"rename", "drop_hyps", "flip_sites", "replace"}
    if unknown:
        raise TwinError(f"unknown delta keys: {sorted(unknown)}")

    print(f"twin_spec: {src_path} + {delta_path} -> {args.out}")
    text = src
    text = apply_rename(text, delta.get("rename", {}))
    text = apply_drop_hyps(text, delta.get("drop_hyps", []))
    text = apply_flip_sites(text, delta.get("flip_sites", []))
    text = apply_replace(text, delta.get("replace", []))

    header = (
        f"-- twin_spec: generated from {src_path} "
        f"(sha256 {sha12(src.encode())})\n"
        f"-- twin_spec: delta {delta_path} "
        f"(sha256 {sha12(delta_path.read_bytes())})\n"
        f"-- twin_spec: do not hand-edit; edit the delta and re-run "
        f"scripts/twin_spec.py\n")
    out = pathlib.Path(args.out)
    out.write_text(header + text)
    print(f"twin_spec: wrote {out} ({(header + text).count(chr(10))} lines)")


if __name__ == "__main__":
    main()
