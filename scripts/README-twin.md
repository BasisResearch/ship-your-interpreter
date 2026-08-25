# twin_spec.py — checked variant emitter for verified segments

A recurring Layer-3 cost: a verified segment spec needs a *twin* — the same
statement and step battery with a small, well-understood delta. Real
exemplars:

- `Vsa/Sim/SnprintfSpec46.lean` from `SnprintfSpec7.lean`: statement + proof
  steps 1–16 verbatim, the `beqz t5` seam at `0x8000812c` flipped
  nottaken→taken, post value `a6 = len` instead of `len+1`, new 6-step tail.
- `Vsa/Sim/SnprintfSpec44.lean` from `SnprintfSpec8.lean`: same statement with
  the `hmag` hypothesis removed and a case-split body.

`scripts/twin_spec.py` makes this a **checked** source-to-source
transformation: every edit in the JSON delta must match the source exactly, or
the tool aborts without writing anything. When the source spec is later
edited, re-running the delta either reproduces the twin or fails loudly — no
silent drift.

## Usage

```sh
python3 scripts/twin_spec.py SRC.lean DELTA.json -o OUT.lean
```

## Delta JSON

```json
{
  "rename":    {"exitToPrint_spec": "exitToPrintNN_spec"},
  "drop_hyps": ["hfoo",
                {"name": "hmag", "in_theorem": "entryToPrint_neg_any_spec"}],
  "flip_sites": [{"addr": "0x8000812c",
                  "from_site": "site_8000812c_nottaken_fl",
                  "to_site":   "site_8000812c_taken_fs",
                  "tail_lines": ["  -- name aliases for the seam threading",
                                 "  ...", "end Vsa.Sim", ""]}],
  "replace":   [{"old_str": "exact text in the (renamed) source",
                 "new_str": "replacement", "count": 1}]
}
```

Applied in this order (so write `drop_hyps`/`flip_sites`/`replace` entries in
the **post-rename** vocabulary):

1. **rename** — whole-word rename of theorem/def/hypothesis names. Each old
   name must occur ≥ 1 time (count reported).
2. **drop_hyps** — remove the paren-balanced binder `(name : ...)`. Each name
   must occur exactly once — either in the whole source (string form) or
   inside the named theorem's declaration (object form with `in_theorem`).
   Statement-only: if the *proof* mentions the hypothesis, patch it with
   `replace` entries or a `flip_sites` tail.
3. **flip_sites** — the seam flip. Finds the first invocation of `from_site`,
   walks up to the step-block comment (`-- ===`) that opens that step, checks
   `addr` appears there, truncates from that comment **to EOF**, and appends
   `tail_lines` verbatim (`to_site` must appear in them; the tail must close
   any namespaces, i.e. end with `end Vsa.Sim`).
4. **replace** — exact-string replacement; occurrence count must equal
   `count` (default 1).

The output starts with a provenance header (`-- twin_spec: generated from …`
with sha256 prefixes of the source and the delta). Do not hand-edit a twin;
edit the delta and re-run.

## Failure = the feature

Any of these aborts with a nonzero exit and **no output file**:

- a `rename` old name / `replace` old_str not found, or found the wrong
  number of times;
- a `drop_hyps` binder absent or ambiguous (e.g. `hmag` appears in two
  theorems of `SnprintfSpec8.lean` — you must scope it with `in_theorem`);
- a `flip_sites.from_site` invocation missing, its step comment missing, the
  `addr` not matching that block, or `to_site` absent from the tail.

## Recorded deltas (`scripts/deltas/`)

- `spec46_from_spec7.json` — reproduces `SnprintfSpec46.lean` from
  `SnprintfSpec7.lean`. Acceptance run (2026-08-25):
  `python3 scripts/twin_spec.py Vsa/Sim/SnprintfSpec7.lean
  scripts/deltas/spec46_from_spec7.json -o /tmp/twin_spec46.lean` produces a
  file whose 917 non-provenance lines are **line-identical (100%)** to the
  committed `SnprintfSpec46.lean`. Honest accounting: 646 of those lines
  (statement + steps 1–16) are derived from Spec7 by rename + 3 checked
  replaces (preamble/imports swap, `hsbne`→`hsbz`, the `x16` post value); the
  remaining 271 lines are the recorded hand tail (steps 17–22 + post),
  carried in the delta's `tail_lines` — the tool guarantees the *seam* and
  the *head*, not the new proof work.
- `fnfmt_from_lldfmt.json` — a NEW twin: `Vsa/Sim/Code/FnFmt.lean`
  (`FnFmtLoaded`, `fnFmtChunk0`, `fnFmt_bytes`) from `Code/LldFmt.lean`:
  the `"<fn %s>"` closure-stringify format string at `.rodata 0x800192c8`
  (`interp.c:97`, `snprintf(buf, sizeof buf, "<fn %s>", name)`), bytes
  `3c 66 6e 20 25 73 3e 00` verified against
  `riscv64-elf-objdump -s c/while-riscv-htif.elf`. Compiles green via
  `lake env lean Vsa/Sim/Code/FnFmt.lean`; axioms
  `[propext, Classical.choice, Quot.sound]`. This is the pin module the
  future M4 closure-printing arm consumes, exactly as the int arm consumes
  `LldFmtLoaded`.

## Related tooling

- `scripts/pro_emitter/gen_spec46.py` — the bespoke one-off this tool
  generalizes (kept for provenance).
- `scripts/gen_image_pins.py` — generates `Vsa/Sim/Code/ImageStatics.lean`
  (the `ImageStaticsLoaded` static-data pins) + `Vsa/Sim/ImageDischarge.lean`
  (one lemma per capstone static-image hypothesis), with every byte
  cross-checked against the ELF.
