# scripts/ — durable proof tooling

Generators that previous sessions kept recreating as throwaways in `/tmp`.
Keep them here; regenerate outputs instead of hand-editing.

## gen_decode_index.py → decode_index.tsv

Maps every instruction word to the `Vsa/Sim/DecodeTable/BatchNNPartMM.lean`
module that proves its `decode_<word>` lemma. Spec/site files must import that
Batch part **directly** (the aggregate `BatchNN.lean` files are too heavy);
this index makes finding the right import mechanical.

```
python3 scripts/gen_decode_index.py        # rewrites scripts/decode_index.tsv
```

Format: `<word-hex8>\t<module>`, sorted by word, one line per decode lemma
(~8250 entries). Sanity anchors checked on regeneration:
`00008067 -> Batch01Part04`, `fc010113 -> Batch16Part01`.

## gen_sites.py — site-battery generator

Emits a Lean file of per-site `StepObs` theorems in the house style of the
proven batteries `Vsa/Sim/SsputsSites.lean` and the sites section of
`Vsa/Sim/SnprintfSpec18.lean`. Input is a TSV, one site per line
(`#` comments and blank lines ignored):

```
<addr-hex>  <word-hex>  <class>  <operand fields...>
```

Classes (registers decimal, immediates hex; see the script docstring for the
full list): `alu_addi rd rs1 imm12`, `addiw rd rs1 imm12`,
`alu_add rd rs1 rs2`, `sub rd rs1 rs2` (64-bit RTYPE SUB,
`execute_rtype_sub_char` — ground truth `site_8000e98c_sr` in
`SnprintfSpec20.lean`), `subw rd rs1 rs2`,
`branch_taken|branch_nottaken bop rs1 rs2 imm13` (bop in
BEQ/BNE/BLT/BGE/BLTU/BGEU), `ld|lw|lbu rd rs1 imm12`, `sd|sw|sb rs2 rs1 imm12`,
`jal rd imm21`, `j imm21`, `jr rs1`.

The generator computes the little-endian byte pins from each word, looks up
each word's DecodeTable module in `scripts/decode_index.tsv`, and emits a
deduplicated sorted import list plus the standard header (opens,
`maxHeartbeats`/`maxRecDepth`, namespace). `--code-loaded` names the
byte-pin predicate from a `Vsa/Sim/Code/*.lean` file; the accessor prefix and
code-module import are derived from it (`Vsa.Sim.Code.MemmoveLoaded` ->
`Vsa.Sim.Code.memmove_at_<addr>` / `import Vsa.Sim.Code.Memmove`; override
with `--code-accessor` / `--code-import`). `--suffix` disambiguates theorem
names (`site_<addr>[_taken|_nottaken]<suffix>`); `--namespace` defaults to
`Vsa.Sim`.

### Self-test (acceptance)

`scripts/selftest_sites.tsv` lists four newlib-memmove sites whose hand-proven
counterparts are in `SnprintfSpec18.lean`:

```
python3 scripts/gen_sites.py scripts/selftest_sites.tsv \
    --code-loaded Vsa.Sim.Code.MemmoveLoaded --suffix _gen \
    -o /tmp/selftest_sites.lean
lake env lean /tmp/selftest_sites.lean     # must exit 0
```

(Do not `lake build` for this; `lake env lean` checks a single file against
the existing build.)

## disasm_to_sites.py / disasm_to_segment.py — disassembly front-ends

The final mechanical layer: `riscv64-elf-objdump` range → gen_sites.py TSV
(`disasm_to_sites.py`), and sites TSV → draft gen_segment.py spec with
def-use-computed pins and `TODO`-marked value annotations
(`disasm_to_segment.py`). See `scripts/README-disasm.md`.
`scripts/ssputs_sites.tsv` is the checked-in acceptance TSV
(`__ssputs_r` 0x8001438c–0x800143f4, twin of the proven `SsputsSites.lean`).

## Related generators (history, recorded in memory notes)

- `experiments/gen_code_lemmas.py` — generates the `Vsa/Sim/Code/*.lean`
  byte-pin files (`<fn>Loaded` predicate + chunk lemmas + per-address
  `<fn>_at_<addr>` accessors) that `--code-loaded` points at.
- `experiments/gen_decode_table.py` — generated the DecodeTable batches.
- `experiments/gen_envget_sites.py` — earlier one-off site generator that
  `scripts/gen_sites.py` supersedes.
- `scripts/decode_index.tsv` — word -> DecodeTable module (this directory).
