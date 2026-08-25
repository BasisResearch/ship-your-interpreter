# disasm_to_sites.py / disasm_to_segment.py — disassembly → generator inputs

The final mechanical layer of the tooling chain:

```
objdump range ──disasm_to_sites.py──▶ site TSV ──gen_sites.py──▶ site battery (.lean)
                                        │
                                        └──disasm_to_segment.py──▶ DRAFT segment JSON
                                                                   ──(fill TODOs)──▶
                                                                   gen_segment.py ──▶ tr_* theorem
```

Validate outputs with `lake env lean <file>` (never `lake build` — another
process owns the build lock).

## disasm_to_sites.py — disassembly → gen_sites.py TSV

```
python3 scripts/disasm_to_sites.py 0xLO 0xHI \
    [--elf c/while-riscv-htif.elf] [--objdump riscv64-elf-objdump] \
    [--path BRANCHES.txt] [-o OUT.tsv]
```

Runs `riscv64-elf-objdump -d --start-address/--stop-address` on the ELF and
classifies every instruction into gen_sites.py's site classes. Classification
is from the **instruction word** (opcode/funct3/funct7), not objdump's text —
pseudo-ops (`mv`, `li`, `sext.w`, `beqz`/`bnez`/…, `j`, `ret`) land in the
right class automatically, and the emitted operand fields are guaranteed to
agree with the encoding gen_sites.py re-derives byte pins from. objdump's
text survives as a trailing `#` comment on every row.

* **Branches**: both arms are emitted by default (taken first, with a
  `# branch:` note above) — delete the dead arm; or pass `--path FILE` with
  `<addr-hex> taken|nottaken` lines to pick per branch address. (Both arms
  *compile*; keeping both is fine for a battery, but disasm_to_segment.py
  requires exactly one arm per branch.)
* **Unsupported mnemonics** (`lh`, `sh`, shifts, non-`ret` `jalr` shapes, …)
  and gen_sites-side operand restrictions visible statically (rd=x0 ALU ops
  such as `nop`, x0-operand loads, rs1=x0 stores) become
  `#UNSUPPORTED <addr> <word> <raw disasm> [reason]` comment lines —
  gen_sites.py skips them, the gap stays visible in the TSV.

### Acceptance (validated)

`scripts/ssputs_sites.tsv` is the checked-in output for the whole of
`__ssputs_r` (the range whose per-site battery was hand-proven in
`Vsa/Sim/SsputsSites.lean`):

```
printf '800143a8 nottaken\n' > /tmp/ssputs_path.txt
python3 scripts/disasm_to_sites.py 0x8001438c 0x800143f4 \
    --path /tmp/ssputs_path.txt -o scripts/ssputs_sites.tsv
```

All 26 rows (addr/word/class/operands) match the proven `SsputsSites.lean`
sites one-for-one (`site_1438c_sp` … `site_143f0_sp`, incl. the
`bgeu` NOT-taken arm, `sext.w → addiw`, `mv`/`li → alu_addi`,
`jal 1 1f2604 → memmove`, `ret → jr 1`). A full battery generated from the
both-arms output (27 sites) compiles:

```
python3 scripts/disasm_to_sites.py 0x8001438c 0x800143f4 -o /tmp/ssputs_both.tsv
python3 scripts/gen_sites.py /tmp/ssputs_both.tsv \
    --code-loaded Vsa.Sim.Code.__ssputs_rLoaded --suffix _dg \
    -o /tmp/ssputs_dg_sites.lean
lake env lean /tmp/ssputs_dg_sites.lean     # exit 0
```

### The `sub` class (added to gen_sites.py alongside this tool)

gen_sites.py now supports 64-bit RTYPE SUB (`sub rd rs1 rs2`), modeled on
`alu_add` with `execute_rtype_sub_char`; ground truth is the hand-written
`site_8000e98c_sr` in `Vsa/Sim/SnprintfSpec20.lean` (word `41270733`,
`sub a4,a4,s2`). Validated:

```
printf '8000e98c\t41270733\tsub\t14\t14\t18\n' > /tmp/sub_site.tsv
python3 scripts/gen_sites.py /tmp/sub_site.tsv \
    --code-loaded Vsa.Sim.Code.__ssprint_rLoaded --suffix _subgen \
    -o /tmp/sub_site.lean
lake env lean /tmp/sub_site.lean            # exit 0
```

and the pre-existing selftest (`scripts/selftest_sites.tsv`) regenerates
byte-identically and still compiles.

## disasm_to_segment.py — sites TSV → DRAFT segment JSON

```
python3 scripts/disasm_to_segment.py 0xLO 0xHI --sites SITES.tsv \
    [--theorem tr_foo] [--loaded-pred Vsa.Sim.Code.XLoaded] \
    [--site-suffix _gen] [--imports M1,M2] [-o DRAFT.json]
```

Consumes the classified rows (exactly one arm per branch — it errors on
double-arm rows) and emits a gen_segment.py `--mode straight` core spec
draft. What it computes vs what it leaves as `TODO(...)`:

**Computed (mechanical):**

* the step list in address order — gen_segment class, gen_sites site name,
  addr; branch `imm`/`target` for taken arms; jal link value (implicit);
  `j`'s alignment side condition as `(by decide)` (the PC is a literal);
* def-use over the operands: registers **read before written** become the
  initial `pins` (ghost values auto-named `v<reg>`, hyps `hv<reg>`, plus the
  `(v<reg> : BitVec 64)` binder line and `m0`); **written** registers get
  per-step `rd` entries — gen_segment's drop/re-add pin choreography then
  runs off `rd`/`rd_val` automatically;
* the site-call argument tails in the gen_sites-uniform signature order,
  with `$v:xN`/`$pin:xN` placeholders for every register the bundle will
  track at that step (initial pins *and* earlier-written registers — those
  resolve once their `rd_val` TODOs are filled);
* the standard `pre_bind` names (good/pc/minstret/tick/loaded/mem0/memeq).

**Left `TODO` (the hand annotations documented in README-segments.md):**

* `rd_val`/`rw` per written register (ghost-level value + rewrite lemma;
  the machine-level expression is carried in an informational `raw_val` key);
* branch guard facts (`pre_lines` skeleton feeding `hguard$k`; for
  concrete-operand branches switch to `"guard": "decide"` + `$guard`);
* load byte values/hypotheses and region side conditions
  (`b<j>`/`hlo/hhiram/hhtif/halign/h<j>` slots in the call);
* store `key`/`key_rw`/`loaded_via` + the four in-call side conditions;
* the callee glue: after a `jal`, a whole `class: call` placeholder step;
* `jr`'s `pc_val`/`pc_rw`/`htgt`;
* `pre`/`post`/`post_proof`, the bespoke tail of `pre_bind.obtain`, the
  battery import, extra ghost binders, `prelude` facts, any `frame` config.

Every placeholder is spelled `TODO(...)`, and **gen_segment.py refuses to
run any spec containing `TODO`** (it lists the offending lines), so a draft
cannot silently generate a broken proof.

### Acceptance measurement (draft vs the validated `setup_mv.json`)

```
printf '800069f4 nottaken\n80006a00 nottaken\n' > /tmp/mv_path.txt
python3 scripts/disasm_to_sites.py 0x800069f0 0x80006a0c \
    --path /tmp/mv_path.txt -o /tmp/setup_mv_sites.tsv
python3 scripts/disasm_to_segment.py 0x800069f0 0x80006a0c \
    --sites /tmp/setup_mv_sites.tsv --theorem tr_setup_mv_draft \
    --loaded-pred Vsa.Sim.Code.MemmoveLoaded -o /tmp/setup_mv_draft.json
```

Field-by-field against `scripts/segments/setup_mv.json` (the hand-annotated,
compile-validated spec):

| field | draft got right | needed hand annotation |
|---|---|---|
| steps: count/order/addr | 7/7 | — |
| steps: class | 7/7 (alu ×5, bnottaken ×2) | — |
| steps: site names | gen_sites convention (`site_800069f0`) | Spec18 drives a *hand-written* battery (`site_69f0`, idiosyncratic short names) — rename per battery |
| steps: `rd` (written reg) | 5/5 (x15,x15,x13,x13,x13) | — |
| steps: `rd_val`/`rw` | 0/5 values (raw machine expr supplied as `raw_val`) | all 5 ghost-level values + 4 rewrites (`li31_val`, `sext0_add`, `dec1_fwd`, `dec1_back`; the `add` needs none) |
| steps: call tails | steps 1,3,5,7: shape identical to the hand spec modulo ghost naming (`$v:x10` vs `dst`); hyp lists (`$pin:`) exact on all 7 | steps 2,4,6 drive Spec18's idiosyncratic hand-site signatures (extra value/proof args like `(dec1_fwd n hn1 (by omega))`) — the draft's tails fit the *gen_sites-uniform* signature instead |
| steps: guard plumbing | 2/2 branches get `pre_lines` skeleton + `hguard$k` in the call, exactly where the hand spec has them | both guard derivations (`bltu_false_of_ge …`, `beq_false_of_toNat_ne …`) |
| pins | x12, x10 — exactly the segment's read-before-written set; hyp/binder plumbing complete | x11, x1 (pinned in the hand spec only because the *postcondition* needs them — invisible to intra-segment def-use); ghost values `v12/v10` vs meaningful `BitVec.ofNat 64 n`/`dst` |
| pre_bind | 7 standard slots auto-named | the bespoke obtain tail (`hreg, hbs, hframe` etc.) |
| loaded_pred, namespace, m0 param | from CLI / defaults | — |
| imports | `Vsa.Sim.RegPins` | the battery module |
| pre/post/post_proof, prelude, frame, extra params | — | all (segment-specific; or switch the draft to `"boundary": "segst"` to synthesize pre/post/pre_bind/post_proof) |

Honest summary: the draft mechanizes the step skeleton, def-use pin
choreography, and call-tail shapes completely (21 `TODO` slots remain on
this 7-step segment, all in the documented hand-annotation categories); it
does **not** see postcondition-motivated pins, ghost-level value names, or
guard/store lemma content.
