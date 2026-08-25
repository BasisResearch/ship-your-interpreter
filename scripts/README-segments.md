# gen_segment.py — whole-segment composition emitter

Companion to `gen_sites.py` (see `scripts/README.md`). Where `gen_sites.py`
generates the per-instruction `site_*` StepObs batteries, `gen_segment.py`
generates the **composition ceremony** on top of them: a complete Lean theorem
`tr_<name> : Triple Pre Post` in the Layer-3 house style — per step the
`obtain ⟨σk, ik, hsk, hik, hGk, hmemk, hobsk⟩ := site_…` chain, the mechanical
PC rewrite, **one `pins_*` (RegPins) bundle transport per step** instead of
per-register `obs_*_other` lines, minstret threading, memory threading
(`hmemEk` accumulated-memory equations + code-pin survival `hloadk`), optional
ghost register-frame threading (`hframek`), the `Steps.single/.trans` chain,
and the final postcondition assembly.

Validate outputs with `lake env lean <file>` (never `lake build` — another
process owns the build lock; `lake env lean` checks one file against the
existing build).

## CLI

```
python3 scripts/gen_segment.py SPEC.json --mode straight|prologue|epilogue|call|loop -o OUT.lean
```

`--emit-spec DUMP.json` additionally dumps the expanded core spec that the
`prologue`/`epilogue` front-ends synthesize (useful for debugging or as a
starting point for hand-tweaked straight specs).

## Validated invocations (all exit 0 via `lake env lean`)

```
# 1. straight: generated twin of SnprintfSpec18's tr_setup_mv (7 steps,
#    StMvF0 → AtHeadMv, real proof end-to-end incl. AtHeadMv assembly)
python3 scripts/gen_segment.py scripts/segments/setup_mv.json \
    --mode straight -o /tmp/gen_setup_mv.lean
lake env lean /tmp/gen_setup_mv.lean

# 2. prologue: __ssputs_r frame entry (addi sp,-64; sd s1,40; lw s1,12(a1);
#    sd s0,48; sd ra,56) with inline Pre/Post structures and SlotHolds posts
python3 scripts/gen_segment.py scripts/segments/ssputs_prologue.json \
    --mode prologue -o /tmp/gen_ssputs_prologue.lean
lake env lean /tmp/gen_ssputs_prologue.lean

# 3. epilogue: __ssputs_r frame exit (ld ra,56; ld s0,48; ld s1,40;
#    addi sp,64; ret) fed from SlotHolds via slot_reload_bytes/slot_reassemble
python3 scripts/gen_segment.py scripts/segments/ssputs_epilogue.json \
    --mode epilogue -o /tmp/gen_ssputs_epilogue.lean
lake env lean /tmp/gen_ssputs_epilogue.lean

# 4. call: jal ra,memmove @0x800143c0 composed with memmove_fwd_spec,
#    pins carried across the callee by pins_of_frame; hclose-closed
python3 scripts/gen_segment.py scripts/segments/memmove_callglue.json \
    --mode call -o /tmp/gen_memmove_callglue.lean
lake env lean /tmp/gen_memmove_callglue.lean

# 5. loop: generated twin of SnprintfSpec18's whole loop layer
#    (AtHeadMv_gen/LoopIMv_gen/LoopMuMv_gen/loopmu_head_mv_gen/
#     loop_body_mv_gen/loop_to_done_mv_gen), reusing Spec18's
#    StMv/StMv1c/StMvDone + iterMv/tr_bne_back_mv/tr_bne_done_mv via import
python3 scripts/gen_segment.py scripts/segments/mv_loop.json \
    --mode loop -o /tmp/gen_mv_loop.lean
lake env lean /tmp/gen_mv_loop.lean

# 6. segst boundaries: the setup_mv segment re-emitted with SegSt Pre/Post
#    ("boundary": "segst") — the postcondition assembly is generated
#    completely (no hclose hypothesis, no post_proof spec input, zero holes)
python3 scripts/gen_segment.py scripts/segments/setup_mv_segst.json \
    --mode straight -o /tmp/gen_setup_mv_segst.lean
lake env lean /tmp/gen_setup_mv_segst.lean
```

## Core segment-spec format (`--mode straight` / `--mode call`)

`scripts/segments/setup_mv.json` is the reference example. Top-level fields:

| field | meaning |
|---|---|
| `theorem`, `doc`, `namespace`, `imports` | obvious; imports must include the site battery + `Vsa.Sim.RegPins` |
| `decls` | raw Lean emitted before the theorem (inline Pre/Post structures) |
| `params` | theorem binder groups, one string per line |
| `pre` / `post` | the applied Pre/Post predicates; or `"post_abstract": true` to add a `(Post : Config → Prop)` parameter |
| `loaded_pred` | fully-qualified code byte-pin predicate (e.g. `Vsa.Sim.Code.MemmoveLoaded`) |
| `pre_bind` | the Pre `obtain` pattern plus the names it binds for the standard facts: `good`, `pc`, `minstret_var`/`minstret`, `tick`, `loaded`, and `mem0`/`memeq` (`mem0` is the entry memory expression, usually `m0` with `memeq : c.σ.mem = m0`; use `"mem0": "c.σ.mem"` and omit `memeq` if the Pre pins memory directly). Do **not** name destructured fields `hs0`/`hs1`/… (collides with the step names). |
| `pins` | the tracked register bundle: `{reg, val, hyp}` triples; `hyp` is the Pre hypothesis. Evolving registers (written mid-segment) are handled automatically: the written pin is dropped from the bundle (an `hqk` restriction built from projections), the rest transported by `pins_*`, and the new value re-added at the front. |
| `frame` | optional ghost register frame: `pred` (e.g. `NotWrittenMv`), `rhs` (e.g. `g R`), `init` (Pre hypothesis), and per-class lemma templates `tmpl` (placeholders `$hobs`, `$rd`) |
| `prelude` | raw Lean `have`s after the destructuring (e.g. `hntn`, region-bound extraction) |
| `steps` | see below |
| `post_proof` | raw closing block (with `$`-placeholders); if omitted, the generator emits an **`hclose` hypothesis parameter** instead — the theorem then compiles green with the postcondition assembly abstracted (`hclose : ∀ c, Pre c → ∀ σ' i' u', GoodState σ' → PC → PinsHold σ' [final pins] → ∃ minstret → i' < 2 → [mem eq] → loaded → [frame] → extras → Post ⟨σ', i', u'⟩`). `hclose_extra` adds segment-specific clauses (types may mention `σ'`) fed from named facts (e.g. a callee's `copied`/frame facts). |

### Step dicts

Site step classes: `alu` (covers ALU ops **and** loads — their post is
`sigmaPost_alu`), `sd`/`sw`/`sb`, `btaken`, `bnottaken`, `jal`, `jr`, `j`.

```json
{"addr": "0x800069fc", "site": "site_69fc", "class": "alu",
 "rd": "x13", "rd_val": "(BitVec.ofNat 64 (n-1))",
 "rw": "dec1_fwd n hn1 (by omega)",
 "pre_lines": ["have hguard$k : ... := ..."],
 "call": "$vmi (BitVec.ofNat 64 n) (BitVec.ofNat 64 (n-1)) $hG $hpc $hmi $pin:x12 (dec1_fwd n hn1 (by omega)) $hmem rfl $hi"}
```

- `call` is the full site-argument tail after the auto-prepended
  `site σprev iprev (uexpr) (0xADDR#64)`; this is what lets the emitter drive
  *hand-written* site batteries with idiosyncratic signatures (Spec18) as well
  as `gen_sites.py`-uniform ones (SsputsSites).
- `rd`/`rd_val`/`rw`: the written register, its post value **after** the
  optional `rwa [rw] at this` value rewrite. `rd_val` becomes the register's
  new bundle pin (set `"track_rd": false` to drop instead).
- branches/jumps: `btaken`/`j`/`jal` need `imm` (`0x0030#13` / `0x1f2604#21`)
  and `target`; the PC rewrite is emitted as an inline
  `show pc + sext imm = tgt from by apply BitVec.eq_of_toNat_eq; decide`.
  `jr` needs `pc_val` + `pc_rw` (e.g. `ret_tgt r halign`). `jal` derives the
  link value/rewrite automatically.
- stores: `key` (normalized Nat key expression), `key_rw` (the `hkey*`
  rewrite lemma, usually emitted in `prelude`), `src_val`, optional `data_rw`
  (`sb`: `stData_zext`), and `loaded_via` — the code-pin survival term with
  `$prev` standing for the previous loaded fact transported to the
  accumulated memory expression (e.g.
  `"ssputs_writeMap8_ss _ _ _ (by omega) $prev"`).

Placeholders use a `$` sigil (`@` collides with Lean explicit application):
`$sigma $tick $u $vmi $hG $hpc $hmi $hmem $memeq $hi $k $pin:xN $v:xN`
(`$pin:xN` = bundle projection for register xN at the previous state,
`$v:xN` = its current tracked value expression, `$memeq` = `hmemE(k-1)`).

### Call steps (`--mode call`)

```json
{"class": "call", "callee": "memmove_fwd_spec",
 "args": "(fun R => $sigma.regs.get? R) (0x800143c4#64) d s n m0 bs (by decide)",
 "pre_fields": ["$hG", "...", "$pin:x10", "hrd1", "⟨$vmi, $hmi⟩", "..."],
 "post_obtain": "⟨hGc, hpcc, hx10c, hx1c, hcopied, hmemfr, htickc, hregfr⟩",
 "post_good": "hGc", "post_pc": "hpcc", "post_tick": "htickc",
 "pc_val": "((0x800143c4#64) : BitVec 64)",
 "pins_drop": ["x11"], "pins_add": [],
 "write_set": ["x11","x13","x14","x15","PC","nextPC","minstret",
               "minstret_increment","mcycle","mtime","mip"],
 "frame_hyp": "hregfr",
 "loaded_lines": ["have hload$k : ... := ssputs_frame_ss ..."]}
```

The callee is instantiated with `g := fun R => σcall.regs.get? R` (so its
Pre frame field is `fun R _ => rfl`); clobbered pins are dropped, the rest
carried across the whole call by a single `pins_of_frame` with the generated
`⟨hn Register.x11 (by decide), …⟩` adapter from the callee's `NotWrittenX`
tuple (`write_set` must list the tuple's registers **in tuple order**).
Minstret is recovered from `GoodState.minstret`. `hmemEk` tracking stops at a
call unless `mem_expr`/`mem_lines` are given; `loaded_lines` (and
`frame_lines` when a ghost frame is configured) are required raw blocks.

## `--mode loop` — whole `Triple.loop` instantiation

`scripts/segments/mv_loop.json` is the reference example (a generated twin
of SnprintfSpec18's loop layer).  Where the other modes emit one segment
theorem, loop mode emits the complete six-declaration loop layer in the
`StrcpySpec`/`SnprintfSpec18` house shape:

| emitted | role |
|---|---|
| `at_head` def | the loop guard `B`: `∃ i, i < bound ∧ head(i) c` |
| `loop_inv` def | the invariant `I`: `at_head ∨ done` |
| `loop_mu` def | the measure: `2^64 - ((regs.get? mu_reg).getD 0).toNat` |
| `loopmu_head` thm | at head iteration `i`, `loop_mu = mu_expr(i)` |
| `loop_body` thm | one iteration re-establishes `I` strictly decreasing `loop_mu` |
| `loop_to_done` thm | `Triple loop_inv done` via `Triple.loop` + the exit `absurd` |

Loop-spec JSON fields (`$i`/`$hlt`/`$heq` placeholders are substituted with
the bound iteration variable / branch facts):

| field | meaning |
|---|---|
| `params`, `args` | shared binder lines and their application string (`"g r dst src n m0 bs"`) |
| `names` | the six emitted declaration names (`at_head`, `loop_inv`, `loop_mu`, `loopmu_head`, `loop_body`, `loop_to_done`) |
| `head` / `done` | the head state applied at `$i` (`"StMv g $i r …"`) / the done state |
| `body_lemma` | `Triple head($i) → pre-branch-state` (`"iterMv g $i r …"`) |
| `back_lemma` | the `i+1 < bound` branch (`"tr_bne_back_mv g $i … $hlt"`) |
| `done_lemma` | the `i+1 = bound` branch (`"tr_bne_done_mv g $i … $heq"`) |
| `bound` | the iteration bound expression (`"n"`) |
| `mu_reg` / `mu_field` / `done_mu_field` | measure register; the head/done structure fields pinning it (`"x15"`, `"a5"`) |
| `mu_expr` / `mu_done_expr` | measure value at head `$i` / at done (`"2^64 - (dst.toNat + $i)"`) |
| `mu_head_proof` / `mu_done_proof` | proof lines closing the measure equations after the emitted `simp only [loop_mu, hSt.mu_field, Option.getD_some]` (`hSt`/`hD` and `i` are in scope) — typically one `ptr_toNat` rewrite |
| `body_prelude` | facts hoisted into `loop_body` for the final `omega`s (e.g. `have hnw := hSt.regions.dst_nowrap`) |

Assumed loop shape (the Spec18/StrcpySpec byte-loop shape): strict head
existential (`i < bound`), guard `B` = `at_head` itself, exit through the
body's `i+1 = bound` branch.  The head/done state records, the body-iteration
lemma, and the two branch lemmas stay hand-written (or come from the site
battery) — loop mode consumes them by name; nothing else is left open.
Hand-written residue in the spec: the two measure-equation rewrite lines and
`body_prelude`.

## `"boundary": "segst"` — SegSt-standardized boundaries (straight mode)

`scripts/segments/setup_mv_segst.json` is the reference example.  With
`"boundary": "segst"` the generated theorem's Pre and Post are `SegSt`
instances (`Vsa/Sim/SegState.lean`): `SegSt pcv L P` with pins list `L` and
payload `P = fun σ => <loaded_pred> σ.mem ∧ σ.mem = <mem> ∧ [frame blanket]`.
This kills the `post_proof` hole: `pre`, `post`, `pre_bind`, and the whole
closing assembly are synthesized —

* the Pre is destructured mechanically
  (`⟨hgood, hpc, hp0, ⟨vmi, hmi⟩, htick, ⟨hloaded, hmemeq[, hframe]⟩⟩`);
* the Post's pins list, end PC, and memory expression are computed by the
  step threading (the same `hp<k>`/`hmemE<k>`/`hload<k>`/`hframe<k>` chain);
* the final `exact ⟨cfg, hsteps, ⟨hG, hpc, hp, ⟨vmi, hmi⟩, hi,
  ⟨hload, hmemE[, hframe]⟩⟩⟩` is emitted complete — zero holes, no `hclose`.

Spec changes vs plain straight: add `"boundary": "segst"`, `"entry"` (the
pre PC), optionally `"mem_param"` (Pre memory name, default `"m0"`; must be a
theorem parameter); drop `pre`/`post`/`pre_bind`/`post_proof`; pins need only
`reg`/`val` (no `hyp` — projections come from the SegSt pins bundle); pure
ghosts that lived in a bespoke Pre record (`MvRegions`-style) become theorem
parameters (`"(hreg : MvRegions dst src n)"`); imports must include
`Vsa.Sim.SegState`.  The `frame` (if configured) folds into the payload as
the third conjunct.

Limits (enforced): straight-line only — no call steps (memory/loaded
threading after a call is segment-specific), and the accumulated memory
expression must be parameter-level (no `c.σ` mentions; lift store values to
parameters).  For the setup_mv acceptance segment nothing had to be left as
a hypothesis — the post is fully auto-assembled.  Published-interface
consumers that want a bespoke named record can bridge with one
`segst_of_*`/`*_of_segst` pair (see `SegState.lean`'s `StMvF0` bridge).

## Prologue / epilogue frame-table format

`scripts/segments/ssputs_prologue.json` / `ssputs_epilogue.json` are the
reference examples. These front-ends synthesize a full core spec (inspect with
`--emit-spec`): inline `Pre`/`Post` structures over the theorem parameters,
the mechanical pointer prelude (`htoh`, `hspN` via `ptr_sub_toNat` +
`sext_fc0_toNat`-style constants, per-offset `hkey<off>` via `ptr_addoff` —
all PtrArith, kernel-recursion-safe), the step list, and the closing proof.

Prologue: `frame_size` K, `sp_dec` site, `saves` `[{addr, site, reg, off}]`
(offsets decimal), optional interleaved `extra_steps` (full core step dicts —
the `lw s1,12(a1)` in the `__ssputs_r` prologue is the worked example,
including generated-name byte-pin transports across the earlier `sd` via
`getElem_writeMap8_disjoint`), `extra_pins`/`extra_params`/`pre_extra`/
`extra_prelude` for their supporting facts. Post = end-PC + final register
pins + one `SlotHolds (sp+sext(-K)) off v` per spill (built by
`slot_save` wrapped in `slot_survives_writeMap8` for each later spill) + the
explicit three-store memory image + minstret/tick.

Epilogue: `reloads` `[{addr, site, reg, off, var}]` (the `x1` reload's `var`
doubles as the return address; Pre carries `ra_align`), `sp_inc`, `ret`.
Each reload's byte hypotheses are fed from the Pre's `SlotHolds` via
`slot_reload_bytes`, and the loaded value collapses by `rw [slot_reassemble v]`.
The `ret` closes with `ret_tgt`. Post = `PC = r`, sp restored to
`vspd + sext K` (raw form; compose with `sp_decK_restore` upstream if the
entry sp is literally `vsp + sext(-K)`), reloaded registers, `mem = m0`.

## What stays hand-written (value annotations)

Everything mechanical is emitted complete; the residual hand-written inputs
in a spec are exactly:

1. **Branch-guard facts** (`pre_lines`): e.g. `bltu_false_of_ge`/`beq_false_of_toNat_ne` derivations from region bounds.
2. **Value rewrites** (`rw`): `li31_val`, `sext0_add`, `dec1_fwd/back`, `ptr_succ`, `slot_reassemble` — one lemma application per rewritten rd.
3. **Store-key normalizations** (`key_rw` lemmas) — auto-generated by the prologue/epilogue front-ends, hand-named in straight mode.
4. **Code-pin survival for stores** (`loaded_via`) — one survival-lemma template per code region.
5. **Callee glue** (`pre_fields`, `post_obtain`, `loaded_lines`) — the callee's Pre is supplied field-by-field (most fields are `$pin:`/standard placeholders).
6. **The final postcondition assembly** (`post_proof`) — or nothing, in which case it becomes the `hclose` hypothesis parameter and the theorem still compiles green; or **eliminated entirely** with `"boundary": "segst"` (SegSt Pre/Post, assembly fully generated — see above).

## Template gaps / known limits

- A segment must **start with a site step** (not a call), and only one
  destructuring shape per Pre (`pre_bind.obtain` is a single pattern).
- `hmemE` tracking is linear: after a call step without `mem_expr`, later
  store steps can't thread memory (re-establish it by hand via `mem_lines`).
- The `hclose` memory clause is only emitted when the accumulated memory
  expression does not mention `c` (i.e. `mem0` is a parameter like `m0`).
- No `obs_*_other` fallback path was needed: pins-based emission reproduced
  every exemplar step class (alu incl. loads, sd, bnottaken, jal, jr) on the
  real code; `btaken`/`j`/`sw`/`sb` share the same machinery but were not
  exercised by an acceptance test.
- Byte-pin transports for loads inside prologues are spelled per-byte in the
  spec (`hbt$k_j` pattern); a `Pin4`/`Pin8`-based shorthand would shrink
  those specs further.
- Interleaved `extra_steps` in a prologue must not write memory (the
  `SlotHolds` nesting assumes only the `sd` spills touch it).
- `pinsAvoid` side conditions close by `(by rfl)` — keep noise registers and
  callee write-sets out of the pin list, or generation succeeds but the file
  fails; the emitter does not currently pre-check this statically.

## Generated-name conventions (for `post_proof` / debugging)

Per step `k`: `σk ik hsk hik hGk hmemk hobsk` (site obtain), `hpck` (PC),
`hrdk` (written register), `hqk`/`hpk` (restricted / new pin bundle),
`vmik hmik` (minstret), `hmemEk` (accumulated memory equation), `hloadk`
(code predicate), `hframek` (ghost frame), `hstepsN` (final Steps chain);
call steps bind `ck hcsk hcpk` and re-export the standard names.

## `"guard": "decide"` — inline guards for concrete-operand branches

Branch steps whose operands are **concrete at spec time** (constant
registers / immediate data — e.g. the `%lld` parse-loop tests over known
format-string bytes, where a register is pinned to a literal) don't need a
`pre_lines` guard derivation: set `"guard": "decide"` on the step and put
`$guard` where the site's `hv` argument goes — it expands to `(by decide)`
inline.

```json
{"addr": "0x80008338", "site": "site_80008338_taken_sn", "class": "btaken",
 "imm": "0x1fc4#13", "target": "0x800082fc",
 "guard": "decide",
 "call": "$vmi (0#64) $hG $hpc $hmi $pin:x27 $hmem rfl $guard $hi"}
```

Guard rails: `$guard` without the option (or the option without `$guard`,
or on a non-branch class) is a spec error. Validated with the segment above
(the `beqz s11` grouping-flag test from `SnprintfSites.lean`, `s11` pinned
to `0#64`, `"boundary": "segst"` — the same guard the hand proof in
`SnprintfSpec5.lean` closes with a literal `(by decide)`): generated and
compiled green via `lake env lean`. All six validated invocations at the
top of this file regenerate **byte-identically** after this change.

## TODO gate (drafts from disasm_to_segment.py)

gen_segment.py now refuses to run a spec whose JSON contains `TODO`
anywhere (it lists the offending lines). `scripts/disasm_to_segment.py`
(see `scripts/README-disasm.md`) emits draft specs with every
hand-annotation slot spelled `TODO(...)`, so an unfinished draft cannot
silently generate a broken theorem. The validated specs in
`scripts/segments/` contain no `TODO` and are unaffected.
