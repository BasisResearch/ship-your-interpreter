# Mechanical PC-trace of the embedded WHILE ELF (2026-08-24)

A ~150-line pure-python RV64IM interpreter over `c/while-riscv-htif.elf`
(program headers → memory image; HTIF console = tohost byte writes with
`(b>>56)&0xff == 1`, exit = odd payload). Validated: runs the stock embedded
script in **exactly 382,730 steps** — the documented reference count.

The embedded WHILE script sits at file offset 0x19be0 = vaddr 0x80018be0
(`src/script.S` incbin, NUL-terminated); patch bytes in the memory image to
run any workload. `println("" + (0 - 9876543210123));` produces
`-9876543210123\n` and exercises `stringify` → `snprintf("%lld")`
(interp.c:94). Set-subtracting a `var x = 1;` run isolates the footprint.

## Definitive `snprintf("%lld", negative)` executed footprint — 490 instrs

  [0x8000739c, 0x80007498)  (63)   interp stringify + snprintf/vsnprintf wrappers
  [0x80007654, 0x800077c0)  (91)   svfprintf prologue + parse      ← pinned
  [0x8000782c, 0x80007a10)  (121)  parse loop + PRINT/CHECK macros ← pinned (ends 0x7a00: tail 4 instrs unpinned!)
  [0x80007cd4, 0x80007ce4)  (4)    conv-char dispatch hop          ← unpinned
  [0x80008008, 0x80008020)  (6)    'd' handler entry               ← pinned
  [0x80008088, 0x80008138)  (44)   sign block + split (VERIFIED Spec4/6 region)
  [0x800082c8, 0x80008398)  (52)   digit loop + exit restore (VERIFIED Spec3/5 + 8358-8394 exit)
  [0x80008534, 0x80008540)  (3)    hop
  [0x80008678, 0x8000868c)  (5)    hop
  [0x80009060, 0x80009070)  (4)    hop
  [0x8000a830, 0x8000a83c)  (3)    no-pad shortcut → j 0x782c      ← unpinned
  [0x8000e908, 0x8000e9cc)  (49)   __ssprint_r fast path (have Code file)
  [0x80010234, 0x80010260)  (11)   helper (likely memchr/strlen bits)
  [0x80012268, 0x80012288)  (8)    helper
  [0x8001438c, 0x800143f4)  (26)   memcpy/memmove core (MemcpySpec machinery exists)

Already verified end-to-end: sign block → split → entry → digit loop → exit
at 0x80008358 (SnprintfSpec3–6, with DigitFrame/EntryFrame memory frames and
the '-' byte surviving at sp+167). Remaining for the composed snprintf_lld_spec:
~340 instructions, of which ~120 (parse loop) run BEFORE the verified part.

## Flush part 2 site/spec plan (next session)

1. Regenerate `Code/SvfprintfSlice.lean` ranges to cover the unpinned bits:
   add [0x80007a00,0x80007a10), [0x80007cd4,0x80007ce4), [0x80008534,0x80008540),
   [0x80008678,0x8000868c), [0x80009060,0x80009070), [0x8000a830,0x8000a83c)
   (extend gen driver; update chunk lists in Spec3/Spec4 insert lemmas).
2. Exit-restore segment 0x80008358–0x80008394 (16 instrs, straight-line): the
   6 `ld` read-backs need loopEntry's exact final memory (strengthen its post
   with the writeMap8 chain) + a writeMap8-readback lemma (EnvGetSpec family
   has the spill-reload pattern). Post: t5 = '-' (sign read-back!), s6 = len,
   t6 = 0, → j 0x8000812c → a6 = len+1 → 0x80008088 → 0x8000a830 → 0x8000782c.
3. The iov/PRINT + __ssprint_r fast path (49 instrs at 0xe908) + memcpy call
   (26 instrs — compose with the existing verified MemcpySpec) + the small
   helpers: sites via the generator, one spec per segment.
4. Byte-for-byte assembly: BufInv + sign byte → (intToString v.toInt).toUTF8
   in the caller buffer, via intToString_signblock_sn4 + loopDigits_natToString;
   needs DLI minimality conjunct (p = 0 ∨ 9 < m/10^(p-1)) for the leading digit.
5. Fast path (|v| ≤ 9) and nonneg arm via 0x80008050 for full ∀-v coverage.

## Flush part 3 progress (2026-08-24 session)

DONE since the plan above (items 1–2 and the head of 3):
- `Code/FlushPins.lean` pins the six unpinned ranges (item 1).
- `SnprintfSitesFlush.lean` + Spec7–16: exit-restore, hops, parse loop to the
  PRINT entry, sign/digit path to `0x8000782c` (items 1–2 done end-to-end:
  `parseToPrint_neg_default_width_spec`).
- `SnprintfSpec11.lean`: PRINT entry `0x8000782c` → first (sign) iovec at
  `0x800078ac`.
- **`SnprintfSpec17.lean` (new, this session):** the second iovec + call setup.
  `iov2ToSsprintCall_spec`: `0x800078ac` → the `jal` at `0x80008684` completed
  (PC = `0x8000e908`, `ra = 0x80008688`, `a0 = s0`, `a1 = mem[sp+8]`,
  `a2 = sp+224`), with the second iovec entry (digit base/len at `viov2`),
  the bumped cursor (sp+240), count (sp+232), and total (sp+16, via the
  `bge t3,a6` ite) written. `iov2Tail_spec` is the shared `0x80007908` → call
  tail (both bge outcomes); `slotHolds_writeMap4_i2` is a new sw-survival
  helper. Axiom audit clean (propext/Classical.choice/Quot.sound).
  Composition note: Spec11's postcondition must be strengthened (x5/x8/x12/
  x16/x20/x22/x26/x28 + `SlotHolds sp+16/sp+8` + vcnt bytes) to feed this
  spec's precondition — mechanical obs-extraction additions.
- **`SnprintfSpec18.lean` + `Code/Memmove.lean` GREEN (2026-08-24):** newlib
  `memmove` (`0x800069c4`) forward byte path fully verified:
  `memmove_fwd_spec` = entry dispatch (both disjointness arms: `dst+n ≤ src`
  via the `0x69c4` bgeu, `src+n ≤ dst` via `0x69c8/0x69cc`) → setup tail
  (`li 31`/`bltu`/`mv`/`addi a3,a2,-1`/`beqz`/`addi`/`add`) → 5-instr byte
  loop (`Triple.loop`, measure `2^64 − a5`) → `ret`.  Post: `[dst,dst+n)` =
  source bytes `bs`, all else = `m0`, `a0 = dst` preserved; pre `1 ≤ n ≤ 31`,
  both windows above the HTIF window.  Memory invariant reuses the strcpy
  machinery via new `cpyinv_store'` (disjointness-only generalization of
  `cpyinv_store`, StrcpySpec.lean); `MvRegions`/`MvBytes`/`NotWrittenMv`
  ({x11,x13,x14,x15}) local to Spec18.  Gotcha: `toNat`+`simp only`+`omega`
  proofs over `sext(0xfff) = 2^64−1` blow the kernel recursion limit
  ("deep recursion detected") — route minus-one pointer arithmetic through
  `sub1_bv_sn5` (SnprintfSpec5) instead.  Axioms clean.

- **`SsputsSites.lean` + `SnprintfSpec19.lean` GREEN (2026-08-24, later):**
  `ssputs_fast_spec` = the complete `__ssputs_r` fast path `0x8001438c → ret`
  (26 sites + the `jal memmove` composed with `memmove_fwd_spec`): from entry
  (a1 = sink struct `p` with cursor `d`/capacity `cap32` pinned, a2 = iov base,
  a3 = n, `n < sext32(cap32)`) to `ra` with a0 = 0, `[d,d+n) = bs`, cursor slot
  := `d+n` (`Pin8`), capacity slot := `swData (spNewCap cap32 n)` (`Pin4`),
  s0/s1/ra/sp restored, everything outside the written set = m0. No residual
  hypotheses. Also landed pace infrastructure (all in Vsa.lean): `RegPins`
  (list-driven register-frame transport, one line per site instead of per
  site×register; side condition closes by `rfl` NOT `decide`), `PtrArith`
  (canonical sext constants + kernel-safe ptr_sub + sp_decK_restore pairs),
  `CodeRangeInsert` (generic Loaded-preservation), `SlotFrame` (unified spill
  save/survive/reload API incl. `slot_survives_frame` for sub-call transport),
  `scripts/` (decode index + site-battery generator).

- **`SsprintSites.lean` + `SnprintfSpec20.lean` GREEN (2026-08-25):** flush
  part 3a done — `ssprint_iov2_spec` = the whole `__ssprint_r` 2-iovec flush
  `0x8000e908 → ret` (16-site entry, two 18-site loop iterations each
  composed with `ssputs_fast_spec` at the `jal 0x8000e97c`, 12-site tail;
  glued `entry.seq (iter1.seq iter2) .seq tail`). Pre (`PreSr`): a0 = reent,
  a1 = sink cursor struct `p` (cursor `d`, capacity `cap32`), a2 = `q` with
  `mem[q] = viov`, count `mem[q+8] = 2`, resid `mem[q+16] = n1+n2`; iov array
  `(s1,n1,bs1)/(s2,n2,bs2)` at `viov` (`1 ≤ n1,n2 ≤ 31` from MvRegions);
  capacity guard stated honestly as `n1 + n2 < cap32.toNat < 2^31`. Post at
  `PC = ra`: a0 = 0, `[d,d+n1) = bs1`, `[d+n1,d+n1+n2) = bs2`, cursor slot
  := `d + ofNat(n1+n2)`, capacity slot := `cap32 - n1 - n2` (32-bit), resid/
  count zeroed, ra/sp/s0/s1/s2–s5 restored, pointwise frame outside the six
  windows `[d,d+n1+n2) ∪ [p,p+8) ∪ [p+12,p+16) ∪ [q+8,q+12) ∪ [q+16,q+24) ∪
  [vsp-88,vsp)`, plus a `NotWrittenSr` register g-frame. No residual
  hypotheses; axioms clean. Second call's guard derived from the first call's
  post via `swData_spNewCap : swData (spNewCap w n) = w - ofNat n` +
  `sext32_toNat_small` (loop condition is exact: resid must equal n1+n2 so
  the `bnez` at 0xe998 exits after iteration 2; count `2 → 1 → 0` folds by
  `lw_count2/1_sr` + `addiw_cnt2/1_sr` since the count is concrete).
  First full `RegPins` consumer: one `pins_alu/store/…` line per site,
  `pins_cons`/`pins_dropK` surgery at rd-in-list sites (new helpers in
  Spec20), one `pins_of_frame` per call via the `sputsW` list +
  `notWrittenSp_of_avoid` adapter (callee `g := fun R => σcall.regs.get? R`
  so its frame obligation is `fun R _ => rfl`). Sites generated by
  `scripts/gen_sites.py` from `scripts/ssprint_sites.tsv` (47 theorems);
  generator gap: no RTYPE-SUB class — the one `sub a4,a4,s2` site
  (0x8000e98c, word 41270733) is hand-written in Spec20 following the
  alu_add template with `execute_rtype_sub_char`. Spec9's `ssprintTail_spec`
  NOT consumed (its post lacks the memory/callee-save clauses); the tail is
  re-proven inside Spec20 from generated sites. Gotchas: `PinsHold` list
  literals need a trailing `trivial` in anonymous constructors; drop-K
  surgery reads `⟨first k-1 components, hp.2^k⟩`; `hmemeq ▸ h` transports
  Loaded across `c.σ.mem = <image>`; store-site mem equations rewrite
  `swData (ofNat 1/0)` via `swData_one/zero_sr` before `Pin4_writeMap4`.

NEXT for the flush (rest of item 3):
a. DONE (SnprintfSpec20, above). `__ssprint_r` fast path `0x8000e908` entry (a2 = sp+224): `ld s0,0(a2)` =
   iov array; count at sink+8 (sp+232, = 2); resid = cursor at sink+16
   (sp+240) ≠ 0 → per-iov loop: `__ssputs_r` (0x8001438c) with the string
   cursor struct `a1 = mem[sp+8]`: fast path `memmove(dest = mem[sinkptr+0],
   src = iov base, n = iov len)`, cursor += n, capacity (mem[sinkptr+12])
   -= n, ret 0; two iterations (sign byte then digits); then a0 = 0 →
   `0x80008688` → `0x80007918` → parse-loop NUL exit → epilogue `0x800079b0`
   → ret with a0 = mem[sp+16] (the total).
b. Compose with MemcpySpec for memmove (0x800069c4).
c. Items 4–5 as planned.

- **Flush part 3b GREEN (2026-08-25 session): the svfprintf RETURN PATH.**
  `SnprintfSpec25.svfprintf_flushReturn_spec` = the whole
  `0x8000e908 → … → svfprintf ret` chain: `ssprint_iov2_spec` (Spec20,
  `r := 0x80008688`) ≫ `retA_spec` (Spec21: `beqz a0` taken, `ld a5,32(sp)=0`,
  `sw zero,232(sp)`, `mv s7,s5`, `j 0x80007720`) ≫ `retB_spec` (Spec22:
  parse-loop head — `ld s6,0(sp)` = fmt cursor at the NUL,
  `ld s4,232(s1)` = `__global_locale.mbtowc`, `jal __locale_mb_cur_max`
  (2 instrs, `lbu a0,1000(gp)=1`), arg setup, **indirect `jalr s4` →
  `__ascii_mbtowc`** (7 instrs: 3 nottaken beqz's, the NUL `lbu`,
  `sw a5,0(sp+180)`, `lbu`/`snez` → a0=0, ret), `beqz a0` taken)
  ≫ `retC_spec` (Spec23: `subw s8,s6,a5 = 0` structurally — same slot value —
  `beqz` → epilogue) ≫ `retD_spec` (Spec24: `ld a5,240(sp)=0` directly from
  ssprint's `Pin8 (q+16) 0` post, FILE `_flags` `lhu`+`andi 64 = 0`, the
  11 callee-save/ra/s0 reloads from `SlotHolds`, `ld a0,16(sp)` = THE TOTAL,
  `addi sp,sp,592`, `ret`).  Post: `PC = vra0`, **`a0 = vtot = mem[sp+16]`**,
  all callee-saves restored, `sp += 592`; memory = ssprint's post + the two
  `writeMap4`s (count slot re-zeroed at `sp+232` ⊂ the q-window, wide-char out
  at `sp+180`), stated as the ssprint pins (digits/sign at `[d,d+n1+n2)`,
  sink cursor/capacity) + a 7-window pointwise frame to `m0`.
  Infrastructure landed: `stepObs_jalr` (tick-absorbing linking-jalr wrapper —
  did NOT exist; built from `step_jalr_notick/tick`) + `obs_jalr_*` +
  `pins_jalr` + hand sites for the 4 generator-gap classes (linking `jalr`,
  `sltu/snez`, `lhu` incl. a new generic `exec_lhu_gen`, `andi`) in
  `SnprintfSitesRet5`; generated batteries `SnprintfSitesRet{,2,3,4}` (48
  sites, `scripts/ret_sites*.tsv`); `Code/__locale_mb_cur_max.lean` +
  `Code/__ascii_mbtowc.lean` byte pins; `DecodeTable/RetSupp.lean` for the 3
  mbtowc words outside the original census (04060263/00f5a023/00064503,
  registered in decode_index.tsv); of-agree transports
  (`svfSlice/flushPins/locale/amb_of_agree_rt`, `slotHolds_of_agree_rt`,
  `slotHolds_of_pin8_rt`) that carry SlotHolds/code pins across ssprint's
  six-window frame.  Residual caller obligations (glue hypotheses, to be
  discharged when part 2 meets the prologue): `PreSr` at the call, prologue
  spill slots (`sp+0x1e8…0x248`), parse state (`sp+0/8/16/32`), the fmt-NUL
  byte, FILE `_flags` bytes with bit 6 clear, `gp = 0x8001b510` (as
  `g x3`), `s1 = 0x8001b798`, the locale mbtowc-pointer/`__mb_cur_max` data
  pins, and address-layout disjointness (d/p/vcur vs stack/static ranges).
  Latency data (per-module `lake env lean`, small-file rule): Spec21 1.7s /
  Spec22 2.8s / Spec23 1.3s / Spec24 5.6s / Spec25 72s (the 34-chunk
  `svfSlice_of_agree_rt` simp dominates); generated site batteries 1.0–2.7s.
  Axioms clean (propext/Classical.choice/Quot.sound); both new capstones added
  to `scripts/check_all.sh` THEOREMS.

- **Flush part 3c GREEN (2026-08-25, later): the composed
  `0x800078ac → svfprintf ret` capstone.**
  `SnprintfSpec26.iov2ToSvfprintfRet_spec` = `iov2ToSsprintCall_spec`
  (Spec17, `vcnt := 1#32`) ≫ `svfprintf_flushReturn_spec` (Spec25), one
  `Steps` chain from the second-iovec entry to svfprintf's `ret` with
  **`a0 = vtotF` = sext32(sel32 + tot32)**, the flushed bytes
  `[d,d+n1) = bs1` / `[d+n1,d+n1+n2) = bs2`, sink cursor/capacity updated,
  uio resid/count cleared, total pinned at `sp+16`, and a pointwise frame to
  the `0x800078ac` memory outside NINE windows (Spec25's seven + the total
  slot `[sp+16,24)` + the second iovec `[sp+368,384)`).  `PreSr` discharged
  from Spec17's exact post writeMaps: resid `sp+240 := vcurF+vnd6 =
  ofNat(n1+n2)` (`hvcurF`/`hvnd6` ghost links, cursor = n1 from Spec11's
  bump over the prologue zero), count `sp+232 := 2` (`swData(sext(1+1))
  = 2#32` by decide), `iov[1] = (vbase, n2)` at `sp+368/376`
  (`viovB = sp+352` from the prologue `addi s5,sp,352`/`sd s5,224(sp)`,
  `viov2 = sp+368` from Spec11's `addi s7,s7,16`); everything else
  (19 SlotHolds incl. the 15 prologue spills, sign iovec pins + `'-'` byte,
  digit bytes at `vbase ∈ [sp+24,sp+224)`, sink struct pins, fmt NUL, FILE
  flags, locale slot/byte, 7 Loaded predicates) transported across the five
  writes by ONE pointwise agreement (`hagree`) + the existing
  `*_of_agree_rt`/`*_frame_*`/`slotHolds_of_agree_rt` machinery.
  **Discovered gap:** Spec17's post exports no x3/x9/x18/x19/x21 and has no
  register-frame clause, so `PreSr.cs1` (`s1 = &__global_locale =
  0x8001b798`), Spec25's `g x3 = 0x8001b510`, and x18/x19/x21 existence are
  untransportable from 0x800078ac hypotheses; they are taken as ONE
  `hreach`-style mid-state residual `hmidregs : ∀ cm, Steps c cm → PC =
  0x8000e908 → …` (env_get_found_spec precedent) — semantically true (none
  of the 28 instructions writes those registers), dischargeable mechanically
  once Spec17's post is strengthened (same obs-extraction additions its own
  composition note already plans for Spec11).  Remaining NEXT residuals
  (hypotheses not yet verified upstream): Spec11→17 register/slot/vcnt facts
  (Spec11 post strengthening), the sink FILE struct pins (snprintf wrapper
  segment), the static locale pins (startup), the prologue/parse slots and
  layout facts, `hmidregs`.  504 lines, `lake env lean` 9.1s, axioms clean;
  added to check_all THEOREMS.

- **PROLOGUE + FIRST PARSE PASS GREEN (2026-08-25, later): `0x80007654 →
  0x80008534`.**  `SnprintfSpec36.svfPrologueParse_spec` = the whole
  `_svfprintf_r` entry chain to the `'l'` handler (Spec16's entry): 138
  executed instructions = the pinned `[0x80007654, 0x800077c0)` range PLUS the
  inlined callees `_localeconv_r` (2i), `strlen(".")` (22i, concrete aligned
  word probe of the static decimal-point string at `0x80019770`),
  `memset(sp+200,0,8)` (17i incl. the computed `jr 12(a3)` byte-store
  dispatch), `__locale_mb_cur_max` (2i), and the indirect `jalr s4` →
  `__ascii_mbtowc` reading the `'%'` (8i).  Path decoded from the tracer
  (patched-script run, exact per-step trace incl. all loads/stores); ALL
  branch guards on this path are concrete (fmt bytes / static data / literal
  compares) except the FILE `_flags` test (caller bytes `fl0/fl1` with
  `&0x80 = 0`) and two null-pointer beqz's (from layout bounds).
  Structure: 8 segment modules + 2 glue capstones, one theorem per module:
  Spec27 `svfProA_spec` (entry+6 spills+`_localeconv_r`+decimal-point load,
  16 steps) ≫ Spec28 `svfProB_spec` (`jal strlen` inlined via the
  hand-proven `StrlenSites` battery, result spill, memset args, 27 steps) ≫
  Spec29 `svfProC_spec` (memset inlined + `lhu/andi/beqz` flags check, 21) ≫
  Spec30 `svfProD_spec` (9 spills + resid/count/iov-base init, 14) ≫
  Spec31 `svfProE_spec` (7 zero slots incl. the TOTAL at sp+16, s1:=locale,
  fmt spill/reload, mbtowc fn-ptr load, 13) ≫ Spec32 `svfProF_spec`
  (locale_mb + mbtowc `'%'` + `lw`-readback + `beq` taken, 21; reuses the
  `SnprintfSitesRet*` mbtowc sites — same instructions as the Spec22 NUL
  path, different data) ≫ Spec33 `svfProG_spec` (`%`-directive init: sign
  byte cleared at sp+167, cursor slot := fmt+1, t1:=0/s4:=-1/s10:=90/table
  base/s9, 15) ≫ Spec34 `svfProH_spec` (dispatch `0x7798→0x8534`, wide-post
  twin of Spec14's `parseDispatch_l_full_spec`, 10) — glued by Spec35
  `svfPrologue_spec` (0x7654→0x7728, all 27 slot facts transported) and
  Spec36 `svfPrologueParse_spec` (the capstone).  Post at `0x80008534`:
  every Spec16 entry hypothesis (x2/x6=0/x20=-1/x25=fmt+2/x26=90/
  x22=parseTableBase/x27=0/x8/x12/x23 + the va-list slot `SlotHolds sp+0x18`
  + fmt bytes 'l','d',NUL at the cursor) and every Spec26 prologue residual
  (15 spills `sp+0x1e8..0x248`, `sp+0x000` cursor slot, `0x008` FILE,
  `0x010` TOTAL=0, iov base `0x0e0` = sp+352 (`hviovBN`), count Pin4
  `0xe8` = 0, resid `0xf0` = 0) plus the WIDENED mid-registers
  x3=0x8001b510, x9=0x8001b798, x18=16, x19=37, x21=sp+352 (kills Spec26's
  `hmidregs` once threaded through Spec16/8/11/17), a pointwise frame
  outside `[vsp, vsp+592)`, and `SvfprintfSliceLoaded`.
  Infrastructure: NEW Code pins `Code/_localeconv_r.lean` + `Code/Memset.lean`
  (gen_code_lemmas.py); generated batteries `SnprintfSitesPro{,2,3}` (87
  sites via disasm_to_sites.py→gen_sites.py, ALL compiled first try); hand
  battery `SnprintfSitesPro4` (8 generator-gap sites: lhu/andi/auipc×2/
  slli×2/srli/offset-`jr` — new gaps found: auipc, slli/srli shifts,
  `jr imm(rs)`); shared `SnprintfProCommon.lean` (pins_dropN 2–18, per-callee
  Loaded-survival, `slotHolds_agree_pro`, two-sided `writeMap4` out-lemma,
  `sp_dec592_pro`, `subw_self_pro`).  Segments emitted by a house-style
  python emitter (`scripts/pro_emitter/emit_pro_seg.py` + per-segment drivers
  `scripts/pro_emitter/gen_spec2*.py`, /tmp copies during the session — Spec22-pattern step ceremony with RegPins bundles, per-write mem
  threading, fine per-window frame clauses).  Check times (`lake env lean`):
  segments 1.5–6.5s, Spec35 17.5s, Spec36 5.8s; axioms clean; both capstones
  in check_all THEOREMS (20/20).
  REMAINING to connect: Spec16 composition at 0x8534 needs its other Loaded
  hyps (`SvfprintfSlice2Loaded`/umoddi3/udivdi3/FlushPins/ParseSlotPinned)
  transported — statically below the frame, one `*_of_agree`/survival hop
  from the exported frame clause; the `hmidregs`/slot facts reach Spec26's
  `0x800078ac` entry via the (still mechanical) Spec16/Spec8/Spec11/Spec17
  post widenings already on the ledger; `hs020S` (sp+0x20 = 0) is NOT a
  prologue fact — it is `sd t3,32(sp)` in the digit-loop entry (0x800082e0,
  Spec5 region) with t3 = 0 from this chain's `x27 = 0` via Spec15/16's
  `mv t3,s11`.

- **POST-WIDENING PASS + `SnprintfSpec37` capstone GREEN (2026-08-25, later):
  `0x80007654 → 0x8000e908` with `PreSr` assembled; Spec26's `hmidregs` is
  dead.**  New `Vsa/Sim/KeepRegs.lean` (value-free register-preservation
  transport on top of `RegPins`: `KeepRegs Rs σ0 σ'` = every `R ∈ Rs` still
  reads its σ0 value; `keep_alu/store/btaken/bnottaken/jr/jal/of_frame` — one
  line per site, `(by decide)` side conditions since the list carries no
  values; `keep_rfl/trans/sub`; `midRegs5 = [x3,x9,x18,x19,x21]`).
  Widened posts (ADD-only; every existing conclusion untouched):
  * Spec4 `signBlock_neg_spec`: + `KeepRegs midRegs5` + single-byte mem frame
    (everything ≠ sp+167 unchanged).
  * Spec5 `loopEntry_spec`/`entryToDigits_spec`: + named spare-slot exports in
    ∀-implication form (`∀ v, x28 = some v → SlotHolds sp+0x20 v`, same for
    x23→0x30, x8→0x78 — the trick that recovers named values past ∃-shaped
    hypotheses) + `KeepRegs midRegs5` (through `__umoddi3` call + digit loop
    via `keep_of_frame` ∘ new `notWrittenL_of_avoid_sn5` adapter).
  * Spec6 `splitToEntry_spec`: + `(vt1' = vt1 ∨ vt1' = vt1 &&& 0xf7f)` flag
    provenance + `KeepRegs keepSplit_sn6` (midRegs5 + x8/x12/x13/x23/x28).
    `signToDigits_neg_spec`: + named slots 0x20=v28/0x30=v23/0x78=v8, flag
    disjunction, `KeepRegs midRegs5`, pointwise frame (sign byte + spill
    window + digit window excluded).
  * Spec7 `exitToPrint_spec`: + `SlotHolds sp+0x20 = 0` (the `sd zero,32(sp)`
    at 0x8390 — so `hs020S` needs NO t3-flow at all), `KeepRegs (x26::midRegs5)`,
    pointwise frame outside [sp+32,64) ∪ [sp+104,112), Slice/FlushPins exports.
  * Spec8 `entryToPrint_neg_spec`: + Slice/FlushPins, x20/x23/x8/x28 named,
    x6 = vflg with provenance ∃, `SlotHolds sp+0x20 0`, `KeepRegs midRegs5`,
    `∃ p` block (x22 = p+1, x16 = p+2 via new `len1_eq_p2`, x26 = digit base,
    `BufInv`), whole-span frame, the sign byte.  (`_default_width` wrapper
    repacked, statement unchanged.)
  * Spec13 `parseDispatchHop_spec`/`parseDispatch_d_spec`: + `KeepRegs midRegs5`.
  * Spec16 `handler_l/handler_ll/parseDispatchArith_d/handlerGap/
    parseToDigitEntry`: + `KeepRegs midRegs5`; `parseToPrintEntry_spec`:
    + `SlotHolds sp+0 = vfmt+4` (the 'd'-handler `sd s9,0(sp)` — `hfmtS`
    surfaced), `KeepRegs midRegs5`, frame outside [sp,8) ∪ [sp+24,32).
  * Spec15 `dispatchD_ll_to_printEntry_spec`: + `SlotHolds sp+0 = v9`,
    `KeepRegs midRegs5`, the same two-window frame.
  * Spec11 `printEntryToSignIov_spec`: + `x5 = 0` (the `andi t0,t1,132` — so
    `hvt0` is Spec11's, not Spec8's), `x12 = vcur+1`, `KeepRegs keepIov_pe`
    (midRegs5 + x6/x8/x16/x20/x22/x26/x28).
  * Spec17 `iov2Tail_spec`/`iov2ToSsprintCall_spec`: + `KeepRegs midRegs5` —
    exactly the five facts Spec26 took as `hmidregs`.  Spec26's proof now
    destructures the extra conjunct (`_hkeep17`); its statement is unchanged
    (the `hmidregs` hypothesis is now dischargeable by any caller from the
    widened post).
  **`SnprintfSpec37.svfEntryToSsprintCall_spec`** = Spec36 ≫ w16 ≫ w8 ≫ w11 ≫
  w17: from the `_svfprintf_r` ABI entry (sp = vsp+592, "%lld" bytes, statics,
  va-area bytes, value ghosts `hneg`/`hmag`, sink FILE struct) to
  `PC = 0x8000e908` with `∃ n2 bs2 vsubw`, **`PreSr` fully assembled**
  (q = sp+0xe0, iov = sp+0x160, sink = vfile, s1 = sp+0xa7 sign byte,
  s2 = sp+348−n2 digits, n1 = 1, count 2, resid 1+n2, ra = 0x80008688,
  cs1 = 0x8001b798, cs2 = 16, cs3 = 37, cs5 = sp+0x160) plus the Spec25
  residuals: x3 = 0x8001b510, locale slot/byte, fmt-cursor slot = vfmt+4 +
  NUL byte, FILE slot, total slot = 1+n2, sp+0x20 = 0, the 13 prologue
  spills, `_flags` bytes, and ONE pointwise frame outside [vsp, vsp+592).
  Digit bytes exported as `bs2 k = '0' + (m / 10^(n2−1−k)) % 10`.
  **Remaining residual hypotheses of the full-composition** (all wrapper/
  caller-owned): sink FILE struct fields (`Pin8 vfile d`, `Pin4 vfile+12
  cap32`, `21 < cap < 2^31`, `_flags` bytes + the 0x80/0x40 bit facts),
  destination-buffer `d` layout, va-area bytes + layout, the value ghosts,
  fmt/stack layout, static image pins — i.e. exactly the `_svsnprintf_r`
  wrapper segment + startup facts + byte-for-byte assembly (items 4–5).
  New helpers in Spec37: `sext32_ofNat_small_37`, `lt0_sext32_negk_37`,
  `ge0_ofNat_false_37`, `sub32_zero/neg1_ofNat_37` (the subw-guard shapes),
  `slice2/umoddi3/cudivdi3/parseSlot_of_agree_37`.  Gotchas: `lake env lean`
  can read STALE dep oleans after cross-file widening — use `lake build` for
  closure checks; multi-line `by` blocks inside `rw [...]` need `;` not
  newline; `simp only [BitVec.toNat_ofNat]` also rewrites `(0#64).toNat` so
  put shape-`show` rewrites before it or use simp+omega; `hvb1/hvb2` in
  Spec26 place the digit buffer below sp+224 but the real buffer ends at
  sp+348 — Spec37 therefore assembles `PreSr` itself (correct disjuncts)
  instead of calling Spec26.  Axioms clean; added to check_all THEOREMS
  (21 capstones).  `lake env lean` Spec37 ≈ 13s.

- **FULL svfprintf spec + BYTE-FOR-BYTE intToString GREEN (2026-08-25, later):
  Spec26 layout fix, `SnprintfSpec38.svfprintf_lld_spec`,
  `SnprintfSpec39` (items 4 closed for the negative multi-digit arm).**
  * **Spec26 layout fix**: `hvb1/hvb2` placed the digit buffer at
    `[vsp+24, vsp+224)` — unsatisfiable on the real run (the buffer is
    `[vsp+348−n2, vsp+348)`, `n2 ≤ 20`, per Spec37's `PreSr` instantiation).
    Corrected to `vsp+328 ≤ vbase` / `vbase+n2 ≤ vsp+348` (the `BufInv`
    window).  Only the `hbs2c1` transport and `SrRegions` omega closures
    consumed them; both re-close on the true bounds unchanged.  9.9s, green.
  * **`SnprintfSpec38.svfprintf_lld_spec`** (~300 ln, 2s): Spec37 ≫ Spec25
    directly (Spec37's post hands `PreSr` + every non-wrapper Spec25 input;
    Spec26's glue pattern reused for the pins/layout adapters).  From the
    `_svfprintf_r` ABI entry `0x80007654` to svfprintf's `ret`:
    `a0 = ofNat 64 (1+n2)`, buffer `[d, d+1+n2)` = `signByte` ++ the exact
    `bs2 k = ofNat 8 (48 + mag/10^(n2−1−k) % 10)` digits, FILE cursor
    `:= d + (1+n2)` / capacity `:= cap32 − 1 − n2`, callee-saves + sp
    restored, one pointwise frame outside `[vsp−88, vsp+592) ∪ [d, d+1+n2)
    ∪ FILE cursor/capacity fields.  Residuals are wrapper-owned ONLY: sink
    FILE struct pins + `_flags` `0x080`/`0x040` bits, dest layout, va-area
    bytes + layout, value ghosts `hneg`/`hmag`, `"%lld"` bytes, image
    statics, fmt/stack layout (NB `hfstk` needs the `vsp−128` margin so the
    fmt NUL survives the flush sub-frames — Spec37's `vsp` bound is not
    enough for Spec25's `hcurstk`; two new fmt disjointness hyps `hfd`/`hfpp`
    for the return path's NUL re-read), `vra0` 4-aligned.
  * **DLI minimality widening (ADD-only)**: the known missing conjunct
    `(p = 0 ∨ 9 < m/10^(p−1))` added to `decimalLoop_spec`'s invariant/post
    (Spec3: loop entry `p = 0` ⇒ `Or.inl rfl`; body step `p → p+1` re-uses
    the guard `9 < m/10^p` as `Or.inr`), threaded through Spec5
    (`entryToDigits_spec`), Spec6 (`signToDigits_neg_spec`), Spec8
    (`entryToPrint_neg_spec` ∃p block), exported by Spec37/38 as
    `n2 = 1 ∨ 9 < mag/10^(n2−2)`.  Whole chain rebuilt green (Spec3 34s,
    Spec5 43s, Spec37 23s).
  * **`SnprintfSpec39`** (byte-for-byte, ~500 ln, 1.5s):
    `digitList_eq_natDigits_39` (the heart: the digit formula list =
    `natDigits (mag+1) mag`, induction on `n2` along `natDigits_step`,
    upper bound `mag/10^(n2−1) ≤ 9` + the new minimality bound), a v4.29
    `String`-as-`ByteArray` UTF-8 layer (`toUTF8 = toByteArray`,
    `utf8EncodeChar c = [c.toNat]` for ASCII, `String.utf8Encode_toList` +
    `List.toList_data_toByteArray` close the loop), `intToString_neg` for
    the sign arm, and TWO capstones: `svfprintf_buffer_eq_intToString`
    (`signByte :: [bs2 0…] = (intToString v.toInt).toUTF8.data.toList` as
    `BitVec 8`) and **`svfprintf_lld_intToString_spec`** = Spec38 restated
    byte-for-byte: `∃ ubytes = (intToString (llArg …).toInt).toUTF8` bytes,
    `a0 = ofNat ubytes.length`, `∀ k < len, mem[d+k] = ubytes[k]`.
  * Gotchas: v4.29 deprecates `String.data` → use `.toList`; `decide` gets
    stuck on `ByteArray` literals (opaque `toList` loop) — route through
    `List.toList_data_toByteArray`; `simp` rewrites
    `toUTF8.data.toList.length` to `utf8ByteSize` breaking `rw [hlen]` —
    use explicit `List.length_*` rws; `List.mem_singleton.mp` applied
    inline under `rw` leaves the singleton element as a metavariable
    ("pattern is a metavariable") — bind `c = '-'` with a `have` first;
    `map f [x]` needs `simp only [List.map_cons]` before an index-arithmetic
    `rw` can find its pattern (beta); `if_pos` under `Char.toNat` needs
    `show c.val.toNat ≤ 127 from h`.
  * check_all THEOREMS extended (24): + `svfprintf_lld_spec`,
    `svfprintf_buffer_eq_intToString`, `svfprintf_lld_intToString_spec`.
  * REMAINING for `snprintf_lld_spec` (M3 close): the wrapper segment
    (stringify `0x80002fc0` → `_snprintf_r 0x80005b74` → snprintf
    `0x80005c44`: FILE init, va-area build, buffer `d`, value ghosts from
    the WHILE value), startup/static image facts, the nonneg arm +
    single-digit fast path (item 5).

Tracer reconstruction: this file + the session transcript; the interpreter is
the ~150-line loop (LUI/AUIPC/JAL/JALR/BRANCH/LOAD/STORE/OP/OP-32/OP-IMM/
OP-IMM-32/M-ext; fence+csr = nop; x0 pinned to 0).

## WRAPPER SEGMENT closed: snprintf_lld_spec (2026-08-25, session f)

Re-traced with a /tmp/pctrace_wrap.py variant (wrapper-range PC log + ABI
snapshots at 0x80005c44/0x80005cb8/0x80005cbc/0x80005cdc/0x80005cf4).
CORRECTIONS to the earlier notes:

  * `stringify`'s INT arm is at `0x800030c0` (kind==2 branch), its
    `jal snprintf` at **0x800030d8** (ra = 0x800030dc) — the previously
    eyeballed call at 0x80003040 is the CLOSURE arm (`"<fn %s>"`).
  * The `"%lld"` format is the `.rodata` string at **0x800192c0**
    (`25 6c 6c 64 00`), NOT 0x800192c8 (that's `"<fn %s>"`).
  * **`_snprintf_r` (0x80005b74) is NOT on the executed path.**  newlib's
    `snprintf` (0x80005c44) builds the string-sink FILE struct itself and
    `jal`s `_svfprintf_r` (0x80007654) directly at 0x80005cb8.
  * Executed wrapper footprint: exactly 40 instructions —
    `[0x80005c44, 0x80005cbc)` pre-call (30: frame −272, 7 va/save spills,
    `ld s1,1120(gp)` = `*_impure_ptr` = 0x8001b538, `bltu t1,a1` INT_MAX
    guard NOT taken, `snez/subw` capacity = sz−1, FILE build: cursor sp+8 :=
    d, cap sp+20 := sz−1, `_flags` sp+24 := 0xffff0208, `_bf` sp+32/40,
    sp+184 := 0, va-ptr sp+0, jal) then `[0x80005cbc, 0x80005cf8)` post-call
    (10: `blt a0,-1` not taken, `bnez s0` taken → 0x80005cdc, `ld a5,8(sp)`
    reload of the UPDATED cursor d+total, **`sb zero,0(a5)` = the NUL
    terminator**, 3 reloads, `addi sp,272`, `ret`).  a0 is returned from
    `_svfprintf_r` UNCHANGED (no recompute).
  * ABI at the real call: a0 = stringify sp+16 (64-byte stack buffer),
    a1 = 64, a2 = 0x800192c0, a3 = v; sp chain: snprintf frame
    [vsp+592, vsp+864), svfprintf frame base vsp = entry_sp − 864.

Modules (all green, axioms {propext, Classical.choice, Quot.sound}):

  * `Vsa/Sim/Code/LldFmt.lean` — 8-byte pin of the `"%lld"` rodata
    (`LldFmtLoaded`).
  * `Vsa/Sim/SnprintfSitesWrap.lean` (suffix `_wp`) — 45 sites: 41 from
    `disasm_to_sites.py 0x80005c44 0x80005cf8 --path` (bltu@5c70 nottaken,
    blt@5cc0 nottaken, bne@5cc4 taken) → `gen_sites.py`; 4 hand sites for
    the generator gaps `lui` ×2 / `not`(xori) / `snez`(sltu) on the
    SitesPro4/SitesRet5 templates (`execute_utype_lui_char`,
    `execute_itype_xori_char`, `execute_rtype_sltu_char`; all 4 words were
    already in decode_index.tsv).  Compiles 1.7s.
  * `Vsa/Sim/SnprintfSpec40.lean` (949 ln, 12s) — `snprintfPreCall_spec`
    0x80005c44 → 0x80007654, emitted by `scripts/pro_emitter/gen_spec40.py`
    (Spec27 house pattern).  Exports Spec38's wrapper-owned inputs: Pin8
    cursor=d @vsp+600, Pin4 cap=ofNat32(sz−1) @vsp+612, `_flags` bytes
    08/02 @vsp+616/7, Pin8 v @vsp+824 (the va spill), SlotHolds s1/s0/ra
    @0x0c8/0x0d0/0x0d8 of base vsp+592, single-window frame
    [vsp+592, vsp+864).  Also hosts the wrapper value lemmas
    (`sp_dec272_wr`/`sp_inc272_wr`/`t1_notmask_wr`/`a6_flags_wr`/
    `subw_cap_wr`/`bltu_of_lt_wr`/`bltu_false_of_ge_wr`) and the
    `*_of_agree_wr` transports (snprintf/lldfmt/localeconv/strlen/memset/
    ssprint/ssputs/memmove, all from ONE `∀ a < 0x8001c000` agreement).
  * `Vsa/Sim/SnprintfSpec41.lean` (307 ln, 2s) — `snprintfPostCall_spec`
    0x80005cbc → ret, emitted by `gen_spec41.py`.  Takes the abstract
    cursor `vcur` (Pin8 @vsp+600) + the three SlotHolds; post: PC=x1=wra0,
    sp=vsp+864, a0 preserved, mem = entry mem + `insert vcur (stData 1 0)`.
  * `Vsa/Sim/SnprintfSpec42.lean` (~430 ln, 3s) — **`snprintf_lld_spec`**,
    THE M3 wrapper capstone: Spec40 ≫ Spec38 ≫ Spec41 restated through
    Spec39's `svfprintf_buffer_eq_intToString`: from
    `snprintf(d, sz, "%lld", v)` ABI entry to `ret` with
    `∃ ubytes = (intToString v.toInt).toUTF8.data.toList`,
    `a0 = ofNat ubytes.length`, buffer `[d, d+len)` = ubytes byte-for-byte
    **plus the NUL at d+len**, callee-saves/sp restored, frame outside
    `[vsp−88, vsp+864) ∪ [d, d+len+1)`.

Residual hypotheses of `snprintf_lld_spec` (honest ledger): value ghosts
(`hneg`/`hmag` — negative multi-digit v; nonneg/single-digit arms are a
separate task), the static-image pins (decimal_point/locale fn/mb_cur_max/
parse-table slot/`_impure_ptr` bytes + the `*Loaded` code pins incl. the new
`LldFmtLoaded`), layout (`vsp ≥ 0x8001c100` 8-aligned with 864 bytes,
`d ≥ 0x8001c000` with 22 writable bytes disjoint from the frames), size
`23 ≤ sz < 2^31` (no truncation), `wra0` 4-aligned.  DISCHARGED vs Spec38:
the whole sink FILE struct (cursor/capacity/`_flags` bit facts), the va-area
bytes/layout, the `"%lld"` bytes + fmt layout (now image-pinned at the true
0x800192c0), vfile layout, `hra0align`, `hvdisj`, `hfd`/`hfpp`/`hfiled`/
`hfilelo`, cap bounds.

Composition-seam gotchas: `vsp.toNat + 592 + K' = vsp.toNat + K` closes by
`rw`'s rfl (small-literal Nat add-assoc IS defeq — trailing `omega` then
dies with "No goals"); the pinw/slot survive chains must peel writes
OUTERMOST-FIRST (reverse write order — kind sequences otherwise misalign
and unification hits a whnf timeout on the 15-store memory term); omega
can't identify `Int.ofNat x` with `↑x` (use `Int.ofNat_lt.mp/.mpr`);
`(sz != 0#64) = true` via `simp only [bne]` + `beq64_false_pro`; the
`jr`-to-symbolic-`wra0` step: emit with a placeholder literal nextpc and
patch the emitted text (`(0xdeadbeef#64)` → `wra0`).

check_all THEOREMS extended (27): + `snprintfPreCall_spec`,
`snprintfPostCall_spec`, `snprintf_lld_spec`.  Full build 910 jobs green.

REMAINING for M3 total closure: nonneg arm + single-digit fast path
(∀-v coverage); the stringify caller composition (0x80002fc0 int arm →
malloc/memcpy → WHILE Str value) is M4-side; startup statics discharge
against the boot image (M6).

## ARM TRACES for ∀-v coverage (2026-08-25, session g) — /tmp/pctrace_arms.py

Tracer variant: patches `println("" + <v>);` at 0x19be0, logs EVERY step from
snprintf entry 0x80005c44 until return-to-ra with stores, plus an ABI/iov
snapshot at __ssprint_r entry 0x8000e908.  Traced v ∈ {±9876543210123, ±10,
±9, ±7, 0}.  Console output correct in all runs.  FOUR machine arms, split at
0x800080e8 (`bgez a3` — sign) and 0x80008104 (`bltu a5,a4`, a5=9 — magnitude):

  neg-multi   (VERIFIED): 80e4 mv → 80e8 bgez NOT taken → 80ec li 45/80f0 sb
    '-' @sp+167/80f4 neg a4 → 80f8 bltz s4 TAKEN (s4=-1 precision) → 8100.
  nonneg      : 80e4 mv → 80e8 bgez TAKEN → **0x80008050 `bltz s4,0x8100`
    TAKEN** (the whole "0x80008050 region" is ONE instruction; NO sign byte —
    sp+167 keeps the prologue-cleared 0) → 8100 split.  8054-8060 (andi -129 /
    bnez / zero-value j 9b58) NOT executed (s4 = -1 < 0 short-circuits, even
    for v = 0: the '0' digit comes from the sb fast path, NOT the 9b58 block).
  magnitude split at 8100: li a5,9; 8104 bltu a5,a4 taken ⇔ m > 9.
  multi (both signs): → 82c8 digit loop = Spec5 region VERBATIM → 8358-8394
    exit restore (Spec7 region; 8384 a6:=sext.w s6=len, 8388 lbu t5:=sp+167,
    8390 sd zero,32(sp)) → j 812c.
  single (m ≤ 9, both signs): 8104 nottaken → 8108 addiw a4,a4,48 →
    **810c sb a4,347(sp)** (single digit at sp+347 = top-1) → 8110 sext.w
    a6,s4 (dead, a6:=-1) → 8114 blez s4 TAKEN → **0x80008ea4 block (6i)**:
    lbu t5,167(sp) (sign read-back); li a6,1; li t6,0; li s6,1 (len);
    addi s10,sp,347 (digit base); j 8128 → 8128 sd zero,32(sp) → 812c.

  SHARED SEAM 0x8000812c (`beqz t5`), state: t6=0, s6=len2 (digit count),
  s10=digit base (sp+348−len2 multi / sp+347 single), a6=len2, t5=sign byte:
    t5='-' (neg): nottaken → 8130 addiw a6,a6,1 (a6=1+len2) → 8134 j 8088.
    t5=0 (nonneg): TAKEN → 8088 directly (a6=len2).
  8088 bnez t6 nottaken → 808c j a830 → a830/a834 sd zero,56/48(sp) →
  a838 j 782c (all four arms; identical to the verified path).

  PRINT 782c (782c ld a2,240(sp); 7830 andi t0,t1,132=0; 7834 mv a0,a2;
  7838 beqz t0 taken → 7cd4 subw a4,t3,a6 (t3=width=0, a4<0); 7cd8 bgtz
  nottaken; 7cdc lbu a4,167(sp); 7ce0 bnez a4):
    neg:  bnez taken → 7844-7878 sign-iovec fill (= Spec11 region verbatim)
      → 78ac-78b8 (li 128/beq nottaken/subw s4,s4,s6/bgtz nottaken) → 78bc.
    nonneg: bnez NOTTAKEN → **7ce4 subw s4,s4,s6; 7ce8 blez s4 TAKEN → 78bc**
      (skips 7844-78b8 entirely; iovec COUNT WILL BE 1).
  78bc-78f0 (14i, same PCs as the verified 2nd-iovec fill; for nonneg s7 =
  iov base itself, count 0→1): andi 256/bnez nottaken; lw count; add a2,s6;
  sd cursor; addiw count; sd s10,0(s7); sd s6,8(s7); li 7; sw count; blt
  nottaken; addi s7,16; andi t1,t1,4 (t1:=0); beqz taken → 78fc mv a5,t3;
  7900 bge t3,a6 nottaken; 7904 mv a5,a6; 7908 = iov2Tail_spec's entry
  (ld a4,16(sp); addw; sd TOTAL:=a6; bnez a2 → 8678 ld a1,8(sp)/addi a2,
  sp,224/mv a0,s0/8684 jal __ssprint_r).

  __ssprint_r ENTRY SNAPSHOTS (q = sp+224):
    v=-9876543210123: count=2 resid=14 iov=[(sp+167,1)'-',(sp+335,13)digits]
    v=+9876543210123: count=1 resid=13 iov=[(sp+335,13) b'9876543210123']
    v=-7: count=2 resid=2  iov=[(sp+167,1)'-',(sp+347,1) b'7']
    v=+7: count=1 resid=1  iov=[(sp+347,1) b'7'];  v=0 same with b'0'
  → the nonneg arm needs a 1-iovec `__ssprint_r` variant (entry + ONE
  iteration + tail; Spec20's iter/tail machinery reusable, count folds
  lw_count1 only).  Return path after ssprint (retA 8688 → … → epilogue →
  svfprintf ret, Spec21-24) is PC-identical in all four traces.

  Footprint deltas vs the verified neg-multi run (all already pinned EXCEPT
  none — every new PC below is inside SvfprintfSlice ranges? NO: check):
    new PCs: 8050 (in [7fc0,8400) ✓ pinned), 8ea4-8eb8 (NOT pinned — outside
    all SvfprintfSlice ranges [8a80,8b10) ends before; needs new Code pins),
    7ce4-7ce8 (in FlushPins? FlushPins covers [7cd4,7ce4) only 4i — 7ce4/7ce8
    NOT pinned), 8104-8114 fast-path arm (pinned, [7fc0,8400)), 8128 (pinned).
  Site-battery gaps (not in any .tsv battery): 8050 bltz-taken, 8104
  bltu-nottaken, 8108 addiw, 810c sb(347), 8110 sext.w, 8114 blez-taken,
  8ea4-8eb8 (6), 812c beqz-taken arm, 7ce0 bnez-nottaken arm, 7ce4 subw,
  7ce8 blez-taken, 80e8 bgez-taken arm.

  ARM PLAN: (a) neg-single = NEW segment 0x800080e4 → 0x8000782c (fast-path
  twin of Spec8, n2=1, digit sp+347) then the ENTIRE verified chain from
  782c (Spec11 ≫ Spec17 ≫ Spec25) applies with n2=1 — Spec39's minimality
  disjunct `n2 = 1 ∨ …` already covers it.  (b) nonneg-multi = tiny arm
  entry (80e4/80e8/8050) ≫ Spec5 entryToDigits VERBATIM ≫ Spec7-twin (beqz
  t5 taken at 812c, a6=len) ≫ NEW PRINT-1iov segment 782c→jal (35i, reuse
  iov2Tail) ≫ ssprint_iov1 ≫ Spec21-24 re-glue.  (c) nonneg-single = arm
  entry ≫ fast-path segment ≫ same 1-iov chain.  (d) total capstone =
  4-way case split on (v.toInt sign, |mag| ≤ 9) at the spec level;
  intToString 0 = "0" handled by the nonneg-single machine arm (digit '0').

## ARM VERIFICATION LANDED (2026-08-25, session g cont.): negative arm TOTAL

* **`Vsa/Sim/Code/ArmPins.lean`** (`ArmPinsLoaded`, 8 instrs): byte pins for
  `[0x80008ea4, 0x80008ebc)` (single-digit tail block) + `[0x80007ce4,
  0x80007cec)` (nonneg PRINT hop — pinned now, consumed by the future 1-iov
  segment).  Generated by `scripts/pro_emitter/gen_armpins.py`.
* **`SnprintfSitesFast.lean`** (`_fs`, 10 sites, svfSlice): 80e4 mv,
  80e8 bgez-taken, 8050 bltz-taken, 8100 li, 8104 bltu-NOTTAKEN, 8108 addiw,
  810c sb(347), 8110 sext.w, 8128 sd-zero, 812c beqz-TAKEN.
  **`SnprintfSitesFast2.lean`** (`_fs2`, 8 sites, ArmPins): 8ea4 lbu … 8eb8 j,
  7ce4 subw, 7ce8 blez-taken.  Both `disasm_to_sites.py → gen_sites.py`,
  compiled first try.
* **`SnprintfSpec43.fastToPrint_neg_spec`** (997 ln, emitted by
  `scripts/pro_emitter/gen_spec43.py`, ~60s check): `0x80008100 → 0x8000782c`,
  21 steps, neg arm (`beqz t5` NOT taken).  Post = Spec7's landing shape at
  `p = 0`: `x22 = 1`, `x16 = 2`, digit `ofNat 8 (48+w.toNat)` at `sp+347`
  (`BufInv top w.toNat 1` via `emit_byte` + `BitVec.ofNat_toNat/setWidth_eq`),
  `SlotHolds sp+0x20 0`, sign byte surviving, 3-window pointwise frame,
  `KeepRegs midRegs5`.
* **`SnprintfSpec44.entryToPrint_neg_any_spec`**: Spec8's statement with
  `hmag` REMOVED (+ `ArmPinsLoaded` hyp + `armPins_of_agree_43`) — case split
  `9 < mag` → Spec8 verbatim; `mag ≤ 9` → `signBlock_neg_spec` ≫
  `splitToEntry_spec` ≫ Spec43, assembling the ∃p block with `p = 0`
  (`0+1`/`0+2`/`x−1−0` close by Nat-literal defeq).
* **HYPOTHESIS-REMOVAL PASS** through the capstone chain (statements
  STRENGTHENED in place, no twins): Spec37 `svfEntryToSsprintCall_spec`,
  Spec38 `svfprintf_lld_spec`, Spec39 `svfprintf_lld_intToString_spec`,
  Spec42 **`snprintf_lld_spec`** all lose `hmag` and gain the `ArmPinsLoaded`
  static pin (transported like FlushPins via one `hagLow` agreement).
  Spec39's `digitList_eq_natDigits_39` already handled `n2 = 1` (minimality
  disjunct `Or.inl`), so byte-for-byte needed NO change.
  ⇒ **`snprintf_lld_spec` now covers EVERY negative v** (single + multi digit).
* **`SnprintfSpec45.entryToPrintNN_fast_spec`** (976 ln, emitted by
  `gen_spec45.py`): the NONNEG single-digit arm `0x800080e4 → 0x8000782c`,
  22 steps (mv → bgez TAKEN → 8050 bltz TAKEN → fast path → 8ea4 tail reads
  the prologue-cleared `0x00` → `beqz t5` TAKEN → hops).  Post: `x16 = 1`
  (= len, NO sign bump), `x30 = 0`, sign slot still `0x00`, digit buffer
  `BufInv top v.toNat 1`, same frame/keeps.  Ready to feed the 1-iovec PRINT
  segment.
* check_all THEOREMS extended (30): + `fastToPrint_neg_spec`,
  `entryToPrint_neg_any_spec`, `entryToPrintNN_fast_spec`.
* Gotchas: `lake env lean` needs `lake build <battery>` after regenerating a
  sites file (stale-olean unknown-identifier errors); `x + 348 - 1 - 0` does
  NOT close by rw-rfl (opaque head) but `348 - 1` literal-literal does —
  trailing `omega` only on the former; `BitVec.ofNat_toNat` lands at
  `setWidth` (chase with `BitVec.setWidth_eq`); the emitted `_tgt` lemmas
  from gen_sites make taken-branch PC rewrites one-line (`rwa [site_…_tgt]`).

REMAINING for ∀-v (the nonneg chain, next sessions):
  1. `exitToPrintNN` — Spec7 twin with `beqz t5` TAKEN at 812c (`a6 = len`),
     for the nonneg MULTI arm (8358 → 782c; 22 steps; `site_8000812c_taken_fs`
     + the `_fl` battery already cover every site) + a tiny nonneg arm-entry
     glue (80e4/80e8/8050 → 8100, sites in `_fs`) ≫ Spec5 `entryToDigits_spec`
     VERBATIM.
  2. PRINT-1iov segment `0x8000782c → 0x8000e908` (35 steps: 782c-7838,
     7cd4-7ce8 (bnez a4 NOTTAKEN at 7ce0 — site needed; 7ce4/7ce8 in `_fs2`),
     78bc-78f0 (iovec fill, s7 = iov base, count 0→1), 78fc-7914, 8678-8684
     jal).  New sites for 782c-7838/7cd4-7ce0/78bc-7914/8678-8684 via
     disasm_to_sites (code-loaded: svfSlice + FlushPins mix); iov2Tail_spec
     (Spec17) covers 7908→call if entered with its pre.
  3. `ssprint_iov1_spec` — Spec20 twin, ONE iteration (entry 16 + iter 18 +
     tail 12; `lw_count1`-style folds; sites all exist in SsprintSites).
  4. Spec25-twin (iov1 ≫ retA-D — Spec21-24 reusable as-is), then
     Spec37/38/39-twins for the nonneg PreSr (n1 = 0, count 1, resid n2) and
     the wrapper glue (Spec40/41 reusable as-is), intToString_nonneg bridge
     (exists in SnprintfSpec.lean).
  5. Total capstone: 2-way sign split at the spec level (neg arm =
     `snprintf_lld_spec`, nonneg arm = the new chain); `intToString 0 = "0"`
     comes out of the nonneg-single machine arm (digit '0').

## NONNEG ARM MACHINE PATH LANDED (2026-08-25, session g cont. 2)

* **`SnprintfSpec46.exitToPrintNN_spec`** (917 ln, `scripts/pro_emitter/
  gen_spec46.py` — Spec7's statement + steps 1-16 extracted VERBATIM from its
  source, new taken-seam steps 17-22): `0x80008358 → 0x8000782c` with the
  sign slot `0x00`, `beqz t5` TAKEN, **`a6 = x16 = len`** (no bump).
* **`SnprintfSpec47.armEntryNN_spec`** (hand, 3 steps): `0x800080e4 →
  0x80008100` — `mv a4,a3` (magnitude = value), `bgez` taken, `8050 bltz s4`
  taken; memory untouched, `t1` UNMASKED.
* **`SnprintfSpec48.entryToPrintNN_any_spec`**: nonneg twin of Spec44 —
  ANY nonneg `v` from `0x800080e4` to the PRINT entry: multi = Spec47 ≫
  `entryToDigits_spec` (Spec5 VERBATIM) ≫ Spec46 (FlushPins/ArmPins carried
  across the loop via `flushPins_of_agree`/`armPins_of_agree_43` over
  `EntryFrame`); single = Spec45.  Post: ∃p block with `x16 = x22 =
  ofNat (p+1)`, `x30 = x31 = 0`, `x6 = vt1` exactly, nonneg value bridge
  `v.toNat = v.toInt.toNat` (`bgez_true'` + `toInt_of_notop`), sign slot
  still `0x00`, Spec8-shaped frame WITHOUT the sp+167 exclusion.
* check_all THEOREMS 33: + `exitToPrintNN_spec`, `armEntryNN_spec`,
  `entryToPrintNN_any_spec`.

⇒ The VALUE-FORMATTING span `0x800080e4 → 0x8000782c` is now verified for
**every** `v : BitVec 64` (Spec44 negative / Spec48 nonneg).  The remaining
gap to `snprintf_lld_total_spec` is purely the nonneg FLUSH chain
(1-iovec PRINT segment ≫ ssprint_iov1 ≫ return-path re-glue ≫ nonneg
svfprintf/wrapper capstones ≫ the 2-way sign-split capstone) — plan in the
previous entry, items 2-5.

## NONNEG FLUSH CHAIN + THE TOTAL CAPSTONE (2026-08-25, session h): ∀-v DONE

**`SnprintfSpec55.snprintf_lld_total_spec` GREEN — `snprintf(d, sz, "%lld", v)`
verified for EVERY `v : BitVec 64`** (statement = Spec42's with NO value
hypothesis; buffer = `(intToString v.toInt).toUTF8 ++ [0]`, `a0` = length,
callee-saves/sp restored, frame outside `[vsp−88, vsp+864) ∪ [d, d+len+1)`).
Proof = 2-way sign split on `zopz0zKzJ_s v 0` (the machine's `bgez` guard at
`0x800080e8`): false → `snprintf_lld_spec` (Spec42, neg arm), true →
`snprintf_lld_nn_spec` (Spec54, nonneg arm incl. `v = 0` → digit `'0'`).

The nonneg chain, per the session-g plan (items 2-5), all green:

* **`SnprintfSitesPrint{,2}.lean`** (`_pv`/`_pv2`): generated batteries for
  the PRINT-1iov segment PCs — 18 sites [782c-7838]∪[78bc-7904] (svfSlice,
  `scripts/print1iov_sites.tsv`) + 4 sites [7cd4-7ce0] (FlushPins,
  `scripts/print1iov_flush_sites.tsv`, incl. the previously-missing
  `site_80007ce0_nottaken_pv2` bnez-NOT-taken fork) + 3 HAND `andi` sites
  (7830/78bc/78ec — gen_sites still has no ANDI class; SitesRet5 template).
* **`SnprintfSpec49.printToSsprintNN_spec`** (1313 ln, emitted by
  `scripts/pro_emitter/gen_spec49.py`, 71s): `0x8000782c → 0x8000e908`,
  35 steps = 27 emitted (ld cursor / andi t0 folds to 0 by `hflag84` /
  beqz-taken → 7cd4 pad-check → `lbu` reads the CLEARED sign byte → `bnez`
  NOT taken → subw/blez → 78bc iovec fill: cursor `vcur→vcur+vs6`, iov[0]
  base/len at `s7 = viov`, count `vcnt→vcnt+1` (sw), addi s7,16, andi t1
  folds to 0 by `hflag4z`, beqz-taken, mv/bge-nt/mv `vsel := vlen`)
  ≫ `iov2Tail_spec` (Spec17, VERBATIM — `SlotHolds sp+16/sp+8` peeled
  outermost-first across the 4 writes).  Post: the exact 5-write memory
  equation + `ra = 0x80008688`, `a1 = vstr`, `a2 = sp+224`, KeepRegs midRegs5.
  Guards are caller hyps in site shape (hpad/hprec/hcntlt/hwlen/hvc2 +
  3 flag-masks) — discharged concretely in Spec52.
* **`SnprintfSpec50.ssprint_iov1_spec`** (1380 ln, generated FROM Spec20's
  SOURCE by `scripts/pro_emitter/gen_spec50.py`, 36s): the 1-iovec
  `__ssprint_r` flush.  `PreSr1`/`St1Sr1`/`St3Sr1`/`SrRegions1`/
  `ssprint_iov1_post` = the 2-iov structures with the SINGLE iovec KEEPING
  the `(s1, n1, bs1)` ghost names and s2/n2/bs2 fields dropped (count pin
  `2→1`, resid `n1+n2→n1`).  `tr_ssprint_entry1` = entry text verbatim;
  `tr_ssprint_iter_1v` = iter1's text with the count folds swapped
  (`lw_count2_sr→lw_count1_sr`, `addiw_cnt2→cnt1`, `swData_one→zero_sr`,
  `(q+8) (1#32)→(0#32)`), the `sub` at 0xe98c closing by `BitVec.sub_self`
  (the `ofNat_sub_left n1 n2` shape breaks at n2 = 0), and the `bnez` at
  0xe998 spliced NOT-taken (iter2's text) → St3-shaped ending assembled from
  iter1's call-1 post (`hcursor'` = d+n1, `swData_spNewCap cap32 n1 ▸ hcap'`
  = capF directly — NO second decrement); `tr_ssprint_tail1` = tail minus
  the copied2 clause.  Capstone = entry1.seq(iter_1v).seq(tail1).
* **`SnprintfSpec51.svfprintf_flushReturn1_spec`** (354 ln, gen_spec51.py,
  12s): Spec25's text with `PreSr→PreSr1`, `ssprint_iov2→iov1`, the digits
  window `[d,d+n1)`, capacity `−n1` once; retA-D (Spec21-24) consumed
  VERBATIM.
* **`SnprintfSpec52.svfEntryToSsprintCallNN_spec`** (hand, ~620 ln, 10s):
  the Spec37-twin — Spec36 ≫ Spec16 (identical text) ≫ **Spec48**
  (nonneg value arm; hwneg/-1 by decide, hwidth via default_width_lt_digits)
  ≫ **Spec49** with everything concrete: vcnt := 0#32 (prologue count),
  vcur := 0 (prologue cursor), vt3 := 0, v20 := −1, vt1 := 0x20 (flag masks
  by decide), hpad via `sub32_zero_ofNat_37 + lt0_sext32_negk_37`, hprec via
  `sub32_neg1_ofNat_37` + NEW `ge0_sext32_negk_52`, hwlen =
  `ge0_ofNat_false_37`.  `PreSr1` assembled from Spec49's 5-write memory
  equation — KEY MOVE: normalize hmem4eq ONCE
  (`rw [hA…, hresv, hsw1, hs2eq, hseltot] at hmem4eq`) instead of ←-rewrites
  in each pin goal (a ←rw of `ofNat(p+1)` hits the NESTED occurrence inside
  the write data and corrupts the term — first bug found).  resid = the
  CURSOR write (`sp+240 = q+16`, value `0+len` folds by `zero_add_ofNat_52`),
  count = `swData(sext32(0+1)) = 1#32` by decide, total = `len+0` folds by
  the Spec37-style hseltot.  Post = Spec37's ledger with `n1`/no sign byte /
  total `= ofNat n1`.
* **`SnprintfSpec53.svfprintf_lld_nn_spec`** (gen_spec53.py from Spec38's
  source, 2.3s): Spec52 ≫ Spec51 — full svfprintf, nonneg: `a0 = n1`,
  `[d, d+n1)` = digits, cursor `+n1`, capacity `−n1`.
* **`SnprintfSpec54`** (gen_spec54.py from Spec42's source, 3.4s):
  `svfprintf_buffer_eq_intToString_nn` (via `intToString_nonneg` +
  `natToString_toUTF8_toList_39` — Spec39's minimality machinery covers
  n1 = 1, so v = 0 rides through as `'0'`) + **`snprintf_lld_nn_spec`** =
  Spec40 ≫ Spec53 ≫ Spec41 with Spec42's IDENTICAL conclusion (cursor
  `d+n1`, NUL at `d+n1`, no cons case-split in the byte-for-byte bullet).
* **`SnprintfSpec55.snprintf_lld_total_spec`** (gen_spec55.py, 1.4s): the
  2-way split (`Bool.eq_false_or_eq_true` puts the TRUE arm first —
  second bug found).

Residual-hypothesis ledger of the TOTAL capstone (Spec42's minus all value
ghosts): static-image pins (decimal_point string+ptr, locale fn slot,
`__mb_cur_max`, 'd' parse-table slot, `_impure_ptr`) + the `*Loaded` code
pins; layout (`vsp ≥ 0x8001c100` 8-aligned, 864-byte frame in RAM;
`d ≥ 0x8001c000`, 22 writable bytes, disjoint from the frames);
`23 ≤ sz < 2^31`; `wra0 % 4 = 0`.  NOTHING about `v`.

Gotchas (new): gen_sites branch args with x0 operands work fine (BLT 0 rs2 /
BNE rs1 0 rows emit `rX_bits_zero` sites); textual ←rw into pin goals vs
one-shot hmem normalization (above); `Bool.eq_false_or_eq_true` arm order;
Spec55's hyp-name scrape must stop at `htick` (the conclusion's `(hk : …)`
binder otherwise leaks into the positional arg list); `(0#64) + x` does NOT
fold definitionally in write-data terms — `zero_add_ofNat_52`.

check_all THEOREMS extended (41, all audits clean, 928 jobs): + printToSsprintNN_spec, ssprint_iov1_spec,
svfprintf_flushReturn1_spec, svfEntryToSsprintCallNN_spec,
svfprintf_lld_nn_spec, svfprintf_buffer_eq_intToString_nn,
snprintf_lld_nn_spec, snprintf_lld_total_spec.
