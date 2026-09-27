import Vsa.Elf

/-! Code-region byte facts for the two `%lld` length-modifier **handler gaps** that
lie *outside* `Code/SvfprintfSlice.lean`'s range-restricted coverage
(`[0x80007654,0x80007a00) ∪ [0x80007fc0,0x80008400) ∪ [0x80008a80,0x80008b10)`):

* the `'l'`  handler `[0x80008534, 0x80008548)` (5 instructions), and
* the `"ll"` handler `[0x80009060, 0x80009070)` (4 instructions).

These are hand-pinned (mirroring the generated per-site byte-fact style of
`SvfprintfSlice.lean`) rather than regenerated into that file, so the existing
(large, generated) coverage file is left untouched.  Bytes decoded directly from
`c/while-riscv-htif.elf` (`riscv64-elf-objdump`):

```
  ── 'l' handler @ 0x80008534 ─────────────────────────────
  80008534: 000ccc03  lbu  s8,0(s9)          s8 := format[2]
  80008538: 06c00793  li   a5,108            a5 := 'l' (0x6c)
  8000853c: 32fc02e3  beq  s8,a5,0x80009060  format[2]=='l' ⇒ "ll"
  80008540: 01036313  ori  t1,t1,16          (single-'l', not taken here)
  80008544: a54ff06f  j    0x80007798

  ── "ll" handler @ 0x80009060 ────────────────────────────
  80009060: 001ccc03  lbu  s8,1(s9)          s8 := format[3]  ('d')
  80009064: 02036313  ori  t1,t1,32          t1 := t1 ||| 0x20  (SET ll-flag)
  80009068: 001c8c93  addi s9,s9,1           advance cursor
  8000906c: f2cfe06f  j    0x80007798        back to conversion dispatch
```
-/

open Std (ExtHashMap)

