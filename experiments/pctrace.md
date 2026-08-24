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

Tracer reconstruction: this file + the session transcript; the interpreter is
the ~150-line loop (LUI/AUIPC/JAL/JALR/BRANCH/LOAD/STORE/OP/OP-32/OP-IMM/
OP-IMM-32/M-ext; fence+csr = nop; x0 pinned to 0).
