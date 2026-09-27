import Vsa.Elf

/-!
# Code byte pins for the static `"%lld"` format string (`LldFmtLoaded`)

The WHILE interpreter's `stringify` (int arm, `0x800030c0`) calls
`snprintf(buf, 64, "%lld", v)` with the format pointer `a2 = 0x800192c0` —
a `.rodata` string in `c/while-riscv-htif.elf`:

    800192c0  25 6c 6c 64 00 00 00 00      "%lld\0" (+ 3 padding zeros)

8 bytes pinned (the padding included so the whole `[vfmt, vfmt+8)` window the
svfprintf layout hypotheses quantify over is image-determined).
-/

