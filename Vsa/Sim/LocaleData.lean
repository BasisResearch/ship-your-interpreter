import Vsa.Sim.ConsoleStream

/-!
# newlib's locale data at the boundary

`_svfprintf_r` (every `snprintf`/`fprintf`) reads three words of
`__global_locale` (`0x8001b798`, in `.data`) before and while it parses a
format: the `mbtowc` hook it calls through `jalr` (`__global_locale + 232`),
`__mb_cur_max` (`+ 0x160`, a byte, via `__locale_mb_cur_max`), and the lconv
record's `decimal_point` (`+ 0x100`, via `_localeconv_r`, then `strlen`). The
interpreter never calls `setlocale`, so they keep the ELF's values: the C
locale's `__ascii_mbtowc`, `1`, and `"."`.

Source: c/while-riscv-htif.elf (the addresses are `gp`-relative loads in
`_svfprintf_r`, `__locale_mb_cur_max`, `_localeconv_r`).
-/

open Vsa.MemRepr

namespace Vsa.Sim

def localeMbtowcAddr : Nat := 0x8001b880
def localeMbMaxAddr : Nat := 0x8001b8f8
def localeDecPointAddr : Nat := 0x8001b898

/-- `__ascii_mbtowc`. -/
def asciiMbtowc : Nat := 0x80012268
/-- The C string `"."` in `.rodata`. -/
def decPointStr : Nat := 0x80019770

/-- The C locale's data, as `_svfprintf_r` reads it. -/
structure LocaleData (m : Mem) : Prop where
  mbtowc : read64 m localeMbtowcAddr = some asciiMbtowc
  mbMax : readLE m localeMbMaxAddr 1 = some 1
  decPoint : read64 m localeDecPointAddr = some decPointStr

end Vsa.Sim
