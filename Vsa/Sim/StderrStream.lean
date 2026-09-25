import Vsa.Sim.ExitRuntimeData

/-!
# `stderr`'s write fields at the boundary (lane N3)

The first `fwrite`/`fprintf` to `stderr` (`__sf[2]`, `0x8001bbd8`) reads two
fields of its `FILE` that `ExitRuntimeData`'s `ExitIdleFile` does not pin:
`_bf._base` (`+24`), which `__swsetup_r` tests before `__smakebuf_r` installs
the one-byte buffer `_nbuf`, and `_write` (`+64`), the write callback
`__sfvwrite_r` calls through `jalr`. `std()` in `__sinit` sets them to `NULL`
and `__swrite`, and nothing writes `stderr` before the interpreter runs.

Source: c/while-riscv-htif.elf (`__swsetup_r` `0x8000f2a4`, `__sfvwrite_r`
`0x8000df10`).
-/

open Vsa.MemRepr

namespace Vsa.Sim

/-- `stderr`'s buffer base and write callback, unused. -/
structure StderrStream (m : Mem) : Prop where
  base : read64 m (exitStderr + 24) = some 0
  writer : read64 m (exitStderr + 64) = some consoleSwrite

end Vsa.Sim
