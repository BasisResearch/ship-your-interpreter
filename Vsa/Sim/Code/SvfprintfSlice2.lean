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

namespace Vsa.Sim.Code

/-- Byte facts for the `'l'` handler `[0x80008534, 0x80008548)` (5 instructions). -/
def svfprintfSlice2ChunkL (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  -- 80008534: lbu s8,0(s9)   000ccc03
  mem[(0x80008534 : Nat)]? = some (0x03 : BitVec 8) ∧
  mem[(0x80008535 : Nat)]? = some (0xcc : BitVec 8) ∧
  mem[(0x80008536 : Nat)]? = some (0x0c : BitVec 8) ∧
  mem[(0x80008537 : Nat)]? = some (0x00 : BitVec 8) ∧
  -- 80008538: li a5,108      06c00793
  mem[(0x80008538 : Nat)]? = some (0x93 : BitVec 8) ∧
  mem[(0x80008539 : Nat)]? = some (0x07 : BitVec 8) ∧
  mem[(0x8000853a : Nat)]? = some (0xc0 : BitVec 8) ∧
  mem[(0x8000853b : Nat)]? = some (0x06 : BitVec 8) ∧
  -- 8000853c: beq s8,a5,+..   32fc02e3
  mem[(0x8000853c : Nat)]? = some (0xe3 : BitVec 8) ∧
  mem[(0x8000853d : Nat)]? = some (0x02 : BitVec 8) ∧
  mem[(0x8000853e : Nat)]? = some (0xfc : BitVec 8) ∧
  mem[(0x8000853f : Nat)]? = some (0x32 : BitVec 8) ∧
  -- 80008540: ori t1,t1,16    01036313
  mem[(0x80008540 : Nat)]? = some (0x13 : BitVec 8) ∧
  mem[(0x80008541 : Nat)]? = some (0x63 : BitVec 8) ∧
  mem[(0x80008542 : Nat)]? = some (0x03 : BitVec 8) ∧
  mem[(0x80008543 : Nat)]? = some (0x01 : BitVec 8) ∧
  -- 80008544: j 0x80007798    a54ff06f
  mem[(0x80008544 : Nat)]? = some (0x6f : BitVec 8) ∧
  mem[(0x80008545 : Nat)]? = some (0xf0 : BitVec 8) ∧
  mem[(0x80008546 : Nat)]? = some (0x4f : BitVec 8) ∧
  mem[(0x80008547 : Nat)]? = some (0xa5 : BitVec 8)

/-- Byte facts for the `"ll"` handler `[0x80009060, 0x80009070)` (4 instructions). -/
def svfprintfSlice2ChunkLL (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  -- 80009060: lbu s8,1(s9)   001ccc03
  mem[(0x80009060 : Nat)]? = some (0x03 : BitVec 8) ∧
  mem[(0x80009061 : Nat)]? = some (0xcc : BitVec 8) ∧
  mem[(0x80009062 : Nat)]? = some (0x1c : BitVec 8) ∧
  mem[(0x80009063 : Nat)]? = some (0x00 : BitVec 8) ∧
  -- 80009064: ori t1,t1,32   02036313
  mem[(0x80009064 : Nat)]? = some (0x13 : BitVec 8) ∧
  mem[(0x80009065 : Nat)]? = some (0x63 : BitVec 8) ∧
  mem[(0x80009066 : Nat)]? = some (0x03 : BitVec 8) ∧
  mem[(0x80009067 : Nat)]? = some (0x02 : BitVec 8) ∧
  -- 80009068: addi s9,s9,1   001c8c93
  mem[(0x80009068 : Nat)]? = some (0x93 : BitVec 8) ∧
  mem[(0x80009069 : Nat)]? = some (0x8c : BitVec 8) ∧
  mem[(0x8000906a : Nat)]? = some (0x1c : BitVec 8) ∧
  mem[(0x8000906b : Nat)]? = some (0x00 : BitVec 8) ∧
  -- 8000906c: j 0x80007798   f2cfe06f
  mem[(0x8000906c : Nat)]? = some (0x6f : BitVec 8) ∧
  mem[(0x8000906d : Nat)]? = some (0xe0 : BitVec 8) ∧
  mem[(0x8000906e : Nat)]? = some (0xcf : BitVec 8) ∧
  mem[(0x8000906f : Nat)]? = some (0xf2 : BitVec 8)

/-- The two handler gaps loaded (`'l'` + `"ll"`). -/
def SvfprintfSlice2Loaded (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  svfprintfSlice2ChunkL mem ∧ svfprintfSlice2ChunkLL mem

theorem svfprintfSlice2_chunkL {mem : ExtHashMap Nat (BitVec 8)}
    (h : SvfprintfSlice2Loaded mem) : svfprintfSlice2ChunkL mem := h.1

theorem svfprintfSlice2_chunkLL {mem : ExtHashMap Nat (BitVec 8)}
    (h : SvfprintfSlice2Loaded mem) : svfprintfSlice2ChunkLL mem := h.2

/-! ## Per-instruction byte accessors (4 bytes each). -/

theorem svfprintfSlice2_at_80008534 {mem : ExtHashMap Nat (BitVec 8)}
    (h : SvfprintfSlice2Loaded mem) :
      mem[(0x80008534 : Nat)]? = some (0x03 : BitVec 8) ∧
      mem[(0x80008535 : Nat)]? = some (0xcc : BitVec 8) ∧
      mem[(0x80008536 : Nat)]? = some (0x0c : BitVec 8) ∧
      mem[(0x80008537 : Nat)]? = some (0x00 : BitVec 8) :=
  have hc := svfprintfSlice2_chunkL h
  ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩

theorem svfprintfSlice2_at_80008538 {mem : ExtHashMap Nat (BitVec 8)}
    (h : SvfprintfSlice2Loaded mem) :
      mem[(0x80008538 : Nat)]? = some (0x93 : BitVec 8) ∧
      mem[(0x80008539 : Nat)]? = some (0x07 : BitVec 8) ∧
      mem[(0x8000853a : Nat)]? = some (0xc0 : BitVec 8) ∧
      mem[(0x8000853b : Nat)]? = some (0x06 : BitVec 8) :=
  have hc := svfprintfSlice2_chunkL h
  ⟨hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.1⟩

theorem svfprintfSlice2_at_8000853c {mem : ExtHashMap Nat (BitVec 8)}
    (h : SvfprintfSlice2Loaded mem) :
      mem[(0x8000853c : Nat)]? = some (0xe3 : BitVec 8) ∧
      mem[(0x8000853d : Nat)]? = some (0x02 : BitVec 8) ∧
      mem[(0x8000853e : Nat)]? = some (0xfc : BitVec 8) ∧
      mem[(0x8000853f : Nat)]? = some (0x32 : BitVec 8) :=
  have hc := svfprintfSlice2_chunkL h
  ⟨hc.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.1,
   hc.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem svfprintfSlice2_at_80009060 {mem : ExtHashMap Nat (BitVec 8)}
    (h : SvfprintfSlice2Loaded mem) :
      mem[(0x80009060 : Nat)]? = some (0x03 : BitVec 8) ∧
      mem[(0x80009061 : Nat)]? = some (0xcc : BitVec 8) ∧
      mem[(0x80009062 : Nat)]? = some (0x1c : BitVec 8) ∧
      mem[(0x80009063 : Nat)]? = some (0x00 : BitVec 8) :=
  have hc := svfprintfSlice2_chunkLL h
  ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩

theorem svfprintfSlice2_at_80009064 {mem : ExtHashMap Nat (BitVec 8)}
    (h : SvfprintfSlice2Loaded mem) :
      mem[(0x80009064 : Nat)]? = some (0x13 : BitVec 8) ∧
      mem[(0x80009065 : Nat)]? = some (0x63 : BitVec 8) ∧
      mem[(0x80009066 : Nat)]? = some (0x03 : BitVec 8) ∧
      mem[(0x80009067 : Nat)]? = some (0x02 : BitVec 8) :=
  have hc := svfprintfSlice2_chunkLL h
  ⟨hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.1⟩

theorem svfprintfSlice2_at_80009068 {mem : ExtHashMap Nat (BitVec 8)}
    (h : SvfprintfSlice2Loaded mem) :
      mem[(0x80009068 : Nat)]? = some (0x93 : BitVec 8) ∧
      mem[(0x80009069 : Nat)]? = some (0x8c : BitVec 8) ∧
      mem[(0x8000906a : Nat)]? = some (0x1c : BitVec 8) ∧
      mem[(0x8000906b : Nat)]? = some (0x00 : BitVec 8) :=
  have hc := svfprintfSlice2_chunkLL h
  ⟨hc.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.1,
   hc.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem svfprintfSlice2_at_8000906c {mem : ExtHashMap Nat (BitVec 8)}
    (h : SvfprintfSlice2Loaded mem) :
      mem[(0x8000906c : Nat)]? = some (0x6f : BitVec 8) ∧
      mem[(0x8000906d : Nat)]? = some (0xe0 : BitVec 8) ∧
      mem[(0x8000906e : Nat)]? = some (0xcf : BitVec 8) ∧
      mem[(0x8000906f : Nat)]? = some (0xf2 : BitVec 8) :=
  have hc := svfprintfSlice2_chunkLL h
  ⟨hc.2.2.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

end Vsa.Sim.Code
