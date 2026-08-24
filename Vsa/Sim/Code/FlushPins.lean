import Vsa.Sim.Regions

/-!
# Code byte pins for the `%lld` flush hop ranges (`FlushPinsLoaded`)

The executed `snprintf("%lld")` path (mechanical PC trace, `experiments/pctrace.md`)
crosses six small ranges outside `SvfprintfSliceLoaded`'s pinned windows: the
parse-loop tail, three dispatch hops, the `__ssprint_r`-call hop, and the no-pad
shortcut.  92 bytes total, generated from `c/while-riscv-htif.elf`.
-/

namespace Vsa.Sim.Code

open Std

def flushPinsChunk0 (mem : ExtHashMap Nat (BitVec 8)) : Prop :=

  mem[(0x80007a00 : Nat)]? = some (0x83 : BitVec 8) ∧
  mem[(0x80007a01 : Nat)]? = some (0x34 : BitVec 8) ∧
  mem[(0x80007a02 : Nat)]? = some (0x81 : BitVec 8) ∧
  mem[(0x80007a03 : Nat)]? = some (0x23 : BitVec 8) ∧
  mem[(0x80007a04 : Nat)]? = some (0x03 : BitVec 8) ∧
  mem[(0x80007a05 : Nat)]? = some (0x3b : BitVec 8) ∧
  mem[(0x80007a06 : Nat)]? = some (0x01 : BitVec 8) ∧
  mem[(0x80007a07 : Nat)]? = some (0x21 : BitVec 8) ∧
  mem[(0x80007a08 : Nat)]? = some (0x13 : BitVec 8) ∧
  mem[(0x80007a09 : Nat)]? = some (0x01 : BitVec 8) ∧
  mem[(0x80007a0a : Nat)]? = some (0x01 : BitVec 8) ∧
  mem[(0x80007a0b : Nat)]? = some (0x25 : BitVec 8) ∧
  mem[(0x80007a0c : Nat)]? = some (0x67 : BitVec 8) ∧
  mem[(0x80007a0d : Nat)]? = some (0x80 : BitVec 8) ∧
  mem[(0x80007a0e : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x80007a0f : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x80007cd4 : Nat)]? = some (0x3b : BitVec 8) ∧
  mem[(0x80007cd5 : Nat)]? = some (0x07 : BitVec 8) ∧
  mem[(0x80007cd6 : Nat)]? = some (0x0e : BitVec 8) ∧
  mem[(0x80007cd7 : Nat)]? = some (0x41 : BitVec 8) ∧
  mem[(0x80007cd8 : Nat)]? = some (0xe3 : BitVec 8) ∧
  mem[(0x80007cd9 : Nat)]? = some (0x40 : BitVec 8) ∧
  mem[(0x80007cda : Nat)]? = some (0xe0 : BitVec 8) ∧
  mem[(0x80007cdb : Nat)]? = some (0x76 : BitVec 8) ∧
  mem[(0x80007cdc : Nat)]? = some (0x03 : BitVec 8) ∧
  mem[(0x80007cdd : Nat)]? = some (0x47 : BitVec 8) ∧
  mem[(0x80007cde : Nat)]? = some (0x71 : BitVec 8) ∧
  mem[(0x80007cdf : Nat)]? = some (0x0a : BitVec 8) ∧
  mem[(0x80007ce0 : Nat)]? = some (0xe3 : BitVec 8) ∧
  mem[(0x80007ce1 : Nat)]? = some (0x12 : BitVec 8) ∧
  mem[(0x80007ce2 : Nat)]? = some (0x07 : BitVec 8) ∧
  mem[(0x80007ce3 : Nat)]? = some (0xb6 : BitVec 8) ∧
  mem[(0x80008534 : Nat)]? = some (0x03 : BitVec 8) ∧
  mem[(0x80008535 : Nat)]? = some (0xcc : BitVec 8) ∧
  mem[(0x80008536 : Nat)]? = some (0x0c : BitVec 8) ∧
  mem[(0x80008537 : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x80008538 : Nat)]? = some (0x93 : BitVec 8) ∧
  mem[(0x80008539 : Nat)]? = some (0x07 : BitVec 8) ∧
  mem[(0x8000853a : Nat)]? = some (0xc0 : BitVec 8) ∧
  mem[(0x8000853b : Nat)]? = some (0x06 : BitVec 8) ∧
  mem[(0x8000853c : Nat)]? = some (0xe3 : BitVec 8) ∧
  mem[(0x8000853d : Nat)]? = some (0x02 : BitVec 8) ∧
  mem[(0x8000853e : Nat)]? = some (0xfc : BitVec 8) ∧
  mem[(0x8000853f : Nat)]? = some (0x32 : BitVec 8) ∧
  mem[(0x80008678 : Nat)]? = some (0x83 : BitVec 8) ∧
  mem[(0x80008679 : Nat)]? = some (0x35 : BitVec 8) ∧
  mem[(0x8000867a : Nat)]? = some (0x81 : BitVec 8) ∧
  mem[(0x8000867b : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x8000867c : Nat)]? = some (0x13 : BitVec 8) ∧
  mem[(0x8000867d : Nat)]? = some (0x06 : BitVec 8) ∧
  mem[(0x8000867e : Nat)]? = some (0x01 : BitVec 8) ∧
  mem[(0x8000867f : Nat)]? = some (0x0e : BitVec 8) ∧
  mem[(0x80008680 : Nat)]? = some (0x13 : BitVec 8) ∧
  mem[(0x80008681 : Nat)]? = some (0x05 : BitVec 8) ∧
  mem[(0x80008682 : Nat)]? = some (0x04 : BitVec 8) ∧
  mem[(0x80008683 : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x80008684 : Nat)]? = some (0xef : BitVec 8) ∧
  mem[(0x80008685 : Nat)]? = some (0x60 : BitVec 8) ∧
  mem[(0x80008686 : Nat)]? = some (0x40 : BitVec 8) ∧
  mem[(0x80008687 : Nat)]? = some (0x28 : BitVec 8) ∧
  mem[(0x80008688 : Nat)]? = some (0x63 : BitVec 8) ∧
  mem[(0x80008689 : Nat)]? = some (0x08 : BitVec 8) ∧
  mem[(0x8000868a : Nat)]? = some (0x05 : BitVec 8) ∧
  mem[(0x8000868b : Nat)]? = some (0xa8 : BitVec 8) ∧
  mem[(0x80009060 : Nat)]? = some (0x03 : BitVec 8) ∧
  mem[(0x80009061 : Nat)]? = some (0xcc : BitVec 8) ∧
  mem[(0x80009062 : Nat)]? = some (0x1c : BitVec 8) ∧
  mem[(0x80009063 : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x80009064 : Nat)]? = some (0x13 : BitVec 8) ∧
  mem[(0x80009065 : Nat)]? = some (0x63 : BitVec 8) ∧
  mem[(0x80009066 : Nat)]? = some (0x03 : BitVec 8) ∧
  mem[(0x80009067 : Nat)]? = some (0x02 : BitVec 8) ∧
  mem[(0x80009068 : Nat)]? = some (0x93 : BitVec 8) ∧
  mem[(0x80009069 : Nat)]? = some (0x8c : BitVec 8) ∧
  mem[(0x8000906a : Nat)]? = some (0x1c : BitVec 8) ∧
  mem[(0x8000906b : Nat)]? = some (0x00 : BitVec 8) ∧
  mem[(0x8000906c : Nat)]? = some (0x6f : BitVec 8) ∧
  mem[(0x8000906d : Nat)]? = some (0xe0 : BitVec 8) ∧
  mem[(0x8000906e : Nat)]? = some (0xcf : BitVec 8) ∧
  mem[(0x8000906f : Nat)]? = some (0xf2 : BitVec 8) ∧
  mem[(0x8000a830 : Nat)]? = some (0x23 : BitVec 8) ∧
  mem[(0x8000a831 : Nat)]? = some (0x3c : BitVec 8) ∧
  mem[(0x8000a832 : Nat)]? = some (0x01 : BitVec 8) ∧
  mem[(0x8000a833 : Nat)]? = some (0x02 : BitVec 8) ∧
  mem[(0x8000a834 : Nat)]? = some (0x23 : BitVec 8) ∧
  mem[(0x8000a835 : Nat)]? = some (0x38 : BitVec 8) ∧
  mem[(0x8000a836 : Nat)]? = some (0x01 : BitVec 8) ∧
  mem[(0x8000a837 : Nat)]? = some (0x02 : BitVec 8) ∧
  mem[(0x8000a838 : Nat)]? = some (0x6f : BitVec 8) ∧
  mem[(0x8000a839 : Nat)]? = some (0xc0 : BitVec 8) ∧
  mem[(0x8000a83a : Nat)]? = some (0x5f : BitVec 8) ∧
  mem[(0x8000a83b : Nat)]? = some (0xff : BitVec 8)


def FlushPinsLoaded (mem : ExtHashMap Nat (BitVec 8)) : Prop := flushPinsChunk0 mem

theorem flushPins_chunk0 {mem : ExtHashMap Nat (BitVec 8)} (h : FlushPinsLoaded mem) :
    flushPinsChunk0 mem := h

/-- `FlushPinsLoaded` depends only on memory below `0x8000b000` (all 92 pins live in
`[0x80007a00, 0x8000a83c)`).  Any memory agreeing with a loaded one on that region
is itself loaded — used to carry the pins across the stack-only writes of the digit
path (`sp ≥ tohost+80 ≫ 0x8000b000`). -/
theorem flushPins_of_agree {m0 mem : ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, a < 0x8000b000 → mem[a]? = m0[a]?) (h : FlushPinsLoaded m0) :
    FlushPinsLoaded mem := by
  unfold FlushPinsLoaded flushPinsChunk0 at h ⊢
  simp (disch := omega) only [hag]
  exact h

theorem flushPins_at_80007a00 {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x80007a00 : Nat)]? = some (0x83 : BitVec 8) ∧
      mem[(0x80007a01 : Nat)]? = some (0x34 : BitVec 8) ∧
      mem[(0x80007a02 : Nat)]? = some (0x81 : BitVec 8) ∧
      mem[(0x80007a03 : Nat)]? = some (0x23 : BitVec 8) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem flushPins_at_80007a04 {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x80007a04 : Nat)]? = some (0x03 : BitVec 8) ∧
      mem[(0x80007a05 : Nat)]? = some (0x3b : BitVec 8) ∧
      mem[(0x80007a06 : Nat)]? = some (0x01 : BitVec 8) ∧
      mem[(0x80007a07 : Nat)]? = some (0x21 : BitVec 8) :=
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_80007a08 {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x80007a08 : Nat)]? = some (0x13 : BitVec 8) ∧
      mem[(0x80007a09 : Nat)]? = some (0x01 : BitVec 8) ∧
      mem[(0x80007a0a : Nat)]? = some (0x01 : BitVec 8) ∧
      mem[(0x80007a0b : Nat)]? = some (0x25 : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_80007a0c {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x80007a0c : Nat)]? = some (0x67 : BitVec 8) ∧
      mem[(0x80007a0d : Nat)]? = some (0x80 : BitVec 8) ∧
      mem[(0x80007a0e : Nat)]? = some (0x00 : BitVec 8) ∧
      mem[(0x80007a0f : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_80007cd4 {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x80007cd4 : Nat)]? = some (0x3b : BitVec 8) ∧
      mem[(0x80007cd5 : Nat)]? = some (0x07 : BitVec 8) ∧
      mem[(0x80007cd6 : Nat)]? = some (0x0e : BitVec 8) ∧
      mem[(0x80007cd7 : Nat)]? = some (0x41 : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_80007cd8 {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x80007cd8 : Nat)]? = some (0xe3 : BitVec 8) ∧
      mem[(0x80007cd9 : Nat)]? = some (0x40 : BitVec 8) ∧
      mem[(0x80007cda : Nat)]? = some (0xe0 : BitVec 8) ∧
      mem[(0x80007cdb : Nat)]? = some (0x76 : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_80007cdc {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x80007cdc : Nat)]? = some (0x03 : BitVec 8) ∧
      mem[(0x80007cdd : Nat)]? = some (0x47 : BitVec 8) ∧
      mem[(0x80007cde : Nat)]? = some (0x71 : BitVec 8) ∧
      mem[(0x80007cdf : Nat)]? = some (0x0a : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_80007ce0 {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x80007ce0 : Nat)]? = some (0xe3 : BitVec 8) ∧
      mem[(0x80007ce1 : Nat)]? = some (0x12 : BitVec 8) ∧
      mem[(0x80007ce2 : Nat)]? = some (0x07 : BitVec 8) ∧
      mem[(0x80007ce3 : Nat)]? = some (0xb6 : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_80008534 {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x80008534 : Nat)]? = some (0x03 : BitVec 8) ∧
      mem[(0x80008535 : Nat)]? = some (0xcc : BitVec 8) ∧
      mem[(0x80008536 : Nat)]? = some (0x0c : BitVec 8) ∧
      mem[(0x80008537 : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_80008538 {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x80008538 : Nat)]? = some (0x93 : BitVec 8) ∧
      mem[(0x80008539 : Nat)]? = some (0x07 : BitVec 8) ∧
      mem[(0x8000853a : Nat)]? = some (0xc0 : BitVec 8) ∧
      mem[(0x8000853b : Nat)]? = some (0x06 : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_8000853c {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x8000853c : Nat)]? = some (0xe3 : BitVec 8) ∧
      mem[(0x8000853d : Nat)]? = some (0x02 : BitVec 8) ∧
      mem[(0x8000853e : Nat)]? = some (0xfc : BitVec 8) ∧
      mem[(0x8000853f : Nat)]? = some (0x32 : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_80008678 {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x80008678 : Nat)]? = some (0x83 : BitVec 8) ∧
      mem[(0x80008679 : Nat)]? = some (0x35 : BitVec 8) ∧
      mem[(0x8000867a : Nat)]? = some (0x81 : BitVec 8) ∧
      mem[(0x8000867b : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_8000867c {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x8000867c : Nat)]? = some (0x13 : BitVec 8) ∧
      mem[(0x8000867d : Nat)]? = some (0x06 : BitVec 8) ∧
      mem[(0x8000867e : Nat)]? = some (0x01 : BitVec 8) ∧
      mem[(0x8000867f : Nat)]? = some (0x0e : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_80008680 {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x80008680 : Nat)]? = some (0x13 : BitVec 8) ∧
      mem[(0x80008681 : Nat)]? = some (0x05 : BitVec 8) ∧
      mem[(0x80008682 : Nat)]? = some (0x04 : BitVec 8) ∧
      mem[(0x80008683 : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_80008684 {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x80008684 : Nat)]? = some (0xef : BitVec 8) ∧
      mem[(0x80008685 : Nat)]? = some (0x60 : BitVec 8) ∧
      mem[(0x80008686 : Nat)]? = some (0x40 : BitVec 8) ∧
      mem[(0x80008687 : Nat)]? = some (0x28 : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_80008688 {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x80008688 : Nat)]? = some (0x63 : BitVec 8) ∧
      mem[(0x80008689 : Nat)]? = some (0x08 : BitVec 8) ∧
      mem[(0x8000868a : Nat)]? = some (0x05 : BitVec 8) ∧
      mem[(0x8000868b : Nat)]? = some (0xa8 : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_80009060 {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x80009060 : Nat)]? = some (0x03 : BitVec 8) ∧
      mem[(0x80009061 : Nat)]? = some (0xcc : BitVec 8) ∧
      mem[(0x80009062 : Nat)]? = some (0x1c : BitVec 8) ∧
      mem[(0x80009063 : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_80009064 {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x80009064 : Nat)]? = some (0x13 : BitVec 8) ∧
      mem[(0x80009065 : Nat)]? = some (0x63 : BitVec 8) ∧
      mem[(0x80009066 : Nat)]? = some (0x03 : BitVec 8) ∧
      mem[(0x80009067 : Nat)]? = some (0x02 : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_80009068 {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x80009068 : Nat)]? = some (0x93 : BitVec 8) ∧
      mem[(0x80009069 : Nat)]? = some (0x8c : BitVec 8) ∧
      mem[(0x8000906a : Nat)]? = some (0x1c : BitVec 8) ∧
      mem[(0x8000906b : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_8000906c {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x8000906c : Nat)]? = some (0x6f : BitVec 8) ∧
      mem[(0x8000906d : Nat)]? = some (0xe0 : BitVec 8) ∧
      mem[(0x8000906e : Nat)]? = some (0xcf : BitVec 8) ∧
      mem[(0x8000906f : Nat)]? = some (0xf2 : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_8000a830 {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x8000a830 : Nat)]? = some (0x23 : BitVec 8) ∧
      mem[(0x8000a831 : Nat)]? = some (0x3c : BitVec 8) ∧
      mem[(0x8000a832 : Nat)]? = some (0x01 : BitVec 8) ∧
      mem[(0x8000a833 : Nat)]? = some (0x02 : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_8000a834 {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x8000a834 : Nat)]? = some (0x23 : BitVec 8) ∧
      mem[(0x8000a835 : Nat)]? = some (0x38 : BitVec 8) ∧
      mem[(0x8000a836 : Nat)]? = some (0x01 : BitVec 8) ∧
      mem[(0x8000a837 : Nat)]? = some (0x02 : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem flushPins_at_8000a838 {mem : ExtHashMap Nat (BitVec 8)}
    (h : FlushPinsLoaded mem) :
      mem[(0x8000a838 : Nat)]? = some (0x6f : BitVec 8) ∧
      mem[(0x8000a839 : Nat)]? = some (0xc0 : BitVec 8) ∧
      mem[(0x8000a83a : Nat)]? = some (0x5f : BitVec 8) ∧
      mem[(0x8000a83b : Nat)]? = some (0xff : BitVec 8) :=
  ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

end Vsa.Sim.Code
