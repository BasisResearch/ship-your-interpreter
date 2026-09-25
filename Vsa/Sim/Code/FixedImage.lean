import Vsa.Sim.Code.FixedImageData

open Std (ExtHashMap)

namespace Vsa.Sim.Code

/-- Byte equality on a bounded interval. Nothing is asserted outside it. -/
def FixedBytesLoaded (base size : Nat) (byte : Nat → BitVec 8)
    (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ offset, offset < size → mem[base + offset]? = some (byte offset)

/-- Exact .text bytes of the approved interpreter ELF. -/
def FixedTextLoaded (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  FixedBytesLoaded fixedTextBase fixedTextSize fixedTextByte mem

/-- The embedded script: `.rodata` opens with `_script_start`
(`c/src/script.S`), the script's bytes and a NUL, 454 bytes in the approved
ELF (`while.wl`). A build with another script of at most 453 bytes, written in
place (`experiments/review-v/patch_elf.py`), has the same image outside it. -/
def fixedScriptSize : Nat := 454

/-- Exact .rodata bytes after the embedded script; mutable .data/BSS are
deliberately separate. The script bytes `[0x80018be0, 0x80018da6)` are not
pinned: no proof reads them (the program is `Loaded`'s AST, not its source),
so every program's build can be `Loaded` (REVIEW.md C2). -/
def FixedRodataLoaded (mem : ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ offset, fixedScriptSize ≤ offset → offset < fixedRodataSize →
    mem[fixedRodataBase + offset]? = some (fixedRodataByte offset)

theorem FixedBytesLoaded.transport
    {base size : Nat} {byte : Nat → BitVec 8}
    {mem mem' : ExtHashMap Nat (BitVec 8)}
    (h : FixedBytesLoaded base size byte mem)
    (hag : ∀ a, base ≤ a → a < base + size → mem'[a]? = mem[a]?) :
    FixedBytesLoaded base size byte mem' := by
  intro offset hoff
  exact (hag (base + offset) (Nat.le_add_right _ _)
    (Nat.add_lt_add_left hoff base)).trans (h offset hoff)

theorem FixedTextLoaded.transport
    {mem mem' : ExtHashMap Nat (BitVec 8)} (h : FixedTextLoaded mem)
    (hag : ∀ a, 0x80000000 ≤ a → a < 0x80018be0 → mem'[a]? = mem[a]?) :
    FixedTextLoaded mem' :=
  FixedBytesLoaded.transport h hag

theorem FixedRodataLoaded.transport
    {mem mem' : ExtHashMap Nat (BitVec 8)} (h : FixedRodataLoaded mem)
    (hag : ∀ a, 0x80018da6 ≤ a → a < 0x8001acf0 → mem'[a]? = mem[a]?) :
    FixedRodataLoaded mem' := by
  intro offset hlo hhi
  exact (hag (fixedRodataBase + offset)
    (by unfold fixedRodataBase; unfold fixedScriptSize at hlo; omega)
    (by unfold fixedRodataBase; unfold fixedRodataSize at hhi; omega)).trans (h offset hlo hhi)

/-- One pinned `.rodata` byte, by absolute address. -/
theorem FixedRodataLoaded.byteAt {mem : ExtHashMap Nat (BitVec 8)} (h : FixedRodataLoaded mem)
    {a : Nat} (hlo : 0x80018da6 ≤ a) (hhi : a < 0x8001acf0) :
    mem[a]? = some (fixedRodataByte (a - 0x80018be0)) := by
  have hb := h (a - 0x80018be0) (by unfold fixedScriptSize; omega)
    (by unfold fixedRodataSize; omega)
  have e : fixedRodataBase + (a - 0x80018be0) = a := by unfold fixedRodataBase; omega
  rw [e] at hb
  exact hb

#print axioms FixedBytesLoaded.transport
#print axioms FixedTextLoaded.transport
#print axioms FixedRodataLoaded.transport
#print axioms FixedRodataLoaded.byteAt

end Vsa.Sim.Code
