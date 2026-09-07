import Vsa.Sim.OutputAliasMemory
import Vsa.Sim.OutputAliasProgramRepr
import Vsa.Sim.OutputAliasStore

/-! A finite RAM snapshot admitting a string literal in the stdout buffer.
Every initial-state fact is derived from explicit bytes and register values.
No execution or representation preservation is assumed. -/

namespace Vsa.Sim.OutputAliasLoaded

open Vsa.MemRepr Vsa.RuntimeRepr
open Vsa.While.LoadedOutputAlias
open Vsa.Sim.LayoutInstance

/-- Little-endian fields outside the immutable ELF image. Unlisted bytes are zero. -/
def snapshotWords : List (Nat × Nat × Nat) :=
  [(0x82000000, 8, 0x82000020),
   (0x82000008, 8, 0x82000040),
   (0x82000020, 4, 0x0),
   (0x82000028, 8, 0x82000080),
   (0x82000040, 4, 0x3),
   (0x82000048, 8, 0x820000c0),
   (0x82000050, 8, 0x82000020),
   (0x82000058, 8, 0x0),
   (0x82000080, 4, 0x9),
   (0x82000088, 8, 0x820000a0),
   (0x82000090, 8, 0x0),
   (0x82000098, 4, 0x0),
   (0x820000a0, 4, 0x4),
   (0x820000a8, 8, 0x81000210),
   (0x820000c0, 4, 0x6),
   (0x820000c8, 4, 0x13),
   (0x820000d0, 8, 0x82000100),
   (0x820000d8, 8, 0x82000120),
   (0x82000100, 4, 0x1),
   (0x82000108, 8, 0x8001bb97),
   (0x82000120, 4, 0x1),
   (0x82000128, 8, 0x82000140),
   (0x81000000, 4, 0x3),
   (0x81000004, 4, 0x8),
   (0x81000008, 8, 0x81000040),
   (0x81000010, 8, 0x81000080),
   (0x81000018, 8, 0x0),
   (0x81000040, 8, 0x81000200),
   (0x81000048, 8, 0x81000210),
   (0x81000050, 8, 0x81000220),
   (0x81000080, 4, 0x5),
   (0x81000088, 8, 0x81000200),
   (0x81000090, 8, 0x80002ed4),
   (0x81000098, 4, 0x5),
   (0x810000a0, 8, 0x81000210),
   (0x810000a8, 8, 0x80002f7c),
   (0x810000b0, 4, 0x5),
   (0x810000b8, 8, 0x81000220),
   (0x810000c0, 8, 0x80002df4),
   (0x81000200, 8, 0x746e697270),
   (0x81000210, 8, 0x6e6c746e697270),
   (0x81000220, 8, 0x747265737361),
   (0x82000140, 2, 0xa),
   (0x8001b970, 8, 0x8001b538),
   (0x8001b548, 8, 0x8001bb20),
   (0x8001b580, 8, 0x80005d2c),
   (0x8001bb20, 8, 0x8001bb97),
   (0x8001bb28, 4, 0x0),
   (0x8001bb2c, 4, 0x0),
   (0x8001bb30, 2, 0x200a),
   (0x8001bb32, 2, 0x1),
   (0x8001bb38, 8, 0x8001bb97),
   (0x8001bb40, 4, 0x1),
   (0x8001bb48, 4, 0x0),
   (0x8001bb50, 8, 0x8001bb20),
   (0x8001bb60, 8, 0x8000efd4),
   (0x8001bbc0, 8, 0x0),
   (0x8001bbd0, 4, 0x0),
   (0x8001b9f8, 8, 0x0),
   (0x8001b9b0, 8, 0x80005d18),
   (0x8001b520, 8, 0x0),
   (0x8001b528, 4, 0x3),
   (0x8001b530, 8, 0x8001ba68),
   (0x8001bb70, 8, 0x8000f0c0),
   (0x8001bb78, 8, 0x0),
   (0x8001bb98, 8, 0x0),
   (0x87fffff8, 8, 0x80000038),
   (0x8001bb97, 1, 0x0),
   (0x87fffe10, 8, 0x81000000),
   (0x87fffe18, 4, 0x0),
   (0x8001b880, 8, 0x80012268),
   (0x8001b898, 8, 0x80019770),
   (0x8001b8f8, 1, 0x1),
   (0x8001ba78, 2, 0x4),
   (0x8001ba7a, 2, 0x0),
   (0x8001ba70, 4, 0x0),
   (0x8001bad8, 4, 0x0),
   (0x8001ba98, 8, 0x8001ba68),
   (0x8001bab8, 8, 0x8000f0c0),
   (0x8001bac0, 8, 0x0),
   (0x8001bae0, 8, 0x0),
   (0x8001bb08, 8, 0x0),
   (0x8001bb18, 4, 0x0),
   (0x8001bbe8, 2, 0x12),
   (0x8001bbea, 2, 0x2),
   (0x8001bbe0, 4, 0x0),
   (0x8001bc48, 4, 0x0),
   (0x8001bc08, 8, 0x8001bbd8),
   (0x8001bc28, 8, 0x8000f0c0),
   (0x8001bc30, 8, 0x0),
   (0x8001bc50, 8, 0x0),
   (0x8001bc78, 8, 0x0),
   (0x8001bc88, 4, 0x0)]

def fieldByte (a : Nat) : List (Nat × Nat × Nat) → BitVec 8
  | [] => 0
  | (base, width, value) :: rest =>
      if base ≤ a ∧ a < base + width then
        BitVec.ofNat 8 (value / 2 ^ (8 * (a - base)))
      else fieldByte a rest

def snapshotByte (a : Nat) : BitVec 8 :=
  if 0x80000000 ≤ a ∧ a < 0x80018be0 then
    Code.fixedTextByte (a - 0x80000000)
  else if 0x80018be0 ≤ a ∧ a < 0x8001acf0 then
    Code.fixedRodataByte (a - 0x80018be0)
  else fieldByte a snapshotWords

def snapshotMem : Mem := ramMemory snapshotByte

/-- Total lookup equation for finite trace certificates, including absent bytes. -/
theorem snapshot_lookup (a : Nat) : snapshotMem[a]? =
    if 0x80000000 ≤ a ∧ a < 0x88000000 then some (snapshotByte a) else none :=
  ramMemory_lookup snapshotByte a

theorem snapshot_get (a : Nat) (b : BitVec 8)
    (hlo : 0x80000000 ≤ a) (hhi : a < 0x88000000)
    (hb : snapshotByte a = b) : snapshotMem[a]? = some b := by
  rw [snapshotMem, ramMemory_get snapshotByte a hlo hhi, hb]

theorem snapshot_read (a width value : Nat)
    (hlo : 0x80000000 ≤ a) (hhi : a + width ≤ 0x88000000)
    (hv : byteRead snapshotByte a width = value) :
    readLE snapshotMem a width = some value := by
  rw [snapshotMem, ramMemory_readLE snapshotByte a width hlo hhi, hv]

local macro "pin_read" : tactic =>
  `(tactic| exact snapshot_read _ _ _ (by decide) (by decide) (by decide))
local macro "pin_byte" : tactic =>
  `(tactic| exact snapshot_get _ _ (by decide) (by decide) (by decide))

theorem snapshot_programReads : ProgramReads snapshotMem where
  array_first := by pin_read
  array_second := by pin_read
  print_tag := by pin_read
  print_expr := by pin_read
  if_tag := by pin_read
  if_cond := by pin_read
  if_then := by pin_read
  if_else := by pin_read
  call_tag := by pin_read
  call_callee := by pin_read
  call_args := by pin_read
  call_argc := by pin_read
  var_tag := by pin_read
  var_name := by pin_read
  equal_tag := by pin_read
  equal_op := by pin_read
  equal_left := by pin_read
  equal_right := by pin_read
  empty_tag := by pin_read
  empty_ptr := by pin_read
  newline_tag := by pin_read
  newline_ptr := by pin_read
  name_p := by pin_byte
  name_r := by pin_byte
  name_i := by pin_byte
  name_n₁ := by pin_byte
  name_t := by pin_byte
  name_l := by pin_byte
  name_n₂ := by pin_byte
  name_zero := by pin_byte
  empty_zero := by pin_byte
  newline_byte := by pin_byte
  newline_zero := by pin_byte

theorem snapshot_program : ProgramRepr snapshotMem 0x82000000 2 program :=
  snapshot_programReads.programRepr

theorem snapshot_storeFacts : StoreFacts snapshotMem where
  count := by pin_read
  capacity := by pin_read
  names := by pin_read
  values := by pin_read
  parent := by pin_read
  names0 := by pin_read
  names1 := by pin_read
  names2 := by pin_read
  tag0 := by pin_read
  name0 := by pin_read
  function0 := by pin_read
  tag1 := by pin_read
  name1 := by pin_read
  function1 := by pin_read
  tag2 := by pin_read
  name2 := by pin_read
  function2 := by pin_read
  printBytes := by
    simp only [NameBytes]
    repeat' apply And.intro
    all_goals pin_byte
  printlnBytes := by
    simp only [NameBytes]
    repeat' apply And.intro
    all_goals pin_byte
  assertBytes := by
    simp only [NameBytes]
    repeat' apply And.intro
    all_goals pin_byte

theorem snapshot_text : Code.FixedTextLoaded snapshotMem := by
  intro k hk
  change k < 0x18be0 at hk
  change snapshotMem[0x80000000 + k]? = some (Code.fixedTextByte k)
  apply snapshot_get _ _ (by omega) (by omega)
  unfold snapshotByte
  rw [if_pos (show 0x80000000 ≤ 0x80000000 + k ∧
    0x80000000 + k < 0x80018be0 from ⟨by omega, by omega⟩)]
  exact congrArg Code.fixedTextByte (by omega)

theorem snapshot_rodata : Code.FixedRodataLoaded snapshotMem := by
  intro k hk
  change k < 0x2110 at hk
  change snapshotMem[0x80018be0 + k]? = some (Code.fixedRodataByte k)
  apply snapshot_get _ _ (by omega) (by omega)
  unfold snapshotByte
  rw [if_neg (show ¬ (0x80000000 ≤ 0x80018be0 + k ∧
    0x80018be0 + k < 0x80018be0) from (by omega))]
  rw [if_pos (show 0x80018be0 ≤ 0x80018be0 + k ∧
    0x80018be0 + k < 0x8001acf0 from ⟨by omega, by omega⟩)]
  exact congrArg Code.fixedRodataByte (by omega)

theorem snapshot_statics : Code.ImageStaticsLoaded snapshotMem := by
  simp only [Code.ImageStaticsLoaded, Code.imgLldFmt, Code.imgDecPointStr,
    Code.imgParseSlotD, Code.imgParseSlotL, Code.imgFnSlot, Code.imgDecPointPtr,
    Code.imgMbCurMax, Code.imgImpurePtr]
  repeat' apply And.intro
  all_goals pin_byte

theorem snapshot_console : ConsoleStream snapshotMem where
  impure := by pin_read
  stdout := by pin_read
  sinit := by pin_read
  cursor := by pin_read
  readCount := by pin_read
  writeCount := by pin_read
  flags := by pin_read
  flag0 := by pin_byte
  flag1 := by pin_byte
  fd := by pin_read
  base := by pin_read
  bufSize := by pin_read
  lineBufSize := by pin_read
  cookie := by pin_read
  writer := by pin_read
  lock := by pin_read
  lockMode := by pin_read
  bufferByte := by exact ⟨0, by pin_byte⟩

theorem snapshot_stdin : ExitIdleFile snapshotMem 0x8001ba68 4 0 where
  flags_read := by pin_read
  descriptor_read := by pin_read
  readCount := by pin_read
  savedReadCount := by pin_read
  cookie := by pin_read
  closeCallback := by pin_read
  ungetcBuffer := by pin_read
  lineBuffer := by pin_read
  lock := by pin_read
  lockMode := by pin_read

theorem snapshot_stderr : ExitIdleFile snapshotMem 0x8001bbd8 18 2 where
  flags_read := by pin_read
  descriptor_read := by pin_read
  readCount := by pin_read
  savedReadCount := by pin_read
  cookie := by pin_read
  closeCallback := by pin_read
  ungetcBuffer := by pin_read
  lineBuffer := by pin_read
  lock := by pin_read
  lockMode := by pin_read

theorem snapshot_exitRuntime : ExitRuntimeData snapshotMem where
  atexit := by pin_read
  atexitLock := ⟨0, by pin_read⟩
  stdioHandler := by pin_read
  glueNext := by pin_read
  glueCount := by pin_read
  glueFiles := by pin_read
  stdin := snapshot_stdin
  stderr := snapshot_stderr
  stdoutClose := by pin_read
  stdoutUngetc := by pin_read
  stdoutLine := by pin_read

theorem snapshot_mainRa : read64 snapshotMem 0x87fffff8 = some 0x80000038 := by
  pin_read

theorem snapshot_globals : read64 snapshotMem interpObject = some 0x81000000 := by
  pin_read

theorem snapshot_depth : read32 snapshotMem (interpObject + 8) = some 0 := by
  pin_read

theorem snapshot_stackBytes : ∀ k, stackSL.lo ≤ k → k < stackSL.hi →
    ∃ b, snapshotMem[k]? = some b := by
  intro k hlo hhi
  exact ⟨snapshotByte k, snapshot_get _ _ (by change 0x87800000 ≤ k at hlo; omega)
    (by change k < 0x88000000 at hhi; exact hhi) rfl⟩

#print axioms snapshot_program
#print axioms snapshot_storeFacts
#print axioms snapshot_text
#print axioms snapshot_rodata
#print axioms snapshot_statics
#print axioms snapshot_console
#print axioms snapshot_exitRuntime
#print axioms snapshot_stackBytes

end Vsa.Sim.OutputAliasLoaded
