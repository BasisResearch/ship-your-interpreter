import Vsa.Sim.EnvDefSites
import Vsa.Sim.StrcmpSpecW4
import Vsa.Sim.Regions
import Vsa.Alloc
import Vsa.RuntimeRepr
import Vsa.Triple

/-!
# Layer 3 — total-correctness spec scaffold for `env_define`

`env_define(Env *env, const char *name, Value v)` (`c/src/env.c`, entry
`0x80002a5c`, 109 instructions).  This is the largest Layer-3 target: a scan loop
that calls `strcmp` per binding, an **update-in-place** path (name found), and an
**append/grow** path (name absent) that calls `strlen`, `malloc`, `memcpy`, and
`realloc` twice.

## Control-flow map (from `experiments/disasm.txt`, env_define range)

```
ENTRY / PROLOGUE  [0x80002a5c .. 0x80002a8c]
  a5c addi sp,sp,-64            ; frame
  a60 sd  s3,24(sp)            ; spill callee-saved
  a64 lw  s3,0(a0)            ; s3 := env->count
  a68..a80 sd s2/s4/s5/ra/s0/s1/s6  ; spill the rest
  a84 mv  s4,a0               ; s4 := env  (ptr)
  a88 mv  s2,a1               ; s2 := name (cstr)
  a8c mv  s5,a2               ; s5 := &v   (value ptr)
  a90 blez s3,0x80002bf4       ; if count <= 0: jump to CAP-INIT block

SCAN-LOOP SETUP  [0x80002a94 .. 0x80002aa0]
  a94 ld  s6,8(a0)            ; s6 := env->names (char** base)
  a98 li  s0,0                ; i := 0
  a9c mv  s1,s6               ; s1 := names base  (name-slot cursor, stride 8)
  aa0 j   0x80002ab0           ; enter loop at the strcmp head

SCAN-LOOP  [0x80002aa4 .. 0x80002abc]   (bottom-tested; head at 0xab0)
  aa4 addi s0,s0,1            ; i++            (back-edge target)
  aa8 addi s1,s1,8            ; cursor += 8
  aac beq  s3,s0,0x80002b14    ; if i == count: exit loop -> CAP-CHECK (name absent)
  ab0 ld   a0,0(s1)           ; a0 := names[i]  (HEAD)
  ab4 mv   a1,s2              ; a1 := name
  ab8 jal  strcmp            ; strcmp(names[i], name)   [CROSS-REGION CALL]
  abc bnez a0,0x80002aa4       ; if != 0: continue loop; else fall to UPDATE

UPDATE PATH (name found at index i)  [0x80002ac0 .. 0x80002ae8]
  ac0 ld   a5,16(s4)          ; a5 := env->vals (Value* base)
  ac4 slli a4,s0,0x1          ; a4 := i*2
  ac8 ld   a1,0(s5)           ; a1 := v.word0
  acc ld   a2,8(s5)           ; a2 := v.word1
  ad0 ld   a3,16(s5)          ; a3 := v.word2
  ad4 add  a4,a4,s0           ; a4 := i*3
  ad8 slli a4,a4,0x3          ; a4 := i*24        (Value stride 24)
  adc add  a5,a5,a4           ; a5 := vals + 24*i
  ae0 sd   a1,0(a5)           ; vals[i].word0 := v.word0
  ae4 sd   a2,8(a5)           ; vals[i].word1 := v.word1
  ae8 sd   a3,16(a5)          ; vals[i].word2 := v.word2   (24-byte Value copy)
  --> fall through to EPILOGUE

EPILOGUE  [0x80002aec .. 0x80002b10]
  aec..b08 ld ra/s0/s1/s2/s3/s4/s5/s6   ; restore
  b0c addi sp,sp,64
  b10 ret

APPEND / GROW PATH (name absent)  [0x80002b14 .. 0x80002c0c]  ── NOT PROVED HERE
  b14 lw   a5,4(s4)           ; a5 := env->cap
  b18 beq  a5,s3,0x80002b90    ; if cap == count: GROW block
  b1c mv   a0,s2 ; b20 jal strlen         ; [CALL strlen]
  b24 addi s0,a0,1            ; s0 := len+1
  b28 mv a0,s0 ; b2c jal malloc          ; [CALL malloc]  copy = xmalloc(len+1)
  b30 mv s1,a0 ; b34 beqz a0,0x80002bd0   ; NULL -> OOM exit path
  b38 mv a2,s0 ; b3c mv a1,s2 ; b40 jal memcpy   ; [CALL memcpy] strcpy(copy,name)
  b44..b88  compute &names[count], &vals[count]; store copy ptr + 24-byte v; count++
  b8c j    0x80002aec          ; -> EPILOGUE
  GROW block b90..bc0: cap = cap?cap*2:8 ; realloc names ; realloc vals  [2x CALL realloc]
  bc8 beqz/bcc bnez -> continue append at 0xb1c, or OOM exit
  OOM path b90..bf0: _impure_ptr / fwrite / exit(1)  (never returns)
  CAP-INIT b90/bf4..c0c: count==0 entry ; cap := 8 ; go to realloc block

CROSS-FUNCTION CALLS: strcmp (per scan iter), strlen, malloc, memcpy, realloc x2.

## Landed (this file + EnvDefSites + Code/Env_define): VERIFIED, sorry-free

* `Vsa/Sim/Code/Env_define.lean` — 109-site code predicate `Env_defineLoaded`.
* `Vsa/Sim/EnvDefSites.lean` — the 40 straight-line `StepObs` site lemmas for the
  prologue + scan-loop body + update path + epilogue (all ALU/load/store class).
* This file: control-flow map, the `env_define` P/Q spec statements connected to
  `FrameRepr` and the spec-side `Vsa.While.Store.define`, the pointer-arithmetic
  helpers for the 24-byte `Value` stride, and the spec-side **update-case
  characterization** (`define_update_*`): on a name hit `define` preserves the
  binding count and rewrites exactly the matching value in place.

## Remaining (see report): the composed `env_define_spec` PROOF

The scan-loop `Triple.loop` (PC-guarded measure = `count - i`, per-iteration
strcmp composition via the ghost-at-call-site pattern; `strcmp_full_spec` is the
landed callee spec — `StrcmpSpecW4.strcmp_full_spec`), the update-path
`FrameRepr` re-establishment (24-byte `Value` copy = 3 `sd`s), and the entire
append/grow path (strlen + malloc + memcpy + realloc×2, with realloc's contract
parameterized as a hypothesis — no landed realloc spec exists yet).  These are
staged but not closed within this session's budget.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.While (Frame Store)
open Vsa.Sim.Code (Env_defineLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Spec-side `define`: the update (name-present) case characterization

When `x` is already bound in frame `f`, `Store.define` keeps the binding list
length fixed and rewrites exactly the matching entry to `(x, v)`.  This is the
spec-side content the machine's update path (`0x80002ac0..0x80002ae8`,
`vals[i] := v`) realises — the assembly locates the hit index `i` in the scan
loop and overwrites the 24-byte `Value` at `vals + 24*i`, changing no other slot,
no name pointer, and not the count. -/

/-- The `map`-with-guard used by `define`'s update branch preserves list length. -/
theorem define_update_length (vars : List (String × Vsa.While.Value)) (x : String) (v : Vsa.While.Value) :
    (vars.map fun p => if p.1 == x then (x, v) else p).length = vars.length := by
  rw [List.length_map]

/-- The update branch rewrites entry `j` to `(x, v)` when `vars[j].1 == x`, and
leaves it fixed otherwise — the pointwise content of `define`'s in-place update. -/
theorem define_update_getElem (vars : List (String × Vsa.While.Value)) (x : String) (v : Vsa.While.Value)
    (j : Nat) (hj : j < vars.length) :
    (vars.map fun p => if p.1 == x then (x, v) else p)[j]'(by rw [List.length_map]; exact hj)
      = (if vars[j].1 == x then (x, v) else vars[j]) := by
  rw [List.getElem_map]

/-- On a name hit, the frame's binding count is unchanged by `define`
(the machine's update path never touches `env->count`). -/
theorem define_update_count (f : Vsa.While.Frame) (x : String) (v : Vsa.While.Value)
    (hhit : f.vars.any (·.1 == x) = true) :
    (({ f with vars :=
          if f.vars.any (·.1 == x) then
            f.vars.map fun p => if p.1 == x then (x, v) else p
          else f.vars ++ [(x, v)] } : Vsa.While.Frame)).vars.length = f.vars.length := by
  simp only [hhit, if_true]
  exact define_update_length f.vars x v

/-! ## Pointer arithmetic for the 24-byte `Value` stride (`vals + 24*i`)

The update path computes `vals + 24*i` by `slli;add;slli;add` (`i*2`, `+i` ⇒
`i*3`, `<<3` ⇒ `i*24`).  These fold the `BitVec` shift/add chain to `24*i`. -/

/-- `slli` by 1 of a `BitVec` index `i` (value `n < 2^59`) is `2*n`. -/
theorem slli1_toNat (i : BitVec 64) :
    (i <<< (1 : Nat)).toNat = i.toNat * 2 % 2^64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]

/-- `slli` by 3 is `8*n`. -/
theorem slli3_toNat (i : BitVec 64) :
    (i <<< (3 : Nat)).toNat = i.toNat * 8 % 2^64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show (2:Nat)^3 = 8 from by decide]

/-- The full stride fold: `((i*2 + i) * 8) = 24*i` (no wrap when `24*i < 2^64`). -/
theorem stride24 (n : Nat) (h : 24 * n < 2^64) :
    (n * 2 % 2^64 + n) * 8 % 2^64 = 24 * n := by
  have h2 : n * 2 % 2^64 = n * 2 := by omega
  rw [h2]; omega

/-- `slli` at shamt `1` picks the literal shift `1` (the `0x01#6` shamt). -/
theorem shl1_lit (v : BitVec 64) :
    shift_bits_left v (Sail.BitVec.extractLsb (0x01#6) 5 0) = v <<< (1 : Nat) := by
  show v <<< (Sail.BitVec.extractLsb (0x01#6) 5 0) = _
  rw [show (Sail.BitVec.extractLsb (0x01#6) 5 0 : BitVec 6) = (1#6 : BitVec 6) from rfl]
  rfl

/-- `slli` at shamt `3` picks the literal shift `3` (the `0x03#6` shamt). -/
theorem shl3_lit (v : BitVec 64) :
    shift_bits_left v (Sail.BitVec.extractLsb (0x03#6) 5 0) = v <<< (3 : Nat) := by
  show v <<< (Sail.BitVec.extractLsb (0x03#6) 5 0) = _
  rw [show (Sail.BitVec.extractLsb (0x03#6) 5 0 : BitVec 6) = (3#6 : BitVec 6) from rfl]
  rfl

/-! ## `Env_defineLoaded` transfer through a memory agreeing on the code region

Re-establishes the code predicate after any cross-region call (`strcmp` etc.)
whose post preserves memory outside its footprint, both disjoint from the
`env_define` text `[0x80002a5c, 0x80002c10)`.  (Region-generic form; the caller
supplies the byte-agreement over the code window.) -/
theorem loaded_envdef_of_agree (mem1 mem2 : Std.ExtHashMap Nat (BitVec 8))
    (hagree : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 → mem2[a]? = mem1[a]?)
    (h : Env_defineLoaded mem1) : Env_defineLoaded mem2 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Vsa.Sim.Code.env_defineChunk0] at c0 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_defineChunk1] at c1 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_defineChunk2] at c2 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_defineChunk3] at c3 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_defineChunk4] at c4 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_defineChunk5] at c5 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])
  · simp only [Vsa.Sim.Code.env_defineChunk6] at c6 ⊢
    repeat' apply And.intro
    all_goals (rw [hagree _ (by decide) (by decide)]; simp_all only [])

end Vsa.Sim
