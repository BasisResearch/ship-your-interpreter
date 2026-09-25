import Vsa.Sim.ConsoleStream
import Vsa.Sim.DeriveCase

/-!
# `ORIENT` sets `__SORD`: the first console write (lane B1, P1)

`interp_run` is entered with `stdout->_flags = 0x000a` (`ConsoleBoot`).
newlib's write paths open with `ORIENT(fp, -1)`, compiled to one block at
four sites (`experiments/disasm.txt`):

| function | block | flags / `_flags2` / `fp` registers | next |
|---|---|---|---|
| `_fwrite_r` | `0x800050f0`–`0x80005108` | `a4` / `a5` / `s0` | `0x8000510c` |
| `_fputs_r` | `0x80006418`–`0x80006430` | `a4` / `a5` / `s0` | `0x80006434` |
| `_vfprintf_r` | `0x8000a8fc`–`0x8000a914` | `a5` / `a4` / `s4` | `0x8000a918` |
| `__swbuf_r` | `0x8000f1b4`–`0x8000f1c8` (`a1 = 0x2000` from `0x8000f110`/`0x8000f1a0`) | `a5` / `a4` / `a2` | `0x8000f1cc: j 0x8000f118` |

Each is reflected here as a `#derive_case` segment (the block model
`wp_segW`/`segToTriple` run), and its reflected outcome decided: from the
registers the preceding `lh`/`lw` leave at a `ConsoleStreamAt o` state
(`_flags` sign-extended, `_flags2 = 0`, `fp = stdout`; the block writes its
two temporaries before reading them, so they are not pinned) the write log is
`sw 0` at `_flags2` and `sh 0x200a` at `_flags`, in the block's order
(`orient*_log`). `ConsoleStreamAt.orient_log`: either log applied to a
`ConsoleStreamAt o` memory is `ConsoleStream`. Each function tests `__SORD`
first (`slli …,0x32`) and skips the block when it is set, so from an
oriented state both paths rejoin with the same memory; from `0x000a` the
block runs once and every later write starts oriented.
-/

open LeanRV64DExecutable Vsa Vsa.MemRepr

namespace Vsa.Sim

/-! ## The four blocks -/

#derive_case orientFwrite chain
  [(0x800050f0#64, 0xffffe637#32),   -- lui  a2,0xffffe
   (0x800050f4#64, 0xfff60613#32),   -- addi a2,a2,-1
   (0x800050f8#64, 0x000025b7#32),   -- lui  a1,0x2
   (0x800050fc#64, 0x00c7f7b3#32),   -- and  a5,a5,a2
   (0x80005100#64, 0x00b76733#32),   -- or   a4,a4,a1
   (0x80005104#64, 0x0af42823#32),   -- sw   a5,176(s0)
   (0x80005108#64, 0x00e41823#32)]   -- sh   a4,16(s0)

#derive_case orientFputs chain
  [(0x80006418#64, 0xffffe6b7#32),   -- lui  a3,0xffffe
   (0x8000641c#64, 0xfff68693#32),   -- addi a3,a3,-1
   (0x80006420#64, 0x00002637#32),   -- lui  a2,0x2
   (0x80006424#64, 0x00d7f7b3#32),   -- and  a5,a5,a3
   (0x80006428#64, 0x00c76733#32),   -- or   a4,a4,a2
   (0x8000642c#64, 0x0af42823#32),   -- sw   a5,176(s0)
   (0x80006430#64, 0x00e41823#32)]   -- sh   a4,16(s0)

#derive_case orientVfprintf chain
  [(0x8000a8fc#64, 0xffffe6b7#32),   -- lui  a3,0xffffe
   (0x8000a900#64, 0xfff68693#32),   -- addi a3,a3,-1
   (0x8000a904#64, 0x00002637#32),   -- lui  a2,0x2
   (0x8000a908#64, 0x00d77733#32),   -- and  a4,a4,a3
   (0x8000a90c#64, 0x00c7e7b3#32),   -- or   a5,a5,a2
   (0x8000a910#64, 0x0aea2823#32),   -- sw   a4,176(s4)
   (0x8000a914#64, 0x00fa1823#32)]   -- sh   a5,16(s4)

#derive_case orientSwbuf chain
  [(0x8000f1b4#64, 0xffffe6b7#32),   -- lui  a3,0xffffe
   (0x8000f1b8#64, 0xfff68693#32),   -- addi a3,a3,-1
   (0x8000f1bc#64, 0x00b7e7b3#32),   -- or   a5,a5,a1
   (0x8000f1c0#64, 0x00d77733#32),   -- and  a4,a4,a3
   (0x8000f1c4#64, 0x00f61823#32),   -- sh   a5,16(a2)
   (0x8000f1c8#64, 0x0ae62823#32)]   -- sw   a4,176(a2)

/-! ## Their reflected outcomes -/

/-- `_flags` as the preceding `lh` leaves it at `ConsoleStreamAt o`. -/
abbrev flagsReg (o : Bool) : BitVec 64 := BitVec.ofNat 64 (consoleFlags o)

/-- `stdout` as a register value. -/
abbrev stdoutReg : BitVec 64 := BitVec.ofNat 64 consoleStdout

/-- `sw 0` at `_flags2`, then `sh 0x200a` at `_flags`. -/
def orientLogWH : List WEntry := [(consoleStdout + 176, 4, 0#64), (consoleStdout + 16, 2, 0x200a#64)]

/-- `sh 0x200a` at `_flags`, then `sw 0` at `_flags2` (`__swbuf_r`). -/
def orientLogHW : List WEntry := [(consoleStdout + 16, 2, 0x200a#64), (consoleStdout + 176, 4, 0#64)]

theorem orientFwrite_log (o : Bool) :
    (evalBlocks orientFwrite (SegEvalState.init
      [(15, 0#64), (14, flagsReg o), (8, stdoutReg)] [])).log = orientLogWH ∧
    evalBlocksPC 0x800050f0#64 (SegEvalState.init
      [(15, 0#64), (14, flagsReg o), (8, stdoutReg)] []) orientFwrite =
      0x8000510c#64 := by
  cases o <;> exact ⟨rfl, rfl⟩

theorem orientFputs_log (o : Bool) :
    (evalBlocks orientFputs (SegEvalState.init
      [(15, 0#64), (14, flagsReg o), (8, stdoutReg)] [])).log = orientLogWH ∧
    evalBlocksPC 0x80006418#64 (SegEvalState.init
      [(15, 0#64), (14, flagsReg o), (8, stdoutReg)] []) orientFputs =
      0x80006434#64 := by
  cases o <;> exact ⟨rfl, rfl⟩

theorem orientVfprintf_log (o : Bool) :
    (evalBlocks orientVfprintf (SegEvalState.init
      [(14, 0#64), (15, flagsReg o), (20, stdoutReg)] [])).log = orientLogWH ∧
    evalBlocksPC 0x8000a8fc#64 (SegEvalState.init
      [(14, 0#64), (15, flagsReg o), (20, stdoutReg)] []) orientVfprintf =
      0x8000a918#64 := by
  cases o <;> exact ⟨rfl, rfl⟩

theorem orientSwbuf_log (o : Bool) :
    (evalBlocks orientSwbuf (SegEvalState.init
      [(11, 0x2000#64), (14, 0#64), (15, flagsReg o), (12, stdoutReg)] [])).log =
      orientLogHW ∧
    evalBlocksPC 0x8000f1b4#64 (SegEvalState.init
      [(11, 0x2000#64), (14, 0#64), (15, flagsReg o), (12, stdoutReg)] []) orientSwbuf =
      0x8000f1cc#64 := by
  cases o <;> exact ⟨rfl, rfl⟩

/-! ## The logs orient `stdout` -/

theorem readLE_zero_bytes {m : Mem} : ∀ {n a : Nat}, readLE m a n = some 0 →
    ∀ i, i < n → m[a + i]? = some 0#8
  | 0, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, a, h, i, hi => by
    generalize h0 : m[a]? = o0 at h
    cases o0 with
    | none => simp [readLE, h0] at h
    | some b0 =>
      generalize hr : readLE m (a + 1) n = r at h
      cases r with
      | none => simp [readLE, h0, hr] at h
      | some v =>
        simp only [readLE, h0, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        have hb : b0 = 0#8 := BitVec.eq_of_toNat_eq (by simp; omega)
        have hv : v = 0 := by omega
        rcases i with _ | i
        · simpa [hb] using h0
        · have := readLE_zero_bytes (hv ▸ hr) i (by omega)
          rwa [show a + 1 + i = a + (i + 1) by omega] at this

/-- The bytes the two `ORIENT` stores leave, off `_flags`' high byte: all
equal to the old ones at a `ConsoleStreamAt o` state. -/
theorem orient_agree {o : Bool} {m m' : Mem} (hc : ConsoleStreamAt o m)
    (h : ∀ a, m'[a]? = if a = consoleStdout + 16 then some 0x0a#8
      else if a = consoleStdout + 17 then some 0x20#8
      else if consoleStdout + 176 ≤ a ∧ a < consoleStdout + 180 then some 0#8 else m[a]?) :
    ConsoleStream m' := by
  have h176 := readLE_zero_bytes hc.lockMode
  refine ConsoleStreamAt.orient (m := m) (fun a _ ha => ?_) (by rw [h]; simp) hc
  rw [h]
  by_cases e16 : a = consoleStdout + 16
  · subst e16; simp [hc.flag0]
  · rw [if_neg e16, if_neg ha]
    by_cases e : consoleStdout + 176 ≤ a ∧ a < consoleStdout + 180
    · rw [if_pos e]
      have := h176 (a - (consoleStdout + 176)) (by omega)
      rw [show consoleStdout + 176 + (a - (consoleStdout + 176)) = a by omega] at this
      exact this.symm
    · rw [if_neg e]

theorem orient_bytes (d : BitVec 64) (h : d = 0x200a#64) :
    (shData d).extractLsb' 0 8 = 0x0a#8 ∧ (shData d).extractLsb' 8 8 = 0x20#8 := by
  subst h; decide

theorem orient_word (i : Nat) (hi : i < 4) : (swData (0#64)).extractLsb' (8 * i) 8 = 0#8 := by
  rcases i with _ | _ | _ | _ | i <;> first | decide | omega

/-- **`ORIENT` orients `stdout`**: its write log (`sw` then `sh`, as in
`_fwrite_r`, `_fputs_r`, `_vfprintf_r`) applied to a `ConsoleStreamAt o`
memory is `ConsoleStream`. -/
theorem ConsoleStreamAt.orient_logWH {o : Bool} {m : Mem} (hc : ConsoleStreamAt o m) :
    ConsoleStream (writeLog m orientLogWH) := by
  refine orient_agree hc fun a => ?_
  simp only [writeLog, orientLogWH, List.foldl_cons, List.foldl_nil, applyW, writeMap4,
    Std.ExtHashMap.getElem?_insert, beq_iff_eq]
  have hb := orient_bytes _ rfl
  rw [hb.1, hb.2]
  have w := orient_word
  by_cases e17 : consoleStdout + 16 + 1 = a
  · subst e17; simp
  by_cases e16 : consoleStdout + 16 = a
  · subst e16; simp
  rw [if_neg e17, if_neg e16, if_neg (Ne.symm e16), if_neg (by omega : ¬ a = consoleStdout + 17)]
  by_cases e3 : consoleStdout + 176 + 3 = a
  · subst e3; simp [w 3 (by decide)]
  by_cases e2 : consoleStdout + 176 + 2 = a
  · subst e2; simp [w 2 (by decide)]
  by_cases e1 : consoleStdout + 176 + 1 = a
  · subst e1; simp [w 1 (by decide)]
  by_cases e0 : consoleStdout + 176 = a
  · subst e0; simpa using w 0 (by decide)
  rw [if_neg e3, if_neg e2, if_neg e1, if_neg e0, if_neg (by omega)]

/-- **`ORIENT` orients `stdout`** (`__swbuf_r`'s order: `sh` then `sw`). -/
theorem ConsoleStreamAt.orient_logHW {o : Bool} {m : Mem} (hc : ConsoleStreamAt o m) :
    ConsoleStream (writeLog m orientLogHW) := by
  refine orient_agree hc fun a => ?_
  simp only [writeLog, orientLogHW, List.foldl_cons, List.foldl_nil, applyW, writeMap4,
    Std.ExtHashMap.getElem?_insert, beq_iff_eq]
  have hb := orient_bytes _ rfl
  rw [hb.1, hb.2]
  have w := orient_word
  by_cases e3 : consoleStdout + 176 + 3 = a
  · subst e3; simp [w 3 (by decide)]
  by_cases e2 : consoleStdout + 176 + 2 = a
  · subst e2; simp [w 2 (by decide)]
  by_cases e1 : consoleStdout + 176 + 1 = a
  · subst e1; simp [w 1 (by decide)]
  by_cases e0 : consoleStdout + 176 = a
  · subst e0; simpa using w 0 (by decide)
  rw [if_neg e3, if_neg e2, if_neg e1, if_neg e0]
  by_cases e17 : consoleStdout + 16 + 1 = a
  · subst e17; simp
  by_cases e16 : consoleStdout + 16 = a
  · subst e16; simp
  rw [if_neg e17, if_neg e16, if_neg (Ne.symm e16), if_neg (by omega : ¬ a = consoleStdout + 17),
    if_neg (by omega)]

end Vsa.Sim
