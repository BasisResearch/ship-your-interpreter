import VsaIris.Vsa.StdioRead
import Vsa.Sim.ExitRuntimeDataTransport
import Vsa.Sim.ConsoleOrient

/-!
# The first console write orients `stdout` (lane B1, P1)

`interp_run` is entered with `stdout->_flags = 0x000a` (`__SWR | __SNBF`, as
`main`'s `setvbuf(stdout, 0, _IONBF, 0)` leaves it): `Loaded`'s
`InterpRunPhysicalFacts.console` is `ConsoleBoot`. Every console write path
opens with newlib's `ORIENT(fp, -1)`, which the binary compiles to the same
block at four sites (`experiments/disasm.txt`):

| function | test (`slli …,0x32` of `_flags`) | `ORIENT` block | rejoins at |
|---|---|---|---|
| `_fwrite_r` | `0x800050e8` (`bltz` → `0x800051d0`) | `0x800050f0`–`0x80005108` | `0x80005160` (via `bgez`) |
| `_fputs_r` | `0x80006410` (`bltz` → `0x800064a0`) | `0x80006418`–`0x80006430` | `0x8000643c` (fall-through) |
| `_vfprintf_r` | `0x8000a8f0` (`bgez` → `0x8000a8fc`) | `0x8000a8fc`–`0x8000a914` | `0x8000a924` (via `bgez`) |
| `__swbuf_r` | `0x8000f108` (`bgez` → `0x8000f1b4`) | `0x8000f1b4`–`0x8000f1c8` | `0x8000f118` (`j`) |

`_vfprintf_r`'s test at `0x8000a8f0` is taken only when `_flags2 & 1` is set; with
`_flags2 = 0` (every boundary state) the route runs the stub lock (`0x8000ace8` →
`0x8000af44`) and tests at `0x8000af54` (`bltz` → `0x8000a918` oriented, else
`j 0x8000a8fc`, the block above; `Fprintf/Outer.lean`).

Each block computes `_flags | 0x2000` (`lui …,0x2; or`) and
`_flags2 & 0xffffffffffffdfff` (`lui …,0xffffe; addi …,-1; and`) and stores
them with `sh …,16(fp)` and `sw …,176(fp)`. At a `ConsoleStreamAt o` state
the halfword is `0x200a` and the word `0` (`orient_values`), so the only byte
that changes is `_flags`' high byte, to `0x20`, and the result is the
oriented `ConsoleStream` (`Vsa.Sim.ConsoleStreamAt.orient`, and for the four blocks' reflected write
logs `Vsa.Sim.ConsoleStreamAt.orient_logWH`/`orient_logHW`; for images,
`StdioOKAt.orient`). From an oriented state the test skips the block; the
two paths rejoin with the same memory.
-/

namespace VsaIris.Stdio

open Vsa.MemRepr Vsa.Sim

/-- **What an `ORIENT` block stores**, at every site, from either
orientation: the `lh` of `_flags` (sign-extended), `or` the `lui …,0x2`
constant, truncated by `sh`, is `0x200a`; the `lw` of `_flags2 = 0`, `and`
the `lui …,0xffffe; addi …,-1` mask, truncated by `sw`, is `0`. -/
theorem orient_values (o : Bool) :
    ((BitVec.signExtend 64 (BitVec.ofNat 16 (consoleFlags o)) |||
        BitVec.signExtend 64 (0x2#20 ++ 0#12)).truncate 16 = 0x200a#16) ∧
    ((BitVec.signExtend 64 (0#32) &&&
        (BitVec.signExtend 64 (0xffffe#20 ++ 0#12) + BitVec.signExtend 64 (0xfff#12))).truncate 32
      = 0#32) := by
  cases o <;> decide

/-- `stdout`'s `_flags` high byte, `consoleStdout + 17`. -/
abbrev consoleFlagHi : Nat := consoleStdout + 17

theorem consoleFlagHi_stdio : stdioFoot consoleFlagHi := by
  unfold stdioFoot InRange consoleFlagHi consoleStdout; omega

theorem consoleFlagHi_off_exit {a : Nat} (h : ExitRuntimeExtraFoot a) : a ≠ consoleFlagHi := by
  have hr : ∀ r ∈ exitRuntimeExtraRegions, r.1 + r.2 ≤ 0x8001bb31 ∨ 0x8001bb32 ≤ r.1 := by
    decide
  obtain ⟨r, hr', h1, h2⟩ := h
  have := hr r hr'
  unfold consoleFlagHi consoleStdout
  omega

/-- **The first write orients `stdout`, on images.** An image that agrees
with a `StdioOKAt o` image on `stdioFoot` except `_flags`' high byte, and holds
`0x20` there, is `StdioOKAt true`. -/
theorem StdioOKAt.orient {o : Bool} {img img' : Nat → BitVec 8} (h : StdioOKAt o img)
    (hkeep : ∀ a, stdioFoot a → a ≠ consoleFlagHi → img' a = img a)
    (hhi : img' consoleFlagHi = 0x20#8) : StdioOKAt true img' := by
  intro m hm
  let m0 : Mem := m.insert consoleFlagHi (img consoleFlagHi)
  have hm0 : ∀ a, a ≠ consoleFlagHi → m0[a]? = m[a]? := fun a ha => by
    simp only [m0, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    rw [if_neg (Ne.symm ha)]
  have h0 : ∀ a, stdioFoot a → m0[a]? = some (img a) := fun a ha => by
    by_cases e : a = consoleFlagHi
    · subst e; simp [m0]
    · rw [hm0 a e, hm a ha, hkeep a ha e]
  obtain ⟨hc, he, hs, hl, hw⟩ := h m0 h0
  have ag : ∀ n a, (∀ k, k < n → a + k ≠ consoleFlagHi) → readLE m0 a n = readLE m a n :=
    fun n a hk => readLE_agreeP (P := fun a => a ≠ consoleFlagHi) (fun a ha => hm0 a ha) n a hk
  refine ⟨ConsoleStreamAt.orient (fun a _ ha => (hm0 a ha).symm) ?_ hc,
    he.transport fun a ha => hm0 a (consoleFlagHi_off_exit ha), ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [hm _ consoleFlagHi_stdio, hhi]
  · rw [← hs]; unfold read64
    refine (ag 8 _ ?_).symm
    intro k hk; unfold stderrPtrAddr consoleFlagHi consoleReent consoleStdout; omega
  · rw [← hl.mbtowc]; unfold read64
    refine (ag 8 _ ?_).symm
    intro k hk; unfold localeMbtowcAddr consoleFlagHi consoleStdout; omega
  · rw [← hl.mbMax]
    refine (ag 1 _ ?_).symm
    intro k hk; unfold localeMbMaxAddr consoleFlagHi consoleStdout; omega
  · rw [← hl.decPoint]; unfold read64
    refine (ag 8 _ ?_).symm
    intro k hk; unfold localeDecPointAddr consoleFlagHi consoleStdout; omega
  · rw [← hw.base]; unfold read64
    refine (ag 8 _ ?_).symm
    intro k hk; unfold exitStderr consoleFlagHi consoleStdout; omega
  · rw [← hw.writer]; unfold read64
    refine (ag 8 _ ?_).symm
    intro k hk; unfold exitStderr consoleFlagHi consoleStdout; omega

/-- An oriented image is a boundary image. -/
theorem StdioOK.of_oriented {img : Nat → BitVec 8} (h : StdioOKAt true img) : StdioOK img :=
  h.ok

end VsaIris.Stdio
