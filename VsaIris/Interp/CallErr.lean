import VsaIris.Interp.ErrArm
import VsaIris.Interp.CallPrefix

/-!
# The call arm's error messages (lane E4)

The call arm's runtime errors (`interp.c:177-207`), each through
`runtime_error(in, line, fmt, a1, a2)` (E2's `ms_rtErrEval`):

| error | `fmt` (`.rodata`) | arguments |
|---|---|---|
| too many arguments | `0x80019470` `"too many arguments (max 32)"` | `0, 0` |
| call depth | `0x800194d0` `"stack overflow (call depth > 1000)"` | `0, 0` |
| `break`/`continue` escaping a body | `0x800194f8` `"'break'/'continue' outside of a loop"` | `0, 0` |
| not callable | `0x80019490` `"cannot call a %s value"` | the kind's name, `0` |
| arity | `0x80019038` `"%s"` | the frame buffer `sp+144` (`snprintf`'d), `0` |

`rodata_fmt0`: a `.rodata` message without conversions is safe to print with
any arguments (one `decide` over the image per message).
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Newlib
open Vsa.MemRepr Vsa.Sim Vsa.While

/-- A `.rodata` format without conversions: its `n` bytes, then the NUL. -/
theorem rodata_fmt0 {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) (p n : Nat)
    (hb : ∀ i, i < n → rodataDom (p + i) ∧ rodataByte (p + i) ≠ 0)
    (hn : rodataDom (p + n) ∧ rodataByte (p + n) = 0)
    (hp : parseFmt ((List.range n).map (fun i => rodataByte (p + i))) = some [])
    (hp64 : p < 2 ^ 64) (x1 x2 : BitVec 64) :
    FmtArgsOK R rd (BitVec.ofNat 64 p) [x1, x2] := by
  have e : (BitVec.ofNat 64 p).toNat = p := Nat.mod_eq_of_lt hp64
  refine ⟨(List.range n).map (fun i => rodataByte (p + i)), [], ⟨?_, hp, by simp,
    fun i hi => absurd hi (Nat.not_lt_zero _)⟩⟩
  rw [e]
  refine cstrCov_rodata hro (fun i h => ?_) (by simpa using hn)
  simp only [List.length_map, List.length_range] at h
  obtain ⟨h1, h2⟩ := hb i h
  exact ⟨h1, by simp, by simpa using h2⟩

theorem tooMany_fmt {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) (x1 x2 : BitVec 64) :
    FmtArgsOK R rd 0x80019470#64 [x1, x2] :=
  rodata_fmt0 hro 0x80019470 27 (by decide) (by decide) (by decide) (by decide) x1 x2

theorem depth_fmt {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) (x1 x2 : BitVec 64) :
    FmtArgsOK R rd 0x800194d0#64 [x1, x2] :=
  rodata_fmt0 hro 0x800194d0 34 (by decide) (by decide) (by decide) (by decide) x1 x2

theorem escape_fmt {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) (x1 x2 : BitVec 64) :
    FmtArgsOK R rd 0x800194f8#64 [x1, x2] :=
  rodata_fmt0 hro 0x800194f8 36 (by decide) (by decide) (by decide) (by decide) x1 x2

/-- `"cannot call a %s value"` with a C string argument. -/
theorem notCallable_fmt {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) {x1 : BitVec 64}
    (hs : ∃ t, CStrCov R rd x1.toNat t) (x2 : BitVec 64) :
    FmtArgsOK R rd 0x80019490#64 [x1, x2] := by
  refine ⟨(List.range 22).map (fun i => rodataByte (0x80019490 + i)), [.str],
    ⟨cstrCov_rodata hro (fun i h => ?_) (by decide), by decide, by simp, ?_⟩⟩
  · simp only [List.length_map, List.length_range] at h
    have := (show ∀ i, i < 22 → rodataDom (0x80019490 + i) ∧ rodataByte (0x80019490 + i) ≠ 0
      by decide) i h
    exact ⟨this.1, by simp, by simpa using this.2⟩
  · intro i hi _
    have : i = 0 := by simpa using hi
    subst this
    exact hs

/-- A `.rodata` format whose only conversions are `convs`, its `%s`
arguments C strings: one `decide` per format for the bytes. -/
theorem rodata_fmtS {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) (p n : Nat) (convs : List Conv)
    (hb : ∀ i, i < n → rodataDom (p + i) ∧ rodataByte (p + i) ≠ 0)
    (hn : rodataDom (p + n) ∧ rodataByte (p + n) = 0)
    (hp : parseFmt ((List.range n).map (fun i => rodataByte (p + i))) = some convs)
    (hp64 : p < 2 ^ 64) {args : List (BitVec 64)} (hlen : convs.length ≤ args.length)
    (hs : ∀ i (h : i < convs.length), convs[i] = .str →
      ∃ t, CStrCov R rd (args[i]'(Nat.lt_of_lt_of_le h hlen)).toNat t) :
    FmtArgsOK R rd (BitVec.ofNat 64 p) args := by
  have e : (BitVec.ofNat 64 p).toNat = p := Nat.mod_eq_of_lt hp64
  refine ⟨(List.range n).map (fun i => rodataByte (p + i)), convs, ⟨?_, hp, hlen, hs⟩⟩
  rw [e]
  refine cstrCov_rodata hro (fun i h => ?_) (by simpa using hn)
  simp only [List.length_map, List.length_range] at h
  obtain ⟨h1, h2⟩ := hb i h
  exact ⟨h1, by simp, by simpa using h2⟩

/-- `"%s expects %d argument(s), got %d"`: the name a C string. -/
theorem arity_fmt {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) {x1 : BitVec 64}
    (hs : ∃ t, CStrCov R rd x1.toNat t) (x2 x3 : BitVec 64) :
    FmtArgsOK R rd 0x800194a8#64 [x1, x2, x3] :=
  rodata_fmtS hro 0x800194a8 33 [.str, .int, .int] (by decide) (by decide) (by decide) (by decide)
    (by simp) (fun i hi hc => by
      match i, hi with
      | 0, _ => exact hs
      | 1, _ => cases hc
      | 2, _ => cases hc)

/-- `"%s"`: its argument a C string. -/
theorem pctS_fmt {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) {x1 : BitVec 64}
    (hs : ∃ t, CStrCov R rd x1.toNat t) (x2 : BitVec 64) :
    FmtArgsOK R rd 0x80019038#64 [x1, x2] :=
  rodata_fmtS hro 0x80019038 2 [.str] (by decide) (by decide) (by decide) (by decide)
    (by simp) (fun i hi _ => by
      match i, hi with
      | 0, _ => exact hs)

/-- An anonymous closure's name, `"<fn>"` (`0x800192d0`). -/
theorem anonName_cstr {R : Nat → Prop} {rd : Nat → BitVec 8}
    (hro : ∀ a, rodataDom a → R a ∧ rd a = rodataByte a) :
    ∃ t, CStrCov R rd (0x800192d0#64 : BitVec 64).toNat t :=
  ⟨(List.range 4).map (fun i => rodataByte (0x800192d0 + i)),
    cstrCov_rodata hro (fun i h => by
      simp only [List.length_map, List.length_range] at h
      have := (show ∀ i, i < 4 → rodataDom (0x800192d0 + i) ∧ rodataByte (0x800192d0 + i) ≠ 0
        by decide) i h
      exact ⟨this.1, by simp, by simpa using this.2⟩) (by decide)⟩

end VsaIris.Interp
