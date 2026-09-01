import Vsa.Sim.rows.StrcpyContract
import Vsa.Sim.StrcpySpecW3

/-!
# `StrcpyContractInhab` — the sound `strcpy` contract inhabited from `strcpy_full_spec`

Task #71 Part 2.  `Vsa/Sim/rows/StrcpyContract.lean` named `StrcpyContract` as a
typed residual, its doc claiming "no composed top-level `strcpy_full_spec` theorem
exists".  **That claim is STALE**: `Vsa/Sim/StrcpySpecW3.lean:1217`
`strcpy_full_spec` IS the complete entry-to-`ret` spec — the aligned word path and
the misaligned byte-head path unified by `Triple.cases` over the `0x80006dcc`
alignment test, `CString`-phrased.

## Law-4 obstruction: `StrcpyContract`'s post frame is UNSOUND

`StrcpyContract`'s post asserts `∀ R, StrcpyNotWritten R → get? R = g R` with
`StrcpyNotWritten := NotWrittenB` (= avoid `{x11, x14, x15}` + control).  But the
aligned WORD path uses `a2 = x12`, `a3 = x13`, `a6 = x16` as scratch and **does
NOT restore them before `ret`** (disasm `0x80006e00..0x80006e78`: no `ld a2/a3/a6`
on the exit path).  `strcpy_full_spec`'s honest post frame is therefore
`NotWrittenCpw` (= avoid `{x11..x16}` + control), which is STRICTLY stronger:
`NotWrittenB x16` holds yet `NotWrittenCpw x16` is false.  Machine-checked:

```
example : StrcpyNotWritten = NotWrittenB := rfl
example : NotWrittenB Register.x16 := by decide
example : ¬ NotWrittenCpw Register.x16 := by decide
example : ¬ (∀ R, NotWrittenB R → NotWrittenCpw R) :=
  fun h => (by decide) (h Register.x16 (by decide))
```

So `StrcpyContract` claims `get? x16 = g x16` for aligned inputs, contradicting
`strcpy`'s actual behaviour — the contract is FALSE on the word path and cannot be
inhabited.  Per CLAUDE.md law 4 we return the machine-checked obstruction and land
the CORRECTED contract `StrcpyContractCpw` (post frame = the honest `NotWrittenCpw`)
fully proved from `strcpy_full_spec`.  The concat C-block (`StrConcatHeap`) needs
only the `CString mem (new+|L|) R` readback + the outside-window frame from strcpy;
its own frame need is over the `NotWrittenCpw`-class scratch, so the corrected
contract suffices for gap 3.  `StrcpyContract.lean`'s `StrcpyNotWritten` alias
should be re-pointed to `NotWrittenCpw` (a one-line fix, out of scope here — the
file is read-only for this task).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)
open Vsa.MemRepr
open Vsa.Sim.Code (StrcpyLoaded)

namespace Vsa.Sim

/-! ## `cstr_shift_copy` — transport a `CStr` chain along a byte-equal copy

`CStr m0 src cs` reads `m0[src], m0[src+1], …, m0[src + cs.length]` (last = NUL).
If `mem[dst + k]? = m0[src + k]?` for every `k ≤ cs.length` (the copied window,
through the NUL — exactly what `strcpy_full_post` provides), the whole chain
transports to `CStr mem dst cs`.  Structural induction on the chain with a shifting
base; the window advances by one per `cons`. -/
theorem cstr_shift_copy {m0 mem : Mem} :
    ∀ {src dst : Nat} {cs : List Char}, CStr m0 src cs →
      (∀ k, k ≤ cs.length → mem[(dst + k)]? = m0[(src + k)]?) →
      CStr mem dst cs := by
  intro src dst cs hcstr
  induction hcstr generalizing dst with
  | @nil a hnul =>
    intro hcopy
    refine CStr.nil ?_
    have := hcopy 0 (Nat.zero_le _)
    simpa using this.trans (by simpa using hnul)
  | @cons a b cs hb hbne hb128 hrest ih =>
    intro hcopy
    refine CStr.cons (b := b) ?_ hbne hb128 ?_
    · have := hcopy 0 (Nat.zero_le _)
      simpa using this.trans (by simpa using hb)
    · refine ih (dst := dst + 1) (fun k hk => ?_)
      have := hcopy (k + 1) (by simp only [List.length_cons]; omega)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

/-- `CString` version of `cstr_shift_copy`. -/
theorem cstring_shift_copy {m0 mem : Mem} {src dst : Nat} {str : String}
    (h : CString m0 src str)
    (hcopy : ∀ k, k ≤ str.length → mem[(dst + k)]? = m0[(src + k)]?) :
    CString mem dst str := by
  obtain ⟨cs, hcstr, hs⟩ := h
  have hlen : cs.length = str.length := by rw [hs, String.length_ofList]
  exact ⟨cs, cstr_shift_copy hcstr (fun k hk => hcopy k (by omega)), hs⟩

/-! ## The geometry supplier

`strcpy_full_spec`'s pre needs the code image (`StrcpyLoaded`) and the region
geometry (`CpyRegions`/`CpwRegions`/`SrcWordMapped`) that `StrcpyContract`'s pre
does not carry.  We bundle them as ONE caller supplier keyed to `(dst, src, str,
m0)` — a data obligation, not a machine fact.  For the concat C-block: `dst =
new + |L|` (a fresh malloc block, disjoint from the arena `src`, in RAM above the
HTIF window) and `src` is a `CString`-holding stringify buffer (source words are
mapped). -/

/-- The `strcpy` geometry + code image the caller supplies for a given call. -/
structure StrcpyGeom (dst src : BitVec 64) (str : String)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  loaded : StrcpyLoaded m0
  cregions : CpyRegions dst src str.length
  wregions : CpwRegions dst src str.length
  srcword : SrcWordMapped m0 src (str.length / 8)

/-! ## `StrcpyContractCpw` — the sound contract (honest `NotWrittenCpw` frame) -/

/-- **The sound `strcpy(dst, src)` contract**, `CString`-copy post with the honest
frame split (`strcpy` clobbers `x12/x13/x16` — see the law-4 note above): the
caller pins `g` on the broader `NotWrittenCpy` set on entry (what the machine
actually reads/preserves), and only the narrower `NotWrittenCpw` set is restored on
exit (the clobbered word-scratch `x12/x13/x16` are NOT).  Otherwise identical to
`StrcpyContract`: from the entry (`x10=dst`, `x11=src`, `x1=r`, `CString m0 src
str`) run to a return at `r` with `x10=dst`, the whole C-string (incl. NUL) at
`[dst, dst+|str|+1)`, memory outside untouched. -/
def StrcpyContractCpw : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (str : String) (m0 : Std.ExtHashMap Nat (BitVec 8)),
    r.toNat % 4 = 0 → StrcpyGeom dst src str m0 →
    Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 strcpyEntry) ∧
        c.σ.regs.get? Register.x10 = some dst ∧
        c.σ.regs.get? Register.x11 = some src ∧
        c.σ.regs.get? Register.x1 = some r ∧
        c.σ.mem = m0 ∧ CString m0 src.toNat str ∧
        (∀ R, NotWrittenCpy R → c.σ.regs.get? R = g R))
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some r ∧
        c.σ.regs.get? Register.x10 = some dst ∧
        c.σ.regs.get? Register.x1 = some r ∧
        CString c.σ.mem dst.toNat str ∧
        (∀ a, (a < dst.toNat ∨ dst.toNat + (str.length + 1) ≤ a) →
          c.σ.mem[a]? = m0[a]?) ∧
        (∀ R, NotWrittenCpw R → c.σ.regs.get? R = g R))

/-- **`StrcpyContractCpw` inhabited** from `strcpy_full_spec` + the caller geometry.
For every call `(g,r,dst,src,str,m0)` with `r` 4-aligned and the geometry supplied:
run `strcpy_full_spec` (`strcpyEntry = 0x80006dc4`), transport the copied bytes to
`CString mem dst str` via `cstring_shift_copy`, and reindex the outside-window
clause (`dst+len < a` ⇔ `dst+(len+1) ≤ a`).  The frame classes align: the pre's
`NotWrittenCpw` frame is stronger than `strcpy_full_spec`'s `NotWrittenCpy` pre
need (`NotWrittenCpw R → NotWrittenCpy R`), and the post frame is `NotWrittenCpw`
verbatim. -/
theorem strcpyContractCpw_of_full : StrcpyContractCpw := by
  intro g r dst src str m0 halign hgeom
  intro c hpre
  obtain ⟨hG, htick, hpc, ha0, ha1, hra, hmem, hcstr, hframe⟩ := hpre
  obtain ⟨hloaded, hcreg, hwreg, hsrcw⟩ := hgeom
  obtain ⟨c', hsteps, hpost⟩ :=
    strcpy_full_spec g r dst src str m0 halign c
      { good := hG, loaded := hmem ▸ hloaded, pc := hpc, a0 := ha0, a1 := ha1, ra := hra,
        minstret := hG.minstret, tick := htick, cregions := hcreg, wregions := hwreg,
        cstring := hcstr, memeq := hmem, srcword := hsrcw,
        -- pre frame is `NotWrittenCpy` verbatim (what `strcpy_full_spec` needs).
        hframe := hframe }
  obtain ⟨hG', hpc', ha0', hra', ⟨bs, hsrcbytes, hdstbytes⟩, houtside, htick', hframe'⟩ := hpost
  refine ⟨c', hsteps, hG', htick', hpc', ha0', hra', ?_, ?_, hframe'⟩
  · -- `CString c'.σ.mem dst.toNat str`: `mem[dst+k]? = bs k = m0[src+k]?` for k ≤ len.
    refine cstring_shift_copy (m0 := m0) (src := src.toNat) (dst := dst.toNat) (str := str)
      hcstr (fun k hk => ?_)
    rw [hdstbytes k hk, ← hsrcbytes k hk]
  · -- outside-window: `dst.toNat + (str.length + 1) ≤ a` ⇒ `dst.toNat + str.length < a`.
    intro a ha
    exact houtside a (ha.imp id (fun h => by omega))

#print axioms cstr_shift_copy
#print axioms cstring_shift_copy
#print axioms strcpyContractCpw_of_full

end Vsa.Sim
