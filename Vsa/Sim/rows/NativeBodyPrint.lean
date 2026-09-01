import Vsa.Sim.rows.NativeArmSplice
import Vsa.Sim.EvalCallPrint
import Vsa.Sim.EvalSimCommon

/-!
# `NativeBodyPrint` — the print/println body legs of the native splice (wave 42)

The `hBody` premises of `nativePrintSpec_of_splice` / `nativePrintlnSpec_of_splice`
(`rows/NativeArmSplice.lean`), reduced to ONE named internal-run residual each,
through ONE shared marshal (`nativeBodyOut` — the parametric
callee-internal-run → `NativeBody*` boundary rebuild, the print/println twin of
`nativeBodyAssert`'s naEntry/naExit marshal, factored over the appended output
string `outApp` so print and println are INSTANCES, not clones).

## Scale honesty (wave-39 warning upheld)

`native_print`'s internal run (`0x80002ed4 … ret`) is a LOOP over the argument
vector whose every iteration calls `value_print` (`0x800028fc` — renders any
`Value`; `int` routes through the landed `snprintf_lld_spec` `%lld` path) and,
between values, `fputc(' ', stdout)` (`0x800062e0` — the newlib buffered-IO
path down to the HTIF `tohost` putchar).  NO site battery or code image exists
for `value_print`/`fputc` internals yet, so the internal runs stay NAMED
RESIDUALS this wave (`NativePrintInternal`/`NativePrintlnInternal`), stated
over named-field boundary structures (`NativePrintEntry`/`NativeFnOutExit`)
rich enough for the eventual `loopFromBody` discharge:

* prologue seg (`0x80002ed4 → 0x80002f08 → j 0x80002f1c`, plus the `blez a2`
  empty-args arm straight to `0x80002f60`) — `#derive_case`/`genseg.py` spans
  over `Native_printLoaded`;
* the loop, head at the back-edge `bne s3,s1 @ 0x80002f4c`, via `loopFromBody`
  (`DeriveLoop`), measure `argc - i`; per-iteration = fputc-seam ≫ body block ≫
  value_print-seam, output growing by `" " ++ Value.display` per iteration —
  the `printedPrefix` algebra (§1) supplies the invariant arithmetic;
* the exit leg (`0x80002f50` restores ≫ `jal value_null` ≫ epilogue `ret`).

RISK NOTE (for the residual prover): `fputc` may write the `_impure_ptr` FILE
state (data segment, OUTSIDE the stack) — if so, `NativeFnOutExit.memFrame`'s
stack-confinement is unsatisfiable as stated and the carve must be amended
(coordinator decision; `NativeBodyPost.memFrame` would need the same carve).
The HTIF `tohost` store itself does NOT touch `σ.mem` (`htif_store_putchar`
changes only the HTIF CSRs + `sailOutput`), so no tohost carve is needed.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Scaffold

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## §1. `printedPrefix` — the loop-invariant output algebra

`printArgs s vs = String.intercalate " " (vs.map (Value.display s))`.  The
print loop renders one value per iteration; at the back-edge head
(`0x80002f4c`, `s1 = i ≥ 1`) the console has grown by exactly the first-`i`
intercalation.  `String.intercalate`'s worker is inaccessible (`go✝`), so the
algebra rides on the definitional acc-shift
`intercalate s (a :: x :: l) = intercalate s ((a ++ s ++ x) :: l)` (both sides
ARE `go (a ++ s ++ x) s l`). -/

/-- The separator-prefixed tail:
`sepTail s l = s ++ l₀ ++ s ++ l₁ ++ …` (empty for `[]`). -/
def sepTail (s : String) : List String → String
  | [] => ""
  | a :: l => s ++ a ++ sepTail s l

/-- Characterize `String.intercalate` without naming its hidden worker:
head ++ separator-prefixed tail. -/
theorem intercalate_eq_sepTail (s : String) (l : List String) (a : String) :
    String.intercalate s (a :: l) = a ++ sepTail s l := by
  induction l generalizing a with
  | nil =>
    show String.intercalate s [a] = a ++ ""
    rw [show String.intercalate s [a] = a from rfl]
    simp
  | cons x xs ih =>
    rw [show String.intercalate s (a :: x :: xs)
          = String.intercalate s ((a ++ s ++ x) :: xs) from rfl, ih]
    show a ++ s ++ x ++ sepTail s xs = a ++ (s ++ x ++ sepTail s xs)
    simp [String.append_assoc]

/-- `sepTail` over a snoc: one more separator + element at the end. -/
theorem sepTail_append (s : String) (l : List String) (x : String) :
    sepTail s (l ++ [x]) = sepTail s l ++ s ++ x := by
  induction l with
  | nil => show s ++ x ++ "" = "" ++ s ++ x; simp
  | cons a as ih =>
    show s ++ a ++ sepTail s (as ++ [x]) = s ++ a ++ sepTail s as ++ s ++ x
    rw [ih]; simp [String.append_assoc]

/-- `intercalate` over a nonempty snoc: append one separator + element. -/
theorem intercalate_append_singleton (s : String) (a : String) (l : List String)
    (x : String) :
    String.intercalate s ((a :: l) ++ [x])
      = String.intercalate s (a :: l) ++ s ++ x := by
  rw [show (a :: l) ++ [x] = a :: (l ++ [x]) from rfl,
    intercalate_eq_sepTail, intercalate_eq_sepTail, sepTail_append]
  simp [String.append_assoc]

/-- The console prefix after the first `i` arguments are rendered:
the intercalation of their displays. -/
def printedPrefix (s : Store) (vs : List Value) (i : Nat) : String :=
  String.intercalate " " ((vs.take i).map (Value.display s))

/-- Rendering all arguments gives exactly `printArgs`. -/
theorem printedPrefix_full (s : Store) (vs : List Value) :
    printedPrefix s vs vs.length = printArgs s vs := by
  unfold printedPrefix printArgs
  rw [List.take_of_length_le (Nat.le_refl _)]

/-- The first argument's render (loop entry, `i = 1`). -/
theorem printedPrefix_one (s : Store) (v : Value) (vs : List Value) :
    printedPrefix s (v :: vs) 1 = Value.display s v := by
  unfold printedPrefix
  rw [show (v :: vs).take 1 = [v] from by simp,
    show ([v]).map (Value.display s) = [Value.display s v] from rfl]
  rfl

/-- The per-iteration step (`1 ≤ i`): one separator space + the `i`-th display.
This is the invariant arithmetic of the back-edge iteration
(fputc `' '` ≫ `value_print vs[i]`). -/
theorem printedPrefix_step (s : Store) (vs : List Value) (i : Nat)
    (h1 : 1 ≤ i) (hi : i < vs.length) :
    printedPrefix s vs (i + 1)
      = printedPrefix s vs i ++ " " ++ Value.display s vs[i] := by
  unfold printedPrefix
  rw [List.take_add_one, getElem?_pos vs i hi]
  cases htake : vs.take i with
  | nil =>
    exfalso
    have := List.length_take (i := i) (l := vs)
    rw [htake] at this
    simp at this
    omega
  | cons a l =>
    rw [show Option.toList (some vs[i]) = [vs[i]] from rfl, List.map_append,
      show ([vs[i]]).map (Value.display s) = [Value.display s vs[i]] from rfl,
      List.map_cons, intercalate_append_singleton]

/-! ## §2. The internal-run boundary structures (named-field, R6) -/

/-- **Region facts for a print-family internal run.**  `fsp` is the native's
entry `sp` (`= spv`, `eval_expr`'s stack pointer — the native and every callee
below it build frames DOWNWARD from `fsp`); `sret` the CALL sret buffer;
`argsBase` the marshalled arg vector.  The headroom bound (4096 bytes) covers
the deepest render path (`value_print → snprintf → _svfprintf_r`); amend if the
measured depth exceeds it. -/
structure NativePrintRegion (SL : StackLayout) (fsp sret argsBase : BitVec 64) : Prop where
  /-- the native + callee frames stay inside the stack region (4096-byte
  headroom below `fsp`). -/
  fspStack : SL.lo + 4096 ≤ fsp.toNat ∧ fsp.toNat ≤ SL.hi
  fspAlign : fsp.toNat % 16 = 0
  /-- the sret window sits inside the stack region (an `eval_expr` frame slot). -/
  sretStack : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi
  sretAlign : sret.toNat % 8 = 0
  sretWin : tohostAddr + 16 ≤ sret.toNat
  /-- the arg vector sits at/above the native's entry `sp` (`spv + 240`). -/
  argsAboveFsp : fsp.toNat ≤ argsBase.toNat
  argsAlign : argsBase.toNat % 8 = 0
  argsWin : tohostAddr + 8 ≤ argsBase.toNat
  /-- the stack region is RAM. -/
  stackRam : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000

/-- **The print-family internal-run ENTRY** (`g` is the run's own ghost frame;
`entryPC` = `nativePrintPC` / `nativePrintlnPC`).  Code-loaded facts for the
specific native ride in the `Extra` conjunct of the residual, NOT here. -/
structure NativePrintEntry
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sStore : Store) (vs : List Value) (out0 : String) (entryPC : Nat)
    (fsp sret retAddr interp argsBase scratch : BitVec 64) (m0 : Mem)
    (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 entryPC)
  a0 : c.σ.regs.get? Register.x10 = some sret
  a1 : c.σ.regs.get? Register.x11 = some interp
  a2 : c.σ.regs.get? Register.x12 = some (BitVec.ofNat 64 vs.length)
  a3 : c.σ.regs.get? Register.x13 = some argsBase
  a4 : c.σ.regs.get? Register.x14 = some scratch
  ra : c.σ.regs.get? Register.x1 = some retAddr
  sp : c.σ.regs.get? Register.x2 = some fsp
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  /-- the whole spec store represented (`value_print` reads closure names). -/
  store : StoreRepr m0 N A φf φc sStore
  /-- the console so far. -/
  out : Vsa.Machine.output c.σ = out0
  /-- the arg vector, one 24-byte `ValueRepr` slot per argument. -/
  args : ∀ i, (hi : i < vs.length) →
    ValueRepr m0 N φc (argsBase.toNat + 24 * i) vs[i]
  argsBytes : ∀ j : Nat, j < 24 * vs.length → ∃ b, m0[argsBase.toNat + j]? = some b
  region : NativePrintRegion SL fsp sret argsBase
  /-- the `ret` target is 4-aligned. -/
  rettgt : (BitVec.update (retAddr + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0
  /-- the ghost-frame tie. -/
  frame : ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R

/-- **The print-family internal-run EXIT** — parked at the (bit-0-cleared)
`ret` target with `.null` in `sret`, the console grown by exactly `outApp`,
memory framed to `m0` at/above `fsp` and outside the stack region (except the
sret write), and the FULL ABI callee-saved frame restored (the amended-`naExit`
lesson: state the frame from day one). -/
structure NativeFnOutExit
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Addr → Nat) (SL : StackLayout)
    (fsp sret retAddr : BitVec 64) (outApp out0 : String) (m0 : Mem)
    (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC
    = some (BitVec.update (retAddr + sign_extend (m := 64) (0x000#12)) 0 0#1)
  /-- `.null` written into the CALL sret. -/
  sretNull : ValueRepr c.σ.mem N φc sret.toNat .null
  /-- **The output-append contract** — the whole point of the print natives. -/
  out : Vsa.Machine.output c.σ = out0 ++ outApp
  /-- memory framed: everything at/above `fsp` and everything outside the
  stack region is untouched, except the 24-byte sret write.  (The HTIF
  `tohost` store never touches `σ.mem`.) -/
  memFrame : ∀ a : Nat, (fsp.toNat ≤ a ∨ ¬ (SL.lo ≤ a ∧ a < SL.hi)) →
    (a < sret.toNat ∨ sret.toNat + 24 ≤ a) → c.σ.mem[a]? = m0[a]?
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  /-- the FULL ABI callee-saved frame. -/
  frame : ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R

/-! ## §3. The named internal-run residuals -/

/-- **The print-specific `Extra`** riding beside the boundary (code images of
the native itself + `value_null`; the `value_print`/`fputc` internals have NO
code images yet — the residual prover generates them and adds their loaded
facts HERE). -/
structure NativePrintExtra (c : Config) : Prop where
  loadedNP : Vsa.Sim.Code.Native_printLoaded c.σ.mem
  loadedVN : Vsa.Sim.Code.Value_nullLoaded c.σ.mem

/-- The println `Extra`: print's plus `native_println`'s own image. -/
structure NativePrintlnExtra (c : Config) : Prop where
  loadedNPln : Vsa.Sim.Code.Native_printlnLoaded c.σ.mem
  loadedNP : Vsa.Sim.Code.Native_printLoaded c.σ.mem
  loadedVN : Vsa.Sim.Code.Value_nullLoaded c.σ.mem

/-- **NAMED RESIDUAL — the `native_print` internal run** (`0x80002ed4 … ret`):
render the arg vector space-separated (console `+= printArgs sStore vs`),
`.null` into sret, stack-confined writes, full ABI frame.  Discharge shape
(multi-wave, per the wave-39 warning):
prologue seg (`genseg.py` over `Native_printLoaded`, `blez` empty-args arm) ≫
`loopFromBody` at the `0x80002f4c` back-edge (measure `argc - i`, invariant
output `= out0 ++ printedPrefix sStore vs i` — §1 supplies the step algebra)
with per-iteration `fputc(' ')` ≫ body block ≫ `value_print vs[i]` seams
(`callSeg`; the two callee contracts are the genuine machine frontier — no
site battery or code image exists for either yet) ≫ restores ≫
`value_null_spec_full` ≫ epilogue `ret`. -/
def NativePrintInternal (N : NativeAddrs) (A : Arena) (SL : StackLayout) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R)) (φf φc : Addr → Nat)
    (sStore : Store) (vs : List Value) (out0 : String)
    (fsp sret retAddr interp argsBase scratch : BitVec 64) (m0 : Mem),
    Triple
      (fun c => NativePrintEntry g N A SL φf φc sStore vs out0 nativePrintPC
          fsp sret retAddr interp argsBase scratch m0 c ∧ NativePrintExtra c)
      (NativeFnOutExit g N φc SL fsp sret retAddr (printArgs sStore vs) out0 m0)

/-- **NAMED RESIDUAL — the `native_println` internal run** (`0x80002f7c … ret`):
`native_print` ≫ one trailing `fputc('\n')` ≫ `value_null` — console
`+= printArgs sStore vs ++ "\n"`.  Discharge = a thin wrapper seg around
`NativePrintInternal`'s Triple plus the single newline HTIF append. -/
def NativePrintlnInternal (N : NativeAddrs) (A : Arena) (SL : StackLayout) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R)) (φf φc : Addr → Nat)
    (sStore : Store) (vs : List Value) (out0 : String)
    (fsp sret retAddr interp argsBase scratch : BitVec 64) (m0 : Mem),
    Triple
      (fun c => NativePrintEntry g N A SL φf φc sStore vs out0 nativePrintlnPC
          fsp sret retAddr interp argsBase scratch m0 c ∧ NativePrintlnExtra c)
      (NativeFnOutExit g N φc SL fsp sret retAddr
        (printArgs sStore vs ++ "\n") out0 m0)

/-! ## §4. The shared marshal — internal run → `NativeBodyPre/Post` boundary

ONE theorem, parametric over the appended output `outApp`, the entry PC, and
the `Extra` rider — print and println (and any future output native) are
instances.  (`nativeBodyAssert` is the third sibling of this shape; see the
observation `native-fnbody-marshal-shape` for the factoring note.) -/

/-- **The output-native body leg** — `Triple (NativeBodyPre ∧ Extra)
(NativeBodyPost @ output-appended state)` from the ∀-quantified internal-run
Triple.  The internal ghost frame is instantiated at the entry config's own
reads (`naEntry`-style: the tie is `rfl`, and the framed exit hands back the
entry values, which `NativeBodyPre.frame` ties to the arm ghost `g`). -/
theorem nativeBodyOut
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (vs : List Value) (outApp : String) (fentry : Nat)
    (spv s7v sret interp argsBase scratch : BitVec 64) (m0 : Mem)
    (Extra : Config → Prop)
    (hRG : NativePrintRegion SL spv sret argsBase)
    (hsretSlot : sret.toNat + 24 ≤ spv.toNat + 1016 ∨ spv.toNat + 1024 ≤ sret.toNat)
    (hcodeStack : ∀ a : Nat, 0x80003164 ≤ a → a < 0x80003fe0 →
      ¬ (SL.lo ≤ a ∧ a < SL.hi))
    (hInternal : ∀ (g_np : (R : Register) → Option (RegisterType R))
        (out0 : String) (m0' : Mem),
        Triple
          (fun c => NativePrintEntry g_np N A SL φf φc st.store vs out0 fentry
              spv sret (0x800039f8#64) interp argsBase scratch m0' c ∧ Extra c)
          (NativeFnOutExit g_np N φc SL spv sret (0x800039f8#64) outApp out0 m0')) :
    Triple
      (fun c => NativeBodyPre g N A SL φf φc st vs fentry
          spv s7v sret interp argsBase scratch m0 c ∧ Extra c)
      (NativeBodyPost g N A SL φf φc ⟨st.store, st.out ++ outApp⟩ spv s7v m0) := by
  intro c hc
  obtain ⟨hpre, hextra⟩ := hc
  obtain ⟨vm, hvm⟩ := hpre.minstret
  -- the internal run's ghost frame := the entry config's own reads
  have hentry : NativePrintEntry (fun R => c.σ.regs.get? R) N A SL φf φc
      st.store vs st.out fentry spv sret (0x800039f8#64) interp argsBase
      scratch c.σ.mem c :=
    { good := hpre.good
      tick := hpre.tick
      mem := rfl
      pc := hpre.pc
      a0 := hpre.a0
      a1 := hpre.a1
      a2 := hpre.a2
      a3 := hpre.a3
      a4 := hpre.a4
      ra := hpre.ra
      sp := hpre.sp
      minstret := ⟨vm, hvm⟩
      store := hpre.store
      out := hpre.out
      args := hpre.args
      argsBytes := hpre.argsBytes
      region := hRG
      rettgt := by decide
      frame := fun R _ => rfl }
  -- run the internal body
  obtain ⟨c', hsteps, hexit⟩ :=
    hInternal (fun R => c.σ.regs.get? R) st.out c.σ.mem c ⟨hentry, hextra⟩
  -- the sret window sits inside the stack region: an address OUTSIDE the
  -- stack automatically avoids the sret carve
  have hsretIn : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) →
      (a < sret.toNat ∨ sret.toNat + 24 ≤ a) := by
    intro a ha
    have h1 := hRG.sretStack.1
    have h2 := hRG.sretStack.2
    by_cases hlo : a < sret.toNat
    · exact Or.inl hlo
    · refine Or.inr ?_
      by_cases hhi : sret.toNat + 24 ≤ a
      · exact hhi
      · exact absurd ⟨by omega, by omega⟩ ha
  refine ⟨c', hsteps, ?_⟩
  refine
    { good := hexit.good
      tick := hexit.tick
      pc := ?_
      minstret := hexit.minstret
      loaded := ?_
      store := ?_
      out := ?_
      frame := ?_
      s7slot := ?_
      memFrame := ?_ }
  · -- PC at the return link (the aligned ret target is the link itself)
    have := hexit.pc
    rwa [show BitVec.update ((0x800039f8#64 : BitVec 64)
        + sign_extend (m := 64) (0x000#12)) 0 0#1 = (0x800039f8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  · -- Eval_exprLoaded survives: the code region is off the stack, hence framed
    refine loaded_eval_expr_agreeP c.σ.mem c'.σ.mem (fun a ha => ?_) hpre.loaded
    have hns := hcodeStack a ha.1 ha.2
    exact (hexit.memFrame a (Or.inr hns) (hsretIn a hns)).symm
  · -- StoreRepr: the internal writes are stack-confined (+ sret, in-stack);
    -- storeSurv absorbs them
    refine hpre.storeSurv c'.σ.mem (fun k hk1 _hk2 => ?_)
    exact (hexit.memFrame k (Or.inr hk1) (hsretIn k hk1)).symm
  · -- OutRepr at the output-appended spec state
    show Vsa.Machine.output c'.σ = st.out ++ outApp
    exact hexit.out
  · -- callee-saved (except s7) back to the arm ghost: the framed exit hands
    -- back the ENTRY reads, which NativeBodyPre.frame ties to g
    intro R hR hne
    exact (hexit.frame R hR).trans (hpre.frame R hR hne)
  · -- the s7 spill image survives (at/above fsp = spv, off the sret window)
    intro i hi
    have := hexit.memFrame (spv.toNat + 1016 + i) (Or.inl (by omega))
      (by rcases hsretSlot with h | h
          · exact Or.inr (by omega)
          · exact Or.inl (by omega))
    rw [this]
    exact hpre.s7slot i hi
  · -- memory outside stack ∪ arena: exit = entry = m0
    intro a ha hA
    have hout1 : c'.σ.mem[a]? = c.σ.mem[a]? :=
      hexit.memFrame a (Or.inr ha) (hsretIn a ha)
    rw [hout1]
    exact hpre.memFrame a ha hA

#print axioms nativeBodyOut

/-! ## §5. The print/println body legs + spec assemblies -/

/-- **The print body leg** from the internal-run residual. -/
theorem nativeBodyPrint
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (vs : List Value) (fentry : Nat)
    (spv s7v sret interp argsBase scratch : BitVec 64) (m0 : Mem)
    (hfe : fentry = nativePrintPC)
    (hRG : NativePrintRegion SL spv sret argsBase)
    (hsretSlot : sret.toNat + 24 ≤ spv.toNat + 1016 ∨ spv.toNat + 1024 ≤ sret.toNat)
    (hcodeStack : ∀ a : Nat, 0x80003164 ≤ a → a < 0x80003fe0 →
      ¬ (SL.lo ≤ a ∧ a < SL.hi))
    (hInternal : NativePrintInternal N A SL) :
    Triple
      (fun c => NativeBodyPre g N A SL φf φc st vs fentry
          spv s7v sret interp argsBase scratch m0 c ∧ NativePrintExtra c)
      (NativeBodyPost g N A SL φf φc ⟨st.store, st.out ++ printArgs st.store vs⟩
        spv s7v m0) := by
  subst hfe
  exact nativeBodyOut g N A SL φf φc st vs (printArgs st.store vs) nativePrintPC
    spv s7v sret interp argsBase scratch m0 NativePrintExtra
    hRG hsretSlot hcodeStack
    (fun g_np out0 m0' =>
      hInternal g_np φf φc st.store vs out0 spv sret (0x800039f8#64)
        interp argsBase scratch m0')

/-- **The println body leg** from the internal-run residual. -/
theorem nativeBodyPrintln
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (vs : List Value) (fentry : Nat)
    (spv s7v sret interp argsBase scratch : BitVec 64) (m0 : Mem)
    (hfe : fentry = nativePrintlnPC)
    (hRG : NativePrintRegion SL spv sret argsBase)
    (hsretSlot : sret.toNat + 24 ≤ spv.toNat + 1016 ∨ spv.toNat + 1024 ≤ sret.toNat)
    (hcodeStack : ∀ a : Nat, 0x80003164 ≤ a → a < 0x80003fe0 →
      ¬ (SL.lo ≤ a ∧ a < SL.hi))
    (hInternal : NativePrintlnInternal N A SL) :
    Triple
      (fun c => NativeBodyPre g N A SL φf φc st vs fentry
          spv s7v sret interp argsBase scratch m0 c ∧ NativePrintlnExtra c)
      (NativeBodyPost g N A SL φf φc
        ⟨st.store, st.out ++ (printArgs st.store vs ++ "\n")⟩ spv s7v m0) := by
  subst hfe
  exact nativeBodyOut g N A SL φf φc st vs (printArgs st.store vs ++ "\n")
    nativePrintlnPC spv s7v sret interp argsBase scratch m0 NativePrintlnExtra
    hRG hsretSlot hcodeStack
    (fun g_np out0 m0' =>
      hInternal g_np φf φc st.store vs out0 spv sret (0x800039f8#64)
        interp argsBase scratch m0')

/-- **`NativePrintSpec` reduced** to the dispatch leg + the internal-run
residual (the `hCallPrint` RemainingWork field, one splice away). -/
theorem nativePrintSpec_of_internal
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (m0 : Mem) (vs : List Value)
    (fentry : Nat) (spv s7v sret interp argsBase scratch : BitVec 64)
    (hfe : fentry = nativePrintPC)
    (hgsp : g Register.x2 = some spv)
    (hgs7 : g Register.x23 = some s7v)
    (hslotLo : 0x80000000 ≤ spv.toNat + 1016)
    (hslotHi : spv.toNat + 1024 ≤ 0x100000000)
    (hslotHtif : spv.toNat + 1024 ≤ tohostAddr ∨ tohostAddr + 8 ≤ spv.toNat + 1016)
    (hslotAlign : (spv.toNat + 1016) % 8 = 0)
    (hRG : NativePrintRegion SL spv sret argsBase)
    (hsretSlot : sret.toNat + 24 ≤ spv.toNat + 1016 ∨ spv.toNat + 1024 ≤ sret.toNat)
    (hcodeStack : ∀ a : Nat, 0x80003164 ≤ a → a < 0x80003fe0 →
      ¬ (SL.lo ≤ a ∧ a < SL.hi))
    (hInternal : NativePrintInternal N A SL)
    (hDispatch : Triple (CallEntryP g N A SL φf φc st d dLeft aLeft m0)
      (fun c => NativeBodyPre g N A SL φf φc st vs fentry
          spv s7v sret interp argsBase scratch m0 c ∧ NativePrintExtra c)) :
    NativePrintSpec g N A SL φf φc st d dLeft aLeft m0 vs :=
  nativePrintSpec_of_splice g N A SL φf φc st d dLeft aLeft m0 vs spv s7v _
    hgsp hgs7 hslotLo hslotHi hslotHtif hslotAlign hDispatch
    (nativeBodyPrint g N A SL φf φc st vs fentry
      spv s7v sret interp argsBase scratch m0
      hfe hRG hsretSlot hcodeStack hInternal)

/-- **`NativePrintlnSpec` reduced** to the dispatch leg + the internal-run
residual (the `hCallPrintln` RemainingWork field, one splice away). -/
theorem nativePrintlnSpec_of_internal
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : SpecSt) (d : Nat) (dLeft aLeft : Nat) (m0 : Mem) (vs : List Value)
    (fentry : Nat) (spv s7v sret interp argsBase scratch : BitVec 64)
    (hfe : fentry = nativePrintlnPC)
    (hgsp : g Register.x2 = some spv)
    (hgs7 : g Register.x23 = some s7v)
    (hslotLo : 0x80000000 ≤ spv.toNat + 1016)
    (hslotHi : spv.toNat + 1024 ≤ 0x100000000)
    (hslotHtif : spv.toNat + 1024 ≤ tohostAddr ∨ tohostAddr + 8 ≤ spv.toNat + 1016)
    (hslotAlign : (spv.toNat + 1016) % 8 = 0)
    (hRG : NativePrintRegion SL spv sret argsBase)
    (hsretSlot : sret.toNat + 24 ≤ spv.toNat + 1016 ∨ spv.toNat + 1024 ≤ sret.toNat)
    (hcodeStack : ∀ a : Nat, 0x80003164 ≤ a → a < 0x80003fe0 →
      ¬ (SL.lo ≤ a ∧ a < SL.hi))
    (hInternal : NativePrintlnInternal N A SL)
    (hDispatch : Triple (CallEntryP g N A SL φf φc st d dLeft aLeft m0)
      (fun c => NativeBodyPre g N A SL φf φc st vs fentry
          spv s7v sret interp argsBase scratch m0 c ∧ NativePrintlnExtra c)) :
    NativePrintlnSpec g N A SL φf φc st d dLeft aLeft m0 vs := by
  refine nativePrintlnSpec_of_splice g N A SL φf φc st d dLeft aLeft m0 vs spv s7v _
    hgsp hgs7 hslotLo hslotHi hslotHtif hslotAlign hDispatch ?_
  have h := nativeBodyPrintln g N A SL φf φc st vs fentry
    spv s7v sret interp argsBase scratch m0
    hfe hRG hsretSlot hcodeStack hInternal
  rwa [show st.out ++ (printArgs st.store vs ++ "\n")
      = st.out ++ printArgs st.store vs ++ "\n" from by
    rw [String.append_assoc]] at h

#print axioms nativeBodyPrint
#print axioms nativeBodyPrintln
#print axioms nativePrintSpec_of_internal
#print axioms nativePrintlnSpec_of_internal
#print axioms printedPrefix_full
#print axioms printedPrefix_step

end Vsa.Sim
