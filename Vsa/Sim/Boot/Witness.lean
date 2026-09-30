import Vsa.Sim.Boot.Physical
import Vsa.Sim.Boot.Fill
import Vsa.Sim.Boot.FastCheck

/-!
# Generic boot witnesses

A `Witness` bundles a boot trace (`script`, `log`, `regs`, `entrySteps`) with the data
derived from it (`runs`, `own`, heap layout, `stmts`/`count`) and the program. `Witness.Ok`
lists the closed Boolean checks, one named field each; every program proves each field by
one `decide +kernel`. From `W.Ok`, `Witness.Ok.loaded` and its siblings give the `Loaded`
witnesses once, for every program.

The fixed runtime bytes that `BootMemFacts` reads (newlib's streams, locale and exit data,
`main`'s saved return address, the interpreter's call depth) are the same in every boot; they
are listed once in `memRef` and each program checks its view against the list.
-/

namespace Vsa.Sim.Boot

open Vsa.MemRepr Vsa.While Vsa.Sim.LayoutInstance

/-- Fixed-address reference words `(address, width, little-endian value)` read by
`BootMemFacts` other than the image, the globals pointer and the stack. -/
def memRef : List (Nat × Nat × Nat) :=
  [(0x87fffff8, 8, 0x80000038), (0x800192c0, 8, 0x646c6c25), (0x80019770, 8, 0x2e),
   (0x8001a20c, 4, 0xfffedf0c), (0x8001a22c, 4, 0xfffee438), (0x8001b880, 8, 0x80012268),
   (0x8001b898, 8, 0x80019770), (0x8001b8f8, 1, 0x1), (0x8001b970, 8, 0x8001b538),
   (0x8001b548, 8, 0x8001bb20), (0x8001b580, 8, 0x80005d2c), (0x8001bb20, 8, 0x8001bb97),
   (0x8001bb28, 4, 0x0), (0x8001bb2c, 4, 0x0), (0x8001bb30, 2, 0xa), (0x8001bb32, 2, 0x1),
   (0x8001bb38, 8, 0x8001bb97), (0x8001bb40, 4, 0x1), (0x8001bb48, 4, 0x0),
   (0x8001bb50, 8, 0x8001bb20), (0x8001bb60, 8, 0x8000efd4), (0x8001bbc0, 8, 0x0),
   (0x8001bbd0, 4, 0x0), (0x8001bb97, 1, 0x0), (0x87fffe18, 4, 0x0), (0x8001b9f8, 8, 0x0),
   (0x8001b978, 8, 0x8001b9e8), (0x8001b9b0, 8, 0x80005d18), (0x8001b520, 8, 0x0),
   (0x8001b528, 4, 0x3), (0x8001b530, 8, 0x8001ba68), (0x8001bb70, 8, 0x8000f0c0),
   (0x8001bb78, 8, 0x0), (0x8001bb98, 8, 0x0), (0x8001ba70, 4, 0x0), (0x8001ba78, 2, 0x4),
   (0x8001ba7a, 2, 0x0), (0x8001ba98, 8, 0x8001ba68), (0x8001bab8, 8, 0x8000f0c0),
   (0x8001bac0, 8, 0x0), (0x8001bad8, 4, 0x0), (0x8001bae0, 8, 0x0), (0x8001bb08, 8, 0x0),
   (0x8001bb18, 4, 0x0), (0x8001bbe0, 4, 0x0), (0x8001bbe8, 2, 0x12), (0x8001bbea, 2, 0x2),
   (0x8001bc08, 8, 0x8001bbd8), (0x8001bc28, 8, 0x8000f0c0), (0x8001bc30, 8, 0x0),
   (0x8001bc48, 4, 0x0), (0x8001bc50, 8, 0x0), (0x8001bc78, 8, 0x0), (0x8001bc88, 4, 0x0)]

/-- The byte view `memRef` describes. -/
def refView (a : Nat) : Option (BitVec 8) :=
  match memRef.find? (fun r => decide (r.1 ≤ a ∧ a < r.1 + r.2.1)) with
  | some r => some (BitVec.ofNat 8 (r.2.2 >>> (8 * (a - r.1))))
  | none => none

def memRefCheck (v : Nat → Option (BitVec 8)) : Bool :=
  memRef.all fun r => readLEv v r.1 r.2.1 == some r.2.2

theorem readLEv_byte {v : Nat → Option (BitVec 8)} :
    ∀ {n a w}, readLEv v a n = some w → ∀ {k}, a ≤ k → k < a + n →
      v k = some (BitVec.ofNat 8 (w >>> (8 * (k - a)))) := by
  intro n
  induction n with
  | zero => intro a w _ k h1 h2; omega
  | succ n ih =>
    intro a w h k h1 h2
    simp only [readLEv] at h
    cases hb : v a with
    | none => rw [hb] at h; cases h
    | some b =>
      cases hr : readLEv v (a + 1) n with
      | none => rw [hb, hr] at h; cases h
      | some r =>
        rw [hb, hr] at h
        have hw : b.toNat + 256 * r = w := by simpa using h
        subst hw
        by_cases hk : k = a
        · subst hk
          rw [hb, Nat.sub_self, Nat.mul_zero, Nat.shiftRight_zero]
          congr 1
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_ofNat]
          have := b.isLt
          omega
        · have hk' : a + 1 ≤ k := by omega
          rw [ih hr hk' (by omega)]
          congr 2
          have he : 8 * (k - a) = 8 + 8 * (k - (a + 1)) := by omega
          rw [he, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (m := b.toNat + 256 * r) (n := 8)]
          congr 1
          have := b.isLt
          show r = (b.toNat + 256 * r) / 256
          omega

theorem PartialView.ref {m : Mem} {v : Nat → Option (BitVec 8)} (hv : PartialView m v)
    (hc : memRefCheck v = true) : PartialView m refView := by
  intro k b hk
  unfold refView at hk
  split at hk
  · rename_i r hr
    cases hk
    have hmem := List.mem_of_find?_eq_some hr
    have hin : r.1 ≤ k ∧ k < r.1 + r.2.1 := by
      have := List.find?_some hr
      simpa using this
    have hread : readLEv v r.1 r.2.1 = some r.2.2 := by
      have := List.all_eq_true.mp hc r hmem
      simpa using this
    exact hv k _ (readLEv_byte hread hin.1 hin.2)
  · cases hk

theorem RunTree.above_mono {t : RunTree} {lo lo' : Nat} (h : t.above lo = true) (hl : lo' ≤ lo) :
    t.above lo' = true := by
  unfold RunTree.above at *
  rw [List.all_eq_true] at *
  intro r hr
  have := h r hr
  simp only [decide_eq_true_eq] at *
  omega

theorem bootMemFacts_of_ref {m : Mem} {e : Nat} (hr : PartialView m refView)
    (htext : Code.FixedTextLoaded m) (hrodata : Code.FixedRodataLoaded m)
    (hg : read64 m interpObject = some e)
    (hstack : ∀ k, stackSL.lo ≤ k → k < stackSL.hi → ∃ b : BitVec 8, m[k]? = some b) :
    BootMemFacts m e where
  mainRa := by boot_readp hr
  text := htext
  rodata := hrodata
  statics := by
    unfold Vsa.Sim.Code.ImageStaticsLoaded Vsa.Sim.Code.imgLldFmt Vsa.Sim.Code.imgDecPointStr
      Vsa.Sim.Code.imgParseSlotD Vsa.Sim.Code.imgParseSlotL Vsa.Sim.Code.imgFnSlot
      Vsa.Sim.Code.imgDecPointPtr Vsa.Sim.Code.imgMbCurMax Vsa.Sim.Code.imgImpurePtr
    boot_factsp hr
  console := by boot_factsp hr
  exitRuntime := by boot_factsp hr
  globals := hg
  depth := by boot_readp hr
  stackBytes := hstack

/-- Everything a boot witness supplies. The trace is `script`, `log`, `regs`, `entrySteps`;
the rest is derived from it and checked by `Witness.Ok`. -/
structure Witness where
  script : Nat
  log : PackedLog
  runs : RunTree
  regs : Nat → BitVec 64
  entrySteps : Nat
  own : BootOwn
  top : Nat
  brkv : Nat
  chunks : List DlHeap.Chunk
  bins : List (List Nat)
  /-- The shared byte ranges as a search tree (the AST coverage predicate). -/
  sharedT : RangeTree
  stmts : Nat
  count : Nat
  prog : Program
  fuel : Nat := 100000
  cfuel : Nat := 1000

namespace Witness

variable (W : Witness)

def view : Nat → Option (BitVec 8) := bootView W.script W.runs

/-- The closed checks of a boot witness, one `decide +kernel` each. -/
structure Ok : Prop where
  log : LogOk W.log W.runs
  above : W.runs.above 0x8001acf0 = true
  memRef : memRefCheck W.view = true
  globals : readLEv W.view interpObject 8 = some W.own.env
  own : OwnOk W.own
  frame : FrameOk W.view W.own
  regs : BootRegs W.regs W.stmts W.count
  store : frameCheck (maskView prologueMask W.view) bootNatives W.own.env initFrame = true
  heapFacts : HeapFactsOk W.view W.own W.top W.brkv W.chunks
    (W.own.env, 0x28) (W.own.pn, 0x48) (W.own.pv, 0xc8)
  heap : heapCheck W.view W.own.exts [(W.own.pn, 8 * W.own.cap), (W.own.pv, 24 * W.own.cap)]
    W.top W.brkv W.chunks W.bins = true
  sharedT : W.sharedT.ranges.all (fun r => W.own.sharedRanges.contains r) = true
  prog : decodesTo W.view W.sharedT.mem W.fuel W.stmts W.count W.prog = true
  cap : capOk W.cfuel W.prog W.top = true
  fits : programStackFits W.prog = true

variable {W}

theorem Ok.shared (h : W.Ok) {k : Nat} (hk : W.sharedT.mem k = true) : W.own.shared k := by
  obtain ⟨r, hr, hin⟩ := RangeTree.mem_sound hk
  have := List.all_eq_true.mp h.sharedT r hr
  exact ⟨r, List.elem_iff.mp this, hin⟩

theorem Ok.memFacts (h : W.Ok) {m : Mem} (hv : PartialView m W.view)
    (hstack : ∀ k, stackSL.lo ≤ k → k < stackSL.hi → ∃ b : BitVec 8, m[k]? = some b) :
    BootMemFacts m W.own.env :=
  bootMemFacts_of_ref (hv.ref h.memRef) (hv.text (RunTree.above_mono h.above (by decide)))
    (hv.rodata h.above) (hv.readLE h.globals) hstack

theorem Ok.loadedEntry (h : W.Ok) {σ : Vsa.Machine.MState} (E : EntryRegs σ W.regs)
    (hout : Vsa.Machine.output σ = "") (hv : PartialView σ.mem W.view)
    (hstack : ∀ k, stackSL.lo ≤ k → k < stackSL.hi → ∃ b : BitVec 8, σ.mem[k]? = some b)
    {tick : Nat} (htick : tick < 2) (steps : Nat) :
    Vsa.Refine.Loaded interpRunLayout W.prog ⟨σ, tick, steps⟩ :=
  loaded_at hv E hout htick (h.memFacts hv hstack) h.regs h.own h.frame h.store h.heap
    h.heapFacts (fun _ hk => h.shared hk) h.prog h.cap h.fits

theorem Ok.loadedEntry_fill (h : W.Ok) {σ : Vsa.Machine.MState} (E : EntryRegs σ W.regs)
    (hout : Vsa.Machine.output σ = "") (hv : PartialView σ.mem W.view)
    {tick : Nat} (htick : tick < 2) (steps : Nat) :
    Vsa.Refine.Loaded interpRunLayout W.prog (Vsa.Densify.fillZero ⟨σ, tick, steps⟩) := by
  rw [fillZero_mk]
  exact h.loadedEntry (E.setMem (Vsa.Densify.fillZeroMem σ.mem)) hout hv.fill
    (fillZeroMem_stack _) htick steps

theorem Ok.loadedAt (h : W.Ok) {m : Mem} (hv : PartialView m W.view)
    (hstack : ∀ k, stackSL.lo ≤ k → k < stackSL.hi → ∃ b : BitVec 8, m[k]? = some b) :
    Vsa.Refine.Loaded interpRunLayout W.prog (bootConfig m W.regs W.entrySteps) :=
  h.loadedEntry (bootState_entryRegs m W.regs) rfl hv hstack (Nat.mod_lt _ (by decide))
    W.entrySteps

theorem Ok.view (h : W.Ok) : ViewOf (bootMem W.script W.log) W.view := bootMem_view h.log

theorem Ok.loaded (h : W.Ok) :
    Vsa.Refine.Loaded interpRunLayout W.prog
      (Vsa.Densify.fillZero (bootConfig (bootMem W.script W.log) W.regs W.entrySteps)) := by
  rw [fillZero_bootConfig]
  exact h.loadedAt h.view.partial.fill (fillZeroMem_stack _)

end Witness

end Vsa.Sim.Boot
