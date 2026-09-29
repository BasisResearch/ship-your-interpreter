import Vsa.Sim.LayoutInstance
import Vsa.Sim.Boot.Ast
import Vsa.AbsInt.CostSound
import Vsa.While.Programs

/-!
# The interpreter theorem with checked program premises

`Loaded interpRunLayout p c` carries two premises quantified over every
program the memory represents: the heap capacity
(`DlHeap.InitialAllocatorAt.capacity`: every normal cost derivation fits the
free heap) and stack admissibility (`StackAdmissible`). Both are discharged
here for one represented program `p`, using `ProgramRepr.unique`:

* capacity from the cost analysis, `interpCostBound p = some B`
  (`progCost_sound`), plus the numeric fact `HeapRoom m B` that the free
  heap above the top chunk holds `2 * B + extendSlack` bytes;
* stack admissibility from the existing checker `programStackFits p`.

`LoadedU` is `Loaded` without those two fields; `loaded_of_checked`
restores `Loaded` from it and the two checks. `endToEnd_checked`
(`VsaIris/Interp/EndToEndChecked.lean`) applies `endToEnd_refinement`.
-/

open Vsa Vsa.Alloc Vsa.Sim Vsa.While Vsa.AbsInt
open Vsa.RuntimeRepr
open Vsa.Machine (Config)

namespace Vsa.Sim.LayoutInstance

/-- The allocation-cost bound of the interpreter corollary. -/
def interpCostBound (p : Program) : CB := progCost (A := Const × Itv) {} p

/-- The free heap above the top chunk holds `2 * B + extendSlack` bytes. -/
def HeapRoom (m : Vsa.MemRepr.Mem) (B : Nat) : Prop :=
  ∀ t, Vsa.MemRepr.read64 m DlHeap.topAddr = some t →
    2 * B + DlHeap.extendSlack ≤ DlHeap.heapEnd - t

/-- The capacity field from a cost bound of the represented program. -/
theorem capacity_of_bound {m : Vsa.MemRepr.Mem} {stmts count top B : Nat} {p : Program}
    (hp : Vsa.MemRepr.ProgramRepr m stmts count p) (hB : interpCostBound p = some B)
    (hroom : 2 * B + DlHeap.extendSlack ≤ DlHeap.heapEnd - top) :
    ∀ p' : Program, Vsa.MemRepr.ProgramRepr m stmts count p' →
      ∀ st' n, ExecSeqCost initSt 0 0 p' st' .normal n →
        2 * n + DlHeap.extendSlack ≤ DlHeap.heapEnd - top := by
  intro p' hp' st' n hc
  obtain rfl := hp.unique hp'
  have hn := seqcost_sound (A := Const × Itv) {} hc [0] initState rfl initState_sound
    initSt_nodup
  unfold interpCostBound progCost at hB
  rw [hB] at hn
  simp only [CLe] at hn
  omega

/-- Stack admissibility from the checker, for the represented program. -/
theorem stackAdmissible_of_check {m : Vsa.MemRepr.Mem} {stmts count : Nat} {p : Program}
    (hp : Vsa.MemRepr.ProgramRepr m stmts count p) (h : programStackFits p = true) :
    StackAdmissible m stmts count := fun _ hp' => by
  obtain rfl := hp.unique hp'
  exact ProgramStackFits.of_check h

/-- `BootHeap` without the allocator's capacity field. -/
structure BootHeapU (m : Vsa.MemRepr.Mem) (A : Arena) (φf φc : Vsa.While.Addr → Nat)
    (stmts count : Nat) (D : RuntimeOwnership.InitialOwnershipData) (top brkv : Nat)
    (chunks : List DlHeap.Chunk) (bins : Nat → List Nat) (F : BootFrame) : Prop where
  owned : RuntimeOwnership.InitialOwned m A stackSL φf φc stmts count D
  heap : DlHeap.HeapAt m D.exts (RuntimeOwnership.ReallocExtent D.allocations) top brkv
    chunks bins
  facts : BootHeapFacts m D.shared (φf 0) top brkv chunks F

/-- `InterpRunReadyFacts` without `capacity` and `stack_admissible`. -/
structure InterpRunReadyFactsU
    (c : Config) (stmts count : Nat) (inp : BitVec 64)
    (N : NativeAddrs) (A : Arena) (φf φc : Vsa.While.Addr → Nat)
    (aLeft : Nat) : Prop extends
    InterpRunPhysicalFacts c stmts count inp N A φf φc aLeft where
  boot : ∃ (D : RuntimeOwnership.InitialOwnershipData) (top brkv : Nat)
    (chunks : List DlHeap.Chunk) (bins : Nat → List Nat) (F : BootFrame),
    BootHeapU c.σ.mem A φf φc stmts count D top brkv chunks bins F
  gprs : ∀ n, 1 ≤ n → n ≤ 31 → (gprGet c.σ n).isSome
  s0_impure : c.σ.regs.get? LeanRV64DExecutable.Register.x8 = some (0x8001b970#64 : BitVec 64)

/-- The boundary of `InterpRunReady` without the two program premises. -/
def InterpRunReadyU (c : Config) (stmts count : Nat) : Prop :=
  ∃ (inp : BitVec 64) (N : NativeAddrs) (A : Arena)
    (φf φc : Vsa.While.Addr → Nat) (aLeft : Nat),
    InterpRunReadyFactsU c stmts count inp N A φf φc aLeft

/-- `Loaded interpRunLayout` without the two program premises. -/
def LoadedU (p : Program) (c : Config) : Prop :=
  ∃ a n, Vsa.MemRepr.ProgramRepr c.σ.mem a n p ∧ InterpRunReadyU c a n

/-- The two checks and the heap room restore `Loaded`. -/
theorem loaded_of_checked {p : Program} {c : Config} {B : Nat} (hL : LoadedU p c)
    (hB : interpCostBound p = some B) (hs : programStackFits p = true)
    (hroom : HeapRoom c.σ.mem B) : Vsa.Refine.Loaded interpRunLayout p c := by
  obtain ⟨a, n, hp, inp, N, A, φf, φc, aLeft, F⟩ := hL
  obtain ⟨D, top, brkv, chunks, bins, Fr, hH⟩ := F.boot
  exact ⟨a, n, hp, inp, N, A, φf, φc, aLeft,
    { F.toInterpRunPhysicalFacts with
      boot := ⟨D, top, brkv, chunks, bins, Fr, hH.owned,
        ⟨hH.heap, capacity_of_bound hp hB (hroom _ hH.heap.top_ptr)⟩, hH.facts⟩
      stack_admissible := stackAdmissible_of_check hp hs
      gprs := F.gprs
      s0_impure := F.s0_impure }⟩

/-- `whileWl` passes both checks. -/
theorem whileWl_interp_checks :
    interpCostBound Programs.whileWl = some 8272 ∧
      programStackFits Programs.whileWl = true := by
  constructor <;> decide +kernel

#print axioms loaded_of_checked
#print axioms whileWl_interp_checks

end Vsa.Sim.LayoutInstance
