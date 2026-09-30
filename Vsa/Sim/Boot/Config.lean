import Vsa.Sim.Boot.Image
import Vsa.Sim.OutputAliasPhysical

/-!
# The boot configuration at `interp_run`'s entry

The Sail state the emulator reaches at `interp_run`'s entry, from a boot
trace: the memory is `bootMem` (loader + store log), the general registers
are the entry row's (`g n` for `xn`), and the control registers are the
model's post-setup values (`OutputAliasPhysical.physicalAssignments`, the
same map the control witness uses; `Vsa/Sim/InitValues.lean`). The counters
(`minstret`, `mcycle`, `mtime`) are left at the setup value: `Loaded` does
not constrain them (`GoodState` asks only for presence). Nothing has been
printed before the entry (`OutRepr`, checked per trace by the generator).
-/

namespace Vsa.Sim.Boot

open LeanRV64DExecutable Sail ConcurrencyInterfaceV1
open Vsa.Machine Vsa.MemRepr Vsa.Sim.OutputAliasLoaded

/-- The control registers of `physicalAssignments` (every entry before `x1`). -/
def csrAssignments : List ((r : Register) × RegisterType r) := physicalAssignments.take 32

/-- `x1 … x31` from `g`. -/
def gprAssignments (g : Nat → BitVec 64) : List ((r : Register) × RegisterType r) :=
  (List.range 31).map fun i => ⟨gprReg (i + 1), gprRT (i + 1) (g (i + 1))⟩

def bootAssignments (g : Nat → BitVec 64) : List ((r : Register) × RegisterType r) :=
  csrAssignments ++ gprAssignments g

/-- The registers, keys only (independent of `g`). -/
def bootKeys : List Register :=
  csrAssignments.map Sigma.fst ++ (List.range 31).map fun i => gprReg (i + 1)

theorem bootAssignments_keys (g : Nat → BitVec 64) :
    (bootAssignments g).map Sigma.fst = bootKeys := by
  simp [bootAssignments, gprAssignments, bootKeys, Function.comp_def]

private theorem bootKeys_distinct : bootKeys.Pairwise (fun a b => (a == b) = false) := by
  decide

private theorem bootAssignments_distinct (g : Nat → BitVec 64) :
    (bootAssignments g).Pairwise (fun a b => (a.1 == b.1) = false) := by
  have h := bootKeys_distinct
  rw [← bootAssignments_keys g, List.pairwise_map] at h
  exact h

def bootRegs (g : Nat → BitVec 64) : Std.ExtDHashMap Register RegisterType :=
  Std.ExtDHashMap.ofList (bootAssignments g)

theorem bootRegs_get {g : Nat → BitVec 64} {r : Register} {v : RegisterType r}
    (h : ⟨r, v⟩ ∈ bootAssignments g) : (bootRegs g).get? r = some v := by
  simpa [bootRegs] using Std.ExtDHashMap.get?_ofList_of_mem
    (k := r) (k' := r) (by simp) (bootAssignments_distinct g) h

theorem bootRegs_csr {g : Nat → BitVec 64} {r : Register} {v : RegisterType r}
    (h : ⟨r, v⟩ ∈ csrAssignments) : (bootRegs g).get? r = some v :=
  bootRegs_get (List.mem_append_left _ h)

/-- A control register reads as in `physicalRegs`. -/
theorem bootRegs_eq_physical {g : Nat → BitVec 64} {r : Register} {v : RegisterType r}
    (h : ⟨r, v⟩ ∈ csrAssignments) : (bootRegs g).get? r = physicalRegs.get? r := by
  rw [bootRegs_csr h]
  have hm : ⟨r, v⟩ ∈ physicalAssignments := List.mem_of_mem_take h
  simpa [physicalRegs] using (Std.ExtDHashMap.get?_ofList_of_mem
    (k := r) (k' := r) (by simp) (by decide) hm).symm

/-- The Sail state at the entry. -/
def bootState (m : Mem) (g : Nat → BitVec 64) : MState :=
  ⟨bootRegs g, (), m, (), 0, #[]⟩

/-- The configuration at the entry after `steps` architectural steps; the
clock counter is `steps % plat_insns_per_tick` (`stepOnce`, two per tick). -/
def bootConfig (m : Mem) (g : Nat → BitVec 64) (steps : Nat) : Config :=
  ⟨bootState m g, steps % 2, steps⟩

@[simp] theorem bootConfig_mem (m : Mem) (g : Nat → BitVec 64) (steps : Nat) :
    (bootConfig m g steps).σ.mem = m := rfl

end Vsa.Sim.Boot

namespace Vsa.Sim.Boot

open LeanRV64DExecutable Sail ConcurrencyInterfaceV1
open Vsa.Machine Vsa.MemRepr Vsa.Sim.OutputAliasLoaded

/-- `x(i+1)` reads the trace's value. -/
theorem bootRegs_gpr (g : Nat → BitVec 64) (i : Nat) (hi : i < 31) :
    (bootRegs g).get? (gprReg (i + 1)) = some (gprRT (i + 1) (g (i + 1))) :=
  bootRegs_get (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))

local macro "csr" : tactic =>
  `(tactic| (apply bootRegs_csr; simp [csrAssignments, physicalAssignments]))

/-- A control register reads as in `physicalRegs`. -/
theorem bootRegs_eq_physical' {g : Nat → BitVec 64} {r : Register}
    (hr : r ∈ csrAssignments.map Sigma.fst) : (bootRegs g).get? r = physicalRegs.get? r := by
  obtain ⟨⟨r', v⟩, hm, rfl⟩ := List.mem_map.1 hr
  exact bootRegs_eq_physical hm

/-- `GoodState` names only control registers, which the boot map shares with
`physicalRegs`. -/
theorem bootState_good (m : Mem) (g : Nat → BitVec 64) : GoodState (bootState m g) := by
  have hr : ∀ r, r ∈ csrAssignments.map Sigma.fst →
      (bootState m g).regs.get? r = (physicalState m).regs.get? r :=
    fun _ h => bootRegs_eq_physical' h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _⟩ := physical_good m
  constructor <;> (rw [hr _ (by decide)]; assumption)

theorem bootState_pc (m : Mem) (g : Nat → BitVec 64) :
    (bootState m g).regs.get? Register.PC = some (0x800043ec#64) := by csr

theorem bootState_htif_payload (m : Mem) (g : Nat → BitVec 64) :
    (bootState m g).regs.get? Register.htif_payload_writes = some (0#4) := by csr

end Vsa.Sim.Boot
