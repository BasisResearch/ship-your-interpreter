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

/-- Every general register is present. -/
theorem bootState_gprs (m : Mem) (g : Nat → BitVec 64) :
    ∀ n, 1 ≤ n → n ≤ 31 → (gprGet (bootState m g) n).isSome := by
  intro n h1 h31
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
  have hi : i < 31 := by omega
  exact match i, hi with
  | 0, _ => by
    show ((bootRegs g).get? Register.x1).isSome = true
    rw [show (bootRegs g).get? Register.x1 = some (g 1) from bootRegs_gpr g 0 (by decide)]
    rfl
  | 1, _ => by
    show ((bootRegs g).get? Register.x2).isSome = true
    rw [show (bootRegs g).get? Register.x2 = some (g 2) from bootRegs_gpr g 1 (by decide)]
    rfl
  | 2, _ => by
    show ((bootRegs g).get? Register.x3).isSome = true
    rw [show (bootRegs g).get? Register.x3 = some (g 3) from bootRegs_gpr g 2 (by decide)]
    rfl
  | 3, _ => by
    show ((bootRegs g).get? Register.x4).isSome = true
    rw [show (bootRegs g).get? Register.x4 = some (g 4) from bootRegs_gpr g 3 (by decide)]
    rfl
  | 4, _ => by
    show ((bootRegs g).get? Register.x5).isSome = true
    rw [show (bootRegs g).get? Register.x5 = some (g 5) from bootRegs_gpr g 4 (by decide)]
    rfl
  | 5, _ => by
    show ((bootRegs g).get? Register.x6).isSome = true
    rw [show (bootRegs g).get? Register.x6 = some (g 6) from bootRegs_gpr g 5 (by decide)]
    rfl
  | 6, _ => by
    show ((bootRegs g).get? Register.x7).isSome = true
    rw [show (bootRegs g).get? Register.x7 = some (g 7) from bootRegs_gpr g 6 (by decide)]
    rfl
  | 7, _ => by
    show ((bootRegs g).get? Register.x8).isSome = true
    rw [show (bootRegs g).get? Register.x8 = some (g 8) from bootRegs_gpr g 7 (by decide)]
    rfl
  | 8, _ => by
    show ((bootRegs g).get? Register.x9).isSome = true
    rw [show (bootRegs g).get? Register.x9 = some (g 9) from bootRegs_gpr g 8 (by decide)]
    rfl
  | 9, _ => by
    show ((bootRegs g).get? Register.x10).isSome = true
    rw [show (bootRegs g).get? Register.x10 = some (g 10) from bootRegs_gpr g 9 (by decide)]
    rfl
  | 10, _ => by
    show ((bootRegs g).get? Register.x11).isSome = true
    rw [show (bootRegs g).get? Register.x11 = some (g 11) from bootRegs_gpr g 10 (by decide)]
    rfl
  | 11, _ => by
    show ((bootRegs g).get? Register.x12).isSome = true
    rw [show (bootRegs g).get? Register.x12 = some (g 12) from bootRegs_gpr g 11 (by decide)]
    rfl
  | 12, _ => by
    show ((bootRegs g).get? Register.x13).isSome = true
    rw [show (bootRegs g).get? Register.x13 = some (g 13) from bootRegs_gpr g 12 (by decide)]
    rfl
  | 13, _ => by
    show ((bootRegs g).get? Register.x14).isSome = true
    rw [show (bootRegs g).get? Register.x14 = some (g 14) from bootRegs_gpr g 13 (by decide)]
    rfl
  | 14, _ => by
    show ((bootRegs g).get? Register.x15).isSome = true
    rw [show (bootRegs g).get? Register.x15 = some (g 15) from bootRegs_gpr g 14 (by decide)]
    rfl
  | 15, _ => by
    show ((bootRegs g).get? Register.x16).isSome = true
    rw [show (bootRegs g).get? Register.x16 = some (g 16) from bootRegs_gpr g 15 (by decide)]
    rfl
  | 16, _ => by
    show ((bootRegs g).get? Register.x17).isSome = true
    rw [show (bootRegs g).get? Register.x17 = some (g 17) from bootRegs_gpr g 16 (by decide)]
    rfl
  | 17, _ => by
    show ((bootRegs g).get? Register.x18).isSome = true
    rw [show (bootRegs g).get? Register.x18 = some (g 18) from bootRegs_gpr g 17 (by decide)]
    rfl
  | 18, _ => by
    show ((bootRegs g).get? Register.x19).isSome = true
    rw [show (bootRegs g).get? Register.x19 = some (g 19) from bootRegs_gpr g 18 (by decide)]
    rfl
  | 19, _ => by
    show ((bootRegs g).get? Register.x20).isSome = true
    rw [show (bootRegs g).get? Register.x20 = some (g 20) from bootRegs_gpr g 19 (by decide)]
    rfl
  | 20, _ => by
    show ((bootRegs g).get? Register.x21).isSome = true
    rw [show (bootRegs g).get? Register.x21 = some (g 21) from bootRegs_gpr g 20 (by decide)]
    rfl
  | 21, _ => by
    show ((bootRegs g).get? Register.x22).isSome = true
    rw [show (bootRegs g).get? Register.x22 = some (g 22) from bootRegs_gpr g 21 (by decide)]
    rfl
  | 22, _ => by
    show ((bootRegs g).get? Register.x23).isSome = true
    rw [show (bootRegs g).get? Register.x23 = some (g 23) from bootRegs_gpr g 22 (by decide)]
    rfl
  | 23, _ => by
    show ((bootRegs g).get? Register.x24).isSome = true
    rw [show (bootRegs g).get? Register.x24 = some (g 24) from bootRegs_gpr g 23 (by decide)]
    rfl
  | 24, _ => by
    show ((bootRegs g).get? Register.x25).isSome = true
    rw [show (bootRegs g).get? Register.x25 = some (g 25) from bootRegs_gpr g 24 (by decide)]
    rfl
  | 25, _ => by
    show ((bootRegs g).get? Register.x26).isSome = true
    rw [show (bootRegs g).get? Register.x26 = some (g 26) from bootRegs_gpr g 25 (by decide)]
    rfl
  | 26, _ => by
    show ((bootRegs g).get? Register.x27).isSome = true
    rw [show (bootRegs g).get? Register.x27 = some (g 27) from bootRegs_gpr g 26 (by decide)]
    rfl
  | 27, _ => by
    show ((bootRegs g).get? Register.x28).isSome = true
    rw [show (bootRegs g).get? Register.x28 = some (g 28) from bootRegs_gpr g 27 (by decide)]
    rfl
  | 28, _ => by
    show ((bootRegs g).get? Register.x29).isSome = true
    rw [show (bootRegs g).get? Register.x29 = some (g 29) from bootRegs_gpr g 28 (by decide)]
    rfl
  | 29, _ => by
    show ((bootRegs g).get? Register.x30).isSome = true
    rw [show (bootRegs g).get? Register.x30 = some (g 30) from bootRegs_gpr g 29 (by decide)]
    rfl
  | 30, _ => by
    show ((bootRegs g).get? Register.x31).isSome = true
    rw [show (bootRegs g).get? Register.x31 = some (g 31) from bootRegs_gpr g 30 (by decide)]
    rfl
  | _ + 31, h => absurd h (by omega)

end Vsa.Sim.Boot
