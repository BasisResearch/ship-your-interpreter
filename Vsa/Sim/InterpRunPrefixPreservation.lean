import Vsa.Sim.DriveToLoopHeadSpans
import Vsa.Sim.ReprSurvival
import Vsa.Sim.ExitRuntimeDataTransport

/-! Preservation across the concrete interpreter prologue and setjmp call. -/

namespace Vsa.Sim

open Vsa.Machine (Config)
open Vsa.MemRepr

/-- Any disjoint byte predicate survives the actual reached prefix carrier. -/
theorem ReadyPrefixFacts.agree_protected
    {inp : BitVec 64} {c0 c1 : Config}
    (F : ReadyPrefixFacts inp c0 c1) {P : Nat → Prop}
    (hP : ∀ k, P k → ¬ interpRunPrefixWriteFootprint inp k) :
    AgreeP P c0.σ.mem c1.σ.mem :=
  fun k hk => F.outside_prefix k (hP k hk)

/-- A protected read retains its Option value, including byte presence. -/
theorem ReadyPrefixFacts.read64_protected
    {inp : BitVec 64} {c0 c1 : Config}
    (F : ReadyPrefixFacts inp c0 c1) {a : Nat}
    (ha : ∀ k, k < 8 → ¬ interpRunPrefixWriteFootprint inp (a + k)) :
    read64 c0.σ.mem a = read64 c1.σ.mem a :=
  read64_agreeP (P := fun k => ¬ interpRunPrefixWriteFootprint inp k)
    F.outside_prefix ha

/-- The approved concrete entry places both write regions above static data. -/
theorem concreteInterpPrefix_low_disjoint {k : Nat} (hk : k < 0x87800000) :
    ¬ interpRunPrefixWriteFootprint (0x87fffe10#64) k := by
  change ¬ ((0x87fffc50 ≤ k ∧ k < 0x87fffd00) ∨
    (0x87fffe20 ≤ k ∧ k < 0x87fffe90))
  omega

/-- Main's saved s0/ra bytes are above both actual write regions. -/
theorem concreteInterpPrefix_main_disjoint {k : Nat}
    (hk : 0x87fffff0 ≤ k ∧ k < 0x88000000) :
    ¬ interpRunPrefixWriteFootprint (0x87fffe10#64) k := by
  change ¬ ((0x87fffc50 ≤ k ∧ k < 0x87fffd00) ∨
    (0x87fffe20 ≤ k ∧ k < 0x87fffe90))
  omega

/-- This covers all fixed text, rodata, and low runtime global bytes. -/
theorem ReadyPrefixFacts.fixed_image_runtime_bytes
    {c0 c1 : Config} (F : ReadyPrefixFacts (0x87fffe10#64) c0 c1) :
    AgreeP (fun k => k < 0x87800000) c0.σ.mem c1.σ.mem :=
  F.agree_protected (fun _ hk => concreteInterpPrefix_low_disjoint hk)

theorem ReadyPrefixFacts.main_saved_bytes
    {c0 c1 : Config} (F : ReadyPrefixFacts (0x87fffe10#64) c0 c1) :
    AgreeP (fun k => 0x87fffff0 ≤ k ∧ k < 0x88000000)
      c0.σ.mem c1.σ.mem :=
  F.agree_protected (fun _ hk => concreteInterpPrefix_main_disjoint hk)

/-- Transfer both exact initial saved values, with presence retained. -/
theorem ReadyPrefixFacts.main_saved_pair
    {c0 c1 : Config} (F : ReadyPrefixFacts (0x87fffe10#64) c0 c1) :
    read64 c0.σ.mem 0x87fffff0 = read64 c1.σ.mem 0x87fffff0 ∧
    read64 c0.σ.mem 0x87fffff8 = read64 c1.σ.mem 0x87fffff8 := by
  constructor
  · exact read64_agreeP F.main_saved_bytes (fun k hk => by constructor <;> omega)
  · exact read64_agreeP F.main_saved_bytes (fun k hk => by constructor <;> omega)

/-- Preserve the complete fixed text through the reached prologue. -/
theorem ReadyPrefixFacts.text_image
    {c0 c1 : Config} (F : ReadyPrefixFacts (0x87fffe10#64) c0 c1)
    (h : Code.FixedTextLoaded c0.σ.mem) : Code.FixedTextLoaded c1.σ.mem :=
  h.transport fun a _ hhi => (F.fixed_image_runtime_bytes a (by omega)).symm

/-- Preserve read-only dispatch tables as well as instruction bytes. -/
theorem ReadyPrefixFacts.rodata_image
    {c0 c1 : Config} (F : ReadyPrefixFacts (0x87fffe10#64) c0 c1)
    (h : Code.FixedRodataLoaded c0.σ.mem) : Code.FixedRodataLoaded c1.σ.mem :=
  h.transport fun a _ hhi => (F.fixed_image_runtime_bytes a (by omega)).symm

theorem ReadyPrefixFacts.main_return
    {c0 c1 : Config} (F : ReadyPrefixFacts (0x87fffe10#64) c0 c1)
    (h : read64 c0.σ.mem 0x87fffff8 = some 0x80000038) :
    read64 c1.σ.mem 0x87fffff8 = some 0x80000038 :=
  F.main_saved_pair.2.symm.trans h

/-- Preserve initialized close-path data through the actual entry prefix. -/
theorem ReadyPrefixFacts.exit_runtime
    {c0 c1 : Config} (F : ReadyPrefixFacts (0x87fffe10#64) c0 c1)
    (h : ExitRuntimeData c0.σ.mem) : ExitRuntimeData c1.σ.mem :=
  h.transport fun a ha =>
    F.fixed_image_runtime_bytes a (exitRuntimeExtraFoot_below_stack ha)

#print axioms ReadyPrefixFacts.agree_protected
#print axioms ReadyPrefixFacts.read64_protected
#print axioms ReadyPrefixFacts.fixed_image_runtime_bytes
#print axioms ReadyPrefixFacts.main_saved_pair
#print axioms ReadyPrefixFacts.text_image
#print axioms ReadyPrefixFacts.rodata_image
#print axioms ReadyPrefixFacts.main_return
#print axioms ReadyPrefixFacts.exit_runtime


/-- Every initially populated stack byte remains present after the actual prefix. -/
theorem ReadyPrefixFacts.stack_bytes
    {c0 c1 : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : Vsa.RuntimeRepr.NativeAddrs} {A : Vsa.RuntimeRepr.Arena}
    {phiF phiC : Vsa.While.Addr → Nat} {aLeft : Nat}
    (P : ReadyPrefixFacts inp c0 c1)
    (F : LayoutInstance.InterpRunReadyFacts c0 stmts count inp N A phiF phiC aLeft) :
    ∀ k, LayoutInstance.stackSL.lo ≤ k → k < LayoutInstance.stackSL.hi →
      ∃ b : BitVec 8, c1.σ.mem[k]? = some b := by
  intro k hlo hhi
  obtain ⟨b, hb⟩ := F.stack_bytes k hlo hhi
  exact P.mem_extends k b hb

#print axioms ReadyPrefixFacts.stack_bytes

end Vsa.Sim

namespace Vsa.Sim
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine

/-- The actual prefix preserves the interpreter's global-environment pointer. -/
theorem ReadyPrefixFacts.globals
    {before after : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {phiF phiC : Vsa.While.Addr → Nat} {aLeft : Nat}
    (P : ReadyPrefixFacts inp before after)
    (F : LayoutInstance.InterpRunReadyFacts before stmts count inp N A phiF phiC aLeft) :
    read64 after.σ.mem inp.toNat = some (phiF 0) := by
  have he := P.read64_protected (a := inp.toNat) (by
    intro k hk
    rw [F.interp_local]
    change ¬ ((0x87fffc50 ≤ 0x87fffe10 + k ∧ 0x87fffe10 + k < 0x87fffd00) ∨
      (0x87fffe20 ≤ 0x87fffe10 + k ∧ 0x87fffe10 + k < 0x87fffe90))
    omega)
  exact he.symm.trans F.globals

#print axioms ReadyPrefixFacts.globals

/-- The reached prefix retains the initialized interpreter depth word. -/
theorem ReadyPrefixFacts.call_depth
    {before after : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {phiF phiC : Vsa.While.Addr → Nat} {aLeft : Nat}
    (P : ReadyPrefixFacts inp before after)
    (F : LayoutInstance.InterpRunReadyFacts before stmts count inp N A phiF phiC aLeft) :
    read32 after.σ.mem (inp.toNat + 8) = some 0 := by
  have he := read32_agreeP (P := fun k => ¬ interpRunPrefixWriteFootprint inp k)
    P.outside_prefix (a := inp.toNat + 8) (by
      intro k hk
      rw [F.interp_local]
      change ¬ ((0x87fffc50 ≤ 0x87fffe10 + 8 + k ∧ 0x87fffe10 + 8 + k < 0x87fffd00) ∨
        (0x87fffe20 ≤ 0x87fffe10 + 8 + k ∧ 0x87fffe10 + 8 + k < 0x87fffe90))
      omega)
  exact he.symm.trans F.call_depth

#print axioms ReadyPrefixFacts.call_depth
end Vsa.Sim
