import Vsa.Sim.LoopSetupBData
import Vsa.Sim.InitialOwnershipPreservation

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine Vsa.While

namespace Vsa.Sim

/-- The array finish computed by setup-B does not wrap under the entry RAM bound. -/
theorem initialLoopFinish_toNat {stmts count : Nat}
    (hram : 0x80000000 ≤ stmts ∧ stmts + 8 * count ≤ 0x100000000) :
    (BitVec.ofNat 64 stmts + (BitVec.ofNat 64 count <<< 3)).toNat = stmts + 8 * count := by
  have hs : (BitVec.ofNat 64 stmts).toNat = stmts := Nat.mod_eq_of_lt (by omega)
  have hc : (BitVec.ofNat 64 count).toNat = count := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, hs, hc, Nat.shiftLeft_eq]
  change (stmts + count * 8 % 2^64) % 2^64 = stmts + 8 * count
  rw [Nat.mod_eq_of_lt (by omega : count * 8 < 2^64),
      Nat.mod_eq_of_lt (by omega : stmts + count * 8 < 2^64)]
  omega

/-- The reached machine cursor denotes exactly the original statement list. -/
theorem InitialLoopHeadFacts.cursor
    {c after : Config} {stmts count : Nat} {inp : BitVec 64} {p : Program}
    {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat} {aLeft : Nat}
    (H : InitialLoopHeadFacts inp stmts count c after)
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A phiF phiC aLeft)
    (hp : ProgramRepr c.σ.mem stmts count p) :
    ExecSeqCursorRepr .interpRun after.σ.mem phiF 0 p 0x87fffc50#64 0x87fffca8#64
      after.σ.regs.get? := by
  have hs : (BitVec.ofNat 64 stmts).toNat = stmts := Nat.mod_eq_of_lt (by have := F.stmts_ram; omega)
  have ast := (H.preservation.toReadyPrefixFacts.ast_owned F hp).erase
  refine ⟨BitVec.ofNat 64 stmts, BitVec.ofNat 64 stmts + (BitVec.ofNat 64 count <<< 3),
    H.cursor_reg, H.finish_reg, H.sp_reg, by decide, ?_, H.saved.script, ?_⟩
  · rw [initialLoopFinish_toNat F.stmts_ram, hs, hp.2]
  · rw [hs, ← hp.2]
    exact ast.1

/-- The saved interpreter pointer still names the represented global environment. -/
theorem InitialLoopHeadFacts.callABI
    {c after : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat} {aLeft : Nat}
    (H : InitialLoopHeadFacts inp stmts count c after)
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A phiF phiC aLeft) :
    ExecSeqCallABI .interpRun after.σ.mem after.σ.regs.get? phiF 0
      0x87fffc50#64 0x87fffca8#64 := by
  exact ⟨inp, H.saved.input, H.preservation.toReadyPrefixFacts.globals F, by decide⟩

/-- Actual initial loop head with one preserved ledger and the exact semantic cursor. -/
structure OwnedLoopHeadFacts (inp : BitVec 64) (stmts count : Nat)
    (before after : Config) (p : Program) (N : NativeAddrs) (A : Arena)
    (phiF phiC : Addr → Nat) (D : RuntimeOwnership.InitialOwnershipData) : Prop extends
    InitialLoopHeadFacts inp stmts count before after,
    ReadyRuntimeFacts after stmts count p N A phiF phiC D where
  cursor : ExecSeqCursorRepr .interpRun after.σ.mem phiF 0 p 0x87fffc50#64 0x87fffca8#64
    after.σ.regs.get?
  callABI : ExecSeqCallABI .interpRun after.σ.mem after.σ.regs.get? phiF 0
    0x87fffc50#64 0x87fffca8#64
  initial : RuntimeOwnership.InitialOwned before.σ.mem A LayoutInstance.stackSL
    phiF phiC stmts count D

/-- Every represented nonempty program reaches its owned machine loop head. -/
theorem readyLoopHead_owned
    {c : Config} {stmts count : Nat} {inp : BitVec 64} {p : Program}
    {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A phiF phiC aLeft)
    (hp : ProgramRepr c.σ.mem stmts count p) (hne : p ≠ []) :
    ∃ after D, OwnedLoopHeadFacts inp stmts count c after p N A phiF phiC D := by
  have hcount : 0 < count := by
    rw [hp.2]
    exact List.length_pos_iff.mpr hne
  obtain ⟨after, H⟩ := readyLoopHead_of_ready F hcount
  obtain ⟨D, O⟩ := F.ownership
  exact ⟨after, D, H, H.preservation.toReadyPrefixFacts.runtime_owned F hp O,
    H.cursor F hp, H.callABI F, O⟩

#print axioms initialLoopFinish_toNat
#print axioms InitialLoopHeadFacts.cursor
#print axioms InitialLoopHeadFacts.callABI
#print axioms readyLoopHead_owned
end Vsa.Sim
