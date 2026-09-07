import Vsa.Sim.PageReadSplit
import Vsa.Sim.RamReadScalar

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
namespace Vsa.Sim

/-- Bare-mode reads ignore the successfully computed page split and permit misalignment. -/
theorem vmem_read_addr_of_pageSplit
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat) (parts : Int × Int) (paddr : physaddr) (v : BitVec (8 * w))
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hwpos : 0 < w)
    (hsplit : (split_on_page_boundary a w).run σ = .ok parts σ)
    (htrv : (translate_and_read_value (virtaddr.Virtaddr a) w
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (paddr, v)) σ) :
    (vmem_read_addr (virtaddr.Virtaddr a) w
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok v) σ := by
  have hmis : plat_misaligned_exception (MemoryAccessType.Load mem_payload.Data) false = none := rfl
  have hep := effectivePrivilege_data σ vmstatus Privilege.Machine hmprv
  have htm := translationMode_machine σ
  simp only [EStateM.run] at hsplit hep htm htrv
  unfold vmem_read_addr
  simp only [hmis, ite_self, LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, pure, EStateM.pure,
    bits_of_virtaddr, sys_misaligned_order_decreasing,
    Functions.not, Bool.false_and, if_false,
    Bool.false_eq_true]
  rw [hsplit]
  simp only [EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map,
    bind,
    pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [bne, EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map, htm,
    show (SATPMode.Bare == SATPMode.Bare) = true from by decide,
    Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, if_false,
    gt_iff_lt]
  rw [show (if false = true then parts.fst else (w : Int)) = (w : Int) from rfl]
  simp only [Int.toNat_natCast]
  rw [htrv]
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont,
    if_false]
  exact congrArg (fun x => EStateM.Result.ok (Result.Ok x) σ)
    (updateSubrange_zeros_load w hwpos v)


/-- Scalar checked reads lifted through the existing translation adapters. -/
theorem translate_and_read_value_ram_scalar {σ : Vsa.Machine.MState} (hg : GoodState σ)
    (a : BitVec 64) (k : Nat) (hk : k ≤ 3)
    (hlo : 0x80000000 ≤ a.toNat) (hhi : a.toNat + 2 ^ k ≤ 0x100000000)
    (hhtif : a.toNat + 2 ^ k ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat) :
    (translate_and_read_value (virtaddr.Virtaddr a) (2 ^ k)
      (MemoryAccessType.Load mem_payload.Data) false false false).run σ =
      .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a), bytesT σ.mem a.toNat (2 ^ k))) σ := by
  have hc := checked_mem_read_ram_scalar hg a k hk hlo hhi hhtif
  have hmprv : _get_Mstatus_MPRV initMstatus = 0#1 := by decide
  have he : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases he with rfl | rfl | rfl | rfl
  · exact translate_and_read_value_data_one_of_mr σ a _ initMstatus
      hg.cur_privilege hg.mstatus hmprv
      (mem_read_data_one_of_cmr σ a _ initMstatus hg.cur_privilege hg.mstatus hmprv hc)
  · exact translate_and_read_value_data_two_of_mr σ a _ initMstatus
      hg.cur_privilege hg.mstatus hmprv
      (mem_read_data_two_of_cmr σ a _ initMstatus hg.cur_privilege hg.mstatus hmprv hc)
  · exact translate_and_read_value_data_four_of_mr σ a _ initMstatus
      hg.cur_privilege hg.mstatus hmprv
      (mem_read_data_four_of_cmr σ a _ initMstatus hg.cur_privilege hg.mstatus hmprv hc)
  · exact translate_and_read_value_data_eight_of_mr σ a _ initMstatus
      hg.cur_privilege hg.mstatus hmprv
      (mem_read_data_eight_of_cmr σ a _ initMstatus hg.cur_privilege hg.mstatus hmprv hc)

/-- Virtual-address scalar loads, including page and granule crossings. -/
theorem vmem_read_addr_ram_scalar {σ : Vsa.Machine.MState} (hg : GoodState σ)
    (a : BitVec 64) (k : Nat) (hk : k ≤ 3)
    (hlo : 0x80000000 ≤ a.toNat) (hhi : a.toNat + 2 ^ k ≤ 0x100000000)
    (hhtif : a.toNat + 2 ^ k ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat) :
    (vmem_read_addr (virtaddr.Virtaddr a) (2 ^ k)
      (MemoryAccessType.Load mem_payload.Data) false false false).run σ =
      .ok (.Ok (bytesT σ.mem a.toNat (2 ^ k))) σ := by
  have hw : 2 ^ k ≤ 8 := Nat.le_trans (Nat.pow_le_pow_right (by decide) hk) (by decide)
  exact vmem_read_addr_of_pageSplit σ a (2 ^ k) (pageReadParts a (2 ^ k)) _ _
    initMstatus hg.cur_privilege hg.mstatus (by decide) (Nat.two_pow_pos _)
    (split_on_page_boundary_ram σ a (2 ^ k) (Nat.two_pow_pos _) hw (by omega))
    (translate_and_read_value_ram_scalar hg a k hk hlo hhi hhtif)

/-- Resolve the base register and offset, then perform the general scalar load. -/
theorem vmem_read_ram_scalar {σ : Vsa.Machine.MState} (hg : GoodState σ)
    (rs : regidx) (offset vbase : BitVec 64) (k : Nat) (hk : k ≤ 3)
    (hrs : (rX_bits rs).run σ = .ok vbase σ)
    (hlo : 0x80000000 ≤ (vbase + offset).toNat)
    (hhi : (vbase + offset).toNat + 2 ^ k ≤ 0x100000000)
    (hhtif : (vbase + offset).toNat + 2 ^ k ≤ tohostAddr ∨
      tohostAddr + 8 ≤ (vbase + offset).toNat) :
    (vmem_read rs offset (2 ^ k) (MemoryAccessType.Load mem_payload.Data)
      false false false).run σ = .ok (.Ok (bytesT σ.mem (vbase + offset).toNat (2 ^ k))) σ :=
  vmem_read_data_w σ rs offset vbase (2 ^ k) _ initMstatus hg.cur_privilege
    hg.mstatus (by decide) hg.mseccfg hrs
    (vmem_read_addr_ram_scalar hg (vbase + offset) k hk hlo hhi hhtif)

#print axioms translate_and_read_value_ram_scalar
#print axioms vmem_read_addr_ram_scalar
#print axioms vmem_read_ram_scalar

#print axioms vmem_read_addr_of_pageSplit
end Vsa.Sim
