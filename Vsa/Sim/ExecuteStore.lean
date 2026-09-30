import Vsa.Sim.MemStore
import Vsa.Sim.ExecuteAlu

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem get_transformed_data_addr_store
    (σ : SequentialState RegisterType trivialChoiceSource)
    (rs : regidx) (offset : BitVec 64) (v1 : BitVec 64) (width : Nat)
    (vmstatus : RegisterType Register.mstatus)
    (vmseccfg : RegisterType Register.mseccfg)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hseccfg : σ.regs.get? Register.mseccfg = some vmseccfg)
    (hpmm : _get_Seccfg_PMM vmseccfg = 0#2)
    (hrs : (rX_bits rs).run σ = .ok v1 σ) :
    (get_transformed_data_addr rs offset (MemoryAccessType.Store mem_payload.Data) width).run σ
      = .ok (Ext_DataAddr_Check.Ext_DataAddr_OK
          (virtaddr.Virtaddr (zero_extend (m := 64) (v1 + offset)))) σ := by
  have htf := transform_effective_address_store σ (v1 + offset) vmstatus vmseccfg
    hpriv hmstatus hmprv hseccfg hpmm
  simp only [EStateM.run] at hrs htf
  unfold get_transformed_data_addr ext_data_get_addr
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure]
  rw [hrs]
  simp only [EStateM.bind, EStateM.pure]
  rw [htf]

theorem vmem_write_store_char
    (σ : SequentialState RegisterType trivialChoiceSource)
    (rs1 : regidx) (offset : BitVec 64) (v1 : BitVec 64) (width : Nat)
    (data : BitVec (8 * width))
    (vmstatus : RegisterType Register.mstatus)
    (vmseccfg : RegisterType Register.mseccfg)
    (m' : SequentialState RegisterType trivialChoiceSource)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hseccfg : σ.regs.get? Register.mseccfg = some vmseccfg)
    (hpmm : _get_Seccfg_PMM vmseccfg = 0#2)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hwrite : (vmem_write_addr (virtaddr.Virtaddr (v1 + offset)) width data
        (MemoryAccessType.Store mem_payload.Data) false false false).run σ
      = .ok (.Ok true) m') :
    (vmem_write rs1 offset width data
        (MemoryAccessType.Store mem_payload.Data) false false false).run σ
      = .ok (.Ok true) m' := by
  have hgta := get_transformed_data_addr_store σ rs1 offset v1 width vmstatus vmseccfg
    hpriv hmstatus hmprv hseccfg hpmm hrs1
  have hze : (zero_extend (m := 64) (v1 + offset) : BitVec 64) = v1 + offset :=
    BitVec.setWidth_eq (v1 + offset)
  simp only [EStateM.run] at hgta hwrite ⊢
  unfold vmem_write
  simp only [LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, pure, EStateM.pure]
  rw [hgta]
  simp only [EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map, hze]
  rw [hwrite]
  simp only [EStateM.pure]

theorem execute_STORE_char
    (imm : BitVec 12) (rs2 rs1 : regidx) (width : Nat)
    (v1 vdata : BitVec 64)
    (σ : SequentialState RegisterType trivialChoiceSource)
    (vmstatus : RegisterType Register.mstatus)
    (vmseccfg : RegisterType Register.mseccfg)
    (m' : SequentialState RegisterType trivialChoiceSource)
    (hwle : width ≤ 8)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hseccfg : σ.regs.get? Register.mseccfg = some vmseccfg)
    (hpmm : _get_Seccfg_PMM vmseccfg = 0#2)
    (hrs2 : (rX_bits rs2).run σ = .ok vdata σ)
    (hrs1 : (rX_bits rs1).run σ = .ok v1 σ)
    (hwrite : (vmem_write_addr
        (virtaddr.Virtaddr (v1 + sign_extend (m := 64) imm)) width
        (Sail.BitVec.extractLsb vdata ((width *i 8) -i 1) 0)
        (MemoryAccessType.Store mem_payload.Data) false false false).run σ
      = .ok (.Ok true) m') :
    (execute_STORE imm rs2 rs1 width).run σ = .ok RETIRE_SUCCESS m' := by
  have hvw := vmem_write_store_char σ rs1 (sign_extend (m := 64) imm) v1 width
    (Sail.BitVec.extractLsb vdata ((width *i 8) -i 1) 0) vmstatus vmseccfg m'
    hpriv hmstatus hmprv hseccfg hpmm hrs1 hwrite
  have hassert : (width ≤b Functions.xlen_bytes) = true := by
    simp only [Functions.xlen_bytes, decide_eq_true_eq]
    omega
  simp only [EStateM.run] at hrs2 hvw ⊢
  unfold execute_STORE
  simp only [bind, EStateM.bind, pure, EStateM.pure,
    LeanRV64DExecutable.assert, PreSail.assert, hassert, if_true]
  rw [hrs2]
  simp only [EStateM.bind, EStateM.pure]
  rw [hvw]
  simp only [EStateM.pure]

end Vsa.Sim
