import Vsa.Sim.MemLoad
import Vsa.Sim.ExecuteAlu

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem get_pmlen_data_machine
    (σ : SequentialState RegisterType trivialChoiceSource)
    (vmstatus : RegisterType Register.mstatus)
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmseccfg : σ.regs.get? Register.mseccfg = some (0#64 : RegisterType Register.mseccfg)) :
    (get_pmlen (MemoryAccessType.Load mem_payload.Data) Privilege.Machine).run σ
      = .ok 0 σ := by
  have h1 : (MemoryAccessType.Load mem_payload.Data ==
      (MemoryAccessType.InstructionFetch () : MemoryAccessType mem_payload)) = false := by decide
  have h2 : (MemoryAccessType.Load mem_payload.Data ==
      (MemoryAccessType.Load mem_payload.PageTableEntry : MemoryAccessType mem_payload)) = false := by decide
  have h3 : (MemoryAccessType.Load mem_payload.Data ==
      (MemoryAccessType.Store mem_payload.PageTableEntry : MemoryAccessType mem_payload)) = false := by decide
  have hpmm : pmm_mode_backwards (_get_Seccfg_PMM 0#64) = PointerMaskingMode.PMM_Disabled := rfl
  have hcond : ((Privilege.Machine == Privilege.Machine) || _get_Mstatus_MXR vmstatus == 0#1) = true := by
    rw [show (Privilege.Machine == Privilege.Machine) = true from by decide, Bool.true_or]
  have hxl : (Functions.xlen == 64) = true := by decide
  simp only [get_pmlen, is_pmm_applicable, get_pmm, bne, h1, h2, h3,
    Bool.not_false, Bool.true_and, Bool.and_true, hcond, hxl,
    bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hmseccfg, hpmm, if_true]

theorem transform_effective_address_data
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmseccfg : σ.regs.get? Register.mseccfg = some (0#64 : RegisterType Register.mseccfg)) :
    (transform_effective_address (virtaddr.Virtaddr a)
        (MemoryAccessType.Load mem_payload.Data)).run σ
      = .ok (virtaddr.Virtaddr a) σ := by
  have hep := effectivePrivilege_machine σ (MemoryAccessType.Load mem_payload.Data) vmstatus
    Privilege.Machine (by decide) hmprv
  have hpm := get_pmlen_data_machine σ vmstatus hmstatus hmseccfg
  simp only [EStateM.run] at hep hpm
  unfold transform_effective_address
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [EStateM.bind]
  rw [hpm]
  simp only [translationMode, bind, EStateM.bind, EStateM.pure, pure]
  have hb : (Privilege.Machine == Privilege.Machine) = true := by decide
  simp only [hb, if_true]
  have hbb : (SATPMode.Bare == SATPMode.Bare) = true := by decide
  simp only [hbb, if_true, pm_transform_PA, EStateM.pure]
  have haeq : ∀ (n : Nat), n = 63 →
      (zero_extend (m := 64) (Sail.BitVec.extractLsb a n 0) : BitVec 64) = a := by
    rintro n rfl
    apply BitVec.eq_of_toNat_eq
    have hlt : a.toNat < 2 ^ 64 := a.isLt
    simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth,
      Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
      Nat.shiftRight_zero, BitVec.toNat_ofNat]
    omega
  rw [haeq _ (by decide)]

theorem get_transformed_data_addr_data
    (σ : SequentialState RegisterType trivialChoiceSource)
    (rs : regidx) (offset : BitVec 64) (v1 : BitVec 64) (width : Nat)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmseccfg : σ.regs.get? Register.mseccfg = some (0#64 : RegisterType Register.mseccfg))
    (hrs : (rX_bits rs).run σ = .ok v1 σ) :
    (get_transformed_data_addr rs offset (MemoryAccessType.Load mem_payload.Data) width).run σ
      = .ok (Ext_DataAddr_Check.Ext_DataAddr_OK (virtaddr.Virtaddr (v1 + offset))) σ := by
  have htf := transform_effective_address_data σ (v1 + offset) vmstatus hpriv hmstatus hmprv hmseccfg
  simp only [EStateM.run] at hrs htf
  unfold get_transformed_data_addr ext_data_get_addr
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure]
  rw [hrs]
  simp only [EStateM.bind, EStateM.pure]
  rw [htf]

theorem and_page_mask_toNat (a : BitVec 64) :
    (a &&& 0xFFFFFFFFFFFFF000#64).toNat = a.toNat / 4096 * 4096 := by
  have hmeq : (0xFFFFFFFFFFFFF000#64 : BitVec 64) = (BitVec.allOnes 64) <<< 12 := by decide
  have hshift : (a &&& 0xFFFFFFFFFFFFF000#64) = (a >>> 12) <<< 12 := by
    rw [hmeq]
    apply BitVec.eq_of_getLsbD_eq
    intro i
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_allOnes]
    by_cases hi : i < 12
    · simp only [hi, decide_true, Bool.not_true, Bool.false_and, Bool.and_false, Bool.and_true,
        Bool.and_self, implies_true]
    · by_cases hlt : i < 64
      · have h3 : 12 + (i - 12) = i := by omega
        have h2 : i - 12 < 64 := by omega
        simp only [hi, decide_false, Bool.not_false, Bool.true_and, hlt, decide_true,
          h2, Bool.and_true, h3, Bool.and_self, implies_true]
      · have hge : a.getLsbD i = false := BitVec.getLsbD_of_ge a i (by omega)
        simp only [hi, decide_false, Bool.not_false, Bool.true_and, hlt,
          Bool.false_and, Bool.and_false, hge, Bool.and_self, implies_true]
  rw [hshift, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
  have ha : a.toNat < 2 ^ 64 := a.isLt
  rw [Nat.shiftRight_eq_div_pow]
  have hb : a.toNat / 4096 < 2 ^ 52 := by omega
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]

theorem split_on_page_boundary_data_w
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) (w : Nat)
    (hwpos : 0 < w) (hwle : w ≤ 8)
    (hpage : (a.toNat + (w - 1)) / 4096 = a.toNat / 4096) :
    (split_on_page_boundary a w).run σ = .ok ((w : Int), 0) σ := by
  have hmask : (Sail.BitVec.updateSubrange ((ones (n := 64)) : BitVec 64)
      (Functions.pagesize_bits -i 1) 0 (zeros (n := ((12 -i 1) -i (0 -i 1))))) = 0xFFFFFFFFFFFFF000#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  simp only [split_on_page_boundary, Sail.BitVec.length, hmask]
  have hai : BitVec.addInt a ((w : Nat) : Int) = a + BitVec.ofNat 64 w := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.addInt]; rfl
  have hsi : BitVec.subInt (a + BitVec.ofNat 64 w) 1 = a + BitVec.ofNat 64 (w - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.subInt, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_sub]
    have h64 : a.toNat < 2 ^ 64 := a.isLt
    have : (BitVec.ofInt 64 1).toNat = 1 := by decide
    omega
  have hintra : ((a &&& 0xFFFFFFFFFFFFF000#64)
      == (BitVec.subInt (BitVec.addInt a ((w : Nat) : Int)) 1 &&& 0xFFFFFFFFFFFFF000#64)) = true := by
    rw [hai, hsi]
    simp only [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [and_page_mask_toNat, and_page_mask_toNat]
    have h64 : a.toNat < 2 ^ 64 := a.isLt
    have haw : (a + BitVec.ofNat 64 (w - 1)).toNat = a.toNat + (w - 1) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [haw, hpage]
  simp only [hintra, if_true, bind, EStateM.bind, EStateM.run, pure, EStateM.pure]

theorem updateSubrange_zeros_load (w : Nat) (hw : 0 < w) (v : BitVec (8 * w)) :
    Sail.BitVec.updateSubrange (zeros (n := (8 * (↑w : Int)).toNat))
        ((8 * (↑w : Int) - 1).toNat) 0 v = v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.updateSubrange, Sail.BitVec.updateSubrange', Functions.zeros,
    BitVec.shiftLeft_zero, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_not,
    BitVec.toNat_setWidth, BitVec.toNat_allOnes]
  have hN : (8 * (↑w : Int)).toNat = 8 * w := by omega
  have hM : (8 * (↑w : Int) - 1).toNat - 0 + 1 = 8 * w := by omega
  simp only [hN, hM, BitVec.zero_eq, BitVec.toNat_ofNat, Nat.zero_mod]
  have hvlt : v.toNat < 2 ^ (8 * w) := BitVec.isLt _
  rw [Nat.and_zero, Nat.zero_or, Nat.mod_mod, Nat.mod_eq_of_lt hvlt]

theorem vmem_read_addr_data_w
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat) (paddr : physaddr) (v : BitVec (8 * w))
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hwpos : 0 < w) (hwle : w ≤ 8)
    (hpage : (a.toNat + (w - 1)) / 4096 = a.toNat / 4096)
    (halignv : is_aligned_vaddr (virtaddr.Virtaddr a) w = true)
    (htrv : (translate_and_read_value (virtaddr.Virtaddr a) w
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (paddr, v)) σ) :
    (vmem_read_addr (virtaddr.Virtaddr a) w
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok v) σ := by
  have hsplit := split_on_page_boundary_data_w σ a w hwpos hwle hpage
  have hep := effectivePrivilege_machine σ (MemoryAccessType.Load mem_payload.Data) vmstatus
    Privilege.Machine (by decide) hmprv
  have htm := translationMode_machine σ
  simp only [EStateM.run] at hsplit hep htm htrv
  unfold vmem_read_addr
  simp only [halignv, LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, pure, EStateM.pure,
    bits_of_virtaddr, sys_misaligned_order_decreasing,
    Functions.not, Bool.not_true, Bool.false_and, Bool.and_false, if_false, if_true,
    Bool.false_eq_true]
  rw [hsplit]
  simp only [EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map,
    bind, ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.pure, liftM, monadLift,
    MonadLift.monadLift, Functor.map, pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [bne, EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map, htm,
    show (SATPMode.Bare == SATPMode.Bare) = true from by decide,
    Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, if_false,
    gt_iff_lt, sys_misaligned_order_decreasing]
  rw [show (if (Bool.false = Bool.true) then ((w:Nat):Int) else ((w:Nat):Int)) = ((w:Nat):Int) from rfl]
  simp only [Int.toNat_natCast]
  rw [htrv]
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont, EStateM.map,
    Bool.false_eq_true, if_false]
  exact congrArg (fun x => EStateM.Result.ok (Result.Ok x) σ)
    (updateSubrange_zeros_load w hwpos v)

theorem is_aligned_vaddr_of_mod (a : BitVec 64) (w : Nat)
    (halign : a.toNat % w = 0) : is_aligned_vaddr (virtaddr.Virtaddr a) w = true := by
  have htmod : Int.tmod (BitVec.toNatInt a) ((w : Nat) : Int) = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat w)) = Int.ofNat (a.toNat % w) :=
      (Int.ofNat_tmod _ _).symm
    rw [show ((w : Nat) : Int) = Int.ofNat w from rfl, this, halign]; rfl
  simp only [is_aligned_vaddr, beq_iff_eq]
  exact htmod

theorem vmem_read_addr_data_ram_w
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat) (v : BitVec (8 * w))
    (vmstatus : RegisterType Register.mstatus)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hwpos : 0 < w) (hwle : w ≤ 8)
    (hlo : 0x80000000 ≤ a.toNat)
    (hhiram : a.toNat + w ≤ 0x100000000)
    (hhtif : a.toNat + w ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (halign : a.toNat % w = 0)
    (hpage : (a.toNat + (w - 1)) / 4096 = a.toNat / 4096)
    (hram : (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) w false).run σ
      = .ok (v, ()) σ) :
    (vmem_read_addr (virtaddr.Virtaddr a) w
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok v) σ :=
  vmem_read_addr_data_w σ a w (physaddr.Physaddr (zero_extend (m := 64) a)) v
    vmstatus hpriv hmstatus hmprv hwpos hwle hpage (is_aligned_vaddr_of_mod a w halign)
    (translate_and_read_value_data_w_of_mr σ a w v vmstatus hpriv hmstatus hmprv
      (mem_read_data_w_of_cmr σ a w v vmstatus hpriv hmstatus hmprv
        (checked_mem_read_data_w_of_ram σ a w v vpmpaddr hwpos hwle hpma hcfg haddr hbase
          hlo hhiram hhtif halign hram)))

theorem vmem_read_addr_data_eight
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (vmstatus : RegisterType Register.mstatus)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat)
    (hhiram : a.toNat + 8 ≤ 0x100000000)
    (hhtif : a.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (halign : a.toNat % 8 = 0)
    (h0 : σ.mem[a.toNat]? = some b0) (h1 : σ.mem[a.toNat + 1]? = some b1)
    (h2 : σ.mem[a.toNat + 2]? = some b2) (h3 : σ.mem[a.toNat + 3]? = some b3)
    (h4 : σ.mem[a.toNat + 4]? = some b4) (h5 : σ.mem[a.toNat + 5]? = some b5)
    (h6 : σ.mem[a.toNat + 6]? = some b6) (h7 : σ.mem[a.toNat + 7]? = some b7) :
    (vmem_read_addr (virtaddr.Virtaddr a) 8
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (((((((b7.append b6).append b5).append b4).append b3).append
          b2).append b1).append b0)) σ :=
  vmem_read_addr_data_ram_w σ a 8 _ vmstatus vpmpaddr hpriv hmstatus hmprv hpma hcfg haddr hbase
    (by decide) (by decide) hlo hhiram hhtif halign (by omega)
    (read_ram_eight σ a b0 b1 b2 b3 b4 b5 b6 b7 h0 h1 h2 h3 h4 h5 h6 h7)

theorem vmem_read_data_w
    (σ : SequentialState RegisterType trivialChoiceSource)
    (rs : regidx) (offset v1 : BitVec 64) (width : Nat) (r : Result (BitVec (8 * width)) ExecutionResult)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmseccfg : σ.regs.get? Register.mseccfg = some (0#64 : RegisterType Register.mseccfg))
    (hrs : (rX_bits rs).run σ = .ok v1 σ)
    (hvra : (vmem_read_addr (virtaddr.Virtaddr (v1 + offset)) width
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ = .ok r σ) :
    (vmem_read rs offset width (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok r σ := by
  have hgta := get_transformed_data_addr_data σ rs offset v1 width vmstatus
    hpriv hmstatus hmprv hmseccfg hrs
  simp only [EStateM.run] at hgta hvra
  unfold vmem_read
  simp only [LeanRV64DExecutable.SailME.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, pure, EStateM.pure]
  rw [hgta]
  simp only [EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map, Functor.map]
  rw [hvra]
  simp only [EStateM.pure]

theorem vmem_read_data_ram_w
    (σ : SequentialState RegisterType trivialChoiceSource)
    (rs : regidx) (offset v1 : BitVec 64) (w : Nat) (v : BitVec (8 * w))
    (vmstatus : RegisterType Register.mstatus) (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmseccfg : σ.regs.get? Register.mseccfg = some (0#64 : RegisterType Register.mseccfg))
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hrs : (rX_bits rs).run σ = .ok v1 σ)
    (hwpos : 0 < w) (hwle : w ≤ 8)
    (hlo : 0x80000000 ≤ (v1 + offset).toNat) (hhiram : (v1 + offset).toNat + w ≤ 0x100000000)
    (hhtif : (v1 + offset).toNat + w ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v1 + offset).toNat)
    (halign : (v1 + offset).toNat % w = 0)
    (hpage : ((v1 + offset).toNat + (w - 1)) / 4096 = (v1 + offset).toNat / 4096)
    (hram : (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr (v1 + offset)) w false).run σ
      = .ok (v, ()) σ) :
    (vmem_read rs offset w (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok v) σ :=
  vmem_read_data_w σ rs offset v1 w _ vmstatus hpriv hmstatus hmprv hmseccfg hrs
    (vmem_read_addr_data_ram_w σ (v1 + offset) w v vmstatus vpmpaddr hpriv hmstatus hmprv
      hpma hcfg haddr hbase hwpos hwle hlo hhiram hhtif halign hpage hram)

theorem vmem_read_data_eight
    (σ : SequentialState RegisterType trivialChoiceSource)
    (rs : regidx) (offset v1 : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (vmstatus : RegisterType Register.mstatus) (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmseccfg : σ.regs.get? Register.mseccfg = some (0#64 : RegisterType Register.mseccfg))
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hrs : (rX_bits rs).run σ = .ok v1 σ)
    (hlo : 0x80000000 ≤ (v1 + offset).toNat) (hhiram : (v1 + offset).toNat + 8 ≤ 0x100000000)
    (hhtif : (v1 + offset).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v1 + offset).toNat)
    (halign : (v1 + offset).toNat % 8 = 0)
    (h0 : σ.mem[(v1 + offset).toNat]? = some b0) (h1 : σ.mem[(v1 + offset).toNat + 1]? = some b1)
    (h2 : σ.mem[(v1 + offset).toNat + 2]? = some b2) (h3 : σ.mem[(v1 + offset).toNat + 3]? = some b3)
    (h4 : σ.mem[(v1 + offset).toNat + 4]? = some b4) (h5 : σ.mem[(v1 + offset).toNat + 5]? = some b5)
    (h6 : σ.mem[(v1 + offset).toNat + 6]? = some b6) (h7 : σ.mem[(v1 + offset).toNat + 7]? = some b7) :
    (vmem_read rs offset 8 (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (((((((b7.append b6).append b5).append b4).append b3).append
          b2).append b1).append b0)) σ :=
  vmem_read_data_w σ rs offset v1 8 _ vmstatus hpriv hmstatus hmprv hmseccfg hrs
    (vmem_read_addr_data_eight σ (v1 + offset) b0 b1 b2 b3 b4 b5 b6 b7 vmstatus vpmpaddr
      hpriv hmstatus hmprv hpma hcfg haddr hbase hlo hhiram hhtif halign
      h0 h1 h2 h3 h4 h5 h6 h7)

theorem execute_load_char (imm : BitVec 12) (rs1 rd : regidx) (is_unsigned : Bool)
    (width : Nat) (data : BitVec (8 * width))
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hwidth : (width ≤b Functions.xlen_bytes) = true)
    (hread : (vmem_read rs1 (sign_extend (m := 64) imm) width
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok data) σ)
    (hwr : (wX_bits rd (extend_value is_unsigned data)).run σ = .ok () σ') :
    (execute (instruction.LOAD (imm, rs1, rd, is_unsigned, width))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hread hwr ⊢
  rw [show (execute (instruction.LOAD (imm, rs1, rd, is_unsigned, width)))
      = execute_LOAD imm rs1 rd is_unsigned width from rfl]
  unfold execute_LOAD
  simp only [LeanRV64DExecutable.assert, PreSail.assert,
    hwidth, if_true, bind, EStateM.bind, pure, EStateM.pure, hread, hwr]

theorem execute_load_signed_char (imm : BitVec 12) (rs1 rd : regidx)
    (width : Nat) (data : BitVec (8 * width))
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hwidth : (width ≤b Functions.xlen_bytes) = true)
    (hread : (vmem_read rs1 (sign_extend (m := 64) imm) width
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok data) σ)
    (hwr : (wX_bits rd (sign_extend (m := 64) data)).run σ = .ok () σ') :
    (execute (instruction.LOAD (imm, rs1, rd, false, width))).run σ
      = .ok RETIRE_SUCCESS σ' :=
  execute_load_char imm rs1 rd false width data σ σ' hwidth hread
    (by simpa only [extend_value, Bool.false_eq_true, if_false] using hwr)

theorem execute_load_unsigned_char (imm : BitVec 12) (rs1 rd : regidx)
    (width : Nat) (data : BitVec (8 * width))
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hwidth : (width ≤b Functions.xlen_bytes) = true)
    (hread : (vmem_read rs1 (sign_extend (m := 64) imm) width
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok data) σ)
    (hwr : (wX_bits rd (zero_extend (m := 64) data)).run σ = .ok () σ') :
    (execute (instruction.LOAD (imm, rs1, rd, true, width))).run σ
      = .ok RETIRE_SUCCESS σ' :=
  execute_load_char imm rs1 rd true width data σ σ' hwidth hread
    (by simpa only [extend_value, if_true] using hwr)

end Vsa.Sim
