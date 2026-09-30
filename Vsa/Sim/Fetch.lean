import Vsa.Sim.Hooks
import Vsa.Sim.Pmp
import Vsa.Sim.StateNF

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem ofInt_zero_gen (n : Nat) : (BitVec.ofInt n 0) = 0#n := by
  apply BitVec.eq_of_toNat_eq; simp

theorem addInt_zero_pa (a : physaddrbits) : BitVec.addInt a (0 : Int) = a := by
  simp only [BitVec.addInt, ofInt_zero_gen, BitVec.add_zero]

theorem read_ram_four
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (h0 : σ.mem[a.toNat]? = some b0) (h1 : σ.mem[a.toNat + 1]? = some b1)
    (h2 : σ.mem[a.toNat + 2]? = some b2) (h3 : σ.mem[a.toNat + 3]? = some b3) :
    (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) 4 false).run σ
      = .ok ((((b3.append b2).append b1).append b0), ()) σ := by
  have e2 : a.toNat + 1 + 1 = a.toNat + 2 := by omega
  have e3 : a.toNat + 1 + 1 + 1 = a.toNat + 3 := by omega
  simp only [Functions.read_ram, PreSail.sail_mem_read, PreSail.readBytes,
    PreSail.readByte, default_meta]
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get, Bool.false_eq_true,
    e2, e3, h0, h1, h2, h3]

theorem checked_mem_read_four
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat)
    (hhi : a.toNat + 4 ≤ tohostAddr)
    (halign : a.toNat % 4 = 0)
    (h0 : σ.mem[a.toNat]? = some b0) (h1 : σ.mem[a.toNat + 1]? = some b1)
    (h2 : σ.mem[a.toNat + 2]? = some b2) (h3 : σ.mem[a.toNat + 3]? = some b3) :
    (checked_mem_read (MemoryAccessType.InstructionFetch ())
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        4 false false false false).run σ
      = .ok (.Ok ((((b3.append b2).append b1).append b0), ())) σ := by
  have htmod : Int.tmod (BitVec.toNatInt a) 4 = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat 4)) = Int.ofNat (a.toNat % 4) :=
      (Int.ofNat_tmod _ _).symm
    rw [show (4 : Int) = Int.ofNat 4 from rfl, this, halign]; rfl
  have hhi' : a.toNat + 4 ≤ 0x100000000 := by
    simp only [tohostAddr] at hhi; omega
  have hpmaC := pmaCheck_ram_exec σ a hpma hlo hhi' htmod
  have hpmp := pmp_allows σ (physaddr.Physaddr a) 4
    (MemoryAccessType.InstructionFetch ()) vpmpaddr hcfg haddr
  have hmmio := within_mmio_readable_ram_false σ a hbase hlo hhi
  have hsplit := split_misaligned_aligned σ a 0 Splittability.CannotSplit htmod
  have hram := read_ram_four σ a b0 b1 b2 b3 h0 h1 h2 h3
  simp only [EStateM.run] at hpmaC hpmp hmmio hsplit hram
  unfold checked_mem_read
  simp only [check_pma_with_pmp_priority, read_kind_of_flags, misaligned_order,
    sys_misaligned_order_decreasing, bits_of_physaddr,
    LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, pure]
  rw [hpmaC]
  simp only [EStateM.pure, ExceptT.bindCont, EStateM.map, EStateM.bind]
  rw [hsplit]
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont, EStateM.map]

  simp only [Int.reduceNeg, Bool.false_eq_true, if_false,
    show ((1 : Int) - 1) = 0 from by decide,
    show Int.toNat 1 = 1 from rfl, show Int.toNat 4 = 4 from rfl,
    show Int.toNat 0 = 0 from rfl]
  rw [untilFuelM]
  simp only [untilFuelM.go]

  simp only [ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure,
    EStateM.map, EStateM.bind, EStateM.pure, bind, pure, Pure.pure,
    LeanRV64DExecutable.assert, PreSail.assert, if_true,
    show (↑(0 : Nat) * (4 : Int)) = (0 : Int) from by decide, addInt_zero_pa,
    hpmp, hmmio, Bool.false_eq_true, if_false]
  have hram' : Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) (Int.toNat 4) false σ
      = EStateM.Result.ok (((b3.append b2).append b1).append b0, ()) σ := hram
  rw [hram']
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont,
    beq_self_eq_true, if_true, default_meta]

  have e1 : (8 * (((0:Nat):Int) + 1) * 4 - 1 : Int).toNat = 31 := by decide
  have e2 : (8 * ((0:Nat):Int) * 4 : Int).toNat = 0 := by decide
  rw [e1, e2]
  congr 3

  simp only [BitVec.updateSubrange, Sail.BitVec.updateSubrange', Functions.zeros]
  have key : (0#32 ||| (b3 +++ b2 +++ b1 +++ b0) <<< 0) = b3 +++ b2 +++ b1 +++ b0 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.shiftLeft_zero]
  exact key

theorem mem_read_four
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (vmstatus : RegisterType Register.mstatus)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat)
    (hhi : a.toNat + 4 ≤ tohostAddr)
    (halign : a.toNat % 4 = 0)
    (h0 : σ.mem[a.toNat]? = some b0) (h1 : σ.mem[a.toNat + 1]? = some b1)
    (h2 : σ.mem[a.toNat + 2]? = some b2) (h3 : σ.mem[a.toNat + 3]? = some b3) :
    (mem_read (MemoryAccessType.InstructionFetch ())
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 4 false false false).run σ
      = .ok (.Ok (((b3.append b2).append b1).append b0)) σ := by
  have hcmr := checked_mem_read_four σ a b0 b1 b2 b3 vpmpaddr hpma hcfg haddr hbase
    hlo hhi halign h0 h1 h2 h3
  have hep := effectivePrivilege_fetch σ vmstatus Privilege.Machine
  simp only [EStateM.run] at hcmr hep
  unfold mem_read mem_read_priv mem_read_priv_meta
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [MemoryOpResult_drop_meta]
  rw [hcmr]

theorem fetch_bytes_four
    (σ : SequentialState RegisterType trivialChoiceSource)
    (pc : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (vmstatus : RegisterType Register.mstatus)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ pc.toNat)
    (hhi : pc.toNat + 4 ≤ tohostAddr)
    (halign : pc.toNat % 4 = 0)
    (h0 : σ.mem[pc.toNat]? = some b0) (h1 : σ.mem[pc.toNat + 1]? = some b1)
    (h2 : σ.mem[pc.toNat + 2]? = some b2) (h3 : σ.mem[pc.toNat + 3]? = some b3) :
    (fetch_bytes pc pc 4).run σ
      = .ok (FetchBytes_Result.FetchBytes_Success
          (((b3.append b2).append b1).append b0)) σ := by
  have htr := translateAddr_machine_fetch σ pc vmstatus hpriv hmstatus
  have hmr := mem_read_four σ pc b0 b1 b2 b3 vmstatus vpmpaddr hpriv hmstatus hpma
    hcfg haddr hbase hlo hhi halign h0 h1 h2 h3
  simp only [EStateM.run] at htr hmr

  have hze : (zero_extend (m := 64) pc : BitVec 64) = pc := BitVec.setWidth_eq pc
  unfold fetch_bytes
  simp only [ext_fetch_check_pc,
    LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, EStateM.pure, pure]
  rw [htr]
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont, EStateM.map, hze]
  rw [hmr]
  simp only [EStateM.pure, BitVec.setWidth_eq]

theorem currentlyEnabled_Zca
    (σ : SequentialState RegisterType trivialChoiceSource)
    (vmisa : RegisterType Register.misa)
    (hmisa : σ.regs.get? Register.misa = some vmisa) :
    (currentlyEnabled extension.Ext_Zca).run σ
      = .ok (_get_Misa_C vmisa == 1#1) σ := by
  simp only [currentlyEnabled, hartSupports]
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmisa, simp_sail]
  congr 1
  simp only [Functions.xlen, Functions.not]
  generalize (_get_Misa_C vmisa == 1#1) = b
  cases b <;> rfl

theorem isRVC_false (b0 b1 b2 b3 : BitVec 8)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = 0b11#2) :
    isRVC (Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 15 0) = false := by
  have hextr : Sail.BitVec.extractLsb
      (Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 15 0) 1 0
      = Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 := by
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb', Nat.shiftRight_zero, BitVec.toNat_ofNat]
    omega
  simp only [isRVC, hextr, hnotrvc, beq_self_eq_true, Functions.not, Bool.not_true]

theorem access_bit0 (pc : BitVec 64) (halign : pc.toNat % 4 = 0) :
    Sail.BitVec.access pc 0 = 0#1 := by
  simp only [Sail.BitVec.access]
  have h : pc[0]! = false := by
    rw [getElem!_pos pc 0 (by omega), BitVec.getElem_eq_testBit_toNat, Nat.testBit_zero,
      decide_eq_false_iff_not]
    omega
  rw [h]; rfl

theorem access_bit1 (pc : BitVec 64) (halign : pc.toNat % 4 = 0) :
    Sail.BitVec.access pc 1 = 0#1 := by
  simp only [Sail.BitVec.access]
  have h : pc[1]! = false := by
    rw [getElem!_pos pc 1 (by omega), BitVec.getElem_eq_testBit_toNat, Nat.testBit_succ,
      Nat.testBit_zero, decide_eq_false_iff_not]
    omega
  rw [h]; rfl

theorem fetch_F_Base
    (σ : SequentialState RegisterType trivialChoiceSource)
    (pc : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (vmstatus : RegisterType Register.mstatus)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (vmisa : RegisterType Register.misa)
    (hpc : σ.regs.get? Register.PC = some (pc : RegisterType Register.PC))
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmisa : σ.regs.get? Register.misa = some vmisa)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ pc.toNat)
    (hhi : pc.toNat + 4 ≤ tohostAddr)
    (halign : pc.toNat % 4 = 0)
    (h0 : σ.mem[pc.toNat]? = some b0) (h1 : σ.mem[pc.toNat + 1]? = some b1)
    (h2 : σ.mem[pc.toNat + 2]? = some b2) (h3 : σ.mem[pc.toNat + 3]? = some b3)
    (hnotrvc : Sail.BitVec.extractLsb
      (((b3.append b2).append b1).append b0) 1 0 = 0b11#2) :
    (fetch ()).run σ
      = .ok (FetchResult.F_Base (((b3.append b2).append b1).append b0)) σ := by
  have hfb := fetch_bytes_four σ pc b0 b1 b2 b3 vmstatus vpmpaddr hpriv hmstatus hpma
    hcfg haddr hbase hlo hhi halign h0 h1 h2 h3
  have hrvc := isRVC_false b0 b1 b2 b3 hnotrvc
  have hzicc := currentlyEnabled_Ziccif σ
  have hzca := currentlyEnabled_Zca σ vmisa hmisa
  simp only [EStateM.run] at hfb hzicc hzca
  have hb0 := access_bit0 pc halign
  have hb1 := access_bit1 pc halign
  have haligned : is_aligned_vaddr (virtaddr.Virtaddr pc) 4 = true := by
    simp only [is_aligned_vaddr, beq_iff_eq]
    simp only [BitVec.toNatInt]
    have h : ((Int.ofNat pc.toNat).tmod (Int.ofNat 4)) = Int.ofNat (pc.toNat % 4) :=
      (Int.ofNat_tmod _ _).symm
    rw [show ((4 : Nat) : Int) = Int.ofNat 4 from rfl, h, halign]; rfl
  unfold fetch
  simp only [get_config_rvfi, ext_fetch_check_pc,
    LeanRV64DExecutable.SailME.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, EStateM.pure, pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hpc,
    Bool.false_eq_true, if_false, hb0, hb1, bne_self_eq_false, Bool.or_self,
    Bool.false_and]
  rw [hzca]
  simp only [ExceptT.bindCont, EStateM.map, EStateM.bind, EStateM.pure, EStateM.get,
    hpc, hzicc, haligned, Bool.and_true, if_true, hfb, hrvc,
    Bool.false_eq_true, if_false]

end Vsa.Sim
