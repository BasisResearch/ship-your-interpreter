import LeanRiscv

namespace Vsa.Sim

open LeanRV64DExecutable

def initMisa : BitVec 64 := 0x800000000034112f#64

def initMstatus : BitVec 64 := 0x0000000a00000000#64

def initPmpcfg : Vector Pmpcfg_ent 64 := Vector.replicate 64 (0#8)

def initPmpaddr : Vector (BitVec 64) 64 := Vector.replicate 64 (0#64)

def tohostAddr : Nat := 0x8001ad00

open MemoryRegionType AtomicSupport Reservability misaligned_exception in

def initPmaRegions : List PMA_Region :=
  [{ base := 0x1000#64
     size := 0x1000#64
     attributes := { mem_type := IOMemory
                     cacheable := true
                     coherent := false
                     executable := false
                     readable := true
                     writable := false
                     read_idempotent := true
                     write_idempotent := true
                     misaligned_exceptions := { load_store := none
                                                vector := none
                                                amo := AccessFault }
                     atomic_support := AMONone
                     reservability := RsrvNone
                     supports_cbo_zero := false
                     supports_pte_read := false
                     supports_pte_write := false
                     misaligned_atomicity_granule_size_exp := 0
                     vector_misaligned_atomicity_granule_size_exp := 0 }
     include_in_device_tree := false },
   { base := 0x2000000#64
     size := 0x10000000#64
     attributes := { mem_type := IOMemory
                     cacheable := false
                     coherent := true
                     executable := false
                     readable := true
                     writable := true
                     read_idempotent := false
                     write_idempotent := false
                     misaligned_exceptions := { load_store := none
                                                vector := none
                                                amo := AccessFault }
                     atomic_support := AMONone
                     reservability := RsrvNone
                     supports_cbo_zero := false
                     supports_pte_read := false
                     supports_pte_write := false
                     misaligned_atomicity_granule_size_exp := 0
                     vector_misaligned_atomicity_granule_size_exp := 0 }
     include_in_device_tree := false },
   { base := 0x80000000#64
     size := 0x80000000#64
     attributes := { mem_type := MainMemory
                     cacheable := true
                     coherent := true
                     executable := true
                     readable := true
                     writable := true
                     read_idempotent := true
                     write_idempotent := true
                     misaligned_exceptions := { load_store := none
                                                vector := none
                                                amo := AccessFault }
                     atomic_support := AMOCASQ
                     reservability := RsrvEventual
                     supports_cbo_zero := true
                     supports_pte_read := true
                     supports_pte_write := true
                     misaligned_atomicity_granule_size_exp := 4
                     vector_misaligned_atomicity_granule_size_exp := 4 }
     include_in_device_tree := true }]

end Vsa.Sim
