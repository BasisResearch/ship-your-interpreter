import Vsa.Elf
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register

def dummy : SequentialState RegisterType trivialChoiceSource :=
  ⟨Std.ExtDHashMap.emptyWithCapacity, (), Std.ExtHashMap.emptyWithCapacity,
    default, default, default⟩

def try_ (m : SailM Unit) : String :=
  match (m *> (encdec_backwards 0x00000513#32)).run dummy with
  | .ok _ _ => "ok"
  | .error e _ => s!"error: {e.print}"

#eval try_ (sail_model_init ())
#eval try_ (sail_model_init () *> writeReg cur_privilege Privilege.Machine)
#eval try_ (sail_model_init () *> writeReg cur_privilege Privilege.Machine
  *> writeReg mseccfg (Mk_Mseccfg (BitVec.zero 64)))
