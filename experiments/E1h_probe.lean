import Vsa.Elf
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000

def dummy : SequentialState RegisterType trivialChoiceSource :=
  ⟨Std.ExtDHashMap.emptyWithCapacity, (), Std.ExtHashMap.emptyWithCapacity,
    default, default, default⟩

def baseState : SequentialState RegisterType trivialChoiceSource :=
  match ((sail_model_init ()) *> writeReg cur_privilege Privilege.Machine).run dummy with
  | .ok _ s => s
  | .error _ s => s

-- probe 1: fully concrete state, rfl
example :
    (encdec_backwards 0x00000513#32).run baseState =
    .ok (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5,
      regidx.Regidx 0x0a#5, iop.ADDI)) baseState := by
  rfl
