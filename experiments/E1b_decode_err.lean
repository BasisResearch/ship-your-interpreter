import LeanRV64DExecutable
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1

def dummy : SequentialState RegisterType trivialChoiceSource :=
  ⟨Std.ExtDHashMap.emptyWithCapacity, (), Std.ExtHashMap.emptyWithCapacity,
    default, default, default⟩

#eval match (encdec_backwards 0x00000513#32).run dummy with
  | .ok _ _ => "ok"
  | .error e _ => s!"error: {e.print}"
