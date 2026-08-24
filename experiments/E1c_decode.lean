import LeanRV64DExecutable
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1

def dummy : SequentialState RegisterType trivialChoiceSource :=
  ⟨Std.ExtDHashMap.emptyWithCapacity, (), Std.ExtHashMap.emptyWithCapacity,
    default, default, default⟩

#eval match ((sail_model_init ()) *> (encdec_backwards 0x00000513#32)).run dummy with
  | .ok ast _ => (s!"ok: {repr ast}").take 200
  | .error e _ => s!"error: {e.print}"
