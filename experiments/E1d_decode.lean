import Vsa.Elf
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa

#eval match whileElf? with
  | .error e => s!"parse error {e}"
  | .ok elf =>
    match ((sail_model_init ()) *> (initializeRegisters elf) *>
           (encdec_backwards 0x00000513#32)).run (initState elf) with
    | .ok ast _ => (s!"ok: {repr ast}")
    | .error e _ => s!"error: {e.print}"
