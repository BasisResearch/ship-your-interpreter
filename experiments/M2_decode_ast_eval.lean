import Vsa.Elf
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa

def decodeWord (w : BitVec 32) : String :=
  match Vsa.whileElf? with
  | .error e => s!"ERR {e}"
  | .ok elf =>
    match ((do Vsa.setupElf elf; ext_decode w : SailM instruction)).run (Vsa.initState elf) with
    | .ok ast _ => toString (repr ast)
    | .error e _ => s!"ERR {e.print}"

#eval IO.println (decodeWord 0x00000513#32)
#eval IO.println (decodeWord 0x00008067#32)
#eval IO.println (decodeWord 0x00813583#32)
#eval IO.println (decodeWord 0x0062f863#32)
