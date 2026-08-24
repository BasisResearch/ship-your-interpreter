import LeanRV64DExecutable
/-!
E1 (Layer 0, decode table): can the KERNEL evaluate `encdec_backwards` on a
concrete 32-bit word, with the state left symbolic? Probe with #eval first
(exploration tooling only), then attempt the rfl/decide proof.
-/
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1

-- a dummy state for exploratory #eval only
def dummy : SequentialState RegisterType trivialChoiceSource :=
  ⟨Std.ExtDHashMap.emptyWithCapacity, (), Std.ExtHashMap.emptyWithCapacity,
    default, default, default⟩

-- 0x00000513 = addi a0, x0, 0 (li a0,0)
#eval match (encdec_backwards 0x00000513#32).run dummy with
  | .ok ast _ => s!"decoded ok: {repr ast}" |>.take 120
  | .error _ _ => "decode error"
