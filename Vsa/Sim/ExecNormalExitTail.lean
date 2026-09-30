import Vsa.Sim.ExecBrkCont
import Vsa.Sim.ExecBlock
import Vsa.Sim.ObsAvoid

/-!
# `ExecNormalExitTail` — the parametric `li a0,0; j 0x8000409c; epilogue` tail

Every `exec_stmt` arm that completes `.normal` ends with the same two
instructions at an arm-specific PC (`0x80004090` for `while`, `0x80004184` for
`expr`, `0x800042d4` for `if` without `else`, `0x80004118` for `varDecl`,
`0x800041e0` for `block`) followed by the shared epilogue.  `WhileNormalExitTail`
proved this tail at `0x80004090`; this file proves it ONCE over the `li` PC and
the `j` immediate, taking the two site lemmas as certificate fields.
-/

-- discipline: allow(R7-conj-tower-def) every `∃` here is a single saved-register witness inside a named-field structure (`NormalExitTailPre`, `EpilogueReady`), mirroring `PreExecEpilogue`'s ghost pins; no ∃/∧ tower is defined
