import Vsa.Sim.rows.ScaffoldRows
import Vsa.Sim.rows.StmtForInitArmStagePre
import Vsa.Sim.rows.StmtForLoopSegPreB
import Vsa.Sim.ExecBlock
import Vsa.Sim.BridgeSegOut
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.ValueTruthySpec
import Vsa.Sim.BlockTactics2

/-!
# Concrete `ExecInit.some` prefix

The initializer prefix loads the present statement pointer and enters the
`exec_stmt` child through the reflected `0x80004248..0x80004254` call span.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim.ScaffoldRows

local notation "SpecSt" => Vsa.While.St

/-! The present-initializer discriminator.  Its fallthrough is the already
reflected `stmtForInitBodySeg` at `0x80004248`. -/

end Vsa.Sim.ScaffoldRows
