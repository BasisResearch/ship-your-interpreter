import Vsa.Sim.EqNeReprReadback
import Vsa.Sim.TermEntry
import Vsa.While.StackNeed
import Vsa.Sim.Code.Exec_stmt
import Vsa.Sim.Code.Strcmp
import Vsa.Sim.LayoutInstance
import Vsa.Sim.MemcpySpec4
import Vsa.Sim.HelperCall
import Vsa.AllocResource
import Vsa.Sim.SegToTripleFramed
import Vsa.Sim.BridgeSeg
import Vsa.Sim.EnvGetSpec3
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.BlockTactics2
import Vsa.Sim.AstTransport
import Vsa.MemReprReadFields
import Vsa.MemReprWithin
import Vsa.Sim.MemRegion
import Vsa.Sim.EvalSimCommon
import Vsa.Sim.ExecEntry
import Vsa.Sim.DecodeNF
import Vsa.Sim.DivLoops
import Vsa.Sim.ExitFootprint
import Vsa.Sim.JmpSpec
import Vsa.Sim.BlockMem
import Vsa.Sim.BlockPilot
import Vsa.While.Cost
import Vsa.Sim.PinW

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.MemRepr Vsa.RuntimeRepr
open Vsa.Alloc (AbiPreserved StackLayout StackOK)
open Vsa.Sim.Code (StrcmpLoaded FixedTextLoaded)
open Vsa.While (Addr Value)

namespace Vsa.Sim

@[simp] private theorem sext0_64 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by decide
@[simp] private theorem sext32_64 : (sign_extend (m := 64) (0x020#12) : BitVec 64).toNat = 32 := by decide

end Vsa.Sim
