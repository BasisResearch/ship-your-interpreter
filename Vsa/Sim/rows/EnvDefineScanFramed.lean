import Vsa.Sim.SegToTripleFramed
import Vsa.Sim.BridgeSegFramed
import Vsa.Sim.EnvGetSpec3
import Vsa.Sim.rows.EnvDefineEpilogueCore

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.MemRepr
open Vsa.RuntimeRepr
open Vsa.Logic (Triple)
open Vsa.Alloc (AbiPreserved StackLayout StackOK)

namespace Vsa.Sim

set_option maxHeartbeats 1600000

def envDefineScanGhost
    (gm : (R : Register) → Option (RegisterType R))
    (idx cursor : BitVec 64) : (R : Register) → Option (RegisterType R) :=
  fun R =>
    if h8 : R = Register.x8 then some (h8 ▸ idx)
    else if h9 : R = Register.x9 then some (h9 ▸ cursor)
    else gm R

@[simp] theorem envDefineScanGhost_x8
    (gm : (R : Register) → Option (RegisterType R)) (idx cursor : BitVec 64) :
    envDefineScanGhost gm idx cursor Register.x8 = some idx := by
  simp [envDefineScanGhost]

@[simp] theorem envDefineScanGhost_x9
    (gm : (R : Register) → Option (RegisterType R)) (idx cursor : BitVec 64) :
    envDefineScanGhost gm idx cursor Register.x9 = some cursor := by
  simp [envDefineScanGhost]

def envDefineScanBaseGhost
    (gm : (R : Register) → Option (RegisterType R))
    (pn : BitVec 64) : (R : Register) → Option (RegisterType R) :=
  fun R => if h22 : R = Register.x22 then some (h22 ▸ pn) else gm R

@[simp] theorem envDefineScanBaseGhost_x22
    (gm : (R : Register) → Option (RegisterType R)) (pn : BitVec 64) :
    envDefineScanBaseGhost gm pn Register.x22 = some pn := by
  simp [envDefineScanBaseGhost]

end Vsa.Sim
