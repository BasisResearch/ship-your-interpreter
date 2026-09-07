import Vsa.Sim.CertifiedSegment
import Vsa.Sim.rows.ExecWhileRouteRows

namespace Vsa.Sim

open LeanRV64DExecutable
open Vsa.Alloc
open Vsa.Machine (Config)
open Vsa.MemRepr (Mem)

/-- The two emitted residual instances sharing the same body-return machine cut. -/
inductive WhileBodyReturnResidual where
  | returning
  | looping
  deriving DecidableEq, Repr

def WhileBodyReturnResidual.identity : WhileBodyReturnResidual → SegmentIdentity
  | .returning => ⟨"hSWhileRetBodyReturn", "hSWhileRet", 0x80004088#64,
      0x80004034#64, true⟩
  | .looping => ⟨"hSWhileLoopBodyReturn", "hSWhileLoop", 0x80004088#64,
      0x80004034#64, true⟩

/-- Concrete parameters of the already proved finite route. -/
structure WhileBodyReturnArgs where
  g : (R : Register) → Option (RegisterType R)
  status : BitVec 64
  sp : BitVec 64
  ra : BitVec 64
  s0 : BitVec 64
  s1 : BitVec 64
  s2 : BitVec 64
  s3 : BitVec 64
  loads : List (List (BitVec 8))
  memory : Mem
  output : Array String

def WhileBodyReturnArgs.pre (args : WhileBodyReturnArgs) : Config → Prop :=
  ExecWhileRoutePreF execWhileLoopRouteSeg args.g args.status args.sp args.ra
    args.s0 args.s1 args.s2 args.s3 args.loads 0x80004088#64 args.memory args.output

def WhileBodyReturnArgs.post (args : WhileBodyReturnArgs) (cfg : Config) : Prop :=
  ExecWhileRoutePost execWhileLoopRouteSeg 0x80004034#64 args.status args.sp args.ra
    args.s0 args.s1 args.s2 args.s3 args.loads args.memory args.output cfg ∧
  (∀ R, AbiPreserved R = true → cfg.σ.regs.get? R = args.g R) ∧
  cfg.tick < 2 ∧ ∃ w, cfg.σ.regs.get? Register.minstret = some w

def whileBodyReturnEffect : RegionEffect := ⟨.abi, [], true⟩

theorem whileBodyReturnEffect_denote (values : Nat → Nat) :
    whileBodyReturnEffect.denote values = execWhileRouteEffect := by
  apply FrameEffect.ext
  · rfl
  · funext a
    simp [RegionEffect.denote, whileBodyReturnEffect, execWhileRouteEffect]
  · apply propext
    simp [RegionEffect.denote, whileBodyReturnEffect, execWhileRouteEffect]

/-- A checked certificate for the exact finite body-return span. -/
def whileBodyReturnCertified (values : Nat → Nat)
    (residual : WhileBodyReturnResidual) (args : WhileBodyReturnArgs) :
    CertifiedSpan values residual.identity args.pre args.post where
  segment :=
    { effect := whileBodyReturnEffect
      machine := by
        rw [whileBodyReturnEffect_denote]
        exact execWhileLoopRouteRow_framed args.g args.status args.sp args.ra
          args.s0 args.s1 args.s2 args.s3 args.loads args.memory args.output }
  entry := by
    intro cfg hp
    rcases hp with ⟨⟨⟨_, _, hpc, _⟩, _⟩, _⟩
    cases residual <;> exact hpc
  exit := by
    intro cfg hq
    rcases hq with ⟨⟨_, _, _, hpc, _⟩, _⟩
    cases residual <;> exact hpc

/-- Emission carries a universally quantified proof and a descriptor equality.
Changing its effect independently of the machine theorem fails type checking. -/
structure WhileBodyReturnExport (identity : SegmentIdentity) where
  effect : RegionEffect
  certify : ∀ values (args : WhileBodyReturnArgs),
    CertifiedSpan values identity args.pre args.post
  exactEffect : ∀ values args, (certify values args).segment.effect = effect

def whileBodyReturnExport (residual : WhileBodyReturnResidual) :
    WhileBodyReturnExport residual.identity where
  effect := whileBodyReturnEffect
  certify := fun values args => whileBodyReturnCertified values residual args
  exactEffect := fun _ _ => rfl

/-- Matching includes residual field, both PCs, and the stop policy. -/
def lookupWhileBodyReturnExport (identity : SegmentIdentity) :
    Option (WhileBodyReturnExport identity) :=
  if h : identity = WhileBodyReturnResidual.returning.identity then
    some (h.symm ▸ whileBodyReturnExport .returning)
  else if h : identity = WhileBodyReturnResidual.looping.identity then
    some (h.symm ▸ whileBodyReturnExport .looping)
  else none

/-- An unknown or mutated query identity has no certificate. -/
theorem lookupWhileBodyReturnExport_reject (identity : SegmentIdentity)
    (hret : identity ≠ WhileBodyReturnResidual.returning.identity)
    (hloop : identity ≠ WhileBodyReturnResidual.looping.identity) :
    lookupWhileBodyReturnExport identity = none := by
  simp [lookupWhileBodyReturnExport, hret, hloop]

#print axioms whileBodyReturnCertified
#print axioms whileBodyReturnExport

end Vsa.Sim
