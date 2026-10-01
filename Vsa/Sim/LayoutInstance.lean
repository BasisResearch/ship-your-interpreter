import Vsa.Sim.GeomFacts
import Vsa.Sim.LocaleData
import Vsa.Sim.StderrStream
import Vsa.Sim.JmpSpec
import Vsa.Sim.EvalSimCommon
import Vsa.Sim.RuntimeOwnershipInitial
import Vsa.Refinement
import Vsa.Sim.SharedGeometry
import Vsa.Sim.BlockPilot
import Vsa.Sim.Code.ImageStatics
import Vsa.Sim.DecodeNF
import Vsa.Sim.EnvDefSpec2
import Vsa.Sim.SnprintfSpec5
import Vsa.Sim.StrcmpSpecW3
import Vsa.Sim.ValueEqualSpec2

open Vsa Vsa.Alloc Vsa.Sim
open Vsa.RuntimeRepr
open Vsa.Machine (Config)
open LeanRV64DExecutable

namespace Vsa.Sim.LayoutInstance

set_option maxHeartbeats 400000

def interpRunEntry : Nat := 0x800043ec

def stackSL : StackLayout := { lo := 0x87800000, hi := 0x88000000 }

def spEntry : Nat := 0x87fffd00

def gpEntry : Nat := 0x8001b510

def interpObject : Nat := 0x87fffe10

def interpRunWriteFootprint (inp : BitVec 64) (k : Nat) : Prop :=
  (stackSL.lo ≤ k ∧ k < stackSL.hi) ∨
  (inp.toNat + 16 ≤ k ∧ k < inp.toNat + 128)

structure InterpRunPhysicalFacts
    (c : Config) (stmts count : Nat) (inp : BitVec 64)
    (N : NativeAddrs) (A : Arena) (φf φc : Vsa.While.Addr → Nat)
    (aLeft : Nat) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 interpRunEntry)
  interp_arg : c.σ.regs.get? Register.x10 = some inp
  interp_local : inp = BitVec.ofNat 64 interpObject
  stmts_arg : c.σ.regs.get? Register.x11 = some (BitVec.ofNat 64 stmts)
  count_arg : c.σ.regs.get? Register.x12 = some (BitVec.ofNat 64 count)

  repl_arg : c.σ.regs.get? Register.x13 = some (0#64 : BitVec 64)

  ra : c.σ.regs.get? Register.x1 = some (0x800045ec#64 : BitVec 64)
  sp : c.σ.regs.get? Register.x2 = some (BitVec.ofNat 64 spEntry)
  gp : c.σ.regs.get? Register.x3 = some (BitVec.ofNat 64 gpEntry)
  main_ra : Vsa.MemRepr.read64 c.σ.mem 0x87fffff8 = some 0x80000038
  htif_payload : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  s0 : ∃ v, c.σ.regs.get? Register.x8 = some v
  s1 : ∃ v, c.σ.regs.get? Register.x9 = some v
  s2 : ∃ v, c.σ.regs.get? Register.x18 = some v
  s3 : ∃ v, c.σ.regs.get? Register.x19 = some v
  s4 : ∃ v, c.σ.regs.get? Register.x20 = some v
  s5 : ∃ v, c.σ.regs.get? Register.x21 = some v
  s6 : ∃ v, c.σ.regs.get? Register.x22 = some v
  s7 : ∃ v, c.σ.regs.get? Register.x23 = some v
  s8 : ∃ v, c.σ.regs.get? Register.x24 = some v
  s9 : ∃ v, c.σ.regs.get? Register.x25 = some v
  s10 : ∃ v, c.σ.regs.get? Register.x26 = some v
  s11 : ∃ v, c.σ.regs.get? Register.x27 = some v
  text_image : Code.FixedTextLoaded c.σ.mem
  rodata_image : Code.FixedRodataLoaded c.σ.mem
  statics : Code.ImageStaticsLoaded c.σ.mem

  console : ConsoleBoot c.σ.mem
  exit_runtime : ExitRuntimeData c.σ.mem
  arena_protected : ∀ a, ProtectedInitialByte a → ¬ (A.lo ≤ a ∧ a < A.hi)
  out : OutRepr c.σ Vsa.While.initSt

  globals : Vsa.MemRepr.read64 c.σ.mem inp.toNat = some (φf 0)
  call_depth : Vsa.MemRepr.read32 c.σ.mem (inp.toNat + 8) = some 0
  interp_geom : ObjGeom (inp.toNat, 384) stackSL spEntry
  setjmp_geom : WinRAM (inp + 16#64)
  stack_ok : StackOK stackSL (BitVec.ofNat 64 spEntry) (176 + 1088)

  stack_bytes : ∀ k, stackSL.lo ≤ k → k < stackSL.hi →
    ∃ b : BitVec 8, c.σ.mem[k]? = some b
  stmts_align : stmts % 8 = 0
  stmts_ram : 0x80000000 ≤ stmts ∧ stmts + 8 * count ≤ 0x100000000
  stmts_win : tohostAddr + 16 ≤ stmts
  stmts_stack : stmts + 8 * count ≤ stackSL.lo ∨ spEntry ≤ stmts
  store : StoreRepr c.σ.mem N A φf φc Vsa.While.initSt.store
  native_addrs : N.print = 0x80002ed4 ∧ N.println = 0x80002f7c ∧
    N.assert = 0x80002df4

  store_survives : ∀ m' : Vsa.MemRepr.Mem,
    (∀ k, ¬ interpRunWriteFootprint inp k → c.σ.mem[k]? = m'[k]?) →
    StoreRepr m' N A φf φc Vsa.While.initSt.store
  arena_budget : A.lo + aLeft ≤ A.hi

def interpRunFrame : Nat := 176

def helperHeadroom : Nat := 2048

structure ProgramStackFits (p : Vsa.While.Program) : Prop where
  need : stackSL.lo + Vsa.While.Stmt.stackNeedList p +
    Vsa.While.maxCallDepth * Vsa.While.perCallBudget + Vsa.While.evalFrame + helperHeadroom +
    interpRunFrame ≤ spEntry
  bodies : Vsa.While.Stmt.bodiesBoundList Vsa.While.perCallBudget p = true

def programStackFits (p : Vsa.While.Program) : Bool :=
  decide (stackSL.lo + Vsa.While.Stmt.stackNeedList p +
    Vsa.While.maxCallDepth * Vsa.While.perCallBudget + Vsa.While.evalFrame + helperHeadroom +
    interpRunFrame ≤ spEntry) &&
  Vsa.While.Stmt.bodiesBoundList Vsa.While.perCallBudget p

theorem ProgramStackFits.of_check {p : Vsa.While.Program}
    (h : programStackFits p = true) : ProgramStackFits p := by
  unfold programStackFits at h
  rw [Bool.and_eq_true, decide_eq_true_iff] at h
  exact ⟨h.1, h.2⟩

def StackAdmissible (m : Vsa.MemRepr.Mem) (stmts count : Nat) : Prop :=
  ∀ p : Vsa.While.Program, Vsa.MemRepr.ProgramRepr m stmts count p → ProgramStackFits p

structure BootFrame where
  cap : Nat
  pn : Nat
  pv : Nat
  sblk : Nat × Nat
  nblk : Nat × Nat
  vblk : Nat × Nat

def BootFrame.blocks (F : BootFrame) : List (Nat × Nat) :=
  F.sblk :: (if F.cap = 0 then [] else [F.nblk, F.vblk])

structure BootFrameChunks (m : Vsa.MemRepr.Mem) (chunks : List DlHeap.Chunk)
    (shared : Nat → Prop) (e : Nat) (F : BootFrame) : Prop where
  cap : Vsa.MemRepr.read32 m (e + 4) = some F.cap
  names : Vsa.MemRepr.read64 m (e + 8) = some F.pn
  vals : Vsa.MemRepr.read64 m (e + 16) = some F.pv
  sblk : F.sblk.1 ≤ e ∧ e + 32 ≤ F.sblk.1 + F.sblk.2
  arrays : 0 < F.cap → F.nblk.1 = F.pn ∧ 8 * F.cap ≤ F.nblk.2 ∧
    F.vblk.1 = F.pv ∧ 24 * F.cap ≤ F.vblk.2

  live : ∀ b ∈ F.blocks, ∃ c ∈ chunks, c.inuse = true ∧ b = (c.addr + 16, c.size - 8)

  nodup : F.blocks.Nodup

  unshared : ∀ b ∈ F.blocks, ∀ k, b.1 ≤ k → k < b.1 + b.2 → ¬ shared k

  cap_canon : F.cap = 8

def impureStderrAddr : Nat := consoleReent + 24

structure BootHeapFacts (m : Vsa.MemRepr.Mem) (shared : Nat → Prop) (e top brkv : Nat)
    (chunks : List DlHeap.Chunk) (F : BootFrame) : Prop where

  top_room : top + 16 ≤ brkv

  brk_page : brkv % 4096 = 0

  binblocks : ∀ bb, Vsa.MemRepr.read64 m DlHeap.binblocksAddr = some bb → bb < 2 ^ 32

  frame : BootFrameChunks m chunks shared e F

  stderr : Vsa.MemRepr.read64 m impureStderrAddr = some exitStderr

  locale : LocaleData m

  stderrStream : StderrStream m

  shared_geom : SharedReadWin shared stackSL

structure BootHeap (m : Vsa.MemRepr.Mem) (A : Arena) (φf φc : Vsa.While.Addr → Nat)
    (stmts count : Nat) (D : RuntimeOwnership.InitialOwnershipData) (top brkv : Nat)
    (chunks : List DlHeap.Chunk) (bins : Nat → List Nat) (F : BootFrame) : Prop where
  owned : RuntimeOwnership.InitialOwned m A stackSL φf φc stmts count D
  alloc : DlHeap.InitialAllocatorAt m D.exts (RuntimeOwnership.ReallocExtent D.allocations)
    stmts count top brkv chunks bins
  facts : BootHeapFacts m D.shared (φf 0) top brkv chunks F

structure InterpRunReadyFacts
    (c : Config) (stmts count : Nat) (inp : BitVec 64)
    (N : NativeAddrs) (A : Arena) (φf φc : Vsa.While.Addr → Nat)
    (aLeft : Nat) : Prop extends
    InterpRunPhysicalFacts c stmts count inp N A φf φc aLeft where

  boot : ∃ (D : RuntimeOwnership.InitialOwnershipData) (top brkv : Nat)
    (chunks : List DlHeap.Chunk) (bins : Nat → List Nat) (F : BootFrame),
    BootHeap c.σ.mem A φf φc stmts count D top brkv chunks bins F

  stack_admissible : StackAdmissible c.σ.mem stmts count

  gprs : ∀ n, 1 ≤ n → n ≤ 31 → (gprGet c.σ n).isSome

  s0_impure : c.σ.regs.get? Register.x8 = some (0x8001b970#64 : BitVec 64)

def InterpRunReady (c : Config) (stmts count : Nat) : Prop :=
  ∃ (inp : BitVec 64) (N : NativeAddrs) (A : Arena)
    (φf φc : Vsa.While.Addr → Nat) (aLeft : Nat),
    InterpRunReadyFacts c stmts count inp N A φf φc aLeft

def interpRunLayout : Vsa.Refine.Layout where
  atInterpRun c a n := InterpRunReady c a n

end Vsa.Sim.LayoutInstance
