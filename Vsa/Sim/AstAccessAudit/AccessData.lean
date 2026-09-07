import Vsa.Sim.AstAccessAudit.AccessSnapshot
import Vsa.Sim.AstAccessAudit.AccessTrace
import Vsa.Sim.OutputAliasPrefix

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.AstAccessAudit
open Vsa.Sim.OutputAliasLoaded

def traceStores : List WEntry :=
  [(0x87fffc50, 8, 0x87fffe10#64),
   (0x87fffcf8, 8, 0x800045ec#64),
   (0x87fffcf0, 8, 0x0#64),
   (0x87fffce8, 8, 0x0#64),
   (0x87fffce0, 8, 0x0#64),
   (0x87fffcd8, 8, 0x0#64),
   (0x87fffcd0, 8, 0x0#64),
   (0x87fffcc8, 8, 0x0#64),
   (0x87fffcc0, 8, 0x0#64),
   (0x87fffc68, 8, 0x82000000#64),
   (0x87fffc60, 8, 0x2#64),
   (0x87fffc58, 8, 0x0#64),
   (0x87fffe20, 8, 0x80004428#64),
   (0x87fffe28, 8, 0x0#64),
   (0x87fffe30, 8, 0x0#64),
   (0x87fffe38, 8, 0x0#64),
   (0x87fffe40, 8, 0x0#64),
   (0x87fffe48, 8, 0x0#64),
   (0x87fffe50, 8, 0x0#64),
   (0x87fffe58, 8, 0x0#64),
   (0x87fffe60, 8, 0x0#64),
   (0x87fffe68, 8, 0x0#64),
   (0x87fffe70, 8, 0x0#64),
   (0x87fffe78, 8, 0x0#64),
   (0x87fffe80, 8, 0x0#64),
   (0x87fffe88, 8, 0x87fffc50#64),
   (0x87fffca8, 4, 0x0#64),
   (0x87fffcb0, 8, 0x0#64),
   (0x87fffc40, 8, 0x82000000#64),
   (0x87fffc38, 8, 0x4000#64),
   (0x87fffc30, 8, 0x82000010#64),
   (0x87fffc28, 8, 0x3#64),
   (0x87fffc48, 8, 0x80004478#64)]

def traceD000 : TraceData :=
  { pc := 0x800043ec#64,
    regs := [(1, 0x800045ec#64), (2, 0x87fffd00#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0x0#64), (8, 0x0#64), (9, 0x0#64), (10, 0x87fffe10#64), (11, 0x82000000#64), (12, 0x2#64), (13, 0x0#64), (14, 0x0#64), (15, 0x0#64), (16, 0x0#64), (17, 0x0#64), (18, 0x0#64), (19, 0x0#64), (20, 0x0#64), (21, 0x0#64), (22, 0x0#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := accessLog ++ traceStores.take 0,
    out := #[], payload := 0x0#4 }

def traceD001 : TraceData :=
  { pc := 0x80004424#64,
    regs := [(1, 0x800045ec#64), (2, 0x87fffc50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0x0#64), (8, 0x0#64), (9, 0x0#64), (10, 0x87fffe20#64), (11, 0x82000000#64), (12, 0x2#64), (13, 0x0#64), (14, 0x0#64), (15, 0x0#64), (16, 0x0#64), (17, 0x0#64), (18, 0x0#64), (19, 0x0#64), (20, 0x0#64), (21, 0x0#64), (22, 0x0#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := accessLog ++ traceStores.take 12,
    out := #[], payload := 0x0#4 }

def traceD002 : TraceData :=
  { pc := 0x80006ffc#64,
    regs := [(1, 0x80004428#64), (2, 0x87fffc50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0x0#64), (8, 0x0#64), (9, 0x0#64), (10, 0x87fffe20#64), (11, 0x82000000#64), (12, 0x2#64), (13, 0x0#64), (14, 0x0#64), (15, 0x0#64), (16, 0x0#64), (17, 0x0#64), (18, 0x0#64), (19, 0x0#64), (20, 0x0#64), (21, 0x0#64), (22, 0x0#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := accessLog ++ traceStores.take 12,
    out := #[], payload := 0x0#4 }

def traceD003 : TraceData :=
  { pc := 0x80004428#64,
    regs := [(1, 0x80004428#64), (2, 0x87fffc50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0x0#64), (8, 0x0#64), (9, 0x0#64), (10, 0x0#64), (11, 0x82000000#64), (12, 0x2#64), (13, 0x0#64), (14, 0x0#64), (15, 0x0#64), (16, 0x0#64), (17, 0x0#64), (18, 0x0#64), (19, 0x0#64), (20, 0x0#64), (21, 0x0#64), (22, 0x0#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := accessLog ++ traceStores.take 26,
    out := #[], payload := 0x0#4 }

def traceD004 : TraceData :=
  { pc := 0x8000445c#64,
    regs := [(1, 0x80004428#64), (2, 0x87fffc50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0x0#64), (8, 0x82000000#64), (9, 0x4000#64), (10, 0x87fffca8#64), (11, 0x82000000#64), (12, 0x2#64), (13, 0x0#64), (14, 0x0#64), (15, 0x0#64), (16, 0x0#64), (17, 0x0#64), (18, 0x82000010#64), (19, 0x3#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := accessLog ++ traceStores.take 26,
    out := #[], payload := 0x0#4 }

def traceD005 : TraceData :=
  { pc := 0x800027ec#64,
    regs := [(1, 0x80004460#64), (2, 0x87fffc50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0x0#64), (8, 0x82000000#64), (9, 0x4000#64), (10, 0x87fffca8#64), (11, 0x82000000#64), (12, 0x2#64), (13, 0x0#64), (14, 0x0#64), (15, 0x0#64), (16, 0x0#64), (17, 0x0#64), (18, 0x82000010#64), (19, 0x3#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := accessLog ++ traceStores.take 26,
    out := #[], payload := 0x0#4 }

def traceD006 : TraceData :=
  { pc := 0x80004460#64,
    regs := [(1, 0x80004460#64), (2, 0x87fffc50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0x0#64), (8, 0x82000000#64), (9, 0x4000#64), (10, 0x87fffca8#64), (11, 0x82000000#64), (12, 0x2#64), (13, 0x0#64), (14, 0x0#64), (15, 0x0#64), (16, 0x0#64), (17, 0x0#64), (18, 0x82000010#64), (19, 0x3#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := accessLog ++ traceStores.take 28,
    out := #[], payload := 0x0#4 }

def traceD007 : TraceData :=
  { pc := 0x80004474#64,
    regs := [(1, 0x80004460#64), (2, 0x87fffc50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0x0#64), (8, 0x82000000#64), (9, 0x4000#64), (10, 0x87fffe10#64), (11, 0x4000#64), (12, 0x81000000#64), (13, 0x87fffca8#64), (14, 0x0#64), (15, 0x87fffe10#64), (16, 0x0#64), (17, 0x0#64), (18, 0x82000010#64), (19, 0x3#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := accessLog ++ traceStores.take 28,
    out := #[], payload := 0x0#4 }

def traceD008 : TraceData :=
  { pc := 0x80003fe0#64,
    regs := [(1, 0x80004478#64), (2, 0x87fffc50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0x0#64), (8, 0x82000000#64), (9, 0x4000#64), (10, 0x87fffe10#64), (11, 0x4000#64), (12, 0x81000000#64), (13, 0x87fffca8#64), (14, 0x0#64), (15, 0x87fffe10#64), (16, 0x0#64), (17, 0x0#64), (18, 0x82000010#64), (19, 0x3#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := accessLog ++ traceStores.take 28,
    out := #[], payload := 0x0#4 }

def traceD009 : TraceData :=
  { pc := 0x80004014#64,
    regs := [(1, 0x80004478#64), (2, 0x87fffba0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0x0#64), (8, 0x4000#64), (9, 0x87fffe10#64), (10, 0x87fffe10#64), (11, 0x4000#64), (12, 0x81000000#64), (13, 0x87fffca8#64), (14, 0x80019fb8#64), (15, 0x87fffe10#64), (16, 0x8#64), (17, 0x0#64), (18, 0x87fffca8#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := accessLog ++ traceStores.take 33,
    out := #[], payload := 0x0#4 }

theorem access_initial_regs : GHolds accessConfig.σ traceD000.regs := by
  simp [traceD000, GHolds, gprGet, accessConfig, physicalConfig,
    physicalState, LayoutInstance.spEntry, LayoutInstance.gpEntry,
    LayoutInstance.interpObject]

theorem access_initial_mcause : accessConfig.σ.regs.get? Register.mcause = none := by
  change physicalRegs.get? Register.mcause = none
  apply Std.ExtDHashMap.get?_ofList_of_contains_eq_false
  decide

theorem access_initial_trace : AccessHolds traceD000 accessConfig where
  good := (physical_carrier accessMem).good
  tick := by decide
  pc := physicalRegs_PC
  minstret := ⟨0, physicalRegs_minstret⟩
  regs := access_initial_regs
  mem := rfl
  out := rfl
  payload := physicalRegs_htif_payload_writes
  mcause_absent := access_initial_mcause

#print axioms access_initial_trace
end Vsa.Sim.AstAccessAudit
