import Vsa.Sim.rows.NativeBodyPrint
import Vsa.Sim.DeriveCaseRow

/-! Reflected finite regions used to construct the native-output components. -/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

#derive_case npCommonSeg chain
  [(0x80002ed4#64, 0xfb010113#32),
   (0x80002ed8#64, 0x03413023#32),
   (0x80002edc#64, 0x04113423#32),
   (0x80002ee0#64, 0x00050a13#32)]

#derive_case npSetupSeg chain
  [(0x80002ee8#64, 0x04813023#32),
   (0x80002eec#64, 0x02913c23#32),
   (0x80002ef0#64, 0x03213823#32),
   (0x80002ef4#64, 0x03313423#32),
   (0x80002ef8#64, 0x00068413#32),
   (0x80002efc#64, 0x00060993#32),
   (0x80002f00#64, 0x00000493#32),
   (0x80002f04#64, 0x46018913#32)]

#derive_case npBodyCopySeg chain
  [(0x80002f1c#64, 0x00093783#32),
   (0x80002f20#64, 0x00043683#32),
   (0x80002f24#64, 0x00843703#32),
   (0x80002f28#64, 0x0107b583#32),
   (0x80002f2c#64, 0x01043783#32),
   (0x80002f30#64, 0x00010513#32),
   (0x80002f34#64, 0x00d13023#32),
   (0x80002f38#64, 0x00e13423#32),
   (0x80002f3c#64, 0x00f13823#32),
   (0x80002f40#64, 0x0014849b#32)]

#derive_case npSeparatorSeg chain
  [(0x80002f0c#64, 0x00093783#32),
   (0x80002f10#64, 0x01840413#32),
   (0x80002f14#64, 0x0107b583#32)]

#derive_case npRestoreSeg chain
  [(0x80002f50#64, 0x04013403#32),
   (0x80002f54#64, 0x03813483#32),
   (0x80002f58#64, 0x03013903#32),
   (0x80002f5c#64, 0x02813983#32),
   (0x80002f60#64, 0x000a0513#32)]

#derive_case npReturnSeg chain
  [(0x80002f68#64, 0x04813083#32),
   (0x80002f6c#64, 0x000a0513#32),
   (0x80002f70#64, 0x02013a03#32),
   (0x80002f74#64, 0x05010113#32)]

#derive_case nplnPrefixSeg chain
  [(0x80002f7c#64, 0xfd010113#32),
   (0x80002f80#64, 0x02813023#32),
   (0x80002f84#64, 0x00050413#32),
   (0x80002f88#64, 0x00010513#32),
   (0x80002f8c#64, 0x02113423#32)]

#derive_case nplnFputcSeg chain
  [(0x80002f94#64, 0x4601b783#32),
   (0x80002f98#64, 0x00a00513#32),
   (0x80002f9c#64, 0x0107b583#32)]

#derive_case nplnNullSeg chain
  [(0x80002fa4#64, 0x00040513#32)]

#derive_case nplnReturnSeg chain
  [(0x80002fac#64, 0x02813083#32),
   (0x80002fb0#64, 0x00040513#32),
   (0x80002fb4#64, 0x02013403#32),
   (0x80002fb8#64, 0x03010113#32)]

/- The anonymous-closure path omitted by `ValuePrintArms`: take the name-null
branch and tail-call `fwrite("<fn>", 1, 4, stream)`. -/
#derive_case vpClosureAnonArm chain
  [(0x80002928#64, 0x00853783#32),
   (0x8000292c#64, 0x0007b783#32),
   (0x80002930#64, 0x0087b603#32)]
    terminator ⟨0x80002934#64, 0x06060e63#32, 0x63#8, 0x0e#8, 0x06#8, 0x06#8,
      .br bop.BEQ true, 12, 0, 0x007c#13, 0#21, 0#12⟩ ;;
  [(0x800029b0#64, 0x00058693#32),
   (0x800029b4#64, 0x00400613#32),
   (0x800029b8#64, 0x00100593#32),
   (0x800029bc#64, 0x00017517#32),
   (0x800029c0#64, 0x91450513#32)]
    terminator ⟨0x800029c4#64, 0x09d0206f#32, 0x6f#8, 0x20#8, 0xd0#8, 0x09#8,
      .j, 0, 0, 0#13, 0x00289c#21, 0#12⟩

def VpClosureAnonArmPost (pv stream : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Mem) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x80005260#64 ∧
  GHolds c.σ
    (evalBlocks vpClosureAnonArm (SegEvalState.init (vpClosureL pv stream) lds)).regs

theorem vpClosureAnonArmRow (pv stream : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) :
    Triple (SegPre vpClosureAnonArm (vpClosureL pv stream) lds 0x80002928#64 m0)
      (VpClosureAnonArmPost pv stream lds m0) := by
  apply segToTriple vpClosureAnonArm (vpClosureL pv stream) lds 0x80002928#64 m0
    (VpClosureAnonArmPost pv stream lds m0)
    (by show ChainOK 0x80002928#64 [10, 11] vpClosureAnonArm; decide)
  intro σ' i' u' hG' _ hmem' hpc' _ hregs
  exact ⟨hG', by rw [hmem']; rfl, by rw [hpc']; rfl, hregs⟩

/-- Existential input package for a reflected straight-line region. -/
def FiniteReady (seg : List BBlock) (pc : BitVec 64) : Config → Prop := fun c =>
  ∃ (L : GRegs) (lds : List (List (BitVec 8))) (m : Mem),
    ChainOK pc (keysG L) seg ∧ SegPre seg L lds pc m c

/-- Exact reflected output package. -/
def FiniteDone (seg : List BBlock) (pc : BitVec 64) : Config → Prop := fun c =>
  ∃ (L : GRegs) (lds : List (List (BitVec 8))) (m : Mem),
    GoodState c.σ ∧
    c.σ.mem = writeLog m (evalBlocks seg (SegEvalState.init L lds)).log ∧
    c.σ.regs.get? Register.PC = some (evalBlocksPC pc (SegEvalState.init L lds) seg) ∧
    GHolds c.σ (evalBlocks seg (SegEvalState.init L lds)).regs

/-- Every finite region above runs by the reflected segment theorem. -/
theorem finiteRun (seg : List BBlock) (pc : BitVec 64) :
    Triple (FiniteReady seg pc) (FiniteDone seg pc) := by
  intro c hc
  obtain ⟨L, lds, m, hok, hpre⟩ := hc
  have hrun : Triple (SegPre seg L lds pc m) (fun c' =>
      GoodState c'.σ ∧
      c'.σ.mem = writeLog m (evalBlocks seg (SegEvalState.init L lds)).log ∧
      c'.σ.regs.get? Register.PC = some (evalBlocksPC pc (SegEvalState.init L lds) seg) ∧
      GHolds c'.σ (evalBlocks seg (SegEvalState.init L lds)).regs) := by
    apply segToTriple seg L lds pc m _ hok
    intro σ' i' u' hG' _ hmem' hpc' _ hregs'
    exact ⟨hG', hmem', hpc', hregs'⟩
  obtain ⟨c', hs, hpost⟩ := hrun c hpre
  exact ⟨c', hs, L, lds, m, hpost⟩

/-- One reflected body with only entry/exit semantic seams abstract. -/
structure Via1 (P Q : Config → Prop) (s1 : List BBlock) (p1 : BitVec 64) where
  enter : Triple P (FiniteReady s1 p1)
  leave : Triple (FiniteDone s1 p1) Q

theorem Via1.run (V : Via1 P Q s1 p1) : Triple P Q :=
  Triple.seq V.enter (Triple.seq (finiteRun s1 p1) V.leave)

/-- Two reflected bodies separated only by a semantic branch/call seam. -/
structure Via2 (P Q : Config → Prop)
    (s1 : List BBlock) (p1 : BitVec 64) (s2 : List BBlock) (p2 : BitVec 64) where
  enter : Triple P (FiniteReady s1 p1)
  middle : Triple (FiniteDone s1 p1) (FiniteReady s2 p2)
  leave : Triple (FiniteDone s2 p2) Q

theorem Via2.run (V : Via2 P Q s1 p1 s2 p2) : Triple P Q :=
  Triple.seq V.enter <| Triple.seq (finiteRun s1 p1) <| Triple.seq V.middle <|
    Triple.seq (finiteRun s2 p2) V.leave

/-- Three reflected bodies separated only by semantic branch/call seams. -/
structure Via3 (P Q : Config → Prop)
    (s1 : List BBlock) (p1 : BitVec 64) (s2 : List BBlock) (p2 : BitVec 64)
    (s3 : List BBlock) (p3 : BitVec 64) where
  enter : Triple P (FiniteReady s1 p1)
  middle12 : Triple (FiniteDone s1 p1) (FiniteReady s2 p2)
  middle23 : Triple (FiniteDone s2 p2) (FiniteReady s3 p3)
  leave : Triple (FiniteDone s3 p3) Q

theorem Via3.run (V : Via3 P Q s1 p1 s2 p2 s3 p3) : Triple P Q :=
  Triple.seq V.enter <| Triple.seq (finiteRun s1 p1) <| Triple.seq V.middle12 <|
    Triple.seq (finiteRun s2 p2) <| Triple.seq V.middle23 <|
      Triple.seq (finiteRun s3 p3) V.leave

/-- A reflected row already proved elsewhere, surrounded only by exact semantic
entry and leaf-call marshalling. -/
structure ViaTriple (P Q MidIn MidOut : Config → Prop) (body : Triple MidIn MidOut) where
  enter : Triple P MidIn
  leave : Triple MidOut Q

theorem ViaTriple.run (V : ViaTriple P Q MidIn MidOut body) : Triple P Q :=
  Triple.seq V.enter (Triple.seq body V.leave)

/-- A reflected arm followed by the exact external leaf contract it tail-calls.
Only the entry, call-boundary, and return-boundary marshals remain explicit. -/
structure ViaLeaf (P Q MidIn MidOut LeafIn LeafOut : Config → Prop)
    (body : Triple MidIn MidOut) (leaf : Triple LeafIn LeafOut) where
  enter : Triple P MidIn
  call : Triple MidOut LeafIn
  leave : Triple LeafOut Q

theorem ViaLeaf.run
    (V : ViaLeaf P Q MidIn MidOut LeafIn LeafOut body leaf) : Triple P Q :=
  Triple.seq V.enter <| Triple.seq body <| Triple.seq V.call <|
    Triple.seq leaf V.leave

/-- Two reflected bodies with one exact leaf after each body. -/
structure Via2TwoLeaves (P Q : Config → Prop)
    (s1 : List BBlock) (p1 : BitVec 64) (s2 : List BBlock) (p2 : BitVec 64)
    (L1In L1Out L2In L2Out : Config → Prop)
    (leaf1 : Triple L1In L1Out) (leaf2 : Triple L2In L2Out) where
  enter : Triple P (FiniteReady s1 p1)
  call1 : Triple (FiniteDone s1 p1) L1In
  next : Triple L1Out (FiniteReady s2 p2)
  call2 : Triple (FiniteDone s2 p2) L2In
  leave : Triple L2Out Q

theorem Via2TwoLeaves.run (V : Via2TwoLeaves P Q s1 p1 s2 p2
    L1In L1Out L2In L2Out leaf1 leaf2) : Triple P Q :=
  Triple.seq V.enter <| Triple.seq (finiteRun s1 p1) <| Triple.seq V.call1 <|
    Triple.seq leaf1 <| Triple.seq V.next <| Triple.seq (finiteRun s2 p2) <|
      Triple.seq V.call2 <| Triple.seq leaf2 V.leave

/-- Three reflected bodies followed by one exact leaf. -/
structure Via3TailLeaf (P Q : Config → Prop)
    (s1 : List BBlock) (p1 : BitVec 64) (s2 : List BBlock) (p2 : BitVec 64)
    (s3 : List BBlock) (p3 : BitVec 64) (LIn LOut : Config → Prop)
    (leaf : Triple LIn LOut) where
  enter : Triple P (FiniteReady s1 p1)
  middle12 : Triple (FiniteDone s1 p1) (FiniteReady s2 p2)
  middle23 : Triple (FiniteDone s2 p2) (FiniteReady s3 p3)
  call : Triple (FiniteDone s3 p3) LIn
  leave : Triple LOut Q

theorem Via3TailLeaf.run (V : Via3TailLeaf P Q s1 p1 s2 p2 s3 p3 LIn LOut leaf) :
    Triple P Q :=
  Triple.seq V.enter <| Triple.seq (finiteRun s1 p1) <| Triple.seq V.middle12 <|
    Triple.seq (finiteRun s2 p2) <| Triple.seq V.middle23 <|
      Triple.seq (finiteRun s3 p3) <| Triple.seq V.call <| Triple.seq leaf V.leave

/-- Three reflected bodies with exact leaves between body one/two and two/three. -/
structure Via3TwoLeaves (P Q : Config → Prop)
    (s1 : List BBlock) (p1 : BitVec 64) (s2 : List BBlock) (p2 : BitVec 64)
    (s3 : List BBlock) (p3 : BitVec 64)
    (L1In L1Out L2In L2Out : Config → Prop)
    (leaf1 : Triple L1In L1Out) (leaf2 : Triple L2In L2Out) where
  enter : Triple P (FiniteReady s1 p1)
  call1 : Triple (FiniteDone s1 p1) L1In
  next12 : Triple L1Out (FiniteReady s2 p2)
  call2 : Triple (FiniteDone s2 p2) L2In
  next23 : Triple L2Out (FiniteReady s3 p3)
  leave : Triple (FiniteDone s3 p3) Q

theorem Via3TwoLeaves.run (V : Via3TwoLeaves P Q s1 p1 s2 p2 s3 p3
    L1In L1Out L2In L2Out leaf1 leaf2) : Triple P Q :=
  Triple.seq V.enter <| Triple.seq (finiteRun s1 p1) <| Triple.seq V.call1 <|
    Triple.seq leaf1 <| Triple.seq V.next12 <| Triple.seq (finiteRun s2 p2) <|
      Triple.seq V.call2 <| Triple.seq leaf2 <| Triple.seq V.next23 <|
        Triple.seq (finiteRun s3 p3) V.leave

/-- Two reflected bodies with one exact leaf between them. -/
structure Via2MiddleLeaf (P Q : Config → Prop)
    (s1 : List BBlock) (p1 : BitVec 64) (s2 : List BBlock) (p2 : BitVec 64)
    (LIn LOut : Config → Prop) (leaf : Triple LIn LOut) where
  enter : Triple P (FiniteReady s1 p1)
  call : Triple (FiniteDone s1 p1) LIn
  next : Triple LOut (FiniteReady s2 p2)
  leave : Triple (FiniteDone s2 p2) Q

theorem Via2MiddleLeaf.run (V : Via2MiddleLeaf P Q s1 p1 s2 p2 LIn LOut leaf) :
    Triple P Q :=
  Triple.seq V.enter <| Triple.seq (finiteRun s1 p1) <| Triple.seq V.call <|
    Triple.seq leaf <| Triple.seq V.next <| Triple.seq (finiteRun s2 p2) V.leave

/-- Three reflected bodies with one exact leaf between body two and three. -/
structure Via3MiddleLeaf (P Q : Config → Prop)
    (s1 : List BBlock) (p1 : BitVec 64) (s2 : List BBlock) (p2 : BitVec 64)
    (s3 : List BBlock) (p3 : BitVec 64) (LIn LOut : Config → Prop)
    (leaf : Triple LIn LOut) where
  enter : Triple P (FiniteReady s1 p1)
  middle : Triple (FiniteDone s1 p1) (FiniteReady s2 p2)
  call : Triple (FiniteDone s2 p2) LIn
  next : Triple LOut (FiniteReady s3 p3)
  leave : Triple (FiniteDone s3 p3) Q

theorem Via3MiddleLeaf.run
    (V : Via3MiddleLeaf P Q s1 p1 s2 p2 s3 p3 LIn LOut leaf) : Triple P Q :=
  Triple.seq V.enter <| Triple.seq (finiteRun s1 p1) <| Triple.seq V.middle <|
    Triple.seq (finiteRun s2 p2) <| Triple.seq V.call <| Triple.seq leaf <|
      Triple.seq V.next <| Triple.seq (finiteRun s3 p3) V.leave

/-- Finite provider for the six value-print arms.  Each field contains the
actual reflected `vp*ArmRow` and the exact external IO contract. -/
structure ValuePrintArmFiniteProvider (SL : StackLayout) where
  null : ∀ (io : CallIOContracts SL) g N A φf φc sStore pv stream ra sp m out,
    g Register.x2 = some sp → StoreRepr m N A φf φc sStore →
    ∃ lds, ViaLeaf
      (ValuePrintArmEntry g N φc pv stream ra .null m out)
      (ValuePrintArmExit g SL (CallIOPrivFoot io) ra sp
        (Value.display sStore .null) out m)
      (SegPre vpNullArm (vpNullL stream) lds 0x8000295c#64 m)
      (VpNullArmPost stream lds m)
      (fun c => GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some 0x80005260#64 ∧
        c.σ.regs.get? Register.x10 = some 0x80019018#64 ∧
        c.σ.regs.get? Register.x11 = some 1#64 ∧
        c.σ.regs.get? Register.x12 = some 4#64 ∧
        c.σ.regs.get? Register.x13 = some stream ∧
        c.σ.regs.get? Register.x1 = some ra ∧ ra.toNat % 4 = 0 ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        IsConsoleStdout stream ∧ ConsoleStream m ∧
        FwriteGround 0x80019018#64 1#64 4#64 "null" ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        Vsa.Machine.output c.σ = out ∧ c.σ.mem = m)
      (fun c => GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some ra ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        ConsoleStream c.σ.mem ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        Vsa.Machine.output c.σ = out ++ "null" ∧
        (∀ a, ¬ io.fwrite.privFoot a → ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
          c.σ.mem[a]? = m[a]?))
      (vpNullArmRow stream lds m)
      (io.fwrite.spec g 0x80019018#64 1#64 4#64 stream ra sp "null" out m)
  boolTrue : ∀ (io : CallIOContracts SL) g N A φf φc sStore pv stream ra sp m out,
    g Register.x2 = some sp → StoreRepr m N A φf φc sStore →
    ∃ lds, ViaLeaf
      (ValuePrintArmEntry g N φc pv stream ra (.bool true) m out)
      (ValuePrintArmExit g SL (CallIOPrivFoot io) ra sp
        (Value.display sStore (.bool true)) out m)
      (SegPre vpBoolTrueArm (vpBoolL pv) lds 0x80002974#64 m)
      (VpBoolTrueArmPost pv lds m) _ _ (vpBoolTrueArmRow pv lds m)
      (io.fputs.spec g 0x80019008#64 stream ra sp "true" out m)
  boolFalse : ∀ (io : CallIOContracts SL) g N A φf φc sStore pv stream ra sp m out,
    g Register.x2 = some sp → StoreRepr m N A φf φc sStore →
    ∃ lds, ViaLeaf
      (ValuePrintArmEntry g N φc pv stream ra (.bool false) m out)
      (ValuePrintArmExit g SL (CallIOPrivFoot io) ra sp
        (Value.display sStore (.bool false)) out m)
      (SegPre vpBoolFalseArm (vpBoolL pv) lds 0x80002974#64 m)
      (VpBoolFalseArmPost pv lds m) _ _ (vpBoolFalseArmRow pv lds m)
      (io.fputs.spec g 0x80019010#64 stream ra sp "false" out m)
  int : ∀ (io : CallIOContracts SL) g N A φf φc sStore n pv stream ra sp m out,
    g Register.x2 = some sp → StoreRepr m N A φf φc sStore →
    ∃ lds, ViaLeaf
      (ValuePrintArmEntry g N φc pv stream ra (.int n) m out)
      (ValuePrintArmExit g SL (CallIOPrivFoot io) ra sp
        (Value.display sStore (.int n)) out m)
      (SegPre vpIntArm (vpIntL pv stream) lds 0x80002990#64 m)
      (VpIntArmPost pv stream lds m) _ _ (vpIntArmRow pv stream lds m)
      (io.fprintf.spec g stream 0x800192c0#64 (BitVec.ofInt 64 n) ra sp
        (Value.display sStore (.int n)) out m)
  str : ∀ (io : CallIOContracts SL) g N A φf φc sStore s pv stream ra sp m out,
    g Register.x2 = some sp → StoreRepr m N A φf φc sStore →
    ∃ lds p, ViaLeaf
      (ValuePrintArmEntry g N φc pv stream ra (.str s) m out)
      (ValuePrintArmExit g SL (CallIOPrivFoot io) ra sp
        (Value.display sStore (.str s)) out m)
      (SegPre vpStrArm (vpStrL pv) lds 0x800029a4#64 m)
      (VpStrArmPost pv lds m) _ _ (vpStrArmRow pv lds m)
      (io.fputs.spec g p stream ra sp s out m)
  closure : ∀ (io : CallIOContracts SL) g N A φf φc sStore a pv stream ra sp m out,
    g Register.x2 = some sp → StoreRepr m N A φf φc sStore →
    ValueClosuresBounded sStore.closures.size (.closure a) →
    (∃ lds p, ViaLeaf
        (ValuePrintArmEntry g N φc pv stream ra (.closure a) m out)
        (ValuePrintArmExit g SL (CallIOPrivFoot io) ra sp
          (Value.display sStore (.closure a)) out m)
        (SegPre vpClosureArm (vpClosureL pv stream) lds 0x80002928#64 m)
        (VpClosureArmPost pv stream lds m) _ _ (vpClosureArmRow pv stream lds m)
        (io.fprintf.spec g stream 0x800192c8#64 p ra sp
          (Value.display sStore (.closure a)) out m)) ∨
    (∃ lds, ViaLeaf
        (ValuePrintArmEntry g N φc pv stream ra (.closure a) m out)
        (ValuePrintArmExit g SL (CallIOPrivFoot io) ra sp
          (Value.display sStore (.closure a)) out m)
        (SegPre vpClosureAnonArm (vpClosureL pv stream) lds 0x80002928#64 m)
        (VpClosureAnonArmPost pv stream lds m) _ _
        (vpClosureAnonArmRow pv stream lds m)
        (io.fwrite.spec g 0x800192d0#64 1#64 4#64 stream ra sp "<fn>" out m))
  native : ∀ (io : CallIOContracts SL) g N A φf φc sStore f pv stream ra sp m out,
    g Register.x2 = some sp → StoreRepr m N A φf φc sStore →
    ∃ lds p, ViaLeaf
      (ValuePrintArmEntry g N φc pv stream ra (.native f) m out)
      (ValuePrintArmExit g SL (CallIOPrivFoot io) ra sp
        (Value.display sStore (.native f)) out m)
      (SegPre vpNativeArm (vpNativeL pv stream) lds 0x80002948#64 m)
      (VpNativeArmPost pv stream lds m) _ _ (vpNativeArmRow pv stream lds m)
      (io.fprintf.spec g stream 0x800192d8#64 p ra sp
        (Value.display sStore (.native f)) out m)

/-- Construct the selected-arm contract from the six reflected rows. -/
def valuePrintArmsContract_of_finite (F : ValuePrintArmFiniteProvider SL) :
    ValuePrintArmsContract SL where
  run := by
    intro io g N A φf φc sStore v pv stream ra sp m out hgsp hStore hBound
    cases v with
    | null =>
        obtain ⟨lds, V⟩ := F.null io g N A φf φc sStore pv stream ra sp m out hgsp hStore
        exact V.run
    | bool b =>
        cases b with
        | false =>
            obtain ⟨lds, V⟩ := F.boolFalse io g N A φf φc sStore pv stream ra sp m out hgsp hStore
            exact V.run
        | true =>
            obtain ⟨lds, V⟩ := F.boolTrue io g N A φf φc sStore pv stream ra sp m out hgsp hStore
            exact V.run
    | int n =>
        obtain ⟨lds, V⟩ := F.int io g N A φf φc sStore n pv stream ra sp m out hgsp hStore
        exact V.run
    | str s =>
        obtain ⟨lds, p, V⟩ :=
          F.str io g N A φf φc sStore s pv stream ra sp m out hgsp hStore
        exact V.run
    | closure a =>
        rcases F.closure io g N A φf φc sStore a pv stream ra sp m out hgsp hStore hBound with
          hNamed | hAnon
        · obtain ⟨lds, p, V⟩ := hNamed
          exact V.run
        · obtain ⟨lds, V⟩ := hAnon
          exact V.run
    | native f =>
        obtain ⟨lds, p, V⟩ :=
          F.native io g N A φf φc sStore f pv stream ra sp m out hgsp hStore
        exact V.run

/-- Finite providers for the four print components.  The `Via` seams contain
only branch/jump observations, helper-call contracts, and representation
marshalling; every straight-line instruction is discharged by `finiteRun`. -/
structure NativePrintFiniteProvider (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (io : CallIOContracts SL) (dispatch : ∀ φc, ValuePrintDispatch N φc)
    (arms : ValuePrintArmsContract SL) where
  empty : ∀ g φf φc sStore out0 fsp sret retAddr interp argsBase scratch m0,
    ∃ gNull mNull outArray, Via3MiddleLeaf
      (fun c => NativePrintEntry g N A SL φf φc sStore [] out0 nativePrintPC
        fsp sret retAddr interp argsBase scratch m0 c ∧ NativePrintExtra c)
      (NativeFnOutExit g N φc SL fsp sret retAddr "" out0 m0)
      npCommonSeg 0x80002ed4#64 npRestoreSeg 0x80002f50#64
      npReturnSeg 0x80002f68#64 _ _
      (value_null_spec_full gNull sret 0x80002f68#64 N φc mNull outArray)
  first : ∀ g φf φc sStore v vs out0 fsp sret retAddr interp argsBase scratch m0,
    ∃ gValue streamValue mValue,
    ∃ hgsp : gValue Register.x2 = some (fsp - 80#64),
    ∃ hStore : StoreRepr mValue N A φf φc sStore,
    ∃ hBound : ValueClosuresBounded sStore.closures.size v,
    Via3TailLeaf
      (fun c => NativePrintEntry g N A SL φf φc sStore (v :: vs) out0 nativePrintPC
        fsp sret retAddr interp argsBase scratch m0 c ∧ NativePrintExtra c)
      (NativePrintLoopInv g N A SL φf φc sStore (v :: vs) out0 fsp sret argsBase m0 1)
      npCommonSeg 0x80002ed4#64 npSetupSeg 0x80002ee8#64
      npBodyCopySeg 0x80002f1c#64 _ _
      (valuePrint_of_dispatch_arms gValue N A SL φf φc sStore v
        (fsp - 80#64) streamValue 0x80002f48#64 (fsp - 80#64) mValue out0
        hgsp hStore hBound (dispatch φc) io arms)
  next : ∀ g φf φc sStore vs out0 fsp sret argsBase m0 i,
      (h1 : 1 ≤ i) → (hi : i < vs.length) →
    ∃ gSpace streamSpace mSpace gValue streamValue mValue,
    ∃ hgsp : gValue Register.x2 = some (fsp - 80#64),
    ∃ hStore : StoreRepr mValue N A φf φc sStore,
    ∃ hBound : ValueClosuresBounded sStore.closures.size vs[i],
    Via2TwoLeaves
      (NativePrintLoopInv g N A SL φf φc sStore vs out0 fsp sret argsBase m0 i)
      (NativePrintLoopInv g N A SL φf φc sStore vs out0 fsp sret argsBase m0 (i + 1))
      npSeparatorSeg 0x80002f0c#64 npBodyCopySeg 0x80002f1c#64 _ _ _ _
      (io.fputc.spec gSpace 32#8 streamSpace 0x80002f1c#64 (fsp - 80#64)
        (out0 ++ printedPrefix sStore vs i) mSpace)
      (valuePrint_of_dispatch_arms gValue N A SL φf φc sStore vs[i]
        (fsp - 80#64) streamValue 0x80002f48#64 (fsp - 80#64) mValue
        ((out0 ++ printedPrefix sStore vs i) ++ " ") hgsp hStore hBound
        (dispatch φc) io arms)
  finish : ∀ g φf φc sStore vs out0 fsp sret retAddr argsBase m0,
    ∃ gNull mNull outArray, Via2MiddleLeaf
      (NativePrintLoopInv g N A SL φf φc sStore vs out0 fsp sret argsBase m0 vs.length)
      (NativeFnOutExit g N φc SL fsp sret retAddr (printArgs sStore vs) out0 m0)
      npRestoreSeg 0x80002f50#64 npReturnSeg 0x80002f68#64 _ _
      (value_null_spec_full gNull sret 0x80002f68#64 N φc mNull outArray)

def nativePrintComponents_of_finite
    (io : CallIOContracts SL) (dispatch : ∀ φc, ValuePrintDispatch N φc)
    (arms : ValuePrintArmsContract SL)
    (F : NativePrintFiniteProvider N A SL io dispatch arms) :
    NativePrintComponents N A SL where
  io := io
  valueDispatch := dispatch
  valueArms := arms
  empty := by
    intro g φf φc s out fsp sr ra ip ab sc m
    obtain ⟨gn, mn, oa, V⟩ := F.empty g φf φc s out fsp sr ra ip ab sc m
    exact V.run
  first := by
    intro g φf φc s v vs out fsp sr ra ip ab sc m
    obtain ⟨gv, stream, mv, hgsp, hs, hb, V⟩ := F.first g φf φc s v vs out fsp sr ra ip ab sc m
    exact V.run
  next := by
    intro g φf φc s vs out fsp sr ab m i h1 hi
    obtain ⟨gs, ss, ms, gv, sv, mv, hgsp, hs, hb, V⟩ :=
      F.next g φf φc s vs out fsp sr ab m i h1 hi
    exact V.run
  finish := by
    intro g φf φc s vs out fsp sr ra ab m
    obtain ⟨gn, mn, oa, V⟩ := F.finish g φf φc s vs out fsp sr ra ab m
    exact V.run

/-- Finite println wrapper: reflected prologue, then the derived print loop,
then reflected fputc/null/return bodies. -/
structure NativePrintlnFiniteProvider
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (C : NativePrintComponents N A SL) where
  prologue : ∀ (g : (R : Register) → Option (RegisterType R))
      (φf φc : Addr → Nat) (sStore : Store) (vs : List Value) (out0 : String)
      (fsp sret retAddr interp argsBase scratch : BitVec 64) (m0 : Mem),
    Via1
      (fun c => NativePrintEntry g N A SL φf φc sStore vs out0 nativePrintlnPC
        fsp sret retAddr interp argsBase scratch m0 c ∧ NativePrintlnExtra c)
      (NativePrintlnPrintEntry C g φf φc sStore vs out0 fsp interp argsBase scratch)
      nplnPrefixSeg 0x80002f7c#64
  epilogue : ∀ (g : (R : Register) → Option (RegisterType R))
      (φf φc : Addr → Nat) (sStore : Store) (vs : List Value) (out0 : String)
      (fsp sret retAddr interp argsBase scratch : BitVec 64) (m0 : Mem),
    ∃ gPutc streamPutc mPutc gNull mNull outArray, Via3TwoLeaves
      (NativePrintlnAfterPrint C g φc sStore vs out0 fsp)
      (NativeFnOutExit g N φc SL fsp sret retAddr (printArgs sStore vs ++ "\n") out0 m0)
      nplnFputcSeg 0x80002f94#64 nplnNullSeg 0x80002fa4#64
      nplnReturnSeg 0x80002fac#64 _ _ _ _
      (C.io.fputc.spec gPutc 10#8 streamPutc 0x80002fa4#64 (fsp - 48#64)
        (out0 ++ printArgs sStore vs) mPutc)
      (value_null_spec_full gNull sret 0x80002fac#64 N φc mNull outArray)

def nativePrintlnComponents_of_finite
    (C : NativePrintComponents N A SL) (F : NativePrintlnFiniteProvider N A SL C) :
    NativePrintlnComponents N A SL where
  print := C
  prologue := fun g φf φc s vs out fsp sr ra ip ab sc m =>
    (F.prologue g φf φc s vs out fsp sr ra ip ab sc m).run
  epilogue := fun g φf φc s vs out fsp sr ra ip ab sc m =>
    let ⟨_, _, _, _, _, _, V⟩ := F.epilogue g φf φc s vs out fsp sr ra ip ab sc m
    V.run

#print axioms finiteRun
#print axioms nativePrintComponents_of_finite
#print axioms nativePrintlnComponents_of_finite

end Vsa.Sim
