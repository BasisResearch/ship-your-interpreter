import Vsa.Sim.SegEffect
import Vsa.Sim.DeriveCaseRow

open LeanRV64DExecutable Sail Vsa
open Vsa.Machine (Config)
open Vsa.MemRepr

namespace Vsa.Sim.EnvGetReflected

/-- ABI registers untouched by every env_get block. -/
def kept (R : Register) : Bool :=
  R == Register.x3 || R == Register.x4 || R == Register.x22 ||
    R == Register.x23 || R == Register.x24 || R == Register.x25 ||
    R == Register.x26 || R == Register.x27

#derive_case env_getX2c10TSeg chain
  []
    terminator ⟨0x80002c10#64, 0x0c050263#32, 0x63#8, 0x02#8, 0x05#8, 0x0c#8, .br bop.BEQ true, 10, 0, 0x00c4#13, 0#21, 0#12⟩

def env_getX2c10TL (a0 : BitVec 64) : GRegs := [(10, a0)]

#derive_case env_getX2c10FSeg chain
  []
    terminator ⟨0x80002c10#64, 0x0c050263#32, 0x63#8, 0x02#8, 0x05#8, 0x0c#8, .br bop.BEQ false, 10, 0, 0x00c4#13, 0#21, 0#12⟩

def env_getX2c10FL (a0 : BitVec 64) : GRegs := [(10, a0)]

#derive_case env_getX2c14Seg chain
  [(0x80002c14#64, 0xfc010113#32),  -- addi sp,sp,-64
   (0x80002c18#64, 0x01313c23#32),  -- sd s3,24(sp)
   (0x80002c1c#64, 0x01413823#32),  -- sd s4,16(sp)
   (0x80002c20#64, 0x01513423#32),  -- sd s5,8(sp)
   (0x80002c24#64, 0x02113c23#32),  -- sd ra,56(sp)
   (0x80002c28#64, 0x02813823#32),  -- sd s0,48(sp)
   (0x80002c2c#64, 0x02913423#32),  -- sd s1,40(sp)
   (0x80002c30#64, 0x03213023#32),  -- sd s2,32(sp)
   (0x80002c34#64, 0x00050a13#32),  -- mv s4,a0
   (0x80002c38#64, 0x00058993#32),  -- mv s3,a1
   (0x80002c3c#64, 0x00060a93#32)]  -- mv s5,a2

def env_getX2c14L (sp s3 s4 s5 ra s0 s1 s2 a0 a1 a2 : BitVec 64) : GRegs := [(2, sp), (19, s3), (20, s4), (21, s5), (1, ra), (8, s0), (9, s1), (18, s2), (10, a0), (11, a1), (12, a2)]

#derive_case env_getX2c40TSeg chain
  [(0x80002c40#64, 0x000a2903#32)]  -- lw s2,0(s4)
    terminator ⟨0x80002c44#64, 0x09205063#32, 0x63#8, 0x50#8, 0x20#8, 0x09#8, .br bop.BGE true, 0, 18, 0x0080#13, 0#21, 0#12⟩

def env_getX2c40TL (s4 : BitVec 64) : GRegs := [(20, s4)]

#derive_case env_getX2c40FSeg chain
  [(0x80002c40#64, 0x000a2903#32)]  -- lw s2,0(s4)
    terminator ⟨0x80002c44#64, 0x09205063#32, 0x63#8, 0x50#8, 0x20#8, 0x09#8, .br bop.BGE false, 0, 18, 0x0080#13, 0#21, 0#12⟩

def env_getX2c40FL (s4 : BitVec 64) : GRegs := [(20, s4)]

#derive_case env_getX2c48Seg chain
  [(0x80002c48#64, 0x008a3483#32),  -- ld s1,8(s4)
   (0x80002c4c#64, 0x00000413#32)]  -- li s0,0
    terminator ⟨0x80002c50#64, 0x0100006f#32, 0x6f#8, 0x00#8, 0x00#8, 0x01#8, .j, 0, 0, 0#13, 0x000010#21, 0#12⟩

def env_getX2c48L (s4 : BitVec 64) : GRegs := [(20, s4)]

#derive_case env_getX2c54TSeg chain
  [(0x80002c54#64, 0x00140413#32),  -- addi s0,s0,1
   (0x80002c58#64, 0x00848493#32)]  -- addi s1,s1,8
    terminator ⟨0x80002c5c#64, 0x07240463#32, 0x63#8, 0x04#8, 0x24#8, 0x07#8, .br bop.BEQ true, 8, 18, 0x0068#13, 0#21, 0#12⟩

def env_getX2c54TL (s0 s1 s2 : BitVec 64) : GRegs := [(8, s0), (9, s1), (18, s2)]

#derive_case env_getX2c54FSeg chain
  [(0x80002c54#64, 0x00140413#32),  -- addi s0,s0,1
   (0x80002c58#64, 0x00848493#32)]  -- addi s1,s1,8
    terminator ⟨0x80002c5c#64, 0x07240463#32, 0x63#8, 0x04#8, 0x24#8, 0x07#8, .br bop.BEQ false, 8, 18, 0x0068#13, 0#21, 0#12⟩

def env_getX2c54FL (s0 s1 s2 : BitVec 64) : GRegs := [(8, s0), (9, s1), (18, s2)]

#derive_case env_getX2c60Seg chain
  [(0x80002c60#64, 0x0004b503#32),  -- ld a0,0(s1)
   (0x80002c64#64, 0x00098593#32)]  -- mv a1,s3

def env_getX2c60L (s1 s3 : BitVec 64) : GRegs := [(9, s1), (19, s3)]

#derive_case env_getX2c6cTSeg chain
  []
    terminator ⟨0x80002c6c#64, 0xfe0514e3#32, 0xe3#8, 0x14#8, 0x05#8, 0xfe#8, .br bop.BNE true, 10, 0, 0x1fe8#13, 0#21, 0#12⟩

def env_getX2c6cTL (a0 : BitVec 64) : GRegs := [(10, a0)]

#derive_case env_getX2c6cFSeg chain
  []
    terminator ⟨0x80002c6c#64, 0xfe0514e3#32, 0xe3#8, 0x14#8, 0x05#8, 0xfe#8, .br bop.BNE false, 10, 0, 0x1fe8#13, 0#21, 0#12⟩

def env_getX2c6cFL (a0 : BitVec 64) : GRegs := [(10, a0)]

#derive_case env_getX2c70Seg chain
  [(0x80002c70#64, 0x010a3783#32),  -- ld a5,16(s4)
   (0x80002c74#64, 0x00141713#32),  -- slli a4,s0,0x1
   (0x80002c78#64, 0x00870733#32),  -- add a4,a4,s0
   (0x80002c7c#64, 0x00371713#32),  -- slli a4,a4,0x3
   (0x80002c80#64, 0x00e787b3#32),  -- add a5,a5,a4
   (0x80002c84#64, 0x0007b703#32),  -- ld a4,0(a5)
   (0x80002c88#64, 0x00100513#32),  -- li a0,1
   (0x80002c8c#64, 0x00eab023#32),  -- sd a4,0(s5)
   (0x80002c90#64, 0x0087b703#32),  -- ld a4,8(a5)
   (0x80002c94#64, 0x00eab423#32),  -- sd a4,8(s5)
   (0x80002c98#64, 0x0107b783#32),  -- ld a5,16(a5)
   (0x80002c9c#64, 0x00fab823#32)]  -- sd a5,16(s5)

def env_getX2c70L (s4 s0 s5 : BitVec 64) : GRegs := [(20, s4), (8, s0), (21, s5)]

#derive_case env_getX2ca0Seg chain
  [(0x80002ca0#64, 0x03813083#32),  -- ld ra,56(sp)
   (0x80002ca4#64, 0x03013403#32),  -- ld s0,48(sp)
   (0x80002ca8#64, 0x02813483#32),  -- ld s1,40(sp)
   (0x80002cac#64, 0x02013903#32),  -- ld s2,32(sp)
   (0x80002cb0#64, 0x01813983#32),  -- ld s3,24(sp)
   (0x80002cb4#64, 0x01013a03#32),  -- ld s4,16(sp)
   (0x80002cb8#64, 0x00813a83#32),  -- ld s5,8(sp)
   (0x80002cbc#64, 0x04010113#32)]  -- addi sp,sp,64
    terminator ⟨0x80002cc0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def env_getX2ca0L (sp : BitVec 64) : GRegs := [(2, sp)]

#derive_case env_getX2cc4TSeg chain
  [(0x80002cc4#64, 0x018a3a03#32)]  -- ld s4,24(s4)
    terminator ⟨0x80002cc8#64, 0xf60a1ce3#32, 0xe3#8, 0x1c#8, 0x0a#8, 0xf6#8, .br bop.BNE true, 20, 0, 0x1f78#13, 0#21, 0#12⟩

def env_getX2cc4TL (s4 : BitVec 64) : GRegs := [(20, s4)]

#derive_case env_getX2cc4FSeg chain
  [(0x80002cc4#64, 0x018a3a03#32)]  -- ld s4,24(s4)
    terminator ⟨0x80002cc8#64, 0xf60a1ce3#32, 0xe3#8, 0x1c#8, 0x0a#8, 0xf6#8, .br bop.BNE false, 20, 0, 0x1f78#13, 0#21, 0#12⟩

def env_getX2cc4FL (s4 : BitVec 64) : GRegs := [(20, s4)]

#derive_case env_getX2cccSeg chain
  [(0x80002ccc#64, 0x00000513#32)]  -- li a0,0
    terminator ⟨0x80002cd0#64, 0xfd1ff06f#32, 0x6f#8, 0xf0#8, 0x1f#8, 0xfd#8, .j, 0, 0, 0#13, 0x1fffd0#21, 0#12⟩

def env_getX2cccL : GRegs := []

#derive_case env_getX2cd4Seg chain
  [(0x80002cd4#64, 0x00000513#32)]  -- li a0,0
    terminator ⟨0x80002cd8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def env_getX2cd4L (ra : BitVec 64) : GRegs := [(1, ra)]

def segments : List (List BBlock) :=
  [env_getX2c10TSeg,
   env_getX2c10FSeg,
   env_getX2c14Seg,
   env_getX2c40TSeg,
   env_getX2c40FSeg,
   env_getX2c48Seg,
   env_getX2c54TSeg,
   env_getX2c54FSeg,
   env_getX2c60Seg,
   env_getX2c6cTSeg,
   env_getX2c6cFSeg,
   env_getX2c70Seg,
   env_getX2ca0Seg,
   env_getX2cc4TSeg,
   env_getX2cc4FSeg,
   env_getX2cccSeg,
   env_getX2cd4Seg]

/-- Prove a property of every retained register through its finite list. -/
theorem kept_of_members {P : Register → Bool}
    (h : ∀ R ∈ [Register.x3, Register.x4, Register.x22, Register.x23,
      Register.x24, Register.x25, Register.x26, Register.x27], P R = true) :
    ∀ R, kept R = true → P R = true := by
  intro R hR
  exact h R (by simpa [kept, Bool.or_eq_true, beq_iff_eq, or_assoc] using hR)

theorem kept_noise : ∀ R ∈ noiseRegs, kept R = false := by decide

theorem kept_segments : ∀ bs ∈ segments, WrChainAvoids kept bs := by decide

/-- Each generated block retains its frame and selected register results on
the same execution. Call and loop composition consume these results. -/
theorem segment_framed
    (bs : List BBlock) (hbs : bs ∈ segments)
    (L : GRegs) (lds : List (List (BitVec 8)))
    (pc0 vm : BitVec 64) (foot : Nat → Prop) (selected : GRegs) (c : Config)
    (hG : GoodState c.σ) (hpc : c.σ.regs.get? Register.PC = some pc0)
    (hmi : c.σ.regs.get? Register.minstret = some vm)
    (hL : GHolds c.σ L) (hkeys : KeysOK (keysG L))
    (hfacts : ChainFacts c.σ.mem c.σ.mem L lds bs)
    (hwf : ChainOK pc0 (keysG L) bs) (hi : c.tick < 2)
    (hfoot : ∀ k, ¬ foot k → c.σ.mem[k]? =
      (writeLog c.σ.mem (evalBlocks bs (SegEvalState.init L lds)).log)[k]?)
    (hproj : GProjects (evalBlocks bs (SegEvalState.init L lds)).regs selected) :
    ∃ c', SelectedFramedSegResult bs L lds pc0 foot kept selected c c' :=
  segEval_selected_framed bs L lds pc0 vm foot kept selected c
    hG hpc hmi hL hkeys hfacts hwf hi hfoot kept_noise (kept_segments bs hbs) hproj

#print axioms kept_of_members
#print axioms kept_noise
#print axioms kept_segments
#print axioms segment_framed

end Vsa.Sim.EnvGetReflected
