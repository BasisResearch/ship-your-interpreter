import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.Code.Strlen

/-! Reflected strlen blocks from `scripts/gen_fn.py --fn strlen --entry 0x80006cf0`.
The supported generated segment declarations are retained. The final snez
instruction uses its existing observational proof in StrlenLastRun. -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Vsa.Sim

#derive_case strlenX6cf0TSeg chain
  [(0x80006cf0#64, 0x00757793#32),  -- andi a5,a0,7
   (0x80006cf4#64, 0x00050713#32)]  -- mv a4,a0
    terminator ⟨0x80006cf8#64, 0x08079063#32, 0x63#8, 0x90#8, 0x07#8, 0x08#8, .br bop.BNE true, 15, 0, 0x0080#13, 0#21, 0#12⟩

#derive_case strlenX6cf0FSeg chain
  [(0x80006cf0#64, 0x00757793#32),  -- andi a5,a0,7
   (0x80006cf4#64, 0x00050713#32)]  -- mv a4,a0
    terminator ⟨0x80006cf8#64, 0x08079063#32, 0x63#8, 0x90#8, 0x07#8, 0x08#8, .br bop.BNE false, 15, 0, 0x0080#13, 0#21, 0#12⟩

#derive_case strlenX6cfcSeg chain
  [(0x80006cfc#64, 0x7f7f87b7#32),  -- lui a5,0x7f7f8
   (0x80006d00#64, 0xf7f78793#32),  -- addi a5,a5,-129
   (0x80006d04#64, 0x02079693#32),  -- slli a3,a5,0x20
   (0x80006d08#64, 0x00f686b3#32),  -- add a3,a3,a5
   (0x80006d0c#64, 0xfff00593#32)]  -- li a1,-1

#derive_case strlenX6d10TSeg chain
  [(0x80006d10#64, 0x00073603#32),  -- ld a2,0(a4)
   (0x80006d14#64, 0x00870713#32),  -- addi a4,a4,8
   (0x80006d18#64, 0x00d677b3#32),  -- and a5,a2,a3
   (0x80006d1c#64, 0x00d787b3#32),  -- add a5,a5,a3
   (0x80006d20#64, 0x00c7e7b3#32),  -- or a5,a5,a2
   (0x80006d24#64, 0x00d7e7b3#32)]  -- or a5,a5,a3
    terminator ⟨0x80006d28#64, 0xfeb784e3#32, 0xe3#8, 0x84#8, 0xb7#8, 0xfe#8, .br bop.BEQ true, 15, 11, 0x1fe8#13, 0#21, 0#12⟩

#derive_case strlenX6d10FSeg chain
  [(0x80006d10#64, 0x00073603#32),  -- ld a2,0(a4)
   (0x80006d14#64, 0x00870713#32),  -- addi a4,a4,8
   (0x80006d18#64, 0x00d677b3#32),  -- and a5,a2,a3
   (0x80006d1c#64, 0x00d787b3#32),  -- add a5,a5,a3
   (0x80006d20#64, 0x00c7e7b3#32),  -- or a5,a5,a2
   (0x80006d24#64, 0x00d7e7b3#32)]  -- or a5,a5,a3
    terminator ⟨0x80006d28#64, 0xfeb784e3#32, 0xe3#8, 0x84#8, 0xb7#8, 0xfe#8, .br bop.BEQ false, 15, 11, 0x1fe8#13, 0#21, 0#12⟩

#derive_case strlenX6d2cTSeg chain
  [(0x80006d2c#64, 0xff874783#32),  -- lbu a5,-8(a4)
   (0x80006d30#64, 0x40a706b3#32)]  -- sub a3,a4,a0
    terminator ⟨0x80006d34#64, 0x06078463#32, 0x63#8, 0x84#8, 0x07#8, 0x06#8, .br bop.BEQ true, 15, 0, 0x0068#13, 0#21, 0#12⟩

#derive_case strlenX6d2cFSeg chain
  [(0x80006d2c#64, 0xff874783#32),  -- lbu a5,-8(a4)
   (0x80006d30#64, 0x40a706b3#32)]  -- sub a3,a4,a0
    terminator ⟨0x80006d34#64, 0x06078463#32, 0x63#8, 0x84#8, 0x07#8, 0x06#8, .br bop.BEQ false, 15, 0, 0x0068#13, 0#21, 0#12⟩

#derive_case strlenX6d38TSeg chain
  [(0x80006d38#64, 0xff974783#32)]  -- lbu a5,-7(a4)
    terminator ⟨0x80006d3c#64, 0x04078c63#32, 0x63#8, 0x8c#8, 0x07#8, 0x04#8, .br bop.BEQ true, 15, 0, 0x0058#13, 0#21, 0#12⟩

#derive_case strlenX6d38FSeg chain
  [(0x80006d38#64, 0xff974783#32)]  -- lbu a5,-7(a4)
    terminator ⟨0x80006d3c#64, 0x04078c63#32, 0x63#8, 0x8c#8, 0x07#8, 0x04#8, .br bop.BEQ false, 15, 0, 0x0058#13, 0#21, 0#12⟩

#derive_case strlenX6d40TSeg chain
  [(0x80006d40#64, 0xffa74783#32)]  -- lbu a5,-6(a4)
    terminator ⟨0x80006d44#64, 0x06078463#32, 0x63#8, 0x84#8, 0x07#8, 0x06#8, .br bop.BEQ true, 15, 0, 0x0068#13, 0#21, 0#12⟩

#derive_case strlenX6d40FSeg chain
  [(0x80006d40#64, 0xffa74783#32)]  -- lbu a5,-6(a4)
    terminator ⟨0x80006d44#64, 0x06078463#32, 0x63#8, 0x84#8, 0x07#8, 0x06#8, .br bop.BEQ false, 15, 0, 0x0068#13, 0#21, 0#12⟩

#derive_case strlenX6d48TSeg chain
  [(0x80006d48#64, 0xffb74783#32)]  -- lbu a5,-5(a4)
    terminator ⟨0x80006d4c#64, 0x04078c63#32, 0x63#8, 0x8c#8, 0x07#8, 0x04#8, .br bop.BEQ true, 15, 0, 0x0058#13, 0#21, 0#12⟩

#derive_case strlenX6d48FSeg chain
  [(0x80006d48#64, 0xffb74783#32)]  -- lbu a5,-5(a4)
    terminator ⟨0x80006d4c#64, 0x04078c63#32, 0x63#8, 0x8c#8, 0x07#8, 0x04#8, .br bop.BEQ false, 15, 0, 0x0058#13, 0#21, 0#12⟩

#derive_case strlenX6d50TSeg chain
  [(0x80006d50#64, 0xffc74783#32)]  -- lbu a5,-4(a4)
    terminator ⟨0x80006d54#64, 0x06078063#32, 0x63#8, 0x80#8, 0x07#8, 0x06#8, .br bop.BEQ true, 15, 0, 0x0060#13, 0#21, 0#12⟩

#derive_case strlenX6d50FSeg chain
  [(0x80006d50#64, 0xffc74783#32)]  -- lbu a5,-4(a4)
    terminator ⟨0x80006d54#64, 0x06078063#32, 0x63#8, 0x80#8, 0x07#8, 0x06#8, .br bop.BEQ false, 15, 0, 0x0060#13, 0#21, 0#12⟩

#derive_case strlenX6d58TSeg chain
  [(0x80006d58#64, 0xffd74783#32)]  -- lbu a5,-3(a4)
    terminator ⟨0x80006d5c#64, 0x06078063#32, 0x63#8, 0x80#8, 0x07#8, 0x06#8, .br bop.BEQ true, 15, 0, 0x0060#13, 0#21, 0#12⟩

#derive_case strlenX6d58FSeg chain
  [(0x80006d58#64, 0xffd74783#32)]  -- lbu a5,-3(a4)
    terminator ⟨0x80006d5c#64, 0x06078063#32, 0x63#8, 0x80#8, 0x07#8, 0x06#8, .br bop.BEQ false, 15, 0, 0x0060#13, 0#21, 0#12⟩

#derive_case strlenX6d74TSeg chain
  []
    terminator ⟨0x80006d74#64, 0xf80684e3#32, 0xe3#8, 0x84#8, 0x06#8, 0xf8#8, .br bop.BEQ true, 13, 0, 0x1f88#13, 0#21, 0#12⟩

#derive_case strlenX6d74FSeg chain
  []
    terminator ⟨0x80006d74#64, 0xf80684e3#32, 0xe3#8, 0x84#8, 0x06#8, 0xf8#8, .br bop.BEQ false, 13, 0, 0x1f88#13, 0#21, 0#12⟩

#derive_case strlenX6d78TSeg chain
  [(0x80006d78#64, 0x00074783#32),  -- lbu a5,0(a4)
   (0x80006d7c#64, 0x00170713#32),  -- addi a4,a4,1
   (0x80006d80#64, 0x00777693#32)]  -- andi a3,a4,7
    terminator ⟨0x80006d84#64, 0xfe0798e3#32, 0xe3#8, 0x98#8, 0x07#8, 0xfe#8, .br bop.BNE true, 15, 0, 0x1ff0#13, 0#21, 0#12⟩

#derive_case strlenX6d78FSeg chain
  [(0x80006d78#64, 0x00074783#32),  -- lbu a5,0(a4)
   (0x80006d7c#64, 0x00170713#32),  -- addi a4,a4,1
   (0x80006d80#64, 0x00777693#32)]  -- andi a3,a4,7
    terminator ⟨0x80006d84#64, 0xfe0798e3#32, 0xe3#8, 0x98#8, 0x07#8, 0xfe#8, .br bop.BNE false, 15, 0, 0x1ff0#13, 0#21, 0#12⟩

#derive_case strlenX6d94Seg chain
  [(0x80006d94#64, 0xff968513#32)]  -- addi a0,a3,-7
    terminator ⟨0x80006d98#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

#derive_case strlenX6d9cSeg chain
  [(0x80006d9c#64, 0xff868513#32)]  -- addi a0,a3,-8
    terminator ⟨0x80006da0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

#derive_case strlenX6da4Seg chain
  [(0x80006da4#64, 0xffb68513#32)]  -- addi a0,a3,-5
    terminator ⟨0x80006da8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

#derive_case strlenX6dacSeg chain
  [(0x80006dac#64, 0xffa68513#32)]  -- addi a0,a3,-6
    terminator ⟨0x80006db0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

#derive_case strlenX6db4Seg chain
  [(0x80006db4#64, 0xffc68513#32)]  -- addi a0,a3,-4
    terminator ⟨0x80006db8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

#derive_case strlenX6dbcSeg chain
  [(0x80006dbc#64, 0xffd68513#32)]  -- addi a0,a3,-3
    terminator ⟨0x80006dc0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

end Vsa.Sim
