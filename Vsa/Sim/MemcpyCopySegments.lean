import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.Code.Memcpy

/-! Reflected memcpy spans for an aligned allocation destination. -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Vsa.Sim

#derive_case memcpyX6bc8TSeg chain
  [(0x80006bc8#64, 0x00a5c7b3#32),  -- xor a5,a1,a0
   (0x80006bcc#64, 0x0077f793#32),  -- andi a5,a5,7
   (0x80006bd0#64, 0x00c508b3#32)]  -- add a7,a0,a2
    terminator ⟨0x80006bd4#64, 0x06079663#32, 0x63#8, 0x96#8, 0x07#8, 0x06#8, .br bop.BNE true, 15, 0, 0x006c#13, 0#21, 0#12⟩

#derive_case memcpyX6bc8FSeg chain
  [(0x80006bc8#64, 0x00a5c7b3#32),  -- xor a5,a1,a0
   (0x80006bcc#64, 0x0077f793#32),  -- andi a5,a5,7
   (0x80006bd0#64, 0x00c508b3#32)]  -- add a7,a0,a2
    terminator ⟨0x80006bd4#64, 0x06079663#32, 0x63#8, 0x96#8, 0x07#8, 0x06#8, .br bop.BNE false, 15, 0, 0x006c#13, 0#21, 0#12⟩

#derive_case memcpyX6be0FSeg chain
  [(0x80006be0#64, 0x00757793#32),  -- andi a5,a0,7
   (0x80006be4#64, 0x00050713#32)]  -- mv a4,a0
    terminator ⟨0x80006be8#64, 0x0c079a63#32, 0x63#8, 0x9a#8, 0x07#8, 0x0c#8, .br bop.BNE false, 15, 0, 0x00d4#13, 0#21, 0#12⟩

#derive_case memcpyX6becTSeg chain
  [(0x80006bec#64, 0xff88f613#32),  -- andi a2,a7,-8
   (0x80006bf0#64, 0x40e606b3#32),  -- sub a3,a2,a4
   (0x80006bf4#64, 0x04000793#32)]  -- li a5,64
    terminator ⟨0x80006bf8#64, 0x06d7c463#32, 0x63#8, 0xc4#8, 0xd7#8, 0x06#8, .br bop.BLT true, 15, 13, 0x0068#13, 0#21, 0#12⟩

#derive_case memcpyX6becFSeg chain
  [(0x80006bec#64, 0xff88f613#32),  -- andi a2,a7,-8
   (0x80006bf0#64, 0x40e606b3#32),  -- sub a3,a2,a4
   (0x80006bf4#64, 0x04000793#32)]  -- li a5,64
    terminator ⟨0x80006bf8#64, 0x06d7c463#32, 0x63#8, 0xc4#8, 0xd7#8, 0x06#8, .br bop.BLT false, 15, 13, 0x0068#13, 0#21, 0#12⟩

#derive_case memcpyX6bfcTSeg chain
  [(0x80006bfc#64, 0x00058693#32),  -- mv a3,a1
   (0x80006c00#64, 0x00070793#32)]  -- mv a5,a4
    terminator ⟨0x80006c04#64, 0x02c77a63#32, 0x63#8, 0x7a#8, 0xc7#8, 0x02#8, .br bop.BGEU true, 14, 12, 0x0034#13, 0#21, 0#12⟩

#derive_case memcpyX6bfcFSeg chain
  [(0x80006bfc#64, 0x00058693#32),  -- mv a3,a1
   (0x80006c00#64, 0x00070793#32)]  -- mv a5,a4
    terminator ⟨0x80006c04#64, 0x02c77a63#32, 0x63#8, 0x7a#8, 0xc7#8, 0x02#8, .br bop.BGEU false, 14, 12, 0x0034#13, 0#21, 0#12⟩

#derive_case memcpyX6c08TSeg chain
  [(0x80006c08#64, 0x0006b803#32),  -- ld a6,0(a3)
   (0x80006c0c#64, 0x00878793#32),  -- addi a5,a5,8
   (0x80006c10#64, 0x00868693#32),  -- addi a3,a3,8
   (0x80006c14#64, 0xff07bc23#32)]  -- sd a6,-8(a5)
    terminator ⟨0x80006c18#64, 0xfec7e8e3#32, 0xe3#8, 0xe8#8, 0xc7#8, 0xfe#8, .br bop.BLTU true, 15, 12, 0x1ff0#13, 0#21, 0#12⟩

#derive_case memcpyX6c08FSeg chain
  [(0x80006c08#64, 0x0006b803#32),  -- ld a6,0(a3)
   (0x80006c0c#64, 0x00878793#32),  -- addi a5,a5,8
   (0x80006c10#64, 0x00868693#32),  -- addi a3,a3,8
   (0x80006c14#64, 0xff07bc23#32)]  -- sd a6,-8(a5)
    terminator ⟨0x80006c18#64, 0xfec7e8e3#32, 0xe3#8, 0xe8#8, 0xc7#8, 0xfe#8, .br bop.BLTU false, 15, 12, 0x1ff0#13, 0#21, 0#12⟩

#derive_case memcpyX6c1cSeg chain
  [(0x80006c1c#64, 0xfff60613#32),  -- addi a2,a2,-1
   (0x80006c20#64, 0x40e60633#32),  -- sub a2,a2,a4
   (0x80006c24#64, 0xff867613#32),  -- andi a2,a2,-8
   (0x80006c28#64, 0x00858593#32),  -- addi a1,a1,8
   (0x80006c2c#64, 0x00870713#32),  -- addi a4,a4,8
   (0x80006c30#64, 0x00c585b3#32),  -- add a1,a1,a2
   (0x80006c34#64, 0x00c70733#32)]  -- add a4,a4,a2

#derive_case memcpyX6c38TSeg chain
  []
    terminator ⟨0x80006c38#64, 0x01176863#32, 0x63#8, 0x68#8, 0x17#8, 0x01#8, .br bop.BLTU true, 14, 17, 0x0010#13, 0#21, 0#12⟩

#derive_case memcpyX6c38FSeg chain
  []
    terminator ⟨0x80006c38#64, 0x01176863#32, 0x63#8, 0x68#8, 0x17#8, 0x01#8, .br bop.BLTU false, 14, 17, 0x0010#13, 0#21, 0#12⟩

#derive_case memcpyX6c3cSeg chain
  []
    terminator ⟨0x80006c3c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

#derive_case memcpyX6c40TSeg chain
  [(0x80006c40#64, 0x00050713#32)]  -- mv a4,a0
    terminator ⟨0x80006c44#64, 0xff157ce3#32, 0xe3#8, 0x7c#8, 0x15#8, 0xff#8, .br bop.BGEU true, 10, 17, 0x1ff8#13, 0#21, 0#12⟩

#derive_case memcpyX6c40FSeg chain
  [(0x80006c40#64, 0x00050713#32)]  -- mv a4,a0
    terminator ⟨0x80006c44#64, 0xff157ce3#32, 0xe3#8, 0x7c#8, 0x15#8, 0xff#8, .br bop.BGEU false, 10, 17, 0x1ff8#13, 0#21, 0#12⟩

#derive_case memcpyX6c48TSeg chain
  [(0x80006c48#64, 0x0005c783#32),  -- lbu a5,0(a1)
   (0x80006c4c#64, 0x00170713#32),  -- addi a4,a4,1
   (0x80006c50#64, 0x00158593#32),  -- addi a1,a1,1
   (0x80006c54#64, 0xfef70fa3#32)]  -- sb a5,-1(a4)
    terminator ⟨0x80006c58#64, 0xfee898e3#32, 0xe3#8, 0x98#8, 0xe8#8, 0xfe#8, .br bop.BNE true, 17, 14, 0x1ff0#13, 0#21, 0#12⟩

#derive_case memcpyX6c48FSeg chain
  [(0x80006c48#64, 0x0005c783#32),  -- lbu a5,0(a1)
   (0x80006c4c#64, 0x00170713#32),  -- addi a4,a4,1
   (0x80006c50#64, 0x00158593#32),  -- addi a1,a1,1
   (0x80006c54#64, 0xfef70fa3#32)]  -- sb a5,-1(a4)
    terminator ⟨0x80006c58#64, 0xfee898e3#32, 0xe3#8, 0x98#8, 0xe8#8, 0xfe#8, .br bop.BNE false, 17, 14, 0x1ff0#13, 0#21, 0#12⟩

#derive_case memcpyX6c5cSeg chain
  []
    terminator ⟨0x80006c5c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

#derive_case memcpyX6c60TSeg chain
  [(0x80006c60#64, 0x0005b683#32),  -- ld a3,0(a1)
   (0x80006c64#64, 0x0085b283#32),  -- ld t0,8(a1)
   (0x80006c68#64, 0x0105bf83#32),  -- ld t6,16(a1)
   (0x80006c6c#64, 0x0185bf03#32),  -- ld t5,24(a1)
   (0x80006c70#64, 0x0205be83#32),  -- ld t4,32(a1)
   (0x80006c74#64, 0x0285be03#32),  -- ld t3,40(a1)
   (0x80006c78#64, 0x0305b303#32),  -- ld t1,48(a1)
   (0x80006c7c#64, 0x0385b803#32),  -- ld a6,56(a1)
   (0x80006c80#64, 0x00d73023#32),  -- sd a3,0(a4)
   (0x80006c84#64, 0x0405b683#32),  -- ld a3,64(a1)
   (0x80006c88#64, 0x04870713#32),  -- addi a4,a4,72
   (0x80006c8c#64, 0xfc573023#32),  -- sd t0,-64(a4)
   (0x80006c90#64, 0xfed73c23#32),  -- sd a3,-8(a4)
   (0x80006c94#64, 0xfdf73423#32),  -- sd t6,-56(a4)
   (0x80006c98#64, 0x40e606b3#32),  -- sub a3,a2,a4
   (0x80006c9c#64, 0xfde73823#32),  -- sd t5,-48(a4)
   (0x80006ca0#64, 0xfdd73c23#32),  -- sd t4,-40(a4)
   (0x80006ca4#64, 0xffc73023#32),  -- sd t3,-32(a4)
   (0x80006ca8#64, 0xfe673423#32),  -- sd t1,-24(a4)
   (0x80006cac#64, 0xff073823#32),  -- sd a6,-16(a4)
   (0x80006cb0#64, 0x04858593#32)]  -- addi a1,a1,72
    terminator ⟨0x80006cb4#64, 0xfad7c6e3#32, 0xe3#8, 0xc6#8, 0xd7#8, 0xfa#8, .br bop.BLT true, 15, 13, 0x1fac#13, 0#21, 0#12⟩

#derive_case memcpyX6c60FSeg chain
  [(0x80006c60#64, 0x0005b683#32),  -- ld a3,0(a1)
   (0x80006c64#64, 0x0085b283#32),  -- ld t0,8(a1)
   (0x80006c68#64, 0x0105bf83#32),  -- ld t6,16(a1)
   (0x80006c6c#64, 0x0185bf03#32),  -- ld t5,24(a1)
   (0x80006c70#64, 0x0205be83#32),  -- ld t4,32(a1)
   (0x80006c74#64, 0x0285be03#32),  -- ld t3,40(a1)
   (0x80006c78#64, 0x0305b303#32),  -- ld t1,48(a1)
   (0x80006c7c#64, 0x0385b803#32),  -- ld a6,56(a1)
   (0x80006c80#64, 0x00d73023#32),  -- sd a3,0(a4)
   (0x80006c84#64, 0x0405b683#32),  -- ld a3,64(a1)
   (0x80006c88#64, 0x04870713#32),  -- addi a4,a4,72
   (0x80006c8c#64, 0xfc573023#32),  -- sd t0,-64(a4)
   (0x80006c90#64, 0xfed73c23#32),  -- sd a3,-8(a4)
   (0x80006c94#64, 0xfdf73423#32),  -- sd t6,-56(a4)
   (0x80006c98#64, 0x40e606b3#32),  -- sub a3,a2,a4
   (0x80006c9c#64, 0xfde73823#32),  -- sd t5,-48(a4)
   (0x80006ca0#64, 0xfdd73c23#32),  -- sd t4,-40(a4)
   (0x80006ca4#64, 0xffc73023#32),  -- sd t3,-32(a4)
   (0x80006ca8#64, 0xfe673423#32),  -- sd t1,-24(a4)
   (0x80006cac#64, 0xff073823#32),  -- sd a6,-16(a4)
   (0x80006cb0#64, 0x04858593#32)]  -- addi a1,a1,72
    terminator ⟨0x80006cb4#64, 0xfad7c6e3#32, 0xe3#8, 0xc6#8, 0xd7#8, 0xfa#8, .br bop.BLT false, 15, 13, 0x1fac#13, 0#21, 0#12⟩

#derive_case memcpyX6cb8Seg chain
  []
    terminator ⟨0x80006cb8#64, 0xf45ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xf4#8, .j, 0, 0, 0#13, 0x1fff44#21, 0#12⟩

end Vsa.Sim
