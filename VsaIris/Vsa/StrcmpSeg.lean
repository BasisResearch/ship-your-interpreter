import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.Code.Strcmp

/-!
# Reflected `strcmp` blocks

`scripts/gen_fn.py --fn strcmp --entry 0x80006ea0`, verbatim. `Vsa/Sim/` has a
site battery for `strcmp` (`StrcmpSites.lean`) but no reflected segments, so
they are declared here for the Iris route (H3). Every instruction `strcmp`
uses (`or`, `andi`, `auipc`, `ld`, `and`, `add`, `slli`, `srli`, `sub`, `lbu`,
`addi`, and the six branch ops) is inside `MKind`/`bop`, so unlike `strlen`'s
`snez` these blocks need no observational site.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Vsa.Sim

#derive_case strcmpX6ea0TSeg chain
  [(0x80006ea0#64, 0x00b56733#32),  -- or a4,a0,a1
   (0x80006ea4#64, 0xfff00393#32),  -- li t2,-1
   (0x80006ea8#64, 0x00777713#32)]  -- andi a4,a4,7
    terminator ⟨0x80006eac#64, 0x0c071c63#32, 0x63#8, 0x1c#8, 0x07#8, 0x0c#8, .br bop.BNE true, 14, 0, 0x00d8#13, 0#21, 0#12⟩

#derive_case strcmpX6ea0FSeg chain
  [(0x80006ea0#64, 0x00b56733#32),  -- or a4,a0,a1
   (0x80006ea4#64, 0xfff00393#32),  -- li t2,-1
   (0x80006ea8#64, 0x00777713#32)]  -- andi a4,a4,7
    terminator ⟨0x80006eac#64, 0x0c071c63#32, 0x63#8, 0x1c#8, 0x07#8, 0x0c#8, .br bop.BNE false, 14, 0, 0x00d8#13, 0#21, 0#12⟩

#derive_case strcmpX6eb0Seg chain
  [(0x80006eb0#64, 0x00014797#32),  -- auipc a5,0x14
   (0x80006eb4#64, 0xdd07b783#32)]  -- ld a5,-560(a5)

#derive_case strcmpX6eb8TSeg chain
  [(0x80006eb8#64, 0x00053603#32),  -- ld a2,0(a0)
   (0x80006ebc#64, 0x0005b683#32),  -- ld a3,0(a1)
   (0x80006ec0#64, 0x00f672b3#32),  -- and t0,a2,a5
   (0x80006ec4#64, 0x00f66333#32),  -- or t1,a2,a5
   (0x80006ec8#64, 0x00f282b3#32),  -- add t0,t0,a5
   (0x80006ecc#64, 0x0062e2b3#32)]  -- or t0,t0,t1
    terminator ⟨0x80006ed0#64, 0x0c729e63#32, 0x63#8, 0x9e#8, 0x72#8, 0x0c#8, .br bop.BNE true, 5, 7, 0x00dc#13, 0#21, 0#12⟩

#derive_case strcmpX6eb8FSeg chain
  [(0x80006eb8#64, 0x00053603#32),  -- ld a2,0(a0)
   (0x80006ebc#64, 0x0005b683#32),  -- ld a3,0(a1)
   (0x80006ec0#64, 0x00f672b3#32),  -- and t0,a2,a5
   (0x80006ec4#64, 0x00f66333#32),  -- or t1,a2,a5
   (0x80006ec8#64, 0x00f282b3#32),  -- add t0,t0,a5
   (0x80006ecc#64, 0x0062e2b3#32)]  -- or t0,t0,t1
    terminator ⟨0x80006ed0#64, 0x0c729e63#32, 0x63#8, 0x9e#8, 0x72#8, 0x0c#8, .br bop.BNE false, 5, 7, 0x00dc#13, 0#21, 0#12⟩

#derive_case strcmpX6ed4TSeg chain
  []
    terminator ⟨0x80006ed4#64, 0x04d61663#32, 0x63#8, 0x16#8, 0xd6#8, 0x04#8, .br bop.BNE true, 12, 13, 0x004c#13, 0#21, 0#12⟩

#derive_case strcmpX6ed4FSeg chain
  []
    terminator ⟨0x80006ed4#64, 0x04d61663#32, 0x63#8, 0x16#8, 0xd6#8, 0x04#8, .br bop.BNE false, 12, 13, 0x004c#13, 0#21, 0#12⟩

#derive_case strcmpX6ed8TSeg chain
  [(0x80006ed8#64, 0x00853603#32),  -- ld a2,8(a0)
   (0x80006edc#64, 0x0085b683#32),  -- ld a3,8(a1)
   (0x80006ee0#64, 0x00f672b3#32),  -- and t0,a2,a5
   (0x80006ee4#64, 0x00f66333#32),  -- or t1,a2,a5
   (0x80006ee8#64, 0x00f282b3#32),  -- add t0,t0,a5
   (0x80006eec#64, 0x0062e2b3#32)]  -- or t0,t0,t1
    terminator ⟨0x80006ef0#64, 0x0a729a63#32, 0x63#8, 0x9a#8, 0x72#8, 0x0a#8, .br bop.BNE true, 5, 7, 0x00b4#13, 0#21, 0#12⟩

#derive_case strcmpX6ed8FSeg chain
  [(0x80006ed8#64, 0x00853603#32),  -- ld a2,8(a0)
   (0x80006edc#64, 0x0085b683#32),  -- ld a3,8(a1)
   (0x80006ee0#64, 0x00f672b3#32),  -- and t0,a2,a5
   (0x80006ee4#64, 0x00f66333#32),  -- or t1,a2,a5
   (0x80006ee8#64, 0x00f282b3#32),  -- add t0,t0,a5
   (0x80006eec#64, 0x0062e2b3#32)]  -- or t0,t0,t1
    terminator ⟨0x80006ef0#64, 0x0a729a63#32, 0x63#8, 0x9a#8, 0x72#8, 0x0a#8, .br bop.BNE false, 5, 7, 0x00b4#13, 0#21, 0#12⟩

#derive_case strcmpX6ef4TSeg chain
  []
    terminator ⟨0x80006ef4#64, 0x02d61663#32, 0x63#8, 0x16#8, 0xd6#8, 0x02#8, .br bop.BNE true, 12, 13, 0x002c#13, 0#21, 0#12⟩

#derive_case strcmpX6ef4FSeg chain
  []
    terminator ⟨0x80006ef4#64, 0x02d61663#32, 0x63#8, 0x16#8, 0xd6#8, 0x02#8, .br bop.BNE false, 12, 13, 0x002c#13, 0#21, 0#12⟩

#derive_case strcmpX6ef8TSeg chain
  [(0x80006ef8#64, 0x01053603#32),  -- ld a2,16(a0)
   (0x80006efc#64, 0x0105b683#32),  -- ld a3,16(a1)
   (0x80006f00#64, 0x00f672b3#32),  -- and t0,a2,a5
   (0x80006f04#64, 0x00f66333#32),  -- or t1,a2,a5
   (0x80006f08#64, 0x00f282b3#32),  -- add t0,t0,a5
   (0x80006f0c#64, 0x0062e2b3#32)]  -- or t0,t0,t1
    terminator ⟨0x80006f10#64, 0x0a729463#32, 0x63#8, 0x94#8, 0x72#8, 0x0a#8, .br bop.BNE true, 5, 7, 0x00a8#13, 0#21, 0#12⟩

#derive_case strcmpX6ef8FSeg chain
  [(0x80006ef8#64, 0x01053603#32),  -- ld a2,16(a0)
   (0x80006efc#64, 0x0105b683#32),  -- ld a3,16(a1)
   (0x80006f00#64, 0x00f672b3#32),  -- and t0,a2,a5
   (0x80006f04#64, 0x00f66333#32),  -- or t1,a2,a5
   (0x80006f08#64, 0x00f282b3#32),  -- add t0,t0,a5
   (0x80006f0c#64, 0x0062e2b3#32)]  -- or t0,t0,t1
    terminator ⟨0x80006f10#64, 0x0a729463#32, 0x63#8, 0x94#8, 0x72#8, 0x0a#8, .br bop.BNE false, 5, 7, 0x00a8#13, 0#21, 0#12⟩

#derive_case strcmpX6f14TSeg chain
  [(0x80006f14#64, 0x01850513#32),  -- addi a0,a0,24
   (0x80006f18#64, 0x01858593#32)]  -- addi a1,a1,24
    terminator ⟨0x80006f1c#64, 0xf8d60ee3#32, 0xe3#8, 0x0e#8, 0xd6#8, 0xf8#8, .br bop.BEQ true, 12, 13, 0x1f9c#13, 0#21, 0#12⟩

#derive_case strcmpX6f14FSeg chain
  [(0x80006f14#64, 0x01850513#32),  -- addi a0,a0,24
   (0x80006f18#64, 0x01858593#32)]  -- addi a1,a1,24
    terminator ⟨0x80006f1c#64, 0xf8d60ee3#32, 0xe3#8, 0x0e#8, 0xd6#8, 0xf8#8, .br bop.BEQ false, 12, 13, 0x1f9c#13, 0#21, 0#12⟩

#derive_case strcmpX6f20TSeg chain
  [(0x80006f20#64, 0x03061713#32),  -- slli a4,a2,0x30
   (0x80006f24#64, 0x03069793#32)]  -- slli a5,a3,0x30
    terminator ⟨0x80006f28#64, 0x02f71a63#32, 0x63#8, 0x1a#8, 0xf7#8, 0x02#8, .br bop.BNE true, 14, 15, 0x0034#13, 0#21, 0#12⟩

#derive_case strcmpX6f20FSeg chain
  [(0x80006f20#64, 0x03061713#32),  -- slli a4,a2,0x30
   (0x80006f24#64, 0x03069793#32)]  -- slli a5,a3,0x30
    terminator ⟨0x80006f28#64, 0x02f71a63#32, 0x63#8, 0x1a#8, 0xf7#8, 0x02#8, .br bop.BNE false, 14, 15, 0x0034#13, 0#21, 0#12⟩

#derive_case strcmpX6f2cTSeg chain
  [(0x80006f2c#64, 0x02061713#32),  -- slli a4,a2,0x20
   (0x80006f30#64, 0x02069793#32)]  -- slli a5,a3,0x20
    terminator ⟨0x80006f34#64, 0x02f71463#32, 0x63#8, 0x14#8, 0xf7#8, 0x02#8, .br bop.BNE true, 14, 15, 0x0028#13, 0#21, 0#12⟩

#derive_case strcmpX6f2cFSeg chain
  [(0x80006f2c#64, 0x02061713#32),  -- slli a4,a2,0x20
   (0x80006f30#64, 0x02069793#32)]  -- slli a5,a3,0x20
    terminator ⟨0x80006f34#64, 0x02f71463#32, 0x63#8, 0x14#8, 0xf7#8, 0x02#8, .br bop.BNE false, 14, 15, 0x0028#13, 0#21, 0#12⟩

#derive_case strcmpX6f38TSeg chain
  [(0x80006f38#64, 0x01061713#32),  -- slli a4,a2,0x10
   (0x80006f3c#64, 0x01069793#32)]  -- slli a5,a3,0x10
    terminator ⟨0x80006f40#64, 0x00f71e63#32, 0x63#8, 0x1e#8, 0xf7#8, 0x00#8, .br bop.BNE true, 14, 15, 0x001c#13, 0#21, 0#12⟩

#derive_case strcmpX6f38FSeg chain
  [(0x80006f38#64, 0x01061713#32),  -- slli a4,a2,0x10
   (0x80006f3c#64, 0x01069793#32)]  -- slli a5,a3,0x10
    terminator ⟨0x80006f40#64, 0x00f71e63#32, 0x63#8, 0x1e#8, 0xf7#8, 0x00#8, .br bop.BNE false, 14, 15, 0x001c#13, 0#21, 0#12⟩

#derive_case strcmpX6f44TSeg chain
  [(0x80006f44#64, 0x03065713#32),  -- srli a4,a2,0x30
   (0x80006f48#64, 0x0306d793#32),  -- srli a5,a3,0x30
   (0x80006f4c#64, 0x40f70533#32),  -- sub a0,a4,a5
   (0x80006f50#64, 0x0ff57593#32)]  -- zext.b a1,a0
    terminator ⟨0x80006f54#64, 0x02059063#32, 0x63#8, 0x90#8, 0x05#8, 0x02#8, .br bop.BNE true, 11, 0, 0x0020#13, 0#21, 0#12⟩

#derive_case strcmpX6f44FSeg chain
  [(0x80006f44#64, 0x03065713#32),  -- srli a4,a2,0x30
   (0x80006f48#64, 0x0306d793#32),  -- srli a5,a3,0x30
   (0x80006f4c#64, 0x40f70533#32),  -- sub a0,a4,a5
   (0x80006f50#64, 0x0ff57593#32)]  -- zext.b a1,a0
    terminator ⟨0x80006f54#64, 0x02059063#32, 0x63#8, 0x90#8, 0x05#8, 0x02#8, .br bop.BNE false, 11, 0, 0x0020#13, 0#21, 0#12⟩

#derive_case strcmpX6f58Seg chain
  []
    terminator ⟨0x80006f58#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

#derive_case strcmpX6f5cTSeg chain
  [(0x80006f5c#64, 0x03075713#32),  -- srli a4,a4,0x30
   (0x80006f60#64, 0x0307d793#32),  -- srli a5,a5,0x30
   (0x80006f64#64, 0x40f70533#32),  -- sub a0,a4,a5
   (0x80006f68#64, 0x0ff57593#32)]  -- zext.b a1,a0
    terminator ⟨0x80006f6c#64, 0x00059463#32, 0x63#8, 0x94#8, 0x05#8, 0x00#8, .br bop.BNE true, 11, 0, 0x0008#13, 0#21, 0#12⟩

#derive_case strcmpX6f5cFSeg chain
  [(0x80006f5c#64, 0x03075713#32),  -- srli a4,a4,0x30
   (0x80006f60#64, 0x0307d793#32),  -- srli a5,a5,0x30
   (0x80006f64#64, 0x40f70533#32),  -- sub a0,a4,a5
   (0x80006f68#64, 0x0ff57593#32)]  -- zext.b a1,a0
    terminator ⟨0x80006f6c#64, 0x00059463#32, 0x63#8, 0x94#8, 0x05#8, 0x00#8, .br bop.BNE false, 11, 0, 0x0008#13, 0#21, 0#12⟩

#derive_case strcmpX6f70Seg chain
  []
    terminator ⟨0x80006f70#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

#derive_case strcmpX6f74Seg chain
  [(0x80006f74#64, 0x0ff77713#32),  -- zext.b a4,a4
   (0x80006f78#64, 0x0ff7f793#32),  -- zext.b a5,a5
   (0x80006f7c#64, 0x40f70533#32)]  -- sub a0,a4,a5
    terminator ⟨0x80006f80#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

#derive_case strcmpX6f84TSeg chain
  [(0x80006f84#64, 0x00054603#32),  -- lbu a2,0(a0)
   (0x80006f88#64, 0x0005c683#32),  -- lbu a3,0(a1)
   (0x80006f8c#64, 0x00150513#32),  -- addi a0,a0,1
   (0x80006f90#64, 0x00158593#32)]  -- addi a1,a1,1
    terminator ⟨0x80006f94#64, 0x00d61463#32, 0x63#8, 0x14#8, 0xd6#8, 0x00#8, .br bop.BNE true, 12, 13, 0x0008#13, 0#21, 0#12⟩

#derive_case strcmpX6f84FSeg chain
  [(0x80006f84#64, 0x00054603#32),  -- lbu a2,0(a0)
   (0x80006f88#64, 0x0005c683#32),  -- lbu a3,0(a1)
   (0x80006f8c#64, 0x00150513#32),  -- addi a0,a0,1
   (0x80006f90#64, 0x00158593#32)]  -- addi a1,a1,1
    terminator ⟨0x80006f94#64, 0x00d61463#32, 0x63#8, 0x14#8, 0xd6#8, 0x00#8, .br bop.BNE false, 12, 13, 0x0008#13, 0#21, 0#12⟩

#derive_case strcmpX6f98TSeg chain
  []
    terminator ⟨0x80006f98#64, 0xfe0616e3#32, 0xe3#8, 0x16#8, 0x06#8, 0xfe#8, .br bop.BNE true, 12, 0, 0x1fec#13, 0#21, 0#12⟩

#derive_case strcmpX6f98FSeg chain
  []
    terminator ⟨0x80006f98#64, 0xfe0616e3#32, 0xe3#8, 0x16#8, 0x06#8, 0xfe#8, .br bop.BNE false, 12, 0, 0x1fec#13, 0#21, 0#12⟩

#derive_case strcmpX6f9cSeg chain
  [(0x80006f9c#64, 0x40d60533#32)]  -- sub a0,a2,a3
    terminator ⟨0x80006fa0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

#derive_case strcmpX6fa4Seg chain
  [(0x80006fa4#64, 0x00850513#32),  -- addi a0,a0,8
   (0x80006fa8#64, 0x00858593#32)]  -- addi a1,a1,8

#derive_case strcmpX6facTSeg chain
  []
    terminator ⟨0x80006fac#64, 0xfcd61ce3#32, 0xe3#8, 0x1c#8, 0xd6#8, 0xfc#8, .br bop.BNE true, 12, 13, 0x1fd8#13, 0#21, 0#12⟩

#derive_case strcmpX6facFSeg chain
  []
    terminator ⟨0x80006fac#64, 0xfcd61ce3#32, 0xe3#8, 0x1c#8, 0xd6#8, 0xfc#8, .br bop.BNE false, 12, 13, 0x1fd8#13, 0#21, 0#12⟩

#derive_case strcmpX6fb0Seg chain
  [(0x80006fb0#64, 0x00000513#32)]  -- li a0,0
    terminator ⟨0x80006fb4#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

#derive_case strcmpX6fb8TSeg chain
  [(0x80006fb8#64, 0x01050513#32),  -- addi a0,a0,16
   (0x80006fbc#64, 0x01058593#32)]  -- addi a1,a1,16
    terminator ⟨0x80006fc0#64, 0xfcd612e3#32, 0xe3#8, 0x12#8, 0xd6#8, 0xfc#8, .br bop.BNE true, 12, 13, 0x1fc4#13, 0#21, 0#12⟩

#derive_case strcmpX6fb8FSeg chain
  [(0x80006fb8#64, 0x01050513#32),  -- addi a0,a0,16
   (0x80006fbc#64, 0x01058593#32)]  -- addi a1,a1,16
    terminator ⟨0x80006fc0#64, 0xfcd612e3#32, 0xe3#8, 0x12#8, 0xd6#8, 0xfc#8, .br bop.BNE false, 12, 13, 0x1fc4#13, 0#21, 0#12⟩

#derive_case strcmpX6fc4Seg chain
  [(0x80006fc4#64, 0x00000513#32)]  -- li a0,0
    terminator ⟨0x80006fc8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩
end Vsa.Sim
